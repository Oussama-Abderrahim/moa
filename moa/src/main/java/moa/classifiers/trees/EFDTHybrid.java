/**
 * Author: Chaitanya Manapragada.
 * <p>
 * Based on HoeffdingTree.java by Richard Kirkby.
 * <p>
 * There is a lot of code repetition from VFDT.java. This needs to be fixed as per DRY principles.
 * <p>
 * Research code written to test the EFDT idea.
 */


package moa.classifiers.trees;

import com.github.javacliparser.IntOption;
import com.yahoo.labs.samoa.instances.Instance;
import moa.classifiers.core.AttributeSplitSuggestion;
import moa.classifiers.core.attributeclassobservers.AttributeClassObserver;
import moa.classifiers.core.conditionaltests.InstanceConditionalTest;
import moa.classifiers.core.conditionaltests.NominalAttributeBinaryTest;
import moa.classifiers.core.conditionaltests.NominalAttributeMultiwayTest;
import moa.classifiers.core.conditionaltests.NumericAttributeBinaryTest;
import moa.classifiers.core.splitcriteria.SplitCriterion;
import moa.core.AutoExpandVector;
import moa.options.ClassOption;

import java.util.*;


public class EFDTHybrid extends EFDT {


    public ClassOption secondSplitCriterionOption = new ClassOption("secondSplitCriterion",
            'h', "Split criterion to use.", SplitCriterion.class,
            "GiniSplitCriterion");


    @Override
    protected void attemptToSplit(ActiveLearningNode node, SplitNode parent,
                                  int parentIndex) {

        if (node.observedClassDistributionIsPure()) return;

        node.addToSplitAttempts(1); // even if we don't actually attempt to split, we've computed infogains


//        SplitCriterion splitCriterion = (SplitCriterion) getPreparedClassOption(this.splitCriterionOption);
//        AttributeSplitSuggestion[] bestSplitSuggestions = node.getBestSplitSuggestions(splitCriterion, this);
//        Arrays.sort(bestSplitSuggestions);

        boolean shouldSplit = false;

        SplitCriterion firstSplitCriterion = (SplitCriterion) getPreparedClassOption(this.splitCriterionOption);
        SplitCriterion secondSplitCriterion = (SplitCriterion) getPreparedClassOption(this.secondSplitCriterionOption);
        SplitCriterion[] splitCriteria = {firstSplitCriterion, secondSplitCriterion};

        for (SplitCriterion splitCriterion : splitCriteria) {

            AttributeSplitSuggestion[] bestSplitSuggestions = node.getBestSplitSuggestions(splitCriterion, this);
            Arrays.sort(bestSplitSuggestions);

            for (int i = 0; i < bestSplitSuggestions.length; i++) {

                if (bestSplitSuggestions[i].splitTest != null) {
                    if (!node.getInfogainSum().containsKey((bestSplitSuggestions[i].splitTest.getAttsTestDependsOn()[0]))) {
                        node.getInfogainSum().put((bestSplitSuggestions[i].splitTest.getAttsTestDependsOn()[0]), 0.0);
                    }
                    double currentSum = node.getInfogainSum().get((bestSplitSuggestions[i].splitTest.getAttsTestDependsOn()[0]));
                    node.getInfogainSum().put((bestSplitSuggestions[i].splitTest.getAttsTestDependsOn()[0]), currentSum + bestSplitSuggestions[i].merit);
                } else { // handle the null attribute
                    double currentSum = node.getInfogainSum().get(-1); // null split
                    node.getInfogainSum().put(-1, currentSum + bestSplitSuggestions[i].merit);
                }

            }

            if (bestSplitSuggestions.length < 2) {
                shouldSplit = bestSplitSuggestions.length > 0;
            } else {
                double hoeffdingBound = computeHoeffdingBound(splitCriterion.getRangeOfMerit(node.getClassDistributionAtTimeOfCreation()),
                        this.splitConfidenceOption.getValue(), node.getWeightSeen());
                AttributeSplitSuggestion bestSuggestion = bestSplitSuggestions[bestSplitSuggestions.length - 1];

                double bestSuggestionAverageMerit;
                double currentAverageMerit = node.getInfogainSum().get(-1) / node.getNumSplitAttempts();

                // because this is an unsplit leaf. current average merit should be always zero on the null split.

                if (bestSuggestion.splitTest == null) { // if you have a null split
                    bestSuggestionAverageMerit = node.getInfogainSum().get(-1) / node.getNumSplitAttempts();
                } else {
                    bestSuggestionAverageMerit = node.getInfogainSum().get((bestSuggestion.splitTest.getAttsTestDependsOn()[0])) / node.getNumSplitAttempts();
                }

                if (bestSuggestion.merit < 1e-10) {
                    shouldSplit = false; // we don't use average here
                } else if ((bestSuggestionAverageMerit - currentAverageMerit) >
                        hoeffdingBound
                        || (hoeffdingBound < this.tieThresholdOption.getValue())) {
                    if (bestSuggestionAverageMerit - currentAverageMerit < hoeffdingBound) {
                        // Placeholder to list this possibility
                    }
                    shouldSplit = true;
                }

                if (shouldSplit) {
                    for (Integer i : node.usedNominalAttributes) {
                        if (bestSuggestion.splitTest == null || bestSuggestion.splitTest.getAttsTestDependsOn().length == 0 || bestSuggestion.splitTest.getAttsTestDependsOn()[0] == i) {
                            shouldSplit = false;
                            break;
                        }
                    }
                }

                // }
                if ((this.removePoorAttsOption != null)
                        && this.removePoorAttsOption.isSet()) {
                    Set<Integer> poorAtts = new HashSet<Integer>();
                    // scan 1 - add any poor to set
                    for (int i = 0; i < bestSplitSuggestions.length; i++) {
                        if (bestSplitSuggestions[i].splitTest != null) {
                            int[] splitAtts = bestSplitSuggestions[i].splitTest.getAttsTestDependsOn();
                            if (splitAtts.length == 1) {
                                if (bestSuggestion.merit
                                        - bestSplitSuggestions[i].merit > hoeffdingBound) {
                                    poorAtts.add(new Integer(splitAtts[0]));
                                }
                            }
                        }
                    }
                    // scan 2 - remove good ones from set
                    for (int i = 0; i < bestSplitSuggestions.length; i++) {
                        if (bestSplitSuggestions[i].splitTest != null) {
                            int[] splitAtts = bestSplitSuggestions[i].splitTest.getAttsTestDependsOn();
                            if (splitAtts.length == 1) {
                                if (bestSuggestion.merit
                                        - bestSplitSuggestions[i].merit < hoeffdingBound) {
                                    poorAtts.remove(new Integer(splitAtts[0]));
                                }
                            }
                        }
                    }
                    for (int poorAtt : poorAtts) {
                        node.disableAttribute(poorAtt);
                    }
                }
            }
            if (shouldSplit) {
                splitCount++;

                AttributeSplitSuggestion splitDecision = bestSplitSuggestions[bestSplitSuggestions.length - 1];
                if (splitDecision.splitTest == null) {
                    // preprune - null wins
                    deactivateLearningNode(node, parent, parentIndex);
                } else {
                    Node newSplit = newSplitNode(splitDecision.splitTest,
                            node.getObservedClassDistribution(), splitDecision.numSplits());
                    ((EFDTHybridSplitNode) newSplit).attributeObservers = node.attributeObservers; // copy the attribute observers
                    ((EFDTHybridSplitNode) newSplit).setInfogainSum(node.getInfogainSum());  // transfer infogain history, leaf to split

                    for (int i = 0; i < splitDecision.numSplits(); i++) {

                        double[] j = splitDecision.resultingClassDistributionFromSplit(i);

                        Node newChild = newLearningNode(splitDecision.resultingClassDistributionFromSplit(i));

                        if (splitDecision.splitTest.getClass() == NominalAttributeBinaryTest.class
                                || splitDecision.splitTest.getClass() == NominalAttributeMultiwayTest.class) {
                            newChild.usedNominalAttributes = new ArrayList<Integer>(node.usedNominalAttributes); //deep copy
                            newChild.usedNominalAttributes.add(splitDecision.splitTest.getAttsTestDependsOn()[0]);
                            // no  nominal attribute should be split on more than once in the path
                        }
                        ((EFDTHybridSplitNode) newSplit).setChild(i, newChild);
                    }
                    this.activeLeafNodeCount--;
                    this.decisionNodeCount++;
                    this.activeLeafNodeCount += splitDecision.numSplits();
                    if (parent == null) {
                        this.treeRoot = newSplit;
                    } else {
                        parent.setChild(parentIndex, newSplit);
                    }

                }
                // manage memory
                enforceTrackerLimit();
                break; // If already split, skip next criteria
            }
        }

    }

    @Override
    public void trainOnInstanceImpl(Instance inst) {

        if (this.treeRoot == null) {
            this.treeRoot = newLearningNode();
            ((EFDTHybridNode) this.treeRoot).setRoot(true);
            this.activeLeafNodeCount = 1;
        }

        FoundNode foundNode = this.treeRoot.filterInstanceToLeaf(inst, null, -1);
        Node leafNode = foundNode.node;

        if (leafNode == null) {
            leafNode = newLearningNode();
            foundNode.parent.setChild(foundNode.parentBranch, leafNode);
            this.activeLeafNodeCount++;
        }

        ((EFDTHybridNode) this.treeRoot).learnFromInstance(inst, this, null, -1);

        numInstances++;
    }


    @Override
    protected LearningNode newLearningNode() {
        return new EFDTHybridLearningNode(new double[0]);
    }

    @Override
    protected LearningNode newLearningNode(double[] initialClassObservations) {
        return new EFDTHybridLearningNode(initialClassObservations);
    }

    @Override
    protected SplitNode newSplitNode(InstanceConditionalTest splitTest, double[] classObservations, int size) {
        return new EFDTHybridSplitNode(splitTest, classObservations, size);
    }

    @Override
    protected SplitNode newSplitNode(InstanceConditionalTest splitTest, double[] classObservations) {
        return new EFDTHybridSplitNode(splitTest, classObservations);
    }


    public interface EFDTHybridNode {

        public boolean isRoot();

        public void setRoot(boolean isRoot);

        public void learnFromInstance(Instance inst, EFDTHybrid ht, EFDTHybridSplitNode parent, int parentBranch);

        public void setParent(EFDTHybridSplitNode parent);

        public EFDTHybridSplitNode getParent();

    }

    public class EFDTHybridLearningNode extends LearningNodeNBAdaptive implements EFDTHybridNode {

        private boolean isRoot;

        private EFDTHybridSplitNode parent = null;

        public EFDTHybridLearningNode(double[] initialClassObservations) {
            super(initialClassObservations);
        }


        /**
         *
         */
        private static final long serialVersionUID = -2525042202040084035L;

        @Override
        public boolean isRoot() {
            return isRoot;
        }

        @Override
        public void setRoot(boolean isRoot) {
            this.isRoot = isRoot;
        }

        @Override
        public void learnFromInstance(Instance inst, VFDT ht) {
            super.learnFromInstance(inst, ht);

        }

        @Override
        public void learnFromInstance(Instance inst, EFDTHybrid ht, EFDTHybridSplitNode parent, int parentBranch) {
            learnFromInstance(inst, ht);

            if (ht.growthAllowed
                    && (this instanceof ActiveLearningNode)) {
                ActiveLearningNode activeLearningNode = this;
                double weightSeen = activeLearningNode.getWeightSeen();
                if (activeLearningNode.nodeTime % ht.gracePeriodOption.getValue() == 0) {
                    attemptToSplit(activeLearningNode, parent,
                            parentBranch);
                    activeLearningNode.setWeightSeenAtLastSplitEvaluation(weightSeen);
                }
            }
        }

        @Override
        public void setParent(EFDTHybridSplitNode parent) {
            this.parent = parent;
        }

        @Override
        public EFDTHybridSplitNode getParent() {
            return this.parent;
        }


    }


    public class EFDTHybridSplitNode extends SplitNode implements EFDTHybridNode {

        /**
         *
         */

        private boolean isRoot;

        private EFDTHybridSplitNode parent = null;

        private static final long serialVersionUID = 1L;

        protected AutoExpandVector<AttributeClassObserver> attributeObservers;

        public EFDTHybridSplitNode(InstanceConditionalTest splitTest, double[] classObservations, int size) {
            super(splitTest, classObservations, size);
        }

        public EFDTHybridSplitNode(InstanceConditionalTest splitTest, double[] classObservations) {
            super(splitTest, classObservations);
        }

        @Override
        public boolean isRoot() {
            return isRoot;
        }

        @Override
        public void setRoot(boolean isRoot) {
            this.isRoot = isRoot;
        }

        public void killSubtree(VFDT ht) {
            for (Node child : this.children) {
                if (child != null) {

                    //Recursive delete of SplitNodes
                    if (child instanceof SplitNode) {
                        ((EFDTHybridSplitNode) child).killSubtree(ht);
                    } else if (child instanceof ActiveLearningNode) {
                        child = null;
                        ht.activeLeafNodeCount--;
                    } else if (child instanceof InactiveLearningNode) {
                        child = null;
                        ht.inactiveLeafNodeCount--;
                    } else {

                    }
                }
            }
        }


        // DRY Don't Repeat Yourself... code duplicated from ActiveLearningNode in VFDT.java. However, this is the most practical way to share stand-alone.
        public AttributeSplitSuggestion[] getBestSplitSuggestions(
                SplitCriterion criterion, EFDTHybrid ht) {
            List<AttributeSplitSuggestion> bestSuggestions = new LinkedList<AttributeSplitSuggestion>();
            double[] preSplitDist = this.observedClassDistribution.getArrayCopy();
            if (!ht.noPrePruneOption.isSet()) {
                // add null split as an option
                bestSuggestions.add(new AttributeSplitSuggestion(null,
                        new double[0][], criterion.getMeritOfSplit(
                        preSplitDist, new double[][]{preSplitDist})));
            }
            for (int i = 0; i < this.attributeObservers.size(); i++) {
                AttributeClassObserver obs = this.attributeObservers.get(i);
                if (obs != null) {
                    AttributeSplitSuggestion bestSuggestion = obs.getBestEvaluatedSplitSuggestion(criterion,
                            preSplitDist, i, ht.binarySplitsOption.isSet());
                    if (bestSuggestion != null) {
                        bestSuggestions.add(bestSuggestion);
                    }
                }
            }
            return bestSuggestions.toArray(new AttributeSplitSuggestion[bestSuggestions.size()]);
        }


        @Override
        public void learnFromInstance(Instance inst, EFDTHybrid ht, EFDTHybridSplitNode parent, int parentBranch) {

            nodeTime++;
            //// Update node statistics and class distribution

            this.observedClassDistribution.addToValue((int) inst.classValue(), inst.weight()); // update prior (predictor)

            for (int i = 0; i < inst.numAttributes() - 1; i++) { //update likelihood
                int instAttIndex = modelAttIndexToInstanceAttIndex(i, inst);
                AttributeClassObserver obs = this.attributeObservers.get(i);
                if (obs == null) {
                    obs = inst.attribute(instAttIndex).isNominal() ? ht.newNominalClassObserver() : ht.newNumericClassObserver();
                    this.attributeObservers.set(i, obs);
                }
                obs.observeAttributeClass(inst.value(instAttIndex), (int) inst.classValue(), inst.weight());
            }

            // check if a better split is available. if so, chop the tree at this point, copying likelihood. predictors for children are from parent likelihood.
            if (ht.numInstances % ht.reEvalPeriodOption.getValue() == 0) {
                this.reEvaluateBestSplit(this, parent, parentBranch);
            }

            int childBranch = this.instanceChildIndex(inst);
            Node child = this.getChild(childBranch);

            if (child != null) {
                ((EFDTHybridNode) child).learnFromInstance(inst, ht, this, childBranch);
            }

        }

        protected void reEvaluateBestSplit(EFDTHybridSplitNode node, EFDTHybridSplitNode parent, int parentIndex) {


            node.addToSplitAttempts(1);

            // EFDT must transfer over gain averages when replacing a node: leaf to split, split to leaf, or split to split
            // It must replace split nodes with leaves if null wins


            // node is a reference to this anyway... why have it at all?

            int currentSplit = -1;
            // and if we always choose to maintain tree structure

            //lets first find out X_a, the current split

            if (this.splitTest != null) {
                currentSplit = this.splitTest.getAttsTestDependsOn()[0];
                // given the current implementations in MOA, we're only ever expecting one int to be returned
            } else { // there is no split, split is null
                currentSplit = -1;
            }

            SplitCriterion firstSplitCriterion = (SplitCriterion) getPreparedClassOption(EFDTHybrid.this.splitCriterionOption);
            SplitCriterion secondSplitCriterion = (SplitCriterion) getPreparedClassOption(EFDTHybrid.this.secondSplitCriterionOption);

            SplitCriterion[] splitCriteria = {firstSplitCriterion, secondSplitCriterion};

            for (SplitCriterion splitCriterion : splitCriteria) {

                //compute Hoeffding bound
                double hoeffdingBound = computeHoeffdingBound(splitCriterion.getRangeOfMerit(node.getClassDistributionAtTimeOfCreation()),
                        EFDTHybrid.this.splitConfidenceOption.getValue(), node.observedClassDistribution.sumOfValues());

                // get best split suggestions
                AttributeSplitSuggestion[] bestSplitSuggestions = node.getBestSplitSuggestions(splitCriterion, EFDTHybrid.this);
                Arrays.sort(bestSplitSuggestions);

                // get the best suggestion
                AttributeSplitSuggestion bestSuggestion = bestSplitSuggestions[bestSplitSuggestions.length - 1];


                for (int i = 0; i < bestSplitSuggestions.length; i++) {

                    if (bestSplitSuggestions[i].splitTest != null) {
                        if (!node.getInfogainSum().containsKey((bestSplitSuggestions[i].splitTest.getAttsTestDependsOn()[0]))) {
                            node.getInfogainSum().put((bestSplitSuggestions[i].splitTest.getAttsTestDependsOn()[0]), 0.0);
                        }
                        double currentSum = node.getInfogainSum().get((bestSplitSuggestions[i].splitTest.getAttsTestDependsOn()[0]));
                        node.getInfogainSum().put((bestSplitSuggestions[i].splitTest.getAttsTestDependsOn()[0]), currentSum + bestSplitSuggestions[i].merit);
                    } else { // handle the null attribute. this is fine to do- it'll always average zero, and we will use this later to potentially burn bad splits.
                        double currentSum = node.getInfogainSum().get(-1); // null split
                        node.getInfogainSum().put(-1, currentSum + bestSplitSuggestions[i].merit);
                    }

                }

                // get the average merit for best and current splits

                double bestSuggestionAverageMerit = 0.0;
                double currentAverageMerit = 0.0;

                if (bestSuggestion.splitTest == null) { // best is null
                    bestSuggestionAverageMerit = node.getInfogainSum().get(-1) / node.getNumSplitAttempts();
                } else {

                    bestSuggestionAverageMerit = node.getInfogainSum().get(bestSuggestion.splitTest.getAttsTestDependsOn()[0]) / node.getNumSplitAttempts();
                }

                if (node.splitTest == null) { // current is null- shouldn't happen, check for robustness
                    currentAverageMerit = node.getInfogainSum().get(-1) / node.getNumSplitAttempts();
                } else {
                    currentAverageMerit = node.getInfogainSum().get(node.splitTest.getAttsTestDependsOn()[0]) / node.getNumSplitAttempts();
                }

                double tieThreshold = EFDTHybrid.this.tieThresholdOption.getValue();

                // compute the average deltaG
                double deltaG = bestSuggestionAverageMerit - currentAverageMerit;

                if (deltaG > hoeffdingBound
                        || (hoeffdingBound < tieThreshold && deltaG > tieThreshold / 2)) {

                    System.err.println(numInstances);

                    AttributeSplitSuggestion splitDecision = bestSuggestion;

                    // if null split wins
                    if (splitDecision.splitTest == null) {

                        node.killSubtree(EFDTHybrid.this);
                        EFDTHybridLearningNode replacement = (EFDTHybridLearningNode) newLearningNode();
                        replacement.setInfogainSum(node.getInfogainSum()); // transfer infogain history, split to replacement leaf
                        if (node.getParent() != null) {
                            node.getParent().setChild(parentIndex, replacement);
                        } else {
                            assert (node.getParent().isRoot());
                            node.setRoot(true);
                        }
                    } else {

                        Node newSplit = newSplitNode(splitDecision.splitTest,
                                node.getObservedClassDistribution(), splitDecision.numSplits());

                        ((EFDTHybridSplitNode) newSplit).attributeObservers = node.attributeObservers; // copy the attribute observers
                        newSplit.setInfogainSum(node.getInfogainSum());  // transfer infogain history, split to replacement split

                        if (node.splitTest == splitDecision.splitTest
                                && node.splitTest.getClass() == NumericAttributeBinaryTest.class &&
                                (argmax(splitDecision.resultingClassDistributions[0]) == argmax(node.getChild(0).getObservedClassDistribution())
                                        || argmax(splitDecision.resultingClassDistributions[1]) == argmax(node.getChild(1).getObservedClassDistribution()))
                        ) {
                            // change split but don't destroy the subtrees
                            for (int i = 0; i < splitDecision.numSplits(); i++) {
                                ((EFDTHybridSplitNode) newSplit).setChild(i, this.getChild(i));
                            }

                        } else {

                            // otherwise, torch the subtree and split on the new best attribute.

                            this.killSubtree(EFDTHybrid.this);

                            for (int i = 0; i < splitDecision.numSplits(); i++) {

                                double[] j = splitDecision.resultingClassDistributionFromSplit(i);

                                Node newChild = newLearningNode(splitDecision.resultingClassDistributionFromSplit(i));

                                if (splitDecision.splitTest.getClass() == NominalAttributeBinaryTest.class
                                        || splitDecision.splitTest.getClass() == NominalAttributeMultiwayTest.class) {
                                    newChild.usedNominalAttributes = new ArrayList<Integer>(node.usedNominalAttributes); //deep copy
                                    newChild.usedNominalAttributes.add(splitDecision.splitTest.getAttsTestDependsOn()[0]);
                                    // no  nominal attribute should be split on more than once in the path
                                }
                                ((EFDTHybridSplitNode) newSplit).setChild(i, newChild);
                            }

                            EFDTHybrid.this.activeLeafNodeCount--;
                            EFDTHybrid.this.decisionNodeCount++;
                            EFDTHybrid.this.activeLeafNodeCount += splitDecision.numSplits();

                        }


                        if (parent == null) {
                            ((EFDTHybridNode) newSplit).setRoot(true);
                            ((EFDTHybridNode) newSplit).setParent(null);
                            EFDTHybrid.this.treeRoot = newSplit;
                        } else {
                            ((EFDTHybridNode) newSplit).setRoot(false);
                            ((EFDTHybridNode) newSplit).setParent(parent);
                            parent.setChild(parentIndex, newSplit);
                        }
                    }
                }
            }
        }

        @Override
        public void setParent(EFDTHybridSplitNode parent) {
            this.parent = parent;
        }

        @Override
        public EFDTHybridSplitNode getParent() {
            return this.parent;
        }
    }


}
