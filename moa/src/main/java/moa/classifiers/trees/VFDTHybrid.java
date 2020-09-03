package moa.classifiers.trees;

import moa.classifiers.core.AttributeSplitSuggestion;
import moa.classifiers.core.conditionaltests.NominalAttributeBinaryTest;
import moa.classifiers.core.conditionaltests.NominalAttributeMultiwayTest;
import moa.classifiers.core.splitcriteria.SplitCriterion;
import moa.options.ClassOption;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

public class VFDTHybrid extends VFDT {

    public ClassOption secondSplitCriterionOption = new ClassOption("secondSplitCriterion",
            'h', "Split criterion to use.", SplitCriterion.class,
            "GiniSplitCriterion");


    @Override
    protected void attemptToSplit(ActiveLearningNode node, SplitNode parent, int parentIndex) {
        if (node.observedClassDistributionIsPure()) return;


        SplitCriterion firstSplitCriterion = (SplitCriterion) getPreparedClassOption(this.splitCriterionOption);
        SplitCriterion secondSplitCriterion = (SplitCriterion) getPreparedClassOption(this.secondSplitCriterionOption);

        SplitCriterion[] splitCriteria = {firstSplitCriterion, secondSplitCriterion};

        for (SplitCriterion splitCriterion : splitCriteria) {

            AttributeSplitSuggestion[] bestSplitSuggestions = node.getBestSplitSuggestions(splitCriterion, this);

            Arrays.sort(bestSplitSuggestions);
            boolean shouldSplit = false;

            for (int i = 0; i < bestSplitSuggestions.length; i++) {

                node.addToSplitAttempts(1); // even if we don't actually attempt to split, we've computed infogains


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
                AttributeSplitSuggestion secondBestSuggestion = bestSplitSuggestions[bestSplitSuggestions.length - 2];


                double bestSuggestionAverageMerit = 0.0;
                double secondBestSuggestionAverageMerit = 0.0;

                if (bestSuggestion.splitTest == null) { // if you have a null split
                    bestSuggestionAverageMerit = node.getInfogainSum().get(-1) / node.getNumSplitAttempts();
                } else {
                    bestSuggestionAverageMerit = node.getInfogainSum().get((bestSuggestion.splitTest.getAttsTestDependsOn()[0])) / node.getNumSplitAttempts();
                }

                if (secondBestSuggestion.splitTest == null) { // if you have a null split
                    secondBestSuggestionAverageMerit = node.getInfogainSum().get(-1) / node.getNumSplitAttempts();
                } else {
                    secondBestSuggestionAverageMerit = node.getInfogainSum().get((secondBestSuggestion.splitTest.getAttsTestDependsOn()[0])) / node.getNumSplitAttempts();
                }

                //comment this if statement to get VFDT bug
                if (bestSuggestion.merit < 1e-10) { // we don't use average here
                    shouldSplit = false;
                } else if ((bestSuggestionAverageMerit - secondBestSuggestionAverageMerit > hoeffdingBound)
                        || (hoeffdingBound < this.tieThresholdOption.getValue())) {
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
                    SplitNode newSplit = newSplitNode(splitDecision.splitTest,
                            node.getObservedClassDistribution(), splitDecision.numSplits());
                    for (int i = 0; i < splitDecision.numSplits(); i++) {

                        double[] j = splitDecision.resultingClassDistributionFromSplit(i);

                        Node newChild = newLearningNode(splitDecision.resultingClassDistributionFromSplit(i));

                        if (splitDecision.splitTest.getClass() == NominalAttributeBinaryTest.class
                                || splitDecision.splitTest.getClass() == NominalAttributeMultiwayTest.class) {
                            newChild.usedNominalAttributes = new ArrayList<Integer>(node.usedNominalAttributes); //deep copy
                            newChild.usedNominalAttributes.add(splitDecision.splitTest.getAttsTestDependsOn()[0]);
                            // no  nominal attribute should be split on more than once in the path
                        }
                        newSplit.setChild(i, newChild);
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
}
