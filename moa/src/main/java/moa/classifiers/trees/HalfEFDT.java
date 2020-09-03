/**
 * Author: Chaitanya Manapragada.
 * <p>
 * Based on HoeffdingTree.java by Richard Kirkby.
 * Research code written to test the EFDT idea.
 *
 * Variant for testing : Using half the value of the computed HoeffdingBound
 */


package moa.classifiers.trees;

public class HalfEFDT extends EFDT {

    @Override
    public double computeHoeffdingBound(double range, double confidence, double n) {
        return super.computeHoeffdingBound(range, confidence, n) * 0.5;
    }
}
