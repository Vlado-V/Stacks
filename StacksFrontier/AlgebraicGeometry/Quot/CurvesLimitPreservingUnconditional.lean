module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreservingOfCharts
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts

/-!
# The stack of curves is limit preserving (Stacks 0D55)

**Stacks 0D55**: the stack `Curves ⟶ Sch_fppf` of families of curves is *limit preserving* in the
sense of Artin's Axioms, Definition 07XL — for every directed inverse system of affine schemes of
the site with limit `T`, the canonical comparison `colim Curves_{Tᵢ} ⥤ Curves_T` is an equivalence
of categories. The statement is proved from the chart descent argument and re-exported here alongside
the general descent interfaces for proper flat families.

## Main results

* `AlgebraicGeometry.isLimitPreserving_curvesFiberedCategory_unconditional`: **Stacks 0D55**, for
  index categories in the universe `u` of the schemes, with no hypothesis beyond the site and its
  containing `Spec(ℤ)`.

## References

* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
* [Stacks Project, Tag 0D50](https://stacks.math.columbia.edu/tag/0D50)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/
