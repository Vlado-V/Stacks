module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentation

/-!
# The stack of curves is algebraic (Stacks 0D5A)

**Stacks 0D5A** says that the stack `Curves` of families of curves is an algebraic stack. The
proof applies Artin's criterion (Stacks 07Y4) to `Curves` over `Spec(ℤ)`. The alternate
construction in `AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory`
uses the representable diagonal of Stacks 0D53 and proves openness of versality using
effectivity of special towers of square-zero thickenings.

With it, the morphism `Curves → Spec(ℤ)` is locally of finite presentation (the second half of
Stacks 0DSS): by Stacks 0CMY this is limit preservation, Stacks 0D55.

## Main results

* `AlgebraicGeometry.curvesFiberedCategory_isAlgebraicStack`: `Curves` is an algebraic stack.
* `AlgebraicGeometry.curvesAlgebraicStack_isLocallyOfFinitePresentation`: `Curves → Spec(ℤ)` is
  locally of finite presentation.

## References

* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u z

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The stack of curves is algebraic** (the absolute statement of Stacks 0D5A). The category
`Curves` of families of curves, fibred in groupoids over the big fppf site of `Spec(ℤ)`, is an
algebraic stack by Artin's criterion, using the representable diagonal and effectivity of
special towers of square-zero thickenings. The index universe `z` of the stack condition is free. -/
theorem curvesFiberedCategory_isAlgebraicStack :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ).val :=
  C1590Private.isAlgebraicStack_curvesFiberedCategory B hZ

/-- **`Curves → Spec(ℤ)` is locally of finite presentation** (the second half of Stacks 0DSS).
The structure morphism of the algebraic stack of curves is locally of finite presentation in the
sense of Stacks 06Q2: by Stacks 0CMY it suffices that `Curves` is limit preserving, which is
Stacks 0D55. -/
theorem curvesAlgebraicStack_isLocallyOfFinitePresentation :
    Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ
        (curvesAlgebraicStack.{u, z} B hZ (curvesFiberedCategory_isAlgebraicStack B hZ))) :=
  isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ _
    (isLimitPreserving_curvesFiberedCategory_unconditional B hZ)

end AlgebraicGeometry

end
