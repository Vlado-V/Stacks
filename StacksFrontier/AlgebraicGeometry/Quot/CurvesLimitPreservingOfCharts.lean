module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving

/-! Limit preservation of the stack of curves via the existing chart descent proof. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0D55.** The stack of families of curves over the big fppf site of `Spec(ℤ)` is limit
preserving in the sense of Artin's Axioms, Definition 07XL: for every inverse system of affine
schemes of the site whose limit of underlying schemes is `T`, the canonical comparison
`colim Curves_{Tᵢ} ⥤ Curves_T` is an equivalence of categories. The index category is taken in
the universe of the schemes. -/
@[stacks 0D55 "at a small index category"]
theorem isLimitPreserving_curvesFiberedCategory_unconditional :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ) :=
  C1590Private.isLimitPreserving_curvesFiberedCategory B hZ

end AlgebraicGeometry

end
