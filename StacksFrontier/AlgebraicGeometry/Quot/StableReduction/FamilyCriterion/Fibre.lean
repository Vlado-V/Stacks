module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies

/-! The genus condition on a stable fibre. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The fibre of `p : Y ⟶ S` over `s ∈ S` is a stable curve of genus `g` over `κ(s)`: its global
functions are `κ(s)`, its genus is `g`, it has genus at least two and neither a rational tail nor
a rational bridge. -/
abbrev IsStableFibreOfGenus (g : ℕ) {Y S : Scheme.{u}} (p : Y ⟶ S) (s : S) : Prop :=
  IsIso ((Scheme.ΓSpecIso (S.residueField s)).inv ≫ (p.fiberToSpecResidueField s).appTop) ∧
    HasGenusTwoNoRationalTailNoRationalBridge (S.residueField s) (p.fiberToSpecResidueField s) ∧
    genus (p.fiberToSpecResidueField s) = g

end AlgebraicGeometry

end
