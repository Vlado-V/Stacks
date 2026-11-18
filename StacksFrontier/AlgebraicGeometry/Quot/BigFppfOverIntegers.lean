module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies

/-!
# Morphisms over the integer base in a big fppf site

The original morphism-lifting and isomorphism-reflection helpers, separated from
stable contraction geometry. Their names, declarations and proofs are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- A morphism of schemes of the site over the integers lifts to a morphism of the site. -/
def BigFppfOver.liftOfIntegers {V W : BigFppfOver B integerBase hZ} (g : (𝒯).obj V ⟶ (𝒯).obj W) :
    V ⟶ W :=
  Over.homMk (ObjectProperty.homMk g) (by
    apply B.inclusion.map_injective
    exact specULiftZIsTerminal.hom_ext _ _)

/-- The underlying morphism of schemes of `BigFppfOver.liftOfIntegers g` is `g`. -/
theorem BigFppfOver.toScheme_map_liftOfIntegers {V W : BigFppfOver B integerBase hZ}
    (g : (𝒯).obj V ⟶ (𝒯).obj W) : (𝒯).map (BigFppfOver.liftOfIntegers g) = g := rfl

/-- A morphism of schemes of the site over the integers is an isomorphism when its underlying
morphism of schemes is. -/
theorem BigFppfOver.isIso_of_isIso_toScheme_map {V W : BigFppfOver B integerBase hZ}
    (a : V ⟶ W) [IsIso ((𝒯).map a)] : IsIso a := by
  refine ⟨BigFppfOver.liftOfIntegers (inv ((𝒯).map a)), ?_, ?_⟩ <;>
    apply (𝒯).map_injective <;>
    rw [Functor.map_comp, BigFppfOver.toScheme_map_liftOfIntegers,
      CategoryTheory.Functor.map_id] <;> simp

end AlgebraicGeometry

end
