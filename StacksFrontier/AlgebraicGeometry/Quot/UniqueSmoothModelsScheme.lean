module

public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.CurveFacts
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.GoodReduction
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelUniquenessOnly
public import StacksFrontier.AlgebraicGeometry.Models.BaseChange

/-!
# Isomorphisms of smooth models over a discrete valuation ring

Two smooth stable models of the same generic curve are isomorphic as models.
A smooth proper model is minimal, so the result follows from uniqueness of
minimal models for curves of positive genus.
-/

public section

open CategoryTheory CategoryTheory.Limits Stacks.Models

universe u

namespace AlgebraicGeometry

/-- Smooth stable models of the same smooth generic curve are isomorphic as models. -/
theorem existsIsoOfSmoothStableModels (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (g : ℕ)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}} (C_to_K : C ⟶ Spec (.of K))
    [Smooth C_to_K] {X X' : Scheme.{u}} {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    {e' : C ≅ pullback p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    (hmod : IsModel C_to_K p e) (hmod' : IsModel C_to_K p' e')
    (hst : IsStableFamilyOfSchemesOfGenus B hZ g p hR)
    (hst' : IsStableFamilyOfSchemesOfGenus B hZ g p' hR)
    (hsmooth : Smooth p) (hsmooth' : Smooth p') :
    ∃ f : X ≅ X', IsModelHom p p' e e' f.hom := by
  obtain ⟨hcurve, _, hH0, _, hproj, hgenus, _⟩ :=
    curveFacts_of_isStableFamilyOfSchemesOfGenus C_to_K hmod hst
  letI := hcurve
  letI := hH0
  letI := hst.isProper
  letI := hst'.isProper
  letI := hsmooth
  letI := hsmooth'
  have hp := isMinimalModel_of_isModel_of_smooth C_to_K hproj p e hmod
  have hp' := isMinimalModel_of_isModel_of_smooth C_to_K hproj p' e' hmod'
  obtain ⟨f, ⟨hf, hfst⟩, -⟩ := existsUnique_iso_of_isMinimalModel C_to_K
    (lt_of_lt_of_le (by decide : 0 < 2) hgenus) p p' e e' hp hp'
  refine ⟨f, ⟨hf, ?_⟩⟩
  apply pullback.hom_ext
  · simp only [genericFiberMapOfHomOver, Category.assoc, pullback.lift_fst]
    exact hfst
  · simp only [genericFiberMapOfHomOver, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact hmod.2.2.2.trans hmod'.2.2.2.symm

end AlgebraicGeometry

end
