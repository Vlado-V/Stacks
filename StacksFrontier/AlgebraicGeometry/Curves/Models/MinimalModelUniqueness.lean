module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelUniquenessOnly
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelExistence

/-!
# Existence and uniqueness of the minimal model

This module retains the combined existence-and-uniqueness theorem and reexports
the individual results.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Stacks Project, Tag 0C6B.** Let `C` be a smooth projective curve over `K` with
`H⁰(C, 𝒪_C) = K` and genus `> 0`. There is a unique minimal model for `C`: a minimal model exists,
and any two minimal models are isomorphic by a unique isomorphism of models, that is, over `R`
and compatible with the identifications of their generic fibres with `C`. -/
@[stacks 0C6B]
theorem exists_isMinimalModel_and_existsUnique_iso {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)) (hg : 0 < genus c) :
    (∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p e) ∧
    ∀ {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R))
      (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p eX → IsMinimalModel c q eY →
        ∃! φ : X ≅ Y, φ.hom ≫ q = p ∧
          eX.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ.hom =
            eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  ⟨exists_isMinimalModel c hproj hH0, fun p q eX eY hX hY =>
    existsUnique_iso_of_isMinimalModel c hg p q eX eY hX hY⟩

end Stacks.Models

end
