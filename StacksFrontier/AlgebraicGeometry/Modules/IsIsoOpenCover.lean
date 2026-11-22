module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Isomorphisms of sheaves of modules on an open cover

A morphism is invertible when its restrictions to a jointly surjective
family of open immersions are invertible.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Invertibility of a morphism of sheaves of modules is local for a jointly surjective family
of open immersions.** -/
public theorem isIso_of_isIso_restrictFunctor_map {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) {I : Type*} {Y : I → Scheme.{u}} (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ (i : I) (y : Y i), j i y = x)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (j i)).map φ)) : IsIso φ := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk φ fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ := hcov x
  have : IsIso ((Scheme.Modules.restrictFunctor (j i)).map φ) := h i
  have h3 : IsIso ((Scheme.Modules.restrictFunctor (j i) ⋙ Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ) :=
    Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y) _
  have h2 : IsIso ((Scheme.Modules.restrictStalkNatIso (j i) y).hom.app M ≫
      (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (j i y)).map φ) := by
    rw [← (Scheme.Modules.restrictStalkNatIso (j i) y).hom.naturality φ]
    infer_instance
  have h2' : IsIso ((Scheme.Modules.restrictStalkNatIso (j i) y).hom.app M ≫
      (TopCat.Presheaf.stalkFunctor Ab.{u} (j i y)).map φ.mapPresheaf) := h2
  exact (isIso_comp_left_iff ((Scheme.Modules.restrictStalkNatIso (j i) y).hom.app M) _).mp h2'

end AlgebraicGeometry.Scheme.Modules

end
