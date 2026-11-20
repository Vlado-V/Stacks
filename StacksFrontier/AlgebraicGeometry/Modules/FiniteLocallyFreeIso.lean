module

public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree

/-!
# Finite local freeness under an isomorphism

A sheaf isomorphism transports a finite locally free generating family.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry

/-- Finite local freeness of a sheaf of modules only depends on its isomorphism class. -/
theorem isFiniteLocallyFree_of_iso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree N := by
  obtain ⟨q, hq, hq'⟩ := h.exists_isFiniteLocallyFreeData
  exact ⟨Stacks.FiniteLocallyFree.localGeneratorsDataOfIsIso e.hom q, inferInstance,
    inferInstance⟩

end Stacks.AlgebraicGeometry

end
