module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorHomAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace

/-! # Currying morphisms from a tensor product of sheaves of modules -/

@[expose] public section

open CategoryTheory TensorProduct Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.PresheafOfModules.InternalHom

universe u

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSpace.{u, u})
variable {F G H : _root_.SheafOfModules.{u} (structureSheafRing X)}

/-- The sheaf-hom `ℋom_{𝒪_X}(F, G)` of two sheaves of modules on a ringed space: the
sheaf-hom over the structure sheaf of the space. -/
noncomputable abbrev sheafHomSpace (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    _root_.SheafOfModules.{u} (structureSheafRing X) :=
  _root_.Stacks.SheafOfModules.sheafHom X.presheaf (structureSheafRing X).property F G

/-- A morphism `F ⟶ ℋom(G, H)` is the curry of a morphism `F ⊗ G ⟶ H` when their
evaluations agree on every local pure tensor. -/
def IsTensorCurry (t : ((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G ⟶ H)
    (c : F ⟶ sheafHomSpace X G H) : Prop :=
  ∀ (U : Opens X.carrier) (f : F.val.obj (op U)) (g : G.val.obj (op U)),
    (((c.val.app (op U) f).app (op (Over.mk (𝟙 U)))).hom g) =
      t.val.app (op U)
        (toTensorSheafSection X F G (op U) (f ⊗ₜ[X.presheaf.obj (op U)] g))

/-- Giving a morphism `F ⊗ G ⟶ H` is canonically equivalent to giving a morphism
`F ⟶ ℋom(G, H)`. -/
@[stacks 01CN "morphism equivalence"]
noncomputable def tensorHomEquiv
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G ⟶ H) ≃ (F ⟶ sheafHomSpace X G H) :=
  (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).trans
    ((presheafTensorHomEquiv X.presheaf F.val G.val H.val).trans
      { toFun := fun f ↦ ⟨f⟩
        invFun := fun f ↦ f.val
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })

/-- The forward direction of `tensorHomEquiv` is the canonical currying map. -/
@[stacks 01CN "morphism equivalence characterization"]
theorem tensorHomEquiv_isTensorCurry
    (t : ((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G ⟶ H) :
    IsTensorCurry X t (tensorHomEquiv X F G H t) := by
  intro U f g
  have h := presheafTensorHomEquiv_apply X.presheaf F.val G.val H.val
    (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t)
    U f (𝟙 U) g
  change (((tensorHomEquiv X F G H t).val.app (op U) f).app
      (op (Over.mk (𝟙 U)))).hom g =
    (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t).app (op U)
      ((F.val.map (𝟙 (op U))) f ⊗ₜ[X.presheaf.obj (op U)] g) at h
  rw [PresheafOfModules.map_id] at h
  have hb := (PresheafOfModules.sheafificationAdjunction
    (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).homEquiv_unit
      (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) H t
  change PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t =
    sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) ≫ t.val at hb
  rwa [hb] at h

end Stacks.SheafOfModules

end
