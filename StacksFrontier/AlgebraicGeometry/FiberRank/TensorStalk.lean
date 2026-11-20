module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint

/-!
# Fibre rank of a tensor product at a point with free stalks

This rank computation uses the stalk comparison for the sheafified tensor product.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open Stacks.SheafOfModules.TensorStalkRingedSpace (tensorStalkIso)

universe u

namespace AlgebraicGeometry.CoherentReflexive

attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

/-- The sheafified tensor product of two `𝒪_X`-modules on a scheme, read as an `𝒪_X`-module.
This is a transport of spelling: the two types are definitionally equal. -/
noncomputable abbrev tensorModules {X : Scheme.{u}} (F G : X.Modules) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
    ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))

/-- The fibre rank of a tensor product is the product of the fibre ranks, at a point where both
stalks are free.  The three module structures on the stalks are parameters, so that the scalar
action of [Stacks, Tag 01CB] — for which the comparison `(ℱ ⊗ 𝒢)_x ≅ ℱ_x ⊗ 𝒢_x` is linear — can
be substituted for Mathlib's. -/
theorem finrank_stalk_tensorSheaf {X : Scheme.{u}} (F G : X.Modules) (x : X)
    (iF : Module (X.presheaf.stalk x) (F.presheaf.stalk x))
    (iG : Module (X.presheaf.stalk x) (G.presheaf.stalk x))
    (iT : Module (X.presheaf.stalk x)
      ((tensorModules F G).presheaf.stalk x))
    (hF : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace F.val x = iF)
    (hG : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val x = iG)
    (hT : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))).val x = iT)
    (fF : @Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) _ _ iF)
    (fG : @Module.Free (X.presheaf.stalk x) (G.presheaf.stalk x) _ _ iG) :
    @Module.finrank _ _ _ _ iT =
      @Module.finrank _ _ _ _ iF * @Module.finrank _ _ _ _ iG := by
  subst hF
  subst hG
  subst hT
  have fF' : @Module.Free
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace F.val x) _ _
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace F.val x) := fF
  have fG' : @Module.Free
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace G.val x) _ _
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val x) := fG
  exact (tensorStalkIso X.toRingedSpace x F G).finrank_eq.trans Module.finrank_tensorProduct

/-- **The fibre rank at the generic point is multiplicative under the tensor product.**  On an
integral scheme the local ring at the generic point is a field, so both stalks are free there
and the comparison `(ℱ ⊗ 𝒢)_η ≅ ℱ_η ⊗ 𝒢_η` of [Stacks, Tag 01CB] computes the rank. -/
theorem fiberRank_genericPoint_tensorSheaf {X : Scheme.{u}} [IsIntegral X] (F G : X.Modules)
    [F.IsFiniteType] [G.IsFiniteType] [(tensorModules F G).IsFiniteType] :
    Scheme.Modules.fiberRank (tensorModules F G) (genericPoint X) =
      Scheme.Modules.fiberRank F (genericPoint X) *
        Scheme.Modules.fiberRank G (genericPoint X) := by
  rw [Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk,
    Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk,
    Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk]
  exact finrank_stalk_tensorSheaf F G _ _ _ _
    (Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace F.val _)
    (Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace G.val _)
    (Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace _ _)
    (Scheme.Modules.free_stalk_genericPoint F) (Scheme.Modules.free_stalk_genericPoint G)

end AlgebraicGeometry.CoherentReflexive

end
