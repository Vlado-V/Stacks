module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists

/-!
# Emptiness of a projective bundle of rank zero

This module contains the existing rank-zero emptiness theorem, with its
original declaration and proof. Its namespace is retained for API compatibility.
The cohomological rank-zero provider re-exports this module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase)

universe u

namespace Stacks.ProjectiveBundleDeRham

/-- **The projective bundle of a module finite locally free of rank zero is empty.** -/
theorem isEmpty_projectiveBundle_of_rank_zero {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] :
    IsEmpty (projectiveBundle X E) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
  have : IsEmpty (Stacks.RelativeProj.symGradedBundle E).scheme :=
    Stacks.Chow.isEmpty_bundle_of_rank_zero E
  exact Function.isEmpty (Stacks.RelativeProj.bundlePresentationIso E).inv.base

end Stacks.ProjectiveBundleDeRham
