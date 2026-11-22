module

public import StacksFrontier.AlgebraicGeometry.Models.ModelHomUniqueness

/-!
# Agreement of maps on the generic fibre

On the overlap of two étale charts, flatness over the original base makes the
generic fibre scheme-theoretically dominant. This detects equality of maps into
a separated target.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

theorem eq_of_genericFiberMapOfHomOver_eq
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R))
    [Flat p] [IsSeparated q] {f g : X ⟶ Y} (hf : f ≫ q = p) (hg : g ≫ q = p)
    (heq : genericFiberMapOfHomOver (K := K) p q f hf = genericFiberMapOfHomOver p q g hg) :
    f = g := by
  have := isSchemeTheoreticallyDominant_genericFiber_fst (K := K) p
  refine eq_of_comp_isSchemeTheoreticallyDominant (pullback.fst p (genericPointInclusion R K))
    f g q (hf.trans hg.symm) ?_
  have hfst (k : X ⟶ Y) (hk : k ≫ q = p) :
      genericFiberMapOfHomOver (K := K) p q k hk ≫ pullback.fst q (genericPointInclusion R K) =
        pullback.fst p (genericPointInclusion R K) ≫ k := pullback.lift_fst _ _ _
  simpa only [hfst] using congrArg (· ≫ pullback.fst q (genericPointInclusion R K)) heq

end Stacks.Models

end
