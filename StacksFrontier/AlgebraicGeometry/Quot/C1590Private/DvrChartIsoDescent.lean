module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget

/-!
# Descent of an isomorphism from a single fppf base chart

After gluing a map between two models, its lift over the common chart is an
isomorphism. The two projection equations identify this lift with the pullback
of the glued map along the chart of its target.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

theorem isIso_of_isIso_after_base_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y Z X V : AlgebraicSpaces B S hS} (z : Z ⟶ Y) (x : X ⟶ Y) (v : V ⟶ Y)
    (hcover : IsFppfCovering B S hS (fun _ : Unit => V.obj) (fun _ => v.hom))
    (f : Z ⟶ X) (hf : f ≫ x = z)
    (localMap : pullback z v ⟶ pullback x v) [IsIso localMap]
    (hfst : localMap ≫ pullback.fst x v = pullback.fst z v ≫ f)
    (hsnd : localMap ≫ pullback.snd x v = pullback.snd z v) : IsIso f := by
  have hcartesian : IsPullback localMap (pullback.fst z v) (pullback.fst x v) f := by
    refine IsPullback.of_right ?_ hfst (IsPullback.of_hasPullback x v).flip
    rw [hsnd, hf]
    exact (IsPullback.of_hasPullback z v).flip
  have hchart : IsIso (pullback.snd f (pullback.fst x v)) :=
    IsIso.of_isIso_fac_left hcartesian.flip.isoPullback_hom_snd
  let K := Topology.precoverage.{u, 0} .fppf B S hS
  let _ : (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget K :=
    isomorphisms_isLocalAtTarget_fppf.{u, 0} B S hS
  have htarget : IsFppfCovering B S hS (fun _ : Unit => (pullback x v).obj)
      (fun _ => (pullback.fst x v).hom) :=
    isFppfCovering_pullback_fst B S hS (fun _ : Unit => V) (fun _ => v) hcover X x
  have hmem : Presieve.ofArrows (fun _ : Unit => pullback x v)
      (fun _ => pullback.fst x v) ∈ K X :=
    ⟨Unit, (fun _ => pullback x v), (fun _ => pullback.fst x v), rfl,
      X.property, (fun _ => (pullback x v).property), htarget⟩
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)) hmem ?_
  rintro W g _ ⟨i⟩
  exact hchart

end AlgebraicGeometry.Space

end
