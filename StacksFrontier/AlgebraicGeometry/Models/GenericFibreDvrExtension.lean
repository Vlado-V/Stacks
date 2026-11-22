module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.AlgebraicGeometry.Models.Basic

/-!
# The generic point under a local extension of DVRs

For an injective local map `R → S` of discrete valuation rings, the pullback
of the generic point of `Spec R` along `Spec S → Spec R` is the generic point
of `Spec S`. Both projections are the maps induced by the corresponding
homomorphisms of rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Models

universe u

variable {R S K L : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra S L] [IsFractionRing S L]

/-- The map on fraction fields associated to an injective ring homomorphism. -/
def fractionRingMapOfInjective (f : R →+* S) (hf : Function.Injective f) : K →+* L :=
  IsFractionRing.lift (g := (algebraMap S L).comp f) ((IsFractionRing.injective S L).comp hf)

private theorem range_genericFiberSpec :
    Set.range (Spec.algebraMap R K) = ({⊥} : Set (PrimeSpectrum R)) := by
  have hbot : Spec.algebraMap R K (⊥ : PrimeSpectrum K) = (⊥ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subsingleton.elim y (⊥ : PrimeSpectrum K), hbot]
    exact Set.mem_singleton _
  · intro hx
    exact ⟨(⊥ : PrimeSpectrum K), hbot.trans (Set.mem_singleton_iff.mp hx).symm⟩

variable [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]

private theorem dvr_top_ne_bot (T : Type u) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] : (⊤ : PrimeSpectrum T) ≠ ⊥ := fun h =>
  IsDiscreteValuationRing.not_a_field T (congrArg PrimeSpectrum.asIdeal h)

private theorem comap_eq_bot_iff_of_dvr_localHom (f : R →+* S) [IsLocalHom f]
    (hf : Function.Injective f) (x : PrimeSpectrum S) :
    PrimeSpectrum.comap f x = ⊥ ↔ x = ⊥ := by
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top x with rfl | rfl
  · exact iff_of_true (PrimeSpectrum.ext (Ideal.comap_bot_of_injective f hf)) rfl
  · have hc : PrimeSpectrum.comap f (⊤ : PrimeSpectrum S) = ⊤ :=
      IsLocalRing.comap_closedPoint f
    rw [hc]
    exact iff_of_false (dvr_top_ne_bot R) (dvr_top_ne_bot S)

set_option backward.isDefEq.respectTransparency false in
/-- The generic-point square of a local injective extension of DVRs is cartesian. -/
theorem isPullback_genericFiberSpec_of_localHom (f : R →+* S) [IsLocalHom f]
    (hf : Function.Injective f) :
    IsPullback (Spec.map (CommRingCat.ofHom (fractionRingMapOfInjective (K := K) (L := L) f hf)))
      (Spec.algebraMap S L) (Spec.algebraMap R K) (Spec.map (CommRingCat.ofHom f)) := by
  let jR := Spec.algebraMap R K
  let jS := Spec.algebraMap S L
  let g := Spec.map (CommRingCat.ofHom f)
  let k := Spec.map (CommRingCat.ofHom (fractionRingMapOfInjective (K := K) (L := L) f hf))
  have hring : (fractionRingMapOfInjective (K := K) (L := L) f hf).comp (algebraMap R K) =
      (algebraMap S L).comp f :=
    RingHom.ext fun r => IsFractionRing.lift_algebraMap (g := (algebraMap S L).comp f)
      ((IsFractionRing.injective S L).comp hf) r
  have hsq : CommSq k jS jR g := ⟨by
    change Spec.map (CommRingCat.ofHom (fractionRingMapOfInjective f hf)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) =
      Spec.map (CommRingCat.ofHom (algebraMap S L)) ≫ Spec.map (CommRingCat.ofHom f)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      hring]⟩
  let : IsOpenImmersion jR := genericFiberSpec_isOpenImmersion
  let : IsOpenImmersion jS := genericFiberSpec_isOpenImmersion
  have hrange : Set.range (pullback.snd jR g) = Set.range jS := by
    rw [IsOpenImmersion.range_pullbackSnd]
    ext x
    change g x ∈ Set.range jR ↔ x ∈ Set.range jS
    have hR : Set.range jR = ({⊥} : Set (PrimeSpectrum R)) := range_genericFiberSpec
    have hS : Set.range jS = ({⊥} : Set (PrimeSpectrum S)) := range_genericFiberSpec
    rw [hR, hS]
    simp only [Set.mem_singleton_iff]
    exact comap_eq_bot_iff_of_dvr_localHom f hf x
  let e := (IsOpenImmersion.isoOfRangeEq (pullback.snd jR g) jS hrange).symm
  have hsnd : e.hom ≫ pullback.snd jR g = jS :=
    IsOpenImmersion.isoOfRangeEq_inv_fac (pullback.snd jR g) jS hrange
  have hfst : e.hom ≫ pullback.fst jR g = k := by
    rw [← cancel_mono jR, Category.assoc, pullback.condition, ← Category.assoc, hsnd, hsq.w]
  exact IsPullback.of_iso_pullback hsq e hfst hsnd

end Stacks.Models

end
