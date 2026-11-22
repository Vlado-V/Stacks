module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.Etale.PermanenceOfProperties

/-!
# The local ring of an étale algebra over a discrete valuation ring

The local ring at a prime over the closed point gives a local étale extension
of the original discrete valuation ring. The affine algebra has finite prime
spectrum, so the local ring is also étale over that algebra.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Models

/-! ### Shrinking an étale neighbourhood of a discrete valuation ring -/

/-- In a ring with finite spectrum the local ring at a prime is a localization away from a single
element: take the product of elements witnessing, for each prime not contained in the given one,
that it is not contained in it. -/
private theorem exists_isLocalizationAway_atPrime_of_finite_primeSpectrum
    (A : Type*) [CommRing A] [Finite (PrimeSpectrum A)] (p : Ideal A) [p.IsPrime] :
    ∃ f ∉ p, IsLocalization.Away f (Localization.AtPrime p) := by
  classical
  let T := {q : PrimeSpectrum A // ¬ q.asIdeal ≤ p}
  have hex (q : T) : ∃ x : A, x ∈ q.1.asIdeal ∧ x ∉ p :=
    IsConcreteLE.not_le_iff_exists.mp q.2
  choose x hx hxp using hex
  have := Fintype.ofFinite T
  let f := ∏ q : T, x q
  have hfp : f ∉ p := by
    simpa only [f, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]
      using hxp
  have hpow : ∀ s ∈ p.primeCompl, ∃ m ∈ Submonoid.powers f, s ∣ m := by
    intro s hs
    have hf : f ∈ (Ideal.span ({s} : Set A)).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      intro q hq
      have hnot : ¬ q ≤ p := fun hle ↦
        hs (hle (hq.1 (Ideal.subset_span (Set.mem_singleton s))))
      let q' : T := ⟨⟨q, hq.2⟩, hnot⟩
      exact q.mem_of_dvd (Finset.dvd_prod_of_mem x (Finset.mem_univ q')) (hx q')
    obtain ⟨n, hn⟩ := hf
    exact ⟨f ^ n, ⟨n, rfl⟩, Ideal.mem_span_singleton.mp hn⟩
  exact ⟨f, hfp, (IsLocalization.iff_of_le_of_exists_dvd
    (Submonoid.powers f) p.primeCompl (Submonoid.powers_le.mpr hfp) hpow).mpr inferInstance⟩

/-- **The local ring of an étale algebra over a discrete valuation ring above the maximal ideal
is a discrete valuation ring.** It is étale over the base, and the inclusion is an extension of
discrete valuation rings in the sense of Tag 09E4; moreover it is étale over the algebra itself,
being a localization away from a single element.

This is the geometric content of Tag 0AP2 in the form needed to shrink an affine étale
neighbourhood of a discrete valuation ring to a discrete valuation ring. -/
public theorem exists_isDiscreteValuationRing_localizationAtPrime_of_etale
    {R B : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing B] [Algebra R B] [Algebra.Etale R B]
    (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap R B) q = IsLocalRing.closedPoint R) :
    ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal))
      (_ : IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)),
      IsDiscreteValuationRing.IsExtension R (Localization.AtPrime q.asIdeal) ∧
        Algebra.Etale R (Localization.AtPrime q.asIdeal) ∧
        Algebra.Etale B (Localization.AtPrime q.asIdeal) := by
  have : Finite (PrimeSpectrum R) := by
    apply Finite.of_injective (fun y : PrimeSpectrum R ↦ y = ⊥)
    intro y z hyz
    rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top y with hy | hy <;>
      rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top z with hz | hz <;>
      simp_all
  have : Finite (PrimeSpectrum B) := Algebra.QuasiFinite.finite_primeSpectrum R B
  obtain ⟨s, hs, hloc⟩ :=
    exists_isLocalizationAway_atPrime_of_finite_primeSpectrum B q.asIdeal
  let L := Localization.AtPrime q.asIdeal
  have : IsLocalization.Away s L := hloc
  have : Algebra.Etale B L := Algebra.Etale.of_isLocalizationAway s
  have : Algebra.Etale R L := Algebra.Etale.comp R B L
  have hpoint : PrimeSpectrum.comap (algebraMap R L) (IsLocalRing.closedPoint L) =
      IsLocalRing.closedPoint R := by
    rw [IsScalarTower.algebraMap_eq R B L, PrimeSpectrum.comap_comp_apply]
    have hclosed : PrimeSpectrum.comap (algebraMap B L) (IsLocalRing.closedPoint L) = q :=
      PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal L q.asIdeal)
    rw [hclosed]
    exact hq
  have : IsLocalHom (algebraMap R L) :=
    (IsLocalRing.isLocalHom_iff_comap_closedPoint _).mpr hpoint
  have heq : IsLocalRing.maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal :=
    (congrArg PrimeSpectrum.asIdeal hq).symm
  have : q.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) := ⟨heq⟩
  have : IsRegularLocalRing L :=
    (isRegularLocalRing_localization_iff_of_etale (IsLocalRing.maximalIdeal R)
      q.asIdeal).mp inferInstance
  have hpne : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    intro hp
    have hm : π ∈ IsLocalRing.maximalIdeal R := hπ.not_isUnit
    rw [hp] at hm
    exact hπ.ne_zero hm
  have : IsDiscreteValuationRing (Localization.AtPrime (IsLocalRing.maximalIdeal R)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hpne _
  have hdim : ringKrullDim L = 1 := by
    rw [← RingHom.Etale.ringKrullDim_localization_atPrime_eq (f := algebraMap R B)
      (RingHom.etale_algebraMap.mpr inferInstance) (IsLocalRing.maximalIdeal R)
      q.asIdeal heq]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  obtain ⟨hd, hv⟩ := ((isDiscreteValuationRing_tfae L).out 3 1).mp
    (show IsRegularLocalRing L ∧ ringKrullDim L = 1 from ⟨inferInstance, hdim⟩)
  have : IsDomain L := hd
  have : IsDiscreteValuationRing L := hv
  have : Module.FaithfullyFlat R L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨hd, hv, { toFaithfulSMul := inferInstance, toIsLocalHom := inferInstance },
    inferInstance, inferInstance⟩

end Stacks.Models
