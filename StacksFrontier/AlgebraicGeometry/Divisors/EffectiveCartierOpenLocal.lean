module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FibrePrincipalDictionary

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u

open AlgebraicGeometry

namespace Stacks.Divisors

/-- **Being an effective Cartier divisor is local for the topology of open immersions.**  If a
jointly surjective family of open immersions `qᵢ : Yᵢ ⟶ X` pulls `J` back to effective Cartier
divisors, then `J` is an effective Cartier divisor: a nonzerodivisor generating the ideal of
`J.comap qᵢ` on an affine open `V` of `Yᵢ` transports to the affine open `qᵢ(V)` of `X` along
the isomorphism of rings of sections that an open immersion provides. -/
theorem isEffectiveCartierDivisor_of_forall_comap {X : Scheme.{u}} (J : X.IdealSheafData)
    {ι : Type*} {Y : ι → Scheme.{u}} (q : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (q i)]
    (hq : ∀ x : X, ∃ i, x ∈ Set.range (q i))
    (h : ∀ i, IsEffectiveCartierDivisor (J.comap (q i))) : IsEffectiveCartierDivisor J := by
  refine isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  obtain ⟨i, z, rfl⟩ := hq x
  obtain ⟨V, hzV, -, g, hg, hgen⟩ :=
    Stacks.Blowup.exists_affineOpens_ideal_eq_span_le (J.comap (q i)) (h i) z ⊤ trivial
  have hsurj : Function.Surjective ((q i).appIso (V : (Y i).Opens)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso _).2
  refine ⟨q i ''ᵁ (V : (Y i).Opens), V.2.image_of_isOpenImmersion (q i), ⟨z, hzV, rfl⟩,
    ((q i).appIso (V : (Y i).Opens)).inv g,
    isRegular_ringEquiv ((q i).appIso (V : (Y i).Opens)).symm.commRingCatIsoToRingEquiv hg, ?_⟩
  rw [← Ideal.map_comap_of_surjective _ hsurj
      (J.ideal ⟨q i ''ᵁ (V : (Y i).Opens), V.2.image_of_isOpenImmersion (q i)⟩),
    ← Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J (q i) V, hgen, Ideal.map_span,
    Set.image_singleton]

end Stacks.Divisors

end
