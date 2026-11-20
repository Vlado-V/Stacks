module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # The fraction field as an away localization of a discrete valuation ring -/

@[expose] public noncomputable section

namespace Stacks.EppTheorem

/-- **The fraction field of a discrete valuation ring is the localisation away from a
uniformizer.** -/
theorem isLocalization_away_of_irreducible
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    {π : B} (hπ : Irreducible π) :
    IsLocalization.Away π L := by
  have hmem : π ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hπ.ne_zero
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := L)
    (nonZeroDivisors B) (Submonoid.powers_le.mpr hmem) ?_).mpr inferInstance
  intro n hn
  obtain ⟨k, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hn) hπ
  refine ⟨π ^ k, ⟨k, rfl⟩, (u⁻¹ : Bˣ), ?_⟩
  rw [mul_comm (u : B), mul_assoc, Units.mul_inv, mul_one]

end Stacks.EppTheorem

end
