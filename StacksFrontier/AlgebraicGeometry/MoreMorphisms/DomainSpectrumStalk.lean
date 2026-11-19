module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-! The stalk of the spectrum of a domain is a domain. -/

@[expose] public noncomputable section

namespace AlgebraicGeometry

universe u

/-- The local ring of the spectrum of a domain at a point is a domain. -/
theorem isDomain_stalk_spec {B : Type u} [CommRing B] [IsDomain B] (b : Spec (.of B)) :
    IsDomain ((Spec (.of B)).presheaf.stalk b) :=
  let : b.asIdeal.IsPrime := b.isPrime
  Function.Injective.isDomain
    ((Spec.stalkIso (.of B) b).commRingCatIsoToRingEquiv : _ →+* Localization.AtPrime b.asIdeal)
    (Spec.stalkIso (.of B) b).commRingCatIsoToRingEquiv.injective

end AlgebraicGeometry

end
