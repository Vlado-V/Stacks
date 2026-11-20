module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageDuality

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality.TwistedInverseImageDuality

attribute [local instance 10000] HasDerivedCategory.standard

/-- The tensor–internal-Hom bijection is natural in the target. -/
theorem curry_naturality_right (X : Scheme.{u}) (A B : Std X) {Z Z' : Std X} (z : Z ⟶ Z')
    (θ : A ⟶ ((sheafHom X).obj (op B)).obj Z) :
    curry X A B Z' (θ ≫ ((sheafHom X).obj (op B)).map z) = curry X A B Z θ ≫ z :=
  (tensorHomAdjunction X B).homEquiv_naturality_right_symm θ z

end Stacks.Duality.TwistedInverseImageDuality

end
