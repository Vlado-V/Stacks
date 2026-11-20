module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Ring

/-!
# The tensor functor on the quasicoherent derived category

The ambient derived tensor product restricts to complexes with quasicoherent cohomology.
This construction also serves the monoidal structure and duality comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.K0
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- The derived tensor product of `D_QCoh(𝒪_X)`, the restriction of `- ⊗^L_{𝒪_X} -`. -/
def quasicoherentDerivedTensor (X : AlgebraicSpaces B S hS) :
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
        QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  liftBifunctor (QcohDerived B S hS X) (smallEtaleDerivedTensor B S hS X)
    (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor X K L hK hL)

end AlgebraicGeometry.Space

end
