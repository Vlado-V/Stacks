module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPresheafCanonicalModel
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsOpenInHilbert
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-! The graph map and its open immersion in an already supplied Hilbert model. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- The ambient space `Z ×_Q X` of the graph construction is of finite presentation over `Q` when
`z` and `x` are: its structure morphism is the base change of `x` along `z` followed by `z`. -/
theorem isFinitePresentation_graphAmbientMap (hz : IsFinitePresentation B S hS z)
    (hx : IsFinitePresentation B S hS x) :
    IsFinitePresentation B S hS (graphAmbientMap B S hS z x hZ hX hQ).hom := by
  have hfst : IsFinitePresentation B S hS (pullback.fst z x) := by
    have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk z : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)
      (ObjectProperty.homMk x : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)
    exact (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hpb.flip hx
  exact isFinitePresentation_comp B S hS (graphAmbient B S hS z x hZ hX hQ).property hZ hQ
    (pullback.fst z x) z hfst hz

/-- The ambient space `Z ×_Q X` of the graph construction is separated over `Q` when `z` and `x`
are: its structure morphism is the base change of `x` along `z` followed by `z`. -/
theorem isSeparated_graphAmbientMap (hz : IsSeparated B S hS z) (hx : IsSeparated B S hS x) :
    IsSeparated B S hS (graphAmbientMap B S hS z x hZ hX hQ).hom :=
  isSeparated_comp B S hS (pullback.fst z x) z
    (isSeparated_pullback_fst_of_snd B S hS x z (isSeparated_pullback B S hS x z hx)) hz

/-- The graph transformation of Stacks 0D1A, valued in a small model of the Hilbert presheaf of
the ambient space `Z ×_Q X` over `Q`. -/
def morToHilbertModel (M : HilbertPresheafModel (graphAmbientMap B S hS z x hZ hX hQ))
    (hsep : IsSeparated B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z) :
    relativeHom B S hS Z X Q z x hZ hX hQ ⟶ M.presheaf :=
  M.mapFrom (graphTransformation hZ hX hQ hsep hfp hflat hproper)

/-- The realisation of `Mor_Q(Z, X)` in a model of the Hilbert presheaf lies over the projection
of `Mor_Q(Z, X)` to `Q`: both read off the first component of a relative morphism. -/
theorem morToHilbertModel_comp_toBase
    (M : HilbertPresheafModel (graphAmbientMap B S hS z x hZ hX hQ))
    (hsep : IsSeparated B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z) :
    morToHilbertModel z x hZ hX hQ M hsep hfp hflat hproper ≫ M.toBase =
      relativeHomProjection B S hS Z X Q z x hZ hX hQ := by
  ext T s
  cases T
  rename_i T
  refine (M.toBase_mapFrom_app_apply
    (graphTransformation hZ hX hQ hsep hfp hflat hproper) (Opposite.op T) s).trans ?_
  rw [hilbertPresheafToBase_app_apply, graphTransformation_app_toBase]
  exact ((relativeHomData B S hS Z X Q z x hZ hX hQ).projection_sections T s).symm

/-- **Stacks 0D1B** for a model of the Hilbert presheaf: the realisation of `Mor_Q(Z, X)` in the
model is an open immersion. -/
theorem morToHilbertModel_isOpenImmersion
    (M : HilbertPresheafModel (graphAmbientMap B S hS z x hZ hX hQ))
    (hsep : IsSeparated B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z) :
    IsOpenImmersion B S hS (morToHilbertModel z x hZ hX hQ M hsep hfp hflat hproper) :=
  M.relative_mapFrom _ _
    (graphTransformation_relative_isOpenImmersion z x hZ hX hQ hsep hfp hflat hproper)

end AlgebraicGeometry.Space

end
