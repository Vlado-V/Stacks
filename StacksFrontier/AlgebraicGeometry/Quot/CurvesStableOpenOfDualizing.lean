module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableSmoothGenusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenus
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOfFieldFibres
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.AffineBase
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableFibreDualizing

/-!
# The open substack of stable curves from the relative dualizing sheaf (towards Stacks 0E76)

The source proves that `Curves^{stable} ⊂ Curves` is open (Stacks 0E76) by reducing to prestable
families (Stacks 0E6U) and then cutting out, over the base `S` of a prestable family
`f : X → S`, the open where the relative dualizing sheaf `ω_{X/S}` (Stacks 0E6R) is relatively
ample (Stacks 0D3D): by Stacks 0E74 a fibre `X_s` is stable exactly when `ω_{X/S}` restricted
to it, which is `ω_{X_s}`, is ample, and that condition is insensitive to the ground field.

This file carries out that argument. Over a prestable family `G` with a relative dualizing sheaf
`ω`, Stacks 0D3D gives an open subspace `V` of the base of `G` such that a morphism `S' → S`
factors through `V` exactly when over every field-valued point of `S'` the fibre carries the
pullback of `ω` as a relatively ample module. For a family `F` mapping to `G`, the fibre of `F`
over a field-valued point is a fibre of `G`, on which `ω` restricts to the dualizing sheaf; a
nodal proper curve over a field with `H⁰ = k` is stable exactly when its dualizing sheaf is
ample (Stacks 0E3P and its converse, from Stacks 0E63, 0E64, 0C19 and 0B5Y), and over the
spectrum of a field relative ampleness is ampleness (Stacks 01VT). So `F` is stable exactly when
its base maps into `V`.

## Main results

* `topologicalKrullDim_eq_one_and_hasAtWorstNodalSingularities_of_isAtWorstNodal`:
  a scheme at-worst-nodal of relative dimension one over a field with `H⁰ = k` has dimension one
  and at-worst-nodal singularities (Stacks 0C59 over the one-point base).
* `AlgebraicGeometry.CurveFamily.isProper_and_dim_and_bijective_and_nodal_fibre`: the fibre of a
  prestable family over a field-valued point is a proper nodal curve with `H⁰ = k`.
* `AlgebraicGeometry.CurveFamily.hasGenusTwoNoRationalTailNoRationalBridge_fibre_iff`: that fibre
  is stable exactly when the restriction of a relative dualizing sheaf to it is relatively ample.
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_dualizing`: condition (o) of
  Stacks 0E0E for `Curves^{stable}` (the openness of Stacks 0E76).
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_dualizing`: condition (o) for
  `𝓜̄_g` (the openness part of Stacks 0E78).

## Implementation notes

Nothing here carries a `stacks` attribute. Stacks 0D3D, read on field-valued points, is
`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_fieldFibres_of_isProper`, and on a
fibre presented by a scheme Stacks 0D32 is
`AlgebraicGeometry.Space.isRelativelyAmple_fibre_of_scheme`. The two main results take as
explicit hypotheses:

* `h0E6I`: condition (o) for `Curves^{h0,1}` (Stacks 0E6I), which gives condition (o) for
  `Curves^{prestable}` (Stacks 0E6U);
* `hω`: every prestable family has a relative dualizing sheaf
  (`AlgebraicGeometry.CurveFamily.IsRelativeDualizingSheaf`, Stacks 0E6P, 0E6Q, 0E6R);
* for the genus statement, `h2` and `h3`: parts (2) and (3) of Stacks 0E1J.

The hypothesis `hrel` of `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_isH01` is not
needed: the stable locus is cut out over each prestable family directly
(`AlgebraicGeometry.IsOpenCurvesLocus.of_points_of_isOpenCurvesLocus`).

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **Stable fibres of a family mapping to a prestable one, read through `ω`.** Let `a : F ⟶ G` be
a morphism of families of curves with `G` prestable, `ω` a relative dualizing sheaf of `G`, and
`t` a field-valued point of the base of `F`. Some presentation of the fibre of `F` over `t` has
genus at least two and neither a rational tail nor a rational bridge exactly when some fibre of
`G` over the image of `t` carries the pullback of `ω` as a module ample relative to the fibre in
the sense of Stacks 0D31 — the fibre condition of Stacks 0D3D read on field-valued points.

A presentation of the fibre of `F` is one of the fibre of `G`, the square of `a` being cartesian,
and on it ampleness in the sense of Stacks 0D31 is relative ampleness in the sense of schemes
(Stacks 0D32); conversely a fibre of `G` ample in the sense of Stacks 0D31 is representable, and
its base change along the identity of `Spec k` is a scheme presenting the fibre of `F`. Both
are then compared by
`AlgebraicGeometry.CurveFamily.hasGenusTwoNoRationalTailNoRationalBridge_fibre_iff`. -/
theorem exists_fibre_hasGenusTwo_iff_exists_fibre_isRelativelyAmple {F G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G)
    {ω : Space.Modules.{u, u} B integerBase hZ G.total.1 G.total.2}
    (hω : G.IsRelativeDualizingSheaf B hZ ω) (a : F ⟶ G)
    (t : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj) :
    (∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ t.siteObject)
        (q : yoneda.obj V ⟶ F.total.obj),
        IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm t.value) ∧
          HasGenusTwoNoRationalTailNoRationalBridge t.carrier
            ((BigFppfOver.toScheme B integerBase hZ).map v)) ↔
      ∃ (X'' : AlgebraicSpaces B integerBase hZ) (p'' : X'' ⟶ G.total)
        (f'' : X'' ⟶ schemeSpace t.siteObject),
        IsPullback p'' f'' G.toBase
            (ObjectProperty.homMk (yonedaEquiv.symm t.value) ≫ schemeSpaceMap a.baseMap) ∧
          Space.IsRelativelyAmple B integerBase hZ f''
            ((Space.modulePullback B integerBase hZ p'').obj ω) := by
  let p := Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap a.baseMap).hom t
  have hval : yonedaEquiv.symm p.value =
      yonedaEquiv.symm t.value ≫ (schemeSpaceMap a.baseMap).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  have hsqa := AlgebraicSpaces.isPullback_hom B integerBase hZ a.cartesian
  constructor
  · rintro ⟨V, v, q, hq, hst⟩
    have hqt : IsPullback (q ≫ a.totalMap.hom) (yoneda.map v) G.toBase.hom
        (yonedaEquiv.symm t.value ≫ (schemeSpaceMap a.baseMap).hom) := hq.paste_horiz hsqa
    have hqp : IsPullback (q ≫ a.totalMap.hom) (yoneda.map v) G.toBase.hom
        (yonedaEquiv.symm p.value) :=
      hval ▸ hqt
    obtain ⟨hinv, hamp⟩ :=
      (hasGenusTwoNoRationalTailNoRationalBridge_fibre_iff (p := p) (v := v) hG hω hqp).1 hst
    exact ⟨schemeSpace V, ObjectProperty.homMk (q ≫ a.totalMap.hom), schemeSpaceMap v,
      Space.isPullback_homMk B integerBase hZ G.total.property (schemeSpace t.siteObject).property
        (schemeSpace G.base).property (schemeSpace V).property hqt,
      Space.isRelativelyAmple_fibre_of_scheme hω.1 t V v (q ≫ a.totalMap.hom) hinv hamp⟩
  · rintro ⟨X'', p'', f'', hsq, hamp⟩
    have hrep : yoneda.relativelyRepresentable f''.hom := hamp.1
    have hU := hrep.isPullback (𝟙 (yoneda.obj t.siteObject))
    obtain ⟨hinv, hrel⟩ := hamp.2 t.siteObject _ (𝟙 _) _ _ hU
    have e := Space.baseChangeModuleCompIso B integerBase hZ p'' ω
      (hrep.pullback (𝟙 (yoneda.obj t.siteObject))) (hrep.fst (𝟙 (yoneda.obj t.siteObject)))
    have hinv' : Stacks.Ample.IsInvertibleModule
        ((BigFppfOver.toScheme B integerBase hZ).obj (hrep.pullback (𝟙 (yoneda.obj t.siteObject))))
        (Space.baseChangeModule B integerBase hZ ω (hrep.pullback (𝟙 (yoneda.obj t.siteObject)))
          (hrep.fst (𝟙 (yoneda.obj t.siteObject)) ≫ p''.hom)) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
    have hrel' := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e.symm).mp hrel
    have hGt : IsPullback (hrep.fst (𝟙 (yoneda.obj t.siteObject)) ≫ p''.hom)
        (yoneda.map (hrep.snd (𝟙 (yoneda.obj t.siteObject)))) G.toBase.hom
        (yonedaEquiv.symm t.value ≫ (schemeSpaceMap a.baseMap).hom) := by
      have h := hU.paste_horiz (AlgebraicSpaces.isPullback_hom B integerBase hZ hsq)
      exact (congrArg (IsPullback _ _ G.toBase.hom) (Category.id_comp _)).mp h
    have hGp : IsPullback (hrep.fst (𝟙 (yoneda.obj t.siteObject)) ≫ p''.hom)
        (yoneda.map (hrep.snd (𝟙 (yoneda.obj t.siteObject)))) G.toBase.hom
        (yonedaEquiv.symm p.value) :=
      hval ▸ hGt
    have hst := (hasGenusTwoNoRationalTailNoRationalBridge_fibre_iff (p := p)
      (v := hrep.snd (𝟙 (yoneda.obj t.siteObject))) hG hω hGp).2 ⟨hinv', hrel'⟩
    have hw : (hrep.fst (𝟙 (yoneda.obj t.siteObject)) ≫ p''.hom) ≫ G.toBase.hom =
        (yoneda.map (hrep.snd (𝟙 (yoneda.obj t.siteObject))) ≫ yonedaEquiv.symm t.value) ≫
          (schemeSpaceMap a.baseMap).hom :=
      hGt.w.trans (Category.assoc _ _ _).symm
    exact ⟨_, hrep.snd (𝟙 (yoneda.obj t.siteObject)), hsqa.lift _ _ hw,
      IsPullback.of_right (by rwa [hsqa.lift_fst]) (hsqa.lift_snd _ _ _) hsqa, hst⟩

end CurveFamily

variable (B hZ) in
/-- **Condition (o) for `𝓜̄ = Curves^{stable}`** (the openness of Stacks 0E76), from condition (o)
for `Curves^{h0,1}` (`h0E6I`, Stacks 0E6I), the existence of a relative dualizing sheaf on every
prestable family (`hω`, Stacks 0E6R). The openness of the relatively ample locus, read on
field-valued points, is Stacks 0D3D
(`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_fieldFibres_of_isProper`).

By Stacks 0E6U it suffices to cut out the stable locus over a prestable family `G`
(`AlgebraicGeometry.IsOpenCurvesLocus.of_points_of_isOpenCurvesLocus`): Stacks 0D3D applied to
`G` and its relative dualizing sheaf `ω` gives an open subspace `V` of the base, through which a
morphism `S' → S` factors exactly when over every field-valued point of `S'` the fibre carries the
pullback of `ω` as a relatively ample module; and a family mapping to `G` is prestable, and its
fibres are stable exactly when that holds over its base
(`AlgebraicGeometry.CurveFamily.exists_fibre_hasGenusTwo_iff_exists_fibre_isRelativelyAmple`,
Stacks 0E74). -/
theorem isOpenCurvesLocus_isStableCurveFamily_of_dualizing
    (h0E6I : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ))
    (hω : ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X →
      ∃ ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2,
        X.IsRelativeDualizingSheaf B hZ ω) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ) := by
  refine IsOpenCurvesLocus.of_points_of_isOpenCurvesLocus
    (isOpenCurvesLocus_isPrestableCurveFamily_of h0E6I) (fun _ h => h.1) fun G hG => ?_
  obtain ⟨ω, hωG⟩ := hω G hG
  obtain ⟨V, hV, -, hVpts⟩ :=
    Space.exists_isOpenSubspace_factors_iff_fieldFibres_of_isProper G.proper hωG.1
  refine ⟨Set.range (Space.pointsMap B integerBase hZ V.toFunctor V.ι),
    Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B integerBase hZ
      (schemeSpace G.base).property V hV, fun F a => ?_⟩
  rw [← Space.factorsThrough_openSubspace_iff_points B integerBase hZ
    (schemeSpace G.base).property (schemeSpace F.base).property V hV
    (schemeSpaceMap a.baseMap).hom, hVpts (schemeSpaceMap a.baseMap),
    CurveFamily.isStableCurveFamily_iff,
    and_iff_right (CurveFamily.isPrestableCurveFamily_of_hom a hG)]
  exact forall_congr' fun t =>
    CurveFamily.exists_fibre_hasGenusTwo_iff_exists_fibre_isRelativelyAmple hG hωG a t

variable (B hZ) in
/-- **Condition (o) for `𝓜̄_g`** (the openness part of Stacks 0E78): `𝓜̄_g = 𝓜̄ ∩ Curves_g`, from
condition (o) for `𝓜̄`
(`AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_dualizing`, from `h0E6I` and `hω`)
and for `Curves_g`
(`AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of_isH01`, from `h0E6I` and parts (2)
and (3) of Stacks 0E1J, `h2` and `h3`), a stable family being in `Curves^{h0,1}`. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_dualizing (g : ℕ)
    (h0E6I : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ))
    (hω : ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X →
      ∃ ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2,
        X.IsRelativeDualizingSheaf B hZ ω)
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g) :=
  ((isOpenCurvesLocus_isStableCurveFamily_of_dualizing B hZ h0E6I hω).and
      (isOpenCurvesLocus_isGenusCurveFamily_of_isH01 B hZ g h0E6I h2 h3)).of_iff fun _ =>
    ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, isH01CurveFamily_of_isPrestableCurveFamily h.1.1, h.2⟩⟩

end AlgebraicGeometry

end
