module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableFibreDualizing
public import StacksFrontier.AlgebraicGeometry.Quot.UniqueStableModelsReduction
public import StacksFrontier.AlgebraicGeometry.AmpleFibreLimit.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.FiniteOrder
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyOfIsPullback
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.RestrictBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings

/-!
# The total space of a stable family of curves is a scheme

Let `f : X → S` be a stable family of curves (Stacks 0E75) and `ω = ω_{X/S}` its relative
dualizing sheaf (Stacks 0E6R). By Stacks 0E74 the module `ω` is ample relative to `f`: over every
point `s` of `S` the fibre `X_s` is stable, so `ω_{X_s}` is ample (Stacks 0E3P), and the locus of
the base over which `ω` is relatively ample is open (Stacks 0D3D) and contains every point. A
morphism of algebraic spaces carrying a relatively ample module is representable (Stacks 0D31,
0D32), and `S` is a scheme, so `X` is a scheme.

In particular the total space of a stable family of curves over the spectrum of a discrete
valuation ring is a scheme, which is `AlgebraicGeometry.StableFamilyTotalIsScheme`, the input of
the reduction of Stacks 0E97 for algebraic spaces to the case of schemes.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_iso_schemeSpace_total_of_isRelativelyAmple`: a family of
  curves whose structure morphism carries a relatively ample module has a scheme as total space.
* `AlgebraicGeometry.CurveFamily.isRelativelyAmple_of_isStableCurveFamily`: the relative
  dualizing sheaf of a stable family of curves is relatively ample (Stacks 0E74, (1) implies (2),
  over the whole base).
* `AlgebraicGeometry.CurveFamily.exists_iso_schemeSpace_total_of_isStableCurveFamily`: the total
  space of a stable family of curves is a scheme.
* `AlgebraicGeometry.stableFamilyTotalIsScheme_of`: `AlgebraicGeometry.StableFamilyTotalIsScheme`.

## Implementation notes

Nothing here carries a `stacks` attribute. One result is not yet available and is an explicit
hypothesis, in the shape of `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_dualizing`:

* `hω`: every prestable family of curves has a relative dualizing sheaf
  (`AlgebraicGeometry.CurveFamily.IsRelativeDualizingSheaf`; Stacks 0E6P, 0E6Q, 0E6R).

Stacks 0D3D enters through `AlgebraicGeometry.Space.isRelativelyAmple_of_isProper_of_fieldFibres`.
The fibrewise ampleness is
`AlgebraicGeometry.CurveFamily.exists_fibre_hasGenusTwo_iff_exists_fibre_isRelativelyAmple`
(Stacks 0E74 on one fibre), applied to the identity of the family.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **A family of curves with a relatively ample module has a scheme as total space.** If the
structure morphism `X ⟶ S` of a family of curves carries a module ample relative to it in the
sense of Stacks 0D31, then `X` is a scheme of the site: the morphism is representable and its
target `S` is a scheme (Stacks 0D32). -/
theorem exists_iso_schemeSpace_total_of_isRelativelyAmple (F : CurveFamily B hZ)
    {L : Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2}
    (hL : Space.IsRelativelyAmple B integerBase hZ F.toBase L) :
    ∃ (X : Scheme.{u}) (hX : B.Contains X),
      Nonempty (F.total ≅ schemeSpace (integerSiteObject B hZ hX)) := by
  have : (schemeSpace F.base).1.IsRepresentable :=
    inferInstanceAs (yoneda.obj F.base).IsRepresentable
  have : F.total.1.IsRepresentable := hL.isRepresentable
  obtain ⟨T, ⟨e⟩⟩ : ∃ T : BigFppfOver B integerBase hZ, Nonempty (F.total ≅ schemeSpace T) :=
    ⟨F.total.1.reprX, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso F.total.1.reprW.symm⟩⟩
  obtain ⟨⟨T, hT⟩, ⟨⟨⟩⟩, tHom⟩ := T
  obtain rfl : tHom = ObjectProperty.homMk (specULiftZIsTerminal.from _) :=
    ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _)
  exact ⟨T, hT, ⟨e⟩⟩

/-- Relative ampleness descends from the étale scheme charts of a curve family. -/
private theorem isRelativelyAmple_of_etaleSchemeCharts (F : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2)
    (hL : Stacks.SheafOfModules.IsInvertible
      (Space.structurePresheaf B integerBase hZ F.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ F.total.1 F.total.2).O)).property L)
    (hchart : ∀ (U Z : BigFppfOver B integerBase hZ) (φ : U ⟶ F.base) (q : Z ⟶ U)
      (p : schemeSpace Z ⟶ F.total),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) →
      IsPullback p (schemeSpaceMap q) F.toBase (schemeSpaceMap φ) →
      Space.IsRelativelyAmple B integerBase hZ (schemeSpaceMap q)
        ((Space.modulePullback B integerBase hZ p).obj L)) :
    Space.IsRelativelyAmple B integerBase hZ F.toBase L := by
  classical
  have hcharts := C1590Private.hasEtaleLocalSchemeCharts B hZ F
  choose U Z φ q p hetale hrange hpullback using hcharts
  have hcover := Space.isEtaleCovering_yoneda_of_etale B integerBase hZ U φ hetale
    (fun x => ⟨x, hrange x⟩)
  have hfpqc := Space.isFpqcCovering_of_isEtaleCovering B integerBase hZ _ _ hcover
  exact (Space.isRelativelyAmple_iff_forall_isRelativelyAmple_of_isFpqcCovering
    hpullback L hL hfpqc).2 fun x => hchart (U x) (Z x) (φ x) (q x) (p x) (hetale x) (hpullback x)

/-- On a scheme chart of a stable family, relative ampleness follows from the ampleness
of the dualizing module on the residue-field fibres of the chart. -/
private theorem isRelativelyAmple_stable_schemeChart {F : CurveFamily B hZ}
    (hF : IsStableCurveFamily B hZ F)
    {ω : Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2}
    (hω : F.IsRelativeDualizingSheaf B hZ ω)
    {U Z : BigFppfOver B integerBase hZ} (φ : U ⟶ F.base) (q : Z ⟶ U)
    (p : schemeSpace Z ⟶ F.total)
    (hp : IsPullback p (schemeSpaceMap q) F.toBase (schemeSpaceMap φ)) :
    Space.IsRelativelyAmple B integerBase hZ (schemeSpaceMap q)
      ((Space.modulePullback B integerBase hZ p).obj ω) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  let G := C1590Private.curveFamilyOfIsPullback F φ p (schemeSpaceMap q) hp
  let a : G ⟶ F := C1590Private.curveFamilyOfIsPullbackHom F φ p (schemeSpaceMap q) hp
  have hG := isStableCurveFamily_of_hom a hF
  let L' := (Space.modulePullback B integerBase hZ p).obj ω
  have hL' : G.IsRelativeDualizingSheaf B hZ L' := hω.of_hom a
  let L := Space.baseChangeModule B integerBase hZ L' Z (𝟙 _)
  letI hL : Stacks.Ample.IsInvertibleModule (T.obj Z) L :=
    Space.isInvertibleModule_baseChangeModule L' hL'.1 Z (𝟙 _)
  have : IsProper (T.map q) := by
    have : (MorphismProperty.inverseImage
        (@IsProper.{u} : MorphismProperty Scheme.{u}) T).IsStableUnderBaseChange :=
      ⟨fun hsq hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsProper) (hsq.map T) hg⟩
    exact (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@IsProper.{u} : MorphismProperty Scheme.{u}) T)).mp
      ((Space.presheaf_isProper_iff B integerBase hZ (yoneda.map q)
        (isAlgebraicSpace_yoneda B integerBase hZ Z)
        (isAlgebraicSpace_yoneda B integerBase hZ U)
        (Functor.relativelyRepresentable.map yoneda q)).mp G.proper)
  have hAmple : Stacks.RelativeAmple.IsRelativelyAmple (T.map q) L := by
    refine Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_of_forall_exists_isRelativelyAmple
      (f := T.map q) (L := L) inferInstance (fun t => ?_)
    let k : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U) :=
      { carrier := (T.obj U).residueField t
        contained := B.residueField_spec_contains U.left.2 t
        toBase := (T.obj U).fromSpecResidueField t ≫ U.hom.1
        value := Space.residueFieldMap B integerBase hZ U t _ }
    obtain ⟨V, v, j, hj, hstable⟩ := hG.2 k
    obtain ⟨hVinv, hVrel⟩ :=
      (hasGenusTwoNoRationalTailNoRationalBridge_fibre_iff hG.1 hL' hj).mp hstable
    let vK : V ⟶ k.siteObject := v
    have : IsAffine (T.obj k.siteObject) := inferInstanceAs (IsAffine (Spec (.of k.carrier)))
    have : Subsingleton (T.obj k.siteObject) :=
      inferInstanceAs (Subsingleton (Spec (.of k.carrier)))
    let jZ : yoneda.obj V ⟶ yoneda.obj Z := j
    let r : V ⟶ Z := yoneda.preimage jZ
    have hr : yoneda.map r = jZ := yoneda.map_preimage jZ
    let κ : k.siteObject ⟶ U := k.value
    have hk : yonedaEquiv.symm k.value = yoneda.map κ := by
      ext W f
      rfl
    have hj' : IsPullback (yoneda.map r) (yoneda.map v) (yoneda.map q) (yoneda.map κ) := by
      rw [hr, ← hk]
      exact hj
    have hcomm : r ≫ q = v ≫ κ := by
      apply yoneda.map_injective
      rw [yoneda.map_comp r q, yoneda.map_comp v κ]
      exact hj'.w
    have hsite : IsPullback r v q κ := IsPullback.of_map yoneda hcomm hj'
    have hfibre : IsPullback (T.map r) (T.map v) (T.map q)
        ((T.obj U).fromSpecResidueField t) := hsite.map T
    let e := hfibre.isoPullback
    have he : e.hom ≫ (T.map q).fiberι t = T.map r := hfibre.isoPullback_hom_fst
    obtain ⟨eL⟩ := Space.nonempty_baseChangeModule_baseChange_of_isInvertible L' hL'.1 Z V (𝟙 _) r
    have hjmap : yoneda.map r ≫ (𝟙 (yoneda.obj Z)) = j := (Category.comp_id _).trans hr
    let eL' : Space.baseChangeModule B integerBase hZ L' V j ≅ pullbackModule (T.map r) L :=
      eqToIso (congrArg (Space.baseChangeModule B integerBase hZ L' V) hjmap.symm) ≪≫ eL
    have hV : Stacks.Ample.IsAmple (T.obj V) (pullbackModule (e.hom ≫ (T.map q).fiberι t) L) := by
      rw [he]
      letI : Stacks.Ample.IsInvertibleModule (T.obj V)
          (Space.baseChangeModule B integerBase hZ L' V j) := hVinv
      have hrel : Stacks.RelativeAmple.IsRelativelyAmple (T.map vK)
          (Space.baseChangeModule B integerBase hZ L' V j) := hVrel
      exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eL').mp
        ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
          ((Scheme.Modules.isRelativelyAmple_iff_isAmple (T.map vK) _).mp hrel))
    have hLf : Stacks.Ample.IsInvertibleModule ((T.map q).fiber t)
        (pullbackModule ((T.map q).fiberι t) L) := inferInstance
    have hf : Stacks.Ample.IsAmple ((T.map q).fiber t) (pullbackModule ((T.map q).fiberι t) L) :=
      @Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isIso _ _ e.hom _ _ hLf
        ((Stacks.RelativeAmpleRestrictBase.isAmple_pullbackModule_comp_iff _ _ _).mpr hV)
    exact Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre (T.map q) L t hf
  refine Space.isRelativelyAmple_of_exists_scheme _ L' hL'.1 U (Iso.refl _) ⟨Z, Iso.refl _, ?_⟩
  let q' : Z ⟶ U := yoneda.preimage ((Iso.refl (yoneda.obj Z)).hom ≫
      (schemeSpaceMap q).hom ≫ (Iso.refl (schemeSpace U).obj).hom)
  have hq : q' = q := by
    apply yoneda.map_injective
    unfold q'
    rw [yoneda.map_preimage]
    change 𝟙 _ ≫ yoneda.map q ≫ 𝟙 _ = yoneda.map q
    simp
  refine ⟨hL, ?_⟩
  change Stacks.RelativeAmple.IsRelativelyAmple (T.map q') L
  exact hq.symm ▸ hAmple

/-- **The relative dualizing sheaf of a stable family of curves is relatively ample** (Stacks
0E74, (1) implies (2), over the whole base). Let `F` be a stable family of curves and `ω` a
relative dualizing sheaf of `F`. Then `ω` is ample relative to the structure morphism of `F`.

Use the étale scheme charts of the family to read the residue-field ampleness on
proper morphisms of schemes. Relative ampleness descends from these charts. -/
theorem isRelativelyAmple_of_isStableCurveFamily {F : CurveFamily B hZ}
    (hF : IsStableCurveFamily B hZ F)
    {ω : Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2}
    (hω : F.IsRelativeDualizingSheaf B hZ ω) :
    Space.IsRelativelyAmple B integerBase hZ F.toBase ω :=
  F.isRelativelyAmple_of_etaleSchemeCharts ω hω.1
    (fun _ _ φ q p _ hp => isRelativelyAmple_stable_schemeChart hF hω φ q p hp)

/-- **The total space of a stable family of curves is a scheme.** Let `F` be a stable family of
curves over a scheme `S`. Its relative dualizing sheaf (`hω`) is relatively ample
(`AlgebraicGeometry.CurveFamily.isRelativelyAmple_of_isStableCurveFamily`, from Stacks 0E74 and
0D3D), so the total space of `F` is a scheme of the site
(`AlgebraicGeometry.CurveFamily.exists_iso_schemeSpace_total_of_isRelativelyAmple`). -/
theorem exists_iso_schemeSpace_total_of_isStableCurveFamily {F : CurveFamily B hZ}
    (hF : IsStableCurveFamily B hZ F)
    (hω : ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X →
      ∃ ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2,
        X.IsRelativeDualizingSheaf B hZ ω) :
    ∃ (X : Scheme.{u}) (hX : B.Contains X),
      Nonempty (F.total ≅ schemeSpace (integerSiteObject B hZ hX)) := by
  obtain ⟨ω, hωF⟩ := hω F hF.1
  exact F.exists_iso_schemeSpace_total_of_isRelativelyAmple
    (isRelativelyAmple_of_isStableCurveFamily hF hωF)

end CurveFamily

variable (B hZ) in
/-- **The total space of a stable family of curves over a discrete valuation ring is a scheme**
(`AlgebraicGeometry.StableFamilyTotalIsScheme`), from the existence of relative dualizing sheaves
(`hω`, Stacks 0E6R): it is
`AlgebraicGeometry.CurveFamily.exists_iso_schemeSpace_total_of_isStableCurveFamily` over the
spectrum of the ring. -/
theorem stableFamilyTotalIsScheme_of (g : ℕ)
    (hω : ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X →
      ∃ ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2,
        X.IsRelativeDualizingSheaf B hZ ω) :
    StableFamilyTotalIsScheme B hZ g := by
  intro R _ _ _ hR F _ hF
  exact CurveFamily.exists_iso_schemeSpace_total_of_isStableCurveFamily hF.1 hω

end AlgebraicGeometry

end
