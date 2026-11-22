module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrChartOverlapDominance

/-!
# Represented models for the overlap of a common étale DVR chart

Pulling back the represented source chart along the first overlap projection
gives the represented overlap. The source remains flat over the original DVR,
and the represented target chart is separated over that DVR.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Models

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "Site" => BigFppfOver B integerBase hZ
local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

private def representedCurveBaseMap (F : CurveFamily B hZ) {Z : Site}
    (η : F.total ≅ schemeSpace Z) : Z ⟶ F.base :=
  (schemeSpaceFunctorFullyFaithful B hZ).preimage (η.inv ≫ F.toBase)

private theorem representedCurveBaseMap_space (F : CurveFamily B hZ) {Z : Site}
    (η : F.total ≅ schemeSpace Z) :
    schemeSpaceMap (representedCurveBaseMap F η) = η.inv ≫ F.toBase :=
  (schemeSpaceFunctorFullyFaithful B hZ).map_preimage _

private theorem representedCurveSquare (F : CurveFamily B hZ) {Z : Site}
    (η : F.total ≅ schemeSpace Z) :
    IsPullback η.inv (schemeSpaceMap (representedCurveBaseMap F η)) F.toBase
      (𝟙 (schemeSpace F.base)) := by
  exact IsPullback.of_horiz_isIso ⟨by
    rw [Category.comp_id, representedCurveBaseMap_space F η]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem representedCurveFlat (F : CurveFamily B hZ) {Z : Site}
    (η : F.total ≅ schemeSpace Z) : Flat ((𝒯).map (representedCurveBaseMap F η)) := by
  let q := representedCurveBaseMap F η
  have hsq : IsPullback η.inv.hom (yoneda.map q) F.toBase.hom (yoneda.map (𝟙 F.base)) := by
    change IsPullback η.inv.hom (schemeSpaceMap q).hom F.toBase.hom
      (schemeSpaceMap (𝟙 F.base)).hom
    rw [show schemeSpaceMap (𝟙 F.base) = 𝟙 (schemeSpace F.base) from
      (schemeSpaceFunctor B integerBase hZ).map_id F.base]
    exact AlgebraicSpaces.isPullback_hom B integerBase hZ (representedCurveSquare F η)
  have het : Etale ((𝒯).map (𝟙 F.base)) := by
    rw [show (𝒯).map (𝟙 F.base) = 𝟙 ((𝒯).obj F.base) from (𝒯).map_id F.base]
    infer_instance
  have hflat := Space.isFlat_of_isPullback B integerBase hZ hsq.flip
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B integerBase hZ _ (𝟙 F.base)).2 het)
    F.flat
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    Flat.isEtaleLocalOnSourceAndTarget q).mp hflat

private theorem representedCurveProper (F : CurveFamily B hZ) {Z : Site}
    (η : F.total ≅ schemeSpace Z) : IsProper ((𝒯).map (representedCurveBaseMap F η)) :=
  Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase hZ _
    (Space.isProper_of_isPullback B integerBase hZ (schemeSpace Z).property F.total.property
      (schemeSpace F.base).property (schemeSpace F.base).property
      (AlgebraicSpaces.isPullback_hom B integerBase hZ (representedCurveSquare F η)) F.proper)

set_option backward.isDefEq.respectTransparency false in
/-- The exact source and target representations needed by
`dvrChartOverlapAgrees_of_generic`, together with the hypotheses for applying
generic-fibre dominance to their morphisms. -/
theorem exists_dvrChartOverlapModels
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {hR : B.Contains (Spec (CommRingCat.of R))} {V Z T : Site}
    (F F' : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hR)
    (hF' : F'.base = integerSiteObject B hZ hR) (a : V ⟶ integerSiteObject B hZ hR)
    (ha : Etale ((𝒯).map a)) (haSep : IsSeparated ((𝒯).map a))
    (η : ((F.ofBaseEq hF).pullback a).total ≅ schemeSpace Z)
    (ε : ((F'.ofBaseEq hF').pullback a).total ≅ schemeSpace T) :
    let F₀ := F.ofBaseEq hF
    let p := F₀.pullbackHom a
    let w := pullback.fst p.baseMap p.baseMap ≫ p.baseMap
    let O := restrictX F₀ w
    let r₁ := factorX p w (pullback.fst p.baseMap p.baseMap) rfl
    ∃ (S : Site) (ξ : O.total ≅ schemeSpace S)
      (r : S ⟶ integerSiteObject B hZ hR) (s : T ⟶ integerSiteObject B hZ hR),
      Flat ((𝒯).map r) ∧ IsSeparated ((𝒯).map s) ∧
      schemeSpaceMap r = ξ.inv ≫ (O.toBase ≫ schemeSpaceMap r₁.baseMap) ≫ schemeSpaceMap a ∧
      schemeSpaceMap s = ε.inv ≫ ((F'.ofBaseEq hF').pullback a).toBase ≫ schemeSpaceMap a ∧
      B.Contains (pullback ((𝒯).map r) (genericPointInclusion R K)) := by
  let F₀ := F.ofBaseEq hF
  let A := F₀.pullback a
  let A' := (F'.ofBaseEq hF').pullback a
  let p := F₀.pullbackHom a
  let π := pullback.fst p.baseMap p.baseMap
  let w := π ≫ p.baseMap
  let O := restrictX F₀ w
  let r₁ := factorX p w π rfl
  let k := r₁.baseMap
  let q : Z ⟶ V := representedCurveBaseMap A η
  let q' : T ⟶ V := representedCurveBaseMap A' ε
  let S := pullback q k
  let d : S ⟶ O.base := pullback.snd q k
  have hsq : IsPullback (schemeSpaceMap (pullback.fst q k) ≫ η.inv) (schemeSpaceMap d)
      A.toBase (schemeSpaceMap k) := by
    change IsPullback (schemeSpaceMap (pullback.fst q k) ≫ η.inv)
      (schemeSpaceMap (pullback.snd q k)) A.toBase (schemeSpaceMap k)
    have h := (CurveFamily.isPullback_schemeSpaceMap_fst_snd q k).paste_horiz
      (representedCurveSquare A η)
    rw [Category.comp_id] at h
    exact h
  let ξ : O.total ≅ schemeSpace S :=
    IsPullback.isoIsPullback A.total (schemeSpace O.base) r₁.cartesian hsq
  have hξ : ξ.inv ≫ O.toBase = schemeSpaceMap d :=
    IsPullback.isoIsPullback_inv_snd A.total (schemeSpace O.base) r₁.cartesian hsq
  let r : S ⟶ integerSiteObject B hZ hR := d ≫ k ≫ a
  let s := q' ≫ a
  have hqs : Flat ((𝒯).map q) := representedCurveFlat A η
  letI : Flat ((𝒯).map d) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback q k).map (𝒯)) hqs
  letI : Etale ((𝒯).map a) := ha
  have hpFlat : Flat ((𝒯).map p.baseMap) := by
    rw [show p.baseMap = a from CurveFamily.pullbackHom_baseMap F₀ a]
    infer_instance
  letI : Flat ((𝒯).map π) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback p.baseMap p.baseMap).map (𝒯)).flip
      hpFlat
  letI : Flat ((𝒯).map k) := by
    change Flat ((𝒯).map (factorX p w π rfl).baseMap)
    rw [factorX_baseMap, Functor.map_comp]
    infer_instance
  have hrFlat : Flat ((𝒯).map r) := by
    change Flat ((𝒯).map (d ≫ k ≫ a))
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  letI : IsProper ((𝒯).map q') := representedCurveProper A' ε
  letI : IsSeparated ((𝒯).map a) := haSep
  have hsSep : IsSeparated ((𝒯).map s) := by
    change IsSeparated ((𝒯).map (q' ≫ a))
    rw [Functor.map_comp]
    infer_instance
  have hr : schemeSpaceMap r = ξ.inv ≫ (O.toBase ≫ schemeSpaceMap k) ≫ schemeSpaceMap a := by
    change schemeSpaceMap (d ≫ k ≫ a) = _
    rw [schemeSpaceMap_comp, schemeSpaceMap_comp]
    simp only [Category.assoc]
    rw [← Category.assoc ξ.inv O.toBase, hξ]
  have hs : schemeSpaceMap s = ε.inv ≫ A'.toBase ≫ schemeSpaceMap a := by
    change schemeSpaceMap (q' ≫ a) = _
    rw [schemeSpaceMap_comp, representedCurveBaseMap_space A' ε, Category.assoc]
  have hOpen : IsOpenImmersion (genericPointInclusion R K) := genericFiberSpec_isOpenImmersion
  have : IsOpenImmersion (pullback.fst ((𝒯).map r) (genericPointInclusion R K)) :=
    MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ hOpen
  have hK : B.Contains (pullback ((𝒯).map r) (genericPointInclusion R K)) :=
    B.contains_of_isOpenImmersion (pullback.fst ((𝒯).map r)
      (genericPointInclusion R K)) S.left.property
  exact ⟨S, ξ, r, s, hrFlat, hsSep, hr, hs, hK⟩

end AlgebraicGeometry.C1590Private

end
