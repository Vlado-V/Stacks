module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrCurveGenericTransport
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelDescent
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesEtaleLocallyProjective

/-!
# Generic agreement of the two restrictions of a DVR chart extension

On the generic fibre of the overlap, each projection to the source chart
factors through its generic family. The resulting maps to the original
generic family are equal by its cartesian square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Models

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "Site" => BigFppfOver B integerBase hZ
local notation "Spaces" => AlgebraicSpaces B integerBase hZ
local notation "forgetScheme" => BigFppfOver.toScheme B integerBase hZ

private theorem eq_of_chart_maps_on_pullback {U V U' V' : Site}
    (j : U ⟶ V) (jL : U' ⟶ V') (k : U' ⟶ U) (a : V' ⟶ V)
    (hSq : IsPullback (schemeSpaceMap k) (schemeSpaceMap jL) (schemeSpaceMap j) (schemeSpaceMap a))
    {F G O : CurveFamily B hZ} (hF : F.base = V) (hG : G.base = U) (c : G ⟶ F)
    (cL : chartCurve G hG k ⟶ chartCurve F hF a)
    (hcL : (curvesProjectionOver B hZ).IsHomLift jL cL)
    (hc : cL ≫ chartCurveHom F hF a = chartCurveHom G hG k ≫ c)
    (r₁ r₂ : O ⟶ chartCurve F hF a)
    (hr : r₁ ≫ chartCurveHom F hF a = r₂ ≫ chartCurveHom F hF a)
    {P X : Spaces} (f : P ⟶ O.total) (b : P ⟶ schemeSpace U)
    (hbase : (f ≫ O.toBase ≫ schemeSpaceMap r₁.baseMap) ≫ schemeSpaceMap a = b ≫ schemeSpaceMap j)
    (n : (chartCurve F hF a).total ⟶ X) (nK : G.total ⟶ X)
    (hn : cL.totalMap ≫ n = (chartCurveHom G hG k).totalMap ≫ nK) :
    f ≫ (r₁.totalMap ≫ n) = f ≫ (r₂.totalMap ≫ n) := by
  have hfac := @IsHomLift.fac' _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ jL cL hcL
  have hcLbase : cL.baseMap = jL := by
    change cL.baseMap = eqToHom (rfl : U' = U') ≫ jL ≫ eqToHom (rfl : V' = V') at hfac
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hfac
  have hcLpb : IsPullback cL.totalMap (chartCurve G hG k).toBase
      (chartCurve F hF a).toBase (schemeSpaceMap jL) := hcLbase ▸ cL.cartesian
  have hproj : r₁.baseMap ≫ a = r₂.baseMap ≫ a := by
    apply (cancel_mono (eqToHom hF.symm)).mp
    simpa only [CurveFamily.comp_baseMap, chartCurveHom_baseMap, Category.assoc] using
      congrArg (fun x : O ⟶ F => x.baseMap) hr
  have hbase₂ : (f ≫ O.toBase ≫ schemeSpaceMap r₂.baseMap) ≫ schemeSpaceMap a =
      b ≫ schemeSpaceMap j := by
    simpa only [Category.assoc, ← schemeSpaceMap_comp, ← hproj] using hbase
  have lift_generic (q : O ⟶ chartCurve F hF a)
      (hq : (f ≫ O.toBase ≫ schemeSpaceMap q.baseMap) ≫ schemeSpaceMap a = b ≫ schemeSpaceMap j) :
      ∃ z : P ⟶ (chartCurve G hG k).total,
        z ≫ cL.totalMap = f ≫ q.totalMap ∧
        (z ≫ (chartCurveHom G hG k).totalMap) ≫ G.toBase =
          b ≫ schemeSpaceMap (eqToHom hG.symm) := by
    let bA := f ≫ O.toBase ≫ schemeSpaceMap q.baseMap
    let bL := hSq.lift b bA hq.symm
    have hbLk : bL ≫ schemeSpaceMap k = b := hSq.lift_fst _ _ _
    have hbLj : bL ≫ schemeSpaceMap jL = bA := hSq.lift_snd _ _ _
    have hq' : (f ≫ q.totalMap) ≫ (chartCurve F hF a).toBase = bL ≫ schemeSpaceMap jL := by
      rw [hbLj, Category.assoc, q.cartesian.w]
    let z := hcLpb.lift (f ≫ q.totalMap) bL hq'
    have hzb : z ≫ (chartCurve G hG k).toBase = bL := hcLpb.lift_snd _ _ _
    refine ⟨z, hcLpb.lift_fst _ _ _, ?_⟩
    rw [Category.assoc, (chartCurveHom G hG k).cartesian.w,
      chartCurveHom_baseMap, schemeSpaceMap_comp, ← Category.assoc z, hzb,
      ← Category.assoc bL, hbLk]
  obtain ⟨z₁, hz₁, hb₁⟩ := lift_generic r₁ hbase
  obtain ⟨z₂, hz₂, hb₂⟩ := lift_generic r₂ hbase₂
  have hz : z₁ ≫ (chartCurveHom G hG k).totalMap = z₂ ≫ (chartCurveHom G hG k).totalMap := by
    apply c.cartesian.hom_ext
    · have he (z : P ⟶ (chartCurve G hG k).total) (q : O ⟶ chartCurve F hF a)
          (hq : z ≫ cL.totalMap = f ≫ q.totalMap) :
          (z ≫ (chartCurveHom G hG k).totalMap) ≫ c.totalMap =
            f ≫ (q ≫ chartCurveHom F hF a).totalMap := by
        have h := congrArg (fun x : chartCurve G hG k ⟶ F => x.totalMap) hc
        simp only [CurveFamily.comp_totalMap] at h
        calc
          _ = z ≫ (chartCurveHom G hG k).totalMap ≫ c.totalMap := Category.assoc ..
          _ = z ≫ cL.totalMap ≫ (chartCurveHom F hF a).totalMap := congrArg (z ≫ ·) h.symm
          _ = (z ≫ cL.totalMap) ≫ (chartCurveHom F hF a).totalMap := (Category.assoc ..).symm
          _ = _ := by rw [hq, CurveFamily.comp_totalMap, Category.assoc]
      rw [he z₁ r₁ hz₁, he z₂ r₂ hz₂, hr]
    · exact hb₁.trans hb₂.symm
  have hres (z : P ⟶ (chartCurve G hG k).total) (q : O ⟶ chartCurve F hF a)
      (hq : z ≫ cL.totalMap = f ≫ q.totalMap) :
      f ≫ q.totalMap ≫ n = (z ≫ (chartCurveHom G hG k).totalMap) ≫ nK := calc
    _ = (f ≫ q.totalMap) ≫ n := (Category.assoc ..).symm
    _ = (z ≫ cL.totalMap) ≫ n := congrArg (· ≫ n) hq.symm
    _ = _ := by rw [Category.assoc, hn, Category.assoc]
  exact (hres z₁ r₁ hz₁).trans ((congrArg (· ≫ nK) hz).trans (hres z₂ r₂ hz₂).symm)

/-- The two pullbacks of the local extension have the same map from the generic
fibre of the actual represented overlap, in the form required by overlap dominance. -/
theorem dvrChartOverlapGeneric_agrees {R A K : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra R A]
    [Field K] [Algebra R K] [IsFractionRing R K] [IsLocalHom (algebraMap R A)]
    (hinj : Function.Injective (algebraMap R A))
    (hR : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (hK : B.Contains (Spec (.of K))) (hL : B.Contains (Spec (.of (FractionRing A))))
    (j : integerSiteObject B hZ hK ⟶ integerSiteObject B hZ hR)
    (hj : (forgetScheme).map j = Spec.algebraMap R K)
    {F F' G G' : CurveFamily B hZ}
    (hF : F.base = integerSiteObject B hZ hR) (hF' : F'.base = integerSiteObject B hZ hR)
    (hG : G.base = integerSiteObject B hZ hK)
    (c : G ⟶ F) (c' : G' ⟶ F') (s : G ⟶ G') {S : Site}
    (r : S ⟶ integerSiteObject B hZ hR)
    (hP : B.Contains (pullback ((forgetScheme).map r) (Spec.algebraMap R K))) :
    let a := integerSiteMap B hZ hA hR (Spec.algebraMap R A)
    let jL := integerSiteMap B hZ hL hA (Spec.algebraMap A (FractionRing A))
    let k := integerSiteMap B hZ hL hK (Spec.map (CommRingCat.ofHom
      (fractionRingMapOfInjective (K := K) (L := FractionRing A) (algebraMap R A) hinj)))
    let p := (F.ofBaseEq hF).pullbackHom a
    let w := pullback.fst p.baseMap p.baseMap ≫ p.baseMap
    let O := restrictX (F.ofBaseEq hF) w
    let r₁ := factorX p w (pullback.fst p.baseMap p.baseMap) rfl
    let r₂ := factorX p w (pullback.snd p.baseMap p.baseMap) pullback.condition.symm
    ∀ (cL : chartCurve G hG k ⟶ chartCurve F hF a) (tL : chartCurve F hF a ⟶ chartCurve F' hF' a),
      (curvesProjectionOver B hZ).IsHomLift jL cL →
      cL ≫ chartCurveHom F hF a = chartCurveHom G hG k ≫ c →
      cL ≫ tL ≫ chartCurveHom F' hF' a = chartCurveHom G hG k ≫ s ≫ c' →
      ∀ (ξ : O.total ≅ schemeSpace S),
        schemeSpaceMap r = ξ.inv ≫ (O.toBase ≫ schemeSpaceMap r₁.baseMap) ≫ schemeSpaceMap a →
        let gK := schemeSpaceMap (CurveFamily.siteHomOfContains (hZ := hZ) hP
          (pullback.fst ((forgetScheme).map r) (Spec.algebraMap R K))) ≫ ξ.inv
        let n := tL.totalMap ≫ ((F'.ofBaseEq hF').pullbackHom a).totalMap
        gK ≫ (r₁.totalMap ≫ n) = gK ≫ (r₂.totalMap ≫ n) := by
  intro a jL k p w O r₁ r₂ cL tL hcL hc hcomp ξ hr gK n
  have hj' : integerSiteMap B hZ hK hR (Spec.algebraMap R K) = j :=
    hj ▸ integerSiteMap_toScheme_map j
  have hSq : IsPullback (schemeSpaceMap k) (schemeSpaceMap jL) (schemeSpaceMap j) (schemeSpaceMap a) := by
    rw [← hj']
    exact isPullback_schemeSpaceMap_integerSiteMap
      (isPullback_genericFiberSpec_of_localHom (K := K) (L := FractionRing A) (algebraMap R A) hinj)
  let j₁ := CurveFamily.siteHomOfContains (hZ := hZ) hP
    (pullback.fst ((forgetScheme).map r) (Spec.algebraMap R K))
  let j₂ : CurveFamily.siteObj (hZ := hZ) hP ⟶ integerSiteObject B hZ hK :=
    CurveFamily.siteHomOfContains (hZ := hZ) hP
      (pullback.snd ((forgetScheme).map r) (Spec.algebraMap R K))
  have hsite : j₁ ≫ r = j₂ ≫ j := by
    apply (forgetScheme).map_injective
    have hm₁ : (forgetScheme).map j₁ = pullback.fst ((forgetScheme).map r) (Spec.algebraMap R K) :=
      CurveFamily.toScheme_map_siteHomOfContains _ _
    have hm₂ : (forgetScheme).map j₂ = pullback.snd ((forgetScheme).map r) (Spec.algebraMap R K) :=
      CurveFamily.toScheme_map_siteHomOfContains _ _
    rw [Functor.map_comp, Functor.map_comp, hm₁, hm₂, hj]
    exact pullback.condition
  have hcoordinates : (gK ≫ O.toBase ≫ schemeSpaceMap r₁.baseMap) ≫ schemeSpaceMap a =
      schemeSpaceMap j₂ ≫ schemeSpaceMap j := calc
    _ = schemeSpaceMap j₁ ≫ schemeSpaceMap r := by
      rw [hr]
      simp only [gK, j₁, Category.assoc]
    _ = _ := by rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp, hsite]
  have hrestrictions : r₁ ≫ chartCurveHom F hF a = r₂ ≫ chartCurveHom F hF a := by
    change r₁ ≫ p ≫ (F.ofBaseEqIso hF).hom = r₂ ≫ p ≫ (F.ofBaseEqIso hF).hom
    rw [← Category.assoc r₁, ← Category.assoc r₂]
    simp only [r₁, r₂, factorX_comp]
  have hgeneric : cL.totalMap ≫ n = (chartCurveHom G hG k).totalMap ≫ (s ≫ c').totalMap := by
    have he := congrArg (fun f : chartCurve G hG k ⟶ F' => f.totalMap) hcomp
    simpa only [n, chartCurveHom, CurveFamily.comp_totalMap, CurveFamily.ofBaseEqIso_hom_totalMap,
      Category.id_comp, Category.comp_id, Category.assoc] using he
  exact eq_of_chart_maps_on_pullback j jL k a hSq hF hG c cL hcL hc r₁ r₂ hrestrictions
    gK (schemeSpaceMap j₂) hcoordinates n (s ≫ c').totalMap hgeneric

end AlgebraicGeometry.C1590Private

end
