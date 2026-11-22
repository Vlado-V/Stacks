module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamiliesEtaleDvrChart
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrChartLocalExtensionUnique
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrChartOverlapGeneric
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrChartOverlapModels
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrCurveChartHomExt

/-!
# Valuative uniqueness for smooth stable models by étale descent

Both total spaces become schemes over a common surjective étale DVR chart.
The checked scheme extension descends after comparison on its generic overlap.
Both the generic equality and uniqueness of the descended arrow are local on
the corresponding bases.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Models

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "Site" => BigFppfOver B integerBase hZ
local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

private theorem chartCurveHom_cover (F : CurveFamily B hZ) {V T : Site}
    (hF : F.base = V) (a : T ⟶ V)
    (hSurj : Surjective ((𝒯).map a)) (hEt : Etale ((𝒯).map a)) :
    Sieve.ofArrows (fun _ : Unit => (chartCurve F hF a).base)
      (fun _ => (chartCurveHom F hF a).baseMap) ∈ BigFppfOver.topology B integerBase hZ F.base := by
  have hSurj' : Surjective ((𝒯).map (chartCurveHom F hF a).baseMap) := by
    rw [chartCurveHom_baseMap, Functor.map_comp]
    let _ := hSurj
    infer_instance
  have hEt' : Etale ((𝒯).map (chartCurveHom F hF a).baseMap) := by
    rw [chartCurveHom_baseMap, Functor.map_comp]
    let _ := hEt
    infer_instance
  change Sieve.generate (Presieve.ofArrows (fun _ : Unit => (chartCurve F hF a).base)
    (fun _ => (chartCurveHom F hF a).baseMap)) ∈ BigFppfOver.topology B integerBase hZ F.base
  rw [Presieve.ofArrows_of_unique]
  exact Space.sieve_generate_singleton_mem_topology_over B integerBase hZ _ hSurj' hEt'

private theorem isIso_of_vertical_curveHom {U : Site} {X Y : CurveFamily B hZ} (t : X ⟶ Y)
    (ht : (curvesProjectionOver B hZ).IsHomLift (𝟙 U) t) : IsIso t := by
  letI := ht
  have hf : (curvesProjectionOver B hZ).IsFiberedInGroupoids := (curvesFiberedCategory B hZ).2
  letI : (curvesProjectionOver B hZ).IsStronglyCartesian (𝟙 U) t :=
    hf.isStronglyCartesian_homLift (𝟙 U) t
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso (curvesProjectionOver B hZ) (𝟙 U) t

/-- The smooth stable valuative statement for the original algebraic-space families. -/
theorem uniqueSmoothStableModels_of_etaleDvr (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (g : ℕ) : UniqueSmoothStableModels B hZ g := by
  intro R _ _ _ K _ _ _ hR hK base j hj F F' G G' c c' s hst hst' hsm hsm' hsmG _ hc hc' hs
  obtain rfl : base = specULiftZIsTerminal.from _ := specULiftZIsTerminal.hom_ext _ _
  generalize Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
    specULiftZIsTerminal.from (Spec (.of R)) = b at j hj hc hc' hs ⊢
  obtain rfl : b = specULiftZIsTerminal.from _ := specULiftZIsTerminal.hom_ext _ _
  have hF : F.base = integerSiteObject B hZ hR :=
    @IsHomLift.codomain_eq _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ j c hc
  have hF' : F'.base = integerSiteObject B hZ hR :=
    @IsHomLift.codomain_eq _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ j c' hc'
  have hG : G.base = integerSiteObject B hZ hK :=
    @IsHomLift.domain_eq _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ j c hc
  have hG' : G'.base = integerSiteObject B hZ hK :=
    @IsHomLift.domain_eq _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ j c' hc'
  have hj' : (BigFppfOver.toScheme B integerBase hZ).map j = Spec.algebraMap R K := hj
  let X : Fin 2 → CurveFamily B hZ := ![F, F']
  have hX (i : Fin 2) : (X i).base = integerSiteObject B hZ hR := by
    fin_cases i
    · exact hF
    · exact hF'
  obtain ⟨A, hComm, hDom, hDvr, hAlg, hExt, hAlgEt, hA, hSurj, hRep⟩ :=
    exists_etaleDvrCover_schemeRepresentations hR X hX
  letI := hComm
  letI := hDom
  letI := hDvr
  letI := hAlg
  letI := hExt
  letI := hAlgEt
  have hInj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hEt : Etale (Spec.algebraMap R A) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hAlgEt)
  let a := integerSiteMap B hZ hA hR (Spec.algebraMap R A)
  have hEt' : Etale ((BigFppfOver.toScheme B integerBase hZ).map a) := hEt
  have hSurj' : Surjective ((BigFppfOver.toScheme B integerBase hZ).map a) := hSurj
  have haSep : IsSeparated ((BigFppfOver.toScheme B integerBase hZ).map a) := by
    change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    infer_instance
  let L := FractionRing A
  have hL : B.Contains (Spec (.of L)) := contains_fractionRing_of_contains_dvr hA
  let kScheme := Spec.map (CommRingCat.ofHom
    (fractionRingMapOfInjective (K := K) (L := L) (algebraMap R A) hInj))
  let k := integerSiteMap B hZ hL hK kScheme
  have hrep : ∃ (Y : Scheme.{u}) (hY : B.Contains Y),
      Nonempty ((chartCurve F hF a).total ≅ schemeSpace (integerSiteObject B hZ hY)) := hRep 0
  have hrep' : ∃ (Y : Scheme.{u}) (hY : B.Contains Y),
      Nonempty ((chartCurve F' hF' a).total ≅ schemeSpace (integerSiteObject B hZ hY)) := hRep 1
  obtain ⟨cL, tL, hcL, hcComp, htL, htBase, hcompL, huniqL⟩ :=
    existsUnique_dvrChartVerticalExtension hInj hEt hR hA hK hL j hj' hF hF' hG hG'
      c c' s hc hc' hs hst hst' hsm hsm' hsmG hrep hrep'
  have : IsIso tL := isIso_of_vertical_curveHom tL htL
  let e := asIso tL
  obtain ⟨Y, hY, ⟨η⟩⟩ := hrep
  obtain ⟨Y', hY', ⟨ε⟩⟩ := hrep'
  obtain ⟨O, ξ, r, q, hFlat, hSep, hr, hq, hPK⟩ :=
    exists_dvrChartOverlapModels (K := K) F F' hF hF' a hEt' haSep η ε
  letI := hFlat
  letI := hSep
  have hgeneric := dvrChartOverlapGeneric_agrees hInj hR hA hK hL j hj'
    hF hF' hG c c' s r hPK cL tL hcL hcComp hcompL ξ hr
  have hoverlap := dvrChartOverlapAgrees_of_generic F F' hF hF' a e htBase r q hPK ε hq ξ hr hgeneric
  obtain ⟨t, ht, hChart⟩ := exists_iso_of_dvrChartOverlap F F' hF hF' a hSurj' hEt' e htBase hoverlap
  have hChart' : (chartCurveHom F hF a).totalMap ≫ t.hom.totalMap =
      tL.totalMap ≫ (chartCurveHom F' hF' a).totalMap := by
    simpa only [chartCurveHom, CurveFamily.comp_totalMap, CurveFamily.ofBaseEqIso_hom_totalMap,
      Category.comp_id, e, asIso_hom] using hChart
  letI : (curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hR)) t.hom := ht
  letI := hc
  letI := hc'
  letI := hs
  have hlc : (curvesProjectionOver B hZ).IsHomLift j (c ≫ t.hom) :=
    @IsHomLift.comp_lift_id_right _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ _ j c hc t.hom ht
  have hrc : (curvesProjectionOver B hZ).IsHomLift j (s ≫ c') := inferInstance
  have hkPb := isPullback_genericFiberSpec_of_localHom (K := K) (L := L) (algebraMap R A) hInj
  have hkSurj : Surjective ((BigFppfOver.toScheme B integerBase hZ).map k) :=
    MorphismProperty.of_isPullback (P := @Surjective) hkPb.flip hSurj
  have hkEt : Etale ((BigFppfOver.toScheme B integerBase hZ).map k) :=
    MorphismProperty.of_isPullback (P := @Etale) hkPb.flip hEt
  have hEq : c ≫ t.hom = s ≫ c' := by
    refine curveFamily_hom_ext_of_cover (chartCurveHom G hG k)
      (chartCurveHom_cover G hG k hkSurj hkEt) (curveFamily_sameBaseMap_of_lifts j hlc hrc) ?_
    have hcTot := congrArg (fun v : chartCurve G hG k ⟶ F => v.totalMap) hcComp
    have hcompTot := congrArg (fun v : chartCurve G hG k ⟶ F' => v.totalMap) hcompL
    simp only [CurveFamily.comp_totalMap] at hcTot hcompTot ⊢
    calc
      _ = (cL.totalMap ≫ (chartCurveHom F hF a).totalMap) ≫ t.hom.totalMap := by
        rw [hcTot, Category.assoc]
      _ = cL.totalMap ≫ tL.totalMap ≫ (chartCurveHom F' hF' a).totalMap := by
        rw [Category.assoc, hChart']
      _ = _ := hcompTot
  refine ⟨t.hom, ⟨ht, hEq⟩, ?_⟩
  rintro u ⟨hu, heq⟩
  obtain ⟨uL, huL, huComp⟩ := exists_lift_chartCurve hF hF' (𝟙 _) (𝟙 _) a a u hu (by simp)
  have huGeneric : cL ≫ uL ≫ chartCurveHom F' hF' a = chartCurveHom G hG k ≫ s ≫ c' := by
    calc
      _ = (cL ≫ chartCurveHom F hF a) ≫ u := by rw [huComp, Category.assoc]
      _ = _ := by rw [hcComp, Category.assoc, heq]
  have huIt := huniqL uL huL huGeneric
  refine curveFamily_hom_ext_of_cover (chartCurveHom F hF a)
    (chartCurveHom_cover F hF a hSurj' hEt') (curveFamily_sameBaseMap_of_lifts (𝟙 _) hu ht) ?_
  have huTot := congrArg (fun v : chartCurve F hF a ⟶ F' => v.totalMap) huComp
  simp only [CurveFamily.comp_totalMap, huIt] at huTot
  exact huTot.symm.trans hChart'.symm

end AlgebraicGeometry.C1590Private

end
