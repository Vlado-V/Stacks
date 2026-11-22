module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrCurveGenericTransport
public import StacksFrontier.AlgebraicGeometry.Quot.UniqueStableModelsReduction
public import StacksFrontier.AlgebraicGeometry.Quot.UniqueSmoothModelsScheme

/-!
# Extending the generic isomorphism over a represented DVR chart

Over one étale extension with represented total spaces, the existing
smooth scheme-model theorem gives a vertical extension. Its restriction
to the generic point agrees with the original comparison via the chart
projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Models

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

private theorem chartCurveHom_etale_baseMap
    (F : CurveFamily B hZ) {V T : BigFppfOver B integerBase hZ}
    (hF : F.base = V) (a : T ⟶ V)
    (ha : Etale ((BigFppfOver.toScheme B integerBase hZ).map a)) :
    Space.IsEtale B integerBase hZ (schemeSpaceMap (chartCurveHom F hF a).baseMap).hom := by
  rw [chartCurveHom_baseMap]
  apply Space.isEtale_of_presheaf_etale B integerBase hZ
  apply (Space.presheaf_yoneda_map_etale_iff B integerBase hZ _).2
  rw [Functor.map_comp]
  let _ := ha
  infer_instance

private theorem stableGenus_chartCurve {g : ℕ} {F : CurveFamily B hZ}
    {V T : BigFppfOver B integerBase hZ} (hF : F.base = V) (a : T ⟶ V)
    (ha : Etale ((BigFppfOver.toScheme B integerBase hZ).map a))
    (h : IsStableCurveFamilyOfGenus B hZ g F) :
    IsStableCurveFamilyOfGenus B hZ g (chartCurve F hF a) :=
  ⟨CurveFamily.isStableCurveFamily_of_hom (chartCurveHom F hF a) h.1,
    CurveFamily.hasGenus_of_hom_of_isEtale (chartCurveHom F hF a)
      (chartCurveHom_etale_baseMap F hF a ha) h.2⟩

private theorem existsIsoOfSmoothStableModelsWith (g : ℕ) :
    ExistsIsoOfStableModelsWith B hZ True g := by
  intro A _ _ _ L _ _ _ hA C q _ Y Y' p p' e e' hmod hmod' hst hst' hs hs'
  exact existsIsoOfSmoothStableModels B hZ g A L hA q hmod hmod' hst hst' (hs trivial) (hs' trivial)

/-- Two family arrows with the same base map agree if their composites do. -/
theorem curveFamily_hom_ext_of_comp {X Y Z : CurveFamily B hZ} (p : Y ⟶ Z)
    {f f' : X ⟶ Y} (hbase : f.baseMap = f'.baseMap) (hcomp : f ≫ p = f' ≫ p) : f = f' := by
  apply CurveFamily.Hom.ext hbase
  apply p.cartesian.hom_ext
  · exact congrArg (fun k : X ⟶ Z => k.totalMap) hcomp
  · rw [f.cartesian.w, f'.cartesian.w, hbase]

/-- Two family arrows lifting the same site arrow have equal base maps. -/
theorem curveFamily_sameBaseMap_of_lifts {X Y : CurveFamily B hZ}
    {U V : BigFppfOver B integerBase hZ} (p : U ⟶ V) {f f' : X ⟶ Y}
    (hf : (curvesProjectionOver B hZ).IsHomLift p f)
    (hf' : (curvesProjectionOver B hZ).IsHomLift p f') : f.baseMap = f'.baseMap := by
  have e := @IsHomLift.fac' _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ p f hf
  have e' := @IsHomLift.fac' _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ p f' hf'
  exact e.trans e'.symm

/-- On a represented chart of the two smooth stable families, their comparison extends
vertically to an isomorphism of total spaces. The two equalities describe its restriction
to the generic family before and after the extension. -/
theorem existsUnique_dvrChartVerticalExtension {g : ℕ} {R A K : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra R A]
    [Field K] [Algebra R K] [IsFractionRing R K] [IsLocalHom (algebraMap R A)]
    (hinj : Function.Injective (algebraMap R A)) (ha : Etale (Spec.algebraMap R A))
    (hR : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (hK : B.Contains (Spec (.of K))) (hL : B.Contains (Spec (.of (FractionRing A))))
    (j : integerSiteObject B hZ hK ⟶ integerSiteObject B hZ hR)
    (hj : (BigFppfOver.toScheme B integerBase hZ).map j = Spec.algebraMap R K)
    {F F' G G' : CurveFamily B hZ}
    (hF : F.base = integerSiteObject B hZ hR) (hF' : F'.base = integerSiteObject B hZ hR)
    (hG : G.base = integerSiteObject B hZ hK) (hG' : G'.base = integerSiteObject B hZ hK)
    (c : G ⟶ F) (c' : G' ⟶ F') (s : G ⟶ G')
    (hc : (curvesProjectionOver B hZ).IsHomLift j c)
    (hc' : (curvesProjectionOver B hZ).IsHomLift j c')
    (hs : (curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hK)) s)
    (hst : IsStableCurveFamilyOfGenus B hZ g F) (hst' : IsStableCurveFamilyOfGenus B hZ g F')
    (hsm : IsSmoothFamily B hZ F) (hsm' : IsSmoothFamily B hZ F') (hsmG : IsSmoothH0Family B hZ G) :
    let a := integerSiteMap B hZ hA hR (Spec.algebraMap R A)
    let jL := integerSiteMap B hZ hL hA (Spec.algebraMap A (FractionRing A))
    let k := integerSiteMap B hZ hL hK (Spec.map (CommRingCat.ofHom
      (fractionRingMapOfInjective (K := K) (L := FractionRing A) (algebraMap R A) hinj)))
    (∃ (Y : Scheme.{u}) (hY : B.Contains Y),
      Nonempty ((chartCurve F hF a).total ≅ schemeSpace (integerSiteObject B hZ hY))) →
    (∃ (Y' : Scheme.{u}) (hY' : B.Contains Y'),
      Nonempty ((chartCurve F' hF' a).total ≅ schemeSpace (integerSiteObject B hZ hY'))) →
    ∃ (cL : chartCurve G hG k ⟶ chartCurve F hF a)
      (tL : chartCurve F hF a ⟶ chartCurve F' hF' a),
      (curvesProjectionOver B hZ).IsHomLift jL cL ∧
      cL ≫ chartCurveHom F hF a = chartCurveHom G hG k ≫ c ∧
      (curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hA)) tL ∧
      tL.baseMap = 𝟙 (integerSiteObject B hZ hA) ∧
      (cL ≫ tL ≫ chartCurveHom F' hF' a = chartCurveHom G hG k ≫ s ≫ c') ∧
      ∀ (uL : chartCurve F hF a ⟶ chartCurve F' hF' a),
        (curvesProjectionOver B hZ).IsHomLift (𝟙 (integerSiteObject B hZ hA)) uL →
        cL ≫ uL ≫ chartCurveHom F' hF' a = chartCurveHom G hG k ≫ s ≫ c' → uL = tL := by
  intro a jL k hrep hrep'
  have hw : k ≫ j = jL ≫ a := dvr_genericSite_commutes hinj hR hA hK hL j hj
  obtain ⟨cL, cL', sL, hCL, hCL', hSL, hcComp, hcComp', hsComp⟩ :=
    exists_chartCurveGenericDiagram hF hF' hG hG' j jL k a c c' s hc hc' hs hw
  have hEt : Etale ((BigFppfOver.toScheme B integerBase hZ).map a) := ha
  obtain ⟨tL, ⟨ht, hcomp⟩, huniq⟩ :=
    existsUnique_hom_of_existsIsoOfStableModelsWith_of_totalRepresentations
      (existsIsoOfSmoothStableModelsWith g) A (FractionRing A) hA hL jL rfl cL cL' sL hrep hrep'
      (stableGenus_chartCurve hF a hEt hst) (stableGenus_chartCurve hF' a hEt hst')
      (fun _ => CurveFamily.isSmoothFamily_of_hom B hZ (chartCurveHom F hF a) hsm)
      (fun _ => CurveFamily.isSmoothFamily_of_hom B hZ (chartCurveHom F' hF' a) hsm')
      (CurveFamily.isSmoothH0Family_of_hom B hZ (chartCurveHom G hG k) hsmG) hCL hCL' hSL
  have hfac := @IsHomLift.fac' _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _
    (𝟙 (integerSiteObject B hZ hA)) tL ht
  have htBase : tL.baseMap = 𝟙 (integerSiteObject B hZ hA) := by
    change tL.baseMap = eqToHom (rfl : integerSiteObject B hZ hA = integerSiteObject B hZ hA) ≫
      𝟙 _ ≫ eqToHom (rfl : integerSiteObject B hZ hA = integerSiteObject B hZ hA) at hfac
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hfac
  have hcomp' : cL ≫ tL ≫ chartCurveHom F' hF' a = chartCurveHom G hG k ≫ s ≫ c' := by
    calc
      _ = (cL ≫ tL) ≫ chartCurveHom F' hF' a := (Category.assoc ..).symm
      _ = (sL ≫ cL') ≫ chartCurveHom F' hF' a := congrArg (· ≫ chartCurveHom F' hF' a) hcomp
      _ = sL ≫ chartCurveHom G' hG' k ≫ c' := by rw [Category.assoc, hcComp']
      _ = _ := by rw [← Category.assoc, hsComp, Category.assoc]
  refine ⟨cL, tL, hCL, hcComp, ht, htBase, hcomp', fun uL huL huComp => huniq uL ⟨huL, ?_⟩⟩
  have hbu := @IsHomLift.comp_lift_id_right _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ _
    jL cL hCL uL huL
  have hbt := @IsHomLift.comp_lift_id_right _ _ _ _ (curvesProjectionOver B hZ) _ _ _ _ _
    jL cL hCL tL ht
  have he : cL ≫ uL = cL ≫ tL :=
    curveFamily_hom_ext_of_comp (chartCurveHom F' hF' a)
      (curveFamily_sameBaseMap_of_lifts jL hbu hbt)
      (by simpa only [Category.assoc] using huComp.trans hcomp'.symm)
  exact he.trans hcomp

end AlgebraicGeometry.C1590Private

end
