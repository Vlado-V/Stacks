module

public import StacksFrontier.AlgebraicGeometry.Models.GenericFibreDvrExtension
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeGlue

/-!
# Transporting a generic-fibre diagram to a local extension of DVRs

The chosen base changes of the two model families and their generic families
carry compatible lifts of the old generic arrows. The lift of the generic
comparison remains vertical.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Models

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Base change through a given identification of the old base. -/
abbrev chartCurve (F : CurveFamily B hZ) {V T : BigFppfOver B integerBase hZ}
    (hF : F.base = V) (a : T ⟶ V) : CurveFamily B hZ :=
  (F.ofBaseEq hF).pullback a

/-- The projection from the chosen base change to the original family. -/
def chartCurveHom (F : CurveFamily B hZ) {V T : BigFppfOver B integerBase hZ}
    (hF : F.base = V) (a : T ⟶ V) : chartCurve F hF a ⟶ F :=
  (F.ofBaseEq hF).pullbackHom a ≫ (F.ofBaseEqIso hF).hom

@[simp]
theorem chartCurveHom_baseMap (F : CurveFamily B hZ) {V T : BigFppfOver B integerBase hZ}
    (hF : F.base = V) (a : T ⟶ V) :
    (chartCurveHom F hF a).baseMap = a ≫ eqToHom hF.symm := by
  simp only [chartCurveHom, CurveFamily.comp_baseMap, CurveFamily.pullbackHom_baseMap,
    CurveFamily.ofBaseEqIso_hom_baseMap]

/-- The projection of a chosen base change lifts the given arrow of the site. -/
theorem chartCurveHom_isHomLift (F : CurveFamily B hZ) {V T : BigFppfOver B integerBase hZ}
    (hF : F.base = V) (a : T ⟶ V) :
    (curvesProjectionOver B hZ).IsHomLift a (chartCurveHom F hF a) := by
  apply IsHomLift.of_fac' (curvesProjectionOver B hZ) a (chartCurveHom F hF a) rfl hF
  change (chartCurveHom F hF a).baseMap = eqToHom rfl ≫ a ≫ eqToHom hF.symm
  rw [eqToHom_refl, Category.id_comp, chartCurveHom_baseMap]

/-- A commuting base square transports a morphism of curve families between chosen base changes. -/
theorem exists_lift_chartCurve {U V U' V' : BigFppfOver B integerBase hZ}
    {G F : CurveFamily B hZ} (hG : G.base = U) (hF : F.base = V)
    (j : U ⟶ V) (j' : U' ⟶ V') (k : U' ⟶ U) (a : V' ⟶ V) (c : G ⟶ F)
    (hc : (curvesProjectionOver B hZ).IsHomLift j c) (hw : k ≫ j = j' ≫ a) :
    ∃ c' : chartCurve G hG k ⟶ chartCurve F hF a,
      (curvesProjectionOver B hZ).IsHomLift j' c' ∧
        c' ≫ chartCurveHom F hF a = chartCurveHom G hG k ≫ c := by
  have := hc
  have hcBase : c.baseMap = eqToHom hG ≫ j ≫ eqToHom hF.symm :=
    IsHomLift.fac' (curvesProjectionOver B hZ) j c
  have hb : j' ≫ (chartCurveHom F hF a).baseMap = (chartCurveHom G hG k ≫ c).baseMap := calc
    _ = (j' ≫ a) ≫ eqToHom hF.symm := by rw [chartCurveHom_baseMap, Category.assoc]
    _ = (k ≫ j) ≫ eqToHom hF.symm := congrArg (· ≫ eqToHom hF.symm) hw.symm
    _ = _ := by
      simp only [CurveFamily.comp_baseMap, chartCurveHom_baseMap, hcBase, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  obtain ⟨c', ⟨hb', hcomp⟩, _⟩ :=
    ((curvesFiberedCategory B hZ).2 :
      (curvesProjectionOver B hZ).IsFiberedInGroupoids).unique_lift
      (chartCurveHom F hF a) (chartCurveHom G hG k ≫ c) j' hb
  have hc'Map : (curvesProjectionOver B hZ).map c' = j' := hb'
  exact ⟨c', hc'Map ▸ IsHomLift.map (curvesProjectionOver B hZ) c', hcomp⟩

/-- The fraction field of a DVR is in the site whenever the DVR itself is. -/
theorem contains_fractionRing_of_contains_dvr {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (hA : B.Contains (Spec (.of A))) :
    B.Contains (Spec (.of (FractionRing A))) := by
  let : IsOpenImmersion (Spec.algebraMap A (FractionRing A)) := genericFiberSpec_isOpenImmersion
  exact BigFppfSite.contains_of_locallyOfFinitePresentation B
    (Spec.algebraMap A (FractionRing A)) hA

/-- The generic-point square of a local extension commutes in the big fppf site. -/
theorem dvr_genericSite_commutes {R A K : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra R A]
    [Field K] [Algebra R K] [IsFractionRing R K] [IsLocalHom (algebraMap R A)]
    (hinj : Function.Injective (algebraMap R A))
    (hR : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (hK : B.Contains (Spec (.of K))) (hL : B.Contains (Spec (.of (FractionRing A))))
    (j : integerSiteObject B hZ hK ⟶ integerSiteObject B hZ hR)
    (hj : (BigFppfOver.toScheme B integerBase hZ).map j = Spec.algebraMap R K) :
    integerSiteMap B hZ hL hK
        (Spec.map (CommRingCat.ofHom (fractionRingMapOfInjective (K := K)
          (L := FractionRing A) (algebraMap R A) hinj))) ≫ j =
      integerSiteMap B hZ hL hA (Spec.algebraMap A (FractionRing A)) ≫
        integerSiteMap B hZ hA hR (Spec.algebraMap R A) := by
  have hj' : integerSiteMap B hZ hK hR (Spec.algebraMap R K) = j :=
    hj ▸ integerSiteMap_toScheme_map j
  rw [← hj', integerSiteMap_comp, integerSiteMap_comp]
  exact congrArg (integerSiteMap B hZ hL hR)
    (isPullback_genericFiberSpec_of_localHom (K := K) (L := FractionRing A)
      (algebraMap R A) hinj).w

/-- The generic-fibre diagram of the two chosen local models. -/
theorem exists_chartCurveGenericDiagram {U V U' V' : BigFppfOver B integerBase hZ}
    {F F' G G' : CurveFamily B hZ}
    (hF : F.base = V) (hF' : F'.base = V) (hG : G.base = U) (hG' : G'.base = U)
    (j : U ⟶ V) (j' : U' ⟶ V') (k : U' ⟶ U) (a : V' ⟶ V)
    (c : G ⟶ F) (c' : G' ⟶ F') (s : G ⟶ G')
    (hc : (curvesProjectionOver B hZ).IsHomLift j c)
    (hc' : (curvesProjectionOver B hZ).IsHomLift j c')
    (hs : (curvesProjectionOver B hZ).IsHomLift (𝟙 U) s) (hw : k ≫ j = j' ≫ a) :
    ∃ (cL : chartCurve G hG k ⟶ chartCurve F hF a)
      (cL' : chartCurve G' hG' k ⟶ chartCurve F' hF' a)
      (sL : chartCurve G hG k ⟶ chartCurve G' hG' k),
      (curvesProjectionOver B hZ).IsHomLift j' cL ∧
        (curvesProjectionOver B hZ).IsHomLift j' cL' ∧
        (curvesProjectionOver B hZ).IsHomLift (𝟙 U') sL ∧
        cL ≫ chartCurveHom F hF a = chartCurveHom G hG k ≫ c ∧
        cL' ≫ chartCurveHom F' hF' a = chartCurveHom G' hG' k ≫ c' ∧
        sL ≫ chartCurveHom G' hG' k = chartCurveHom G hG k ≫ s := by
  obtain ⟨cL, hcL, hcomp⟩ := exists_lift_chartCurve hG hF j j' k a c hc hw
  obtain ⟨cL', hcL', hcomp'⟩ := exists_lift_chartCurve hG' hF' j j' k a c' hc' hw
  obtain ⟨sL, hsL, hcomps⟩ := exists_lift_chartCurve hG hG' (𝟙 U) (𝟙 U') k k s hs
    (by rw [Category.comp_id, Category.id_comp])
  exact ⟨cL, cL', sL, hcL, hcL', hsL, hcomp, hcomp', hcomps⟩

end AlgebraicGeometry.C1590Private

end
