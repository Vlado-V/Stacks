module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveMorFunctorsEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeGlue
public import StacksFrontier.RingTheory.Etale.DiscreteValuationLocalization

/-!
# Common scheme representations over an étale DVR cover

The common affine charts of finitely many curve families can be refined near
the closed point of a discrete valuation ring to a surjective étale map from
another discrete valuation ring. Their pullbacks to that single cover have
scheme total spaces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

private theorem exists_etaleDvrCover_of_affine_etale_over_closedPoint
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : B.Contains (Spec (.of R))) {V : BigFppfOver B integerBase hZ}
    (φ : V ⟶ integerSiteObject B hZ hR)
    (hφ : Etale ((BigFppfOver.toScheme B integerBase hZ).map φ))
    (hV : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj V))
    (v : (BigFppfOver.toScheme B integerBase hZ).obj V)
    (hv : (BigFppfOver.toScheme B integerBase hZ).map φ v = IsLocalRing.closedPoint R) :
    ∃ (L : Type u) (_ : CommRing L) (_ : IsDomain L) (_ : IsDiscreteValuationRing L)
      (_ : Algebra R L) (_ : IsDiscreteValuationRing.IsExtension R L) (_ : Algebra.Etale R L)
      (hL : B.Contains (Spec (.of L))) (j : integerSiteObject B hZ hL ⟶ V),
      j ≫ φ = integerSiteMap B hZ hL hR (Spec.algebraMap R L) ∧
        Surjective (Spec.algebraMap R L) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  let W := T.obj V
  let : IsAffine W := hV
  let A := Γ(W, ⊤)
  let fφ : W ⟶ Spec (.of R) := T.map φ
  let f : Spec A ⟶ Spec (.of R) := W.isoSpec.inv ≫ fφ
  let : Etale fφ := hφ
  let : Algebra R A := (Spec.preimage f).hom.toAlgebra
  have hSpec : Spec.algebraMap R A = f := Spec.map_preimage f
  have hEt : Etale (Spec.algebraMap R A) := by
    rw [hSpec]
    change Etale (W.isoSpec.inv ≫ fφ)
    infer_instance
  let : Algebra.Etale R A := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hEt)
  let q : PrimeSpectrum A := W.isoSpec.hom v
  have hq : PrimeSpectrum.comap (algebraMap R A) q = IsLocalRing.closedPoint R := by
    have hinv : W.isoSpec.inv (W.isoSpec.hom v) = v :=
      (Scheme.homeoOfIso W.isoSpec).symm_apply_apply v
    let closed : Spec (.of R) := IsLocalRing.closedPoint R
    have hφv : fφ v = closed := hv
    have happly : (Spec.algebraMap R A) q = f q :=
      congrArg (fun g : Spec A ⟶ Spec (.of R) => g q) hSpec
    have hcomp : f q = fφ (W.isoSpec.inv (W.isoSpec.hom v)) :=
      Scheme.Hom.comp_apply _ _ _
    have hpoint : fφ (W.isoSpec.inv (W.isoSpec.hom v)) = fφ v :=
      congrArg (fun w : W => fφ w) hinv
    exact happly.trans (hcomp.trans (hpoint.trans hφv))
  obtain ⟨hd, hdvr, hext, hEtR, _⟩ :=
    Stacks.Models.exists_isDiscreteValuationRing_localizationAtPrime_of_etale q hq
  let L := Localization.AtPrime q.asIdeal
  let : IsDomain L := hd
  let : IsDiscreteValuationRing L := hdvr
  let : IsDiscreteValuationRing.IsExtension R L := hext
  let : Algebra.Etale R L := hEtR
  let : Etale (Spec.algebraMap R L) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hEtR)
  have hL : B.Contains (Spec (.of L)) :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B (Spec.algebraMap R L) hR
  let j : integerSiteObject B hZ hL ⟶ V :=
    CurveFamily.siteHom (Spec.algebraMap A L ≫ W.isoSpec.inv)
  have hcomp : j ≫ φ = integerSiteMap B hZ hL hR (Spec.algebraMap R L) := by
    apply T.map_injective
    rw [Functor.map_comp, CurveFamily.toScheme_map_siteHom]
    change (Spec.algebraMap A L ≫ W.isoSpec.inv) ≫ fφ = Spec.algebraMap R L
    calc
      (Spec.algebraMap A L ≫ W.isoSpec.inv) ≫ fφ = Spec.algebraMap A L ≫ f :=
        Category.assoc _ _ _
      _ = Spec.algebraMap A L ≫ Spec.algebraMap R A :=
        congrArg (fun g : Spec A ⟶ Spec (.of R) => Spec.algebraMap A L ≫ g) hSpec.symm
      _ = Spec.algebraMap R L := by
        change _ = Spec.map (CommRingCat.ofHom (algebraMap R L))
        rw [IsScalarTower.algebraMap_eq R A L, CommRingCat.ofHom_comp, Spec.map_comp] <;> rfl
  let : Module.FaithfullyFlat R L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨L, inferInstance, hd, hdvr, inferInstance, hext, hEtR, hL, j, hcomp,
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := L)⟩⟩

/-- Finitely many families with base `Spec R` have scheme total spaces after
pullback along one surjective étale extension of discrete valuation rings. -/
theorem exists_etaleDvrCover_schemeRepresentations
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : B.Contains (Spec (.of R))) {ι : Type*} [Finite ι]
    (X : ι → CurveFamily B hZ) (hX : ∀ i, (X i).base = integerSiteObject B hZ hR) :
    ∃ (L : Type u) (_ : CommRing L) (_ : IsDomain L) (_ : IsDiscreteValuationRing L)
      (_ : Algebra R L) (_ : IsDiscreteValuationRing.IsExtension R L) (_ : Algebra.Etale R L)
      (hL : B.Contains (Spec (.of L))), Surjective (Spec.algebraMap R L) ∧
      ∀ i, ∃ (Y : Scheme.{u}) (hY : B.Contains Y),
        Nonempty ((((X i).ofBaseEq (hX i)).pullback
          (integerSiteMap B hZ hL hR (Spec.algebraMap R L))).total ≅
            schemeSpace (integerSiteObject B hZ hY)) := by
  let F (i : ι) := (X i).ofBaseEq (hX i)
  let S := integerSiteObject B hZ hR
  have hF (i : ι) : (F i).base = S := rfl
  obtain ⟨V, φ, v, hφ, hV, hv, charts⟩ :=
    exists_affine_etale_isPullback_isProjectiveMorphism
      F hF (fun i => curvesSmoothLocallyPolarized B hZ (F i))
      (IsLocalRing.closedPoint R)
  obtain ⟨L, hComm, hDom, hDvr, hAlg, hExt, hEt, hL, j, hj, hsurj⟩ :=
    exists_etaleDvrCover_of_affine_etale_over_closedPoint hR φ hφ hV v hv
  refine ⟨L, hComm, hDom, hDvr, hAlg, hExt, hEt, hL, hsurj, fun i => ?_⟩
  obtain ⟨Z, p, q, hChart, _⟩ := charts i
  have hφ' : φ ≫ eqToHom (hF i).symm = φ := by
    change φ ≫ eqToHom (rfl : S = S) = φ
    rw [eqToHom_refl, Category.comp_id]
  have hChart' : IsPullback p (schemeSpaceMap q) (F i).toBase (schemeSpaceMap φ) :=
    Eq.mp (congrArg (fun a : V ⟶ S =>
      IsPullback p (schemeSpaceMap q) (F i).toBase (schemeSpaceMap a)) hφ') hChart
  let k := integerSiteMap B hZ hL hR (Spec.algebraMap R L)
  have hBottom : schemeSpaceMap j ≫ schemeSpaceMap φ = schemeSpaceMap k :=
    (schemeSpaceMap_comp j φ).symm.trans
      (congrArg (fun a : integerSiteObject B hZ hL ⟶ S => schemeSpaceMap a) hj)
  have hSquare := Eq.mp (congrArg
    (fun a : schemeSpace (integerSiteObject B hZ hL) ⟶ schemeSpace S =>
      IsPullback (schemeSpaceMap (pullback.fst q j) ≫ p)
        (schemeSpaceMap (pullback.snd q j)) (F i).toBase a) hBottom)
    ((CurveFamily.isPullback_schemeSpaceMap_fst_snd q j).paste_horiz hChart')
  let U := pullback q j
  let Y := (BigFppfOver.toScheme B integerBase hZ).obj U
  have hY : B.Contains Y := U.left.property
  let e : U ≅ integerSiteObject B hZ hY :=
    Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  let e' : ((F i).pullback k).total ≅ schemeSpace U :=
    IsPullback.isoIsPullback (F i).total (schemeSpace (integerSiteObject B hZ hL))
      ((F i).isPullback_pullbackHom k) hSquare
  exact ⟨Y, hY, ⟨e' ≪≫ (schemeSpaceFunctor B integerBase hZ).mapIso e⟩⟩

end AlgebraicGeometry.C1590Private

end
