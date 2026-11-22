module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrChartIsoDescent
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelDescent
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering

/-!
# Gluing a common chart isomorphism of two curve families

The necessary compatibility is the equality on one chosen overlap. The
restriction maps are the existing cartesian factorizations of the source
chart projection, so the equality concerns the actual local isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The two restrictions of a local total-space map agree on the actual overlap. -/
def DvrChartOverlapAgrees {A F F' : CurveFamily B hZ} (p : A ⟶ F)
    (n : A.total ⟶ F'.total) : Prop :=
  let a := p.baseMap
  let w := pullback.fst a a ≫ a
  (factorX p w (pullback.fst a a) rfl).totalMap ≫ n =
    (factorX p w (pullback.snd a a) pullback.condition.symm).totalMap ≫ n

/-- An isomorphism of the two canonical chart pullbacks agreeing on the
single overlap descends to an isomorphism over the original base. The
returned projection equation identifies it with the supplied chart map. -/
theorem exists_iso_of_dvrChartOverlap {U V : BigFppfOver B integerBase hZ}
    (F F' : CurveFamily B hZ) (hF : F.base = U) (hF' : F'.base = U) (a : V ⟶ U)
    (hsurj : Surjective ((BigFppfOver.toScheme B integerBase hZ).map a))
    (het : Etale ((BigFppfOver.toScheme B integerBase hZ).map a))
    (e : (F.ofBaseEq hF).pullback a ≅ (F'.ofBaseEq hF').pullback a)
    (he : e.hom.baseMap = 𝟙 V)
    (hoverlap : DvrChartOverlapAgrees ((F.ofBaseEq hF).pullbackHom a)
      (e.hom.totalMap ≫ ((F'.ofBaseEq hF').pullbackHom a).totalMap)) :
    ∃ t : F ≅ F', (curvesProjectionOver B hZ).IsHomLift (𝟙 U) t.hom ∧
      ((F.ofBaseEq hF).pullbackHom a).totalMap ≫ t.hom.totalMap =
        e.hom.totalMap ≫ ((F'.ofBaseEq hF').pullbackHom a).totalMap := by
  let F₀ := F.ofBaseEq hF
  let F₁ := F'.ofBaseEq hF'
  let A := F₀.pullback a
  let A' := F₁.pullback a
  let p := F₀.pullbackHom a
  let p' := F₁.pullbackHom a
  let n : A.total ⟶ F₁.total := e.hom.totalMap ≫ p'.totalMap
  let member : Unit → CurveFamily B hZ := fun _ => A
  let chart : ∀ i, member i ⟶ F₀ := fun _ => p
  have hid : schemeSpaceMap (𝟙 V) = 𝟙 (schemeSpace V) :=
    (schemeSpaceFunctor B integerBase hZ).map_id V
  have heOver : e.hom.totalMap ≫ A'.toBase = A.toBase := by
    simpa only [he, hid, Category.comp_id] using e.hom.cartesian.w
  have hnOver : n ≫ F₁.toBase = A.toBase ≫ schemeSpaceMap a := by
    change (e.hom.totalMap ≫ p'.totalMap) ≫ F₁.toBase = _
    rw [Category.assoc, (F₁.isPullback_pullbackHom a).w, ← Category.assoc, heOver]
  have hcov : Sieve.ofArrows (fun i => (member i).base) (fun i => (chart i).baseMap) ∈
      BigFppfOver.topology B integerBase hZ F₀.base := by
    change Sieve.generate (Presieve.ofArrows (fun _ : Unit => V)
      (fun _ => (F₀.pullbackHom a).baseMap)) ∈ BigFppfOver.topology B integerBase hZ U
    rw [CurveFamily.pullbackHom_baseMap, Presieve.ofArrows_of_unique]
    exact Space.sieve_generate_singleton_mem_topology_over B integerBase hZ a hsurj het
  have hyonedaId : yoneda.map (eqToHom (rfl : F₁.base = F₁.base)) =
      𝟙 (yoneda.obj F₁.base) :=
    (congrArg (fun f : F₁.base ⟶ F₁.base => yoneda.map f) (eqToHom_refl _ rfl)).trans
      (yoneda.map_id F₁.base)
  obtain ⟨m, hm, hres⟩ := exists_glue_out member chart (show F₁.base = F₀.base from rfl)
    hcov (fun _ => n) (fun i => by
      cases i
      change n.hom ≫ yonedaToBase F₁ ≫ yoneda.map (eqToHom rfl) =
        yonedaToBase A ≫ yoneda.map p.baseMap
      rw [hyonedaId, Category.comp_id]
      have hh := congrArg (fun (f : A.total ⟶ schemeSpace U) => f.hom) hnOver
      change n.hom ≫ F₁.toBase.hom = A.toBase.hom ≫ (schemeSpaceMap a).hom at hh
      change n.hom ≫ F₁.toBase.hom = A.toBase.hom ≫ (schemeSpaceMap p.baseMap).hom
      rw [show p.baseMap = a from CurveFamily.pullbackHom_baseMap F₀ a]
      exact hh)
    (fun i j => by cases i; cases j; exact hoverlap)
  have hmOver : m ≫ F₁.toBase = F₀.toBase := by
    apply ObjectProperty.hom_ext
    change m.hom ≫ yonedaToBase F₁ = yonedaToBase F₀
    have hc := congrArg (fun f : yoneda.obj F₁.base ⟶ yoneda.obj F₁.base =>
      m.hom ≫ yonedaToBase F₁ ≫ f) hyonedaId
    exact (congrArg (m.hom ≫ ·) (Category.comp_id (yonedaToBase F₁))).symm.trans
      (hc.symm.trans hm)
  have hchart : p.totalMap ≫ m = e.hom.totalMap ≫ p'.totalMap := hres ()
  have hcovSpace : Space.IsFppfCovering B integerBase hZ
      (fun _ : Unit => (schemeSpace V).obj) (fun _ => (schemeSpaceMap a).hom) := by
    let : Etale ((BigFppfOver.toScheme B integerBase hZ).map a) := het
    refine Space.isFppfCovering_yoneda_map B integerBase hZ (fun _ : Unit => V)
      (fun _ => a) (fun _ => inferInstance) (fun _ => inferInstance) ?_
    intro y
    obtain ⟨x, hx⟩ := hsurj.surj y
    exact ⟨(), x, hx⟩
  let q := F₀.isPullback_pullbackHom a
  let q' := F₁.isPullback_pullbackHom a
  have : IsIso e.hom.baseMap := by rw [he]; infer_instance
  have : IsIso e.hom.totalMap := CurveFamily.isIso_totalMap_of_isIso_baseMap e.hom
  let ell : pullback F₀.toBase (schemeSpaceMap a) ≅ pullback F₁.toBase (schemeSpaceMap a) :=
    q.isoPullback.symm ≪≫ (asIso e.hom.totalMap ≪≫ q'.isoPullback)
  have hfst : ell.hom ≫ pullback.fst F₁.toBase (schemeSpaceMap a) =
      pullback.fst F₀.toBase (schemeSpaceMap a) ≫ m := by
    change (q.isoPullback.inv ≫ (e.hom.totalMap ≫ q'.isoPullback.hom)) ≫ _ = _
    rw [Category.assoc, Category.assoc, q'.isoPullback_hom_fst, ← hchart,
      ← Category.assoc, q.isoPullback_inv_fst]
  have hsnd : ell.hom ≫ pullback.snd F₁.toBase (schemeSpaceMap a) =
      pullback.snd F₀.toBase (schemeSpaceMap a) := by
    change (q.isoPullback.inv ≫ (e.hom.totalMap ≫ q'.isoPullback.hom)) ≫ _ = _
    rw [Category.assoc, Category.assoc, q'.isoPullback_hom_snd, heOver, q.isoPullback_inv_snd]
  have : IsIso m := Space.isIso_of_isIso_after_base_chart B integerBase hZ
    F₀.toBase F₁.toBase (schemeSpaceMap a) hcovSpace m hmOver ell.hom hfst hsnd
  have hidU : schemeSpaceMap (𝟙 U) = 𝟙 (schemeSpace U) :=
    (schemeSpaceFunctor B integerBase hZ).map_id U
  let t₀ : F₀ ≅ F₁ := CurveFamily.isoMk (Iso.refl U) (asIso m) (by
    change m ≫ F₁.toBase = F₀.toBase ≫ schemeSpaceMap (𝟙 U)
    rw [hidU, Category.comp_id]
    exact hmOver)
  let t : F ≅ F' := (F.ofBaseEqIso hF).symm ≪≫ (t₀ ≪≫ F'.ofBaseEqIso hF')
  refine ⟨t, IsHomLift.of_fac' (curvesProjectionOver B hZ) (𝟙 U) t.hom hF hF' ?_, ?_⟩
  · have hinv : (F.ofBaseEqIso hF).inv.baseMap = eqToHom hF := by cases hF; rfl
    change (F.ofBaseEqIso hF).inv.baseMap ≫ (𝟙 U) ≫
      (F'.ofBaseEqIso hF').hom.baseMap = eqToHom hF ≫ 𝟙 U ≫ eqToHom hF'.symm
    rw [hinv, CurveFamily.ofBaseEqIso_hom_baseMap]
  · change p.totalMap ≫ (𝟙 F.total ≫ (m ≫ 𝟙 F'.total)) = _
    calc
      _ = p.totalMap ≫ (m ≫ 𝟙 F'.total) :=
        congrArg (p.totalMap ≫ ·) (Category.id_comp (m ≫ 𝟙 F'.total))
      _ = p.totalMap ≫ m := congrArg (p.totalMap ≫ ·) (Category.comp_id m)
      _ = _ := hchart

end AlgebraicGeometry.C1590Private

end
