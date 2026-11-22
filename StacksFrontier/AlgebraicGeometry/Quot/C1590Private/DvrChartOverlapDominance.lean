module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrChartOverlapGlue
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.DvrOverlapHomExt
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesEtaleLocallyProjective

/-!
# Generic agreement on the overlap of representable curve charts

The two overlap maps into the original target lift into the same represented
target chart with the same base coordinate. Generic agreement of their first
coordinates then detects equality by the scheme-level dominance theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Models

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

local notation "Site" => BigFppfOver B integerBase hZ
local notation "Spaces" => AlgebraicSpaces B integerBase hZ
local notation "forgetScheme" => BigFppfOver.toScheme B integerBase hZ

/-- The map from the represented generic fibre of an overlap to its total space. -/
def dvrOverlapGenericProjection {hR : B.Contains (Spec (CommRingCat.of R))} {S : Site}
    {P : Spaces} (ξ : P ≅ schemeSpace S) (r : S ⟶ integerSiteObject B hZ hR)
    (hK : B.Contains (pullback ((forgetScheme).map r) (genericPointInclusion R K))) :
    schemeSpace (CurveFamily.siteObj (hZ := hZ) hK) ⟶ P :=
  schemeSpaceMap (CurveFamily.siteHomOfContains hK
    (pullback.fst ((forgetScheme).map r) (genericPointInclusion R K))) ≫ ξ.inv

set_option backward.isDefEq.respectTransparency false in
private theorem eq_of_chart_generic_agreement
    {hR : B.Contains (Spec (CommRingCat.of R))} {S T V : Site}
    {P Q X : Spaces} (ξ : P ≅ schemeSpace S) (ε : Q ≅ schemeSpace T)
    (r : S ⟶ integerSiteObject B hZ hR) (s : T ⟶ integerSiteObject B hZ hR)
    (a : V ⟶ integerSiteObject B hZ hR) (p : Q ⟶ X) (q : Q ⟶ schemeSpace V)
    (f : X ⟶ schemeSpace (integerSiteObject B hZ hR))
    (hp : IsPullback p q f (schemeSpaceMap a))
    (n₁ n₂ : P ⟶ X) (b : P ⟶ schemeSpace V)
    (hn₁ : n₁ ≫ f = b ≫ schemeSpaceMap a) (hn₂ : n₂ ≫ f = b ≫ schemeSpaceMap a)
    (hr : schemeSpaceMap r = ξ.inv ≫ b ≫ schemeSpaceMap a)
    (hs : schemeSpaceMap s = ε.inv ≫ q ≫ schemeSpaceMap a)
    [hFlat : Flat ((forgetScheme).map r)] [IsSeparated ((forgetScheme).map s)]
    (hK : B.Contains (pullback ((forgetScheme).map r) (genericPointInclusion R K)))
    (hgen : dvrOverlapGenericProjection ξ r hK ≫ n₁ =
      dvrOverlapGenericProjection ξ r hK ≫ n₂) : n₁ = n₂ := by
  let m₁ := hp.lift n₁ b hn₁
  let m₂ := hp.lift n₂ b hn₂
  have hm₁p : m₁ ≫ p = n₁ := hp.lift_fst n₁ b hn₁
  have hm₂p : m₂ ≫ p = n₂ := hp.lift_fst n₂ b hn₂
  have hm₁q : m₁ ≫ q = b := hp.lift_snd n₁ b hn₁
  have hm₂q : m₂ ≫ q = b := hp.lift_snd n₂ b hn₂
  let gK : CurveFamily.siteObj (hZ := hZ) hK ⟶ S :=
    CurveFamily.siteHomOfContains hK (pullback.fst ((forgetScheme).map r) (genericPointInclusion R K))
  have hmK : (schemeSpaceMap gK ≫ ξ.inv) ≫ m₁ = (schemeSpaceMap gK ≫ ξ.inv) ≫ m₂ := by
    apply hp.hom_ext
    · simpa only [Category.assoc, hm₁p, hm₂p, dvrOverlapGenericProjection, gK] using hgen
    · simp only [Category.assoc, hm₁q, hm₂q]
  let represented (m : P ⟶ Q) : S ⟶ T :=
    (schemeSpaceFunctorFullyFaithful B hZ).preimage (ξ.inv ≫ m ≫ ε.hom)
  have hrepresented (m : P ⟶ Q) : schemeSpaceMap (represented m) = ξ.inv ≫ m ≫ ε.hom :=
    (schemeSpaceFunctorFullyFaithful B hZ).map_preimage _
  have hover (m : P ⟶ Q) (hmq : m ≫ q = b) : represented m ≫ s = r := by
    apply schemeSpaceMap_injective
    rw [schemeSpaceMap_comp, hrepresented, hs, hr]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc m q, hmq]
  have hsite : gK ≫ represented m₁ = gK ≫ represented m₂ := by
    apply schemeSpaceMap_injective
    rw [schemeSpaceMap_comp, schemeSpaceMap_comp, hrepresented, hrepresented]
    simpa only [Category.assoc] using
      congrArg (fun k : schemeSpace (CurveFamily.siteObj (hZ := hZ) hK) ⟶ Q => k ≫ ε.hom) hmK
  have hprojection : (forgetScheme).map gK = pullback.fst ((forgetScheme).map r)
      (genericPointInclusion R K) := CurveFamily.toScheme_map_siteHomOfContains _ _
  have hscheme : pullback.fst ((forgetScheme).map r) (genericPointInclusion R K) ≫
      (forgetScheme).map (represented m₁) = pullback.fst ((forgetScheme).map r)
      (genericPointInclusion R K) ≫ (forgetScheme).map (represented m₂) := by
    have h := congrArg
      (fun k : CurveFamily.siteObj (hZ := hZ) hK ⟶ T => (forgetScheme).map k) hsite
    rw [Functor.map_comp, Functor.map_comp, hprojection] at h
    exact h
  have hoverScheme (m : P ⟶ Q) (hmq : m ≫ q = b) :
      (forgetScheme).map (represented m) ≫ (forgetScheme).map s = (forgetScheme).map r := by
    rw [← Functor.map_comp, hover m hmq]
  have hdom : IsSchemeTheoreticallyDominant
      (pullback.fst ((forgetScheme).map r) (genericPointInclusion R K)) :=
    @isSchemeTheoreticallyDominant_genericFiber_fst R K _ _ _ _ _ _ ((forgetScheme).map r) hFlat
  have hmaps := eq_of_comp_isSchemeTheoreticallyDominant
    (pullback.fst ((forgetScheme).map r) (genericPointInclusion R K))
    ((forgetScheme).map (represented m₁)) ((forgetScheme).map (represented m₂)) ((forgetScheme).map s)
    ((hoverScheme m₁ hm₁q).trans (hoverScheme m₂ hm₂q).symm) hscheme
  have hbetween : represented m₁ = represented m₂ := (forgetScheme).map_injective hmaps
  have hconjugates : ξ.inv ≫ m₁ ≫ ε.hom = ξ.inv ≫ m₂ ≫ ε.hom := by
    rw [← hrepresented m₁, ← hrepresented m₂, hbetween]
  have hm : m₁ = m₂ := by
    apply (cancel_mono ε.hom).mp
    exact (cancel_epi ξ.inv).mp hconjugates
  exact hm₁p.symm.trans ((congrArg (fun m : P ⟶ Q => m ≫ p) hm).trans hm₂p)

/-- Generic agreement of the two restrictions of a local isomorphism on the
original generic overlap implies the exact compatibility used by curve-family
descent. The represented target is the one common target chart. -/
theorem dvrChartOverlapAgrees_of_generic
    {hR : B.Contains (Spec (CommRingCat.of R))} {V S T : Site}
    (F F' : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hR)
    (hF' : F'.base = integerSiteObject B hZ hR) (a : V ⟶ integerSiteObject B hZ hR)
    (e : (F.ofBaseEq hF).pullback a ≅ (F'.ofBaseEq hF').pullback a)
    (he : e.hom.baseMap = 𝟙 V)
    (r : S ⟶ integerSiteObject B hZ hR) (s : T ⟶ integerSiteObject B hZ hR)
    [Flat ((forgetScheme).map r)] [IsSeparated ((forgetScheme).map s)]
    (hK : B.Contains (pullback ((forgetScheme).map r) (genericPointInclusion R K)))
    (ε : ((F'.ofBaseEq hF').pullback a).total ≅ schemeSpace T)
    (hs : schemeSpaceMap s = ε.inv ≫ ((F'.ofBaseEq hF').pullback a).toBase ≫ schemeSpaceMap a) :
    let F₀ := F.ofBaseEq hF
    let p := F₀.pullbackHom a
    let w := pullback.fst p.baseMap p.baseMap ≫ p.baseMap
    let O := restrictX F₀ w
    let r₁ := factorX p w (pullback.fst p.baseMap p.baseMap) rfl
    let r₂ := factorX p w (pullback.snd p.baseMap p.baseMap) pullback.condition.symm
    let n := e.hom.totalMap ≫ ((F'.ofBaseEq hF').pullbackHom a).totalMap
    ∀ (ξ : O.total ≅ schemeSpace S),
      schemeSpaceMap r = ξ.inv ≫ (O.toBase ≫ schemeSpaceMap r₁.baseMap) ≫ schemeSpaceMap a →
      dvrOverlapGenericProjection ξ r hK ≫ (r₁.totalMap ≫ n) =
        dvrOverlapGenericProjection ξ r hK ≫ (r₂.totalMap ≫ n) →
      DvrChartOverlapAgrees p n := by
  dsimp only
  let F₀ := F.ofBaseEq hF
  let F₁ := F'.ofBaseEq hF'
  let A := F₀.pullback a
  let A' := F₁.pullback a
  let p := F₀.pullbackHom a
  let p' := F₁.pullbackHom a
  let w := pullback.fst p.baseMap p.baseMap ≫ p.baseMap
  let O := restrictX F₀ w
  let r₁ := factorX p w (pullback.fst p.baseMap p.baseMap) rfl
  let r₂ := factorX p w (pullback.snd p.baseMap p.baseMap) pullback.condition.symm
  let n : A.total ⟶ F₁.total := e.hom.totalMap ≫ p'.totalMap
  intro ξ hr hgen
  change r₁.totalMap ≫ n = r₂.totalMap ≫ n
  let b : O.total ⟶ schemeSpace V := O.toBase ≫ schemeSpaceMap r₁.baseMap
  have hid : schemeSpaceMap (𝟙 V) = 𝟙 (schemeSpace V) :=
    (schemeSpaceFunctor B integerBase hZ).map_id V
  have heOver : e.hom.totalMap ≫ A'.toBase = A.toBase := by
    simpa only [he, hid, Category.comp_id] using e.hom.cartesian.w
  have hnOver : n ≫ F₁.toBase = A.toBase ≫ schemeSpaceMap a := by
    change (e.hom.totalMap ≫ p'.totalMap) ≫ F₁.toBase = _
    rw [Category.assoc, (F₁.isPullback_pullbackHom a).w, ← Category.assoc, heOver]
  have hbase : r₂.baseMap ≫ a = r₁.baseMap ≫ a := by
    have h : r₂ ≫ p = r₁ ≫ p := (factorX_comp p w _ _).trans (factorX_comp p w _ _).symm
    simpa only [CurveFamily.comp_baseMap, p, CurveFamily.pullbackHom_baseMap] using
      congrArg (fun k : O ⟶ F₀ => k.baseMap) h
  have hrestr (k : O ⟶ A) (hk : k.baseMap ≫ a = r₁.baseMap ≫ a) :
      (k.totalMap ≫ n) ≫ F₁.toBase = b ≫ schemeSpaceMap a := by
    rw [Category.assoc, hnOver, ← Category.assoc, k.cartesian.w]
    simp only [b, Category.assoc, ← schemeSpaceMap_comp, hk]
  exact eq_of_chart_generic_agreement ξ ε r s a p'.totalMap A'.toBase F₁.toBase
    (F₁.isPullback_pullbackHom a) (r₁.totalMap ≫ n) (r₂.totalMap ≫ n) b
    (hrestr r₁ rfl) (hrestr r₂ hbase) hr hs hK hgen

end AlgebraicGeometry.C1590Private

end
