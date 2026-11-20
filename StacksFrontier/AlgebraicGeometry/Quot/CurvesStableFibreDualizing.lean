module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableSmoothGenusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenus
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.AffineBase
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre

/-! # Dualizing ampleness on a single stable curve fibre -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

/-- **A nodal curve over a field.** Let `f : X ⟶ Spec k` be at-worst-nodal of relative dimension
one with `Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)` bijective. Then `X` has dimension one and at-worst-nodal
singularities over `k`. The bijectivity makes `X` nonempty, and Stacks 0C59 describes the fibre
of `f` over the point of `Spec k`, which is `X`. -/
theorem topologicalKrullDim_eq_one_and_hasAtWorstNodalSingularities_of_isAtWorstNodal
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (hglob : Function.Bijective f.appTop) :
    topologicalKrullDim X = 1 ∧
      @Stacks.Curves.HasAtWorstNodalSingularities k _ X ⟨f⟩ := by
  have hne : Nonempty X := by
    by_contra hne
    have : IsEmpty X := not_nonempty_iff.mp hne
    have h01 : (0 : Γ(Spec (.of k), ⊤)) = 1 := hglob.1 (Subsingleton.elim _ _)
    have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom h01
    rw [map_zero, map_one] at h
    exact zero_ne_one h
  obtain ⟨-, hlfp, h⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).mpr hf
  have : LocallyOfFinitePresentation f := hlfp
  let j : Spec (.of k) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (RingHom.id k))
  have := isIso_descResidueField_of_surjective (RingHom.id k) Function.surjective_id
  have hj : j = 𝟙 _ := Spec.map_id _
  have : IsIso j := by
    rw [hj]
    infer_instance
  obtain ⟨E, -, hE⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField f j
  let e : X ⟶ f.fiber (j (IsLocalRing.closedPoint k)) := inv (pullback.fst f j) ≫ E.inv
  obtain ⟨-, hdim, hnodal⟩ := h _ ⟨e (Classical.arbitrary X)⟩
  let φ : CommRingCat.of k ⟶ CommRingCat.of ((Spec (.of k)).residueField
      (j (IsLocalRing.closedPoint k))) :=
    inv ((Spec (.of k)).descResidueField (Scheme.stalkClosedPointTo j))
  have : IsIso φ := IsIso.inv_isIso
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (j (IsLocalRing.closedPoint k))) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have hsnd : pullback.snd f j = pullback.fst f j ≫ f :=
    calc pullback.snd f j = pullback.snd f j ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = pullback.snd f j ≫ j := by rw [hj]
      _ = pullback.fst f j ≫ f := pullback.condition.symm
  have he : e ≫ f.fiberToSpecResidueField _ ≫ Spec.map φ = f := by
    rw [← hE]
    simp only [e, φ, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, IsIso.inv_hom_id,
      Spec.map_id, Category.comp_id, hsnd, IsIso.inv_hom_id_assoc]
  refine ⟨?_, Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ f hdim e φ he hnodal⟩
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso e)).isHomeomorph, hdim]

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **The fibre of a prestable family over a field-valued point is a proper nodal curve with
`H⁰ = k`.** Let `V` present the fibre of a prestable family `G` over a field-valued point
`Spec k → S`. Then `V` is proper over `k`, of dimension one, with `k = H⁰(V, 𝒪_V)` and
at-worst-nodal singularities. The fibre is itself a prestable family over `Spec k`; its
structure morphism is at-worst-nodal of relative dimension one and has bijective pullback of
global functions, and
`AlgebraicGeometry.topologicalKrullDim_eq_one_and_hasAtWorstNodalSingularities_of_isAtWorstNodal`
applies. -/
theorem isProper_and_dim_and_bijective_and_nodal_fibre {G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ G.total.obj}
    (hsq : IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value)) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) ∧
      topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) = 1 ∧
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map v).appTop ∧
      @Stacks.Curves.HasAtWorstNodalSingularities p.carrier _
        ((BigFppfOver.toScheme B integerBase hZ).obj V)
        ⟨(BigFppfOver.toScheme B integerBase hZ).map v⟩ := by
  have hF : IsPrestableCurveFamily B hZ (G.fibreFamily hsq) :=
    isPrestableCurveFamily_of_hom (G.fibreFamilyHom hsq) hG
  have hglob : Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map v).appTop :=
    (Space.bijective_globalFunctionsMap_schemeSpaceMap_iff v).1 (by
      have h := HasUniversallyBijectiveGlobalFunctions.bijective_globalFunctionsMap B hZ hF.2
      exact h)
  have hnod : IsAtWorstNodalOfRelativeDimensionOne
      ((BigFppfOver.toScheme B integerBase hZ).map v) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget v).1 hF.1
  obtain ⟨hdim, hnodal⟩ :=
    topologicalKrullDim_eq_one_and_hasAtWorstNodalSingularities_of_isAtWorstNodal p.carrier
      ((BigFppfOver.toScheme B integerBase hZ).map v) hnod hglob
  exact ⟨G.isProper_fibre hsq, hdim, hglob, hnodal⟩

/-- **Stacks 0E74 on one fibre.** Let `ω` be a relative dualizing sheaf of a prestable family `G`
and `V` a presentation of the fibre of `G` over a field-valued point `Spec k → S`. The fibre has
genus at least two and neither a rational tail nor a rational bridge exactly when the pullback of
`ω` to `V` is invertible and ample relative to `V ⟶ Spec k`.

The pullback of `ω` to `V` is the dualizing sheaf `ω_V`, and `V` is a proper nodal curve with
`H⁰ = k` (`AlgebraicGeometry.CurveFamily.isProper_and_dim_and_bijective_and_nodal_fibre`), so
`hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField_of`
(Stacks 0E3P and its converse) applies; over the spectrum of a field relative ampleness is
ampleness (Stacks 01VT, `AlgebraicGeometry.Scheme.Modules.isRelativelyAmple_iff_isAmple`). -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_fibre_iff {G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G)
    {ω : Space.Modules.{u, u} B integerBase hZ G.total.1 G.total.2}
    (hω : G.IsRelativeDualizingSheaf B hZ ω)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ G.total.obj}
    (hsq : IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value)) :
    HasGenusTwoNoRationalTailNoRationalBridge p.carrier
        ((BigFppfOver.toScheme B integerBase hZ).map v) ↔
      ∃ hinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B integerBase hZ).obj V)
          (Space.baseChangeModule B integerBase hZ ω V q),
        @Stacks.RelativeAmple.IsRelativelyAmple _ _ ((BigFppfOver.toScheme B integerBase hZ).map v)
          (Space.baseChangeModule B integerBase hZ ω V q) hinv := by
  obtain ⟨hproper, ⟨e⟩⟩ := hω.2 p V v q hsq
  obtain ⟨-, hdim, hglob, hnodal⟩ := isProper_and_dim_and_bijective_and_nodal_fibre hG hsq
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj p.siteObject) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))
  have : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  rw [hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField_of
    isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail hd hn C hC)
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge hd hn C hC)
    (fun κ _ _ f _ _ _ hd _ _ => invertibleCurveDegree_dualizingSheafOverField κ f hd)
    p.carrier _ hdim hglob hnodal]
  constructor
  · rintro ⟨hinv, hamp⟩
    have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B integerBase hZ).obj V)
        (Space.baseChangeModule B integerBase hZ ω V q) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
    exact ⟨inferInstance, (Scheme.Modules.isRelativelyAmple_iff_isAmple _ _).2
      (Scheme.Modules.isAmple_of_iso e.symm hamp)⟩
  · rintro ⟨hinv, hamp⟩
    have : SheafOfModules.IsInvertible
        ((BigFppfOver.toScheme B integerBase hZ).obj V).toRingedSpace.presheaf
        (structureSheafRing ((BigFppfOver.toScheme B integerBase hZ).obj V).toRingedSpace).property
        (Stacks.Duality.dualizingSheafOverField ((BigFppfOver.toScheme B integerBase hZ).map v)) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
    exact ⟨inferInstance, Scheme.Modules.isAmple_of_iso e
      ((Scheme.Modules.isRelativelyAmple_iff_isAmple _ _).1 hamp)⟩

end CurveFamily

end AlgebraicGeometry

end
