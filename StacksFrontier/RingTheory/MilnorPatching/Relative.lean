module

public import StacksFrontier.RingTheory.MilnorPatching.RelativeCore

/-!
# Coherence of the relative scalar extension square

This module retains the natural isomorphism of the two functor composites
and its tensor formulas. Import `RelativeCore` for the relative patching
data and the individual component base changes.
-/

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

universe uA uA' uB uD' v uR uS uT uU w

namespace MilnorPatching
open ModuleGlueing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

/-- Transport the tensor law through an equality of gluing isomorphisms. -/
private lemma extensionIso_one_tmul_of_eq
    {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (i : T →+* U)
    (comm : h.comp f = i.comp g)
    (M : ModuleCat.{max w uS uT uU} R) (m : M)
    (e : (ModuleCat.extendScalars h).obj ((ModuleCat.extendScalars f).obj M) ≅
      (ModuleCat.extendScalars i).obj ((ModuleCat.extendScalars g).obj M))
    (he : e = ((extensionOfScalarsToPullback f g h i comm).obj M).iso) :
    e.hom ((1 : U) ⊗ₜ[S,h] ((1 : S) ⊗ₜ[R,f] m)) =
      (1 : U) ⊗ₜ[T,i] ((1 : T) ⊗ₜ[R,g] m) := by
  subst e
  exact extension_iso_one_tmul f g h i comm M m

variable {A : Type uA} {A' : Type uA'} {B : Type uB} {D' : Type uD'}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
variable {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}

namespace RelativeModuleFibreProductSituation

variable {base : RingFibreProduct.Situation toBase surjection I}
    (s : RelativeModuleFibreProductSituation (D' := D') base)

set_option maxHeartbeats 8000000 in
-- unifying the gluing isomorphism with `extensionIso_one_tmul_of_eq` and the closing `rfl` is slow
/-- The gluing isomorphism of scalar extension preserves tensors of `1`. -/
public theorem extensionOfScalarsToTensorProductPullback_iso_one_tmul
    (L : ModuleCat.{max v uA uA' uB uD'} D') (l : L) :
    letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    letI : Algebra base.fibreProduct B := (toB (base := base)).toAlgebra
    letI : Algebra base.fibreProduct A' := (toA' (base := base)).toAlgebra
    letI : Algebra base.fibreProduct A := (toA (base := base)).toAlgebra
    ((extensionOfScalarsToTensorProductPullback.{_, _, _, _, _, v} (D' := D')
        ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
        ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
          A)).obj L).iso.hom
      ((1 : s.C) ⊗ₜ[s.D,s.DtoC] ((1 : s.D) ⊗ₜ[D',s.toD] l)) =
      (1 : s.C) ⊗ₜ[s.C',s.C'toC] ((1 : s.C') ⊗ₜ[D',s.toC'] l) := by
  let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
  let : Algebra base.fibreProduct B := (toB (base := base)).toAlgebra
  let : Algebra base.fibreProduct A' := (toA' (base := base)).toAlgebra
  let : Algebra base.fibreProduct A := (toA (base := base)).toAlgebra
  exact extensionIso_one_tmul_of_eq.{_, _, _, _, v}
      s.toD s.toC' s.DtoC s.C'toC s.relativeSquare_comm L l
      ((extensionOfScalarsToTensorProductPullback.{_, _, _, _, _, v} (D' := D')
        ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
        ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
          A)).obj L).iso
      rfl

set_option maxHeartbeats 1000000 in
-- was section-wide; the statement elaborates tensor base change over `base.fibreProduct`
/-- The component base-change maps respect the gluing isomorphisms. -/
public theorem restrictionSquare_coherence
    (L : ModuleCat.{max v uA uA' uB uD'} D') :
    letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    letI : Algebra base.fibreProduct B := (toB (base := base)).toAlgebra
    letI : Algebra base.fibreProduct A' := (toA' (base := base)).toAlgebra
    letI : Algebra base.fibreProduct A := (toA (base := base)).toAlgebra
    (ModuleCat.extendScalars toBase).map
        (s.extensionRestrictionFstIso.{uA, uA', uB, uD', v}.inv.app L) ≫
      (s.restrictionFstIso.{uA, uA', uB, uD', v}.inv.app
          ((ModuleCat.extendScalars s.toD).obj L) ≫
        (ModuleCat.restrictScalars s.AtoC).map
          ((extensionOfScalarsToTensorProductPullback.{_, _, _, _, _, v} (D' := D')
              ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
              ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
                A)).obj L).iso.hom ≫
        s.restrictionSndIso.{uA, uA', uB, uD', v}.hom.app
          ((ModuleCat.extendScalars s.toC').obj L)) =
      ((extensionOfScalarsToPullback.{max v uD'}
          (toB (base := base)) (toA' (base := base)) toBase surjection
          (RingHom.pullback_comm_sq toBase surjection)).obj
        ((ModuleCat.restrictScalars s.toD').obj L)).iso.hom ≫
      (ModuleCat.extendScalars surjection).map
        (s.extensionRestrictionSndIso.{uA, uA', uB, uD', v}.inv.app L) := by
  apply extendScalars_twice_hom_ext.{_, _, _, max v uD'}
    (toB (base := base)) toBase
    ((ModuleCat.restrictScalars s.toD').obj L)
  intro l
  let LB := (ModuleCat.extendScalars s.toD).obj L
  let LA := (ModuleCat.extendScalars s.toC').obj L
  let f := s.extensionRestrictionFstIso.{uA, uA', uB, uD', v}.inv.app L
  let g := s.extensionRestrictionSndIso.{uA, uA', uB, uD', v}.inv.app L
  let a := s.restrictionFstIso.{uA, uA', uB, uD', v}.inv.app LB
  let b := s.restrictionSndIso.{uA, uA', uB, uD', v}.hom.app LA
  let i :=
    letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    letI : Algebra base.fibreProduct B := (toB (base := base)).toAlgebra
    letI : Algebra base.fibreProduct A' := (toA' (base := base)).toAlgebra
    letI : Algebra base.fibreProduct A := (toA (base := base)).toAlgebra
    ((extensionOfScalarsToTensorProductPullback.{_, _, _, _, _, v} (D' := D')
      ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
      ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A)).obj
        L).iso.hom
  let j := ((extensionOfScalarsToPullback.{max v uD'}
      (toB (base := base)) (toA' (base := base)) toBase surjection
      (RingHom.pullback_comm_sq toBase surjection)).obj ((ModuleCat.restrictScalars s.toD').obj
        L)).iso.hom
  have hf := s.extensionRestrictionFstIso_inv_tmul.{uA, uA', uB, uD', v} L 1 l
  have hg := s.extensionRestrictionSndIso_inv_tmul.{uA, uA', uB, uD', v} L 1 l
  have ha := s.restrictionFstIso_inv_tmul.{uA, uA', uB, uD', v}
    LB 1 ((s.toD 1) ⊗ₜ[D',s.toD] l)
  have hi := s.extensionOfScalarsToTensorProductPullback_iso_one_tmul.{uA, uA', uB, uD', v} L l
  have hj := extension_iso_one_tmul.{_, _, _, _, max v uD'}
    (toB (base := base)) (toA' (base := base)) toBase surjection
    (RingHom.pullback_comm_sq toBase surjection)
    ((ModuleCat.restrictScalars s.toD').obj L) l
  have hb := pushoutBaseChange_hom_one_tmul.{_, _, _, _, max v uA uA' uB uD'}
    s.A'toC' surjection s.C'toC s.AtoC s.C'toC_A'toC' (sndPushout s) LA
    ((s.toC' 1) ⊗ₜ[D',s.toC'] l)
  simp only [map_one] at hf hg ha hb
  change b (i (a ((1 : A) ⊗ₜ[B,toBase] (f ((1 : B) ⊗ₜ[base.fibreProduct,toB] l))))) =
    (ModuleCat.extendScalars surjection).map g
      (j ((1 : A) ⊗ₜ[B,toBase] ((1 : B) ⊗ₜ[base.fibreProduct,toB] l)))
  rw [hf, ha, hi, hj, ModuleCat.ExtendScalars.map_tmul, hg]
  exact hb

set_option maxHeartbeats 1000000 in
-- was section-wide; the statement elaborates tensor base change over `base.fibreProduct`
/-- The canonical natural isomorphism expressing commutativity of the functor square
in Tag 08KK. -/
public noncomputable def restrictionSquareIso :
    letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    letI : Algebra base.fibreProduct B := (toB (base := base)).toAlgebra
    letI : Algebra base.fibreProduct A' := (toA' (base := base)).toAlgebra
    letI : Algebra base.fibreProduct A := (toA (base := base)).toAlgebra
    extensionOfScalarsToTensorProductPullback.{_, _, _, _, _, v} (D' := D')
        ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
        ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A) ⋙
      s.restrictCompatibleModules.{uA, uA', uB, uD', v} ≅
      ModuleCat.restrictScalars s.toD' ⋙
        extensionOfScalarsToPullback.{max v uD'}
          (toB (base := base)) (toA' (base := base)) toBase surjection
          (RingHom.pullback_comm_sq toBase surjection) := by
  refine Iso.symm (NatIso.ofComponents (fun L => ?_) ?_)
  · refine CategoricalPullback.mkIso
      (s.extensionRestrictionFstIso.{uA, uA', uB, uD', v}.app L).symm
      (s.extensionRestrictionSndIso.{uA, uA', uB, uD', v}.app L).symm ?_
    exact s.restrictionSquare_coherence.{uA, uA', uB, uD', v} L
  · intro L M f
    apply CategoricalPullback.hom_ext
    · exact s.extensionRestrictionFstIso.{uA, uA', uB, uD', v}.inv.naturality f
    · exact s.extensionRestrictionSndIso.{uA, uA', uB, uD', v}.inv.naturality f

set_option maxHeartbeats 1000000 in
-- was section-wide; the statement elaborates tensor base change over `base.fibreProduct`
/-- Pure-tensor law for the first inverse component of the displayed functor square. -/
public theorem restrictionSquareIso_inv_fst_tmul
    (L : ModuleCat.{max v uA uA' uB uD'} D') (b : B) (l : L) :
    (s.restrictionSquareIso.{uA, uA', uB, uD', v}.inv.app L).fst (b ⊗ₜ[base.fibreProduct,toB] l) =
      s.BtoD b ⊗ₜ[D',s.toD] l :=
  s.extensionRestrictionFstIso_inv_tmul.{uA, uA', uB, uD', v} L b l

set_option maxHeartbeats 1000000 in
-- was section-wide; the statement elaborates tensor base change over `base.fibreProduct`
/-- Pure-tensor law for the second inverse component of the displayed functor square. -/
public theorem restrictionSquareIso_inv_snd_tmul
    (L : ModuleCat.{max v uA uA' uB uD'} D') (a : A') (l : L) :
    (s.restrictionSquareIso.{uA, uA', uB, uD', v}.inv.app L).snd (a ⊗ₜ[base.fibreProduct,toA'] l) =
      s.A'toC' a ⊗ₜ[D',s.toC'] l :=
  s.extensionRestrictionSndIso_inv_tmul.{uA, uA', uB, uD', v} L a l

end RelativeModuleFibreProductSituation

end

end MilnorPatching
