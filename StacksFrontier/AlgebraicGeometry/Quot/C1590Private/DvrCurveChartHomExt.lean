module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.RelativeHomGlue
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies

/-!
# Equality of curve-family morphisms on a common base chart

A covering base change detects equality of the total-space maps. The separate
base-map equality then gives equality in the category of curve families.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

theorem curveFamily_hom_ext_of_cover {A F F' : CurveFamily B hZ} (p : A ⟶ F)
    (hcov : Sieve.ofArrows (fun _ : Unit => A.base) (fun _ => p.baseMap) ∈
      BigFppfOver.topology B integerBase hZ F.base)
    {f g : F ⟶ F'} (hbase : f.baseMap = g.baseMap)
    (hlocal : p.totalMap ≫ f.totalMap = p.totalMap ≫ g.totalMap) : f = g := by
  apply CurveFamily.Hom.ext
  · exact hbase
  · apply ObjectProperty.hom_ext
    let z : F.total.obj ⟶ yoneda.obj F.base := F.toBase.hom
    refine hom_ext_of_local F'.total.property.isSheaf z
      (fun _ : Unit => A.base) (fun _ => p.baseMap) hcov ?_
    intro _
    have hpb := AlgebraicSpaces.isPullback_hom B integerBase hZ p.cartesian
    let a := yoneda.map p.baseMap
    let k := hpb.lift (pullback.snd a z) (pullback.fst a z) pullback.condition.symm
    have hk : k ≫ p.totalMap.hom = pullback.snd a z := hpb.lift_fst _ _ _
    have eq : p.totalMap.hom ≫ f.totalMap.hom = p.totalMap.hom ≫ g.totalMap.hom :=
      congrArg (fun m => m.hom) hlocal
    exact (by simpa only [← Category.assoc, hk] using congrArg (k ≫ ·) eq)

end AlgebraicGeometry.C1590Private

end
