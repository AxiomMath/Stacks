module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFibreClassifier
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal

/-!
# The 2-fibre product of `Quot_{F/X/B} ⟶ Coh_{X/B}` with a scheme-valued point

Let `y : (Sch/V)_{fppf} ⟶ Coh_{X/B}` be a scheme-valued point.  An object of the 2-fibre product
`(Sch/V) ×_{Coh_{X/B}} Quot_{F/X/B}` over a scheme `T` is a morphism `x : T ⟶ V`, a quotient
`F_T ⟶ F_T/K` and an isomorphism `y(x) ≅ (T, F_T/K)` of `Coh_{X/B}`.  Such an object determines
the surjection `F_T ⟶ y(x)` composed of the projection onto `F_T/K` and the isomorphism; this is
the map that identifies the 2-fibre product with the functor of surjections in the proof of
Stacks 09TU.  This file defines it and proves that it is compatible with the morphisms of the
2-fibre product.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.fibreProduct`: the 2-fibre product.
* `AlgebraicGeometry.Space.QuotSituation.fibreClassMap`: the map `F_T ⟶ y(x)` attached to an
  object.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.fibreClassMap_map`: along a morphism of the 2-fibre
  product, the map attached to the source is the pullback of the map attached to the target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)
  {V : BigFppfOver B S hS}
  (y : (Stack.schemeFibredCategory B S hS V).val ⥤ᵇ D.toCoherentSituation.coherentCFG.val)

/-- **The 2-fibre product `(Sch/V) ×_{Coh_{X/B}} Quot_{F/X/B}`** of a scheme-valued point `y` of
`Coh_{X/B}` with the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}`. -/
abbrev fibreProduct : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  Stack.twoFibreProduct B S hS D.toCoherentSituation.coherentCFG
    (Stack.schemeFibredCategory B S hS V) D.quotCatFiberedInGroupoids y D.quotToCoherentCFG.hom

/-- The morphism of `Coh_{X/B}` a scheme-valued point attaches to a morphism of schemes over `V`,
written out. -/
def fibreMapHom {x' x : Over V} (a : x' ⟶ x) : CoherentHom (y.obj x') (y.obj x) :=
  y.map a

/-- The isomorphism of `Coh_{X/B}` carried by an object of the 2-fibre product, as a morphism of
`Coh_{X/B}` written out. -/
def fibreIsoHom (P : (D.fibreProduct y).val.obj) :
    CoherentHom (y.obj P.x) (D.cohObjectOfFamily P.y.fiber.as) :=
  P.iso.hom

/-- **The map `F_T ⟶ y(x)` attached to an object of the 2-fibre product**: the projection
`F_T ⟶ F_T/K` pulled back along the isomorphism `y(x) ≅ (T, F_T/K)`. -/
def fibreClassMap (P : (D.fibreProduct y).val.obj) :
    D.baseChangeModule (y.obj P.x).T ⟶ (y.obj P.x).F :=
  D.pullMapOf (D.fibreIsoHom y P).base (D.fibreIsoHom y P).fibre
    (D.quotientProjection _ P.y.fiber.as.subobject)

/-- **Along a morphism of the 2-fibre product, the map attached to the source is the pullback of
the map attached to the target**, along the morphism of `Coh_{X/B}` the point `y` attaches to
the first component. -/
theorem fibreClassMap_map {P' P : (D.fibreProduct y).val.obj} (m : P' ⟶ P) :
    D.fibreClassMap y P' =
      D.pullMapOf (D.fibreMapHom y m.a).base (D.fibreMapHom y m.a).fibre
        (D.fibreClassMap y P) := by
  have e := Discrete.eq_of_hom m.b.fiber
  let jb : CoherentHom (D.cohObjectOfFamily P'.y.fiber.as) (D.cohObjectOfFamily P.y.fiber.as) :=
    D.cohHomOfData (D.familyBaseMap m.b.base P.y.fiber.as e)
      (D.quotientPullback_familyBaseMap m.b.base P.y.fiber.as e)
      P.y.fiber.as.mem P'.y.fiber.as.mem
  let ya : CoherentHom (y.obj P'.x) (y.obj P.x) := D.fibreMapHom y m.a
  have hw : CoherentHom.comp ya (D.fibreIsoHom y P) =
      CoherentHom.comp (D.fibreIsoHom y P') jb := m.w
  have hπ : D.pullMapOf jb.base jb.fibre (D.quotientProjection _ P.y.fiber.as.subobject) =
      D.quotientProjection _ P'.y.fiber.as.subobject :=
    D.pullMapOf_quotientFibreIso_quotientProjection (D.familyBaseMap m.b.base P.y.fiber.as e)
      (D.quotientPullback_familyBaseMap m.b.base P.y.fiber.as e)
  calc D.fibreClassMap y P'
      = D.pullMapOf (D.fibreIsoHom y P').base (D.fibreIsoHom y P').fibre
          (D.pullMapOf jb.base jb.fibre (D.quotientProjection _ P.y.fiber.as.subobject)) :=
        congrArg (D.pullMapOf (D.fibreIsoHom y P').base (D.fibreIsoHom y P').fibre) hπ.symm
    _ = D.pullMapOf (CoherentHom.comp (D.fibreIsoHom y P') jb).base
          (CoherentHom.comp (D.fibreIsoHom y P') jb).fibre
          (D.quotientProjection _ P.y.fiber.as.subobject) :=
        (D.pullMapOf_comp _ _ _ _ _).symm
    _ = D.pullMapOf (CoherentHom.comp ya (D.fibreIsoHom y P)).base
          (CoherentHom.comp ya (D.fibreIsoHom y P)).fibre
          (D.quotientProjection _ P.y.fiber.as.subobject) :=
        congrArg (fun e : CoherentHom (y.obj P'.x) (D.cohObjectOfFamily P.y.fiber.as) =>
          D.pullMapOf e.base e.fibre (D.quotientProjection _ P.y.fiber.as.subobject)) hw.symm
    _ = D.pullMapOf ya.base ya.fibre (D.fibreClassMap y P) :=
        D.pullMapOf_comp _ _ _ _ _

end AlgebraicGeometry.Space.QuotSituation

end
