module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleStalkPointDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChart

/-!
# Weak association at a geometric point depends only on the point underneath it

Let `X` be an algebraic space over a scheme `S`, let `F` be an `𝒪_X`-module and let `x̄` be a
geometric point of `X` lying over a point `x` of `|X|`. Weak association of the maximal ideal
of the étale local ring `𝒪_{X, x̄}` to the geometric stalk `F_{x̄}` does not depend on `x̄`: it
holds at one geometric point above `x` exactly when it holds at every one. So the weakly
associated points of Stacks 0CTX, defined by the condition at *some* geometric point above a
point, are detected by *any* geometric point above it.

The comparison is an isomorphism, built on the stalk colimits themselves, so no descent of
weakly associated primes along a flat base change is involved. If `ȳ` dominates `x̄` then the
lifts of `x̄` into an étale chart and the lifts of `ȳ` into the same chart are in canonical
bijection, surjectively by `AlgebraicGeometry.Space.exists_neighborhood_map_of_dominates` and
injectively by `AlgebraicGeometry.Space.chartLift_unique_of_comp_eq`. The two geometric points
therefore determine points of the small étale site with isomorphic fibre functors, and the
fibre of a presheaf and the stalk of a sheaf of modules transport along such an isomorphism
germ by germ. Two geometric points above one point of `|X|` are dominated by a common third
(`AlgebraicGeometry.Space.GeometricPoint.exists_common_extension`), which reduces the general
case to a domination.

## Main definitions

* `Stacks.presheafFiberMapAlong` and `Stacks.presheafFiberIsoAlong` transport the fibre of a
  presheaf between two points of a site along a morphism, respectively an isomorphism, of their
  fibre functors.
* `Stacks.moduleStalkLargeMapAlong` and `Stacks.moduleStalkLargeAddEquivAlong` do the same for
  the stalk of a sheaf of modules.
* `AlgebraicGeometry.Space.geometricFiberIsoAlong` is the isomorphism of geometric fibre
  functors along a domination of geometric points.

## Main results

* `Stacks.isWeaklyAssociatedPrime_moduleStalkLarge_congr_of_fiberIso`: weak association of the
  maximal ideal to the stalk of a sheaf of modules transports between two points of a site with
  isomorphic fibre functors.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPrime_geometricModuleStalk_iff_of_image_eq`: the
  analogue for weak association of Stacks 04K4. Two geometric points above the same point of
  `|X|` give the same condition.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPrime`: a point is
  weakly associated to a module exactly when the maximal ideal of the étale local ring is a
  weakly associated prime of the geometric stalk at a *given* geometric point above it.

## Implementation notes

The transport of the module stalk is built with the germ calculus of
`Stacks.moduleStalkLargeDescOfCompatibleFamily` rather than by reindexing the colimit, so that
the semilinearity of the comparison over the comparison of the structure rings is available
directly from `Stacks.moduleStalkLargeDescOfCompatibleFamily_smul`.

The condition is stated in the two spellings that occur in the development — over the fibre of
the structure sheaf at the point of the site, and over the étale local ring after the extension
of scalars of `AlgebraicGeometry.Space.pointStalkRingEquiv` — and the independence is proved in
the first, where the comparison lives, then carried to the second.

## References

* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m v w t u' v'

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace Stacks

/-! ### The fibre of a presheaf along a morphism of fibre functors -/

section PresheafFiber

variable {C : Type t} [Category.{v} C] {J : GrothendieckTopology C} (p q : J.Point.{w})
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- The comparison of the fibres of a presheaf at two points of a site along a morphism of
their fibre functors: the germ of a section at a neighbourhood of the first point is the germ
of the same section at the transported neighbourhood of the second. -/
noncomputable def presheafFiberMapAlong (e : p.fiber ⟶ q.fiber) (P : Cᵒᵖ ⥤ A) :
    (p.presheafFiber (A := A)).obj P ⟶ (q.presheafFiber (A := A)).obj P :=
  p.presheafFiberDesc (fun U x => q.toPresheafFiber U (e.app U x) P) (fun U V f x =>
    (q.toPresheafFiber_w f (e.app U x) P).trans
      (congrArg (fun y => q.toPresheafFiber V y P) (e.naturality_apply f x).symm))

/-- The comparison of fibres sends the germ of a section to the germ of that section at the
transported neighbourhood. -/
@[reassoc]
theorem toPresheafFiber_presheafFiberMapAlong (e : p.fiber ⟶ q.fiber) (P : Cᵒᵖ ⥤ A) (U : C)
    (x : p.fiber.obj U) :
    p.toPresheafFiber U x P ≫ presheafFiberMapAlong p q e P =
      q.toPresheafFiber U (e.app U x) P :=
  p.toPresheafFiber_presheafFiberDesc _ _ U x

/-- Two points of a site whose fibre functors are isomorphic have isomorphic fibres on every
presheaf. -/
noncomputable def presheafFiberIsoAlong (e : p.fiber ≅ q.fiber) (P : Cᵒᵖ ⥤ A) :
    (p.presheafFiber (A := A)).obj P ≅ (q.presheafFiber (A := A)).obj P where
  hom := presheafFiberMapAlong p q e.hom P
  inv := presheafFiberMapAlong q p e.inv P
  hom_inv_id := by
    refine p.presheafFiber_hom_ext fun U x => ?_
    rw [Category.comp_id, ← Category.assoc, toPresheafFiber_presheafFiberMapAlong,
      toPresheafFiber_presheafFiberMapAlong]
    have hx : e.inv.app U (e.hom.app U x) = x := by simp
    exact congrArg (fun y => p.toPresheafFiber U y P) hx
  inv_hom_id := by
    refine q.presheafFiber_hom_ext fun U x => ?_
    rw [Category.comp_id, ← Category.assoc, toPresheafFiber_presheafFiberMapAlong,
      toPresheafFiber_presheafFiberMapAlong]
    have hx : e.hom.app U (e.inv.app U x) = x := by simp
    exact congrArg (fun y => q.toPresheafFiber U y P) hx

end PresheafFiber

/-! ### The stalk of a sheaf of modules along a morphism of fibre functors -/

section ModuleStalk

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (p q : J.Point.{w})
  (O : Sheaf J CommRingCat.{w}) (F : SheafOfModules.{m} (commRingSheafToRingSheaf O))

/-- The comparison of the stalks of the structure sheaf at two points of a site whose fibre
functors are isomorphic, as a ring isomorphism. -/
noncomputable def presheafFiberRingEquivAlong (e : p.fiber ≅ q.fiber) :
    ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) ≃+*
      ((q.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
  (presheafFiberIsoAlong p q e O.obj).commRingCatIsoToRingEquiv

omit [LocallySmall.{w} C] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The ring comparison sends the germ of a regular function to the germ of that function at
the transported neighbourhood. -/
theorem presheafFiberRingEquivAlong_toPresheafFiber (e : p.fiber ≅ q.fiber) (U : C)
    (x : p.fiber.obj U) (a : O.obj.obj (op U)) :
    presheafFiberRingEquivAlong p q O e (p.toPresheafFiber U x O.obj a) =
      q.toPresheafFiber U (e.hom.app U x) O.obj a :=
  ConcreteCategory.congr_hom
    (toPresheafFiber_presheafFiberMapAlong p q e.hom O.obj U x) a

/-- The comparison of the stalks of a sheaf of modules at two points of a site along a
morphism of their fibre functors: the germ of a section at a neighbourhood of the first point
is the germ of the same section at the transported neighbourhood of the second. -/
noncomputable def moduleStalkLargeMapAlong (e : p.fiber ⟶ q.fiber) :
    moduleStalkLarge.{m} p O F →+ moduleStalkLarge.{m} q O F :=
  moduleStalkLargeDescOfCompatibleFamily p O F
    (fun U x => moduleStalkLargeGerm q O F U (e.app U x))
    (fun _ V f x s => (moduleStalkLargeGerm_w q O F f (e.app _ x) s).trans
      (congrArg (fun y => moduleStalkLargeGerm q O F V y s) (e.naturality_apply f x).symm))

/-- The comparison of module stalks sends a germ to the germ of the same section. -/
theorem moduleStalkLargeMapAlong_germ (e : p.fiber ⟶ q.fiber) (U : C) (x : p.fiber.obj U)
    (s : F.val.obj (op U)) :
    moduleStalkLargeMapAlong p q O F e (moduleStalkLargeGerm p O F U x s) =
      moduleStalkLargeGerm q O F U (e.app U x) s :=
  moduleStalkLargeDescOfCompatibleFamily_germ p O F _ _ U x s

/-- The comparison of the stalks of a sheaf of modules at two points of a site whose fibre
functors are isomorphic, as an isomorphism of additive groups. -/
noncomputable def moduleStalkLargeAddEquivAlong (e : p.fiber ≅ q.fiber) :
    moduleStalkLarge.{m} p O F ≃+ moduleStalkLarge.{m} q O F where
  toFun := moduleStalkLargeMapAlong p q O F e.hom
  invFun := moduleStalkLargeMapAlong q p O F e.inv
  map_add' := map_add _
  left_inv z := by
    have h : (moduleStalkLargeMapAlong q p O F e.inv).comp
        (moduleStalkLargeMapAlong p q O F e.hom) = AddMonoidHom.id _ := by
      refine moduleStalkLarge_addHom_ext p O F _ _ fun U x s => ?_
      have hx : e.inv.app U (e.hom.app U x) = x := by simp
      change moduleStalkLargeMapAlong q p O F e.inv
        (moduleStalkLargeMapAlong p q O F e.hom (moduleStalkLargeGerm p O F U x s)) = _
      rw [moduleStalkLargeMapAlong_germ, moduleStalkLargeMapAlong_germ]
      exact congrArg (fun y => moduleStalkLargeGerm p O F U y s) hx
    exact DFunLike.congr_fun h z
  right_inv z := by
    have h : (moduleStalkLargeMapAlong p q O F e.hom).comp
        (moduleStalkLargeMapAlong q p O F e.inv) = AddMonoidHom.id _ := by
      refine moduleStalkLarge_addHom_ext q O F _ _ fun U x s => ?_
      have hx : e.hom.app U (e.inv.app U x) = x := by simp
      change moduleStalkLargeMapAlong p q O F e.hom
        (moduleStalkLargeMapAlong q p O F e.inv (moduleStalkLargeGerm q O F U x s)) = _
      rw [moduleStalkLargeMapAlong_germ, moduleStalkLargeMapAlong_germ]
      exact congrArg (fun y => moduleStalkLargeGerm q O F U y s) hx
    exact DFunLike.congr_fun h z

/-- The comparison of module stalks is semilinear along the comparison of the stalks of the
structure sheaf. -/
theorem moduleStalkLargeAddEquivAlong_smul (e : p.fiber ≅ q.fiber)
    (r : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (z : moduleStalkLarge.{m} p O F) :
    moduleStalkLargeAddEquivAlong p q O F e (r • z) =
      presheafFiberRingEquivAlong p q O e r • moduleStalkLargeAddEquivAlong p q O F e z :=
  moduleStalkLargeDescOfCompatibleFamily_smul p O F _ _
    (presheafFiberRingEquivAlong p q O e).toRingHom
    (fun U x a s => by
      have h : (presheafFiberRingEquivAlong p q O e).toRingHom
            (p.toPresheafFiber U x O.obj a) =
          q.toPresheafFiber U (e.hom.app U x) O.obj a :=
        presheafFiberRingEquivAlong_toPresheafFiber p q O e U x a
      rw [moduleStalkLargeGerm_smul, h]) r z

/-- **Weak association of the maximal ideal to the stalk of a sheaf of modules transports
between two points of a site whose fibre functors are isomorphic.** -/
theorem isWeaklyAssociatedPrime_moduleStalkLarge_congr_of_fiberIso (e : p.fiber ≅ q.fiber)
    [IsLocalRing ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj)]
    [IsLocalRing ((q.presheafFiber (A := CommRingCat.{w})).obj O.obj)] :
    IsWeaklyAssociatedPrime ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj)
        (moduleStalkLarge.{m} p O F)
        (IsLocalRing.maximalIdeal ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj)) ↔
      IsWeaklyAssociatedPrime ((q.presheafFiber (A := CommRingCat.{w})).obj O.obj)
        (moduleStalkLarge.{m} q O F)
        (IsLocalRing.maximalIdeal ((q.presheafFiber (A := CommRingCat.{w})).obj O.obj)) :=
  isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv
    (presheafFiberRingEquivAlong p q O e) (moduleStalkLargeAddEquivAlong p q O F e)
    (moduleStalkLargeAddEquivAlong_smul p q O F e)

end ModuleStalk

end Stacks

namespace AlgebraicGeometry.Space

/-! ### The geometric fibre along a domination of geometric points -/

section GeometricFiber

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x y : GeometricPoint B S hS F}
  (f : y.val.siteObject ⟶ x.val.siteObject) (hf : F.map f.op x.val.value = y.val.value)

/-- The lift of a geometric point into an étale chart carried by a lift of a geometric point
dominating it. -/
noncomputable def chartLiftAlong (U : SmallEtale B S hS F)
    (η : GeometricFiber B S hS F y U) : GeometricFiber B S hS F x U :=
  ⟨(exists_neighborhood_map_of_dominates f hf ⟨U, η.1, η.2⟩).choose,
    (exists_neighborhood_map_of_dominates f hf ⟨U, η.1, η.2⟩).choose_spec.1⟩

/-- The lift of the dominated point restricts along the domination to the given lift. -/
theorem comp_chartLiftAlong (U : SmallEtale B S hS F) (η : GeometricFiber B S hS F y U) :
    f ≫ (chartLiftAlong f hf U η).1 = η.1 :=
  (exists_neighborhood_map_of_dominates f hf ⟨U, η.1, η.2⟩).choose_spec.2

include hf in
/-- Composing a lift of a geometric point with the morphism of field spectra witnessing a
domination gives a lift of the dominating point. -/
theorem comp_mem_geometricFiber (U : SmallEtale B S hS F)
    (pt : GeometricFiber B S hS F x U) :
    U.obj.hom.app (op y.val.siteObject) (f ≫ pt.1) = y.val.value := by
  have hn' := congrArg (fun k => k pt.1) (U.obj.hom.naturality f.op)
  have hh : U.obj.hom.app (op y.val.siteObject) (f ≫ pt.1) =
      F.map f.op (U.obj.hom.app (op x.val.siteObject) pt.1) := by
    simpa only [types_comp_apply, yoneda_obj_map, Quiver.Hom.unop_op,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, Function.comp_apply] using hn'
  rw [pt.2, hf] at hh
  exact hh

/-- **The lifts of a geometric point into the étale charts are the lifts of a geometric point
dominating it.** Composing with the morphism of field spectra witnessing the domination is a
bijection: it is surjective by
`AlgebraicGeometry.Space.exists_neighborhood_map_of_dominates` and injective by
`AlgebraicGeometry.Space.chartLift_unique_of_comp_eq`. -/
noncomputable def geometricFiberIsoAlong :
    geometricFiber B S hS F x ≅ geometricFiber B S hS F y :=
  NatIso.ofComponents
    (fun U => Equiv.toIso
      { toFun := fun pt => ⟨f ≫ pt.1, comp_mem_geometricFiber f hf U pt⟩
        invFun := chartLiftAlong f hf U
        left_inv := fun pt => Subtype.ext
          (chartLift_unique_of_comp_eq f ⟨U, f ≫ pt.1, comp_mem_geometricFiber f hf U pt⟩
            _ pt.1 (chartLiftAlong f hf U _).2 pt.2
            (comp_chartLiftAlong f hf U ⟨f ≫ pt.1, comp_mem_geometricFiber f hf U pt⟩))
        right_inv := fun η => Subtype.ext (comp_chartLiftAlong f hf U η) })
    (by
      intro U V g
      ext pt
      exact Subtype.ext (Category.assoc f pt.1 _).symm)

end GeometricFiber

/-! ### Independence of the geometric point -/

section Independence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (G : Modules.{u, m} B S hS X.1 X.2)

/-- Weak association of the maximal ideal of the étale local ring to the geometric stalk is
weak association of the maximal ideal of the stalk of the structure sheaf at the point of the
small étale site to the stalk of the module there: the two differ by the extension of scalars
along a ring isomorphism. -/
theorem isWeaklyAssociatedPrime_moduleStalkLarge_iff_geometricModuleStalk
    (xbar : GeometricPoint B S hS X.1) :
    letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
    letI : IsLocalRing
        (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS X).O.obj) :=
      (pointStalkRingEquiv B S hS X xbar).symm.isLocalRing
    letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar G) :=
      (geometricModuleStalk B S hS X xbar G).isModule
    (IsWeaklyAssociatedPrime
        (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS X).O.obj)
        (Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 xbar X.2)
          (smallEtaleRingedTopos B S hS X).O G)
        (IsLocalRing.maximalIdeal _) ↔
      IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
        (geometricModuleStalk B S hS X xbar G)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar))) := by
  let : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  let : IsLocalRing
      (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj) :=
    (pointStalkRingEquiv B S hS X xbar).symm.isLocalRing
  exact isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv
    (pointStalkRingEquiv B S hS X xbar)
    (ModuleCat.extendScalarsRingEquivAddEquiv (pointStalkRingEquiv B S hS X xbar) _)
    (ModuleCat.extendScalarsRingEquivAddEquiv_smul _ _)

/-- **Stacks 04K4 for weak association, along a domination.** If `ȳ` dominates `x̄` then the
maximal ideal of `𝒪_{X, x̄}` is weakly associated to `F_{x̄}` exactly when the maximal ideal of
`𝒪_{X, ȳ}` is weakly associated to `F_{ȳ}`. -/
theorem isWeaklyAssociatedPrime_geometricModuleStalk_iff_of_dominates
    {x y : GeometricPoint B S hS X.1} (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : X.1.map f.op x.val.value = y.val.value) :
    letI : IsLocalRing (etaleLocalRing B S hS X.1 x) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 x
    letI : IsLocalRing (etaleLocalRing B S hS X.1 y) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 y
    letI : Module (etaleLocalRing B S hS X.1 x) (geometricModuleStalk B S hS X x G) :=
      (geometricModuleStalk B S hS X x G).isModule
    letI : Module (etaleLocalRing B S hS X.1 y) (geometricModuleStalk B S hS X y G) :=
      (geometricModuleStalk B S hS X y G).isModule
    (IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 x) (geometricModuleStalk B S hS X x G)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 x)) ↔
      IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 y) (geometricModuleStalk B S hS X y G)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 y))) := by
  let : IsLocalRing (etaleLocalRing B S hS X.1 x) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  let : IsLocalRing (etaleLocalRing B S hS X.1 y) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 y
  let : IsLocalRing
      (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj) :=
    (pointStalkRingEquiv B S hS X x).symm.isLocalRing
  let : IsLocalRing
      (((etaleSitePoint B S hS X.1 y X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj) :=
    (pointStalkRingEquiv B S hS X y).symm.isLocalRing
  refine Iff.trans
    (isWeaklyAssociatedPrime_moduleStalkLarge_iff_geometricModuleStalk B S hS X G x).symm
    (Iff.trans ?_ (isWeaklyAssociatedPrime_moduleStalkLarge_iff_geometricModuleStalk
      B S hS X G y))
  exact Stacks.isWeaklyAssociatedPrime_moduleStalkLarge_congr_of_fiberIso
    (etaleSitePoint B S hS X.1 x X.2) (etaleSitePoint B S hS X.1 y X.2)
    (smallEtaleRingedTopos B S hS X).O G (geometricFiberIsoAlong f hf)

/-- **The analogue for weak association of Stacks 04K4.** Two geometric points lying over the
same point of `|X|` give the same condition: the maximal ideal of the étale local ring at one
is weakly associated to the geometric stalk there exactly when the same holds at the other. -/
theorem isWeaklyAssociatedPrime_geometricModuleStalk_iff_of_image_eq
    (x y : GeometricPoint B S hS X.1) (h : x.image = y.image) :
    letI : IsLocalRing (etaleLocalRing B S hS X.1 x) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 x
    letI : IsLocalRing (etaleLocalRing B S hS X.1 y) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 y
    letI : Module (etaleLocalRing B S hS X.1 x) (geometricModuleStalk B S hS X x G) :=
      (geometricModuleStalk B S hS X x G).isModule
    letI : Module (etaleLocalRing B S hS X.1 y) (geometricModuleStalk B S hS X y G) :=
      (geometricModuleStalk B S hS X y G).isModule
    (IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 x) (geometricModuleStalk B S hS X x G)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 x)) ↔
      IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 y) (geometricModuleStalk B S hS X y G)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 y))) := by
  obtain ⟨r, ⟨fx, hfx⟩, ⟨fy, hfy⟩⟩ :=
    GeometricPoint.exists_common_extension x y (rfl : x.LiesOver x.image) h.symm
  exact (isWeaklyAssociatedPrime_geometricModuleStalk_iff_of_dominates B S hS X G fx hfx).trans
    (isWeaklyAssociatedPrime_geometricModuleStalk_iff_of_dominates B S hS X G fy hfy).symm

/-- **Weak association read at a prescribed geometric point.** A point of an algebraic space
is weakly associated to an `𝒪_X`-module exactly when, at a *given* geometric point above it,
the maximal ideal of the étale local ring is a weakly associated prime of the geometric stalk.

The definition of Stacks 0CTX asks for the condition at some geometric point above the point;
by the analogue for weak association of Stacks 04K4 the choice does not matter. -/
theorem isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPrime (pt : points B S hS X.1)
    (xbar : GeometricPoint B S hS X.1) (hxbar : xbar.LiesOver pt) :
    letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
    letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar G) :=
      (geometricModuleStalk B S hS X xbar G).isModule
    (IsWeaklyAssociatedPoint B S hS X G pt ↔
      IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
        (geometricModuleStalk B S hS X xbar G)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar))) := by
  constructor
  · rintro ⟨ybar, hybar, hwa⟩
    exact (isWeaklyAssociatedPrime_geometricModuleStalk_iff_of_image_eq B S hS X G ybar xbar
      (hybar.trans hxbar.symm)).mp hwa
  · intro hwa
    exact ⟨xbar, hxbar, hwa⟩

end Independence

end AlgebraicGeometry.Space

end
