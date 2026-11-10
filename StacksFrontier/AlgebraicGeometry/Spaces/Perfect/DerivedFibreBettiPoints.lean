module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import
  StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreEtaleRefinement

/-!
# Betti numbers of a pseudo-coherent complex at the geometric points of an algebraic space

For a field-valued point of an algebraic space `X` the geometric stalk of the structure sheaf of
the space it presents is a field, so the derived fibre of a pseudo-coherent complex at a
geometric point has well-defined Betti numbers.

All names are in the namespace `AlgebraicGeometry.Space`, except
`CategoryTheory.GrothendieckTopology.Point.bijective_toPresheafFiber_of_isTerminal`.

## Main definitions

* `geometricFibreBetti`: the `i`-th Betti number of an object `E` of `D(𝒪_X)` at a geometric
  point `x`: the dimension of the `i`-th cohomology of the derived stalk, at the tautological
  geometric point, of the derived pullback of `E` to the space presented by `x`.

## Main results

* `geometricFibreBetti_derivedPullback`: Betti numbers commute with derived pullback.
* `finrank_idChart_eq_finrank_moduleStalk`: on the space of the spectrum of an algebraically
  closed field, a module has the same dimension over the global sections as its stalk at any
  geometric point.
* `CategoryTheory.GrothendieckTopology.Point.bijective_toPresheafFiber_of_isTerminal`: the germ
  map at a terminal neighbourhood which maps to every neighbourhood is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.GrothendieckTopology.Point

universe w v' u'

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  {FC : A → A → Type*} {CC : A → Type w}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} A FC]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]

/-- If a neighbourhood `(U, x)` of a point of a site has `U` terminal and maps to every other
neighbourhood, the germ map at it is bijective for every presheaf. -/
theorem bijective_toPresheafFiber_of_isTerminal {U : C} (hU : IsTerminal U)
    (x : Φ.fiber.obj U) (hx : ∀ (V : C) (y : Φ.fiber.obj V), ∃ g : U ⟶ V, Φ.fiber.map g x = y)
    (P : Cᵒᵖ ⥤ A) :
    Function.Bijective (Φ.toPresheafFiber U x P) := by
  constructor
  · intro s t hst
    obtain ⟨V, f, y, hy, hst'⟩ := (Φ.toPresheafFiber_eq_iff' U x s t).1 hst
    obtain ⟨g, hg⟩ := hx V y
    have hgf : g ≫ f = 𝟙 U := hU.hom_ext _ _
    have key : ∀ u, P.map g.op (P.map f.op u) = u := fun u => by
      rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, hgf, op_id, P.map_id,
        ConcreteCategory.id_apply]
    rw [← key s, hst', key t]
  · intro m
    obtain ⟨V, y, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) m
    obtain ⟨g, rfl⟩ := hx V y
    exact ⟨P.map g.op z, Φ.toPresheafFiber_w_apply g x P z⟩

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS}

/-- The morphism of algebraic spaces presented by a field-valued point. -/
abbrev fieldHom (p : FieldValuedPoint B S hS X.1) : fieldValuedPointSpace B S hS p ⟶ X :=
  ObjectProperty.homMk (fieldMorphism B S hS X.1 p)

/-- The point of the small étale site of the field space at the tautological geometric
point. -/
abbrev tautPoint (x : GeometricPoint B S hS X.1) :=
  etaleSitePoint B S hS (fieldValuedPointSpace B S hS x.val).1 (tautologicalGeometricPoint B S hS x)
    (fieldValuedPointSpace B S hS x.val).2

/-- Derived pullback along the morphism `fieldHom` presented by a field-valued point. -/
abbrev fieldPullback (x : FieldValuedPoint B S hS X.1) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (fieldValuedPointSpace B S hS x))) :=
  haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS (fieldHom B S hS x)
  smallEtaleDerivedModulePullback B S hS (fieldHom B S hS x)

/-- The `i`-th Betti number of `E` at a geometric point. -/
def geometricFibreBetti
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (i : ℤ)
    (x : GeometricPoint B S hS X.1) : ℕ :=
  Module.finrank
    (geometricStalkRing B S hS (X := fieldValuedPointSpace B S hS x.val)
      (tautologicalGeometricPoint B S hS x))
    ((DerivedCategory.homologyFunctor (ModuleCat.{u}
        (geometricStalkRing B S hS (X := fieldValuedPointSpace B S hS x.val)
          (tautologicalGeometricPoint B S hS x))) i).obj
      ((geometricDerivedStalk B S hS (X := fieldValuedPointSpace B S hS x.val)
        (tautologicalGeometricPoint B S hS x)).obj ((fieldPullback B S hS x.val).obj E)))

/-- The morphism presented by the image under `g` of a field-valued point `p` is the composite
of the morphism presented by `p` with `g`. -/
theorem fieldHom_map {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (p : FieldValuedPoint B S hS Y.1) :
    fieldHom B S hS (FieldValuedPoint.map B S hS Y.1 g.hom p) = fieldHom B S hS p ≫ g := by
  apply ObjectProperty.hom_ext
  change yonedaEquiv.symm (g.hom.app _ p.value) = yonedaEquiv.symm p.value ≫ g.hom
  rw [yonedaEquiv_symm_naturality_right]

/-- **Betti numbers commute with derived pullback**: the Betti numbers of `Lg^*E` at a geometric
point `y` of `Y` are those of `E` at the image of `y` in `X`. -/
theorem geometricFibreBetti_derivedPullback {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (i : ℤ)
    (y : GeometricPoint B S hS Y.1) :
    geometricFibreBetti B S hS
        ((smallEtaleDerivedModulePullback B S hS g).obj E) i y =
      geometricFibreBetti B S hS E i (geometricPointMap g.hom y) := by
  let e : (fieldPullback B S hS (geometricPointMap g.hom y).val).obj E ≅
      (fieldPullback B S hS y.val).obj ((smallEtaleDerivedModulePullback B S hS g).obj E) :=
    eqToIso (congrArg (fun k => (derivedPull B S hS (hasDerivedModulePullbacks B S hS) k).obj E)
      (fieldHom_map B S hS g y.val)) ≪≫
      ((smallEtaleDerivedPullbackData B S hS).compIso (fieldHom B S hS y.val) g).app E
  exact (((DerivedCategory.homologyFunctor _ i).mapIso
    ((geometricDerivedStalk B S hS (X := fieldValuedPointSpace B S hS y.val)
      (tautologicalGeometricPoint B S hS y)).mapIso e)).toLinearEquiv.finrank_eq).symm

/-- The lift of a geometric point `z` of the space of a field spectrum `T` to the identity
chart. -/
def idChartLift {T : BigFppfOver B S hS} (z : GeometricPoint B S hS (yoneda.obj T)) :
    GeometricFiber B S hS (yoneda.obj T) z (idChart B S hS T) :=
  ⟨z.val.value, rfl⟩

/-- On the space of the spectrum of an algebraically closed field, every lift of a geometric
point into an étale chart comes from the identity chart. -/
theorem exists_idChart_map_lift (p : FieldValuedPoint B S hS X.1) [IsAlgClosed p.carrier]
    (z : GeometricPoint B S hS (yoneda.obj p.siteObject))
    (V : SmallEtale B S hS (yoneda.obj p.siteObject))
    (y : GeometricFiber B S hS (yoneda.obj p.siteObject) z V) :
    ∃ g : idChart B S hS p.siteObject ⟶ V,
      (geometricFiber B S hS (yoneda.obj p.siteObject) z).map g (idChartLift B S hS z) = y := by
  obtain ⟨π, hπ⟩ := yoneda.map_surjective V.obj.hom
  have hπe : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map π) :=
    (presheaf_yoneda_map_etale_iff B S hS π).1 (hπ ▸ V.property)
  have hy : y.1 ≫ π = z.val.value := by
    have h2 : (yoneda.map π).app _ y.1 = z.val.value := by rw [hπ]; exact y.2
    exact h2
  obtain ⟨l, hl, hq⟩ := etale_field_map_factors p.carrier
    ((BigFppfOver.toScheme B S hS).map π) hπe z.val.carrier
    ((BigFppfOver.toScheme B S hS).map y.1)
  have hlS : l ≫ B.inclusion.map V.obj.left.hom = B.inclusion.map p.siteObject.hom := by
    have hw' : (BigFppfOver.toScheme B S hS).map π ≫ B.inclusion.map p.siteObject.hom =
        B.inclusion.map V.obj.left.hom := by
      rw [← Over.w π]; rfl
    rw [← hw', ← Category.assoc, hl, Category.id_comp]
  let s : p.siteObject ⟶ V.obj.left :=
    Over.homMk (ObjectProperty.homMk l) (by apply ObjectProperty.hom_ext; exact hlS)
  have hsπ : s ≫ π = 𝟙 _ :=
    BigFppfOver.map_toScheme_injective B S hS (by
      dsimp only
      rw [Functor.map_comp, CategoryTheory.Functor.map_id]
      exact hl)
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk s ?_), ?_⟩
  · change yoneda.map s ≫ V.obj.hom = 𝟙 _
    rw [← hπ, ← yoneda.map_comp, hsπ, yoneda.map_id]
  · apply Subtype.ext
    change z.val.value ≫ s = y.1
    apply BigFppfOver.map_toScheme_injective B S hS
    dsimp only
    rw [Functor.map_comp]
    change (BigFppfOver.toScheme B S hS).map z.val.value ≫ l = _
    have hz : (BigFppfOver.toScheme B S hS).map z.val.value =
        (BigFppfOver.toScheme B S hS).map y.1 ≫ (BigFppfOver.toScheme B S hS).map π := by
      rw [← Functor.map_comp, hy]
    rw [hz]
    exact hq.symm

set_option maxHeartbeats 800000 in
-- elaborating the nested site-point fibres of ringed-topos structure sheaves is heavy
open Opposite in
/-- **On the space of the spectrum of an algebraically closed field the stalk at any geometric
point is the module of global sections**, so the two have the same dimension. -/
theorem finrank_idChart_eq_finrank_moduleStalk (p : FieldValuedPoint B S hS X.1)
    [IsAlgClosed p.carrier] (z : GeometricPoint B S hS (fieldValuedPointSpace B S hS p).1)
    (M : SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (fieldValuedPointSpace B S hS p))) :
    Module.finrank
        ((ringedToposStructureRingSheaf B S hS (fieldValuedPointSpace B S hS p)).obj.obj
          (op (idChart B S hS p.siteObject)))
        (M.val.obj (op (idChart B S hS p.siteObject))) =
      Module.finrank
        (((etaleSitePoint B S hS (fieldValuedPointSpace B S hS p).1 z
            (fieldValuedPointSpace B S hS p).2).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS (fieldValuedPointSpace B S hS p)).O.obj)
        ((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS (fieldValuedPointSpace B S hS p).1 z
            (fieldValuedPointSpace B S hS p).2)
          (smallEtaleRingedTopos B S hS (fieldValuedPointSpace B S hS p)).O).obj M) := by
  let Φ := etaleSitePoint B S hS (fieldValuedPointSpace B S hS p).1 z
    (fieldValuedPointSpace B S hS p).2
  let R := ringedToposStructureRingSheaf B S hS (fieldValuedPointSpace B S hS p)
  let U := idChart B S hS p.siteObject
  have hlift : ∀ (V : SmallEtale B S hS (fieldValuedPointSpace B S hS p).1) (y : Φ.fiber.obj V),
      ∃ g : U ⟶ V, Φ.fiber.map g (idChartLift B S hS z) = y :=
    fun V y => exists_idChart_map_lift B S hS p z V y
  have hbij := fun (P : (SmallEtale B S hS (fieldValuedPointSpace B S hS p).1)ᵒᵖ ⥤
      AddCommGrpCat.{u}) =>
    Φ.bijective_toPresheafFiber_of_isTerminal (isTerminal_idChart B S hS p.siteObject)
      (idChartLift B S hS z) hlift P
  have hbijR := Φ.bijective_toPresheafFiber_of_isTerminal
    (isTerminal_idChart B S hS p.siteObject) (idChartLift B S hS z) hlift R.obj
  have h1 : Module.rank (R.obj.obj (op U)) (M.val.obj (op U)) =
      Module.rank ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj)
        ((Stacks.presheafModuleFiber Φ R.obj).obj M.val) :=
    rank_eq_of_equiv_equiv (Φ.toPresheafFiber U (idChartLift B S hS z) R.obj)
      (AddEquiv.ofBijective (Stacks.toPresheafModuleFiber Φ M.val U (idChartLift B S hS z))
        (hbij M.val.presheaf)) hbijR
      (fun r m => Stacks.toPresheafModuleFiber_smul Φ M.val U _ r m)
  let e : (Φ.presheafFiber (A := RingCat.{u})).obj R.obj ≅
      (forget₂ CommRingCat.{u} RingCat.{u}).obj ((Φ.presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS (fieldValuedPointSpace B S hS p)).O.obj) :=
    Stacks.commRingSheafFiberIso Φ (smallEtaleRingedTopos B S hS (fieldValuedPointSpace B S hS p)).O
  have h2 : Module.rank ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj)
        ((Stacks.presheafModuleFiber Φ R.obj).obj M.val) =
      Module.rank ((Φ.presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS (fieldValuedPointSpace B S hS p)).O.obj)
        ((Stacks.sheafModuleFiberOfCommRing Φ
          (smallEtaleRingedTopos B S hS (fieldValuedPointSpace B S hS p)).O).obj M) :=
    rank_eq_of_equiv_equiv e.hom.hom (AddEquiv.refl _)
      (ConcreteCategory.bijective_of_isIso e.hom)
      (fun r m => by
        have hr : e.inv.hom (e.hom.hom r) = r := by
          rw [← RingCat.comp_apply, Iso.hom_inv_id, RingCat.id_apply]
        change r • m = (e.inv.hom (e.hom.hom r)) • m
        rw [hr])
  exact congrArg Cardinal.toNat (h1.trans h2)

end AlgebraicGeometry.Space
