module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric points of an algebraic space and the étale local ring

A *geometric point* of a presheaf `F` on the big fppf site of `S` — in the intended
application an algebraic space over `S` — is a field-valued point of `F` whose field is
algebraically closed; this is `AlgebraicGeometry.Space.GeometricPoint`.

A *small étale neighbourhood* of a geometric point is an étale chart of `F` together with a
lift of the point to it; these are the pairs `(U, ū)` with `U` an object of the small étale
site over which the *stalk* at the geometric point is the colimit of the sections of a
presheaf.  Taking that stalk of the structure sheaf gives the *étale local ring* at the
geometric point, whose spectrum is the strict henselization there. Since the neighbourhood
category has objects in `Type (u + 1)`, the étale local ring is a colimit in
`CommRingCat.{u + 1}` of the section rings raised by `ULift`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtaleNeighborhood` is an étale chart with a chosen lift of
  the geometric point, `AlgebraicGeometry.Space.SmallEtaleNeighborhood.Hom` a morphism of such
  and `AlgebraicGeometry.Space.SmallEtaleNeighborhood.sections` the diagram of sections of a
  presheaf over them.
* `AlgebraicGeometry.Space.stalk` is the stalk of a category-valued presheaf whenever that
  colimit exists, `AlgebraicGeometry.Space.stalkFunctor` its functorial form when the target
  has all colimits of the neighbourhood shape, and `AlgebraicGeometry.Space.stalkSet` /
  `AlgebraicGeometry.Space.stalkSetFunctor` the set-valued version with no smallness
  assumption.
* `AlgebraicGeometry.Space.GeometricFiber` and `AlgebraicGeometry.Space.geometricFiber` are
  the lifts of a geometric point into an étale chart, as a set and as a functor.
* `AlgebraicGeometry.Space.etaleLocalRing` is the ring of germs of regular functions at a
  geometric point, `AlgebraicGeometry.Space.etaleLocalRingGerm` the germ map of a section
  over a neighbourhood, and `AlgebraicGeometry.Space.strictHenselization` its spectrum.
* `AlgebraicGeometry.Space.geometricPointMap` is the image of a geometric point under a
  morphism of presheaves.

## Main results

* `AlgebraicGeometry.Space.neighborhoodFiberElementsEquiv`: the category of small étale
  neighbourhoods of a geometric point is equivalent to the category of elements of its
  geometric fibre functor, and `AlgebraicGeometry.Space.fiberColimitEquiv` identifies the
  colimits taken over the two shapes.

## References

* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/-! ### Étale neighbourhoods in the small étale site -/

section Stalks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A *small étale neighbourhood* of a geometric point `x` is an étale chart of `F` together
with a lift of `x` to it: a pair `(U, ū)` with `U ∈ Ob(F_étale)` a scheme chart, rather than an
arbitrary étale algebraic space over `F`. -/
@[sga "4 VIII 3.9" "more general", sga "4½ Arcata 2.3.1" "special case"]
structure SmallEtaleNeighborhood (x : GeometricPoint B S hS F) where
  /-- The étale chart of `F` underlying the neighbourhood. -/
  chart : SmallEtale B S hS F
  /-- The chosen lift of the geometric point to the chart. -/
  point : x.val.siteObject ⟶ chart.obj.left
  /-- The chosen lift composes to the section defining the geometric point. -/
  point_comp : chart.obj.hom.app (Opposite.op x.val.siteObject) point = x.val.value

namespace SmallEtaleNeighborhood

variable {x : GeometricPoint B S hS F}

/-- A morphism of small étale neighbourhoods is a morphism of charts carrying the chosen
lift to the chosen lift. -/
@[ext]
structure Hom (U V : SmallEtaleNeighborhood x) where
  /-- The underlying morphism of étale charts. -/
  hom : U.chart ⟶ V.chart
  /-- The morphism carries the chosen lift of the geometric point to the chosen lift. -/
  point_comp : U.point ≫ (SmallEtale.toOver B S hS F).map hom = V.point

/-- Small étale neighbourhoods of a geometric point form a category. -/
instance : Category (SmallEtaleNeighborhood x) where
  Hom := Hom
  id U := { hom := 𝟙 U.chart, point_comp := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      point_comp := by
        rw [Functor.map_comp, ← Category.assoc, f.point_comp, g.point_comp] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- The underlying morphism of charts of the identity is the identity. -/
@[simp]
theorem id_hom (U : SmallEtaleNeighborhood x) : Hom.hom (𝟙 U) = 𝟙 U.chart := rfl

/-- The underlying morphism of charts of a composite is the composite. -/
@[simp]
theorem comp_hom {U V W : SmallEtaleNeighborhood x} (f : U ⟶ V) (g : V ⟶ W) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

/-- Sections of a presheaf on the small étale site over the small étale neighbourhoods of a
geometric point, directed by restriction to refinements. -/
@[implicit_reducible]
def sections {C : Type w} [Category.{v} C] (P : (SmallEtale B S hS F)ᵒᵖ ⥤ C) :
    (SmallEtaleNeighborhood x)ᵒᵖ ⥤ C where
  obj U := P.obj (Opposite.op U.unop.chart)
  map f := P.map f.unop.hom.op
  map_id U := by simp
  map_comp f g := by simp

end SmallEtaleNeighborhood

/-- The field-valued point of the chart of a small étale neighbourhood of a geometric point:
the same field spectrum, with the chosen lift carried by the neighbourhood as its section. -/
def chartFieldValuedPoint {x : GeometricPoint B S hS F}
    (V : SmallEtaleNeighborhood x) :
    FieldValuedPoint B S hS (yoneda.obj V.chart.obj.left) where
  carrier := x.val.carrier
  contained := x.val.contained
  toBase := x.val.toBase
  value := V.point

/-- The chart point of a small étale neighbourhood lies above the image of the geometric
point. -/
theorem chartFieldValuedPoint_pointsMap {x : GeometricPoint B S hS F}
    (V : SmallEtaleNeighborhood x) :
    pointsMap B S hS (yoneda.obj V.chart.obj.left) V.chart.obj.hom
        ((chartFieldValuedPoint V).class B S hS (yoneda.obj V.chart.obj.left)) = x.image := by
  have h : FieldValuedPoint.map B S hS (yoneda.obj V.chart.obj.left) V.chart.obj.hom
      (chartFieldValuedPoint V) = x.val :=
    congrArg (fun v : F.obj (Opposite.op x.val.siteObject) ↦
      ({ carrier := x.val.carrier, field := x.val.field,
         contained := x.val.contained, toBase := x.val.toBase,
         value := v } : FieldValuedPoint B S hS F)) V.point_comp
  rw [pointsMap_class, h]

/-! ### Stalks at a geometric point -/

/-- The stalk of a presheaf on the small étale site at a geometric point,
formed as the colimit of its sections over the small étale neighbourhoods of that point. -/
@[stacks 04JY "category-valued stalk"]
noncomputable abbrev stalk {C : Type w} [Category.{v} C] (x : GeometricPoint B S hS F)
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ C)
    [HasColimit (SmallEtaleNeighborhood.sections (x := x) P)] : C :=
  colimit (SmallEtaleNeighborhood.sections (x := x) P)

/-- The stalk at a geometric point, as a functor of the presheaf. -/
@[implicit_reducible, stacks 04JY "stalk functor"]
noncomputable def stalkFunctor (C : Type w) [Category.{v} C] (x : GeometricPoint B S hS F)
    [HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ C] :
    ((SmallEtale B S hS F)ᵒᵖ ⥤ C) ⥤ C :=
  ((Functor.whiskeringLeft (SmallEtaleNeighborhood x)ᵒᵖ (SmallEtale B S hS F)ᵒᵖ C).obj
      { obj := fun U => Opposite.op U.unop.chart
        map := fun f => f.unop.hom.op
        map_id := by simp
        map_comp := by simp }) ⋙ colim

/-- The stalk functor sends a presheaf to its stalk. -/
@[simp]
theorem stalkFunctor_obj (C : Type w) [Category.{v} C] (x : GeometricPoint B S hS F)
    [HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ C] (P : (SmallEtale B S hS F)ᵒᵖ ⥤ C) :
    (stalkFunctor C x).obj P = stalk x P := rfl

/-- A morphism of presheaves acts on a stalk by applying it to local sections. -/
@[simp]
theorem stalkFunctor_ι_map (C : Type w) [Category.{v} C] (x : GeometricPoint B S hS F)
    [HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ C]
    {P Q : (SmallEtale B S hS F)ᵒᵖ ⥤ C} (α : P ⟶ Q)
    (U : (SmallEtaleNeighborhood x)ᵒᵖ) :
    colimit.ι (SmallEtaleNeighborhood.sections (x := x) P) U ≫ (stalkFunctor C x).map α =
      α.app (Opposite.op U.unop.chart) ≫
        colimit.ι (SmallEtaleNeighborhood.sections (x := x) Q) U := by
  simp [stalkFunctor, SmallEtaleNeighborhood.sections, Functor.comp]

/-- The set-valued stalk at a geometric point, formed as the quotient colimit
`CategoryTheory.Functor.ColimitType`, with no smallness assumption on the neighbourhood
category. -/
@[stacks 04JY "set-valued stalk"]
abbrev stalkSet (x : GeometricPoint B S hS F) (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type w) :
    Type _ :=
  (SmallEtaleNeighborhood.sections (x := x) P).ColimitType

/-- The map on set-valued stalks induced by a morphism of presheaves. -/
def stalkSetMap (x : GeometricPoint B S hS F)
    {P Q : (SmallEtale B S hS F)ᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    stalkSet x P → stalkSet x Q :=
  Quot.map
    (fun p => ⟨p.1, α.app (Opposite.op p.1.unop.chart) p.2⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      refine ⟨f, ?_⟩
      dsimp [SmallEtaleNeighborhood.sections] at h ⊢
      rw [h]
      simpa only [types_comp_apply] using
        congrArg (fun g => g a) (α.naturality f.unop.hom.op))

/-- The map on set-valued stalks sends a germ to the germ of its image. -/
@[simp]
theorem stalkSetMap_ι (x : GeometricPoint B S hS F)
    {P Q : (SmallEtale B S hS F)ᵒᵖ ⥤ Type w} (α : P ⟶ Q)
    (U : (SmallEtaleNeighborhood x)ᵒᵖ) (a : P.obj (Opposite.op U.unop.chart)) :
    stalkSetMap x α ((SmallEtaleNeighborhood.sections (x := x) P).ιColimitType U a) =
      (SmallEtaleNeighborhood.sections (x := x) Q).ιColimitType U
        (α.app (Opposite.op U.unop.chart) a) := rfl

/-- The set-valued stalk at a geometric point, as a functor of the presheaf. -/
@[implicit_reducible, stacks 04JY "set-valued stalk functor"]
def stalkSetFunctor (x : GeometricPoint B S hS F) :
    ((SmallEtale B S hS F)ᵒᵖ ⥤ Type w) ⥤ Type (max (u + 1) w) where
  obj P := stalkSet x P
  map α := TypeCat.ofHom (stalkSetMap x α)
  map_id P := by
    ext z
    induction z using Quot.inductionOn with
    | _ p => rfl
  map_comp α β := by
    ext z
    induction z using Quot.inductionOn with
    | _ p => rfl

/-- The set-valued stalk functor sends a presheaf to its set-valued stalk. -/
@[simp]
theorem stalkSetFunctor_obj (x : GeometricPoint B S hS F)
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type w) :
    (stalkSetFunctor x).obj P = stalkSet x P := rfl

/-- The set-valued stalk functor acts on morphisms by `stalkSetMap`. -/
@[simp]
theorem stalkSetFunctor_map_apply (x : GeometricPoint B S hS F)
    {P Q : (SmallEtale B S hS F)ᵒᵖ ⥤ Type w} (α : P ⟶ Q) (z : stalkSet x P) :
    (stalkSetFunctor x).map α z = stalkSetMap x α z := rfl

end Stalks

/-! ### The geometric fibre on the small étale site -/

section GeometricFiber

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The set of lifts of a geometric point into an étale chart of `F`. -/
abbrev GeometricFiber (x : GeometricPoint B S hS F) (U : SmallEtale B S hS F) : Type _ :=
  {p : x.val.siteObject ⟶ U.obj.left //
    U.obj.hom.app (Opposite.op x.val.siteObject) p = x.val.value}

/-- The functor of lifts of a geometric point into the étale charts of `F`: the fibre functor
of the point of the small étale site determined by the geometric point. -/
noncomputable def geometricFiber (x : GeometricPoint B S hS F) :
    SmallEtale B S hS F ⥤ Type u where
  obj U := GeometricFiber.{u} B S hS F x U
  map {U V} f := TypeCat.ofHom (fun p =>
    ⟨p.1 ≫ (SmallEtale.toOver B S hS F).map f,
    by
      calc
        V.obj.hom.app (Opposite.op x.val.siteObject)
            (p.1 ≫ (SmallEtale.toOver B S hS F).map f) =
            U.obj.hom.app (Opposite.op x.val.siteObject) p.1 := by
              change ((yoneda.map f.1.left ≫ V.obj.hom).app
                (Opposite.op x.val.siteObject)) p.1 =
                U.obj.hom.app (Opposite.op x.val.siteObject) p.1
              exact congrArg (fun α => α.app (Opposite.op x.val.siteObject) p.1)
                (CostructuredArrow.w f.1)
        _ = x.val.value := p.2⟩)
  map_id U := by
    ext p
    simp
  map_comp f g := by
    ext p
    simp

/-- A lift of a geometric point into an étale chart is the same data as a small étale
neighbourhood of that point. -/
noncomputable def neighborhoodToFiberElements (x : GeometricPoint B S hS F) :
    SmallEtaleNeighborhood x ⥤ (geometricFiber B S hS F x).Elements where
  obj U := (geometricFiber B S hS F x).elementsMk U.chart ⟨U.point, U.point_comp⟩
  map {U V} f := Functor.Elements.homMk f.hom (Subtype.ext f.point_comp)
  map_id U := by
    apply Functor.Elements.hom_ext
    rfl
  map_comp f g := by
    apply Functor.Elements.hom_ext
    rfl

/-- The inverse correspondence, from elements of the geometric fibre to small étale
neighbourhoods. -/
noncomputable def fiberElementsToNeighborhood (x : GeometricPoint B S hS F) :
    (geometricFiber B S hS F x).Elements ⥤ SmallEtaleNeighborhood x where
  obj U := ⟨U.obj, U.val.1, U.val.2⟩
  map {U V} f := ⟨f.hom, congrArg Subtype.val f.map_val⟩
  map_id U := by
    apply SmallEtaleNeighborhood.Hom.ext
    rfl
  map_comp f g := by
    apply SmallEtaleNeighborhood.Hom.ext
    rfl

/-- The category of elements of the geometric fibre is equivalent to the category of small
étale neighbourhoods used to form the stalk at the geometric point. -/
noncomputable def neighborhoodFiberElementsEquiv (x : GeometricPoint B S hS F) :
    SmallEtaleNeighborhood x ≌ (geometricFiber B S hS F x).Elements where
  functor := neighborhoodToFiberElements B S hS F x
  inverse := fiberElementsToNeighborhood B S hS F x
  unitIso := NatIso.ofComponents (fun U => Iso.refl U) (by
    intro U V f
    apply SmallEtaleNeighborhood.Hom.ext
    rfl)
  counitIso := NatIso.ofComponents (fun U => Iso.refl U) (by
    intro U V f
    apply Functor.Elements.hom_ext
    rfl)
  functor_unitIso_comp := by
    intro U
    apply Functor.Elements.hom_ext
    rfl

/-- The colimit over the category of elements of the geometric fibre is the set-valued stalk
over the small étale neighbourhoods. -/
noncomputable def fiberColimitEquiv (x : GeometricPoint B S hS F)
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type (u + 1)) :
    ((Functor.Elements.π (geometricFiber B S hS F x)).op ⋙ P).ColimitType ≃
      stalkSet x P where
  toFun := Quot.map
    (fun a => ⟨Opposite.op ((fiberElementsToNeighborhood B S hS F x).obj a.1.unop), a.2⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      exact ⟨((fiberElementsToNeighborhood B S hS F x).map f.unop).op, h⟩)
  invFun := Quot.map
    (fun a => ⟨Opposite.op ((neighborhoodToFiberElements B S hS F x).obj a.1.unop), a.2⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      exact ⟨((neighborhoodToFiberElements B S hS F x).map f.unop).op, h⟩)
  left_inv a := by induction a using Quot.inductionOn; rfl
  right_inv a := by induction a using Quot.inductionOn; rfl

end GeometricFiber

/-! ### Étale local rings -/

section EtaleLocalRing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The small étale neighbourhoods of a geometric point index colimits of commutative rings
in the universe `u + 1` in which the neighbourhood category itself lives. -/
noncomputable instance (x : GeometricPoint B S hS F) :
    HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ CommRingCat.{u + 1} :=
  hasColimitsOfShape_of_equivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := (SmallEtaleNeighborhood x)ᵒᵖ)).symm

/-- The structure presheaf of the small étale site with its section rings raised to the
universe in which the étale neighbourhoods of a geometric point live. -/
@[implicit_reducible]
def liftedStructurePresheaf : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (ULift.{u + 1} ((structurePresheaf B S hS F).obj U))
  map f := CommRingCat.ofHom (((structurePresheaf B S hS F).map f).hom.ulift)
  map_id U := by ext x; simp
  map_comp f g := by ext x; simp [RingHom.ulift_apply]

/-- The *étale local ring* of an algebraic space at a geometric point: the
stalk of the structure sheaf on the small étale site, i.e. the ring of germs at that point of
regular functions on étale neighbourhoods. -/
@[stacks 04KG "étale local ring"]
noncomputable abbrev etaleLocalRing (x : GeometricPoint B S hS F) : CommRingCat.{u + 1} :=
  stalk x (liftedStructurePresheaf B S hS F)

/-- The canonical ring homomorphism sending a regular function on a small étale
neighbourhood to its germ in the étale local ring. -/
noncomputable def etaleLocalRingGerm (x : GeometricPoint B S hS F)
    (U : (SmallEtaleNeighborhood x)ᵒᵖ) :
    ((structurePresheaf B S hS F).obj (Opposite.op U.unop.chart)) →+*
      etaleLocalRing B S hS F x :=
  (colimit.ι (SmallEtaleNeighborhood.sections (liftedStructurePresheaf B S hS F)) U).hom.comp
    ULift.ringEquiv.symm.toRingHom

/-- The *strict henselization* of an algebraic space at a geometric point is
the spectrum of its étale local ring. -/
@[stacks 04KG "strict henselization", sga "4½ Arcata 5.1.1"]
noncomputable abbrev strictHenselization (x : GeometricPoint B S hS F) : Scheme.{u + 1} :=
  Spec (etaleLocalRing B S hS F x)

end EtaleLocalRing

/-! ### Functoriality of geometric points -/

/-- The image of a geometric point under a morphism of presheaves. -/
noncomputable def geometricPointMap {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (z : GeometricPoint B S hS F) : GeometricPoint B S hS G :=
  ⟨FieldValuedPoint.map B S hS F f z.val, z.property⟩

/-- The point of `G` underlying `geometricPointMap f z` is the image under `pointsMap` of the
point of `F` underlying `z`. -/
@[simp]
theorem geometricPointMap_image {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (z : GeometricPoint B S hS F) :
    (geometricPointMap f z).image = pointsMap B S hS F f z.image := rfl

end AlgebraicGeometry.Space

end
