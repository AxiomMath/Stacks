module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.QuasiFiniteFunctoriality

/-!
# Cartesian triples over a pushout along a closed immersion and an integral morphism

Let `Y ← Z → X` be the span of a pushout situation of [Stacks Project, Tag 0ECI].  A *cartesian
triple* over it is a span `Y' ← Z' → X'` over that span whose two squares are cartesian and
whose three vertical morphisms are separated and locally quasi-finite, as in
[Stacks Project, Tag 0ECK].  This file makes the cartesian triples into a category, by declaring
the compatible componentwise morphisms, and shows that the pushout construction of
[Stacks Project, Tag 0ECK] is a fully faithful functor from it to the schemes over `Y ⨿_Z X`.

The flat and the étale cartesian triples, and the flat respectively étale, separated, locally
quasi-finite schemes over `Y ⨿_Z X`, are the two pairs of categories compared by
[Stacks Project, Tag 0ECL].

## Main definitions

* `AlgebraicGeometry.CartesianTripleHom` is a morphism of cartesian triples.
* `AlgebraicGeometry.FlatCartesianTriple` and `AlgebraicGeometry.EtaleCartesianTriple` are the
  categories of cartesian triples with flat, respectively étale, vertical morphisms.
* `AlgebraicGeometry.flatSchemesOverProperty` and `AlgebraicGeometry.etaleSchemesOverProperty`,
  and the categories `AlgebraicGeometry.flatSchemesOver` and
  `AlgebraicGeometry.etaleSchemesOver` of flat, respectively étale, separated and locally
  quasi-finite schemes over the pushout.
* `AlgebraicGeometry.triplePushoutMap` is the morphism of pushouts induced by a morphism of
  cartesian triples, and `AlgebraicGeometry.flatTripleToOver`,
  `AlgebraicGeometry.etaleTripleToOver` are the resulting functors to schemes over the pushout.

## Main results

* `AlgebraicGeometry.triplePushoutMap_injective` and
  `AlgebraicGeometry.exists_cartesianTripleHom_of_comp_pushoutMap`: the pushout construction is
  fully faithful on morphisms of cartesian triples.

## Implementation notes

A morphism of triples is three compatible morphisms of schemes, not merely a morphism between
the two pushouts; the two results above say that the two notions agree.

Stacks terminology includes local finite type in "locally quasi-finite".  Mathlib separates this
into `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`, so the
two categories of schemes over the pushout record both conditions, as do the vertical morphisms
of a cartesian triple.

## References

* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ECK](https://stacks.math.columbia.edu/tag/0ECK)
* [Stacks Project, Tag 0ECL](https://stacks.math.columbia.edu/tag/0ECL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}

/-- A morphism of cartesian diagrams over a fixed pushout situation: three morphisms between
the three schemes of the two diagrams, compatible with the two horizontal morphisms and with the
three vertical morphisms to the base situation. -/
structure CartesianTripleHom (d e : CartesianDiagram s) where
  /-- The component over `X`. -/
  x : d.X' ⟶ e.X'
  /-- The component over `Y`. -/
  y : d.Y' ⟶ e.Y'
  /-- The component over `Z`. -/
  z : d.Z' ⟶ e.Z'
  /-- The components commute with the two closed immersions. -/
  left : d.i' ≫ x = z ≫ e.i'
  /-- The components commute with the two integral morphisms. -/
  right : d.j' ≫ y = z ≫ e.j'
  /-- The component over `X` is a morphism over `X`. -/
  overX : x ≫ e.f = d.f
  /-- The component over `Y` is a morphism over `Y`. -/
  overY : y ≫ e.g = d.g
  /-- The component over `Z` is a morphism over `Z`. -/
  overZ : z ≫ e.h = d.h

namespace CartesianTripleHom

/-- Two morphisms of cartesian diagrams agreeing in all three components are equal. -/
@[ext] theorem ext {d e : CartesianDiagram s} {a b : CartesianTripleHom d e}
    (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a
  cases b
  simp_all

/-- The identity morphism of a cartesian diagram. -/
def id (d : CartesianDiagram s) : CartesianTripleHom d d where
  x := 𝟙 _
  y := 𝟙 _
  z := 𝟙 _
  left := by simp
  right := by simp
  overX := by simp
  overY := by simp
  overZ := by simp

/-- The componentwise composition of two morphisms of cartesian diagrams. -/
def comp {d e k : CartesianDiagram s} (a : CartesianTripleHom d e)
    (b : CartesianTripleHom e k) : CartesianTripleHom d k where
  x := a.x ≫ b.x
  y := a.y ≫ b.y
  z := a.z ≫ b.z
  left := by rw [reassoc_of% a.left, b.left, Category.assoc]
  right := by rw [reassoc_of% a.right, b.right, Category.assoc]
  overX := by rw [Category.assoc, b.overX, a.overX]
  overY := by rw [Category.assoc, b.overY, a.overY]
  overZ := by rw [Category.assoc, b.overZ, a.overZ]

end CartesianTripleHom

/-- The cartesian diagrams over a pushout situation whose three vertical morphisms are flat. -/
abbrev FlatCartesianTriple (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :=
  {d : CartesianDiagram s // Flat d.f ∧ Flat d.g ∧ Flat d.h}

/-- The cartesian diagrams over a pushout situation whose three vertical morphisms are étale. -/
abbrev EtaleCartesianTriple (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :=
  {d : CartesianDiagram s // Etale d.f ∧ Etale d.g ∧ Etale d.h}

/-- The category of flat cartesian triples, whose morphisms are the morphisms
`AlgebraicGeometry.CartesianTripleHom` of the underlying cartesian diagrams. -/
instance (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    Category (FlatCartesianTriple s) where
  Hom d e := CartesianTripleHom d.1 e.1
  id d := CartesianTripleHom.id d.1
  comp a b := CartesianTripleHom.comp a b
  id_comp a := by
    apply CartesianTripleHom.ext <;> simp [CartesianTripleHom.comp, CartesianTripleHom.id]
  comp_id a := by
    apply CartesianTripleHom.ext <;> simp [CartesianTripleHom.comp, CartesianTripleHom.id]
  assoc a b c := by
    apply CartesianTripleHom.ext <;> simp [CartesianTripleHom.comp, Category.assoc]

/-- The category of étale cartesian triples, whose morphisms are the morphisms
`AlgebraicGeometry.CartesianTripleHom` of the underlying cartesian diagrams. -/
instance (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    Category (EtaleCartesianTriple s) where
  Hom d e := CartesianTripleHom d.1 e.1
  id d := CartesianTripleHom.id d.1
  comp a b := CartesianTripleHom.comp a b
  id_comp a := by
    apply CartesianTripleHom.ext <;> simp [CartesianTripleHom.comp, CartesianTripleHom.id]
  comp_id a := by
    apply CartesianTripleHom.ext <;> simp [CartesianTripleHom.comp, CartesianTripleHom.id]
  assoc a b c := by
    apply CartesianTripleHom.ext <;> simp [CartesianTripleHom.comp, Category.assoc]

/-- Being flat, separated and locally quasi-finite over the pushout `Y ⨿_Z X`. -/
def flatSchemesOverProperty (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    ObjectProperty (Over (pushoutScheme s)) := fun W ↦
  Flat W.hom ∧ IsSeparated W.hom ∧ LocallyOfFiniteType W.hom ∧ LocallyQuasiFinite W.hom

/-- Being étale, separated and locally quasi-finite over the pushout `Y ⨿_Z X`. -/
def etaleSchemesOverProperty (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    ObjectProperty (Over (pushoutScheme s)) := fun W ↦
  Etale W.hom ∧ IsSeparated W.hom ∧ LocallyOfFiniteType W.hom ∧ LocallyQuasiFinite W.hom

/-- The schemes over the pushout `Y ⨿_Z X` which are flat, separated and locally quasi-finite
over it. -/
abbrev flatSchemesOver (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :=
  (flatSchemesOverProperty s).FullSubcategory

/-- The schemes over the pushout `Y ⨿_Z X` which are étale, separated and locally quasi-finite
over it. -/
abbrev etaleSchemesOver (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :=
  (etaleSchemesOverProperty s).FullSubcategory

/-- The morphism of pushouts induced by a morphism of cartesian diagrams, from the universal
property of the source pushout. -/
noncomputable def triplePushoutMap {d e : CartesianDiagram s} (m : CartesianTripleHom d e) :
    pushoutScheme (inducedSituation s d) ⟶ pushoutScheme (inducedSituation s e) :=
  (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.desc
    (m.x ≫ pushoutInl (inducedSituation s e))
    (m.y ≫ pushoutInr (inducedSituation s e)) (by
      rw [← Category.assoc, m.left, Category.assoc,
        (pushoutAlongClosedImmersionAndIntegral (inducedSituation s e)).isPushout.w,
        ← Category.assoc, ← m.right, Category.assoc])

/-- The induced morphism of pushouts restricts to the component over `X`. -/
theorem pushoutInl_comp_triplePushoutMap {d e : CartesianDiagram s}
    (m : CartesianTripleHom d e) :
    pushoutInl (inducedSituation s d) ≫ triplePushoutMap m =
      m.x ≫ pushoutInl (inducedSituation s e) :=
  (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.inl_desc _ _ _

/-- The induced morphism of pushouts restricts to the component over `Y`. -/
theorem pushoutInr_comp_triplePushoutMap {d e : CartesianDiagram s}
    (m : CartesianTripleHom d e) :
    pushoutInr (inducedSituation s d) ≫ triplePushoutMap m =
      m.y ≫ pushoutInr (inducedSituation s e) :=
  (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.inr_desc _ _ _

/-- The morphism of pushouts induced by a morphism of cartesian diagrams is a morphism over the
pushout of the base situation. -/
theorem triplePushoutMap_comp_pushoutMap {d e : CartesianDiagram s}
    (m : CartesianTripleHom d e) :
    triplePushoutMap m ≫ pushoutMap s e = pushoutMap s d := by
  apply (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.hom_ext
  · rw [← Category.assoc, pushoutInl_comp_triplePushoutMap, Category.assoc,
      (pushoutMap_left_isPullback s e).w, ← Category.assoc, m.overX,
      (pushoutMap_left_isPullback s d).w]
  · rw [← Category.assoc, pushoutInr_comp_triplePushoutMap, Category.assoc,
      (pushoutMap_right_isPullback s e).w, ← Category.assoc, m.overY,
      (pushoutMap_right_isPullback s d).w]

/-- A morphism of cartesian diagrams is determined by the morphism of pushouts it induces: the
two cartesian squares of [Stacks Project, Tag 0ECK] recover the components over `X` and `Y`, and
the cartesian square of the source diagram recovers the component over `Z`. -/
theorem triplePushoutMap_injective {d e : CartesianDiagram s}
    {m n : CartesianTripleHom d e} (h : triplePushoutMap m = triplePushoutMap n) : m = n := by
  have hx : m.x = n.x := by
    apply (pushoutMap_left_isPullback s e).hom_ext
    · rw [← pushoutInl_comp_triplePushoutMap, ← pushoutInl_comp_triplePushoutMap, h]
    · rw [m.overX, n.overX]
  have hy : m.y = n.y := by
    apply (pushoutMap_right_isPullback s e).hom_ext
    · rw [← pushoutInr_comp_triplePushoutMap, ← pushoutInr_comp_triplePushoutMap, h]
    · rw [m.overY, n.overY]
  have hz : m.z = n.z := by
    apply e.left_isPullback.hom_ext
    · rw [← m.left, ← n.left, hx]
    · rw [m.overZ, n.overZ]
  exact CartesianTripleHom.ext hx hy hz

/-- Every morphism between two induced pushouts which lies over the pushout of the base
situation comes from a morphism of cartesian diagrams.  The components over `X` and `Y` are
produced by the two cartesian squares of [Stacks Project, Tag 0ECK] and the component over `Z`
by the cartesian square of the target diagram. -/
theorem exists_cartesianTripleHom_of_comp_pushoutMap (d e : CartesianDiagram s)
    (k : pushoutScheme (inducedSituation s d) ⟶ pushoutScheme (inducedSituation s e))
    (hk : k ≫ pushoutMap s e = pushoutMap s d) :
    ∃ m : CartesianTripleHom d e, triplePushoutMap m = k := by
  have hd := pushoutMap_left_isPullback s e
  have he := pushoutMap_right_isPullback s e
  let x := hd.lift (pushoutInl (inducedSituation s d) ≫ k) d.f (by
    rw [Category.assoc, hk, (pushoutMap_left_isPullback s d).w])
  let y := he.lift (pushoutInr (inducedSituation s d) ≫ k) d.g (by
    rw [Category.assoc, hk, (pushoutMap_right_isPullback s d).w])
  have hxPinl : x ≫ pushoutInl (inducedSituation s e) =
      pushoutInl (inducedSituation s d) ≫ k := hd.lift_fst _ _ _
  have hyPinr : y ≫ pushoutInr (inducedSituation s e) =
      pushoutInr (inducedSituation s d) ≫ k := he.lift_fst _ _ _
  have hxOver : x ≫ e.f = d.f := hd.lift_snd _ _ _
  have hcompat : d.i' ≫ x ≫ pushoutInl (inducedSituation s e) =
      d.j' ≫ y ≫ pushoutInr (inducedSituation s e) := by
    rw [hxPinl, hyPinr, ← Category.assoc, ← Category.assoc,
      (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.w]
  have hzpb := pushoutSquare_isPullback (inducedSituation s e)
  let z := hzpb.lift (d.i' ≫ x) (d.j' ≫ y) hcompat
  have hzInl : z ≫ e.i' = d.i' ≫ x := hzpb.lift_fst _ _ _
  have hzOver : z ≫ e.h = d.h := by
    apply (cancel_mono s.i).1
    rw [Category.assoc, ← e.left_isPullback.w, reassoc_of% hzInl, hxOver, d.left_isPullback.w]
  let m : CartesianTripleHom d e :=
    { x := x
      y := y
      z := z
      left := hzInl.symm
      right := (hzpb.lift_snd _ _ _).symm
      overX := hxOver
      overY := he.lift_snd _ _ _
      overZ := hzOver }
  exact ⟨m, (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.hom_ext
    ((pushoutInl_comp_triplePushoutMap m).trans hxPinl)
    ((pushoutInr_comp_triplePushoutMap m).trans hyPinr)⟩

/-- The identity morphism of cartesian diagrams induces the identity of pushouts. -/
theorem triplePushoutMap_id (d : CartesianDiagram s) :
    triplePushoutMap (CartesianTripleHom.id d) = 𝟙 _ := by
  apply (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.hom_ext <;>
    simp [pushoutInl_comp_triplePushoutMap, pushoutInr_comp_triplePushoutMap,
      CartesianTripleHom.id]

/-- The morphism of pushouts induced by a composition is the composition of the induced
morphisms. -/
theorem triplePushoutMap_comp {d e k : CartesianDiagram s} (m : CartesianTripleHom d e)
    (n : CartesianTripleHom e k) :
    triplePushoutMap (CartesianTripleHom.comp m n) =
      triplePushoutMap m ≫ triplePushoutMap n := by
  apply (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.hom_ext
  · rw [pushoutInl_comp_triplePushoutMap, ← Category.assoc,
      pushoutInl_comp_triplePushoutMap, Category.assoc, pushoutInl_comp_triplePushoutMap]
    rfl
  · rw [pushoutInr_comp_triplePushoutMap, ← Category.assoc,
      pushoutInr_comp_triplePushoutMap, Category.assoc, pushoutInr_comp_triplePushoutMap]
    rfl

/-- The pushout construction as a functor from flat cartesian triples to schemes over the
pushout of the base situation. -/
noncomputable def flatTripleToOver (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    FlatCartesianTriple s ⥤ Over (pushoutScheme s) where
  obj d := Over.mk (pushoutMap s d.1)
  map {d e} m := Over.homMk (triplePushoutMap m) (triplePushoutMap_comp_pushoutMap m)
  map_id d := by
    ext
    exact triplePushoutMap_id d.1
  map_comp m n := by
    ext
    exact triplePushoutMap_comp m n

/-- The pushout construction as a functor from étale cartesian triples to schemes over the
pushout of the base situation. -/
noncomputable def etaleTripleToOver (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    EtaleCartesianTriple s ⥤ Over (pushoutScheme s) where
  obj d := Over.mk (pushoutMap s d.1)
  map {d e} m := Over.homMk (triplePushoutMap m) (triplePushoutMap_comp_pushoutMap m)
  map_id d := by
    ext
    exact triplePushoutMap_id d.1
  map_comp m n := by
    ext
    exact triplePushoutMap_comp m n

end AlgebraicGeometry

end
