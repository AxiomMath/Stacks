module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TwoYonedaPairs

/-!
# The 2-fibre product of the two graphs of a parallel pair, and the equalizing morphisms it
classifies

Let `p : 𝒳 ⥤ 𝒞` be a category fibred in groupoids, let `x`, `x'` be objects of the fibres `𝒳_U`,
`𝒳_{U'}` and let `a, b : x ⟶ x'` be two parallel morphisms of `𝒳`, lying over morphisms
`g_a, g_b : U ⟶ U'` of `𝒞`. The 2-Yoneda lemma (Stacks 004B) turns `x` and `x'` into 1-morphisms
`𝒞/U ⟶ 𝒳` and `𝒞/U' ⟶ 𝒳` over `𝒞`, and `a` into a 1-morphism `Γ_a : 𝒞/U ⟶ U ×_{x, 𝒳, x'} U'`
over `𝒞` — its **graph** in the sense of Stacks 050I, taken over `𝒳`. This file describes the
2-fibre product

```text
U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U
```

in the (2,1)-category of categories over `𝒞`, and proves that an object of it amounts to **a
morphism of `𝒳` into `x` equalizing `a` and `b`**.

It is the counterpart, for the equalizer of a parallel pair, of
`StacksFrontier/CategoryTheory/TwoFibreProduct/TwoYonedaPairs.lean`, which does the same for the
2-fibre product of the two represented slices and the *pairs* of morphisms it classifies. The
consumer is condition (4) of **Stacks 0GN4** for the fppf site of an algebraic stack, where the
source identifies the equalizer with the one of the two underlying morphisms of schemes — an
identification which is loose, because the pullback of `x` along the scheme-level equalizer of
`g_a` and `g_b` need *not* equalize `a` and `b`, the two composites lying over the same morphism
of `𝒞` but differing by an automorphism of its source. The object which does classify the
equalizing morphisms is the 2-fibre product above.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.comparison` and `.comparisonIso`: the
  2-isomorphism `x ≅ g_a ≫ x'` of 1-morphisms out of `𝒞/U` which exhibits `a` as a 1-morphism
  over `𝒳`, built as the unique *vertical* identification factoring the chosen cartesian arrow of
  `x` followed by `a` through the chosen cartesian arrow of `x'`.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.graphFunctor`: the graph
  `Γ_a : 𝒞/U ⟶ U ×_{x, 𝒳, x'} U'` itself, the mediating 1-morphism of Stacks 0040 for the cone
  with legs the identity and the slice functor of `g_a`.
* `CategoryTheory.TwoFibreProductOver.twoYonedaGraph`: the 2-fibre product of the two graphs.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.objOf`, `.fstHom`, `.map`: the object of `𝒳`
  an object of that 2-fibre product classifies, the morphism into `x` it classifies, and the
  morphism of `𝒳` a morphism of it induces.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.objOfSlice`: the object of the 2-fibre
  product attached to an object of the slice whose chosen cartesian arrow equalizes `a` and `b`.

## Main results

* `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.comparison_hom_comp_chosenHom`: the defining
  property of the comparison isomorphism of the graph, and
  `.graphFunctor_obj_iso_hom_comp_chosenHom`, the same at the components of the quadruple the
  graph produces.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.fstHom_comp_eq`: **the morphism an object of
  the 2-fibre product classifies equalizes `a` and `b`.**
* `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.map_comp_fstHom`: a morphism of the 2-fibre
  product carries the classified morphism of its source to the classified morphism of its target.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.exists_objOf_of_equalizing_hom`: **every
  morphism of `𝒳` into `x` equalizing `a` and `b` is classified by an object of the 2-fibre
  product lying over the image of its source.**

Nothing here is a statement of the Stacks project: the source states the graph of a 1-morphism of
algebraic stacks (Stacks 050I, in this library `AlgebraicGeometry.Stack.graph`) and the fibre
categories of a 2-fibre product one of whose factors is a slice (Stacks 02Y5), not this absolute
description of the 2-fibre product of two graphs of 2-Yoneda 1-morphisms, which the proof of
Stacks 0GN4 condition (4) for a stack uses silently. No `@[stacks]` attribute is carried.

## Implementation notes

The graph is built here as `CategoryTheory.TwoFibreProductOver.lift` rather than through
`AlgebraicGeometry.Stack.graph`, which is Stacks 050I in the 2-category of algebraic stacks.
Those agree, but `AlgebraicGeometry.Stack.graph` is produced from the universal property by
`Quotient.out` and so has no description on objects, while the dictionary needs one: the whole
content of `.fstHom_comp_eq` is the defining property
`.comparison_hom_comp_chosenHom` of the filler, which pins the filler down uniquely
— a 1-morphism `𝒞/U ⟶ 𝒳` has as many vertical self-2-isomorphisms as `x` has automorphisms in its
fibre, and only one of them makes the square with the chosen cartesian arrows commute. Taking
`lift` of the identity and of `Over.map g_a` also makes both projections of the graph correct on
the nose rather than up to 2-isomorphism, which is what lets
`.objOf` and `.fstHom` be stated without any transport.

The base morphisms `g_a`, `g_b` are taken as *data* with `p.IsHomLift` hypotheses rather than
read off as `p.map a`. That is what keeps the file free of `eqToHom`: the one place an object
equality would arise is the passage from a bare morphism `α : y ⟶ x` to the slice object it lies
over, and it happens once, in
`.exists_objOf_of_equalizing_hom`, everything else being stated relative to a given slice object
by `.exists_objOf_of_equalizing_hom_of_slice`.

Two morphisms of `𝒞` with the same source and target which are lifted by one and the same
morphism of `𝒳` are equal, by `CategoryTheory.IsHomLift.fac` twice and proof irrelevance. That is
how `s ≫ g_a = s ≫ g_b` is obtained from `α ≫ a = α ≫ b`, with no computation in `𝒞`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 02Y5](https://stacks.math.columbia.edu/tag/02Y5)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

-- `Functor.Fiber` is a plain `def`, and the 2-fibre product's projections, structure functor and
-- mediating 1-morphism are semireducible, so without these the goals below — which mention the
-- components of an object of a 2-fibre product taken at a mediating 1-morphism — are not
-- type-correct at `implicit` transparency and `rw` declines to abstract over their subterms.
attribute [local implicit_reducible] Functor.Fiber lift fst snd structureFunctor

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒞}
  (hp : p.IsFiberedInGroupoids) {U U' : 𝒞} (x : p.Fiber U) (x' : p.Fiber U')

namespace TwoYonedaGraph

/-- **Two morphisms `U ⟶ U'` which agree after precomposition with the structure morphism of an
object `s` of the slice `𝒞/U` give isomorphic images of `s` in the slice `𝒞/U'`**, through the
morphism whose underlying morphism of `𝒞` is the identity.

This is the second component of the comparison morphism of the two graphs of a parallel pair:
equalizing forces the two base morphisms to agree after precomposition, and no more. -/
def overMapCompare {f f' : U ⟶ U'} (s : Over U) (h : s.hom ≫ f = s.hom ≫ f') :
    (Over.map f).obj s ⟶ (Over.map f').obj s :=
  Over.homMk (𝟙 s.left) (by simpa using h.symm)

/-- The underlying morphism of `𝒞` of `overMapCompare` is the identity. -/
@[simp]
theorem overMapCompare_left {f f' : U ⟶ U'} (s : Over U) (h : s.hom ≫ f = s.hom ≫ f') :
    (overMapCompare s h).left = 𝟙 s.left := rfl

include hp

section Graph

variable (g : U ⟶ U') (a : x.1 ⟶ x'.1) [p.IsHomLift g a]

/-- The chosen cartesian arrow of `x` at `s`, followed by `a`, lies over `s.hom ≫ g`, which is
the structure morphism of `(Over.map g).obj s`. -/
instance isHomLift_chosenHom_comp (s : Over U) :
    p.IsHomLift ((Over.map g).obj s).hom (TwoYonedaPair.chosenHom hp x s ≫ a) := by
  have hobj : ((Over.map g).obj s).hom = s.hom ≫ g := rfl
  have hc : p.IsHomLift s.hom (TwoYonedaPair.chosenHom hp x s) :=
    (TwoYonedaPair.isStronglyCartesian_chosenHom hp x s).toIsHomLift
  rw [hobj]
  exact IsHomLift.comp p s.hom g _ a

/-- The image under the 2-Yoneda functor of a morphism of the slice lies over its own underlying
morphism of `𝒞`. -/
instance isHomLift_liftFunctor_map {s s' : Over U} (h : s ⟶ s') :
    p.IsHomLift h.left ((Functor.TwoYoneda.liftFunctor p hp U x).map h) :=
  IsHomLift.of_fac' p h.left _
    (Functor.congr_obj (Functor.TwoYoneda.liftFunctor_w p hp U x) s)
    (Functor.congr_obj (Functor.TwoYoneda.liftFunctor_w p hp U x) s')
    (by simpa using Functor.congr_hom (Functor.TwoYoneda.liftFunctor_w p hp U x) h)

/-- The comparison isomorphism of the graph of `a` at an object `s` of the slice `𝒞/U`: the
unique vertical isomorphism `s^*x ≅ (s ≫ g)^*x'` through which the chosen cartesian arrow of `x`
at `s` followed by `a` factors as the chosen cartesian arrow of `x'`. -/
def comparison (s : Over U) :
    (Functor.TwoYoneda.liftFunctor p hp U x).obj s ≅
      (Functor.TwoYoneda.liftFunctor p hp U' x').obj ((Over.map g).obj s) :=
  TwoYonedaPair.fstIso hp x' ((Over.map g).obj s) (TwoYonedaPair.chosenHom hp x s ≫ a)

/-- **The defining property of the comparison isomorphism of the graph of `a`**: it factors the
chosen cartesian arrow of `x` followed by `a` through the chosen cartesian arrow of `x'`. -/
@[simp]
theorem comparison_hom_comp_chosenHom (s : Over U) :
    (comparison hp x x' g a s).hom ≫ TwoYonedaPair.chosenHom hp x' ((Over.map g).obj s) =
      TwoYonedaPair.chosenHom hp x s ≫ a :=
  TwoYonedaPair.fstIso_hom_comp_chosenHom hp x' _ _

/-- The comparison isomorphism of the graph of `a` is vertical. -/
instance isHomLift_comparison_hom (s : Over U) :
    p.IsHomLift (𝟙 s.left) (comparison hp x x' g a s).hom :=
  TwoYonedaPair.isHomLift_fstIso_hom hp x' ((Over.map g).obj s)
    (TwoYonedaPair.chosenHom hp x s ≫ a)

/-- **The comparison isomorphisms of the graph of `a` are natural in `s`.** Both sides of the
naturality square lie over the underlying morphism of `𝒞` of the morphism of slices, and agree
after composition with the chosen cartesian arrow of `x'`, which is strongly cartesian over the
structure morphism of its index; so they are equal. -/
def comparisonIso :
    Functor.TwoYoneda.liftFunctor p hp U x ≅
      Over.map g ⋙ Functor.TwoYoneda.liftFunctor p hp U' x' :=
  NatIso.ofComponents (comparison hp x x' g a) (by
    intro s s' h
    simp only [Functor.comp_map]
    have hmap : p.IsHomLift h.left
        ((Functor.TwoYoneda.liftFunctor p hp U' x').map ((Over.map g).map h)) :=
      isHomLift_liftFunctor_map hp x' ((Over.map g).map h)
    have : p.IsHomLift h.left ((Functor.TwoYoneda.liftFunctor p hp U x).map h ≫
        (comparison hp x x' g a s').hom) := inferInstance
    have : p.IsHomLift h.left ((comparison hp x x' g a s).hom ≫
        (Functor.TwoYoneda.liftFunctor p hp U' x').map ((Over.map g).map h)) := inferInstance
    refine Functor.IsStronglyCartesian.ext p ((Over.map g).obj s').hom
      (TwoYonedaPair.chosenHom hp x' ((Over.map g).obj s')) h.left ?_
    simp only [Category.assoc]
    rw [comparison_hom_comp_chosenHom,
      TwoYonedaPair.map_comp_chosenHom hp x' ((Over.map g).map h),
      comparison_hom_comp_chosenHom, ← Category.assoc,
      TwoYonedaPair.map_comp_chosenHom hp x h])

/-- **The graph of `a` as a 1-morphism `𝒞/U ⟶ U ×_{x, 𝒳, x'} U'` of categories over `𝒞`**
(Stacks 050I at the two 2-Yoneda 1-morphisms): the mediating 1-morphism of Stacks 0040 for the
test cone with legs the identity of `𝒞/U` and the slice functor `Over.map g`, filled by
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.comparisonIso`.

So its first projection is the identity and its second projection the slice functor of `g`, both
on the nose, and the quadruple it attaches to `s` is the one of the pair
`(s^*x ⟶ x, s^*x ⟶ x ⟶ x')`. -/
def graphFunctor : Over U ⥤ twoYonedaPair hp x x' :=
  lift (Over.forget U) (Over.forget U') p
    (Functor.TwoYoneda.liftFunctor p hp U x) (Functor.TwoYoneda.liftFunctor p hp U' x')
    (Over.forget U) (𝟭 (Over U)) (Over.map g) rfl rfl (comparisonIso hp x x' g a)
    (fun s => isHomLift_comparison_hom hp x x' g a s)

/-- The graph of `a` is a 1-morphism of categories over `𝒞`. -/
theorem graphFunctor_comp_structureFunctor :
    graphFunctor hp x x' g a ⋙
        structureFunctor (Over.forget U) (Over.forget U') p
          (Functor.TwoYoneda.liftFunctor p hp U x)
          (Functor.TwoYoneda.liftFunctor p hp U' x') =
      Over.forget U :=
  lift_comp_structureFunctor ..

/-- The quadruple the graph of `a` attaches to `s` has `s` as its first component. -/
@[simp]
theorem graphFunctor_obj_x (s : Over U) : ((graphFunctor hp x x' g a).obj s).x = s := rfl

/-- The quadruple the graph of `a` attaches to `s` lies over the base object of `s`. -/
@[simp]
theorem graphFunctor_obj_base (s : Over U) :
    ((graphFunctor hp x x' g a).obj s).base = s.left := rfl

/-- The second component of the quadruple the graph of `a` attaches to `s` is the image of `s`
under the slice functor of `g`. -/
@[simp]
theorem graphFunctor_obj_y (s : Over U) :
    ((graphFunctor hp x x' g a).obj s).y = (Over.map g).obj s := rfl

/-- The comparison isomorphism of the quadruple the graph of `a` attaches to `s`. -/
@[simp]
theorem graphFunctor_obj_iso_hom (s : Over U) :
    ((graphFunctor hp x x' g a).obj s).iso.hom = (comparison hp x x' g a s).hom := rfl

/-- **The defining property of the comparison isomorphism of the graph of `a`**, stated at the
components of the quadruple the graph attaches to `s` rather than at `s` itself. This is the
spelling in which the components of a morphism of a 2-fibre product taken at two graphs are
type-correct. -/
theorem graphFunctor_obj_iso_hom_comp_chosenHom (s : Over U) :
    ((graphFunctor hp x x' g a).obj s).iso.hom ≫
        TwoYonedaPair.chosenHom hp x' ((graphFunctor hp x x' g a).obj s).y =
      TwoYonedaPair.chosenHom hp x ((graphFunctor hp x x' g a).obj s).x ≫ a :=
  comparison_hom_comp_chosenHom hp x x' g a s

/-- The first component of the morphism of quadruples the graph of `a` attaches to a morphism of
slices is that morphism. -/
@[simp]
theorem graphFunctor_map_a {s s' : Over U} (h : s ⟶ s') :
    ((graphFunctor hp x x' g a).map h).a = h := rfl

end Graph

end TwoYonedaGraph

section Equalizer

variable (ga : U ⟶ U') (a : x.1 ⟶ x'.1) [p.IsHomLift ga a]
  (gb : U ⟶ U') (b : x.1 ⟶ x'.1) [p.IsHomLift gb b]

include hp

/-- **The 2-fibre product `U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` of the two graphs of a parallel
pair `a, b : x ⟶ x'`**, in the (2,1)-category of categories over `𝒞`.

This is the object which classifies the morphisms of `𝒳` into `x` equalizing `a` and `b`, in the
same way as `CategoryTheory.TwoFibreProductOver.twoYonedaPair` classifies the pairs of morphisms
into `x` and into `x'`. -/
abbrev twoYonedaGraph : Type max u₁ v₁ :=
  TwoFibreProductOver (Over.forget U) (Over.forget U)
    (structureFunctor (Over.forget U) (Over.forget U') p
      (Functor.TwoYoneda.liftFunctor p hp U x) (Functor.TwoYoneda.liftFunctor p hp U' x'))
    (TwoYonedaGraph.graphFunctor hp x x' ga a) (TwoYonedaGraph.graphFunctor hp x x' gb b)

namespace TwoYonedaGraph

include hp

/-- The object of `𝒳` an object of `U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` classifies: the chosen
pullback `s^*x` of `x` along its first component. It lies over the base object. -/
abbrev objOf (P : twoYonedaGraph hp x x' ga a gb b) : 𝒳 :=
  (Functor.TwoYoneda.liftFunctor p hp U x).obj P.x

/-- The morphism of `𝒳` an object of `U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` classifies: the
chosen cartesian arrow `s^*x ⟶ x` at its first component. -/
def fstHom (P : twoYonedaGraph hp x x' ga a gb b) : objOf hp x x' ga a gb b P ⟶ x.1 :=
  TwoYonedaPair.chosenHom hp x P.x

/-- **The morphism an object of `U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` classifies equalizes `a`
and `b`.**

This is the content of the presentation of the equalizer by the two graphs, and it is where the
comparison isomorphisms of the two graphs are used. Composing the commuting square of the
comparison isomorphism of the object with the chosen cartesian arrow of `x'` turns its two sides
into the chosen cartesian arrow of `x` followed by `a` and by `b` respectively: the defining
property of the two comparison isomorphisms accounts for the two factors, and the two components
of the comparison isomorphism of the object carry the chosen arrows at its second component back
to the ones at its first. -/
theorem fstHom_comp_eq (P : twoYonedaGraph hp x x' ga a gb b) :
    fstHom hp x x' ga a gb b P ≫ a = fstHom hp x x' ga a gb b P ≫ b := by
  change TwoYonedaPair.chosenHom hp x ((graphFunctor hp x x' ga a).obj P.x).x ≫ a =
    TwoYonedaPair.chosenHom hp x ((graphFunctor hp x x' ga a).obj P.x).x ≫ b
  rw [← graphFunctor_obj_iso_hom_comp_chosenHom hp x x' ga a P.x,
    ← TwoYonedaPair.map_comp_chosenHom hp x' P.iso.hom.b, ← Category.assoc, ← P.iso.hom.w,
    Category.assoc, graphFunctor_obj_iso_hom_comp_chosenHom hp x x' gb b P.y, ← Category.assoc,
    TwoYonedaPair.map_comp_chosenHom hp x P.iso.hom.a]

/-- The morphism of `𝒳` a morphism of `U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` induces between the
objects its source and target classify: the image under the 2-Yoneda functor of `x` of the first
component of its first component. -/
abbrev map {P Q : twoYonedaGraph hp x x' ga a gb b} (ψ : P ⟶ Q) :
    objOf hp x x' ga a gb b P ⟶ objOf hp x x' ga a gb b Q :=
  (Functor.TwoYoneda.liftFunctor p hp U x).map ψ.a

/-- **A morphism of `U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` carries the classified morphism of its
source to the classified morphism of its target.** -/
theorem map_comp_fstHom {P Q : twoYonedaGraph hp x x' ga a gb b} (ψ : P ⟶ Q) :
    map hp x x' ga a gb b ψ ≫ fstHom hp x x' ga a gb b Q = fstHom hp x x' ga a gb b P :=
  TwoYonedaPair.map_comp_chosenHom hp x ψ.a

/-- **The comparison morphism of the two graphs at an object `s` of the slice whose chosen
cartesian arrow equalizes `a` and `b`**: both components are identities, the second being read
through the equality `s ≫ g_a = s ≫ g_b` of base morphisms which equalizing forces.

The commuting square it has to satisfy is again the defining property of the two comparison
isomorphisms: after composition with the chosen cartesian arrow of `x'` its two sides become the
chosen arrow of `x` at `s` followed by `b` and by `a`, which the hypothesis identifies. -/
def compare (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    (graphFunctor hp x x' ga a).obj s ⟶ (graphFunctor hp x x' gb b).obj s where
  hbase := 𝟙 s.left
  a := 𝟙 s
  b := overMapCompare s hg
  ha := IsHomLift.map (Over.forget U) (𝟙 s)
  hb := IsHomLift.map (Over.forget U') (overMapCompare s hg)
  w := by
    have hmap : p.IsHomLift (𝟙 s.left)
        ((Functor.TwoYoneda.liftFunctor p hp U' x').map (overMapCompare (f := ga) (f' := gb) s hg))
          := isHomLift_liftFunctor_map hp x' (overMapCompare s hg)
    have : p.IsHomLift (𝟙 s.left) ((comparison hp x x' ga a s).hom ≫
        (Functor.TwoYoneda.liftFunctor p hp U' x').map
          (overMapCompare (f := ga) (f' := gb) s hg)) := inferInstance
    change (Functor.TwoYoneda.liftFunctor p hp U x).map (𝟙 s) ≫ (comparison hp x x' gb b s).hom =
      (comparison hp x x' ga a s).hom ≫
        (Functor.TwoYoneda.liftFunctor p hp U' x').map (overMapCompare s hg)
    rw [Functor.map_id, Category.id_comp]
    refine (Functor.IsStronglyCartesian.ext p ((Over.map gb).obj s).hom
      (TwoYonedaPair.chosenHom hp x' ((Over.map gb).obj s)) (𝟙 s.left) ?_).symm
    rw [Category.assoc, TwoYonedaPair.map_comp_chosenHom hp x' (overMapCompare s hg),
      comparison_hom_comp_chosenHom, comparison_hom_comp_chosenHom, hs]

/-- The base morphism of the comparison morphism of the two graphs is an identity. -/
@[simp]
theorem compare_hbase (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    (compare hp x x' ga a gb b s hg hs).hbase = 𝟙 s.left := rfl

/-- The first component of the comparison morphism of the two graphs is an identity. -/
@[simp]
theorem compare_a (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    (compare hp x x' ga a gb b s hg hs).a = 𝟙 s := rfl

/-- The second component of the comparison morphism of the two graphs has identity underlying
morphism. -/
@[simp]
theorem compare_b_left (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    (compare hp x x' ga a gb b s hg hs).b.left = 𝟙 s.left := rfl

/-- **The comparison morphism of the two graphs at such an `s` is an isomorphism**: both of its
components are identities, so the morphism in the opposite direction built the same way is
inverse to it. -/
def compareIso (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    (graphFunctor hp x x' ga a).obj s ≅ (graphFunctor hp x x' gb b).obj s where
  hom := compare hp x x' ga a gb b s hg hs
  inv := compare hp x x' gb b ga a s hg.symm hs.symm
  hom_inv_id := by
    refine Hom.ext' ?_ (Over.OverMorphism.ext ?_) <;> exact Category.comp_id _
  inv_hom_id := by
    refine Hom.ext' ?_ (Over.OverMorphism.ext ?_) <;> exact Category.comp_id _

/-- The underlying comparison morphism of
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.compareIso`. -/
@[simp]
theorem compareIso_hom (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    (compareIso hp x x' ga a gb b s hg hs).hom = compare hp x x' ga a gb b s hg hs := rfl

/-- **The object of `U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` attached to an object of the slice
whose chosen cartesian arrow equalizes `a` and `b`**: both its components are `s` and its
comparison isomorphism is
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.compareIso`. -/
def objOfSlice (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    twoYonedaGraph hp x x' ga a gb b where
  base := s.left
  x := s
  y := s
  hx := rfl
  hy := rfl
  iso := compareIso hp x x' ga a gb b s hg hs
  vertical := IsHomLift.map
    (structureFunctor (Over.forget U) (Over.forget U') p
      (Functor.TwoYoneda.liftFunctor p hp U x) (Functor.TwoYoneda.liftFunctor p hp U' x'))
    (compareIso hp x x' ga a gb b s hg hs).hom

/-- The object attached to such an `s` has `s` as its first component, hence classifies the
chosen pullback `s^*x` and the chosen cartesian arrow at `s`. -/
@[simp]
theorem objOfSlice_x (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    (objOfSlice hp x x' ga a gb b s hg hs).x = s := rfl

/-- The object attached to such an `s` lies over the base object of `s`. -/
@[simp]
theorem objOfSlice_base (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    (objOfSlice hp x x' ga a gb b s hg hs).base = s.left := rfl

/-- The morphism the object attached to such an `s` classifies is the chosen cartesian arrow
at `s`. -/
@[simp]
theorem fstHom_objOfSlice (s : Over U) (hg : s.hom ≫ ga = s.hom ≫ gb)
    (hs : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b) :
    fstHom hp x x' ga a gb b (objOfSlice hp x x' ga a gb b s hg hs) =
      TwoYonedaPair.chosenHom hp x s := rfl

/-- **A morphism of `𝒳` into `x` equalizing `a` and `b` is classified by an object of
`U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` over the object of the slice it lies over.**

Relative to a slice object `s` which `α : y ⟶ x` lies over, the object is
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.objOfSlice` at `s`: the chosen cartesian arrow
of `x` at `s` equalizes `a` and `b` because `α` does and the two differ by the identification `α`
provides, and the equality of base morphisms that construction needs holds because
`s ≫ g_a` and `s ≫ g_b` are both lifted by the one morphism `α ≫ a = α ≫ b`.

The identification is *vertical*: both it and its inverse lie over the identity of the base
object, which is what lets a consumer compose with its inverse without leaving a fibre.

This is the form with no object equality in it; the one a consumer holding only `α` can use is
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.exists_objOf_of_equalizing_hom`. -/
theorem exists_objOf_of_equalizing_hom_of_slice (s : Over U) {y : 𝒳} (α : y ⟶ x.1)
    [p.IsHomLift s.hom α] (hα : α ≫ a = α ≫ b) :
    ∃ (P : twoYonedaGraph hp x x' ga a gb b) (e : y ≅ objOf hp x x' ga a gb b P),
      P.base = s.left ∧ p.IsHomLift (𝟙 s.left) e.inv ∧
        e.hom ≫ fstHom hp x x' ga a gb b P = α := by
  have he : (TwoYonedaPair.fstIso hp x s α).hom ≫ TwoYonedaPair.chosenHom hp x s = α :=
    TwoYonedaPair.fstIso_hom_comp_chosenHom hp x s α
  have hchosen : TwoYonedaPair.chosenHom hp x s ≫ a = TwoYonedaPair.chosenHom hp x s ≫ b :=
    (Iso.cancel_iso_hom_left (TwoYonedaPair.fstIso hp x s α) _ _).1 <| by
      rw [← Category.assoc, ← Category.assoc, he, hα]
  have hga : p.IsHomLift (s.hom ≫ ga) (α ≫ b) := by
    rw [← hα]
    exact IsHomLift.comp p s.hom ga α a
  have hgb : p.IsHomLift (s.hom ≫ gb) (α ≫ b) := IsHomLift.comp p s.hom gb α b
  have hg : s.hom ≫ ga = s.hom ≫ gb :=
    (IsHomLift.fac p (s.hom ≫ ga) (α ≫ b)).trans (IsHomLift.fac p (s.hom ≫ gb) (α ≫ b)).symm
  exact ⟨objOfSlice hp x x' ga a gb b s hg hchosen, TwoYonedaPair.fstIso hp x s α, rfl,
    TwoYonedaPair.isHomLift_fstIso_inv hp x s α, he⟩

/-- **Every morphism of `𝒳` into `x` equalizing `a` and `b` is classified by an object of
`U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` lying over the image of its source.**

This is the analogue for the graph presentation of
`CategoryTheory.TwoFibreProductOver.TwoYonedaPair.exists_quadruple_of_hom_pair`: given
`α : y ⟶ x` with `α ≫ a = α ≫ b` there is an object `P` whose base is `p y` on the nose,
together with a vertical isomorphism of `y` with the object `P` classifies carrying the morphism
`P` classifies back to `α`.

It is
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.exists_objOf_of_equalizing_hom_of_slice` at
the slice object `p α : p y ⟶ U`, read through the equality `p x = U` witnessing that `x` lies in
its fibre; that is the only bookkeeping, and it happens once, here. -/
theorem exists_objOf_of_equalizing_hom {y : 𝒳} (α : y ⟶ x.1) (hα : α ≫ a = α ≫ b) :
    ∃ (P : twoYonedaGraph hp x x' ga a gb b) (e : y ≅ objOf hp x x' ga a gb b P),
      P.base = p.obj y ∧ p.IsHomLift (𝟙 (p.obj y)) e.inv ∧
        e.hom ≫ fstHom hp x x' ga a gb b P = α := by
  have : p.IsHomLift (Over.mk (p.map α ≫ eqToHom x.2)).hom α :=
    IsHomLift.of_fac' p _ α rfl x.2 (by simp)
  exact exists_objOf_of_equalizing_hom_of_slice hp x x' ga a gb b
    (Over.mk (p.map α ≫ eqToHom x.2)) α hα

end TwoYonedaGraph

end Equalizer

end CategoryTheory.TwoFibreProductOver

end
