module

public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyEqualizerDictionary
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TwoYonedaGraphs
public import StacksCore.Tactic.StacksAttribute

/-!
# Condition (4) of Stacks 0GN4 for the fppf site of an algebraic stack

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site, and give its total
category the fppf topology of **Stacks 06TP**. Condition (4) of **Stacks 0GN4** asks, for two
objects `x`, `x'` of that site lying over affine schemes and two parallel morphisms
`a, b : x ⟶ x'`, for a finite family `V_i` of such objects with morphisms `p_i : V_i ⟶ x`
equalizing `a` and `b` for which `∐_i h_{V_i}^# ⟶ Equalizer(h_a^#, h_b^#)` is a surjection of
fppf sheaves of sets. This file proves that condition, with one member, for a stack which is
quasi-separated over a quasi-separated base scheme, and so completes the four conditions of
Stacks 0GN4 for the fppf site.

`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEqualizerDictionary.lean` reduced the
condition to one geometric statement, the hypothesis `h_affine_dominating` of
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_of_exists_affine_dominating`: one
object `V` lying over an affine scheme with an equalizing morphism `p_V : V ⟶ x` which dominates
every equalizing morphism of the site after a covering taken in the big fppf category over `S`.
What is added here is that statement, `AlgebraicGeometry.Stack.exists_affine_dominating`.

## The 2-fibre product which classifies the equalizing morphisms

The source identifies the equalizer of `h_a^#` and `h_b^#` with the equalizer of the two
underlying morphisms of schemes, and that identification is loose: the pullback `ζ` of `x` along
the scheme-level equalizer of `p(a)` and `p(b)` need *not* satisfy `ζ ≫ a = ζ ≫ b`, the two
composites lying over the same morphism of the base but differing by an automorphism of the
source of `ζ`. The object which does classify the equalizing morphisms is the 2-fibre product

```text
U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U
```

of the two **graphs** of `a` and of `b` over the 2-fibre product condition (3) is about, and it is
a quasi-compact quasi-separated algebraic stack rather than an affine scheme. Three inputs make it
available.

* The **graph** is **Stacks 050I** over `𝒳`. It is taken here in the concrete form
  `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.graphFunctor`, whose two projections are the
  identity and the slice functor of `p(a)` on the nose, and whose filler is pinned down by its
  compatibility with the chosen cartesian arrows of the 2-Yoneda lemma. That compatibility is the
  entire content of the dictionary, so the graph is built from it rather than from the universal
  property; see the implementation notes of
  `StacksFrontier/CategoryTheory/TwoFibreProduct/TwoYonedaGraphs.lean`.
* **Quasi-compactness** of the 2-fibre product is **Stacks 075S** part (3) at the two graphs,
  `AlgebraicGeometry.Stack.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct`, which
  needs nothing of the two 1-morphisms: the two sources are the slice at an affine object, hence
  quasi-compact and quasi-separated over `S`, and the target is quasi-separated over `S` by
  `AlgebraicGeometry.Stack.isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism`.
  This is where quasi-separatedness of `𝒳` genuinely enters, through
  `AlgebraicGeometry.Stack.isQuasiSeparatedOver_schemeStack_of_isAffine` — a step the source never
  invokes at condition (4).
* The **dictionary** between the objects of that 2-fibre product and the equalizing morphisms of
  the site is `StacksFrontier/CategoryTheory/TwoFibreProduct/TwoYonedaGraphs.lean`, the analogue for
  the graph presentation of `StacksFrontier/CategoryTheory/TwoFibreProduct/TwoYonedaPairs.lean`:
  `CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.fstHom_comp_eq` says the morphism an object
  classifies equalizes `a` and `b`,
  `.exists_objOf_of_equalizing_hom` says every equalizing morphism arises from an object over the
  scheme its source lies over, and `.map_comp_fstHom` says a morphism of the 2-fibre product
  induces a morphism of the site compatible with the classified morphisms.

## Main definitions

* `AlgebraicGeometry.Stack.graphAlgebraicStacks`: the graph of a morphism of the fppf site, as a
  1-morphism of algebraic stacks from the slice at its source into the 2-fibre product of the two
  2-Yoneda 1-morphisms.
* `AlgebraicGeometry.Stack.equalizerTwoFibreProduct`: the 2-fibre product of the two graphs.
* `AlgebraicGeometry.Stack.equalizerObjects`, `.equalizerObj`, `.equalizerHom`, `.equalizerMap`:
  the objects of that 2-fibre product, the object of the site one of them classifies, the
  equalizing morphism it classifies, and the morphism of the site a morphism of them induces.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactStack_equalizerTwoFibreProduct`: the 2-fibre product of
  the two graphs is a quasi-compact algebraic stack, for a stack quasi-separated over a
  quasi-separated base scheme.
* `AlgebraicGeometry.Stack.isHomLift_equalizerMap`: the morphism of the site a morphism of the
  2-fibre product induces lies over the same morphism of the base.
* `AlgebraicGeometry.Stack.exists_graph_dominating`: one object of the 2-fibre product lying over
  an affine scheme which dominates every object after a covering taken in the big fppf category
  over `S`.
* `AlgebraicGeometry.Stack.exists_affine_dominating`: the geometric statement
  `h_affine_dominating`, which is what condition (4) was reduced to.
* `AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift`:
  **condition (4) itself**, in the shape
  `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf` consumes as its
  hypothesis `h_equalizer`.
* `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact`:
  **Stacks 0GQV in the fppf topology** for a quasi-compact algebraic stack quasi-separated over a
  quasi-separated base scheme, with all four conditions of Stacks 0GN4 discharged.

## Implementation notes

The dominating object is produced exactly as the dominating quadruple of condition (3) is, in
`AlgebraicGeometry.Stack.exists_quadruple_dominating`. **Stacks 04YC** parts (1) and (2) turn
quasi-compactness of the 2-fibre product into an affine object `U₀` and a surjective, relatively
smooth 1-morphism `f` from the slice it represents; `Q` is `f(1_{U₀})`, which lies over `U₀`
because `f` is a based functor; relative smoothness gives flatness and local finite presentation,
and **Stacks 06QA** then covers the base object of any object `P` by objects over each of which
`P` receives a morphism from `f(ξ)` for an object `ξ` of the slice over `U₀`.

Two identifications make that passage free of transport. The total category of the 2-fibre product
of algebraic stacks at the two graphs is
`CategoryTheory.TwoFibreProductOver.twoYonedaGraph` on the nose, by
`AlgebraicGeometry.Stack.obj_equalizerTwoFibreProduct`; and the object of the site an object of it
classifies lies over the base object of that object, by
`AlgebraicGeometry.Stack.obj_equalizerObj`, so the covering sieve Stacks 06QA produces downstairs
is already a sieve where the consumer wants it.

The one place an object equality is unavoidable is the passage from an equalizing morphism
`α : y ⟶ x` of the site to the object of the 2-fibre product classifying it: that object lies
over the scheme `y` lies over, but only up to the equality the dictionary returns, so the covering
sieve the dominating object carries has to be read on the other side of it. The isomorphism of `y`
with the object classified is vertical, which is what makes the composite morphism of the site
produced at each member of the covering lie over that member and not merely over its image.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] essentiallySmall_join hasSheafify_ab_join enoughInjectives_sheaf_join
  globalSections_additive_join

universe v₀ u₀

/-- Sheaves of sets on a site have coproducts over an index type in `Type`, built from the
colimits of the size of the join of the two universes of the site. The instance is needed to form
the finite coproducts of sheafified representables condition (4) of Stacks 0GN4 speaks of, and is
restated in this constructed form — rather than as the
`CategoryTheory.Limits.HasColimitsOfSize` at the join universe which the files proving
Stacks 0GN3 and Stacks 0GN4 install — because with the imports of this file the search that
descends from that statement to the coproduct over a finite index type does not terminate within
the elaborator's budget. Pinning the instance at the shape actually used costs nothing and is
local to this file. It is anonymous because the files this one imports export declarations of the
same name whose `instance` attribute is local to them. -/
local instance {C : Type u₀} [Category.{v₀} C]
    (J : GrothendieckTopology C) {ι : Type} (A : ι → Sheaf J (Type max u₀ v₀)) :
    HasCoproduct A :=
  letI : HasColimitsOfSize.{max u₀ v₀, max u₀ v₀} (Sheaf J (Type max u₀ v₀)) :=
    Sheaf.instHasColimitsOfSize
  letI : HasColimitsOfSize.{0, 0} (Sheaf J (Type max u₀ v₀)) := hasColimitsOfSizeShrink _
  inferInstance

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

section Graph

variable {x x' : 𝒳.val.val.obj}

/-- **A morphism of the fppf site lies over its own image in the big fppf category over `S`**,
with its source and target spelled as the underlying objects of the fibre objects they name.

This is `CategoryTheory.IsHomLift.map`, and the only content is the spelling. The dictionary of
`StacksFrontier/CategoryTheory/TwoFibreProduct/TwoYonedaGraphs.lean` takes the base morphism as data
with a lifting hypothesis, and at the fppf site that hypothesis is wanted of a morphism whose
type is read through `AlgebraicGeometry.Stack.fibreObj`; `CategoryTheory.Functor.Fiber` is a plain
`def`, so instance search — which unfolds neither it nor `CategoryTheory.Functor.Fiber.mk` — does
not see `CategoryTheory.IsHomLift.map` as an answer to that question. Restating it once at the
spelling that occurs is what lets every statement below elaborate. -/
instance isHomLift_map_fibreObj (a : x ⟶ x') :
    𝒳.val.val.p.IsHomLift (𝒳.val.val.p.map a)
      (show (fibreObj B S hS 𝒳.val x).1 ⟶ (fibreObj B S hS 𝒳.val x').1 from a) :=
  IsHomLift.map 𝒳.val.val.p a

/-- **The graph of a morphism `a : x ⟶ x'` of the fppf site, as a based functor** from the slice
at the scheme `x` lies over into the 2-fibre product of the two 2-Yoneda 1-morphisms. This is
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.graphFunctor` at the structure functor of
`𝒳`, with `p(a)` as the base morphism `a` lies over. -/
def graphBasedFunctor (a : x ⟶ x') :
    (schemeFibredCategory B S hS (𝒳.val.val.p.obj x)).val ⥤ᵇ
      (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 x)
        (objectMorphismAlgebraicStacks B S hS 𝒳 x')).val.val where
  toFunctor :=
    TwoFibreProductOver.TwoYonedaGraph.graphFunctor 𝒳.val.isFiberedInGroupoids
      (fibreObj B S hS 𝒳.val x) (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map a) a
  w := TwoFibreProductOver.TwoYonedaGraph.graphFunctor_comp_structureFunctor ..

/-- **The graph of a morphism of the fppf site, as a 1-morphism of algebraic stacks**
`U ⟶ U ×_{x, 𝒳, x'} U'`. The 1-morphisms of the 2-category of algebraic stacks are those of the
ambient 2-category of categories fibred in groupoids, which in turn are the based functors, so no
condition has to be checked. -/
def graphAlgebraicStacks (a : x ⟶ x') :
    sliceAlgebraicStack B S hS 𝒳 x ⟶
      twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 x)
        (objectMorphismAlgebraicStacks B S hS 𝒳 x') :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (graphBasedFunctor B S hS 𝒳 a))

/-- **The 2-fibre product `U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` of the two graphs of a parallel
pair of morphisms of the fppf site**, as an algebraic stack over `S`. This is the object the
source of Stacks 0GN4 covers by an affine scheme in order to discharge condition (4). -/
abbrev equalizerTwoFibreProduct (a b : x ⟶ x') : AlgebraicStacks.{u, w} B S hS :=
  twoFibreProductAlgebraicStack B S hS (graphAlgebraicStacks B S hS 𝒳 a)
    (graphAlgebraicStacks B S hS 𝒳 b)

/-- The objects of the 2-fibre product of the two graphs: the type
`CategoryTheory.TwoFibreProductOver.twoYonedaGraph` the dictionary is stated for. -/
abbrev equalizerObjects (a b : x ⟶ x') : Type (u + 1) :=
  TwoFibreProductOver.twoYonedaGraph 𝒳.val.isFiberedInGroupoids (fibreObj B S hS 𝒳.val x)
    (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map a) a (𝒳.val.val.p.map b) b

/-- **The total category of the 2-fibre product of the two graphs is the type the dictionary is
stated for.** Nothing is transported: the 2-fibre product of algebraic stacks has the 2-fibre
product of categories over the site as its total category, and the underlying functor of
`AlgebraicGeometry.Stack.graphAlgebraicStacks` is
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.graphFunctor`. -/
theorem obj_equalizerTwoFibreProduct (a b : x ⟶ x') :
    (equalizerTwoFibreProduct B S hS 𝒳 a b).val.val.obj = equalizerObjects B S hS 𝒳 a b :=
  rfl

variable (a b : x ⟶ x')

/-- The object of the fppf site an object of the 2-fibre product of the two graphs classifies. -/
abbrev equalizerObj (P : equalizerObjects B S hS 𝒳 a b) : 𝒳.val.val.obj :=
  TwoFibreProductOver.TwoYonedaGraph.objOf 𝒳.val.isFiberedInGroupoids (fibreObj B S hS 𝒳.val x)
    (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map a) a (𝒳.val.val.p.map b) b P

/-- The equalizing morphism of the fppf site an object of the 2-fibre product of the two graphs
classifies. -/
abbrev equalizerHom (P : equalizerObjects B S hS 𝒳 a b) : equalizerObj B S hS 𝒳 a b P ⟶ x :=
  TwoFibreProductOver.TwoYonedaGraph.fstHom 𝒳.val.isFiberedInGroupoids (fibreObj B S hS 𝒳.val x)
    (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map a) a (𝒳.val.val.p.map b) b P

/-- The morphism of the fppf site a morphism of the 2-fibre product of the two graphs induces
between the objects its source and target classify. -/
abbrev equalizerMap {P P' : equalizerObjects B S hS 𝒳 a b} (ψ : P ⟶ P') :
    equalizerObj B S hS 𝒳 a b P ⟶ equalizerObj B S hS 𝒳 a b P' :=
  TwoFibreProductOver.TwoYonedaGraph.map 𝒳.val.isFiberedInGroupoids (fibreObj B S hS 𝒳.val x)
    (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map a) a (𝒳.val.val.p.map b) b ψ

/-- **The object of the fppf site an object of the 2-fibre product of the two graphs classifies
lies over the base object of that object.** The object is the chosen pullback of `x` along the
first component, so it lies over the source of that component, which is the base object. -/
theorem obj_equalizerObj (P : equalizerObjects B S hS 𝒳 a b) :
    𝒳.val.val.p.obj (equalizerObj B S hS 𝒳 a b P) = P.base :=
  (Functor.congr_obj (twoYonedaLiftFunctor_comp_p B S hS 𝒳.val x) P.x).trans P.hx

/-- **The morphism an object of the 2-fibre product of the two graphs classifies equalizes `a`
and `b`.** This is
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.fstHom_comp_eq` at the fppf site. -/
theorem equalizerHom_comp_eq (P : equalizerObjects B S hS 𝒳 a b) :
    equalizerHom B S hS 𝒳 a b P ≫ a = equalizerHom B S hS 𝒳 a b P ≫ b :=
  TwoFibreProductOver.TwoYonedaGraph.fstHom_comp_eq 𝒳.val.isFiberedInGroupoids
    (fibreObj B S hS 𝒳.val x) (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map a) a
    (𝒳.val.val.p.map b) b P

/-- **A morphism of the 2-fibre product of the two graphs carries the classified morphism of its
source to the classified morphism of its target.** This is
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.map_comp_fstHom` at the fppf site. -/
theorem equalizerMap_comp_equalizerHom {P P' : equalizerObjects B S hS 𝒳 a b} (ψ : P ⟶ P') :
    equalizerMap B S hS 𝒳 a b ψ ≫ equalizerHom B S hS 𝒳 a b P' =
      equalizerHom B S hS 𝒳 a b P :=
  TwoFibreProductOver.TwoYonedaGraph.map_comp_fstHom 𝒳.val.isFiberedInGroupoids
    (fibreObj B S hS 𝒳.val x) (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map a) a
    (𝒳.val.val.p.map b) b ψ

/-- **A morphism of the 2-fibre product of the two graphs and the morphism of the fppf site it
induces lie over the same morphism of the big fppf category over `S`.**

The first projection of a 2-fibre product is strictly over the base, so the first component of a
morphism lying over `k` lies over `k` in the slice; and the 2-Yoneda functor of `x` is strictly
over the base, so it carries that lift to a lift of `k` in the fppf site. Both steps are
`CategoryTheory.Functor.isHomLift_map_of_comp_eq`, exactly as in
`AlgebraicGeometry.Stack.isHomLift_quadMap`. -/
theorem isHomLift_equalizerMap {P P' : equalizerObjects B S hS 𝒳 a b} (ψ : P ⟶ P')
    {T T' : BigFppfOver B S hS} (k : T ⟶ T')
    (h : (TwoFibreProductOver.structureFunctor (Over.forget (𝒳.val.val.p.obj x))
      (Over.forget (𝒳.val.val.p.obj x))
      (TwoFibreProductOver.structureFunctor (Over.forget (𝒳.val.val.p.obj x))
        (Over.forget (𝒳.val.val.p.obj x')) 𝒳.val.val.p
        (Functor.TwoYoneda.liftFunctor 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          (𝒳.val.val.p.obj x) (fibreObj B S hS 𝒳.val x))
        (Functor.TwoYoneda.liftFunctor 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          (𝒳.val.val.p.obj x') (fibreObj B S hS 𝒳.val x')))
      (TwoFibreProductOver.TwoYonedaGraph.graphFunctor 𝒳.val.isFiberedInGroupoids
        (fibreObj B S hS 𝒳.val x) (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map a) a)
      (TwoFibreProductOver.TwoYonedaGraph.graphFunctor 𝒳.val.isFiberedInGroupoids
        (fibreObj B S hS 𝒳.val x) (fibreObj B S hS 𝒳.val x')
        (𝒳.val.val.p.map b) b)).IsHomLift k ψ) :
    𝒳.val.val.p.IsHomLift k (equalizerMap B S hS 𝒳 a b ψ) := by
  have := h
  have hfst : (Over.forget (𝒳.val.val.p.obj x)).IsHomLift k ψ.a :=
    Functor.isHomLift_map_of_comp_eq
      (TwoFibreProductOver.fst_comp_eq (p𝒳 := Over.forget (𝒳.val.val.p.obj x))
        (p𝒴 := Over.forget (𝒳.val.val.p.obj x))
        (p𝒮 := TwoFibreProductOver.structureFunctor (Over.forget (𝒳.val.val.p.obj x))
          (Over.forget (𝒳.val.val.p.obj x')) 𝒳.val.val.p
          (Functor.TwoYoneda.liftFunctor 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
            (𝒳.val.val.p.obj x) (fibreObj B S hS 𝒳.val x))
          (Functor.TwoYoneda.liftFunctor 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
            (𝒳.val.val.p.obj x') (fibreObj B S hS 𝒳.val x')))
        (F := TwoFibreProductOver.TwoYonedaGraph.graphFunctor 𝒳.val.isFiberedInGroupoids
          (fibreObj B S hS 𝒳.val x) (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map a) a)
        (G := TwoFibreProductOver.TwoYonedaGraph.graphFunctor 𝒳.val.isFiberedInGroupoids
          (fibreObj B S hS 𝒳.val x) (fibreObj B S hS 𝒳.val x') (𝒳.val.val.p.map b) b)) k ψ
  have := hfst
  exact Functor.isHomLift_map_of_comp_eq (twoYonedaLiftFunctor_comp_p B S hS 𝒳.val x) k ψ.a

end Graph

section AffineEqualizer

variable {x x' : 𝒳.val.val.obj} (a b : x ⟶ x')

/-- **The 2-fibre product of the two graphs of a parallel pair of morphisms between objects lying
over affine schemes is a quasi-compact algebraic stack**, for an algebraic stack quasi-separated
over a quasi-separated base scheme.

This is **Stacks 075S** part (3) at the two graphs, and it asks nothing of the two 1-morphisms:
their common source is the slice at an affine object, which is
`AlgebraicGeometry.Stack.schemeStack` there on the nose, hence quasi-compact by
`AlgebraicGeometry.Stack.isQuasiCompactStack_schemeStack_of_isAffine` and quasi-separated over `S`
by `AlgebraicGeometry.Stack.isQuasiSeparatedOver_schemeStack_of_isAffine`; and their common target
is quasi-separated over `S` by
`AlgebraicGeometry.Stack.isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism`.

That last input is the one condition (4) needs and condition (3) does not, and it is where
quasi-separatedness of `𝒳` enters the proof of condition (4) — a step the source does not
record. -/
theorem isQuasiCompactStack_equalizerTwoFibreProduct (hqsS : QuasiSeparatedSpace S)
    (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    (hx : IsAffineObject B S hS 𝒳.val.val.p x)
    (hx' : IsAffineObject B S hS 𝒳.val.val.p x') :
    IsQuasiCompactStack.{u, w} B S hS (equalizerTwoFibreProduct B S hS 𝒳 a b).val
      (equalizerTwoFibreProduct B S hS 𝒳 a b).property :=
  (isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct.{u, w} B S hS hqsS
    (graphAlgebraicStacks B S hS 𝒳 a) (graphAlgebraicStacks B S hS 𝒳 b)
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj x) hx)
    (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj x) hx)
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj x) hx)
    (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj x) hx)
    (isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism.{u, w} B S hS 𝒳 hqsS h𝒳
      hx hx')).1

/-- **A quasi-compact 2-fibre product of the two graphs has an object over an affine scheme which
dominates every object after a covering taken downstairs, in any topology in which a surjective
smooth 1-morphism admits fibre lifts.**

This is the exact analogue for condition (4) of
`AlgebraicGeometry.Stack.exists_quadruple_dominating_associatedTopology`, and is produced the same
way. **Stacks 04YC** parts (1) and (2) turn quasi-compactness into an affine object `U₀` and a
surjective, relatively smooth 1-morphism `f` from the slice `(Sch/S)/U₀` onto the 2-fibre product;
the dominating object is `Q = f(1_{U₀})`, which lies over `U₀` because `f` is a based functor.
Relative smoothness is upgraded to smoothness in the sense of **Stacks 075U** by
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty`, and the hypothesis
then covers the base object of any object `P` by objects over each of which `P` receives a morphism
from `f(ξ)` for an object `ξ` of the slice; `f(ξ)` is the dominating object over that member of the
covering, and its morphism to `Q` is the image under `f` of the structure morphism `ξ ⟶ 1_{U₀}`.

The only step that reads the chosen topology is the fibre-lifting hypothesis applied to `f`: the
fppf statement `AlgebraicGeometry.Stack.exists_graph_dominating` is this at
`AlgebraicGeometry.BigFppfSite.topology`, where **Stacks 06QA** discharges it from the flatness and
local finite presentation that smoothness supplies, and the étale one is its value at
`AlgebraicGeometry.etaleTopology`, where **Stacks 06XH** part (2) discharges it from surjectivity
and smoothness alone.

Two identifications make the passage free of transport, and neither mentions a topology: the total
category of the 2-fibre product is `CategoryTheory.TwoFibreProductOver.twoYonedaGraph` on the nose
by `AlgebraicGeometry.Stack.obj_equalizerTwoFibreProduct`, and the object of the site an object of
it classifies lies over the base object of that object by
`AlgebraicGeometry.Stack.obj_equalizerObj`. -/
theorem exists_graph_dominating_associatedTopology (τ : GrothendieckTopology B.Schemes)
    (hqc : IsQuasiCompactStack.{u, w} B S hS (equalizerTwoFibreProduct B S hS 𝒳 a b).val
      (equalizerTwoFibreProduct B S hS 𝒳 a b).property)
    (h_lift : ∀ (𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒲),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (z : 𝒲.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (c : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj c ⟶ z.1),
              𝒲.val.val.p.IsHomLift k α) :
    ∃ Q : equalizerObjects B S hS 𝒳 a b,
      IsAffineObject B S hS 𝒳.val.val.p (equalizerObj B S hS 𝒳 a b Q) ∧
        ∀ P : equalizerObjects B S hS 𝒳 a b,
          ∃ R ∈ τ.over (B.obj hS) P.base,
            ∀ ⦃T : BigFppfOver B S hS⦄ ⦃k : T ⟶ P.base⦄, R.arrows k →
              ∃ (P' : equalizerObjects B S hS 𝒳 a b) (ψ : P' ⟶ P) (_ : P' ⟶ Q),
                𝒳.val.val.p.IsHomLift k (equalizerMap B S hS 𝒳 a b ψ) := by
  classical
  set ℰ := equalizerTwoFibreProduct B S hS 𝒳 a b with hℰ
  obtain ⟨U₀, hU₀, f, hsurj, hsmooth⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS ℰ).1 hqc
  obtain ⟨hfrep, hrel⟩ := hsmooth
  have hsm : AlgebraicStacks.IsSmooth B S hS f :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) ℰ.property f.hom hfrep hrel
  set F := CatFiberedInGroupoids.homFunctor f.hom with hF
  have hw : F ⋙ ℰ.val.val.p = (schemeFibredCategory B S hS U₀).val.p := f.hom.hom.w
  refine ⟨F.obj (Over.mk (𝟙 U₀)), ?_, ?_⟩
  · have hproj : 𝒳.val.val.p.obj (equalizerObj B S hS 𝒳 a b (F.obj (Over.mk (𝟙 U₀)))) = U₀ :=
      (obj_equalizerObj B S hS 𝒳 a b (F.obj (Over.mk (𝟙 U₀)))).trans
        (Functor.congr_obj hw (Over.mk (𝟙 U₀)))
    change IsAffine ((BigFppfOver.toScheme B S hS).obj
      (𝒳.val.val.p.obj (equalizerObj B S hS 𝒳 a b (F.obj (Over.mk (𝟙 U₀))))))
    rw [hproj]
    exact hU₀
  · intro P
    obtain ⟨R, hR, hlift⟩ := h_lift _ ℰ f hsurj hsm P.base (Functor.Fiber.mk (a := P) rfl)
    refine ⟨R, hR, ?_⟩
    intro T k hk
    obtain ⟨ξ, φ, hφ⟩ := hlift hk
    exact ⟨F.obj ξ, φ, F.map (Over.homMk ξ.hom (Category.comp_id ξ.hom)),
      isHomLift_equalizerMap B S hS 𝒳 a b φ k hφ⟩

/-- **A quasi-compact 2-fibre product of the two graphs has an object over an affine scheme which
dominates every object after an fppf covering taken downstairs.**

This is `AlgebraicGeometry.Stack.exists_graph_dominating_associatedTopology` at the big fppf
topology of `B`, its fibre-lifting hypothesis discharged by **Stacks 06QA**,
`AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift`: the affine smooth presentation of
**Stacks 04YC** is surjective and smooth, and smoothness supplies the flatness and local finite
presentation that tag asks for, by `AlgebraicGeometry.AlgebraicStacks.isFlat_of_isSmooth` and
`AlgebraicGeometry.AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth`. -/
theorem exists_graph_dominating
    (hqc : IsQuasiCompactStack.{u, w} B S hS (equalizerTwoFibreProduct B S hS 𝒳 a b).val
      (equalizerTwoFibreProduct B S hS 𝒳 a b).property) :
    ∃ Q : equalizerObjects B S hS 𝒳 a b,
      IsAffineObject B S hS 𝒳.val.val.p (equalizerObj B S hS 𝒳 a b Q) ∧
        ∀ P : equalizerObjects B S hS 𝒳 a b,
          ∃ R ∈ BigFppfOver.topology B S hS P.base,
            ∀ ⦃T : BigFppfOver B S hS⦄ ⦃k : T ⟶ P.base⦄, R.arrows k →
              ∃ (P' : equalizerObjects B S hS 𝒳 a b) (ψ : P' ⟶ P) (_ : P' ⟶ Q),
                𝒳.val.val.p.IsHomLift k (equalizerMap B S hS 𝒳 a b ψ) :=
  exists_graph_dominating_associatedTopology.{u, w} B S hS 𝒳 a b B.topology hqc
    fun _ _ f hsurj hsm => exists_fppfCovering_fibre_lift B S hS f hsurj
      (AlgebraicStacks.isFlat_of_isSmooth B S hS f hsm)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS f hsm)

end AffineEqualizer

section Condition

variable (hqsS : QuasiSeparatedSpace S) (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)

include hqsS h𝒳

/-- **The geometric statement condition (4) of Stacks 0GN4 was reduced to**, for an algebraic stack
quasi-separated over a quasi-separated base scheme and any topology of Stacks 06TP in which a
surjective smooth 1-morphism admits fibre lifts: for two objects `x`, `x'` of the site lying over
affine schemes and two morphisms `a, b : x ⟶ x'`, there is an object `V` lying over an affine
scheme together with a morphism `p_V : V ⟶ x` satisfying `p_V ≫ a = p_V ≫ b`, such that every
morphism `α : y ⟶ x` of the site with `α ≫ a = α ≫ b` carries a covering sieve of the scheme `y`
lies over, over each member `k` of which there are `g : w ⟶ y` lying over `k` and `r : w ⟶ V` with
`r ≫ p_V = g ≫ α`.

This is the hypothesis `h_affine_dominating` of
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_of_exists_affine_dominating`, and
with it condition (4) is proved — at the fppf topology with the fibre-lifting hypothesis discharged
by **Stacks 06QA**, and at the étale topology by **Stacks 06XH** part (2).

Quasi-separatedness enters only through
`AlgebraicGeometry.Stack.isQuasiCompactStack_equalizerTwoFibreProduct`, which mentions no topology.

`V` is the object of the site the dominating object of
`AlgebraicGeometry.Stack.exists_graph_dominating_associatedTopology` classifies, and `p_V` the
equalizing morphism it classifies. For an equalizing `α : y ⟶ x`, the dictionary
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.exists_objOf_of_equalizing_hom` produces an
object `P` of the 2-fibre product classifying `α` over the scheme `y` lies over, together with a
vertical identification `e` of `y` with the object `P` classifies; the covering the dominating
object carries at `P` is the covering sought, and over each of its members `k` the dominating
datum gives `ψ : P' ⟶ P` and `χ : P' ⟶ Q`, whence `g` is the morphism `ψ` induces followed by
`e⁻¹` — lying over `k` because the morphism `ψ` induces does, by
`AlgebraicGeometry.Stack.isHomLift_equalizerMap`, and `e⁻¹` is vertical — and `r` the morphism
`χ` induces. -/
theorem exists_affine_dominating (τ : GrothendieckTopology B.Schemes)
    (h_lift : ∀ (𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒲),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (z : 𝒲.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (c : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj c ⟶ z.1),
              𝒲.val.val.p.IsHomLift k α) :
    ∀ {x x' : 𝒳.val.val.obj} (a b : x ⟶ x'),
      x ∈ affineObjects B S hS 𝒳.val → x' ∈ affineObjects B S hS 𝒳.val →
      ∃ (V : 𝒳.val.val.obj) (pV : V ⟶ x), V ∈ affineObjects B S hS 𝒳.val ∧
        pV ≫ a = pV ≫ b ∧
        ∀ (y : 𝒳.val.val.obj) (α : y ⟶ x), α ≫ a = α ≫ b →
          ∃ R ∈ τ.over (B.obj hS) (𝒳.val.val.p.obj y),
            ∀ ⦃T : BigFppfOver B S hS⦄ ⦃k : T ⟶ 𝒳.val.val.p.obj y⦄, R.arrows k →
              ∃ (w : 𝒳.val.val.obj) (g : w ⟶ y) (r : w ⟶ V),
                𝒳.val.val.p.IsHomLift k g ∧ r ≫ pV = g ≫ α := by
  intro x x' a b hx hx'
  obtain ⟨Q, hQaff, hQ⟩ := exists_graph_dominating_associatedTopology B S hS 𝒳 a b τ
    (isQuasiCompactStack_equalizerTwoFibreProduct B S hS 𝒳 a b hqsS h𝒳 hx hx') h_lift
  refine ⟨equalizerObj B S hS 𝒳 a b Q, equalizerHom B S hS 𝒳 a b Q, hQaff,
    equalizerHom_comp_eq B S hS 𝒳 a b Q, ?_⟩
  intro y α hα
  obtain ⟨P, e, hbase, hvert, hfac⟩ :=
    TwoFibreProductOver.TwoYonedaGraph.exists_objOf_of_equalizing_hom
      𝒳.val.isFiberedInGroupoids (fibreObj B S hS 𝒳.val x) (fibreObj B S hS 𝒳.val x')
      (𝒳.val.val.p.map a) a (𝒳.val.val.p.map b) b α hα
  rw [← hbase] at hvert ⊢
  obtain ⟨R, hR, hlift⟩ := hQ P
  refine ⟨R, hR, ?_⟩
  intro T k hk
  obtain ⟨P', ψ, χ, hψ⟩ := hlift hk
  have := hvert
  have := hψ
  have h4 : e.inv ≫ α = equalizerHom B S hS 𝒳 a b P := (Iso.inv_comp_eq e).2 hfac.symm
  exact ⟨equalizerObj B S hS 𝒳 a b P', equalizerMap B S hS 𝒳 a b ψ ≫ e.inv,
    equalizerMap B S hS 𝒳 a b χ, inferInstance, by
      rw [equalizerMap_comp_equalizerHom, Category.assoc, h4, equalizerMap_comp_equalizerHom]⟩

/-- **Condition (4) of Stacks 0GN4 at an arbitrary topology of Stacks 06TP in which a surjective
smooth 1-morphism admits fibre lifts**, for an algebraic stack quasi-separated over a
quasi-separated base scheme: for two objects `x`, `x'` of the site lying over affine schemes and
two morphisms `a, b : x ⟶ x'` there is a finite family of objects lying over affine schemes, each
with a morphism to `x` equalizing `a` and `b`, whose sheafified representables jointly cover the
equalizer of `h_a^#` and `h_b^#`.

The family has one member, as in the source: the object the dominating object of
`AlgebraicGeometry.Stack.exists_graph_dominating_associatedTopology` classifies, with the
equalizing morphism it classifies. This is
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_of_dominating_of_topology` with its
hypothesis discharged by `AlgebraicGeometry.Stack.exists_affine_dominating`.

The fppf statement
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift` is its value
at `AlgebraicGeometry.BigFppfSite.topology`, and the étale one
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale` its
value at `AlgebraicGeometry.etaleTopology`. -/
theorem exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology
    (τ : GrothendieckTopology B.Schemes)
    (h_lift : ∀ (𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒲),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (z : 𝒲.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (c : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj c ⟶ z.1),
              𝒲.val.val.p.IsHomLift k α) :
    ∀ {x x' : 𝒳.val.val.obj} (a b : x ⟶ x'),
      x ∈ affineObjects B S hS 𝒳.val → x' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ x) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p τ)).map a)
              (g := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p τ)).map b)
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p τ)).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda
                    (associatedTopology B S hS 𝒳.val.val.p τ)).map (hp i))) :=
  exists_fin_affineObjects_isLocallySurjective_equalizerLift_of_dominating_of_topology.{u, w}
    B S hS 𝒳 τ (exists_affine_dominating.{u, w} B S hS 𝒳 hqsS h𝒳 τ h_lift)

/-- **Condition (4) of Stacks 0GN4 for the fppf site of an algebraic stack quasi-separated over a
quasi-separated base scheme**, in the shape
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf` consumes as its
hypothesis `h_equalizer`: for two objects `x`, `x'` of the site lying over affine schemes and two
morphisms `a, b : x ⟶ x'` there is a finite family of objects lying over affine schemes, each with
a morphism to `x` equalizing `a` and `b`, whose sheafified representables jointly cover the
equalizer of `h_a^#` and `h_b^#`.

The family has one member, as in the source: the object the dominating object of
`AlgebraicGeometry.Stack.exists_graph_dominating` classifies, with the equalizing morphism it
classifies. This is
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology` at the big fppf
topology of `B`, its fibre-lifting hypothesis discharged by **Stacks 06QA**,
`AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift`. -/
@[stacks 0GN4 "condition (4) for the fppf site of an algebraic stack quasi-separated over a \
quasi-separated base scheme, with the collection B of Stacks 0GQV: the objects of the site lying \
over affine schemes; the family produced has one member, as in the source"]
theorem exists_fin_affineObjects_isLocallySurjective_equalizerLift :
    ∀ {x x' : 𝒳.val.val.obj} (a b : x ⟶ x'),
      x ∈ affineObjects B S hS 𝒳.val → x' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ x) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map a)
              (g := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map b)
              ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (hp i))) :=
  exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology.{u, w}
    B S hS 𝒳 hqsS h𝒳 B.topology
    fun _ _ f hsurj hsm => exists_fppfCovering_fibre_lift B S hS f hsurj
      (AlgebraicStacks.isFlat_of_isSmooth B S hS f hsm)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS f hsm)

/-- **Stacks 0GQV in the fppf topology for a quasi-compact algebraic stack which is quasi-separated
over a quasi-separated base scheme.** Let `𝒳` be such a stack and give its total category the fppf
topology of Stacks 06TP. Then `colim_i H^p(𝒳, F_i) ⟶ H^p(𝒳, colim_i F_i)` is an isomorphism in
every degree `p`, for every filtered diagram `F` of abelian fppf sheaves on `𝒳`.

All four conditions of Stacks 0GN4 are discharged: (1) from quasi-compactness by
`AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from`, (2) for every
category fibred in groupoids by
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_fppfTopology`, (3) by
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift` and (4) by
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift` above.

The quasi-separatedness hypothesis is `AlgebraicGeometry.Stack.IsQuasiSeparatedOver` of `𝒳`
together with quasi-separatedness of the base scheme `S`, which is what Stacks 075S asks for and
what conditions (3) and (4) use. -/
@[stacks 0GQV "the first assertion, in the fppf topology, for a quasi-compact algebraic stack \
quasi-separated over a quasi-separated base scheme; all four conditions of 0GN4 proved"]
theorem isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (fppfTopology B S hS 𝒳.val) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (fppfTopology B S hS 𝒳.val) Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiSeparatedOver.{u, w}
    B S hS 𝒳 hqsS hqc h𝒳
    (exists_fin_affineObjects_isLocallySurjective_equalizerLift.{u, w} B S hS 𝒳 hqsS h𝒳)
    p F

end Condition

end AlgebraicGeometry.Stack

end
