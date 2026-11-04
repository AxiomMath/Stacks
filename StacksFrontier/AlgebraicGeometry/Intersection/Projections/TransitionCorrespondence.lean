module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTwist
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionLocus
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TripleTautologicalGerm

/-!
# The incidence correspondence of Tag 0B1S as a scheme

Tag 0B1S studies, for closed subvarieties `X, Y` of `𝐏(V)`, the classes `[g]` of the parameter
space `𝐏 = 𝐏((End V)ᵛ)` at which the projective transformation `r_g` carries `X` to a subvariety
meeting `Y` improperly. The source gets the bad locus from the *incidence correspondence*

`T = {(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}`,

a subscheme of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏`. This file builds it.

A closed point of `𝐏(V)` is the class `[f]` of a nonzero functional on `V` and `r_g([f]) = [f ∘
g]`, so the condition `r_g(x) = y` on representatives `f, f', g` is that `f ∘ g` and `f'` be
proportional, that is that the `2 × 2` minors

`f (g v) · f' w - f (g w) · f' v`

of the pair of rows `(f ∘ g, f')` all vanish. Each minor is a global section of

`𝒪(1,1,1) = tpSource^* 𝒪(1) ⊗ tpTarget^* 𝒪(1) ⊗ tpPar^* 𝒪_𝐏(1)`,

being linear in `f`, in `f'` and in `g` separately. It is not a *tensor* of three tautological
sections but a finite sum of such: `f (g v)` is bilinear in `(f, g)` rather than linear in a
single coordinate, and expanding `g v` in a basis writes it as `∑ i, f (bᵢ) · φᵢ,ᵥ g` with
`φᵢ,ᵥ ∈ (End V)ᵛ` the functional `g ↦ (g v)ᵢ`. That expansion is
`AlgebraicGeometry.ProjectiveSpaceOfModule.paramCoord`, and the sum is
`AlgebraicGeometry.ProjectiveSpaceOfModule.minorSection`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionProd`: the product
  `𝐏(V) ×_k 𝐏(V) ×_k 𝐏`, formed as `(𝐏(V) ×_k 𝐏(V)) ×_k 𝐏` so that the projection to the first
  two factors is a single `pullback.fst`, with its projections
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tpFst`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tpSource`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tpTarget` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tpPar`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionTwistModule`: `𝒪(1,1,1)` on that product,
  with `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionTensorSection` the tensor of three
  tautological sections.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.paramCoord`: the functional on `End V` reading off
  one coordinate of `g v`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.minorSection`: the `2 × 2` minor attached to a pair
  of vectors of `V`, a section of `𝒪(1,1,1)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionLocus`: the common zero locus of those
  minors, and `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubscheme` the closed
  subscheme it carries, with
  `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionProj` its projection to `𝐏(V) ×_k 𝐏(V)`
  and `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionProjPar` its projection to `𝐏`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionVariety`: the base change of that
  projection along a morphism `S ⟶ 𝐏(V) ×_k 𝐏(V)`. The base Tag 0B1S needs is a product of two
  closed subschemes, `AlgebraicGeometry.ProjectiveSpaceOfModule.prodOfClosedToProdTwo`; unlike
  Tag 0B1R's incidence variety of lines this correspondence needs **no** restriction of the base
  away from the diagonal, see the implementation notes.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.apply_eq_sum_paramCoord`: the expansion
  `f (g v) = ∑ i, f (bᵢ) * paramCoord i v g` that makes the minor a sum of tensors.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_span_singleton_iff_forall_minor_eq_zero`: the
  minors cut out exactly the condition `f ∘ g ∈ k ∙ f'`, the degenerate case `f ∘ g = 0`
  included. This is why the equations are the right ones.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universallyOpen_tpFst`: the projection of the
  *ambient* product to `𝐏(V) ×_k 𝐏(V)` is universally open.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_transitionTensorSection_iff`:
  a tensor of three tautological sections is nonvanishing exactly where each of the three
  degree-one forms avoids the homogeneous prime of the corresponding projection, by the generic
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tripleTaut` calculus.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_transitionLocus` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.range_transitionSubschemeι`: the locus is closed and
  is the image of the subscheme.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_transitionProd`: the dimension
  of the product is the sum of the dimensions.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isPullback_transitionVariety`: the correspondence
  over a base is the fibre product of the subscheme with that base.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isOpenMap_transitionVarietyToBase_of_universallyOpen`
  carries openness of the projection from the full base `𝐏(V) ×_k 𝐏(V)` to any base over it,
  which is the step Tag 004Z consumes.

## Implementation notes

**Why no restriction of the base is needed.** Tag 0B1R's incidence variety of lines has to be
taken over the distinct-pairs base
`AlgebraicGeometry.ProjectiveSpaceOfModule.prodOfClosedOffSndToProdTwo`, because over a pair of
coinciding points every determinant section of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus` vanishes and the fibre
degenerates from a line to a whole copy of `𝐏(V)`: that is
`AlgebraicGeometry.ProjectiveSpaceOfModule.range_diagThree_subset_collinearLocus` of
`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Diagonal`. The correspondence built here
does **not** degenerate on the diagonal. Its fibre over a pair of closed points is the projective
linear subspace cut out by
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEquations` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionLocus`, whose corank is
`dim V - 1` by
`AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_transitionSubmodule` **whether or not
the two points agree** — the condition `f ∘ g ∈ k ∙ f'` is one linear condition per coordinate of
`f'` regardless. So the fibre is irreducible of dimension `(dim V)² - dim V` over every pair,
which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_linearSubspace_transitionEquations`
together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_linearSubspace_transitionEquations`.

**The product is left-nested.** `transitionProd` is `(𝐏(V) ×_k 𝐏(V)) ×_k 𝐏`, so `tpFst` is a
single `pullback.fst` and `AlgebraicGeometry.topologicalKrullDim_pullback` applies on the nose,
exactly as for `AlgebraicGeometry.ProjectiveSpaceOfModule.prodThree`. The third factor is the
projective space of a *different* module, `ParameterModule k V = (End V)ᵛ`, so the three
tautological pullbacks cannot share one instantiation; the generic-in-the-module pullback section
`AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTaut` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTwist` is reused rather than
redeclared.

**The minors are sums, and the sum is built by hand.** The type of global sections of a presheaf
of modules is a bare type with no additive structure attached, so
`AlgebraicGeometry.ProjectiveSpaceOfModule.minorSection` is assembled as a compatible family
through `PresheafOfModules.sectionsMk`, as
`AlgebraicGeometry.ProjectiveSpaceOfModule.detSection` is.

**What is still owed for Tag 0B1S.** This file provides the correspondence and the transfer of
openness along a base change. The two facts about it that Tag 0B1S's bad-locus analysis needs and
that are **not** proved here are:

* that the fibre of `transitionProj` over a pair of closed points is the projective linear
  subspace of `transitionEquations` — the chart computation of `minorSection` against a frame of
  `𝒪(1,1,1)`, the analogue for this correspondence of
  `AlgebraicGeometry.ProjectiveSpaceOfModule.divBySection_detSection` of
  `StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityFibre` together with the
  chart linearity of `StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.ChartLinear`;
* that `transitionProj` is universally open. It is: its fibres are the projectivisations of the
  subspaces `transitionSubmodule k V f f'`, which form a subbundle of constant corank `dim V - 1`
  of the trivial bundle `End V` on `𝐏(V) ×_k 𝐏(V)`, so the projection is a Zariski-locally
  trivial `𝐏^{(dim V)² - dim V}`-bundle, hence flat and of finite presentation, hence universally
  open by `AlgebraicGeometry.universallyOpen_of_flat_of_locallyOfFinitePresentation`. The local
  trivialisation is explicit — over the chart where `f bᵢ ≠ 0` and `f' bⱼ ≠ 0` the two families
  `a (f) : bᵢ ↦ bᵢ / f bᵢ`, `b_l ↦ b_l - (f b_l / f bᵢ) bᵢ` and `b (f') : x ↦ f' x · bⱼ + (x -
  xⱼ bⱼ)` of linear automorphisms of `V` satisfy `f ∘ a (f) = εᵢ` and `εⱼ ∘ b (f') = f'`, so
  `g ↦ a (f) ∘ g ∘ b (f')` carries the constant subspace `transitionSubmodule k V εᵢ εⱼ` onto
  `transitionSubmodule k V f f'` — but turning it into an isomorphism of schemes needs the action
  of `GL(V)` on `𝐏` in families, that is over a base, and
  `StacksFrontier.AlgebraicGeometry.Intersection.Projections.LinearAction` provides it only for a
  single element of `GL(V)` over `Spec k`.

Openness is genuinely needed and genuinely open: it must not be assumed by analogy with Tag
0B1R, where flatness and openness of the corresponding projection are **false** over a base
meeting the diagonal.

**Openness is needed for only one of the two routes to `IrreducibleSpace T`.** Parts (2b) and
(2c) of Tag 0B2L are the only consumers of that irreducibility, and there are two ways to reach
it. The route through Tag 004Z needs the universal openness above. The other route needs no
openness at all: exhibit the correspondence over `X × Y` as the closure of the image of a
*product* `X × Y × 𝔸(k × V × V × V × End V)`, under the map carrying a pair of points and a tuple
of parameters to the endomorphism
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionParametrisation`, whose values
fill out `transitionSubmodule k V f f'` exactly, for every pair of nonzero functionals, and which
is *bilinear* in `(f, f')`. The source of that map is irreducible because it is a product of
irreducibles over an algebraically closed field,
`AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_prodOfClosed` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionBase`, so the closure of the
image is irreducible, and the image contains every closed point of the correspondence. What that
route owes instead is the classifying morphism to `𝐏`: an `𝒪(1,1)` on a scheme over *two*
projective spaces — the library has the one-slot pullback section
`AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTautSection` and the three-slot package
`AlgebraicGeometry.ProjectiveSpaceOfModule.tripleTaut`, and not the two-slot one — together with
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections`, which
is basis free, lands in `projectiveSpaceOfModule` itself, and whose `Classifies` clause (1)
computes the preimage of every standard open, so that the value of the morphism at a closed point
is readable and the `φ^* 𝒪(1) ≅ ℒ` identification that Tag 01ND is registered without is not in
the way.

That two-slot twist is **not** written as a one-slot deletion of `tripleTaut`: a parallel copy of
the whole germ calculus would be exactly the duplication this file's triple layer was extracted to
avoid. It is
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.InertSlotTwist`, which keeps `tripleTaut`
and makes the third slot **inert** — `M₃` the ground field as a module over itself, `p₃` the
structure morphism followed by `AlgebraicGeometry.ProjectiveSpaceOfModule.onePoint`, the unique
point of `𝐏(k)`. The third tautological section at `1 : k` is then nonvanishing everywhere, so
`AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautSection` is bilinear and the third conjunct of
the nonvanishing criterion and the third ratio of the germ formula are discharged once and for
all. No identification of `𝐏(k)` with `Spec k` is needed, and the value of the inert slot at a
point is `AlgebraicGeometry.ProjectiveSpaceOfModule.pointOfDual_base`, which the library already
had.

The value of the classifying morphism at a point is in the library too, as
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections_base_eq`
of `StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsPointValue`: the image of `x` is
the point cut out by a nonzero functional `φ` as soon as `ψ(v)` vanishes at `x` for every `v` in
the kernel of `φ`. Nor is there a twist gap to route around in that API — the isomorphism
`φ^* 𝒪(1) ≅ ℒ` is
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.twistIsoOfGeneratingSections`, clause
(5) of Tag 0FCY — though locating the image of a point does not use it.

So what the classifying morphism `Φ` still owes is only the linear map `ψ` itself: for each
`φ ∈ (End V)ᵛ`, the coordinate `φ(G)` expanded in a basis as
`∑ i j, P i j • pairTautSection (bᵢ) (bⱼ)` with `P i j` a polynomial in the affine parameters
`(c, u, u', w, h)`, together with the bridge between the `.sections` spelling of a global section
that the tautological layer produces and the `Γ(ℒ, ⊤)` spelling that
`morphismOfGeneratingSections` consumes.

**What the correspondence is already known to satisfy.** Its projection to the parameter space is
proper over a base proper over the ground field, so the image of a closed subset of it is closed:
`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionProper`. That is the step the
source of Tag 0B1S asserts without proof. The translation of a jump in the fibre dimension into
badness of `g` is
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_topologicalKrullDim_fibre_le` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.ClauseTwoFibre`, and it holds for every
`g` whose domain of definition contains `X`, singular ones included.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 004Z](https://stacks.math.columbia.edu/tag/004Z)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The product `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` -/

/-- **The product `𝐏(V) ×_k 𝐏(V) ×_k 𝐏`** in which the incidence correspondence of Tag 0B1S
lives, formed as `(𝐏(V) ×_k 𝐏(V)) ×_k 𝐏` so that the projection to the first two factors is a
single `pullback.fst`. -/
public abbrev transitionProd : Scheme.{u} :=
  pullback (prodTwoToSpec k V) (projectiveSpaceOfModuleToSpec k (ParameterModule k V))

/-- The projection of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` to the product of the first two factors. -/
public def tpFst : transitionProd k V ⟶ prodTwo k V := pullback.fst _ _

/-- The projection to the source copy of `𝐏(V)`, the factor carrying the point `x`. -/
public def tpSource : transitionProd k V ⟶ projectiveSpaceOfModule k V :=
  tpFst k V ≫ pullback.fst _ _

/-- The projection to the target copy of `𝐏(V)`, the factor carrying the point `y`. -/
public def tpTarget : transitionProd k V ⟶ projectiveSpaceOfModule k V :=
  tpFst k V ≫ pullback.snd _ _

/-- The projection to the parameter space `𝐏 = 𝐏((End V)ᵛ)`, the factor carrying the class
`[g]`. -/
public def tpPar : transitionProd k V ⟶ projectiveSpaceOfModule k (ParameterModule k V) :=
  pullback.snd _ _

/-- The structure morphism of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` over `Spec k`. -/
public def transitionProdToSpec : transitionProd k V ⟶ Spec (.of k) :=
  tpPar k V ≫ projectiveSpaceOfModuleToSpec k (ParameterModule k V)

public instance locallyOfFiniteType_transitionProdToSpec [FiniteDimensional k V] [Nontrivial V]
    [Nontrivial (ParameterModule k V)] :
    LocallyOfFiniteType (transitionProdToSpec k V) := by
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) := by
    have := isProper_projectiveSpaceOfModuleToSpec k (ParameterModule k V)
    infer_instance
  rw [transitionProdToSpec, tpPar]
  infer_instance

/-- **The dimension of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏`** is the dimension of `𝐏(V) ×_k 𝐏(V)` plus that of
the parameter space. -/
public theorem topologicalKrullDim_transitionProd [FiniteDimensional k V] [Nontrivial V]
    [Nontrivial (ParameterModule k V)] :
    topologicalKrullDim (transitionProd k V) =
      topologicalKrullDim (prodTwo k V) +
        topologicalKrullDim (projectiveSpaceOfModule k (ParameterModule k V)) :=
  topologicalKrullDim_pullback k (prodTwoToSpec k V)
    (projectiveSpaceOfModuleToSpec k (ParameterModule k V))

/-- **The projection of the ambient product to the first two factors is universally open.** It
is the base change of `𝐏 ⟶ Spec k` along `𝐏(V) ×_k 𝐏(V) ⟶ Spec k`, and every morphism to the
spectrum of a field is universally open, so the *trivial* `𝐏`-bundle over `𝐏(V) ×_k 𝐏(V)` is
universally open over it.

`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionProj` is the restriction of this projection
to the closed subscheme `T`, and its openness does **not** follow from this: openness is not
inherited by the restriction to a closed subscheme. It is the subbundle fact recorded in the
implementation notes. -/
public instance universallyOpen_tpFst : UniversallyOpen (tpFst k V) := by
  have h : UniversallyOpen (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) :=
    inferInstance
  rw [tpFst]
  infer_instance

/-- The projection to the first two factors is a morphism over `Spec k`; this is the pullback
condition defining the product. -/
public theorem tpFst_comp_toSpec :
    tpFst k V ≫ prodTwoToSpec k V = transitionProdToSpec k V := pullback.condition

/-- The source projection is a morphism over `Spec k`. -/
public theorem tpSource_comp_toSpec :
    tpSource k V ≫ projectiveSpaceOfModuleToSpec k V = transitionProdToSpec k V := by
  rw [tpSource, transitionProdToSpec, Category.assoc,
    show (pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V) ≫ projectiveSpaceOfModuleToSpec k V) =
      prodTwoToSpec k V from rfl, tpFst, tpPar]
  exact pullback.condition

/-- The target projection is a morphism over `Spec k`. -/
public theorem tpTarget_comp_toSpec :
    tpTarget k V ≫ projectiveSpaceOfModuleToSpec k V = transitionProdToSpec k V := by
  rw [tpTarget, transitionProdToSpec, Category.assoc, ← pullback.condition,
    show (pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V) ≫ projectiveSpaceOfModuleToSpec k V) =
      prodTwoToSpec k V from rfl, tpFst, tpPar]
  exact pullback.condition

/-- The parameter projection is a morphism over `Spec k`. -/
public theorem tpPar_comp_toSpec :
    tpPar k V ≫ projectiveSpaceOfModuleToSpec k (ParameterModule k V) =
      transitionProdToSpec k V := rfl

/-! ### The invertible module `𝒪(1,1,1)` and its tensor sections -/

/-- The pullback `tpSource^* 𝒪(1)` of the tautological module of `𝐏(V)`. -/
public abbrev tpTautSource : (transitionProd k V).Modules :=
  (Scheme.Modules.pullback (tpSource k V)).obj (tautologicalModule k V)

/-- The pullback `tpTarget^* 𝒪(1)` of the tautological module of `𝐏(V)`. -/
public abbrev tpTautTarget : (transitionProd k V).Modules :=
  (Scheme.Modules.pullback (tpTarget k V)).obj (tautologicalModule k V)

/-- The pullback `tpPar^* 𝒪_𝐏(1)` of the tautological module of the parameter space. -/
public abbrev tpTautPar : (transitionProd k V).Modules :=
  (Scheme.Modules.pullback (tpPar k V)).obj (tautologicalModule k (ParameterModule k V))

/-- **The invertible module `𝒪(1,1,1)`** on `𝐏(V) ×_k 𝐏(V) ×_k 𝐏`: the generic
`AlgebraicGeometry.ProjectiveSpaceOfModule.tripleTaut` at the three projections, so the whole
germ calculus proved there applies to it. -/
public def transitionTwistModule : (transitionProd k V).Modules :=
  tripleTaut k V V (ParameterModule k V) (tpSource k V) (tpTarget k V) (tpPar k V)

/-- **`𝒪(1,1,1)` is invertible.** -/
public theorem isInvertible_transitionTwistModule :
    Stacks.SheafOfModules.IsInvertible (transitionProd k V).presheaf
      (structureSheafRing (transitionProd k V).toRingedSpace).property
      (transitionTwistModule k V) :=
  isInvertible_tripleTaut k V V (ParameterModule k V) (tpSource k V) (tpTarget k V) (tpPar k V)

/-- **The tensor `tpSource^*(ι a) ⊗ tpTarget^*(ι b) ⊗ tpPar^*(ι φ)` of three tautological
sections**, a global section of `𝒪(1,1,1)`. -/
public def transitionTensorSection (a b : V) (φ : ParameterModule k V) :
    (transitionTwistModule k V).sections :=
  tripleTautSection k V V (ParameterModule k V) (tpSource k V) (tpTarget k V) (tpPar k V) a b φ

/-- **A tensor of three tautological sections is nonvanishing at a point exactly when each of the
three degree-one forms avoids the homogeneous prime of the corresponding projection** of that
point. -/
public theorem mem_nonvanishingLocus_transitionTensorSection_iff (a b : V)
    (φ : ParameterModule k V) (t : transitionProd k V) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := (transitionProd k V).toRingedSpace)
        (transitionTwistModule k V) (transitionTensorSection k V a b φ) ↔
      SymmetricAlgebra.ι k V a ∉ ((tpSource k V).base t).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k V b ∉ ((tpTarget k V).base t).asHomogeneousIdeal ∧
          SymmetricAlgebra.ι k (ParameterModule k V) φ ∉
            ((tpPar k V).base t).asHomogeneousIdeal :=
  mem_nonvanishingLocus_tripleTautSection_iff k V V (ParameterModule k V) (tpSource k V)
    (tpTarget k V) (tpPar k V) a b φ t

/-! ### The `2 × 2` minors as sections of `𝒪(1,1,1)` -/

/-- **The functional on `End V` reading off a coordinate of `g v`**: the element `g ↦ c (g v)` of
`ParameterModule k V = (End V)ᵛ`. It is this functional, and not `c` or `v` separately, that is a
degree-one form on the parameter space. -/
public def paramCoord (c : Module.Dual k V) (v : V) : ParameterModule k V :=
  Module.Dual.eval k V v ∘ₗ dualPostcomp k V c

@[simp]
public theorem paramCoord_apply (c : Module.Dual k V) (v : V) (g : V →ₗ[k] V) :
    paramCoord k V c v g = c (g v) := rfl

/-- **The expansion that makes a `2 × 2` minor a finite sum of tensors of tautological
sections.** The entry `f (g v)` is bilinear in `(f, g)`, so it is not a single tensor; expanding
`g v` in a basis writes it as the sum over the basis of the degree-one form `f bᵢ` on the source
factor times the degree-one form `paramCoord (b.coord i) v` on the parameter factor. -/
public theorem apply_eq_sum_paramCoord {ι : Type*} [Fintype ι] (b : Module.Basis ι k V)
    (f : Module.Dual k V) (g : V →ₗ[k] V) (v : V) :
    f (g v) = ∑ i, paramCoord k V (b.coord i) v g * f (b i) := by
  conv_lhs => rw [← b.sum_repr (g v)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, paramCoord_apply, Module.Basis.coord_apply]

/-- A nonzero linear functional is nonzero at some vector. -/
private theorem exists_apply_ne_zero {M : Type*} [AddCommGroup M] [Module k M]
    {f : Module.Dual k M} (hf : f ≠ 0) : ∃ a, f a ≠ 0 := by
  simpa using DFunLike.ne_iff.mp hf

/-- **The minors cut out exactly the proportionality condition, the degenerate case included.**
For `f' ≠ 0`, the functional `f ∘ g` lies on the line spanned by `f'` exactly when every `2 × 2`
minor `f (g v) · f' w - f (g w) · f' v` vanishes. This is the linear-algebra content of
`AlgebraicGeometry.ProjectiveSpaceOfModule.minorSection`: it is why the equations written there
are the right ones.

The dictionary between vanishing minors and equality of the *points* cut out by two functionals
is already available, as
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearFunctionalPoint_eq_of_minors_eq` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.minors_eq_of_linearFunctionalPoint_eq` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProportional`. Both need
*both* functionals to be nonzero, so they say nothing at the classes where `f ∘ g = 0` — and
those are exactly the classes at which `[f]` leaves the domain of definition
`AlgebraicGeometry.ProjectiveSpaceOfModule.endDomain`, which the transition locus contains and
the graph of `r_g` does not. The span-membership form here covers them, and it is the form
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubmodule` is stated in, so it is what
identifies the fibre of `transitionProj` with
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEquations`. -/
public theorem mem_span_singleton_iff_forall_minor_eq_zero {f f' : Module.Dual k V}
    (hf' : f' ≠ 0) (g : V →ₗ[k] V) :
    f ∘ₗ g ∈ Submodule.span k {f'} ↔ ∀ v w : V, f (g v) * f' w - f (g w) * f' v = 0 := by
  refine ⟨fun hmem v w => ?_, fun hmin => ?_⟩
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have key (x : V) : f (g x) = c * f' x := by
      simpa using (LinearMap.congr_fun hc x).symm
    rw [key v, key w]
    ring
  · obtain ⟨w₀, hw₀⟩ := exists_apply_ne_zero k hf'
    refine Submodule.mem_span_singleton.mpr ⟨f (g w₀) / f' w₀, LinearMap.ext fun x => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, div_mul_eq_mul_div,
      div_eq_iff hw₀]
    linear_combination -(hmin x w₀)

/-- **The `2 × 2` minor of the pair of rows `(f ∘ g, f')` at a pair of vectors**, as a global
section of `𝒪(1,1,1)`: the antisymmetrisation `f (g v) · f' w - f (g w) · f' v`, written out
through `AlgebraicGeometry.ProjectiveSpaceOfModule.apply_eq_sum_paramCoord` as a sum of tensors
of three tautological sections. Its vanishing at a triple of closed points says that `f ∘ g` and
`f'` are proportional at the pair `(v, w)`, and the vanishing of all of them says that
`r_g` carries `[f]` to `[f']`. -/
public def minorSection [FiniteDimensional k V] (v w : V) :
    (transitionTwistModule k V).sections :=
  (transitionTwistModule k V).val.sectionsMk
    (fun U => ∑ i : Fin (Module.finrank k V),
      ((transitionTensorSection k V (Module.finBasis k V i) w
            (paramCoord k V ((Module.finBasis k V).coord i) v)).eval U -
        (transitionTensorSection k V (Module.finBasis k V i) v
            (paramCoord k V ((Module.finBasis k V).coord i) w)).eval U))
    (by
      intro U W f
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub, PresheafOfModules.sections_property, PresheafOfModules.sections_property]
      rfl)

/-- The minor section evaluates over an open to the signed sum of the evaluations of the tensors
of tautological sections. -/
public theorem minorSection_eval [FiniteDimensional k V] (v w : V)
    (U : (Opens ↥(transitionProd k V))ᵒᵖ) :
    (minorSection k V v w).eval U =
      ∑ i : Fin (Module.finrank k V),
        ((transitionTensorSection k V (Module.finBasis k V i) w
              (paramCoord k V ((Module.finBasis k V).coord i) v)).eval U -
          (transitionTensorSection k V (Module.finBasis k V i) v
              (paramCoord k V ((Module.finBasis k V).coord i) w)).eval U) :=
  rfl

/-- **The normalising scalars of the minor section sum to the `2 × 2` minor divided by the
product of the three reference values.** The hypothesis on `f₃` says that the functional cutting
out the parameter point is evaluation at the endomorphism `g`, which is what
`AlgebraicGeometry.ProjectiveSpaceOfModule.RepresentsParameterPoint` provides; under it the sum
over the basis of `V` contracts, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_eq_sum_paramCoord`, to the entries `f (g v)` and
`f (g w)` of the minor. -/
public theorem sum_ratio_eq_minor [FiniteDimensional k V] (f f' : Module.Dual k V)
    (f₃ : Module.Dual k (ParameterModule k V)) (g : V →ₗ[k] V)
    (hg : ∀ ψ : ParameterModule k V, f₃ ψ = ψ g)
    (a₀ : V) (ha₀ : f a₀ ≠ 0) (b₀ : V) (hb₀ : f' b₀ ≠ 0)
    (c₀ : ParameterModule k V) (_hc₀ : f₃ c₀ ≠ 0) (v w : V) :
    ∑ i : Fin (Module.finrank k V),
        (f (Module.finBasis k V i) / f a₀ * (f' w / f' b₀) *
            (f₃ (paramCoord k V ((Module.finBasis k V).coord i) v) / f₃ c₀) -
          f (Module.finBasis k V i) / f a₀ * (f' v / f' b₀) *
            (f₃ (paramCoord k V ((Module.finBasis k V).coord i) w) / f₃ c₀)) =
      (f' w * f (g v) - f' v * f (g w)) / (f a₀ * f' b₀ * f₃ c₀) := by
  have h (x : V) : f (g x) = ∑ i : Fin (Module.finrank k V),
      (Module.finBasis k V).coord i (g x) * f (Module.finBasis k V i) := by
    simpa using apply_eq_sum_paramCoord k V (Module.finBasis k V) f g x
  simp only [hg, paramCoord_apply]
  rw [h v, h w, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-! ### The transition locus and the incidence correspondence -/

/-- **The transition locus**: the set of points of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` at which every `2 × 2`
minor of the pair `(f ∘ g, f')` vanishes, that is at which the two rows are proportional. At a
triple of closed points this says exactly that `r_g` carries `[f]` to `[f']`. -/
public def transitionLocus [FiniteDimensional k V] : Set (transitionProd k V) :=
  ⋂ p : V × V, (Stacks.SheafOfModules.nonvanishingLocus
    (X := (transitionProd k V).toRingedSpace) (transitionTwistModule k V)
    (minorSection k V p.1 p.2))ᶜ

/-- A point of the triple product lies in the transition locus exactly when no minor section is
nonvanishing at it. -/
public theorem mem_transitionLocus_iff [FiniteDimensional k V] (t : transitionProd k V) :
    t ∈ transitionLocus k V ↔ ∀ p : V × V,
      t ∉ Stacks.SheafOfModules.nonvanishingLocus (X := (transitionProd k V).toRingedSpace)
        (transitionTwistModule k V) (minorSection k V p.1 p.2) :=
  Set.mem_iInter

/-- **The transition locus is closed**: the nonvanishing locus of a global section of an
invertible module is open, and the transition locus is the intersection of the complements. -/
public theorem isClosed_transitionLocus [FiniteDimensional k V] :
    IsClosed (transitionLocus k V) := by
  have hinv := isInvertible_transitionTwistModule k V
  exact isClosed_iInter fun p =>
    (Stacks.SheafOfModules.isOpen_nonvanishingLocus (transitionTwistModule k V)
      (minorSection k V p.1 p.2)).isClosed_compl

/-- The ideal sheaf of the transition locus, the vanishing ideal of that closed subset. -/
public def transitionIdeal [FiniteDimensional k V] : (transitionProd k V).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨transitionLocus k V, isClosed_transitionLocus k V⟩

/-- **The incidence correspondence `T` of Tag 0B1S as a closed subscheme** of
`𝐏(V) ×_k 𝐏(V) ×_k 𝐏`, with its reduced induced structure: the triples `(x, y, [g])` with
`r_g(x) = y`. -/
public def transitionSubscheme [FiniteDimensional k V] : Scheme.{u} :=
  (transitionIdeal k V).subscheme

/-- The inclusion of the incidence correspondence into the triple product. -/
public def transitionSubschemeι [FiniteDimensional k V] :
    transitionSubscheme k V ⟶ transitionProd k V := (transitionIdeal k V).subschemeι

/-- The incidence correspondence is a closed subscheme of the triple product. -/
public instance isClosedImmersion_transitionSubschemeι [FiniteDimensional k V] :
    IsClosedImmersion (transitionSubschemeι k V) :=
  inferInstanceAs (IsClosedImmersion (transitionIdeal k V).subschemeι)

/-- **The points of the incidence correspondence are exactly the points of the transition
locus.** -/
public theorem range_transitionSubschemeι [FiniteDimensional k V] :
    Set.range (transitionSubschemeι k V).base = transitionLocus k V :=
  ((transitionIdeal k V).range_subschemeι).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- **The projection of the incidence correspondence to `𝐏(V) ×_k 𝐏(V)`**, the morphism whose
fibre over a pair of closed points is the projective linear subspace of
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEquations`. -/
public def transitionProj [FiniteDimensional k V] :
    transitionSubscheme k V ⟶ prodTwo k V := transitionSubschemeι k V ≫ tpFst k V

/-- The projection of the incidence correspondence to the parameter space, the morphism whose
fibre dimension Tag 0B2L bounds. -/
public def transitionProjPar [FiniteDimensional k V] :
    transitionSubscheme k V ⟶ projectiveSpaceOfModule k (ParameterModule k V) :=
  transitionSubschemeι k V ≫ tpPar k V

/-- The structure morphism of the incidence correspondence over `Spec k`. -/
public def transitionToSpec [FiniteDimensional k V] :
    transitionSubscheme k V ⟶ Spec (.of k) :=
  transitionSubschemeι k V ≫ transitionProdToSpec k V

public instance locallyOfFiniteType_transitionToSpec [FiniteDimensional k V] [Nontrivial V]
    [Nontrivial (ParameterModule k V)] : LocallyOfFiniteType (transitionToSpec k V) := by
  rw [transitionToSpec]
  infer_instance

/-- **The incidence correspondence over a base `S` mapping to `𝐏(V) ×_k 𝐏(V)`**: the base change
along that morphism of the projection to the first two factors. The base Tag 0B1S needs is the
product of the two closed subvarieties, `prodOfClosedToProdTwo k V X Y hX hY`; no restriction
away from the diagonal is needed, unlike for the incidence variety of lines of Tag 0B1R. -/
public def transitionVariety [FiniteDimensional k V] {S : Scheme.{u}} (f : S ⟶ prodTwo k V) :
    Scheme.{u} := pullback (transitionProj k V) f

/-- The projection of the incidence correspondence over a base to that base. -/
public def transitionVarietyToBase [FiniteDimensional k V] {S : Scheme.{u}}
    (f : S ⟶ prodTwo k V) : transitionVariety k V f ⟶ S := pullback.snd _ _

/-- The projection of the incidence correspondence over a base to the correspondence itself. -/
public def transitionVarietyToSubscheme [FiniteDimensional k V] {S : Scheme.{u}}
    (f : S ⟶ prodTwo k V) : transitionVariety k V f ⟶ transitionSubscheme k V := pullback.fst _ _

/-- The morphism from the incidence correspondence over a base to the parameter space, sending a
triple `(x, y, [g])` to `[g]`. This is the morphism whose fibre dimension Tag 0B2L bounds. -/
public def transitionVarietyToPar [FiniteDimensional k V] {S : Scheme.{u}}
    (f : S ⟶ prodTwo k V) :
    transitionVariety k V f ⟶ projectiveSpaceOfModule k (ParameterModule k V) :=
  transitionVarietyToSubscheme k V f ≫ transitionProjPar k V

/-- **The incidence correspondence over a base is the fibre product** of the correspondence with
that base over `𝐏(V) ×_k 𝐏(V)`. -/
public theorem isPullback_transitionVariety [FiniteDimensional k V] {S : Scheme.{u}}
    (f : S ⟶ prodTwo k V) :
    IsPullback (transitionVarietyToSubscheme k V f) (transitionVarietyToBase k V f)
      (transitionProj k V) f :=
  IsPullback.of_hasPullback _ _

/-- **Openness of the projection transfers from the full base `𝐏(V) ×_k 𝐏(V)` to any base over
it.** Topological openness does not base change, so the hypothesis is the *universal* openness of
the projection from the full base; that is what makes the projection of the correspondence over
`X × Y` to `X × Y` an open map, which is hypothesis (b) of Tag 004Z in
`irreducibleSpace_of_isOpenMap_of_dense_isIrreducible_fiber` of
`StacksFrontier.Topology.Irreducible.DenseFibres`. -/
public theorem isOpenMap_transitionVarietyToBase_of_universallyOpen [FiniteDimensional k V]
    (h : UniversallyOpen (transitionProj k V)) {S : Scheme.{u}} (f : S ⟶ prodTwo k V) :
    IsOpenMap (transitionVarietyToBase k V f).base :=
  have := h
  Scheme.Hom.isOpenMap (pullback.snd (transitionProj k V) f)

/-! ### The closed points of the transition locus -/

section Content

variable [FiniteDimensional k V]

attribute [local instance] isInvertible_tautologicalModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- The germ of the minor section is the signed sum over a basis of `V` of the germs of its
tensors of three tautological sections. -/
private theorem minorGerm_eq_sum (t : transitionProd k V) (v w : V) :
    grpGerm (transitionProd k V).toRingedSpace
        (tripleSh k V V (ParameterModule k V) (tpSource k V) (tpTarget k V)
          (tpPar k V)).val t ⊤ (Opens.mem_top t) ((minorSection k V v w).eval (op ⊤)) =
      ∑ i : Fin (Module.finrank k V),
        (tripleGerm k V V (ParameterModule k V) (tpSource k V) (tpTarget k V) (tpPar k V) t
            (Module.finBasis k V i) w (paramCoord k V ((Module.finBasis k V).coord i) v) -
          tripleGerm k V V (ParameterModule k V) (tpSource k V) (tpTarget k V) (tpPar k V) t
            (Module.finBasis k V i) v (paramCoord k V ((Module.finBasis k V).coord i) w)) := by
  rw [minorSection_eval]
  exact Eq.trans
    (map_sum (grpGerm (transitionProd k V).toRingedSpace
      (tripleSh k V V (ParameterModule k V) (tpSource k V) (tpTarget k V)
        (tpPar k V)).val t ⊤ (Opens.mem_top t)) _ Finset.univ)
    (Finset.sum_congr rfl fun i _ => map_sub _ _ _)

/-- **The minor section attached to `(v, w)` is nonvanishing at a point whose three projections
are the closed points cut out by `f`, `f'` and `f₃` exactly when the corresponding `2 × 2` minor
is nonzero**, where `g` is the endomorphism at which `f₃` is evaluation. -/
public theorem mem_nonvanishingLocus_minorSection_iff (t : transitionProd k V)
    (f : Module.Dual k V) (hf : f ≠ 0)
    (hsrc : (tpSource k V).base t = linearFunctionalPoint k V f hf)
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (htgt : (tpTarget k V).base t = linearFunctionalPoint k V f' hf')
    (f₃ : Module.Dual k (ParameterModule k V)) (hf₃ : f₃ ≠ 0)
    (hpar : (tpPar k V).base t = linearFunctionalPoint k (ParameterModule k V) f₃ hf₃)
    (g : V →ₗ[k] V) (hg : ∀ ψ : ParameterModule k V, f₃ ψ = ψ g) (v w : V) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := (transitionProd k V).toRingedSpace)
        (transitionTwistModule k V) (minorSection k V v w) ↔
      f' w * f (g v) - f' v * f (g w) ≠ 0 := by
  obtain ⟨a₀, ha₀⟩ := exists_apply_ne_zero k hf
  obtain ⟨b₀, hb₀⟩ := exists_apply_ne_zero k hf'
  obtain ⟨c₀, hc₀⟩ := exists_apply_ne_zero k hf₃
  refine mem_nonvanishingLocus_iff_of_germ_sub_smul_mem k V V (ParameterModule k V)
    (tpSource k V) (tpTarget k V) (tpPar k V) t f hf hsrc f' hf' htgt f₃ hf₃ hpar
    (transitionProdToSpec k V) a₀ ha₀ b₀ hb₀ c₀ hc₀ (minorSection k V v w) _ ?_
  rw [minorGerm_eq_sum k V t v w,
    ← sum_ratio_eq_minor k V f f' f₃ g hg a₀ ha₀ b₀ hb₀ c₀ hc₀ v w]
  exact tripleGerm_sum_sub_smul_mem k V V (ParameterModule k V) (tpSource k V) (tpTarget k V)
    (tpPar k V) t f hf hsrc f' hf' htgt f₃ hf₃ hpar (transitionProdToSpec k V)
    (tpSource_comp_toSpec k V) (tpTarget_comp_toSpec k V) (tpPar_comp_toSpec k V)
    a₀ ha₀ b₀ hb₀ c₀ hc₀ _ _ _ _ _ _

/-- **A point of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` whose three projections are closed points lies on the
transition locus exactly when `f ∘ g` lies on the line of `f'`** — that is, exactly when the
projective transformation attached to `g` carries the source point to the target point. This is
what makes `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubscheme` the incidence
correspondence `T` of Tag 0B1S and not merely some closed subscheme. -/
public theorem mem_transitionLocus_iff_of_linearFunctionalPoint (t : transitionProd k V)
    (f : Module.Dual k V) (hf : f ≠ 0)
    (hsrc : (tpSource k V).base t = linearFunctionalPoint k V f hf)
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (htgt : (tpTarget k V).base t = linearFunctionalPoint k V f' hf')
    (f₃ : Module.Dual k (ParameterModule k V)) (hf₃ : f₃ ≠ 0)
    (hpar : (tpPar k V).base t = linearFunctionalPoint k (ParameterModule k V) f₃ hf₃)
    (g : V →ₗ[k] V) (hg : ∀ ψ : ParameterModule k V, f₃ ψ = ψ g) :
    t ∈ transitionLocus k V ↔ f ∘ₗ g ∈ Submodule.span k {f'} := by
  rw [mem_span_singleton_iff_forall_minor_eq_zero k V hf' g, mem_transitionLocus_iff]
  have key (v w : V) : t ∉ Stacks.SheafOfModules.nonvanishingLocus
      (X := (transitionProd k V).toRingedSpace) (transitionTwistModule k V)
      (minorSection k V v w) ↔ f' w * f (g v) - f' v * f (g w) = 0 := by
    rw [mem_nonvanishingLocus_minorSection_iff k V t f hf hsrc f' hf' htgt f₃ hf₃ hpar g hg,
      not_not]
  refine ⟨fun h v w => ?_, fun h p => (key p.1 p.2).2 ?_⟩
  · linear_combination -((key w v).1 (h (w, v)))
  · linear_combination -(h p.2 p.1)

end Content

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
