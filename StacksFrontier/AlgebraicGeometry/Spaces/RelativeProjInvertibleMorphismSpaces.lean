module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Spaces
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleLocus

/-!
# The morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)` of algebraic spaces

[Stacks, Tag 0D2Z] fixes a scheme `S`, an algebraic space `Y` over `S`, a quasi-coherent graded
`𝒪_Y`-algebra `𝒜` with relative Proj `π : Proj_Y(𝒜) ⟶ Y`, a morphism of algebraic spaces
`f : X ⟶ Y`, an invertible `𝒪_X`-module `ℒ` and a graded `𝒪_X`-algebra homomorphism
`ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}`.  On the open subspace `U(ψ) ⊆ X` of [Stacks, Tag 0D2Y] — the
locus where `f^*𝒜_d ⟶ ℒ^{⊗ d}` is surjective for some `d ≥ 1` — it produces a canonical morphism
of algebraic spaces over `Y`

  `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`

together with a graded map `θ`, characterized by three properties.  The source's proof is
"Omitted. Hints: …", and the hint is a reduction: *a quasi-compact scheme `W ⟶ X` factors through
`U(ψ)` exactly when `ψ|_W` is surjective in some positive degree, which describes `U(ψ)` as a
subfunctor of `X` on `(Sch/S)_{fppf}`; for such a `W` the quadruple `(d, W ⟶ Y, ℒ|_W, ψ^{(d)}|_W)`
gives a morphism `W ⟶ Proj_Y(𝒜)` by the construction of the relative Proj, independent of `d`,
and this family of morphisms is a transformation of functors, i.e. the morphism `r_{ℒ,ψ}`.*

This file carries out the second half of that reduction: given `U(ψ)` as a
`CategoryTheory.Subfunctor` of `X` — the source's own description of it — together with the
restrictions of `ψ` to its test schemes, it builds `r_{ℒ,ψ}` out of the morphisms that
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/Spaces.lean` attaches to those
restrictions, the compatibility of the restrictions under base change being exactly the
naturality that makes the family a transformation of functors.  The subfunctor is pinned to the
open `U(ψ)` of [Stacks, Tag 0D2Y]: a test scheme `ρ : T ⟶ X` belongs to it exactly when the open
that `U(ψ)` cuts on that scheme point is the whole of `T`.

## Main definitions

* `AlgebraicGeometry.Space.InvertibleQuotientLocus` is the input of that construction: the data
  of [Stacks, Tag 0D2Y], the subfunctor `U(ψ) ⊆ X` it determines, the restriction of `ψ` to each
  test scheme of `U(ψ)`, and the compatibility of those restrictions under base change.
* `AlgebraicGeometry.Space.InvertibleQuotientLocus.morphism` is **`r_{ℒ,ψ}`**: the morphism of
  algebraic spaces `U(ψ) ⟶ Proj_Y(𝒜)`.
* `AlgebraicGeometry.Space.InvertibleQuotientLocus.factor` is the factorisation through
  `U(ψ) ⊆ X` of a test scheme of `X` lying in `U(ψ)`, in which clause (2)(b) is stated.

## Main results

* `AlgebraicGeometry.Space.InvertibleQuotientLocus.morphism_comp_toBase`: `r_{ℒ,ψ}` is a morphism
  *over* `Y`.
* `AlgebraicGeometry.Space.InvertibleQuotientLocus.factor_comp_morphism`: **clause (2)(b)** of the
  tag.  For a scheme `W ⟶ X` lying in `U(ψ)`, the composite of `W ⟶ U(ψ)` with `r_{ℒ,ψ}` is the
  morphism `W ⟶ Proj_Y(𝒜)` that the construction of the relative Proj attaches to `ψ|_W`.  The
  factorisation is an explicit hypothesis of the lemma;
  `AlgebraicGeometry.Space.InvertibleQuotientLocus.factor_comp_morphism_of_locus_eq_top` is the
  same statement with that hypothesis in its [Stacks, Tag 0D2Y] form.
* `AlgebraicGeometry.Space.InvertibleQuotientLocus.eq_morphism`: `r_{ℒ,ψ}` is the only morphism
  `U(ψ) ⟶ Proj_Y(𝒜)` with clause (2)(b) — the "characterized by" of the tag, for clause (2)(b).
* `AlgebraicGeometry.Space.InvertibleQuotientLocus.factor_comp_ι` and
  `AlgebraicGeometry.Space.InvertibleQuotientLocus.yonedaEquiv_factor` identify the
  factorisation.
* `AlgebraicGeometry.Space.InvertibleQuotientLocus.ofTotalPairs`: the datum is inhabited with
  `U(ψ) = X`, when the open `U(ψ)` cuts the whole of every scheme point of `X` and `ψ` is
  surjective in degree one over every test scheme.

## What is carried, and why

**The subfunctor is pinned to the open `U(ψ)`, not carried freely.**  The open subspace `U(ψ)` is
[Stacks, Tag 0D2Y] and is available here as
`AlgebraicGeometry.Space.GradedPowerMapPoints.locus`: the open it cuts on each scheme point of
`X`.  That file does not assemble those opens into a subfunctor — the compatibility of the family
under pullback along a morphism of *test objects* cannot be stated for the datum, as its "Not done
here" records — so the subfunctor is a field here.  It is not, however, a free one: a test scheme
factors through an open subspace exactly when the open it cuts on it is everything, which is the
field `AlgebraicGeometry.Space.InvertibleQuotientLocus.mem_locus_iff_locus_eq_top`, and that
determines the subfunctor completely from the Tag 0D2Y data.  In particular the empty subfunctor
inhabits the datum only for a `ψ` whose `U(ψ)` really is empty, and then the results below are
statements about an empty open subspace, which is what the tag says about it.

**The restrictions of `ψ` are carried, not built.**  `ψ` itself cannot be written at
this spelling: neither the pullback of a quasi-coherent graded algebra along a morphism of
algebraic spaces nor the tensor powers of an invertible module on the small étale site of an
algebraic space is available here, which is what the implementation notes of
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/Locus.lean` record.  What *is*
available is the restriction of `ψ` to a scheme over `X` on which it is surjective, in the shape
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair` — an invertible module with a graded map out of
the restricted algebra, surjective in degree one.  So `InvertibleQuotientLocus` carries the family
of those restrictions, together with
`AlgebraicGeometry.Space.InvertibleQuotientLocus.pair_isPullback`, which says that the family
comes from one `ψ`.  The datum follows the pattern of the Tag 085F datum
`AlgebraicGeometry.Space.RelativeProjHomPoints`.

**`X` is representable.**  The source's clause (2) is itself stated for a *scheme* `W ⟶ X`, and
clause (3) for schemes `X'` and `Y'`; the reduction the hint performs is to schemes over `X`.
Here `X` is a scheme object of the site, and `Y` remains an arbitrary algebraic space, which is
what makes the relative Proj below the relative Proj of an algebraic space.  Taking `X` to be an
arbitrary algebraic space would need the algebras `d.algebra T f` at the different points `f` of
the base to be compared, and `AlgebraicGeometry.Space.RelativeProjPoints` carries no such
comparison — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/Spaces.lean`.  With `X`
representable every restriction of `ψ` is a pair for the one algebra `𝒜` restricted to `X`, and
that is what lets them be compared.

**Degree one.**  `F1Pair` carries degree-one surjectivity as a field, whereas the tag allows any
`d ≥ 1`.  For an algebra generated in degree one — the standing hypothesis of Tag 01O4, hence of
every `F1Representation`, hence of the hypothesis `hgen` below — the two loci agree; that
comparison is not proved here either.

## Not done here

* **Clause (2)(a) is not proved.**  Clause (2)(a) says that a scheme `W ⟶ X` over which `ψ` is
  surjective lies in `U(ψ)`.  Through `mem_locus_iff_locus_eq_top` that now reads: if `ψ|_W` is
  surjective then the open `U(ψ)` cuts the whole of `W`.  Its hypothesis is the surjectivity of
  *`ψ`'s own* restriction, which is carried here as
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair`, whereas the open is cut by
  `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap`, which uses the
  iterated tensor product `Stacks.TensorPowers.natTensorPow` rather than the tensor algebras
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebras` that `F1Pair` and the
  representations of Tag 01O4 consume; the comparison of the two is what the `Locus` file records
  as missing, and without it the hypothesis and the conclusion speak of different objects.
  Quantifying clause (2)(a) instead over *every* pair on `W` would be a different and stronger
  hypothesis than the source's — a second invertible quotient of `𝒜|_W` says nothing about where
  `ψ` is surjective — so it is not imposed.  Clause (2)(b) is therefore stated with the
  factorisation through `U(ψ)` as an explicit hypothesis of the lemma.
* **The graded map `θ` is not constructed, and clause (1) is not proved.**  Clause (1) is a
  commuting square one side of which is `θ`.  Its source is the pullback along `r_{ℒ,ψ}` of
  `⨁_{d ≥ 0} 𝒪_{Proj_Y(𝒜)}(d)`; the twists of the relative Proj of an algebraic space are
  Tag 085A and are not in this library, so there is nothing for `θ` to be a map out of.
* **Clause (3) is not proved.**  It compares the morphism with its base change along
  `g : Y' ⟶ Y` through the isomorphism `Proj_{Y'}(g^*𝒜) = Y' ×_Y Proj_Y(𝒜)` of
  [Stacks, Tag 085C].  `AlgebraicGeometry.Space.GradedAlgebraPoints.F.baseChangeEquiv` has that
  isomorphism only as a family of bijections of the values of the functor of quadruples, there
  being no representing algebraic space to transport it to (Tag 084B is not proved), and the
  restricted algebras over `Y` and over `Y'` are unrelated data in
  `AlgebraicGeometry.Space.RelativeProjPoints`, so neither `U(ψ') = (g')^{-1}(U(ψ))` nor the
  agreement of the two morphisms can be stated.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 0D2Y](https://stacks.math.columbia.edu/tag/0D2Y)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 085D](https://stacks.math.columbia.edu/tag/085D)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace AlgebraicGeometry.Space

universe u

/-- **The locus `U(ψ) ⊆ X` of [Stacks, Tag 0D2Z] together with the restrictions of `ψ` to it.**

The source describes `U(ψ)` as the subfunctor of `X` on `(Sch/S)_{fppf}` whose points are the
schemes `W ⟶ X` over which `ψ` is surjective in some positive degree, and attaches the morphism
`r_{ℒ,ψ}` to the restrictions `ψ|_W`.  This structure is the input of that construction: the
open `U(ψ)` of [Stacks, Tag 0D2Y], the subfunctor of `X` it determines, the restriction of `ψ` to
each test scheme of that subfunctor as a pair of [Stacks, Tag 01O4], and the compatibility of
those restrictions under base change.

The subfunctor is not a free parameter: `mem_locus_iff_locus_eq_top` pins it to the open `U(ψ)`
of `points`, and at most one subfunctor has that property.  See the module docstring for why the
family of restrictions of `ψ` is carried rather than cut out of a global `ψ`. -/
public structure InvertibleQuotientLocus {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Y Proj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Proj ⟶ Y}
    (d : RelativeProjPoints B S hS π) (TA : TensorAlgebras.{u})
    (i : TensorAlgebraPullbackIsos.{u} TA) (X : BigFppfOver B S hS)
    (f : yoneda.obj X ⟶ Y) where
  /-- The open subspace `U(ψ) ⊆ X`, as the subfunctor of `X` the source describes it as. -/
  locus : Subfunctor (yoneda.obj X)
  /-- The data of [Stacks, Tag 0D2Y]: the open `U(ψ)` that `locus` is the subfunctor of, given by
  the open it cuts on each scheme point of `X`. -/
  points : GradedPowerMapPoints B S hS (yoneda.obj X)
  /-- **`locus` is exactly `U(ψ)`.**  A test scheme `ρ : T ⟶ X` factors through the open subspace
  `U(ψ) ⊆ X` precisely when the open that `U(ψ)` cuts on that scheme point is the whole of `T`. -/
  mem_locus_iff_locus_eq_top {T : BigFppfOver B S hS} (ρ : T ⟶ X) :
    ρ ∈ locus.obj (op T) ↔ points.locus T (yoneda.map ρ) = ⊤
  /-- The restriction `ψ|_W` of `ψ` to a test scheme `W ⟶ X` of `U(ψ)`: an invertible module on
  `W` together with a graded map out of the restricted algebra, surjective in degree one. -/
  pair {T : BigFppfOver B S hS} {ρ : T ⟶ X} (hρ : ρ ∈ locus.obj (op T)) :
    F1Pair (d.algebra X f) TA ((BigFppfOver.toScheme B S hS).map ρ)
  /-- The restrictions of `ψ` are compatible with base change of the test scheme: this is what
  says that they are the restrictions of one graded map. -/
  pair_isPullback {T T' : BigFppfOver B S hS} (g : T' ⟶ T) {ρ : T ⟶ X}
      (hρ : ρ ∈ locus.obj (op T)) :
    IsPullbackPair (d.algebra X f) TA i ((BigFppfOver.toScheme B S hS).map g) (pair hρ)
      (pair (show g ≫ ρ ∈ locus.obj (op T') from locus.map g.op hρ))

namespace InvertibleQuotientLocus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Proj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Proj ⟶ Y}
    {d : RelativeProjPoints B S hS π} {TA : TensorAlgebras.{u}}
    {i : TensorAlgebraPullbackIsos.{u} TA}
    {D : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ Y), TwistData (d.algebra T f)}
    (hgen : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ Y),
      IsGeneratedInDegreeOne (d.algebra T f))
    (rep : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ Y),
      F1Representation (d.algebra T f) TA i (D T f))
    {X : BigFppfOver B S hS} {f : yoneda.obj X ⟶ Y}
    (L : InvertibleQuotientLocus d TA i X f)

/-- **`r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`, the morphism of [Stacks, Tag 0D2Z].**

Its value on a test scheme `W ⟶ X` of `U(ψ)` is the morphism `W ⟶ Proj_Y(𝒜)` that the
construction of the relative Proj attaches to `ψ|_W`, and its naturality is the compatibility of
the restrictions of `ψ` with base change: this is the transformation of functors the source's
proof produces. -/
@[stacks 0D2Z "variant: the morphism r_{L,psi} built from a family of degree-one \
restrictions of psi to the test schemes of U(psi); the tag is \
AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
public def morphism : L.locus.toFunctor ⟶ Proj where
  app U := ↾fun a => yonedaEquiv (d.pointOfPair TA i hgen rep X f a.1 (L.pair a.2))
  naturality U V h := by
    ext a
    refine Eq.trans ?_ (yonedaEquiv_naturality'
      (d.pointOfPair TA i hgen rep X f a.1 (L.pair a.2)) h).symm
    exact congrArg yonedaEquiv (d.map_comp_pointOfPair TA i hgen rep X f a.1 h.unop
      (L.pair a.2) (L.pair (L.locus.map h a.2)) (L.pair_isPullback h.unop a.2)).symm

/-- **`r_{ℒ,ψ}` is a morphism over `Y`**, as [Stacks, Tag 0D2Z] asserts: composing it with the
structure morphism `π : Proj_Y(𝒜) ⟶ Y` gives the restriction of `f : X ⟶ Y` to `U(ψ)`. -/
@[stacks 0D2Z "variant: the morphism of `morphism` lies over Y; the tag is \
AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
public theorem morphism_comp_toBase : L.morphism hgen rep ≫ π = L.locus.ι ≫ f := by
  ext U a
  obtain ⟨ρ, hρ⟩ := a
  change π.app U (yonedaEquiv (d.pointOfPair TA i hgen rep X f ρ (L.pair hρ))) = f.app U ρ
  rw [← yonedaEquiv_comp, d.pointOfPair_comp_toBase TA i hgen rep X f ρ (L.pair hρ),
    yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- The factorisation through `U(ψ) ⊆ X` of a test scheme `W ⟶ X` lying in `U(ψ)`.  It is the
morphism `W ⟶ U(ψ)` whose composite with `r_{ℒ,ψ}` clause (2)(b) computes. -/
public def factor {W : BigFppfOver B S hS} (w : W ⟶ X) (hw : w ∈ L.locus.obj (op W)) :
    yoneda.obj W ⟶ L.locus.toFunctor :=
  yonedaEquiv.symm (⟨w, hw⟩ : L.locus.toFunctor.obj (op W))

/-- The point of `U(ψ)` underlying the factorisation is the point of `X` it was built from. -/
public theorem yonedaEquiv_factor {W : BigFppfOver B S hS} (w : W ⟶ X)
    (hw : w ∈ L.locus.obj (op W)) :
    yonedaEquiv (L.factor w hw) = (⟨w, hw⟩ : L.locus.toFunctor.obj (op W)) :=
  yonedaEquiv.apply_symm_apply _

/-- The factorisation is a factorisation of `W ⟶ X` through the inclusion `U(ψ) ⊆ X`. -/
public theorem factor_comp_ι {W : BigFppfOver B S hS} (w : W ⟶ X)
    (hw : w ∈ L.locus.obj (op W)) : L.factor w hw ≫ L.locus.ι = yoneda.map w :=
  (yonedaEquiv_symm_naturality_right W L.locus.ι
        (⟨w, hw⟩ : L.locus.toFunctor.obj (op W))).trans
    (yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map w).symm)

/-- **Clause (2)(b) of [Stacks, Tag 0D2Z].**  For a scheme `W ⟶ X` lying in `U(ψ)`, the composite
of the factorisation `W ⟶ U(ψ)` with `r_{ℒ,ψ}` is the morphism `W ⟶ Proj_Y(𝒜)` that the
construction of the relative Proj attaches to `ψ|_W` — in this library, the morphism the
representing bijection of [Stacks, Tag 085D] attaches to it. -/
@[stacks 0D2Z "variant: clause (2)(b) for the morphism of `morphism`, at the test \
schemes of U(psi); the tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
public theorem factor_comp_morphism {W : BigFppfOver B S hS} (w : W ⟶ X)
    (hw : w ∈ L.locus.obj (op W)) :
    L.factor w hw ≫ L.morphism hgen rep = d.pointOfPair TA i hgen rep X f w (L.pair hw) :=
  (yonedaEquiv_symm_naturality_right W (L.morphism hgen rep)
        (⟨w, hw⟩ : L.locus.toFunctor.obj (op W))).trans
    (yonedaEquiv.symm_apply_apply _)

/-- **Clause (2)(b), with the factorisation written in the terms of [Stacks, Tag 0D2Y].**  A
scheme `W ⟶ X` factors through `U(ψ)` exactly when the open `U(ψ)` cuts the whole of `W`, so
clause (2)(b) may be read off that hypothesis directly. -/
public theorem factor_comp_morphism_of_locus_eq_top {W : BigFppfOver B S hS} (w : W ⟶ X)
    (hw : L.points.locus W (yoneda.map w) = ⊤) :
    L.factor w ((L.mem_locus_iff_locus_eq_top w).2 hw) ≫ L.morphism hgen rep =
      d.pointOfPair TA i hgen rep X f w (L.pair ((L.mem_locus_iff_locus_eq_top w).2 hw)) :=
  L.factor_comp_morphism hgen rep w _

/-- **`r_{ℒ,ψ}` is the only morphism with clause (2)(b).**  Together with `factor_comp_morphism`
this is the "characterized by" of [Stacks, Tag 0D2Z] for clause (2)(b): every test scheme of
`U(ψ)` carries a restriction of `ψ`, so clause (2)(b) prescribes the morphism on every point of
`U(ψ)`. -/
@[stacks 0D2Z "variant: the uniqueness of the morphism of `morphism` given clause (2)(b); the \
tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
public theorem eq_morphism (Φ : L.locus.toFunctor ⟶ Proj)
    (hΦ : ∀ {W : BigFppfOver B S hS} (w : W ⟶ X) (hw : w ∈ L.locus.obj (op W)),
      L.factor w hw ≫ Φ = d.pointOfPair TA i hgen rep X f w (L.pair hw)) :
    Φ = L.morphism hgen rep := by
  ext U a
  obtain ⟨ρ, hρ⟩ := a
  have h (Ψ : L.locus.toFunctor ⟶ Proj) :
      yonedaEquiv (L.factor ρ hρ ≫ Ψ) = Ψ.app U ⟨ρ, hρ⟩ := by
    rw [yonedaEquiv_comp, L.yonedaEquiv_factor ρ hρ]
  exact (h Φ).symm.trans <| (congrArg yonedaEquiv (hΦ ρ hρ)).trans <|
    (congrArg yonedaEquiv (L.factor_comp_morphism hgen rep ρ hρ)).symm.trans (h _)

/-- **The datum is inhabited with `U(ψ) = X`.**  If the open `U(ψ)` of [Stacks, Tag 0D2Y] cuts
the whole of every scheme point of `X`, and `ψ` is surjective in degree one over every scheme
`W ⟶ X` compatibly with base change, then the full subfunctor of `X` together with that family
is a datum: the case of the tag in which the locus is everything.

The hypothesis `hlocus` is what the pinning of the locus demands here; it is not dischargeable
from `points` alone, since a general `U(ψ)` is a proper open. -/
public def ofTotalPairs (points : GradedPowerMapPoints B S hS (yoneda.obj X))
    (hlocus : ∀ {T : BigFppfOver B S hS} (ρ : T ⟶ X), points.locus T (yoneda.map ρ) = ⊤)
    (P : ∀ {T : BigFppfOver B S hS} (ρ : T ⟶ X),
      F1Pair (d.algebra X f) TA ((BigFppfOver.toScheme B S hS).map ρ))
    (hP : ∀ {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (ρ : T ⟶ X),
      IsPullbackPair (d.algebra X f) TA i ((BigFppfOver.toScheme B S hS).map g) (P ρ)
        (P (g ≫ ρ))) :
    InvertibleQuotientLocus d TA i X f where
  locus := ⊤
  points := points
  mem_locus_iff_locus_eq_top ρ := iff_of_true trivial (hlocus ρ)
  pair := fun {_} {ρ} _ => P ρ
  pair_isPullback := fun {_ _} g {ρ} _ => hP g ρ

end InvertibleQuotientLocus

end AlgebraicGeometry.Space

end
