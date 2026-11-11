module

public import StacksFrontier.AlgebraicGeometry.Morphism.Composition
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of the relative Proj of an algebraic space

Let `S` be a scheme, `X` an algebraic space over `S` and `ψ : 𝒜 ⟶ ℬ` a map of quasi-coherent
graded `𝒪_X`-algebras.  Writing `P = Proj_X(𝒜) ⟶ X` and `Q = Proj_X(ℬ) ⟶ X`, the map `ψ` does
not in general induce a morphism `Q ⟶ P`: it induces one only on an open subspace
`U(ψ) ⊆ Q`, the locus where the induced map of graded section rings is "defined".  This file
constructs that open subspace and the morphism

`r_ψ : U(ψ) ⟶ P`

over `X`, proves the étale-local description that characterizes them — on a scheme `W` étale
over `X` the pair `(U(ψ) ×_X W, r_ψ|)` is the pair the case of schemes attaches to
`ψ|_W : 𝒜|_W ⟶ ℬ|_W` — and proves the composition law: for `φ : 𝒜 ⟶ ℬ` and `ψ : ℬ ⟶ 𝒞`,

`U(ψ ∘ φ) = r_ψ^{-1}(U(φ))` and `r_{ψ ∘ φ} = r_φ ∘ r_ψ|_{U(ψ ∘ φ)}`.

These are Stacks 085F and the first two assertions of Stacks 085G, the étale-local analogues of
the scheme-level Stacks 07ZG and 07ZH.  The third assertion of Stacks 085G,
`θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`, is in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityComp`.

## Main definitions

* `AlgebraicGeometry.Space.liftToOpens` is the factorization of a morphism of schemes all of
  whose points land in an open subscheme of the target through that open subscheme.
* `AlgebraicGeometry.Space.RelativeProjPoints.sectionOfPoint` is the section of the
  scheme-level relative Proj of the restricted algebra attached to a point of the relative
  Proj of an algebraic space lying over a scheme point of the base.
* `AlgebraicGeometry.Space.IsDefinedOn` and `AlgebraicGeometry.Space.IsDefined` are the
  condition that such a point lies in the domain of definition of `ψ`: its section factors
  through the open `U(ψ|_T)` of Stacks 07ZG.
* `AlgebraicGeometry.Space.pointHomOn` and `AlgebraicGeometry.Space.pointHomAt` are the point
  of `P` induced by a point of `Q` in the domain of definition, obtained by applying the
  scheme-level morphism `r_{ψ|_T}` of Stacks 07ZG to that factorization.
* `AlgebraicGeometry.Space.RelativeProjHomPoints` is a map of quasi-coherent graded
  `𝒪_X`-algebras read over the scheme points of the base: the restriction `ψ|_T` at every
  scheme point `T ⟶ X`, together with the compatibility of the resulting opens and morphisms
  with restriction in the test object.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeMapSubfunctor` is **Stacks 085F**,
  the open subspace `U(ψ) ⊆ Q`, and
  `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeMapSpaceHom` is **Stacks 085F**, the
  morphism `r_ψ : U(ψ) ⟶ P`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.definedLocus` is the open subscheme of a
  scheme point of `Q` cut out by `U(ψ)`; it is what exhibits `U(ψ)` as an open subspace.
* `AlgebraicGeometry.Space.relativeMapCompLift` is the restriction of the scheme-level
  morphism `r_ψ` to the open attached to a composite, the morphism `q` of the factorized form
  of Stacks 07ZH.
* `AlgebraicGeometry.Space.homComp` is the composite of two maps of graded algebras at each
  scheme point of the base, and
  `AlgebraicGeometry.Space.RelativeProjHomPoints.comp` assembles it into a map of graded
  algebras over the scheme points of the base.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointTwist` is the twist `𝒪_P(n)` of the relative
  Proj of an algebraic space, over a scheme point of the base, and
  `AlgebraicGeometry.Space.RelativeProjPoints.fibreTwist` is that module read on the étale chart
  `T ×_X P` of `P`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap` is **Stacks 085F's third
  component**, the map `θ_n : r_ψ^*𝒪_P(n) ⟶ 𝒪_{U(ψ)}(n)`, and
  `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistAlgebraSpaceHom` is the same `θ` as
  a map of `ℤ`-graded algebras, which is the shape the source states.

## Main results

* `AlgebraicGeometry.Space.RelativeProjHomPoints.isOpenSubspace_relativeMapSubfunctor` is
  **Stacks 085F**: `U(ψ)` is an open subspace of `Q`, that is, it is an algebraic space over
  `S` and its inclusion into `Q` is an open immersion.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeMapSpaceHom_comp` is **Stacks 085F**:
  `r_ψ` is a morphism over `X`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.mem_relativeMapSubfunctor_iff` and
  `AlgebraicGeometry.Space.RelativeProjHomPoints.app_relativeMapSpaceHom` are **Stacks 085F's
  étale-local characterization**: a point of `Q` over a scheme point `f` of `X` lies in `U(ψ)`
  exactly when its section of `Proj_T(ℬ|_T)` factors through the open `U(ψ|_T)` of
  Stacks 07ZG, and `r_ψ` then produces the point of `P` whose section is the image of that
  factorization under the morphism `r_{ψ|_T}` of Stacks 07ZG — the latter identification being
  `AlgebraicGeometry.Space.sectionOfPoint_pointHomOn`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeMapSubfunctor_unique` and
  `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeMapSpaceHom_unique` are the
  uniqueness half of **Stacks 085F's characterization**: that description determines both the
  open subspace and the morphism.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.comp_relativeMapSubfunctor_le` and
  `AlgebraicGeometry.Space.RelativeProjHomPoints.mem_comp_relativeMapSubfunctor_iff` are the
  **first assertion of Stacks 085G**: `U(ψ ∘ φ)` is contained in `U(ψ)`, and a point of `U(ψ)`
  lies in `U(ψ ∘ φ)` exactly when its image under `r_ψ` lies in `U(φ)`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.app_comp_relativeMapSpaceHom` is the **second
  assertion of Stacks 085G**: on `U(ψ ∘ φ)` the morphism `r_{ψ ∘ φ}` is `r_ψ` followed by
  `r_φ`.
* `AlgebraicGeometry.Space.relativeMapHom_comp_eq` is the scheme-level second assertion of
  Stacks 07ZH with the restriction of `r_ψ` named, and
  `AlgebraicGeometry.Space.preimage_relativeMapDomain_comp` is its first assertion pulled back
  along a morphism landing in `U(ψ)`; these are the two scheme-level inputs to Stacks 085G.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap_chart` and
  `…relativeTwistSpaceMap_unique` are **Stacks 085F's characterization of `θ`**: on the piece of
  `U(ψ|_T)` over an affine open of a scheme point of the base, `θ_n` is Stacks 01MY's comparison
  map there, and that description determines `θ_n`.

## Implementation notes

**How the relative Proj enters.**  The relative Proj of an algebraic space is presented
through its base changes to the scheme points of the base, by
`AlgebraicGeometry.Space.RelativeProjPoints`: for every object `T` of the site and every
`T`-point `f` of `X` that structure supplies a quasi-coherent graded algebra on the scheme of
`T` — the restriction `f^*𝒜` — and a cartesian square identifying `Proj_T(f^*𝒜)` with
`T ×_X P`.  This is the second assertion of Stacks 084B, and it is the presentation used for
Stacks 085D.  Everything below is read off it: the `T'`-points of `P` over `f` are the sections
of the scheme-level relative Proj of `f^*𝒜`, which is
`AlgebraicGeometry.Space.RelativeProjPoints.pointEquivProjOver`, and `U(ψ)` and `r_ψ` are
built from the open `U(ψ|_T)` and the morphism `r_{ψ|_T}` of Stacks 07ZG applied to those
sections.

**The two compatibility clauses.**  A `AlgebraicGeometry.Space.RelativeProjPoints` gives a
graded algebra at each point of the base and no comparison between the algebra at a point and
the algebra at its restriction.  The inverse image of a `SheafGradedAlgebra` along a morphism of
schemes does exist —
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.pullback` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationRestrict`, for an arbitrary
morphism of base schemes — but that is not what is missing here: the algebras of a
`RelativeProjPoints` are a *field* of the structure, supplied independently at every point of the
base, so nothing identifies the algebra at a restricted point with the inverse image of the
algebra at the point it restricts from, and the structure carries no such identification.
Without such a comparison the open `U(ψ|_T)` computed at a
point and the one computed after restriction are opens of two unrelated schemes, so the
condition cutting out `U(ψ)` would not be functorial.  The two remaining fields of
`AlgebraicGeometry.Space.RelativeProjHomPoints` are exactly that compatibility, transported to
the open and to the morphism of Stacks 07ZG: they say the canonical identifications
`Proj_Z(g^*𝒜) = Z ×_X Proj_X(𝒜)` of Stacks 084B are compatible with a composite
`Z' ⟶ Z ⟶ X`.  They are properties of the presentation, never of `U(ψ)` or of `r_ψ`, and they
are closed under composition: `AlgebraicGeometry.Space.RelativeProjHomPoints.comp` proves them
for `ψ ∘ φ` from the two factors, using only the composition law of Stacks 07ZH.

**The subspace is a subfunctor.**  `U(ψ)` is Mathlib's `CategoryTheory.Subfunctor` of `Q`, as
`AlgebraicGeometry.Space.IsOpenSubspace` asks, so its points, its inclusion and its
functoriality come from Mathlib directly.  Openness is proved over each scheme point of `Q`:
the inverse image of `U(ψ)` along a point `q : T ⟶ Q` is the open subscheme of `T` cut out by
`AlgebraicGeometry.Space.RelativeProjHomPoints.definedLocus`, which is again an object of the
site, so the required cartesian square is the canonical one of
`CategoryTheory.Subfunctor.isPullback_fromPreimage`.  Algebraicity is Stacks 02WY for the
resulting representable inclusion.  The sheaf condition is proved separately, in
`AlgebraicGeometry.Space.RelativeProjHomPoints.isSheaf_relativeMapSubfunctor`: the defining
condition is local because a covering sieve of the big fppf site is jointly surjective on
points.

**Statements are pointwise.**  Both assertions of Stacks 085G are stated on points of the
subfunctors rather than as equalities of subobjects and of morphisms out of them.  That avoids
naming a comparison isomorphism between `U(ψ ∘ φ)` and the inverse image of `U(φ)` under `r_ψ`
and is the same content: a subfunctor is determined by its points, and a morphism out of a
subfunctor by its values.

**The source's typographical slip in Stacks 085G.**  The source writes the first assertion as
`U(ψ ∘ φ) = r_φ^{-1}(U(ψ))`, which does not typecheck: `r_φ` is defined on an open of
`Q = Proj_X(ℬ)` and takes values in `P = Proj_X(𝒜)`, while `U(ψ)` is an open of
`R = Proj_X(𝒞)`.  The scheme-level analogue Stacks 07ZH states it as
`U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`, and that is the reading the second assertion — which both tags
state identically — requires.  The formalization below is that reading.

## The twists and `θ`

The third component of Stacks 085F is the map of `ℤ`-graded `𝒪_{U(ψ)}`-algebras

`θ = θ_ψ : r_ψ^*(⨁_d 𝒪_P(d)) ⟶ ⨁_d 𝒪_{U(ψ)}(d)`.

It is here, over the scheme points of the base, exactly as `U(ψ)` and `r_ψ` are:
`AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap` in each degree and
`AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistAlgebraSpaceHom` as a map of graded
algebras, both read at the point `(T, f)` as the map Stacks 07ZG attaches to `ψ|_{T,f}`.  That
reading is not a weakening: the source *characterizes* the triple `(U(ψ), r_ψ, θ)` by the property
that its restriction to `U(ψ) ×_X W` is the triple of Stacks 07ZG for `ψ|_W`, for every scheme `W`
étale over `X`, and the three declarations above are that restriction, in the same presentation
by the scheme points of the base that the rest of this file uses.

A `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` exists for every quasi-coherent
graded algebra, by `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, which
is what makes `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist` and
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap` — the scheme-level twists and the
scheme-level `θ` — total.

## What is not formalized

**`θ` as a single morphism of sheaves of modules on the algebraic space `U(ψ)`.**  What is here
is the family of its restrictions to the charts of the base, which is what the source's
characterization consists of; assembling that family into one morphism of quasi-coherent modules
on `U(ψ)` needs two things this library does not have.  First, a comparison, under restriction in
the test object, between `𝒪_P(n)` computed at `(T, f)` and at a restricted point: this is the
twist analogue of the two compatibility fields of
`AlgebraicGeometry.Space.RelativeProjHomPoints` and, for the same reason recorded for the open
and the morphism in the implementation notes above, it does not follow from
`AlgebraicGeometry.Space.RelativeProjPoints` and would have to be carried as a further field.
Second, descent of a morphism of quasi-coherent modules along the étale cover of `P` by the
fibres — the module-coefficient half of Stacks 03M3, which is available here only for a scheme
target.

**The third assertion of Stacks 085G**, the compatibility `θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`, is
stated and proved in `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityComp`, as
`AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap_comp`, for the `θ` of this
file: over every scheme point `(T, f)` of the base and in every degree, the inverse image of `θ_φ`
along the restriction of `r_ψ` to `U(ψ ∘ φ)`, followed by `θ_ψ` restricted to `U(ψ ∘ φ)`, is
`θ_{ψ ∘ φ}`.  It lives in that module because its scheme-level input,
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_comp` (the third assertion of
Stacks 07ZH), needs an import this file does not have.

## References

* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 085G](https://stacks.math.columbia.edu/tag/085G)
* [Stacks Project, Tag 085D](https://stacks.math.columbia.edu/tag/085D)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZH](https://stacks.math.columbia.edu/tag/07ZH)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X} {πQ : Q ⟶ X}

/-! ### Factoring a morphism of schemes through an open subscheme -/

/-- A morphism of schemes all of whose points land in an open subscheme of the target factors
through that open subscheme. -/
def liftToOpens {Y Z : Scheme.{u}} (g : Y ⟶ Z) (D : Z.Opens) (h : g ⁻¹ᵁ D = ⊤) :
    Y ⟶ D.toScheme :=
  IsOpenImmersion.lift D.ι g (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ g ⁻¹ᵁ D := by rw [h]; trivial
    exact hy)

/-- The factorization through the open subscheme recovers the morphism. -/
@[reassoc]
theorem liftToOpens_comp_ι {Y Z : Scheme.{u}} (g : Y ⟶ Z) (D : Z.Opens) (h : g ⁻¹ᵁ D = ⊤) :
    liftToOpens g D h ≫ D.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factorization through an open subscheme is the only one: the inclusion of an open
subscheme is a monomorphism. -/
@[ega "I 4.1.8" "open subscheme"]
theorem liftToOpens_unique {Y Z : Scheme.{u}} (g : Y ⟶ Z) (D : Z.Opens) (h : g ⁻¹ᵁ D = ⊤)
    (k : Y ⟶ D.toScheme) (hk : k ≫ D.ι = g) : k = liftToOpens g D h :=
  (cancel_mono D.ι).1 (hk.trans (liftToOpens_comp_ι g D h).symm)

/-- A morphism of schemes factors through an open subscheme of its target exactly when all its
points land there. -/
theorem preimage_eq_top_iff {Y Z : Scheme.{u}} (g : Y ⟶ Z) (D : Z.Opens) :
    g ⁻¹ᵁ D = ⊤ ↔ Set.range g ⊆ (D : Set Z) := by
  constructor
  · rintro h _ ⟨y, rfl⟩
    have hy : y ∈ g ⁻¹ᵁ D := by
      rw [h]
      trivial
    exact hy
  · exact fun h => TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => h ⟨y, rfl⟩)

/-- The factorization through an open subscheme depends only on the morphism. -/
theorem liftToOpens_congr {Y Z : Scheme.{u}} (g g' : Y ⟶ Z) (hgg' : g = g') (D : Z.Opens)
    (h : g ⁻¹ᵁ D = ⊤) (h' : g' ⁻¹ᵁ D = ⊤) : liftToOpens g D h = liftToOpens g' D h' := by
  subst hgg'
  rfl

/-- Enlarging the open subscheme does not change the factorization. -/
theorem liftToOpens_comp_homOfLE {Y Z : Scheme.{u}} (g : Y ⟶ Z) (D D' : Z.Opens)
    (hDD' : D ≤ D') (h : g ⁻¹ᵁ D = ⊤) (h' : g ⁻¹ᵁ D' = ⊤) :
    liftToOpens g D h ≫ Z.homOfLE hDD' = liftToOpens g D' h' :=
  liftToOpens_unique g D' h' (liftToOpens g D h ≫ Z.homOfLE hDD') (by
    rw [Category.assoc, Scheme.homOfLE_ι, liftToOpens_comp_ι])

/-! ### The section of the scheme-level relative Proj attached to a point -/

namespace RelativeProjPoints

variable (d : RelativeProjPoints B S hS πQ)

/-- The section of the scheme-level relative Proj of the restricted algebra attached to a point
of the relative Proj lying over a point `f` of the base along `r : T' ⟶ T`. -/
def sectionOfPoint (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) {T' : BigFppfOver B S hS}
    (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f) :
    (BigFppfOver.toScheme B S hS).obj T' ⟶ (relativeProj (d.algebra T f)).scheme :=
  (d.pointEquivProjOver T f r ⟨u, hu⟩).1

/-- The section attached to a point is a section of the structure morphism of the relative
Proj. -/
@[reassoc]
theorem sectionOfPoint_comp_toBase (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f) :
    d.sectionOfPoint T f r u hu ≫ (relativeProj (d.algebra T f)).toBase =
      (BigFppfOver.toScheme B S hS).map r :=
  (d.pointEquivProjOver T f r ⟨u, hu⟩).2

/-- Restricting a point along `r' : T'' ⟶ T'` precomposes its section with `r'`. -/
theorem sectionOfPoint_restrict (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' T'' : BigFppfOver B S hS} (r : T' ⟶ T) (r' : T'' ⟶ T') (u : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f)
    (hu' : (yoneda.map r' ≫ u) ≫ πQ = yoneda.map (r' ≫ r) ≫ f) :
    d.sectionOfPoint T f (r' ≫ r) (yoneda.map r' ≫ u) hu' =
      (BigFppfOver.toScheme B S hS).map r' ≫ d.sectionOfPoint T f r u hu :=
  d.pointEquivProjOver_natural T f r r' ⟨u, hu⟩

/-- Restricting a point precomposes its section, stated for a composite given by hypothesis. -/
theorem sectionOfPoint_restrict' (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' T'' : BigFppfOver B S hS} (r : T' ⟶ T) (r' : T'' ⟶ T') (r'' : T'' ⟶ T)
    (hr : r'' = r' ≫ r) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f)
    (hu' : (yoneda.map r' ≫ u) ≫ πQ = yoneda.map r'' ≫ f) :
    d.sectionOfPoint T f r'' (yoneda.map r' ≫ u) hu' =
      (BigFppfOver.toScheme B S hS).map r' ≫ d.sectionOfPoint T f r u hu := by
  subst hr
  exact d.sectionOfPoint_restrict T f r r' u hu hu'

/-- A point of the relative Proj is determined by its section: the correspondence between
points over `f` along `r` and sections of the scheme-level relative Proj is a bijection. -/
theorem eq_of_sectionOfPoint_eq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u v : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f) (hv : v ≫ πQ = yoneda.map r ≫ f)
    (h : d.sectionOfPoint T f r u hu = d.sectionOfPoint T f r v hv) : u = v := by
  have key : (⟨u, hu⟩ : {w : yoneda.obj T' ⟶ Q // w ≫ πQ = yoneda.map r ≫ f}) = ⟨v, hv⟩ :=
    (d.pointEquivProjOver T f r).injective (Subtype.ext h)
  exact congrArg Subtype.val key

end RelativeProjPoints

/-! ### The domain of definition and the induced point, at a scheme point of the base -/

section Pointwise

variable (dP : RelativeProjPoints B S hS πP) (dQ : RelativeProjPoints B S hS πQ)
    (ψ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      SheafGradedAlgebraHom (dP.algebra T f) (dQ.algebra T f))

/-- **The domain of definition, tested at a point.** A point of `Q = Proj_X(ℬ)` lying over a
point `f` of `X` at `T` along `r : T' ⟶ T` is *in the domain of definition* of `ψ` when its
section of the scheme-level relative Proj of `ℬ|_T` factors through the open `U(ψ_{T,f})` of
Tag 07ZG. -/
abbrev IsDefinedOn (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) {T' : BigFppfOver B S hS}
    (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f) : Prop :=
  dQ.sectionOfPoint T f r u hu ⁻¹ᵁ (ψ T f).relativeMapDomain = ⊤

/-- The tautological witness that a point of the relative Proj lies over its own image in the
base. -/
theorem comp_eq_self {T : BigFppfOver B S hS} (u : yoneda.obj T ⟶ Q) :
    u ≫ πQ = yoneda.map (𝟙 T) ≫ (u ≫ πQ) := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The domain of definition of `ψ`, as a condition on a point of `Q`.** This is the condition
cutting out the open subspace `U(ψ) ⊆ Q`: the point is tested over its own image in the base. -/
abbrev IsDefined (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q) : Prop :=
  IsDefinedOn dP dQ ψ T (u ≫ πQ) (𝟙 T) u (comp_eq_self u)

/-- A point in the domain of definition stays in it after restriction along any morphism of the
site, when tested over the same point of the base. -/
theorem isDefinedOn_restrict (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' T'' : BigFppfOver B S hS} (r : T' ⟶ T) (r' : T'' ⟶ T') (r'' : T'' ⟶ T)
    (hr : r'' = r' ≫ r) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f)
    (hu' : (yoneda.map r' ≫ u) ≫ πQ = yoneda.map r'' ≫ f)
    (h : IsDefinedOn dP dQ ψ T f r u hu) :
    IsDefinedOn dP dQ ψ T f r'' (yoneda.map r' ≫ u) hu' := by
  subst hr
  change dQ.sectionOfPoint T f (r' ≫ r) (yoneda.map r' ≫ u) hu' ⁻¹ᵁ
    (ψ T f).relativeMapDomain = ⊤
  rw [dQ.sectionOfPoint_restrict T f r r' u hu hu', Scheme.Hom.comp_preimage, h,
    Scheme.Hom.preimage_top]

/-- A point in the domain of definition stays in it after restriction along `r`, when tested
over its own image in the base. -/
private theorem isDefinedOn_restrict_self (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (h : IsDefined dP dQ ψ T u) :
    IsDefinedOn dP dQ ψ T (u ≫ πQ) r (yoneda.map r ≫ u) (Category.assoc _ _ _) :=
  isDefinedOn_restrict dP dQ ψ T (u ≫ πQ) (𝟙 T) r r (Category.comp_id r).symm u
    (comp_eq_self u) (Category.assoc _ _ _) h

/-- The section of the scheme-level relative Proj of `𝒜|_T` built from a point of `Q` in the
domain of definition: the section of `ℬ|_T` factors through `U(ψ_{T,f})`, and the morphism
`r_{ψ_{T,f}}` of Tag 07ZG carries that factorization into `Proj_T(𝒜|_T)`. -/
def pointSection (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) {T' : BigFppfOver B S hS}
    (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f)
    (h : IsDefinedOn dP dQ ψ T f r u hu) :
    {g : (BigFppfOver.toScheme B S hS).obj T' ⟶ (relativeProj (dP.algebra T f)).scheme //
      g ≫ (relativeProj (dP.algebra T f)).toBase = (BigFppfOver.toScheme B S hS).map r} :=
  ⟨liftToOpens (dQ.sectionOfPoint T f r u hu) (ψ T f).relativeMapDomain h ≫
      relativeMapHom (ψ T f), by
    rw [Category.assoc, relativeMapHom_comp_toBase, ← Category.assoc, liftToOpens_comp_ι,
      dQ.sectionOfPoint_comp_toBase]⟩

/-- **The point of `P = Proj_X(𝒜)` induced by a point of `Q` in the domain of definition.** -/
def pointHomOn (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) {T' : BigFppfOver B S hS}
    (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f)
    (h : IsDefinedOn dP dQ ψ T f r u hu) : yoneda.obj T' ⟶ P :=
  ((dP.pointEquivProjOver T f r).symm (pointSection dP dQ ψ T f r u hu h)).1

/-- The induced point of `P` lies over the same point of the base. -/
theorem pointHomOn_comp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f) (h : IsDefinedOn dP dQ ψ T f r u hu) :
    pointHomOn dP dQ ψ T f r u hu h ≫ πP = yoneda.map r ≫ f :=
  ((dP.pointEquivProjOver T f r).symm (pointSection dP dQ ψ T f r u hu h)).2

/-- **The induced point of `P`, read through its section of the scheme-level relative Proj.**
This is the étale-local description of the morphism `r_ψ` of Tag 085F: at a scheme point of the
base it is the morphism `r_{ψ_{T,f}}` of Tag 07ZG. -/
theorem sectionOfPoint_pointHomOn (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f) (h : IsDefinedOn dP dQ ψ T f r u hu) :
    dP.sectionOfPoint T f r (pointHomOn dP dQ ψ T f r u hu h)
        (pointHomOn_comp dP dQ ψ T f r u hu h) =
      liftToOpens (dQ.sectionOfPoint T f r u hu) (ψ T f).relativeMapDomain h ≫
        relativeMapHom (ψ T f) :=
  congrArg Subtype.val
    ((dP.pointEquivProjOver T f r).apply_symm_apply (pointSection dP dQ ψ T f r u hu h))

/-- **The point of `P` induced by a point of `Q` in the domain of definition**, taken over the
point's own image in the base. -/
def pointHomAt (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q)
    (h : IsDefined dP dQ ψ T u) : yoneda.obj T ⟶ P :=
  pointHomOn dP dQ ψ T (u ≫ πQ) (𝟙 T) u (comp_eq_self u) h

/-- The induced point of `P` lies over the same point of the base. -/
theorem pointHomAt_comp (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q)
    (h : IsDefined dP dQ ψ T u) : pointHomAt dP dQ ψ T u h ≫ πP = u ≫ πQ := by
  rw [pointHomAt, pointHomOn_comp, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The induced point of `P` is compatible with restriction in the test object**, at a fixed
point of the base. -/
theorem pointHomOn_restrict (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' T'' : BigFppfOver B S hS} (r : T' ⟶ T) (r' : T'' ⟶ T') (r'' : T'' ⟶ T)
    (hr : r'' = r' ≫ r) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f)
    (hu' : (yoneda.map r' ≫ u) ≫ πQ = yoneda.map r'' ≫ f)
    (h : IsDefinedOn dP dQ ψ T f r u hu)
    (h' : IsDefinedOn dP dQ ψ T f r'' (yoneda.map r' ≫ u) hu') :
    pointHomOn dP dQ ψ T f r'' (yoneda.map r' ≫ u) hu' h' =
      yoneda.map r' ≫ pointHomOn dP dQ ψ T f r u hu h := by
  subst hr
  have hv : (yoneda.map r' ≫ pointHomOn dP dQ ψ T f r u hu h) ≫ πP =
      yoneda.map (r' ≫ r) ≫ f := by
    rw [Category.assoc, pointHomOn_comp, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
  refine dP.eq_of_sectionOfPoint_eq T f (r' ≫ r)
    (pointHomOn dP dQ ψ T f (r' ≫ r) (yoneda.map r' ≫ u) hu' h')
    (yoneda.map r' ≫ pointHomOn dP dQ ψ T f r u hu h)
    (pointHomOn_comp dP dQ ψ T f (r' ≫ r) (yoneda.map r' ≫ u) hu' h') hv ?_
  rw [sectionOfPoint_pointHomOn, dP.sectionOfPoint_restrict T f r r'
      (pointHomOn dP dQ ψ T f r u hu h) (pointHomOn_comp dP dQ ψ T f r u hu h) hv,
    sectionOfPoint_pointHomOn, ← Category.assoc]
  refine congrArg (fun k => k ≫ relativeMapHom (ψ T f)) ?_
  refine (liftToOpens_unique _ _ h' _ ?_).symm
  rw [Category.assoc, liftToOpens_comp_ι, dQ.sectionOfPoint_restrict T f r r' u hu hu']

/-- The domain of definition does not depend on the chosen name of the point of the base. -/
theorem isDefinedOn_congr_base (T : BigFppfOver B S hS) (f f' : yoneda.obj T ⟶ X)
    (hff : f = f') {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f) (hu' : u ≫ πQ = yoneda.map r ≫ f') :
    IsDefinedOn dP dQ ψ T f r u hu ↔ IsDefinedOn dP dQ ψ T f' r u hu' := by
  subst hff
  rfl

/-- The induced point of `P` does not depend on the chosen name of the point of the base. -/
theorem pointHomOn_congr_base (T : BigFppfOver B S hS) (f f' : yoneda.obj T ⟶ X)
    (hff : f = f') {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f) (hu' : u ≫ πQ = yoneda.map r ≫ f')
    (h : IsDefinedOn dP dQ ψ T f r u hu) (h' : IsDefinedOn dP dQ ψ T f' r u hu') :
    pointHomOn dP dQ ψ T f r u hu h = pointHomOn dP dQ ψ T f' r u hu' h' := by
  subst hff
  rfl

/-- The induced point of `P` depends only on the point of `Q`, not on the witness that it is in
the domain of definition. -/
theorem pointHomAt_congr (T : BigFppfOver B S hS) (u v : yoneda.obj T ⟶ Q) (huv : u = v)
    (hu : IsDefined dP dQ ψ T u) (hv : IsDefined dP dQ ψ T v) :
    pointHomAt dP dQ ψ T u hu = pointHomAt dP dQ ψ T v hv := by
  subst huv
  rfl

end Pointwise

/-! ### The map of graded algebras, over the scheme points of the base -/

section Space

variable {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}

/-- **A map `ψ : 𝒜 ⟶ ℬ` of quasi-coherent graded `𝒪_X`-algebras, read over the scheme points of
the base.**

For every object `T` of the site and every `T`-point `f` of `X` the restriction `ψ|_T` is a
homomorphism of the quasi-coherent graded algebras on the scheme of `T` that the two relative
Proj presentations supply, and the two remaining fields say that the resulting data is
compatible with restriction in the test object: the open `U(ψ|_T)` and the morphism `r_{ψ|_T}`
of Tag 07ZG computed at a point of `X` agree with the ones computed after restriction.

That compatibility is the canonicity of the identifications `Proj_Z(g^*𝒜) = Z ×_X Proj_X(𝒜)` of
Stacks 084B: those identifications are compatible with a composite `Z' ⟶ Z ⟶ X`, and the two
fields are that compatibility transported to the open and to the morphism Tag 07ZG attaches to
the restricted homomorphism.  It is exactly what the proof of Tag 085F uses, and it cannot be
derived from `AlgebraicGeometry.Space.RelativeProjPoints` alone: that structure gives a graded
algebra at each point of the base and no comparison between the algebras at a point and at its
restriction.  The inverse image of a `SheafGradedAlgebra` along a morphism of schemes is
available (`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.pullback`), but the
algebras of a `RelativeProjPoints` are a field of the structure rather than inverse images of one
another, so no comparison between them follows from it. -/
structure RelativeProjHomPoints (dP : RelativeProjPoints B S hS πP)
    (dQ : RelativeProjPoints B S hS πQ) where
  /-- The restriction of `ψ` to a scheme point of the base. -/
  hom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    SheafGradedAlgebraHom (dP.algebra T f) (dQ.algebra T f)
  /-- The open `U(ψ|_T)` of Tag 07ZG is compatible with restriction in the test object. -/
  isDefinedOn_iff (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
      {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
      (hu : u ≫ πQ = yoneda.map r ≫ f) :
    IsDefinedOn dP dQ hom T f r u hu ↔ IsDefined dP dQ hom T' u
  /-- The morphism `r_{ψ|_T}` of Tag 07ZG is compatible with restriction in the test object. -/
  pointHomOn_eq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
      {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
      (hu : u ≫ πQ = yoneda.map r ≫ f) (h : IsDefinedOn dP dQ hom T f r u hu) :
    pointHomOn dP dQ hom T f r u hu h =
      pointHomAt dP dQ hom T' u ((isDefinedOn_iff T f r u hu).1 h)

namespace RelativeProjHomPoints

variable (hψ : RelativeProjHomPoints dP dQ)

/-- The domain of definition is stable under restriction of the test object. -/
theorem isDefined_restrict (T T' : BigFppfOver B S hS) (r : T' ⟶ T) (u : yoneda.obj T ⟶ Q)
    (h : IsDefined dP dQ hψ.hom T u) : IsDefined dP dQ hψ.hom T' (yoneda.map r ≫ u) :=
  (hψ.isDefinedOn_iff T (u ≫ πQ) r (yoneda.map r ≫ u) (Category.assoc _ _ _)).1
    (isDefinedOn_restrict_self dP dQ hψ.hom T u r h)

/-- **The induced point of `P` is compatible with restriction of the test object.** This is what
makes the induced points into a morphism of algebraic spaces. -/
theorem pointHomAt_restrict (T T' : BigFppfOver B S hS) (r : T' ⟶ T) (u : yoneda.obj T ⟶ Q)
    (h : IsDefined dP dQ hψ.hom T u)
    (h' : IsDefined dP dQ hψ.hom T' (yoneda.map r ≫ u)) :
    pointHomAt dP dQ hψ.hom T' (yoneda.map r ≫ u) h' =
      yoneda.map r ≫ pointHomAt dP dQ hψ.hom T u h := by
  have hd := isDefinedOn_restrict_self dP dQ hψ.hom T u r h
  rw [← hψ.pointHomOn_eq T (u ≫ πQ) r (yoneda.map r ≫ u) (Category.assoc _ _ _) hd]
  exact pointHomOn_restrict dP dQ hψ.hom T (u ≫ πQ) (𝟙 T) r r (Category.comp_id r).symm u
    (comp_eq_self u) (Category.assoc _ _ _) h hd

/-- The induced point of `P` is compatible with restriction of the test object, stated for a
point of `Q` propositionally equal to a restriction. -/
theorem pointHomAt_restrict' (T T' : BigFppfOver B S hS) (r : T' ⟶ T) (u : yoneda.obj T ⟶ Q)
    (v : yoneda.obj T' ⟶ Q) (hv : v = yoneda.map r ≫ u)
    (h : IsDefined dP dQ hψ.hom T u) (h' : IsDefined dP dQ hψ.hom T' v) :
    pointHomAt dP dQ hψ.hom T' v h' = yoneda.map r ≫ pointHomAt dP dQ hψ.hom T u h := by
  subst hv
  exact hψ.pointHomAt_restrict T T' r u h h'

/-- **Tag 085F, the open subspace `U(ψ) ⊆ Q`.** The subfunctor of `Q = Proj_X(ℬ)` whose
`T`-points are the points lying in the domain of definition of `ψ`: those whose section of the
scheme-level relative Proj of `ℬ|_T` factors through the open `U(ψ|_T)` of Tag 07ZG. -/
@[stacks 085F "the open subspace U(ψ) of Q"]
def relativeMapSubfunctor : Subfunctor Q where
  obj Y := {x | IsDefined dP dQ hψ.hom Y.unop (yonedaEquiv.symm x)}
  map {Y Z} i x hx := by
    change IsDefined dP dQ hψ.hom Z.unop (yonedaEquiv.symm (Q.map i x))
    rw [yonedaEquiv_symm_map]
    exact hψ.isDefined_restrict Y.unop Z.unop i.unop (yonedaEquiv.symm x) hx

/-- Membership in the subfunctor `U(ψ)`, unfolded. -/
theorem mem_relativeMapSubfunctor_obj {Y : (BigFppfOver B S hS)ᵒᵖ} (y : Q.obj Y) :
    y ∈ hψ.relativeMapSubfunctor.obj Y ↔
      IsDefined dP dQ hψ.hom Y.unop (yonedaEquiv.symm y) :=
  Iff.rfl

/-- **Tag 085F's étale-local description of the open subspace.** A point of `Q` lying over a
point `f` of the base at `T`, along any `r : T' ⟶ T`, belongs to `U(ψ)` exactly when its section
of the scheme-level relative Proj of `ℬ|_T` factors through the open `U(ψ|_T)` of Tag 07ZG.

Read at an étale chart `W` of `X` and `r = 𝟙`, this is the assertion `U(ψ) ×_X W = U(ψ|_W)` of
the source. -/
@[stacks 085F "the étale-local description of the open subspace U(ψ)"]
theorem mem_relativeMapSubfunctor_iff (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f) :
    yonedaEquiv u ∈ hψ.relativeMapSubfunctor.obj (op T') ↔
      dQ.sectionOfPoint T f r u hu ⁻¹ᵁ (hψ.hom T f).relativeMapDomain = ⊤ := by
  change IsDefined dP dQ hψ.hom T' (yonedaEquiv.symm (yonedaEquiv u)) ↔ _
  rw [Equiv.symm_apply_apply]
  exact (hψ.isDefinedOn_iff T f r u hu).symm

/-- Membership in `U(ψ)`, for a point tested over its own image in the base. -/
theorem mem_relativeMapSubfunctor_iff' (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q) :
    yonedaEquiv u ∈ hψ.relativeMapSubfunctor.obj (op T) ↔ IsDefined dP dQ hψ.hom T u := by
  change IsDefined dP dQ hψ.hom T (yonedaEquiv.symm (yonedaEquiv u)) ↔ _
  rw [Equiv.symm_apply_apply]

/-- **Tag 085F, the morphism `r_ψ : U(ψ) ⟶ P` of algebraic spaces.** On a `T`-point of `U(ψ)`
it is the point of `P = Proj_X(𝒜)` whose section of the scheme-level relative Proj of `𝒜|_T` is
obtained from the section of `ℬ|_T` by the morphism `r_{ψ|_T}` of Tag 07ZG. -/
@[stacks 085F "the morphism r_ψ : U(ψ) ⟶ P"]
def relativeMapSpaceHom : hψ.relativeMapSubfunctor.toFunctor ⟶ P where
  app Y := ↾fun x => yonedaEquiv (pointHomAt dP dQ hψ.hom Y.unop (yonedaEquiv.symm x.1) x.2)
  naturality Y Z i := by
    ext x
    refine Eq.trans ?_ (yonedaEquiv_naturality'
      (pointHomAt dP dQ hψ.hom Y.unop (yonedaEquiv.symm x.1) x.2) i).symm
    exact congrArg yonedaEquiv (hψ.pointHomAt_restrict' Y.unop Z.unop i.unop
      (yonedaEquiv.symm x.1) (yonedaEquiv.symm (Q.map i x.1)) (yonedaEquiv_symm_map i x.1)
      x.2 _)

/-- **Tag 085F: the morphism `r_ψ` is a morphism over `X`.** -/
@[stacks 085F "the morphism r_ψ is a morphism over X"]
theorem relativeMapSpaceHom_comp :
    hψ.relativeMapSpaceHom ≫ πP = hψ.relativeMapSubfunctor.ι ≫ πQ := by
  ext Y x
  obtain ⟨y, hy⟩ := x
  have hy' : IsDefined dP dQ hψ.hom Y.unop (yonedaEquiv.symm y) :=
    (hψ.mem_relativeMapSubfunctor_obj y).1 hy
  change πP.app Y (yonedaEquiv (pointHomAt dP dQ hψ.hom Y.unop
      (yonedaEquiv.symm y) hy')) = πQ.app Y y
  rw [← yonedaEquiv_comp, pointHomAt_comp, yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- **Tag 085F's étale-local description of the morphism `r_ψ`.** On a point of `U(ψ)` lying
over a point `f` of the base at `T`, along any `r : T' ⟶ T`, the morphism `r_ψ` produces the
point of `P` whose section of the scheme-level relative Proj of `𝒜|_T` is the one the morphism
`r_{ψ|_T}` of Tag 07ZG produces; that last identification is
`AlgebraicGeometry.Space.sectionOfPoint_pointHomOn`.

Read at an étale chart `W` of `X` and `r = 𝟙`, this is the assertion that `r_ψ` restricted to
`U(ψ) ×_X W` is the morphism `r_{ψ|_W}` of the source. -/
@[stacks 085F "the étale-local description of the morphism r_ψ"]
theorem app_relativeMapSpaceHom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f) (hd : IsDefinedOn dP dQ hψ.hom T f r u hu)
    (hx : yonedaEquiv u ∈ hψ.relativeMapSubfunctor.obj (op T')) :
    hψ.relativeMapSpaceHom.app (op T') ⟨yonedaEquiv u, hx⟩ =
      yonedaEquiv (pointHomOn dP dQ hψ.hom T f r u hu hd) := by
  change yonedaEquiv (pointHomAt dP dQ hψ.hom T' (yonedaEquiv.symm (yonedaEquiv u)) hx) = _
  refine congrArg yonedaEquiv (Eq.trans ?_ (hψ.pointHomOn_eq T f r u hu hd).symm)
  exact pointHomAt_congr dP dQ hψ.hom T' _ u (Equiv.symm_apply_apply yonedaEquiv u) hx _

/-- **Tag 085F's description determines the open subspace.** A subfunctor of `Q` whose points
are exactly the points in the domain of definition of `ψ` is `U(ψ)`. -/
@[stacks 085F "the étale-local description determines U(ψ)"]
theorem relativeMapSubfunctor_unique (G : Subfunctor Q)
    (hG : ∀ (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q),
      yonedaEquiv u ∈ G.obj (op T) ↔ IsDefined dP dQ hψ.hom T u) :
    G = hψ.relativeMapSubfunctor := by
  have h : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ) (y : Q.obj Y),
      y ∈ G.obj Y ↔ y ∈ hψ.relativeMapSubfunctor.obj Y := fun Y y => by
    rw [hψ.mem_relativeMapSubfunctor_obj]
    simpa using hG Y.unop (yonedaEquiv.symm y)
  exact le_antisymm (fun Y y hy => (h Y y).1 hy) (fun Y y hy => (h Y y).2 hy)

/-- **Tag 085F's description determines the morphism.** A morphism out of `U(ψ)` whose value at
every point is the point of `P` the scheme-level morphism `r_{ψ|_T}` of Tag 07ZG produces is
`r_ψ`. -/
@[stacks 085F "the étale-local description determines r_ψ"]
theorem relativeMapSpaceHom_unique (k : hψ.relativeMapSubfunctor.toFunctor ⟶ P)
    (hk : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ) (y : Q.obj Y)
      (hy : y ∈ hψ.relativeMapSubfunctor.obj Y),
      k.app Y ⟨y, hy⟩ = yonedaEquiv (pointHomAt dP dQ hψ.hom Y.unop (yonedaEquiv.symm y)
        ((hψ.mem_relativeMapSubfunctor_obj y).1 hy))) :
    k = hψ.relativeMapSpaceHom := by
  ext Y x
  obtain ⟨y, hy⟩ := x
  exact hk Y y hy

/-! ### `U(ψ)` is an open subspace -/

/-- **The open subscheme of a scheme point of `Q` on which `ψ` is defined.** For a point `u` of
`Q` at `T` this is the inverse image, under the section of the scheme-level relative Proj of
`ℬ|_T` attached to `u`, of the open `U(ψ|_T)` of Tag 07ZG. -/
def definedLocus (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q) :
    ((BigFppfOver.toScheme B S hS).obj T).Opens :=
  dQ.sectionOfPoint T (u ≫ πQ) (𝟙 T) u (comp_eq_self u) ⁻¹ᵁ
    (hψ.hom T (u ≫ πQ)).relativeMapDomain

/-- A point of `Q` is in the domain of definition exactly when its defined locus is
everything. -/
theorem isDefined_iff_definedLocus (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q) :
    IsDefined dP dQ hψ.hom T u ↔ hψ.definedLocus T u = ⊤ :=
  Iff.rfl

/-- **The defined locus computes membership of every restriction of a point.** A restriction of
`u` along `r : T' ⟶ T` lies in `U(ψ)` exactly when `r` maps into the defined locus of `u`. -/
theorem isDefined_restrict_iff (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) :
    IsDefined dP dQ hψ.hom T' (yoneda.map r ≫ u) ↔
      Set.range ((BigFppfOver.toScheme B S hS).map r) ⊆ (hψ.definedLocus T u : Set _) := by
  rw [← preimage_eq_top_iff]
  change _ ↔ (BigFppfOver.toScheme B S hS).map r ⁻¹ᵁ
    (dQ.sectionOfPoint T (u ≫ πQ) (𝟙 T) u (comp_eq_self u) ⁻¹ᵁ
      (hψ.hom T (u ≫ πQ)).relativeMapDomain) = ⊤
  rw [← Scheme.Hom.comp_preimage, ← dQ.sectionOfPoint_restrict' T (u ≫ πQ) (𝟙 T) r r
    (Category.comp_id r).symm u (comp_eq_self u) (Category.assoc _ _ _)]
  exact (hψ.isDefinedOn_iff T (u ≫ πQ) r (yoneda.map r ≫ u) (Category.assoc _ _ _)).symm

/-- The morphism from a representable presheaf determined by a section is the restriction of
the morphism the section comes from. -/
theorem yonedaEquiv_symm_app_eq {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ Q)
    {Y : (BigFppfOver B S hS)ᵒᵖ} (f : Y.unop ⟶ A) :
    yonedaEquiv.symm (q.app Y f) = yoneda.map f ≫ q := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- **The inverse image of `U(ψ)` along a scheme point of `Q` is an open subscheme of that
point.** It is the open subscheme cut out by the defined locus. -/
theorem range_yoneda_map_eq_preimage_relativeMapSubfunctor (A : BigFppfOver B S hS)
    (q : yoneda.obj A ⟶ Q) {b : BigFppfOver B S hS} (i : b ⟶ A)
    (hirange : Set.range ((BigFppfOver.toScheme B S hS).map i) =
      (hψ.definedLocus A q : Set _))
    (hiuniv : ∀ {A' : BigFppfOver B S hS} (g : A' ⟶ A),
      Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆ (hψ.definedLocus A q : Set _) →
        ∃ h : A' ⟶ b, h ≫ i = g) :
    Subfunctor.range (yoneda.map i) = hψ.relativeMapSubfunctor.preimage q := by
  ext Y f
  have hmem : ∀ g : Y.unop ⟶ A, (q.app Y g ∈ hψ.relativeMapSubfunctor.obj Y ↔
      Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆ (hψ.definedLocus A q : Set _)) := by
    intro g
    rw [hψ.mem_relativeMapSubfunctor_obj, yonedaEquiv_symm_app_eq q g]
    exact hψ.isDefined_restrict_iff A q g
  constructor
  · rintro ⟨g, rfl⟩
    refine (hmem _).2 ?_
    rintro z ⟨y, rfl⟩
    rw [← hirange]
    refine ⟨(BigFppfOver.toScheme B S hS).map g y, ?_⟩
    rw [show (yoneda.map i).app Y g = g ≫ i from rfl, CategoryTheory.Functor.map_comp,
      Scheme.Hom.comp_apply]
  · exact fun hf => (hiuniv f ((hmem f).1 hf)).imp fun _ hh => hh

/-- **Tag 085F: the inclusion `U(ψ) ⟶ Q` is an open immersion of algebraic spaces.** Over a
scheme point of `Q` the inverse image of `U(ψ)` is the open subscheme cut out by the defined
locus, which is again an object of the site. -/
theorem presheaf_isOpenImmersion_ι_relativeMapSubfunctor :
    IsOpenImmersion B S hS hψ.relativeMapSubfunctor.ι := by
  have hRI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists ?_
  intro A q
  obtain ⟨b, i, hi, hirange, hiuniv⟩ := exists_restrict_bigFppfOver A (hψ.definedLocus A q)
  have hmono : Mono i := inverseImage_isOpenImmersion_le_monomorphisms i hi
  have hkey : Subfunctor.range (yoneda.map i) = hψ.relativeMapSubfunctor.preimage q :=
    hψ.range_yoneda_map_eq_preimage_relativeMapSubfunctor A q i hirange hiuniv
  have hsq := Subfunctor.isPullback_fromPreimage hψ.relativeMapSubfunctor q
  have hiso := Subfunctor.isIso_lift hkey.le hkey.ge
  refine ⟨b, Subfunctor.lift (yoneda.map i) hkey.le ≫
    hψ.relativeMapSubfunctor.fromPreimage q, i, ?_, hi⟩
  refine IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, hψ.relativeMapSubfunctor.fromPreimage_ι q,
      ← Category.assoc, Subfunctor.lift_ι]⟩
    (asIso (Subfunctor.lift (yoneda.map i) hkey.le) ≪≫ hsq.isoPullback) ?_ ?_
  · simp [hsq.isoPullback_hom_fst]
  · simp [hsq.isoPullback_hom_snd]

/-- **`U(ψ)` is an fppf sheaf.** Its defining condition is local on the source, because a
covering sieve of the big fppf site over `S` is jointly surjective on points. -/
theorem isSheaf_relativeMapSubfunctor
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      hψ.relativeMapSubfunctor.toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 hQ)]
  intro Y s hs
  change hψ.definedLocus Y.unop (yonedaEquiv.symm s) = ⊤
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => ?_)
  obtain ⟨A', h, hh, hmem⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hs z
  have h1 : IsDefined dP dQ hψ.hom A' (yoneda.map h ≫ yonedaEquiv.symm s) := by
    have h0 := (hψ.mem_relativeMapSubfunctor_obj (Q.map h.op s)).1 hh
    rwa [yonedaEquiv_symm_map h.op s] at h0
  exact (hψ.isDefined_restrict_iff Y.unop (yonedaEquiv.symm s) h).1 h1 hmem

/-- **`U(ψ)` is an algebraic space over `S`**: it is a sheaf and its inclusion into the
algebraic space `Q` is representable. -/
theorem isAlgebraicSpace_relativeMapSubfunctor (hQ : IsAlgebraicSpace B S hS Q) :
    IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor :=
  _root_.AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS
    hψ.relativeMapSubfunctor.ι
    hψ.presheaf_isOpenImmersion_ι_relativeMapSubfunctor.rep hQ

/-- **Tag 085F: `U(ψ)` is an open subspace of `Q = Proj_X(ℬ)`.** -/
@[stacks 085F "U(ψ) is an open subspace of Q"]
theorem isOpenSubspace_relativeMapSubfunctor (hQ : IsAlgebraicSpace B S hS Q) :
    IsOpenSubspace B S hS hψ.relativeMapSubfunctor :=
  ⟨hψ.isAlgebraicSpace_relativeMapSubfunctor hQ,
    hψ.presheaf_isOpenImmersion_ι_relativeMapSubfunctor⟩

end RelativeProjHomPoints

/-! ### The twists of the relative Proj, and the map `θ` -/

section Twists

open Stacks.AlgebraicGeometry.Tag07ZGTwist

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πY : Y ⟶ X}

/-- **The `n`-th twist `𝒪_P(n)` of the relative Proj of an algebraic space, over a scheme point
of the base.**  The presentation `AlgebraicGeometry.Space.RelativeProjPoints` presents
`P = Proj_X(𝒜)` by its base changes to the scheme points of `X`, and over the point `(T, f)` that
base change is the scheme-level relative Proj of the restricted algebra `𝒜|_T`; the twist there is
the one Tag 01NR glues, `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist`.

This is the base-change clause of Tag 084D read at `(T, f)`, and it is the object the `θ` of
Tag 085F maps between.  It is not the same thing as a sheaf on `P`: see the module docstring. -/
abbrev RelativeProjPoints.pointTwist (d : RelativeProjPoints B S hS πY)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ) :
    (relativeProj (d.algebra T f)).scheme.Modules :=
  relativeTwist (d.algebra T f) n

/-- **`𝒪_P(n)` read on the étale chart `T ×_X P` of `P`.**  The presentation supplies the base
change `T ×_X P` as an *object of the site*, `AlgebraicGeometry.Space.RelativeProjPoints.fibre`,
together with the identification of its scheme with the scheme-level relative Proj of `𝒜|_T`; this
is `AlgebraicGeometry.Space.RelativeProjPoints.pointTwist` transported along that identification.

Taken over a family of points `(T, f)` covering `X`, the morphisms
`AlgebraicGeometry.Space.RelativeProjPoints.fibreToSpace` are an étale cover of `P`, so this is
the restriction of `𝒪_P(n)` to a chart of `P` itself. -/
def RelativeProjPoints.fibreTwist (d : RelativeProjPoints B S hS πY)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ) :
    ((BigFppfOver.toScheme B S hS).obj (d.fibre T f)).Modules :=
  (Scheme.Modules.pullback (d.fibreIso T f).hom).obj (d.pointTwist T f n)

namespace RelativeProjHomPoints

/-- **Tag 085F, the third component: the map `θ` on the twists, over a scheme point of the
base.**  For every `n : ℤ`,

`θ_n : r_ψ^*𝒪_P(n) ⟶ 𝒪_Q(n)|_{U(ψ)}`,

read over the scheme point `(T, f)` of `X` as the map Tag 07ZG attaches to the restriction
`ψ|_{T,f}` — a *single* morphism of sheaves of modules on the whole of `U(ψ|_{T,f})`, namely
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap`.

This is `θ` itself, not a chart-by-chart approximation of it: Tag 085F *characterizes* `θ` by the
property that its restriction to `U(ψ) ×_X W` is the scheme-level `θ` of `ψ|_W` for every scheme
`W` étale over `X`, and that restriction is exactly what this is.  The characterization is
`AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap_chart` and
`…relativeTwistSpaceMap_unique`. -/
@[stacks 085F "the third component: the map θ on the n-th twists, over a scheme point of the
base — the scheme-level θ of Tag 07ZG for the restricted map, which is what the tag's
étale-local characterization of θ asks for"]
abbrev relativeTwistSpaceMap (hψ : RelativeProjHomPoints dP dQ)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ) :
    (Scheme.Modules.pullback (relativeMapHom (hψ.hom T f))).obj (dP.pointTwist T f n) ⟶
      (Scheme.Modules.pullback (hψ.hom T f).relativeMapDomain.ι).obj (dQ.pointTwist T f n) :=
  relativeTwistMap (hψ.hom T f) n

/-- **Tag 085F, the third component as a map of `ℤ`-graded algebras.**  The source asks for `θ`
as a homomorphism

`θ : r_ψ^*(⨁_{d ∈ ℤ} 𝒪_P(d)) ⟶ ⨁_{d ∈ ℤ} 𝒪_{U(ψ)}(d)`

of sheaves of `ℤ`-graded algebras, not only for the degreewise family; over a scheme point of the
base that is `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom`, whose degree-`n`
component is `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap`. -/
@[stacks 085F "the third component as a map of ℤ-graded algebras, over a scheme point of the
base"]
abbrev relativeTwistAlgebraSpaceHom (hψ : RelativeProjHomPoints dP dQ)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :=
  relativeTwistAlgebraHom (hψ.hom T f)

/-- The degreewise components of `θ` are the maps on the twists. -/
theorem relativeTwistAlgebraSpaceHom_app (hψ : RelativeProjHomPoints dP dQ)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ) :
    (hψ.relativeTwistAlgebraSpaceHom T f).app n = hψ.relativeTwistSpaceMap T f n :=
  rfl

/-- **Tag 085F's étale-local description of `θ`.**  Over the piece of `U(ψ|_{T,f})` lying over an
affine open `U` of the scheme point `T` of the base, `θ_n` is Tag 01MY's comparison map for the
induced homomorphism `Γ(U, 𝒜|_T) ⟶ Γ(U, ℬ|_T)` of graded rings of sections, conjugated by the
chart identifications of Tag 01NR.

This is the affine-local reading of the étale-local description; the étale-local description
itself — that `θ` restricted to `U(ψ) ×_X W` is the scheme-level `θ` of `ψ|_W` — holds by
construction, `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap` being that
restriction. -/
@[stacks 085F "the étale-local description of θ, read on the affine charts of a scheme point of
the base"]
theorem relativeTwistSpaceMap_chart (hψ : RelativeProjHomPoints dP dQ)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ)
    (U : ((BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    (Scheme.Modules.pullback (pieceIncl (hψ.hom T f) U)).map (hψ.relativeTwistSpaceMap T f n) =
      relativeTwistChart (hψ.hom T f) n U :=
  relativeTwistMap_chart (hψ.hom T f) n U

/-- **Tag 085F's description determines `θ`.**  A map on the `n`-th twists whose restriction to
the piece over every affine open of the scheme point of the base is Tag 01MY's comparison map
there is `θ_n`. -/
@[stacks 085F "the étale-local description determines θ"]
theorem relativeTwistSpaceMap_unique (hψ : RelativeProjHomPoints dP dQ)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ)
    {θ : (Scheme.Modules.pullback (relativeMapHom (hψ.hom T f))).obj (dP.pointTwist T f n) ⟶
      (Scheme.Modules.pullback (hψ.hom T f).relativeMapDomain.ι).obj (dQ.pointTwist T f n)}
    (hθ : ∀ U : ((BigFppfOver.toScheme B S hS).obj T).affineOpens,
      (Scheme.Modules.pullback (pieceIncl (hψ.hom T f) U)).map θ =
        relativeTwistChart (hψ.hom T f) n U) :
    θ = hψ.relativeTwistSpaceMap T f n :=
  relativeTwistMap_unique (hψ.hom T f) n hθ (relativeTwistMap_chart (hψ.hom T f) n)

end RelativeProjHomPoints

end Twists

end Space

/-! ### Composition, at the level of schemes -/

section SchemeComposition

variable {Z : Scheme.{u}} {A₁ A₂ A₃ : SheafGradedAlgebra Z}
    (φ : SheafGradedAlgebraHom A₁ A₂) (ψ : SheafGradedAlgebraHom A₂ A₃)

open Stacks.AlgebraicGeometry.RelativeProjMapComp

/-- **The domain of definition of a composite, read through the morphism of the outer factor.**
On the open where `ψ` is defined the open `U(ψ ∘ φ)` is the inverse image of `U(φ)` under
`r_ψ`; this is the first assertion of Tag 07ZH, pulled back along a morphism `g` landing in
`U(ψ)`. -/
theorem preimage_relativeMapDomain_comp {Y : Scheme.{u}}
    (g : Y ⟶ (relativeProj A₃).scheme) (h : g ⁻¹ᵁ ψ.relativeMapDomain = ⊤) :
    g ⁻¹ᵁ (ψ.comp φ).relativeMapDomain =
      (liftToOpens g ψ.relativeMapDomain h ≫ relativeMapHom ψ) ⁻¹ᵁ φ.relativeMapDomain := by
  rw [Scheme.Hom.comp_preimage, relativeMapHom_preimage_relativeMapDomain,
    ← Scheme.Hom.comp_preimage, liftToOpens_comp_ι]

/-- A morphism landing in the domain of definition of a composite lands in the domain of
definition of the outer factor. -/
theorem preimage_relativeMapDomain_eq_top_of_comp {Y : Scheme.{u}}
    (g : Y ⟶ (relativeProj A₃).scheme) (h : g ⁻¹ᵁ (ψ.comp φ).relativeMapDomain = ⊤) :
    g ⁻¹ᵁ ψ.relativeMapDomain = ⊤ :=
  top_le_iff.1 (h.ge.trans (Scheme.Hom.preimage_mono g (relativeMapDomain_comp_le φ ψ)))

/-- **The restriction of `r_ψ` to the open attached to the composite.** This is the morphism
`q` of the factorized form of Tag 07ZH's second assertion. -/
def relativeMapCompLift :
    (ψ.comp φ).relativeMapDomain.toScheme ⟶ φ.relativeMapDomain.toScheme :=
  liftToOpens ((relativeProj A₃).scheme.homOfLE (relativeMapDomain_comp_le φ ψ) ≫
      relativeMapHom ψ) φ.relativeMapDomain (by
    rw [Scheme.Hom.comp_preimage, relativeMapHom_preimage_relativeMapDomain,
      ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι, Scheme.Opens.ι_preimage_self])

/-- **Tag 07ZH's second assertion, with the restriction of `r_ψ` named.** -/
theorem relativeMapHom_comp_eq :
    relativeMapHom (ψ.comp φ) = relativeMapCompLift φ ψ ≫ relativeMapHom φ :=
  relativeMapHom_comp' φ ψ (relativeMapCompLift φ ψ) (liftToOpens_comp_ι _ _ _)

/-- **The factorization through the open attached to a composite, followed by the restriction of
`r_ψ`.** This is the comparison that makes Tag 07ZH's second assertion usable pointwise. -/
theorem liftToOpens_comp_relativeMapCompLift {Y : Scheme.{u}}
    (g : Y ⟶ (relativeProj A₃).scheme)
    (hc : g ⁻¹ᵁ (ψ.comp φ).relativeMapDomain = ⊤)
    (hd : g ⁻¹ᵁ ψ.relativeMapDomain = ⊤)
    (hd2 : (liftToOpens g ψ.relativeMapDomain hd ≫ relativeMapHom ψ) ⁻¹ᵁ
      φ.relativeMapDomain = ⊤) :
    liftToOpens g (ψ.comp φ).relativeMapDomain hc ≫ relativeMapCompLift φ ψ =
      liftToOpens (liftToOpens g ψ.relativeMapDomain hd ≫ relativeMapHom ψ)
        φ.relativeMapDomain hd2 := by
  refine liftToOpens_unique (liftToOpens g ψ.relativeMapDomain hd ≫ relativeMapHom ψ)
    φ.relativeMapDomain hd2 _ ?_
  rw [Category.assoc, relativeMapCompLift, liftToOpens_comp_ι, ← Category.assoc,
    liftToOpens_comp_homOfLE g _ _ (relativeMapDomain_comp_le φ ψ) hc hd]

end SchemeComposition

/-! ### Tag 085G: composition of the morphisms of relative Proj -/

section Composition

variable {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πR : R ⟶ X}
    {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
    {dR : RelativeProjPoints B S hS πR}

/-- The composite of two maps of quasi-coherent graded algebras, at each scheme point of the
base. -/
def homComp
    (φ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      SheafGradedAlgebraHom (dP.algebra T f) (dQ.algebra T f))
    (ψ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      SheafGradedAlgebraHom (dQ.algebra T f) (dR.algebra T f))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    SheafGradedAlgebraHom (dP.algebra T f) (dR.algebra T f) :=
  (ψ T f).comp (φ T f)

variable (φ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      SheafGradedAlgebraHom (dP.algebra T f) (dQ.algebra T f))
    (ψ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      SheafGradedAlgebraHom (dQ.algebra T f) (dR.algebra T f))

/-- A point in the domain of definition of a composite is in the domain of definition of the
outer factor. -/
theorem isDefinedOn_of_homComp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ R)
    (hu : u ≫ πR = yoneda.map r ≫ f) (h : IsDefinedOn dP dR (homComp φ ψ) T f r u hu) :
    IsDefinedOn dQ dR ψ T f r u hu :=
  preimage_relativeMapDomain_eq_top_of_comp (φ T f) (ψ T f) _ h

/-- **The first assertion of Tag 085G, at a scheme point of the base.** A point of
`R = Proj_X(𝒞)` in the domain of definition of `ψ` is in the domain of definition of `ψ ∘ φ`
exactly when the point of `Q` it induces is in the domain of definition of `φ`. -/
theorem isDefinedOn_homComp_iff (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ R)
    (hu : u ≫ πR = yoneda.map r ≫ f) (hd : IsDefinedOn dQ dR ψ T f r u hu) :
    IsDefinedOn dP dR (homComp φ ψ) T f r u hu ↔
      IsDefinedOn dP dQ φ T f r (pointHomOn dQ dR ψ T f r u hu hd)
        (pointHomOn_comp dQ dR ψ T f r u hu hd) := by
  change dR.sectionOfPoint T f r u hu ⁻¹ᵁ ((ψ T f).comp (φ T f)).relativeMapDomain = ⊤ ↔
    dQ.sectionOfPoint T f r (pointHomOn dQ dR ψ T f r u hu hd)
        (pointHomOn_comp dQ dR ψ T f r u hu hd) ⁻¹ᵁ (φ T f).relativeMapDomain = ⊤
  rw [sectionOfPoint_pointHomOn dQ dR ψ T f r u hu hd,
    preimage_relativeMapDomain_comp (φ T f) (ψ T f) (dR.sectionOfPoint T f r u hu) hd]

/-- **The second assertion of Tag 085G, at a scheme point of the base.** The point of `P`
induced by `ψ ∘ φ` is the point induced by `φ` from the point induced by `ψ`. -/
theorem pointHomOn_homComp_eq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ R)
    (hu : u ≫ πR = yoneda.map r ≫ f) (hd : IsDefinedOn dQ dR ψ T f r u hu)
    (hc : IsDefinedOn dP dR (homComp φ ψ) T f r u hu)
    (hd2 : IsDefinedOn dP dQ φ T f r (pointHomOn dQ dR ψ T f r u hu hd)
      (pointHomOn_comp dQ dR ψ T f r u hu hd)) :
    pointHomOn dP dR (homComp φ ψ) T f r u hu hc =
      pointHomOn dP dQ φ T f r (pointHomOn dQ dR ψ T f r u hu hd)
        (pointHomOn_comp dQ dR ψ T f r u hu hd) hd2 := by
  refine dP.eq_of_sectionOfPoint_eq T f r _ _
    (pointHomOn_comp dP dR (homComp φ ψ) T f r u hu hc)
    (pointHomOn_comp dP dQ φ T f r _ (pointHomOn_comp dQ dR ψ T f r u hu hd) hd2) ?_
  have hd2' : (liftToOpens (dR.sectionOfPoint T f r u hu) (ψ T f).relativeMapDomain hd ≫
      relativeMapHom (ψ T f)) ⁻¹ᵁ (φ T f).relativeMapDomain = ⊤ := by
    rwa [← sectionOfPoint_pointHomOn dQ dR ψ T f r u hu hd]
  rw [sectionOfPoint_pointHomOn dP dR (homComp φ ψ) T f r u hu hc,
    sectionOfPoint_pointHomOn dP dQ φ T f r _ (pointHomOn_comp dQ dR ψ T f r u hu hd) hd2]
  change liftToOpens (dR.sectionOfPoint T f r u hu)
      ((ψ T f).comp (φ T f)).relativeMapDomain hc ≫
      relativeMapHom ((ψ T f).comp (φ T f)) = _
  rw [relativeMapHom_comp_eq (φ T f) (ψ T f), ← Category.assoc,
    liftToOpens_comp_relativeMapCompLift (φ T f) (ψ T f) (dR.sectionOfPoint T f r u hu)
      hc hd hd2',
    liftToOpens_congr (dQ.sectionOfPoint T f r (pointHomOn dQ dR ψ T f r u hu hd)
        (pointHomOn_comp dQ dR ψ T f r u hu hd)) _
      (sectionOfPoint_pointHomOn dQ dR ψ T f r u hu hd) (φ T f).relativeMapDomain hd2 hd2']

/-- A point in the domain of definition of a composite is in the domain of definition of the
outer factor, tested over its own image in the base. -/
theorem isDefined_of_homComp (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ R)
    (h : IsDefined dP dR (homComp φ ψ) T u) : IsDefined dQ dR ψ T u :=
  isDefinedOn_of_homComp φ ψ T (u ≫ πR) (𝟙 T) u (comp_eq_self u) h

/-- **The first assertion of Tag 085G, tested at a point over its own image in the base.** -/
theorem isDefined_homComp_iff (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ R)
    (hd : IsDefined dQ dR ψ T u) :
    IsDefined dP dR (homComp φ ψ) T u ↔
      IsDefined dP dQ φ T (pointHomAt dQ dR ψ T u hd) := by
  refine (isDefinedOn_homComp_iff φ ψ T (u ≫ πR) (𝟙 T) u (comp_eq_self u) hd).trans ?_
  exact isDefinedOn_congr_base dP dQ φ T (u ≫ πR) (pointHomAt dQ dR ψ T u hd ≫ πQ)
    (pointHomAt_comp dQ dR ψ T u hd).symm (𝟙 T) (pointHomAt dQ dR ψ T u hd)
    (pointHomOn_comp dQ dR ψ T (u ≫ πR) (𝟙 T) u (comp_eq_self u) hd)
    (comp_eq_self (pointHomAt dQ dR ψ T u hd))

/-- **The second assertion of Tag 085G, tested at a point over its own image in the base.** -/
theorem pointHomAt_homComp_eq (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ R)
    (hd : IsDefined dQ dR ψ T u) (hc : IsDefined dP dR (homComp φ ψ) T u)
    (hc2 : IsDefined dP dQ φ T (pointHomAt dQ dR ψ T u hd)) :
    pointHomAt dP dR (homComp φ ψ) T u hc =
      pointHomAt dP dQ φ T (pointHomAt dQ dR ψ T u hd) hc2 := by
  have hu : pointHomAt dQ dR ψ T u hd ≫ πQ = yoneda.map (𝟙 T) ≫ (u ≫ πR) :=
    pointHomOn_comp dQ dR ψ T (u ≫ πR) (𝟙 T) u (comp_eq_self u) hd
  have hff : u ≫ πR = pointHomAt dQ dR ψ T u hd ≫ πQ :=
    (pointHomAt_comp dQ dR ψ T u hd).symm
  have hd2 : IsDefinedOn dP dQ φ T (u ≫ πR) (𝟙 T) (pointHomAt dQ dR ψ T u hd) hu :=
    (isDefinedOn_congr_base dP dQ φ T (u ≫ πR) _ hff (𝟙 T) (pointHomAt dQ dR ψ T u hd) hu
      (comp_eq_self _)).2 hc2
  refine (pointHomOn_homComp_eq φ ψ T (u ≫ πR) (𝟙 T) u (comp_eq_self u) hd hc hd2).trans ?_
  exact pointHomOn_congr_base dP dQ φ T (u ≫ πR) _ hff (𝟙 T) (pointHomAt dQ dR ψ T u hd) hu
    (comp_eq_self _) hd2 hc2

namespace RelativeProjHomPoints

variable (hφ : RelativeProjHomPoints dP dQ) (hψ : RelativeProjHomPoints dQ dR)

/-- The domain of definition of a composite is compatible with restriction in the test
object. -/
theorem comp_isDefinedOn_iff (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ R)
    (hu : u ≫ πR = yoneda.map r ≫ f) :
    IsDefinedOn dP dR (homComp hφ.hom hψ.hom) T f r u hu ↔
      IsDefined dP dR (homComp hφ.hom hψ.hom) T' u := by
  constructor
  · intro hc
    have hd : IsDefinedOn dQ dR hψ.hom T f r u hu :=
      isDefinedOn_of_homComp hφ.hom hψ.hom T f r u hu hc
    have hd' := (hψ.isDefinedOn_iff T f r u hu).1 hd
    have hv := (isDefinedOn_homComp_iff hφ.hom hψ.hom T f r u hu hd).1 hc
    have hv' := (hφ.isDefinedOn_iff T f r (pointHomOn dQ dR hψ.hom T f r u hu hd)
      (pointHomOn_comp dQ dR hψ.hom T f r u hu hd)).1 hv
    rw [hψ.pointHomOn_eq T f r u hu hd] at hv'
    exact (isDefined_homComp_iff hφ.hom hψ.hom T' u hd').2 hv'
  · intro hc'
    have hd' : IsDefined dQ dR hψ.hom T' u := isDefined_of_homComp hφ.hom hψ.hom T' u hc'
    have hd : IsDefinedOn dQ dR hψ.hom T f r u hu := (hψ.isDefinedOn_iff T f r u hu).2 hd'
    have hv' := (isDefined_homComp_iff hφ.hom hψ.hom T' u hd').1 hc'
    rw [← hψ.pointHomOn_eq T f r u hu hd] at hv'
    exact (isDefinedOn_homComp_iff hφ.hom hψ.hom T f r u hu hd).2
      ((hφ.isDefinedOn_iff T f r (pointHomOn dQ dR hψ.hom T f r u hu hd)
        (pointHomOn_comp dQ dR hψ.hom T f r u hu hd)).2 hv')

/-- The induced point of a composite is compatible with restriction in the test object. -/
theorem comp_pointHomOn_eq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ R)
    (hu : u ≫ πR = yoneda.map r ≫ f)
    (h : IsDefinedOn dP dR (homComp hφ.hom hψ.hom) T f r u hu) :
    pointHomOn dP dR (homComp hφ.hom hψ.hom) T f r u hu h =
      pointHomAt dP dR (homComp hφ.hom hψ.hom) T' u
        ((hφ.comp_isDefinedOn_iff hψ T f r u hu).1 h) := by
  have hd : IsDefinedOn dQ dR hψ.hom T f r u hu :=
    isDefinedOn_of_homComp hφ.hom hψ.hom T f r u hu h
  have hd' := (hψ.isDefinedOn_iff T f r u hu).1 hd
  have hd2 := (isDefinedOn_homComp_iff hφ.hom hψ.hom T f r u hu hd).1 h
  rw [pointHomOn_homComp_eq hφ.hom hψ.hom T f r u hu hd h hd2,
    hφ.pointHomOn_eq T f r (pointHomOn dQ dR hψ.hom T f r u hu hd)
      (pointHomOn_comp dQ dR hψ.hom T f r u hu hd) hd2,
    pointHomAt_homComp_eq hφ.hom hψ.hom T' u hd'
      ((hφ.comp_isDefinedOn_iff hψ T f r u hu).1 h)
      ((isDefined_homComp_iff hφ.hom hψ.hom T' u hd').1
        ((hφ.comp_isDefinedOn_iff hψ T f r u hu).1 h))]
  exact pointHomAt_congr dP dQ hφ.hom T' _ _ (hψ.pointHomOn_eq T f r u hu hd) _ _

/-- **The composite of two maps of quasi-coherent graded algebras, over the scheme points of the
base.** -/
def comp : RelativeProjHomPoints dP dR where
  hom := homComp hφ.hom hψ.hom
  isDefinedOn_iff := hφ.comp_isDefinedOn_iff hψ
  pointHomOn_eq := hφ.comp_pointHomOn_eq hψ

/-- The restriction of `ψ ∘ φ` to a scheme point of the base is the composite of the two
restrictions. -/
theorem comp_hom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    (hφ.comp hψ).hom T f = (hψ.hom T f).comp (hφ.hom T f) :=
  rfl

/-- **Tag 085G, the first assertion: `U(ψ ∘ φ) ⊆ U(ψ)`.** -/
@[stacks 085G "the domain U(ψ ∘ φ) lies in U(ψ)"]
theorem comp_relativeMapSubfunctor_le :
    (hφ.comp hψ).relativeMapSubfunctor ≤ hψ.relativeMapSubfunctor :=
  fun Y y hy => isDefined_of_homComp hφ.hom hψ.hom Y.unop (yonedaEquiv.symm y) hy

/-- **Tag 085G, the first assertion: `U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`.** A point of
`R = Proj_X(𝒞)` lying in `U(ψ)` lies in `U(ψ ∘ φ)` exactly when its image under
`r_ψ : U(ψ) ⟶ Q` lies in `U(φ)`.

Together with `AlgebraicGeometry.Space.RelativeProjHomPoints.comp_relativeMapSubfunctor_le`
this is the equality `U(ψ ∘ φ) = r_ψ^{-1}(U(φ))` of the source.  (The source writes the
right-hand side of that equality as `r_φ^{-1}(U(ψ))`, which does not typecheck: `r_φ` is defined
on an open of `Q` and takes values in `P`, while `U(ψ)` is an open of `R`.  The reading above is
the one the scheme-level analogue Tag 07ZH states, and it is the one the second assertion — which
the source states identically in both tags — requires.) -/
@[stacks 085G "U(ψ ∘ φ) is the inverse image of U(φ) under r_ψ"]
theorem mem_comp_relativeMapSubfunctor_iff (Y : (BigFppfOver B S hS)ᵒᵖ) (y : R.obj Y)
    (hy : y ∈ hψ.relativeMapSubfunctor.obj Y) :
    y ∈ (hφ.comp hψ).relativeMapSubfunctor.obj Y ↔
      hψ.relativeMapSpaceHom.app Y ⟨y, hy⟩ ∈ hφ.relativeMapSubfunctor.obj Y := by
  refine (isDefined_homComp_iff hφ.hom hψ.hom Y.unop (yonedaEquiv.symm y) hy).trans ?_
  change _ ↔ IsDefined dP dQ hφ.hom Y.unop (yonedaEquiv.symm (yonedaEquiv
    (pointHomAt dQ dR hψ.hom Y.unop (yonedaEquiv.symm y) hy)))
  rw [Equiv.symm_apply_apply]

/-- **Tag 085G, the second assertion: `r_{ψ ∘ φ} = r_φ ∘ r_ψ|_{U(ψ ∘ φ)}`.** -/
@[stacks 085G "the morphism r_{ψ ∘ φ} is r_φ after r_ψ"]
theorem app_comp_relativeMapSpaceHom (Y : (BigFppfOver B S hS)ᵒᵖ) (y : R.obj Y)
    (hy : y ∈ hψ.relativeMapSubfunctor.obj Y)
    (hc : y ∈ (hφ.comp hψ).relativeMapSubfunctor.obj Y)
    (hc2 : hψ.relativeMapSpaceHom.app Y ⟨y, hy⟩ ∈ hφ.relativeMapSubfunctor.obj Y) :
    (hφ.comp hψ).relativeMapSpaceHom.app Y ⟨y, hc⟩ =
      hφ.relativeMapSpaceHom.app Y ⟨hψ.relativeMapSpaceHom.app Y ⟨y, hy⟩, hc2⟩ := by
  change yonedaEquiv (pointHomAt dP dR (homComp hφ.hom hψ.hom) Y.unop
      (yonedaEquiv.symm y) hc) =
    yonedaEquiv (pointHomAt dP dQ hφ.hom Y.unop (yonedaEquiv.symm (yonedaEquiv
      (pointHomAt dQ dR hψ.hom Y.unop (yonedaEquiv.symm y) hy))) hc2)
  refine congrArg yonedaEquiv ?_
  refine (pointHomAt_homComp_eq hφ.hom hψ.hom Y.unop (yonedaEquiv.symm y) hy hc ?_).trans ?_
  · exact (isDefined_homComp_iff hφ.hom hψ.hom Y.unop (yonedaEquiv.symm y) hy).1 hc
  · exact pointHomAt_congr dP dQ hφ.hom Y.unop _ _
      (Equiv.symm_apply_apply yonedaEquiv _).symm _ hc2

end RelativeProjHomPoints

end Composition

end AlgebraicGeometry.Space

end
