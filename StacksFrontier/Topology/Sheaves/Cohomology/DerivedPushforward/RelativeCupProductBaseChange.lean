module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductAndBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct

/-!
# The relative cup product is compatible with a commutative square of ringed spaces

Let

```
            g'
    X' ----------→ X
    |              |
 f' |              | f
    v      g       v
    Y' ----------→ Y
```

be a commutative square of ringed spaces and let `K, L ∈ D(𝒪_X)`.  Stacks 0H99 asserts that the
hexagon

```
                                     Lg^*(cup for f)
  Lg^*(Rf_*K ⊗^L_{𝒪_Y} Rf_*L)  ------------------------→  Lg^*Rf_*(K ⊗^L_{𝒪_X} L)
            ‖ 079U for g                                              | 08HY
            v                                                         v
  Lg^*Rf_*K ⊗^L_{𝒪_{Y'}} Lg^*Rf_*L                        Rf'_*L(g')^*(K ⊗^L_{𝒪_X} L)
            | 08HY ⊗ 08HY                                             ‖ 079U for g'
            v                                                         v
  Rf'_*L(g')^*K ⊗^L_{𝒪_{Y'}} Rf'_*L(g')^*L  ----------→  Rf'_*(L(g')^*K ⊗^L_{𝒪_{X'}} L(g')^*L)
                                     cup for f'
```

commutes in `D(𝒪_{Y'})`: the horizontal arrows are the relative cup product of Stacks 0B68, the
two arrows marked 08HY are the derived base change map of that tag, and the two identifications
are the comparison of derived pullback with the derived tensor product, Stacks 079U.  The
source's proof is "Omitted"; the proof below is complete, with no hypothesis beyond
commutativity of the square and no hypothesis at all on `K` and `L`.

## Main definitions

* `Stacks.Cohomology.DerivedRelativeCupProduct.RelativeCupProductBaseChangeSquare`: the hexagon
  itself, as a predicate on a cup product, three base change maps and a second cup product, over
  arbitrary categories, functors and bifunctors.
* `Stacks.Cohomology.DerivedRelativeCupProduct.ComparisonCompatibleWithSquare`: the coherence of
  a pullback-tensor comparison with the identification of the two composites around a base change
  square — the one hypothesis the hexagon needs.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_derivedBaseChangeMap`:
  **Stacks 0H99**, the hexagon above at the relative cup product of Stacks 0B68 and the derived
  base change map of Stacks 08HY, for arbitrary `K, L ∈ D(𝒪_X)`.
* `Stacks.Cohomology.DerivedRelativeCupProduct.derivedPullbackTensorIso_comparison_square`: the
  coherence the hexagon rests on, proved for ringed spaces — the two composite comparisons of
  Stacks 079U around the square agree under the identification of the two iterated derived
  pullbacks with the derived pullback along the common composite.
* `Stacks.Cohomology.DerivedRelativeCupProduct.comparisonCompatibleWithSquare_of_composition_laws`
  and `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_derivedBaseChangeMap`:
  the two abstract steps the geometric statements instantiate.

## Implementation notes

*Where the diagram chase is.*  Not here.  The whole of it is
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_baseChangeMap`, carried
out over arbitrary categories, adjunctions and bifunctors, for the cup product
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct` of an adjunction and the
canonical base change map `Stacks.CategoryTheory.BaseChange.map` of a square of adjunctions.  The
relative cup product of Stacks 0B68 and the derived base change map of Stacks 08HY are those two
constructions at the derived adjunctions of Stacks 079W, so the geometric statement below is one
argument-passing application of it.

*What the abstract chase leaves open, and why it is available here.*  Its single hypothesis is
that the comparison of Stacks 079U along a composite is the composite of the two comparisons, for
the two ways around the square — `ComparisonCompatibleWithSquare` below.  For ringed topoi that
is not available in this tree, and
`Stacks.Cohomology.RelativeCupProductBaseChangeOnTopoi.relativeCupProduct_derivedBaseChangeMap`
carries it as a hypothesis.  For ringed spaces it **is** available:
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp` is exactly the
composition law for `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` along the
composition isomorphism of Stacks 0D5S.  Applying it to the two factorizations `f' ≫ g` and
`g' ≫ f` of the common composite, and transporting between them along commutativity of the
square, discharges it; that is `derivedPullbackTensorIso_comparison_square`, and this file
therefore carries 0H99 with no clause.

*Why the two factorizations need a transport.*  The derived base change map of Stacks 08HY
identifies `Lg^* ⋙ L(f')^*` with `L(g' ≫ f)^*` through
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`, which is the composition
isomorphism at `(f', g)` followed by the `eqToIso` of `g' ≫ f = f' ≫ g`.  The composition law
for Stacks 079U speaks about `L(f' ≫ g)^*`, so one `eqToHom` stands between the two; that it is
compatible with the comparison is `comparison_eqToIso_transport`, proved by substituting the
equality of the two composites away.

*Why the two diagrams are predicates applied to the canonical maps.*  This is forced.  The
derived pullbacks and pushforwards are reducible abbreviations over total derived
functors, and the four categories here are spelled one way by the pullback development
(`SheafOfModules (structureSheafRing X)`) and another by the tensor-product
development.  A hexagon written out at those and proved by one application of the abstract chase
elaborates without complaint and then **fails the kernel** — `(kernel) deterministic timeout`,
and no `set_option` may appear in this library.  The same is true of the
single step `(eg.hom ≫ ef.inv).app T = (c₁.hom.app T ≫ ee.hom.app T) ≫ ef.inv.app T`, true by
definition of `derivedPullbackCompIsoLeft`, when stated at those categories; whereas the equality
of *isomorphisms* `derivedPullbackCompIsoLeft g' f' f g sq =
derivedPullbackCompIsoCanonical f' g ≪≫ eqToIso _`, with no component taken, costs nothing.
Stating the hexagon and the coherence as predicates over abstract data and applying them to the
canonical maps keeps every concrete declaration an application of one head symbol to arguments,
which is what the kernel can check here: the only reductions left to it are `relativeCupProduct`
to `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap` and
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` to its `Mate` form, each on a single
morphism in an argument position.  Nothing is weakened: both predicates are `@[expose]`
definitions whose bodies are the diagrams, and the canonical maps appear in them as arguments.

*The sheafification binders.*  `HasSheafify` and `WEqualsLocallyBijective` for `AddCommGrpCat.{u}`
on the four sites of opens are the binders the derived tensor product of Stacks 06YU is stated
under.  Both are `Prop`s and both are inhabited for every ringed space, by
`Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, so they are not a weakening.

## References

* [Stacks Project, Tag 0H99](https://stacks.math.columbia.edu/tag/0H99)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0H9A](https://stacks.math.columbia.edu/tag/0H9A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedRelativeCupProduct

/-! ### Bookkeeping over abstract morphisms -/

section Cancellation

universe v₁ v₂ u₁ u₂ w₁

/-- **The bookkeeping of `ComparisonCompatibleWithSquare`.**  Two composition laws `ha`, `hb` for
the two ways around a square and one transport `hcc` between their common targets produce the
coherence of the two composite comparisons under the identification `κ` of the two composites.

Everything is a bare morphism: the objects are derived pullbacks of derived tensor products and
`CategoryTheory.Category.assoc` is a field rather than a definitional equality, so a lemma stated
at natural transformations would have to be matched at exactly the bracketing the unfolded goal
carries. -/
private lemma comparison_square_of_composition_laws {D : Type u₁} [Category.{v₁} D]
    {u w₁ w₂ v m₁ m₂ bu bw₁ bw₂ bv : D}
    (c₁ : u ⟶ w₁) (e : w₁ ⟶ w₂) (c₂ : v ⟶ w₂) (c₂inv : w₂ ⟶ v)
    (C₁a : u ⟶ m₁) (C₁b : m₁ ⟶ bu) (A₁ : w₁ ⟶ bw₁) (A₂ : w₂ ⟶ bw₂)
    (C₂a : v ⟶ m₂) (C₂b : m₂ ⟶ bv)
    (mc₁ : bu ⟶ bw₁) (me : bw₁ ⟶ bw₂) (mc₂ : bv ⟶ bw₂) (mc₂inv : bw₂ ⟶ bv)
    (κ : u ⟶ v) (mκ : bu ⟶ bv)
    (hκ : κ = (c₁ ≫ e) ≫ c₂inv) (hmκ : mκ = mc₁ ≫ me ≫ mc₂inv)
    (hc₂ : c₂inv ≫ c₂ = 𝟙 w₂) (hmc₂ : mc₂ ≫ mc₂inv = 𝟙 bv)
    (ha : c₁ ≫ A₁ = C₁a ≫ C₁b ≫ mc₁) (hb : c₂ ≫ A₂ = C₂a ≫ C₂b ≫ mc₂)
    (hcc : A₁ ≫ me = e ≫ A₂) :
    (C₁a ≫ C₁b) ≫ mκ = κ ≫ C₂a ≫ C₂b := by
  have h : c₂ ≫ A₂ ≫ mc₂inv = C₂a ≫ C₂b := by
    rw [reassoc_of% hb, hmc₂, Category.comp_id]
  have hA₂ : A₂ ≫ mc₂inv = c₂inv ≫ C₂a ≫ C₂b := by rw [← h, reassoc_of% hc₂]
  rw [hκ, hmκ]
  simp only [Category.assoc]
  rw [← reassoc_of% ha, reassoc_of% hcc, hA₂]

/-- **A comparison of two bifunctors along a functor is compatible with an equality of
functors.**  For a family of functors `Φ` and a comparison `α i` of `AP` with `AQ` along each
`Φ i`, equal indices `i = j` give equal functors, and the resulting `eqToIso` carries the
comparison at `i` to the comparison at `j`.

This is the transport the two factorizations of the common composite of a commutative square need.
It is stated abstractly because the concrete goal is not type-correct at `implicit` transparency —
the pullback development and the tensor-product development name the structure sheaf of a ringed
space differently — and, as recorded in the module docstring, the same statement written out at
the derived pullbacks and derived tensor products of four ringed spaces is past what the kernel
will check, while over variables it is immediate. -/
private lemma comparison_eqToIso_transport {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B]
    {ι : Type w₁} (AP : A × A ⥤ A) (AQ : B × B ⥤ B) (Φ : ι → (A ⥤ B))
    (α : ∀ i, AP ⋙ Φ i ⟶ (Φ i).prod (Φ i) ⋙ AQ) {i j : ι} (e : i = j) (M N : A) :
    (α i).app (M, N) ≫
        AQ.map ((eqToIso (congrArg Φ e)).hom.app M ×ₘ (eqToIso (congrArg Φ e)).hom.app N) =
      (eqToIso (congrArg Φ e)).hom.app (AP.obj (M, N)) ≫ (α j).app (M, N) := by
  subst e
  simp

/-- A bifunctor applied to a pair of three-fold composites splits into three applications. -/
private lemma map_mkHom_comp₃ {A B : Type u₁} [Category.{v₁} A] [Category.{v₁} B]
    (T : A × A ⥤ B) {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : A}
    (p₁ : a₁ ⟶ a₂) (p₂ : a₂ ⟶ a₃) (p₃ : a₃ ⟶ a₄)
    (q₁ : b₁ ⟶ b₂) (q₂ : b₂ ⟶ b₃) (q₃ : b₃ ⟶ b₄) :
    T.map (((p₁ ≫ p₂) ≫ p₃) ×ₘ ((q₁ ≫ q₂) ≫ q₃)) =
      T.map (p₁ ×ₘ q₁) ≫ T.map (p₂ ×ₘ q₂) ≫ T.map (p₃ ×ₘ q₃) := by
  rw [show (((p₁ ≫ p₂) ≫ p₃) ×ₘ ((q₁ ≫ q₂) ≫ q₃) : ((a₁, b₁) : A × A) ⟶ (a₄, b₄)) =
      (p₁ ×ₘ q₁) ≫ (p₂ ×ₘ q₂) ≫ (p₃ ×ₘ q₃) from
        CategoryTheory.Prod.hom_ext (Category.assoc p₁ p₂ p₃) (Category.assoc q₁ q₂ q₃),
    T.map_comp, T.map_comp]

/-- A bifunctor applied to a pair of mutually inverse morphisms in each factor is the identity. -/
private lemma map_mkHom_comp_id {A B : Type u₁} [Category.{v₁} A] [Category.{v₁} B]
    (T : A × A ⥤ B) {a₁ a₂ b₁ b₂ : A} {p : a₁ ⟶ a₂} {p' : a₂ ⟶ a₁} {q : b₁ ⟶ b₂} {q' : b₂ ⟶ b₁}
    (hp : p ≫ p' = 𝟙 a₁) (hq : q ≫ q' = 𝟙 b₁) :
    T.map (p ×ₘ q) ≫ T.map (p' ×ₘ q') = 𝟙 (T.obj (a₁, b₁)) := by
  rw [← T.map_comp,
    show ((p ×ₘ q) ≫ (p' ×ₘ q') : ((a₁, b₁) : A × A) ⟶ (a₁, b₁)) = 𝟙 (a₁, b₁) from
      CategoryTheory.Prod.hom_ext hp hq,
    T.map_id]

end Cancellation

/-! ### The two diagrams, as predicates on abstract data -/

section Predicates

universe w₁

variable {P P' Q Q' : Type*} [Category P] [Category P'] [Category Q] [Category Q']

/-- **The coherence of a pullback-tensor comparison with a base change square.**

The two composites `Lg ⋙ Lf'` and `Lf ⋙ Lg'` around the square are both identified with `Lc`, by
`eg` and `ef`, and each carries a comparison of the bifunctor `AP` with `AQ'` obtained by
composing its two factors' comparisons,
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.compComparison`, which takes its bifunctors in
the order target, middle, source.  This asserts that `eg.hom ≫ ef.inv` carries one to the other.

It is, verbatim, the hypothesis `hθ` of
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_baseChangeMap`, and it is
the only hypothesis `RelativeCupProductBaseChangeSquare` needs. -/
def ComparisonCompatibleWithSquare
    {Lg : P ⥤ P'} {Lf' : P' ⥤ Q'} {Lf : P ⥤ Q} {Lg' : Q ⥤ Q'} {Lc : P ⥤ Q'}
    (AP : P × P ⥤ P) (AP' : P' × P' ⥤ P') (AQ : Q × Q ⥤ Q) (AQ' : Q' × Q' ⥤ Q')
    (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (αf' : AP' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ AQ')
    (αf : AP ⋙ Lf ⟶ Lf.prod Lf ⋙ AQ) (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) : Prop :=
  ∀ M N : P,
    (Stacks.Cohomology.RelativeCupProductOnRingedTopoi.compComparison
          AQ' AP' AP αf' αg).app (M, N) ≫
        AQ'.map ((eg.hom ≫ ef.inv).app M ×ₘ (eg.hom ≫ ef.inv).app N) =
      (eg.hom ≫ ef.inv).app (AP.obj (M, N)) ≫
        (Stacks.Cohomology.RelativeCupProductOnRingedTopoi.compComparison
          AQ' AQ AP αg' αf).app (M, N)

/-- **The hexagon of Stacks 0H99.**

For right adjoints `Rf`, `Rf'` along the vertical edges of a commutative square, functors `Lg`,
`Lg'` along its horizontal edges, bifunctors `AP`, `AQ`, `AP'`, `AQ'` on the four categories
compared along `Lg` and `Lg'` by `αg` and `αg'`, and objects `K`, `L`, this says that

* `Lg` of the cup product `cup : AP(Rf K, Rf L) ⟶ Rf (AQ (K, L))`, followed by the base change
  map `bc` at `AQ (K, L)` and by `Rf'` of the comparison `αg'`,

equals

* the comparison `αg` at `(Rf K, Rf L)`, followed by the base change map in each tensor factor
  (`bcK`, `bcL`) and by the cup product `cup'` for the other vertical edge.

Taking `cup` and `cup'` to be the relative cup product of Stacks 0B68 and `bc`, `bcK`, `bcL` to
be the derived base change map of Stacks 08HY gives exactly the diagram of Stacks 0H99; that is
`relativeCupProduct_derivedBaseChangeMap`. -/
def RelativeCupProductBaseChangeSquare (Rf : Q ⥤ P) (Rf' : Q' ⥤ P') (Lg : P ⥤ P') (Lg' : Q ⥤ Q')
    (AP : P × P ⥤ P) (AQ : Q × Q ⥤ Q) (AP' : P' × P' ⥤ P') (AQ' : Q' × Q' ⥤ Q')
    (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ')
    (K L : Q)
    (cup : AP.obj (Rf.obj K, Rf.obj L) ⟶ Rf.obj (AQ.obj (K, L)))
    (bc : Lg.obj (Rf.obj (AQ.obj (K, L))) ⟶ Rf'.obj (Lg'.obj (AQ.obj (K, L))))
    (bcK : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K))
    (bcL : Lg.obj (Rf.obj L) ⟶ Rf'.obj (Lg'.obj L))
    (cup' : AP'.obj (Rf'.obj (Lg'.obj K), Rf'.obj (Lg'.obj L)) ⟶
      Rf'.obj (AQ'.obj (Lg'.obj K, Lg'.obj L))) : Prop :=
  Lg.map cup ≫ bc ≫ Rf'.map (αg'.app (K, L)) =
    αg.app (Rf.obj K, Rf.obj L) ≫ AP'.map (bcK ×ₘ bcL) ≫ cup'

/-- **The coherence of a pullback-tensor comparison around a square, from the composition law for
each of the two composites.**

The two composites are identified with members of one family of functors `Φ`, each carrying a
comparison `α i` of `AP` with `AQ'`: `Lg ⋙ Lf'` with `Φ i` by `c₁` and `Lf ⋙ Lg'` with `Φ j` by
`ef`, where `i = j`.  Given the composition law for each of the two composites — `ha`, `hb`, in
the shape `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp` states it — the
identification `eg.hom ≫ ef.inv` carries the one composite comparison to the other.

Two choices here are load-bearing rather than cosmetic.  The family `Φ` with an equality of indices
replaces an isomorphism `Φ i ≅ Φ j` together with the compatibility of `α i` and `α j` under it:
that compatibility is then `comparison_eqToIso_transport`, discharged inside this lemma, where it
is an equality between abstract data.  Supplied instead as a hypothesis, it is an equality
between the derived tensor products of four ringed spaces, and matching the caller's lemma
against it exhausts the kernel's budget.  And `eg` is a parameter with
`heg : eg = c₁ ≪≫ eqToIso (congrArg Φ e)` rather than written out, so that a consumer whose
identification is a *definition* unfolding to that — as
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` is — discharges `heg` by an
equality of isomorphisms, with no component taken. -/
lemma comparisonCompatibleWithSquare_of_composition_laws
    {Lg : P ⥤ P'} {Lf' : P' ⥤ Q'} {Lf : P ⥤ Q} {Lg' : Q ⥤ Q'}
    (AP : P × P ⥤ P) (AP' : P' × P' ⥤ P') (AQ : Q × Q ⥤ Q) (AQ' : Q' × Q' ⥤ Q')
    (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (αf' : AP' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ AQ')
    (αf : AP ⋙ Lf ⟶ Lf.prod Lf ⋙ AQ) (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ')
    {ι : Type w₁} (Φ : ι → (P ⥤ Q'))
    (α : ∀ i, AP ⋙ Φ i ⟶ (Φ i).prod (Φ i) ⋙ AQ') {i j : ι} (e : i = j)
    (c₁ : Lg ⋙ Lf' ≅ Φ i) (ef : Lf ⋙ Lg' ≅ Φ j)
    (eg : Lg ⋙ Lf' ≅ Φ j) (heg : eg = c₁ ≪≫ eqToIso (congrArg Φ e))
    (ha : Functor.whiskerLeft AP c₁.hom ≫ α i =
      Functor.whiskerRight αg Lf' ≫ Functor.whiskerLeft (Lg.prod Lg) αf' ≫
        Functor.whiskerRight (NatTrans.prod c₁.hom c₁.hom) AQ')
    (hb : Functor.whiskerLeft AP ef.hom ≫ α j =
      Functor.whiskerRight αf Lg' ≫ Functor.whiskerLeft (Lf.prod Lf) αg' ≫
        Functor.whiskerRight (NatTrans.prod ef.hom ef.hom) AQ') :
    ComparisonCompatibleWithSquare AP AP' AQ AQ' αg αf' αf αg' eg ef := by
  subst heg
  intro M N
  exact comparison_square_of_composition_laws
    (c₁.hom.app (AP.obj (M, N))) ((eqToIso (congrArg Φ e)).hom.app (AP.obj (M, N)))
    (ef.hom.app (AP.obj (M, N))) (ef.inv.app (AP.obj (M, N)))
    (Lf'.map (αg.app (M, N))) (αf'.app (Lg.obj M, Lg.obj N))
    ((α i).app (M, N)) ((α j).app (M, N))
    (Lg'.map (αf.app (M, N))) (αg'.app (Lf.obj M, Lf.obj N))
    (AQ'.map (c₁.hom.app M ×ₘ c₁.hom.app N))
    (AQ'.map ((eqToIso (congrArg Φ e)).hom.app M ×ₘ (eqToIso (congrArg Φ e)).hom.app N))
    (AQ'.map (ef.hom.app M ×ₘ ef.hom.app N))
    (AQ'.map (ef.inv.app M ×ₘ ef.inv.app N))
    _ _ rfl (map_mkHom_comp₃ AQ' _ _ _ _ _ _) (ef.inv_hom_id_app _)
    (map_mkHom_comp_id AQ' (ef.hom_inv_id_app M) (ef.hom_inv_id_app N))
    (NatTrans.congr_app ha (M, N)) (NatTrans.congr_app hb (M, N))
    (comparison_eqToIso_transport AP AQ' Φ α e M N)

end Predicates

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The hexagon over abstract derived functors -/

section Mate

variable {X' X Y' Y : RingedSpace.{u, u}}
  {Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  {Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
  {Lf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Rf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'))}
  {Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'))}
  {Lg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lc : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
  (AP : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ×
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (AQ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ×
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
  (AP' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')) ×
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')))
  (AQ' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ×
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
  (αf : AP ⋙ Lf ⟶ Lf.prod Lf ⋙ AQ) (αf' : AP' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ AQ')
  (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- **The hexagon of Stacks 0H99 over abstract functors, adjunctions and bifunctors.**

This is `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_baseChangeMap`
read as `RelativeCupProductBaseChangeSquare`, and restated for the two constructions the
canonical statement is phrased with: the doubled-counit adjunction morphism
`Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap`, of which the relative cup
product of Stacks 0B68 is an instance, and
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap`, of which the derived base change
map of Stacks 08HY is an instance.  Both agree with the constructions that lemma uses by one
delta-reduction each, and over variables those reductions are free. -/
lemma adjunctionBitensorMap_derivedBaseChangeMap
    (hθ : ComparisonCompatibleWithSquare AP AP' AQ AQ' αg αf' αf αg' eg ef)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    RelativeCupProductBaseChangeSquare Rf Rf' Lg Lg' AP AQ AP' AQ' αg αg' K L
      (adjunctionBitensorMap adjf AP AQ αf K L)
      (Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap adjf adjf' eg ef
        (AQ.obj (K, L)))
      (Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap adjf adjf' eg ef K)
      (Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap adjf adjf' eg ef L)
      (adjunctionBitensorMap adjf' AP' AQ' αf' (Lg'.obj K) (Lg'.obj L)) :=
  Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_baseChangeMap
    adjf adjf' AP AQ AP' AQ' αf αf' αg αg' eg ef hθ K L

end Mate

/-! ### Stacks 0H99 -/

section Canonical

variable {X' X Y' Y : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : g' ≫ f = f' ≫ g)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison of Stacks 079U is coherent around a commutative square of ringed spaces.**

Both composites of derived pullbacks around the square, `Lg^* ⋙ L(f')^*` and `Lf^* ⋙ L(g')^*`,
are identified with the derived pullback along the common composite by the composition
isomorphism of Stacks 0D5S — on the left by
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`, on the right by
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` — hence with each other.
Each composite also carries the composite of the two comparisons of Stacks 079U along its two
factors.  This says that the identification carries the one composite comparison to the other.

It is the single hypothesis of
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_baseChangeMap`, and for
ringed spaces it is a theorem: `comparisonCompatibleWithSquare_of_composition_laws` at the
composition law `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp` for the
two factorizations `f' ≫ g` and `g' ≫ f` of the common composite, and the transport
`comparison_eqToIso_transport` between them. -/
theorem derivedPullbackTensorIso_comparison_square :
    ComparisonCompatibleWithSquare
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y'.sheaf))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf))
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g)
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f')
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g')
      (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq)
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f) :=
  comparisonCompatibleWithSquare_of_composition_laws
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y'.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f')
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g')
    (fun h : X' ⟶ Y => Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h)
    (fun h => Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison h) sq.symm
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f' g)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f)
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq) rfl
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp f' g)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp g' f)

/-- **Stacks 0H99: the relative cup product is compatible with a commutative square of ringed
spaces.**

For a commutative square `g' ≫ f = f' ≫ g` of ringed spaces and arbitrary `K, L ∈ D(𝒪_X)`, the
hexagon `RelativeCupProductBaseChangeSquare` commutes at the relative cup product of Stacks 0B68
for `f` and for `f'` and the derived base change map of Stacks 08HY: the derived pullback along
`g` of the cup product for `f`, followed by the base change map and by `Rf'_*` of the comparison
of Stacks 079U for `g'`, equals the comparison of Stacks 079U for `g`, followed by the base
change map in each tensor factor and by the cup product for `f'`.

There is no boundedness, flatness or quasi-coherence hypothesis on `K` and `L`, and no associator
or symmetry of `⊗^L` is used: the hexagon has binary tensor products only. -/
@[stacks 0H99]
theorem relativeCupProduct_derivedBaseChangeMap
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    RelativeCupProductBaseChangeSquare
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f')
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g')
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y'.sheaf))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf))
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g)
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g') K L
      (relativeCupProduct f K L)
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj K).obj L))
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq K)
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq L)
      (relativeCupProduct f'
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').obj K)
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').obj L)) :=
  adjunctionBitensorMap_derivedBaseChangeMap
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f')
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y'.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f')
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g')
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f)
    (derivedPullbackTensorIso_comparison_square g' f' f g sq) K L

end Canonical

end Stacks.Cohomology.DerivedRelativeCupProduct

end
