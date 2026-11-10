module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# Compatibility of the relative cup product with a base change square

Consider a commutative square of ringed topoi

```
                g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
        |  f'                |  f
        v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
                g
```

and let `K`, `L` be arbitrary objects of `D(𝒪_C)`.  [Stacks, Tag 0H9A] asserts that the relative
cup product of [Stacks, Tag 0B6C] is compatible with the square, in the sense that the diagram

```
Lg^*(Rf_*K ⊗^L_{𝒪_D} Rf_*L) ----------→ Lg^*(Rf_*(K ⊗^L_{𝒪_C} L))
            ‖ (Tag 07A4 for g)                      | (Tag 07A7)
            v                                       v
Lg^*Rf_*K ⊗^L_{𝒪_{D'}} Lg^*Rf_*L        R(f')_*L(g')^*(K ⊗^L_{𝒪_C} L)
            | (Tag 07A7 in both factors)            ‖ R(f')_* of Tag 07A4 for g'
            v                                       v
R(f')_*L(g')^*K ⊗^L_{𝒪_{D'}} R(f')_*L(g')^*L --→ R(f')_*(L(g')^*K ⊗^L_{𝒪_{C'}} L(g')^*L)
```

commutes in `D(𝒪_{D'})`.  The two horizontal arrows are the relative cup product of
[Stacks, Tag 0B6C], for `f` on top (pulled back along `g`) and for `f'` on the bottom; the
vertical arrows are the base change map of [Stacks, Tag 07A7] and the comparison of
[Stacks, Tag 07A4].

## Main results

* `adjunctionCupProduct_baseChange_square` — the statement over abstract adjunctions: a square of
  categories whose two horizontal functors have right adjoints and whose two composites are
  identified with one functor, with a bifunctor at each of the four corners and a comparison
  along each of the four functors.  No sheaf, complex or derived category enters.

**[Stacks, Tag 0H9A]** itself is
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct_baseChange_square` of
the module `RelativeCupProductBaseChangeOfToposHom` in the directory
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor`:
that lemma instantiated at the derived tensor products of [Stacks, Tag 06YU], the comparisons of
[Stacks, Tag 07A4] and the base change map of [Stacks, Tag 07A7].

## Implementation notes

*The statement is an equality of two composites.*  The source draws a commutative diagram, and
that is what is stated: the composite down the left and along the bottom equals the composite
along the top and down the right, as a single equation between two morphisms of `D(𝒪_{D'})`.  It
is **not** the existence of a mediating comparison, and it is not an isomorphism statement.  All
four morphisms `f`, `f'`, `g`, `g'` of the square occur in it, and the commutativity `h` of the
square is used -- it is what identifies the two iterated derived pullbacks around the square, and
hence what lets the base change map of [Stacks, Tag 07A7] be written down at all.

*How the square's two `@{=}` edges are handled.*  The source marks the left edge of its diagram,
`Lg^*(A ⊗^L B) = Lg^*A ⊗^L Lg^*B`, and the right edge,
`R(f')_*L(g')^*(K ⊗^L L) = R(f')_*(L(g')^*K ⊗^L L(g')^*L)`, with equality signs.  Neither is an
equality of objects here: each is the forward map of the bifunctorial isomorphism of
[Stacks, Tag 07A4], `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`, for `g` and for
`g'` respectively.  They therefore appear in the statement as honest arrows, placed exactly where
the source draws its `@{=}` edges, and nothing is absorbed into a transport.  This is the
opposite choice from the one `relativeCupProduct_comp` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/RelativeCupProductCoherence.lean` had
to make for [Stacks, Tag 0FPN]: there the source's `@{=}` edge was an identification of
*functors* (`R(f' ∘ f)_* = Rf'_*Rf_*`) and had to be realized as a literal composite to avoid a
silent transport, whereas here both `@{=}` edges are maps between objects of one category that
this development already has, so they can simply be written down.  There is no composite
morphism of ringed topoi in the statement and so no analogue of that choice arises for the
functors: `Lg^*`, `L(g')^*`, `Rf_*` and `R(f')_*` all appear as themselves.

*The one hypothesis of the abstract lemma beyond the source.*  The source's proof is
"Omitted."  The two iterated derived pullbacks around the square, `L(f')^* ∘ Lg^*` and
`L(g')^* ∘ Lf^*`, are not equal functors here: each is identified with the derived pullback along
the common composite by [Stacks, Tag 0D6D], and the resulting isomorphism `c` is an isomorphism
rather than an identity.  So the verification must know that the four comparisons of
[Stacks, Tag 07A4] around the square match up across it, which is
`Stacks.AffineProjectionFormula.TensorComparisonCompatible`, the hypothesis `hsq` of
`adjunctionCupProduct_baseChange_square`.  For a commutative square of morphisms of ringed topoi
it is discharged by
`Stacks.Sheaves.DerivedPullback.OfToposHom.tensorComparisonCompatible_derivedPullbackTensorIso`,
which is how `relativeCupProduct_baseChange_square` obtains [Stacks, Tag 0H9A] with no hypothesis
beyond the commutativity of the square.  Everything else -- the whole adjunction calculus that
"we omit the verification" refers to -- is proved here.

*Nothing is assumed about `K` and `L`.*  They are arbitrary objects of the unbounded derived
category `D(𝒪_C)`: no boundedness, finiteness, perfectness or quasi-coherence.

*Why the abstract layer.*  The statement is an equality between composites of six functors, four
of which (`Lg^*`, `L(g')^*`, `Rf_*`, `R(f')_*`) are reducible abbreviations over total derived
functors.  Rewriting inside such a goal builds a proof term the kernel cannot check in its
budget.  Proving the identity once with the functors, adjunctions and bifunctors as variables
makes the geometric statement a single application, which is the factorization
`Stacks.CategoryTheory.BaseChange` and `Stacks.AffineProjectionFormula` already perform for the
base change map and for Equation 21.50.0.1.  The abstract layer of
`RelativeCupProductCoherence.lean` is reused rather than rebuilt: `adjunctionCupProduct_transpose`
gives the adjunct of the cup product, and the two bifunctor manipulations are
`CategoryTheory.bifunctor_comparison_naturality` and `CategoryTheory.bifunctor_map_comp_both` of
`StacksFrontier/CategoryTheory/BifunctorProdMap.lean`.

*What is and is not definitional.*  The mathematical content is not: the square is not `rfl`, and
the proof of the abstract lemma genuinely consumes `hsq` -- deleting the one rewrite by it leaves
exactly that equation as the open goal, so the hypothesis is neither decoration nor more than is
needed.  What *is* definitional is only the passage from the abstract lemma to the geometric one,
`relativeCupProduct_baseChange_square`, which is a single application of the abstract one with no
transport and no bridging lemma.  That is the same arrangement as
`derivedBaseChangeMap_projectionFormulaMap_square`.

## References

* [Stacks Project, Tag 0H9A](https://stacks.math.columbia.edu/tag/0H9A)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AffineProjectionFormula
open Stacks.Cohomology.DerivedBaseChangeOnTopoi
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Sheaves.DerivedPullback
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

universe u

/-! ### Compatibility with base change, over abstract adjunctions -/

section AbstractSquare

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
  (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
  (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B')

/-- **[Stacks, Tag 0H9A] over abstract adjunctions.**  For a square of categories in which the
two horizontal functors `Lf`, `Lf'` have right adjoints and the two composites around the square
are identified with one functor, and for a bifunctor at each of the four corners with a
comparison along each of the four functors, the cup product `adjunctionCupProduct` of the two
adjunctions is compatible with the base change map `Stacks.CategoryTheory.BaseChange.map`: the
square

```
Lg(A(Rf G, Rf H)) --------Lg(cup for f)-------→ Lg(Rf(B(G, H)))
        | αg                                           | base change
        v                                              v
A'(Lg Rf G, Lg Rf H)                          Rf'(Lg'(B(G, H)))
        | base change in both factors                  | Rf'(αg')
        v                                              v
A'(Rf' Lg' G, Rf' Lg' H) --cup for f'--→ Rf'(B'(Lg' G, Lg' H))
```

commutes: the two composites `Lg(A(Rf G, Rf H)) ⟶ Rf'(B'(Lg' G, Lg' H))` are equal.

The only input is `TensorComparisonCompatible`, the compatibility of the four comparisons with
the identification of the two composites around the square; everything else is the adjunction
calculus.  Concretely: both sides land in `Rf'`-of-something, so it is enough to compare their
adjuncts under `Lf' ⊣ Rf'`, which `adjunctionCupProduct_transpose` and
`Stacks.AffineProjectionFormula.map_baseChangeMap_comp_counit` compute; the left one is then the
comparison along `Lg` followed by the one along `Lf'`, with the counit of `Lf ⊣ Rf` in both
factors, and the right one is the comparison along `Lf` followed by the one along `Lg'`, with the
same counit in the same two factors.  The compatibility identifies them. -/
theorem adjunctionCupProduct_baseChange_square (G H : T)
    (hsq : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' (Rf.obj G) (Rf.obj H)) :
    αg.app (Rf.obj G, Rf.obj H) ≫
        A'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef G ×ₘ
            Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef H) ≫
          adjunctionCupProduct adjf' A' B' αf' (Lg'.obj G) (Lg'.obj H) =
      Lg.map (adjunctionCupProduct adjf A B αf G H) ≫
        Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (B.obj (G, H)) ≫
          Rf'.map (αg'.app (G, H)) := by
  rw [TensorComparisonCompatible] at hsq
  have h1 : Lf'.map (A'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef G ×ₘ
          Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef H)) ≫
        αf'.app (Rf'.obj (Lg'.obj G), Rf'.obj (Lg'.obj H)) =
      αf'.app (Lg.obj (Rf.obj G), Lg.obj (Rf.obj H)) ≫
        B'.map (Lf'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef G) ×ₘ
          Lf'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef H)) :=
    bifunctor_comparison_naturality A' B' αf' _ _
  have h2 : Lf'.map (Lg.map (adjunctionCupProduct adjf A B αf G H)) ≫
      (squareCompositeIso eg ef).hom.app (Rf.obj (B.obj (G, H))) =
      (squareCompositeIso eg ef).hom.app (A.obj (Rf.obj G, Rf.obj H)) ≫
        Lg'.map (Lf.map (adjunctionCupProduct adjf A B αf G H)) := by
    have h := (squareCompositeIso eg ef).hom.naturality (adjunctionCupProduct adjf A B αf G H)
    simpa using h
  have h3 : Lg'.map (B.map (adjf.counit.app G ×ₘ adjf.counit.app H)) ≫ αg'.app (G, H) =
      αg'.app (Lf.obj (Rf.obj G), Lf.obj (Rf.obj H)) ≫
        B'.map (Lg'.map (adjf.counit.app G) ×ₘ Lg'.map (adjf.counit.app H)) :=
    bifunctor_comparison_naturality B B' αg' _ _
  refine (adjf'.homEquiv _ _).symm.injective ?_
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  conv_lhs => rw [adjunctionCupProduct_transpose, reassoc_of% h1,
    ← bifunctor_map_comp_both, map_baseChangeMap_comp_counit, map_baseChangeMap_comp_counit,
    bifunctor_map_comp_both, reassoc_of% hsq]
  conv_rhs => rw [Adjunction.counit_naturality, map_baseChangeMap_comp_counit_assoc,
    reassoc_of% h2, ← Functor.map_comp_assoc, adjunctionCupProduct_transpose,
    Functor.map_comp, Category.assoc, h3]

end AbstractSquare

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
