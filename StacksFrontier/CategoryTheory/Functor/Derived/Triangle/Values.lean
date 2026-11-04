module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Opposite.Basic
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.CategoryTheory.EssentiallyConstant.Cofinal
import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
public import StacksFrontier.CategoryTheory.Localization.Saturated.Defs
import StacksFrontier.CategoryTheory.Triangulated.Localization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Values of the right derived functor and their induced morphisms

The ind-object `X/W ⥤ H` whose essential constancy defines the value `RF(X)` (Tag 05S9), and
the morphisms `RF(f)` between values (Tag 05SA). Part of the proof of [Stacks, Tag 05SC]; the
section docstring below describes the whole argument.
-/

section

/-!
# The derived functors take a distinguished triangle to a distinguished triangle

Let `F : 𝒟 ⥤ 𝒟'` be an exact functor of pretriangulated categories and let `W` be a saturated
multiplicative system in `𝒟` compatible with the triangulation. The right derived functor `RF`
is *defined at* an object `X` when the ind-object
$$ X/W ⟶ 𝒟', \qquad (s : X ⟶ X') ⟼ F(X'), $$
is essentially constant, its value being `RF(X)`, and the left derived functor `LF` is defined
at `X` when the pro-object
$$ W/X ⟶ 𝒟', \qquad (s : X' ⟶ X) ⟼ F(X'), $$
is essentially constant, its value being `LF(X)` (Tag 05S9). A morphism `f : X ⟶ Y` of `𝒟` at
whose two ends `RF` is defined induces a unique morphism `RF(f) : RF(X) ⟶ RF(Y)` between the
values, characterised by the requirement that
`F(X') ⟶ RF(X) ⟶ RF(Y)` equals `F(X') ⟶ F(Y') ⟶ RF(Y)` for every commutative square
`f ≫ s' = s ≫ f'` with `s, s'` in `W` (Tag 05SA); dually `LF(f) : LF(X) ⟶ LF(Y)` is
characterised by `LF(X) ⟶ LF(Y) ⟶ F(Y')` equalling `LF(X) ⟶ F(X') ⟶ F(Y')` for every
commutative square `s ≫ f = f' ≫ s'` with `s, s'` in `W`.

For a distinguished triangle `(X, Y, Z, f, g, h)` of `𝒟`, if `RF` is defined at two of the three
objects `X, Y, Z` then it is defined at the third, and
`(RF(X), RF(Y), RF(Z), RF(f), RF(g), RF(h))` is a distinguished triangle of `𝒟'`. The same holds
for `LF`: definedness at two of the three vertices gives definedness at the third, and
`(LF(X), LF(Y), LF(Z), LF(f), LF(g), LF(h))` is a distinguished triangle of `𝒟'`.

## Main results

* `exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished`, in the
  namespace `CategoryTheory.Functor`:
  both assertions of the lemma. Each of the two conjuncts is the two-out-of-three property of
  definedness along a distinguished triangle together with the statement that the triangle of
  values, with the three induced morphisms, is distinguished — the first conjunct for `RF`, the
  second for `LF`.

## Proof outline

Let `F : C ⥤ H` be an exact functor of pretriangulated categories and let `W` be a saturated
multiplicative system in `C` compatible with the triangulation. For an object `X` of `C` a
*value* of the right derived functor at `X` is a cocone `c` on the ind-object
`X/W ⟶ H`, `(s : X ⟶ X') ↦ F(X')` at which that ind-object is essentially constant
(`CategoryTheory.Functor.IsRightDerivedValueAt`, Tag 05S9).

Two ingredients are elementary and are proved here in the generality in which they hold — for
a functor `F : C ⥤ H` between arbitrary categories and a class `W` with a left calculus of
fractions, no triangulated structure being involved.

*The induced morphism (Tag 05SA).* If `RF` is defined at `X` with value `c`, and `d` is any
cocone on the ind-object at `Y`, then a morphism `f : X ⟶ Y` induces `u : c.pt ⟶ d.pt`
compatible with the coprojections along every square `f ≫ t = s ≫ f'` with `s`, `t` in `W`.
The construction is the source's: choose an index `s₀` and a section `r : c.pt ⟶ F(X'₀)` of the
coprojection at `s₀`, complete `f` and `s₀` to a square by the Ore condition MS2 and set
`u = r ≫ F(f₀) ≫ d_{t₀}`. What makes this independent of the choices is that the composite
`F(X') ⟶ F(Y') ⟶ d.pt` attached to a square over a *fixed* index `s` does not depend on the
square: two squares over `s` are dominated by a third — the Ore condition again — and the two
resulting morphisms out of `X'` become equal after postcomposition with a morphism of `W`, by
the cancellation axiom MS3.

*Uniqueness of values.* A cocone at which the ind-object is essentially constant is a colimit
cocone, so two values at the same object are uniquely isomorphic compatibly with the
coprojections. Filteredness of `X/W` is not needed for this.

## Implementation notes

*Definedness and values.* Being defined at `X` with value `c.pt` is
`CategoryTheory.Functor.IsRightDerivedValueAt`, resp.
`CategoryTheory.Functor.IsLeftDerivedValueAt`, of Tag 05S9 — the source's essential constancy of
the ind-object over `X/W`, resp. of the pro-object over `W/X`, with the cocone, resp. cone,
carrying the value as a parameter so that the value and its coprojections `F(X') ⟶ RF(X)`, resp.
its projections `LF(X) ⟶ F(X')`, can be named. "Defined at `X`" is therefore
`∃ c, F.IsRightDerivedValueAt W X c`, resp. `∃ c, F.IsLeftDerivedValueAt W X c`. Mathlib's
`Functor.HasPointwiseRightDerivedFunctorAt`, the existence of the colimit computing the value, is
strictly weaker and is not the source's notion.

*Both assertions of the lemma, each in the form Tag 05S9 gives it.* The source's final sentence,
"similarly for `LF`", is a second assertion, and it is the second conjunct of the statement: the
ind-side is the first conjunct, the pro-side the second, and a use of one half is a projection.
The pro-side is phrased on the pro-objects over `W/X`, in the form Tag 05S9(2) gives them, so it
speaks about the same distinguished triangle `T`, with `LF(f)`, `LF(g)`, `LF(h)` in the same three
positions and no rotation or reversal at the point of use. Reading it instead as the ind-side for
`F.op`, `W.op` and the opposite triangle needs the pretriangulated structure on the opposite
categories together with the transports of exactness of `F`, of saturation of `W` (Tag 05Q8) and
of compatibility with the triangulation along `op`, and the identification of
`IsLeftDerivedValueAt` with `F.op.IsRightDerivedValueAt W.op (op X)` across
`(W.Over ⊤ X)ᵒᵖ ≌ W.op.Under ⊤ (op X)`; those are statements about opposite categories rather than
about derived functors, and none of them is needed to use the pro-side. The two halves are the
same four clauses read in opposite categories, so each is the mirror of the other: projections
replace coprojections and every characterising square is read backwards, while the triangle of
values `LF(X) ⟶ LF(Y) ⟶ LF(Z) ⟶ LF(X)⟦1⟧` runs in the same direction as
`RF(X) ⟶ RF(Y) ⟶ RF(Z) ⟶ RF(X)⟦1⟧`. Instantiating the three characterising clauses at the
identity indices `s = t = r = 𝟙` recovers the three commuting squares of a morphism of triangles
`F.mapTriangle.obj T ⟶ Triangle.mk (RF f) (RF g) (RF h)` on the ind-side and
`Triangle.mk (LF f) (LF g) (LF h) ⟶ F.mapTriangle.obj T` on the pro-side, the direction in which
the canonical map `F(X) ⟶ RF(X)`, resp. `LF(X) ⟶ F(X)`, of Tag 05SX goes.

*The induced morphisms are pinned, not merely asserted to exist.* The three morphisms of each
triangle of values are characterised by the squares of Tag 05SA, resp. by their duals, one for
each of `f`, `g` and `h`, which determine them uniquely. For `h : Z ⟶ X⟦1⟧` the relevant value at
`X⟦1⟧` is `RF(X)⟦1⟧`, resp. `LF(X)⟦1⟧`: the indices `s⟦1⟧ : X⟦1⟧ ⟶ X'⟦1⟧`, resp.
`s⟦1⟧ : X'⟦1⟧ ⟶ X⟦1⟧`, obtained by shifting indices of `X/W`, resp. of `W/X` (they lie in `W`,
which is stable under shift), are cofinal in `(X⟦1⟧)/W`, resp. initial in `W/(X⟦1⟧)`, and the
coprojection of `RF(X)⟦1⟧` at `s⟦1⟧` is `F(X'⟦1⟧) ⟶ F(X')⟦1⟧ ⟶ RF(X)⟦1⟧`, the commutation
isomorphism of `F` with the shift followed by the shift of the coprojection at `s`, while the
projection of `LF(X)⟦1⟧` at `s⟦1⟧` is `LF(X)⟦1⟧ ⟶ F(X')⟦1⟧ ⟶ F(X'⟦1⟧)`, the shift of the
projection at `s` followed by the inverse of that isomorphism. This is the canonical
identification `RF(X)⟦1⟧ = RF(X⟦1⟧)`, resp. `LF(X)⟦1⟧ = LF(X⟦1⟧)`, of Tag 05SU, written out on
that cofinal, resp. initial, family rather than imported; in both halves it is transposed to the
side of the shifted (co)projection, where it appears as `commShiftIso.hom`.

*Quantification.* The values are quantified over universally: in each half the conclusion holds
for every choice of values at the three objects, which exist by the three preceding clauses. This
is stronger than producing one triangle for one choice, and needs no uniqueness statement about
values.

*Hypotheses.* The categories are only pretriangulated, not triangulated: the source's input on
the index categories (Tag 05R9: the category of morphisms of distinguished triangles with all three
components in `W` is filtered and cofinal over `X/W`, `Y/W` and `Z/W`, and dually cofiltered and
initial over `W/X`, `W/Y` and `W/Z`) is a statement about pretriangulated categories, so the
octahedron axiom is not assumed. Saturation of `W`, MS4 of Situation 05S8, is imposed as
`MorphismProperty.IsSaturated` (Tag 05Q8): it is what makes the category of `W`-morphisms of
triangles *full* over `X/W` in the proof of Tag 05R9 — a morphism of `X/W` between two indices
lies in `W` by MS4 and Tag 05Q9 — and that cofinality is the load-bearing step here. It is not a
hypothesis one may drop: by Tag 05RG the class `{f | cone f ∈ 𝒟'}` of a full triangulated
subcategory `𝒟' ⊆ 𝒟` is a multiplicative system compatible with the triangulation which is
saturated exactly when `𝒟'` is thick, so non-saturated such classes exist. Since `IsSaturated`
bundles both calculi of fractions and MS1, none of `W.HasLeftCalculusOfFractions`,
`W.HasRightCalculusOfFractions` and `W.IsMultiplicative` is imposed separately; the ind-side runs
on the left calculus and the pro-side on the right one, and saturation supplies both. Stability of
`W` under the shift is part of `MorphismProperty.IsCompatibleWithTriangulation`, and is what makes
the shifted indices of the third clause of each half available.

Faithfulness. (1) Every hypothesis is used: `T` distinguished is what makes both conclusions of
each half hold (for a non-distinguished triangle definedness at two vertices says nothing about
the third), and the hypotheses on `W` and on the exactness of `F` are what the source's argument
runs on. (2) The base is the source's: `W` is a class of morphisms of the source category `C` of
`F`, the values are objects of the target `H`, and the shift used on both sides is the `ℤ`-shift
of the respective pretriangulated structure. (3) The canonical morphisms `RF(f)`, `RF(g)`,
`RF(h)`, resp. `LF(f)`, `LF(g)`, `LF(h)`, are pinned by their characterising property of Tag 05SA
against the (co)projections of the given value (co)cones, not merely asserted to exist. (4) The
instantiation is not degenerate: for `W` the class of isomorphisms of `C` — a saturated
multiplicative system compatible with the triangulation — both derived functors are defined at
every object with value `F(X)`, and each conclusion is `F.map_distinguished`; the content is that
definedness spreads along distinguished triangles for a `W` for which it holds only on a proper
subcategory. (5) Both sentences of the source are covered, and neither half is a special case of
the other in this repository.

The three two-out-of-three statements are the single statement "defined at `obj₁` and at `obj₂`
implies defined at `obj₃`" read on the rotations of the triangle, together with the fact that
`RF` is defined at `X` if and only if it is defined at `X[n]` (Tag 05SU): the rotation of
`(X, Y, Z, f, g, h)` is `(Y, Z, X[1], g, h, -f[1])`, so the second statement is the first for
`T.rotate` followed by a descent from `X[1]` to `X`, and the third is the first for
`T.rotate.rotate` preceded and followed by such a passage.

*The choice of indices (the source's first two paragraphs).* Before any triangulated input is
used, the source fixes an index `s : X ⟶ X'` of `X/W` with a section `α : A ⟶ F(X')` of the
coprojection, completes `f` and `s` to a square by the Ore condition MS2, and then *replaces* the
resulting index of `Y/W` by a later one so that a section `β : B ⟶ F(Y')` exists for which the
square `α ≫ F(f') = u ≫ β` commutes — the naive square need not commute. This is
`exists_compatible_retraction_square`, proved here for a functor between arbitrary
categories and a class with a left calculus of fractions: the identity that does hold outright is
`α ≫ F(f₁) ≫ d_{t₁} = u`, and the cofinality clause of essential constancy at `Y` turns it into
the commuting square after one enlargement of the index, `β` being a section because the
enlargement is compatible with the coprojections.

*The argument from the chosen indices on.* `isRightDerivedValueAt_obj₃_of_dist_aux`
is the rest of the source's proof, read from those choices. MS6 completes `(s, t)` to a morphism of
distinguished triangles `(s, t, s'') : T ⟶ T'` with `s'' ∈ W`; TR3 completes `(α, β)` to a morphism
of triangles `(α, β, γ) : (A, B, Z₀, RF(f), b, a) ⟶ F(T')`, the target being distinguished because
`F` is exact; and Tag 05SB moves the values at `X` and at `Y` to values at `X'` and `Y'` whose
retractions at the identity indices are `α` and `β` on the nose. Over the category `ℐ` of
`W`-morphisms of distinguished triangles out of `T'` — filtered, and cofinal over each of `X'/W`,
`Y'/W`, `Z'/W` by Tag 05R9, saturation of `W` being what makes it full over them — the base object
is the identity of `T'`, so it is initial and the comparison morphisms are `(α, β, γ)` followed by
the transitions. The five lemma carries the bijectivity of the comparison maps of Tag 05PY(4) at
the first two vertices to the third, that criterion exhibits `Z₀` as the value of the ind-object
over `ℐ`, cofinality of `ℐ ⟶ Z'/W` brings it back to `Z'/W`, and Tag 05SB along `s'' : Z ⟶ Z'`
brings it to `Z/W`.

*The five lemma step.* Its conclusion is the factorization property
`exists_factorization_hom₃`: for a diagram `N : I ⥤ Triangle H` of distinguished
triangles, a distinguished `T₀` and a family of morphisms of triangles `φ i : T₀ ⟶ N i` compatible
with the transitions, if at the first and second vertices every morphism `V ⟶ N(i).objₘ` factors
as `h ≫ φ(k).homₘ` after a transition `i ⟶ k`, and `φ(i).hom₂` is a split monomorphism, then the
same holds at the third vertex. This is the bijectivity of
`Mor(V, T₀.obj₃) ⟶ colim_i Mor(V, N(i).obj₃)` of the source's diagram, in the colimit-free form
the criterion of Tag 05PY(4) consumes: the two hypotheses are the surjectivity and the injectivity
of the comparison maps at the first two vertices, injectivity being free from the splitting, and
the proof is the source's chase through the two exact sequences `Mor(V, -)` of `T₀` and of `N(k)`
(`Triangle.coyoneda_exact₁` and `Triangle.coyoneda_exact₃`), the transitions being carried along
explicitly. Neither filteredness nor smallness of `I` is used. The passage to the shifted vertices,
`exists_factorization_shift`, is the same property for `M ⋙ shiftFunctor H n` and
holds because the shift is an equivalence.

*The injectivity half of the five lemma.* `eq_of_comp_hom₃` is the complementary
statement: with the same data, and with `φ(i).hom₁` split mono as well, two
morphisms `V ⟶ T₀.obj₃` that agree after `φ(i).hom₃` are equal. Together with
`exists_factorization_hom₃` this is the bijectivity of the source's comparison map at the third
vertex, in the two halves the criterion of Tag 05PY(4) consumes. Both splittings are available in
the application: `φ(i).hom₁ = α ≫ F(t₁)` is split by the coprojection of the value at `X'` at the
index `t₁`, because the base index of `ℐ` is the identity of `T'` and the transition out of it is
the structure morphism of the object of `ℐ`.

*Transport of a pinned value along a cofinal functor of index categories.* Tag 0A1S is available
in the library (`essentiallyConstant_comp_final_of`, `essentiallyConstant_of_comp_final`) with the
value existentially quantified, which is not enough here: the argument needs the cocone and the
retraction that the source names. The two directions with the data kept are
`isEssentiallyConstantWith_comp_final` (restriction; the whiskered cocone, at any
index `j₀` under the given one, the retraction being `r ≫ M(τ₀)`) and
`isEssentiallyConstantWith_of_comp_final` (extension along
`Functor.Final.extendCocone`, which keeps the vertex and the coprojections at objects in the
image). Their proofs are the library's, run on the pinned data; the combinatorial core,
`exists_lift_cospan`, is the library's lemma. `isEssentiallyConstantWith_changeIndex`
moves the retraction to any other index carrying a section of its coprojection — what lets the
base index over `ℐ` be the identity of `T'`, with retractions `α`, `β`, `γ` on the nose — and
`MorphismProperty.isFiltered_under_of_hasLeftCalculusOfFractions` is Tag 05Q0, filteredness of
`X/W`, which those transports need.

*Moving a value along a morphism of `W`.* Tag 05SB is used twice, in both directions, and each time
with the cocone kept rather than existentially quantified.
`exists_isEssentiallyConstantWith_at_index` moves the value at `X` forward to `X'`
along an index `s` of `X/W` at which a section `α` of the coprojection is given: the value at `X'`
that Tag 05SB provides, extended along the inverse of the isomorphism of Tag 05SB, has vertex
`RF(X)` and coprojection `c_s` at the identity index, so `α` splits that coprojection and the base
index of the witness may be moved there (`isEssentiallyConstantWith_changeIndex`).
`exists_isRightDerivedValueAt_of_mem` moves a value at `X'` back to `X` along
`s : X ⟶ X'` in `W`, together with the formula `ι_a = F(f) ≫ d_b` for its coprojections along every
square `a ≫ f = s ≫ b`, which is the characterisation of that same isomorphism.

*The two compatibility clauses come for free.* Once the value `ι₃` at `Z` is in hand, the clauses
pinning `b` and `a` as the morphisms of Tag 05SA need no diagram chase: the induced morphisms `v`
and `w` of `exists_map_of_isRightDerivedValueAt` satisfy them by construction, and `b = v`, `a = w`
are two instances of one computation, `eq_of_split_comp_eq` — a morphism out of a value
is determined by one splitting of one coprojection. The splitting is `γ`, which splits the
coprojection of `ι₃` at the index `sz` of the MS6 morphism of triangles: indeed
`v = β ≫ (d_{sy} ≫ v) = β ≫ F(T'.mor₂) ≫ ι₃(sz) = b ≫ γ ≫ ι₃(sz) = b` by the second TR3 square,
and symmetrically `w = γ ≫ (ι₃(sz) ≫ w) = γ ≫ F(T'.mor₃) ≫ (commShiftIso).app X' ≫
(c_{sx})⟦1⟧ = a ≫ (α ≫ c_{sx})⟦1⟧ = a` by the third. For `a` the induced morphism goes to a value
`c₁` at `X⟦1⟧`, which exists by Tag 05SU(1), and is transported to `RF(X)⟦1⟧` along the isomorphism
`exists_iso_shift_of_isRightDerivedValueAt`, which is compatible with the coprojections
at the shifted indices `s⟦1⟧`: restricted along `s ↦ s⟦1⟧`, which is full and essentially
surjective, the ind-object at `X⟦1⟧` and the shift of the ind-object at `X` carry two essentially
constant — hence colimit — cocones on one and the same diagram.

*The criterion of Tag 05PY(4) at a large index category.* The criterion itself is available here
at an index category of arbitrary size, in the colimit-free form
`exists_isEssentiallyConstantWith_of_hom_factorization`: the bijectivity of
`Mor(V, X) ⟶ colim_j Mor(V, M(j))`, `h ↦ [h ≫ ρ]`, is expressed by the transition data that
witnesses equality of classes in a filtered colimit of Hom-sets, so that nothing is said about a
colimit and no smallness is required. The library's
`CategoryTheory.EssentiallyConstantInd.isEssentiallyConstantWith_of_bijective_homComparison` asks
instead for the colimit in `Type v`, which is unavailable for `X/W` — its objects live in
`Type (max u v)` while the Hom-sets of the target live in `Type v`. What essential
constancy contributes to that comparison is proved in the same form:
`exists_factorization_of_pinned`, the surjectivity of the comparison map read on a
family of comparison morphisms, and `comp_map_comp_ι_app`, that each member of such a
family is split by a coprojection.

Tag 05SU(1), that `RF` is defined at `X` if and only if it is defined at `X[n]`, is proved here
(`exists_isRightDerivedValueAt_shift_iff`) from three transport properties of
essential constancy stated in the generality in which they hold, for a diagram indexed by an
arbitrary category: it is preserved by an arbitrary functor on the target
(`isEssentiallyConstantWith_comp`), invariant under an isomorphism of diagrams
(`isEssentiallyConstantWith_ofIso`) and inherited by the restriction along a full and
essentially surjective functor of index categories (`isEssentiallyConstantWith_precomp`).
Filteredness is used in none of the three. The index functor `X/W ⥤ (X[n])/W`, `s ↦ s[n]`, is
full because `shiftFunctor C n` is, and essentially surjective because an index
`t : X[n] ⟶ U` is the shift of `X ⟶ X[n][-n] ⟶ U[-n]`, which lies in `W` by stability under
the shift and respect for isomorphisms; the commutation of `F` with the shift then identifies
the restricted diagram with `(X/W ⥤ H) ⋙ shiftFunctor H n`, and applying `shiftFunctor H (-n)`
returns the ind-object at `X`.

## References

* [Stacks project, Tag 05SC](https://stacks.math.columbia.edu/tag/05SC), Lemma 13.14.5; the
  situation is Tag 05S8, definedness is Tag 05S9, the morphisms `RF(f)` are Tag 05SA, saturation
  is Tag 05Q8 and the filtered index category is Tag 05R9.
* [Stacks project, Tag 05SC](https://stacks.math.columbia.edu/tag/05SC), Lemma 13.14.5; the
  induced morphisms are Tag 05SA, the shift is Tag 05SU and the index category of the argument
  is Tag 05R9.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped CategoryTheory.Pretriangulated.Opposite

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace DerivedFunctorValues

section Values

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  (F : C ⥤ H) (W : MorphismProperty C)

/-- The ind-object `X/W ⟶ H`, `(s : X ⟶ X') ↦ F(X')` of Tag 05S9. -/
public abbrev indDiagram (X : C) : W.Under ⊤ X ⥤ H :=
  MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F

/-- The identity index `𝟙 X` of the category `X/W`. It is initial there, and it is the index at
which the retractions of the source's proof of Tag 05SC are taken. -/
abbrev idIndex (W : MorphismProperty C) [W.ContainsIdentities] (X : C) : W.Under ⊤ X :=
  MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X)

/-- A cocone at which the ind-object is essentially constant is a colimit cocone. -/
lemma nonempty_isColimit_of_isRightDerivedValueAt {X : C}
    {c : Cocone (indDiagram F W X)} (hc : F.IsRightDerivedValueAt W X c) :
    Nonempty (IsColimit c) := by
  obtain ⟨s₀, r, hr, hcof⟩ := hc
  refine ⟨EssentiallyConstantInd.IsEssentiallyConstantWith.isColimit
    (M := indDiagram F W X) (t := c) (i := s₀) (r := r) ⟨hr, fun j => ?_⟩⟩
  obtain ⟨t, u, v, huv⟩ := hcof j
  exact ⟨t, v, u, huv⟩

/-- Two values of `RF` at the same object are isomorphic compatibly with the coprojections. -/
lemma exists_iso_of_isRightDerivedValueAt {X : C} {c d : Cocone (indDiagram F W X)}
    (hc : F.IsRightDerivedValueAt W X c) (hd : F.IsRightDerivedValueAt W X d) :
    ∃ e : c.pt ≅ d.pt, ∀ s, c.ι.app s ≫ e.hom = d.ι.app s := by
  obtain ⟨hc'⟩ := nonempty_isColimit_of_isRightDerivedValueAt F W hc
  obtain ⟨hd'⟩ := nonempty_isColimit_of_isRightDerivedValueAt F W hd
  exact ⟨hc'.coconePointUniqueUpToIso hd', fun s => hc'.comp_coconePointUniqueUpToIso_hom hd' s⟩

variable [W.HasLeftCalculusOfFractions]

/-- The Ore condition MS2, read on the index categories: a morphism `f : X ⟶ Y` and an index
`s` of `X/W` are completed by an index `t` of `Y/W` and a morphism `f' : X' ⟶ Y'` with
`f ≫ t = s ≫ f'`. -/
lemma exists_leftSquare_under {X Y : C} (f : X ⟶ Y) (s : W.Under ⊤ X) :
    ∃ (t : W.Under ⊤ Y) (f' : s.right ⟶ t.right), f ≫ t.hom = s.hom ≫ f' := by
  obtain ⟨Y', t, ht, f', hf'⟩ := exists_leftSquare f s.hom s.prop
  exact ⟨MorphismProperty.Under.mk ⊤ t ht, f', hf'⟩

/-- The composite `F(X') ⟶ F(Y') ⟶ d.pt` attached to a square `f ≫ t = s ≫ f'` over a fixed
index `s` of `X/W` does not depend on the square. This is the well-definedness step in the
construction of the induced morphism of Tag 05SA. -/
public lemma map_comp_ι_app_eq {X Y : C} (f : X ⟶ Y) {d : Cocone (indDiagram F W Y)}
    (s : W.Under ⊤ X) (t₁ t₂ : W.Under ⊤ Y) (f₁ : s.right ⟶ t₁.right) (f₂ : s.right ⟶ t₂.right)
    (h₁ : f ≫ t₁.hom = s.hom ≫ f₁) (h₂ : f ≫ t₂.hom = s.hom ≫ f₂) :
    F.map f₁ ≫ d.ι.app t₁ = F.map f₂ ≫ d.ι.app t₂ := by
  obtain ⟨V, k, hk, m, hkm⟩ := exists_leftSquare t₂.hom t₁.hom t₁.prop
  obtain ⟨V', q, hq, hq'⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
    (f₁ ≫ m) (f₂ ≫ k) s.hom s.prop
    (by rw [← Category.assoc, ← h₁, ← Category.assoc, ← h₂, Category.assoc, Category.assoc, hkm])
  have key : t₁.hom ≫ m ≫ q = t₂.hom ≫ k ≫ q := by
    rw [← Category.assoc, ← hkm, Category.assoc]
  have hmem : W (t₂.hom ≫ k ≫ q) := W.comp_mem _ _ t₂.prop (W.comp_mem _ _ hk hq)
  obtain ⟨t₃, a, b, hab⟩ : ∃ (t₃ : W.Under ⊤ Y) (a : t₁ ⟶ t₃) (b : t₂ ⟶ t₃),
      f₁ ≫ a.right = f₂ ≫ b.right := by
    refine ⟨MorphismProperty.Under.mk ⊤ (t₂.hom ≫ k ≫ q) hmem,
      MorphismProperty.Under.homMk (m ≫ q) key trivial,
      MorphismProperty.Under.homMk (k ≫ q) rfl trivial, ?_⟩
    show f₁ ≫ m ≫ q = f₂ ≫ k ≫ q
    rw [← Category.assoc, ← Category.assoc, hq']
  have hw₁ : F.map a.right ≫ d.ι.app t₃ = d.ι.app t₁ := d.w a
  have hw₂ : F.map b.right ≫ d.ι.app t₃ = d.ι.app t₂ := d.w b
  calc F.map f₁ ≫ d.ι.app t₁
      = F.map f₁ ≫ F.map a.right ≫ d.ι.app t₃ := by rw [hw₁]
    _ = (F.map f₁ ≫ F.map a.right) ≫ d.ι.app t₃ := (Category.assoc _ _ _).symm
    _ = F.map (f₁ ≫ a.right) ≫ d.ι.app t₃ := by rw [F.map_comp]
    _ = F.map (f₂ ≫ b.right) ≫ d.ι.app t₃ := by rw [hab]
    _ = (F.map f₂ ≫ F.map b.right) ≫ d.ι.app t₃ := by rw [F.map_comp]
    _ = F.map f₂ ≫ F.map b.right ≫ d.ι.app t₃ := Category.assoc _ _ _
    _ = F.map f₂ ≫ d.ι.app t₂ := by rw [hw₂]

/-- Reassociation, used to finish the construction of the induced morphism below: substituting
`b = A ≫ r ≫ p` into `(b ≫ q) ≫ D` gives `A ≫ r ≫ (p ≫ q) ≫ D`. It is stated for abstract
morphisms of `H` because the composites in question involve the coprojections of a cocone on the
ind-object, whose source is `F(X')` only after unfolding the diagram, so that `Category.assoc`
cannot be used as a rewrite rule on them. -/
private lemma comp_reassoc {P Q R S T U : H} {A : P ⟶ Q} {r : Q ⟶ R} {p : R ⟶ S} {b : P ⟶ S}
    (h : b = A ≫ r ≫ p) (q : S ⟶ T) (D : T ⟶ U) :
    A ≫ r ≫ (p ≫ q) ≫ D = (b ≫ q) ≫ D := by
  rw [h]; simp only [Category.assoc]

/-- A retraction is carried along a splitting: if `α ≫ p = 𝟙`, `φ ≫ ψ = 𝟙` and `p ≫ φ = q`, then
`α ≫ q ≫ ψ = 𝟙`. Like `comp_reassoc` it is stated for abstract morphisms of `H`, because the
morphisms it is applied to are coprojections of a cocone on the ind-object, whose source and target
are `F(X')` and the value only after unfolding the diagram. -/
lemma comp_comp_eq_id {P Q R : H} {α : P ⟶ Q} {p : Q ⟶ P} {φ : P ⟶ R} {ψ : R ⟶ P}
    {q : Q ⟶ R} (hα : α ≫ p = 𝟙 P) (hφψ : φ ≫ ψ = 𝟙 P) (hq : p ≫ φ = q) :
    α ≫ q ≫ ψ = 𝟙 P := by
  rw [← hq, Category.assoc, hφψ, Category.comp_id, hα]

/-- **A morphism out of a value is determined by one splitting of one coprojection.** If `p` is
split by `β`, if `p ≫ v` factors as `m ≫ k`, if `b ≫ g = β ≫ m` and if `g ≫ k = 𝟙`, then `b = v`.
This is the computation by which the morphisms `b` and `a` of a distinguished triangle of values are
identified with the morphisms of Tag 05SA: `v` is the morphism of Tag 05SA and `g` is the section
provided by the chosen index. Like `comp_reassoc` it is stated for abstract morphisms of `H`. -/
lemma eq_of_split_comp_eq {P Q R S : H} {β : P ⟶ Q} {p : Q ⟶ P} {v : P ⟶ R} {m : Q ⟶ S}
    {k : S ⟶ R} {b : P ⟶ R} {g : R ⟶ S} (hβ : β ≫ p = 𝟙 P) (h₁ : p ≫ v = m ≫ k)
    (h₂ : b ≫ g = β ≫ m) (h₃ : g ≫ k = 𝟙 R) : b = v :=
  calc b = b ≫ 𝟙 R := (Category.comp_id b).symm
    _ = (b ≫ g) ≫ k := by rw [← h₃, Category.assoc]
    _ = (β ≫ m) ≫ k := by rw [h₂]
    _ = (β ≫ p) ≫ v := by rw [Category.assoc, ← h₁, Category.assoc]
    _ = v := by rw [hβ, Category.id_comp]

/-- Transporting a morphism to a value along an isomorphism of values: from `x ≫ w = y ≫ z`,
`κ ≫ eh = z` and `eh ≫ ei = 𝟙` it follows that `x ≫ w ≫ ei = y ≫ κ`. Like `comp_reassoc` it is
stated for abstract morphisms of `H`. -/
lemma comp_comp_inv_eq {P Q R S V : H} {x : P ⟶ Q} {w : Q ⟶ R} {y : P ⟶ S} {z : S ⟶ R}
    {κ : S ⟶ V} {eh : V ⟶ R} {ei : R ⟶ V} (h₁ : x ≫ w = y ≫ z) (h₂ : κ ≫ eh = z)
    (h₃ : eh ≫ ei = 𝟙 V) : x ≫ w ≫ ei = y ≫ κ := by
  rw [← Category.assoc, h₁, ← h₂, Category.assoc, Category.assoc, h₃, Category.comp_id]

/-- **Tag 05SA(1)**, existence. If `RF` is defined at `X` with value `c`, then a morphism
`f : X ⟶ Y` induces a morphism `c.pt ⟶ d.pt` to the vertex of any cocone `d` on the ind-object
at `Y`, compatible with the coprojections along every square `f ≫ t = s ≫ f'` with `s` an index
of `X/W` and `t` an index of `Y/W`. -/
public lemma exists_map_of_isRightDerivedValueAt {X Y : C} (f : X ⟶ Y)
    {c : Cocone (indDiagram F W X)} (hc : F.IsRightDerivedValueAt W X c)
    (d : Cocone (indDiagram F W Y)) :
    ∃ u : c.pt ⟶ d.pt, ∀ (s : W.Under ⊤ X) (t : W.Under ⊤ Y) (f' : s.right ⟶ t.right),
      f ≫ t.hom = s.hom ≫ f' → c.ι.app s ≫ u = F.map f' ≫ d.ι.app t := by
  obtain ⟨s₀, r, hr, hcof⟩ := hc
  obtain ⟨Y₀, t₀, ht₀, f₀, hsq₀⟩ := exists_leftSquare f (X' := s₀.right) s₀.hom s₀.prop
  refine ⟨r ≫ F.map f₀ ≫ d.ι.app (MorphismProperty.Under.mk ⊤ t₀ ht₀), ?_⟩
  intro s t f' hsq
  obtain ⟨k, β, α, hk⟩ := hcof s
  obtain ⟨Yk, tk, htk, fk, hsqk⟩ := exists_leftSquare f (X' := k.right) k.hom k.prop
  have key : ∀ (s' : W.Under ⊤ X) (a : s' ⟶ k) (t : W.Under ⊤ Y) (f' : s'.right ⟶ t.right),
      f ≫ t.hom = s'.hom ≫ f' → F.map f' ≫ d.ι.app t
        = F.map (a.right ≫ fk) ≫ d.ι.app (MorphismProperty.Under.mk ⊤ tk htk) := by
    intro s' a t f' hsq'
    refine map_comp_ι_app_eq F W f s' t (MorphismProperty.Under.mk ⊤ tk htk) f'
      (a.right ≫ fk) hsq' ?_
    refine hsqk.trans ?_
    simp [← MorphismProperty.Under.w a]
  have e₁ := key s₀ α (MorphismProperty.Under.mk ⊤ t₀ ht₀) f₀ hsq₀
  have e₂ := key s β t f' hsq
  erw [e₁, e₂, F.map_comp, F.map_comp]
  exact comp_reassoc hk _ _

/-- **The choice of compatible retractions** in the source's proof of Tag 05SC. Let `RF` be
defined at `X` with value `c` and at `Y` with value `d`, and let `u : c.pt ⟶ d.pt` be the induced
morphism of Tag 05SA attached to `f : X ⟶ Y`. Then there are indices `s : X ⟶ X'`, `t : Y ⟶ Y'`,
a morphism `f' : X' ⟶ Y'` filling the square `f ≫ t = s ≫ f'`, and sections
`α : c.pt ⟶ F(X')`, `β : d.pt ⟶ F(Y')` of the coprojections at `s` and `t`, such that the square
`α ≫ F(f') = u ≫ β` commutes.

*Argument (the source's).* Take for `s` the index and for `α` the section given by essential
constancy at `X`, and complete `f` and `s` to a square `f ≫ t₁ = s ≫ f₁` by the Ore condition
MS2. The square `α ≫ F(f₁) = u ≫ β₁` need not commute for any candidate `β₁`; what does hold, by
the defining property of `u` at the square `(s, t₁, f₁)` and `α ≫ c_s = 𝟙`, is
`α ≫ F(f₁) ≫ d_{t₁} = u`. Essential constancy at `Y` provides a transition `w : t₁ ⟶ t'` and an
index morphism `v` from the base index with `F(w) = d_{t₁} ≫ r ≫ F(v)`; taking
`β := r ≫ F(v)` and `f' := f₁ ≫ w` turns that identity into the commuting square, while `β` is a
section because `F(v) ≫ d_{t'} = d_{base}`. -/
lemma exists_compatible_retraction_square {X Y : C} (f : X ⟶ Y)
    {c : Cocone (indDiagram F W X)} (hc : F.IsRightDerivedValueAt W X c)
    {d : Cocone (indDiagram F W Y)} (hd : F.IsRightDerivedValueAt W Y d)
    (u : c.pt ⟶ d.pt)
    (hu : ∀ (s : W.Under ⊤ X) (t : W.Under ⊤ Y) (f' : s.right ⟶ t.right),
      f ≫ t.hom = s.hom ≫ f' → c.ι.app s ≫ u = F.map f' ≫ d.ι.app t) :
    ∃ (s : W.Under ⊤ X) (t : W.Under ⊤ Y) (α : c.pt ⟶ F.obj s.right)
      (β : d.pt ⟶ F.obj t.right) (f' : s.right ⟶ t.right),
      α ≫ c.ι.app s = 𝟙 c.pt ∧ β ≫ d.ι.app t = 𝟙 d.pt ∧
        f ≫ t.hom = s.hom ≫ f' ∧ α ≫ F.map f' = u ≫ β := by
  obtain ⟨s₀, α, hα, -⟩ := hc
  obtain ⟨t₀, r, hr, hcof⟩ := hd
  obtain ⟨ty, f₁, hsq₁⟩ := exists_leftSquare_under W f s₀
  obtain ⟨t', w, v, hwv⟩ := hcof ty
  have hstep : α ≫ F.map f₁ ≫ d.ι.app ty = u :=
    calc α ≫ F.map f₁ ≫ d.ι.app ty = α ≫ c.ι.app s₀ ≫ u :=
        congrArg (fun z => α ≫ z) (hu s₀ ty f₁ hsq₁).symm
      _ = (α ≫ c.ι.app s₀) ≫ u := (Category.assoc _ _ _).symm
      _ = 𝟙 c.pt ≫ u := by rw [hα]
      _ = u := Category.id_comp u
  refine ⟨s₀, t', α, r ≫ F.map v.right, f₁ ≫ w.right, hα, ?_, ?_, ?_⟩
  · have hv : F.map v.right ≫ d.ι.app t' = d.ι.app t₀ := d.w v
    calc (r ≫ F.map v.right) ≫ d.ι.app t' = r ≫ F.map v.right ≫ d.ι.app t' :=
          Category.assoc _ _ _
      _ = r ≫ d.ι.app t₀ := by rw [hv]
      _ = 𝟙 d.pt := hr
  · have hw : ty.hom ≫ w.right = t'.hom := MorphismProperty.Under.w w
    calc f ≫ t'.hom = f ≫ ty.hom ≫ w.right := by rw [hw]
      _ = (f ≫ ty.hom) ≫ w.right := (Category.assoc _ _ _).symm
      _ = (s₀.hom ≫ f₁) ≫ w.right := by rw [hsq₁]
      _ = s₀.hom ≫ f₁ ≫ w.right := Category.assoc _ _ _
  · have e₁ : F.map f₁ ≫ d.ι.app ty ≫ r ≫ F.map v.right
        = (F.map f₁ ≫ d.ι.app ty) ≫ r ≫ F.map v.right := (Category.assoc _ _ _).symm
    calc α ≫ F.map (f₁ ≫ w.right) = α ≫ F.map f₁ ≫ F.map w.right := by rw [F.map_comp]
      _ = α ≫ F.map f₁ ≫ d.ι.app ty ≫ r ≫ F.map v.right :=
          congrArg (fun z => α ≫ F.map f₁ ≫ z) hwv
      _ = α ≫ (F.map f₁ ≫ d.ι.app ty) ≫ r ≫ F.map v.right := congrArg (fun z => α ≫ z) e₁
      _ = (α ≫ F.map f₁ ≫ d.ι.app ty) ≫ r ≫ F.map v.right := (Category.assoc _ _ _).symm
      _ = u ≫ r ≫ F.map v.right := by rw [hstep]

end Values

end DerivedFunctorValues

end

end
