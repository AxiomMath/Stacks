module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Order.SuccPred.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Ring.Basic
public import StacksFrontier.Algebra.Homology.Resolution.Defs.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution.BoundedAbove

/-!
# Morphisms out of K-projective complexes

Lifting and homotopy properties of K-projective complexes ([Stacks, Tag 0648], [Stacks, Tag 0649],
[Stacks, Tag 064A], [Stacks, Tag 064B], [Stacks, Tag 064D]) and the horseshoe lemma for
projective resolutions of complexes ([Stacks, Tag 064C]).
-/

section

/-!
# Projective resolutions of complexes, and morphisms out of K-projective complexes

Let `A` be an abelian category. A cochain complex `P` of `A` which is bounded above and consists
of projective objects is *K-projective*: every morphism from it to an acyclic complex is
null-homotopic. This file collects what such a `P` does, all of it dual to the K-injective
material of `StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution`.

First, a morphism `γ : P ⟶ K` out of a K-projective complex factors through any
quasi-isomorphism `α : L ⟶ K` up to homotopy. In the diagram

```text
  K  <--α--  L
  ^         ^
   \ γ     / β
     \    /
       P
```

the arrow `β` exists with `β ≫ α` homotopic to `γ`: the cone of `α` is acyclic and the
cohomological functor `Mor_{K(A)}(P, -)` kills it, so postcomposition with `α` is a bijection
`Mor_{K(A)}(P, L) → Mor_{K(A)}(P, K)`. When moreover the terms of `P` are projective and `α` is
an epimorphism in every degree the factorization holds on the nose: each component of the
homotopy factors through the epimorphism `α`, and subtracting the null homotopic map of that
family turns the homotopy into an equality. Bijectivity is injective as well as surjective, so
`β` is unique up to homotopy: two morphisms `β₁, β₂ : P ⟶ L` whose composites with `α` are
homotopic are themselves homotopic.

Secondly, morphisms out of a K-projective complex are the same in the homotopy and in the
derived category: the localization functor `Qh : K(A) ⥤ D(A)` induces a bijection
`Mor_{K(A)}(P, L) → Mor_{D(A)}(P, L)`, so no formal fraction `γ α⁻¹` is needed to describe one.
That property in fact characterizes K-projectivity, since a morphism from `P` to an acyclic `L`
dies in `D(A)`, where `L` is a zero object, hence is null-homotopic. Combined with truncation it
gives a vanishing theorem: if `P` is concentrated in degrees `≥ n` and `K` has no cohomology
above some `m < n`, then `Mor_{K(A)}(P, K) = Mor_{D(A)}(P, K) = 0`, because `K` is
quasi-isomorphic to `τ_{≤ m} K`, which vanishes in every degree `≥ n`.

Finally, resolutions can be chosen compatibly along a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes: given any projective resolution `π : P ⟶ X₃` of
the quotient, there are projective resolutions `π₁` of `X₁` and `π₂` of `X₂` fitting into a
short exact sequence `0 ⟶ P₁ ⟶ P₂ ⟶ P ⟶ 0` of resolving complexes with both squares commuting —
the resolution of the quotient may be the prescribed one. The middle term is the *twisted direct
sum* of `P₁` and `P` along a family `δ : Pⁿ ⟶ P₁ⁿ⁺¹`, the complex with terms `P₁ⁿ ⊞ Pⁿ` and
differential `(d, δ; 0, d)`: it is degreewise split, hence an extension of `P` by `P₁`. The
family `δ` is obtained from the defect `h ≫ d - d ≫ h` of a degreewise — not chainwise — lift `h`
of `π` along `X₂ ⟶ X₃`, which the projectivity of the terms of `P` supplies; the defect is
killed by `X₂ ⟶ X₃`, so it factors through `X₁`, and the strict factorization above lets it be
lifted through a degreewise epimorphic resolution of `X₁`. The resolution map `P₂ ⟶ X₂` is then
a quasi-isomorphism by the five lemma applied to the two long exact homology sequences.

## Main results

* `CochainComplex.IsKProjective.exists_lift_of_quasiIso`: a morphism out of a K-projective
  complex factors through a quasi-isomorphism, up to homotopy, and exactly under the extra
  hypotheses above.
* `CochainComplex.IsKProjective.nonempty_homotopy_of_comp_quasiIso`: that factorization is
  unique up to homotopy.
* `CochainComplex.isKProjective_iff_Qh_map_bijective`: `P` is K-projective if and only if `Qh`
  induces a bijection `Mor_{K(A)}(P, L) → Mor_{D(A)}(P, L)` for every object `L` of `K(A)`.
* `CochainComplex.IsKProjective.hom_eq_zero_of_isStrictlyGE_of_isLE`: no nonzero morphism, in
  `K(A)` or in `D(A)`, from a K-projective complex concentrated in degrees `≥ n` to a complex
  with no cohomology above `m < n`.
* `CochainComplex.exists_shortExact_isProjectiveResolution`: a short exact sequence of cochain
  complexes whose sub-object is bounded above, together with a prescribed projective resolution
  of its quotient, extends to a short exact sequence of projective resolutions.

## Implementation notes

Being K-projective is Mathlib's class `CochainComplex.IsKProjective`, which
`CochainComplex.isKProjective_of_projective` derives from `P.IsStrictlyLE d` (Mathlib's spelling
of `Pⁱ = 0` for `d < i`) together with `∀ n, Projective (P.X n)`. Every statement here is
therefore the source's for a complex bounded above with projective terms, and remains meaningful
for an unbounded K-projective complex; for a tag that is a generalization, never a weakening.
Being a quasi-isomorphism is the class `QuasiIso`. A `Homotopy` is data rather than a
proposition, so "commutes up to homotopy" is `Nonempty (Homotopy _ _)`, equivalently equality of
the images in `HomotopyCategory A (.up ℤ)`.

Two assertions of [Stacks 0649] are the two conjuncts of one theorem, with the hypotheses that
only the second uses attached to its own conjunct: boundedness of `P` is not among them, since a
homotopy `h : β ≫ α ≃ γ` has components `P.X i ⟶ K.X j` which lift through the epimorphisms
`α.f j` as soon as each `P.X i` is projective. Degreewise projectivity of `P` cannot be dropped
from the second part: over `ℤ`, with `P = K` the contractible complex `ℤ/2 --id--> ℤ/2` in
degrees `0, 1`, the degreewise surjective quasi-isomorphism `α : (ℤ --id--> ℤ) ⟶ K` admits no
`β` with `β ≫ α = 𝟙 K`, since `Hom(ℤ/2, ℤ) = 0`. Nor can K-projectivity be dropped from the
first: over `k[x]/(x²)` the unbounded acyclic complex `⋯ → R → R → ⋯` with differential `x`
consists of free modules but is not contractible.

[Stacks 064A] contracts the source's third arrow `γ : P ⟶ K` and its two homotopies
`βᵢ ≫ α ≃ γ` into the single hypothesis `Homotopy (β₁ ≫ α) (β₂ ≫ α)`; composing the first
homotopy with the inverse of the second gives it, and the source's form is recovered by taking
`γ := β₂ ≫ α`, so no generality is lost and `γ`, which the conclusion does not mention, is not
carried along as a dead hypothesis.

[Stacks 064B] is stated as an `iff`. Only the forward implication is the source's, and only it is
Mathlib's `CochainComplex.IsKProjective.Qh_map_bijective`; the converse is the content added
here, so that one name carries a characterization of K-projectivity rather than a second
spelling of an existing lemma. It is the K-projective form of [Stacks 070I] `(1) ↔ (3)`, and the
name mutates that of its Mathlib sibling `CochainComplex.isKProjective_iff_leftOrthogonal`. The
dual of the forward implication is [Stacks 05TG].

[Stacks 064D] replaces the source's distinguished triangle `(τ_{≤ n-1} K, K, τ_{≥ n} K)` by the
truncation itself: the third vertex is acyclic exactly because the first map is a
quasi-isomorphism, and `DerivedCategory.Q` inverts quasi-isomorphisms, so
`CochainComplex.ιTruncLE` alone does the work of the triangle together with the source's
[Stacks 0647] — itself subsumed by `CochainComplex.IsKProjective`. Its hypothesis
`Hⁱ(K) = 0` for `i ≥ n` is `K.IsLE m` for `m := n - 1`; as in Mathlib's
`DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective` the two bounds are kept as
separate variables with `m < n`, which applies without rewriting when a bound is given in
another form. `IsLE` is the *cohomological* condition, not the strict vanishing `IsStrictlyLE`
of the terms. Both halves of the source's chain of equalities of Hom-sets are stated: they are
equivalent given `P.IsKProjective`, by [Stacks 064B], which is how the source reads the first
equality, and both are kept so that the statement is the tag rather than half of it.

[Stacks 064C] is stated for a *given* projective resolution of the quotient, which is the
source's "we may assume `P₃ = P`"; the unqualified existence assertion of the source follows by
resolving the quotient with [Stacks 0646]. The source writes `Comp⁺(C)`, but a projective
resolution in the sense of [Stacks 0644] is a quasi-isomorphism from a complex bounded *above*,
so boundedness above is what is assumed, and only of the sub-object: no hypothesis on the other
two terms is used and none is imposed. The upper row is given by its components `P₁`, `P₂`, `i`,
`p` rather than as a morphism of short complexes, because that is what expresses `P₃ = P` on the
nose. Its middle term is built by hand as `twist`, a degreewise biproduct with a differential
twisted by a `1`-cocycle, rather than as `(CochainComplex.mappingCone δ)⟦-1⟧` to which it is
isomorphic: the construction needs the two morphisms `P₁ ⟶ P₂` and `P₂ ⟶ P` on the nose, with
the induced short exact sequence of complexes and no shift intervening.

Two general facts used below are absent from Mathlib and are private here:
`quasiIso_τ₂_of_shortExact`, the `τ₂` analogue of
`HomologicalComplex.HomologySequence.quasiIso_τ₃`, which unlike the variant in
`StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution` needs no hypothesis that
every degree have a predecessor and a successor; and
`hom_eq_zero_of_isStrictlyGE_of_isStrictlyLE`, that a morphism from a complex strictly `≥ n` to
one strictly `≤ m` vanishes when `m < n`.

## References

* [Stacks, Tag 0649](https://stacks.math.columbia.edu/tag/0649)
* [Stacks, Tag 064A](https://stacks.math.columbia.edu/tag/064A)
* [Stacks, Tag 064B](https://stacks.math.columbia.edu/tag/064B)
* [Stacks, Tag 064C](https://stacks.math.columbia.edu/tag/064C)
* [Stacks, Tag 064D](https://stacks.math.columbia.edu/tag/064D)
* [Stacks, Tag 0648](https://stacks.math.columbia.edu/tag/0648)
* [Stacks, Tag 05TF](https://stacks.math.columbia.edu/tag/05TF)

## Tags

K-projective complex, projective resolution, quasi-isomorphism, homotopy, derived category
-/

@[expose] public section

universe w v u u' v'

open CategoryTheory

section Homotopy

/-- Correcting a factorization by a null homotopic map. If `h` is a homotopy from `β ≫ α` to `γ`
and the family `hom` of morphisms `P.X i ⟶ L.X j` factors the components of `h` through `α`, i.e.
`hom i j ≫ α.f j = h.hom i j`, then subtracting the null homotopic map of `hom` from `β` turns
the homotopy into an equality: `(β - nullHomotopicMap hom) ≫ α = γ`.

Indeed postcomposition with `α` takes the null homotopic map of `hom` to the null homotopic map
of `fun i j => hom i j ≫ α.f j`, which is that of `h.hom` by hypothesis, hence is `β ≫ α - γ`
because a homotopy exhibits the difference of the two maps it connects as a null homotopic map. -/
private lemma sub_nullHomotopicMap_comp_eq {ι : Type*} {V : Type u} [Category.{v} V]
    [Preadditive V] {c : ComplexShape ι} {P K L : HomologicalComplex V c} {α : L ⟶ K} {β : P ⟶ L}
    {γ : P ⟶ K} (h : Homotopy (β ≫ α) γ) (hom : ∀ i j, P.X i ⟶ L.X j)
    (hα : ∀ i j, hom i j ≫ α.f j = h.hom i j) :
    (β - Homotopy.nullHomotopicMap hom) ≫ α = γ := by
  rw [Preadditive.sub_comp, Homotopy.nullHomotopicMap_comp, funext₂ hα,
    ← Homotopy.sub_eq_nullHomotopicMap h, sub_sub_cancel]

/-- A homotopy can be removed from a factorization through a degreewise epimorphism when the
source has projective terms: if `α` is an epimorphism in every degree, every term of `P` is a
projective object and `β₀ ≫ α` is homotopic to `γ`, then `γ = β ≫ α` for some `β`. Each component
of the homotopy factors through `α` by projectivity, and subtracting the null homotopic map of
the family of factorizations from `β₀` gives such a `β`. -/
private lemma exists_comp_eq_of_homotopy {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V]
    {c : ComplexShape ι} {P K L : HomologicalComplex V c} [∀ n, Projective (P.X n)] {α : L ⟶ K}
    [∀ n, Epi (α.f n)] {β₀ : P ⟶ L} {γ : P ⟶ K} (h : Homotopy (β₀ ≫ α) γ) :
    ∃ β : P ⟶ L, β ≫ α = γ :=
  ⟨β₀ - Homotopy.nullHomotopicMap fun i j => Projective.factorThru (h.hom i j) (α.f j),
    sub_nullHomotopicMap_comp_eq h _ fun _ _ => Projective.factorThru_comp _ _⟩

end Homotopy

section KProjective

/-- The image in the homotopy category of a K-projective cochain complex is colocal for the
quasi-isomorphisms: postcomposition with a quasi-isomorphism of `K(A)` is bijective on morphisms
out of it. This is K-projectivity, read as left orthogonality to the acyclic complexes, through
the identification of the quasi-isomorphisms with the class of morphisms attached to the
triangulated subcategory of acyclic complexes. -/
private lemma isColocal_quasiIso {A : Type u} [Category.{v} A] [Abelian A]
    (P : CochainComplex A ℤ) [P.IsKProjective] :
    (HomotopyCategory.quasiIso A (.up ℤ)).isColocal
      ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, ObjectProperty.isColocal_trW]
  exact CochainComplex.IsKProjective.leftOrthogonal P

/-- **Remark [Stacks 0648]** for a K-projective complex, the dual of [Stacks 05TF]. If `P` is a
K-projective cochain complex and `α : L ⟶ K` is a quasi-isomorphism, then postcomposition with
the image of `α` in the homotopy category is a bijection
`Hom_{K(A)}(P, L) → Hom_{K(A)}(P, K)`.

Its surjectivity is the first assertion of [Stacks 0649] and its injectivity is
[Stacks 064A]. -/
@[stacks 0648]
lemma bijective_postcomp_quotient_map {A : Type u} [Category.{v} A] [Abelian A]
    {P K L : CochainComplex A ℤ} [P.IsKProjective] (α : L ⟶ K) [QuasiIso α] :
    Function.Bijective (fun β : (HomotopyCategory.quotient A (.up ℤ)).obj P ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj L ↦
      β ≫ (HomotopyCategory.quotient A (.up ℤ)).map α) :=
  isColocal_quasiIso P _ <| (HomotopyCategory.quotient_map_mem_quasiIso_iff α).2 <|
    (HomologicalComplex.mem_quasiIso_iff α).2 inferInstance

/-- The first assertion of [Stacks 0649]: a morphism `γ : P ⟶ K` out of a K-projective complex
factors, up to homotopy, through any quasi-isomorphism `α : L ⟶ K`. -/
private lemma exists_nonempty_homotopy_comp {A : Type u} [Category.{v} A] [Abelian A]
    {P K L : CochainComplex A ℤ} [P.IsKProjective] (α : L ⟶ K) [QuasiIso α] (γ : P ⟶ K) :
    ∃ β : P ⟶ L, Nonempty (Homotopy (β ≫ α) γ) := by
  obtain ⟨β, hβ⟩ := (bijective_postcomp_quotient_map α).surjective
    ((HomotopyCategory.quotient A (.up ℤ)).map γ)
  obtain ⟨β, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective β
  exact ⟨β, ⟨HomotopyCategory.homotopyOfEq _ _ <|
    by rw [CategoryTheory.Functor.map_comp]; exact hβ⟩⟩

/-- **Stacks 0649.** Let `A` be an abelian category, let `α : L ⟶ K` be a quasi-isomorphism of
cochain complexes in `A` and let `P` be a K-projective cochain complex — for instance one which
is bounded above and consists of projective objects, by
`CochainComplex.isKProjective_of_projective`. Then, given `γ : P ⟶ K`:
(1) there is a `β : P ⟶ L` with `β ≫ α` homotopic to `γ`, and
(2) if the terms of `P` are projective and `α` is epimorphic in every degree, there is a
`β : P ⟶ L` with `β ≫ α = γ`. -/
@[stacks 0649]
public theorem CochainComplex.IsKProjective.exists_lift_of_quasiIso {A : Type u} [Category.{v} A]
    [Abelian A] {P K L : CochainComplex A ℤ} [P.IsKProjective] (α : L ⟶ K) [QuasiIso α]
    (γ : P ⟶ K) :
    (∃ β : P ⟶ L, Nonempty (Homotopy (β ≫ α) γ)) ∧
      ((∀ n : ℤ, Projective (P.X n)) → (∀ n : ℤ, Epi (α.f n)) → ∃ β : P ⟶ L, β ≫ α = γ) :=
  ⟨exists_nonempty_homotopy_comp α γ, fun _ _ =>
    have ⟨_, ⟨h⟩⟩ := exists_nonempty_homotopy_comp α γ
    exists_comp_eq_of_homotopy h⟩

/-- **Stacks 064A.** Let `A` be an abelian category, let `α : L ⟶ K` be a quasi-isomorphism of
cochain complexes in `A` and let `P` be a K-projective cochain complex — for instance one which
is bounded above and consists of projective objects, by
`CochainComplex.isKProjective_of_projective`. Then two morphisms `β₁, β₂ : P ⟶ L` whose
composites with `α` are homotopic are themselves homotopic; in particular a lift of a given
`γ : P ⟶ K` through `α` up to homotopy is unique up to homotopy. -/
@[stacks 064A]
public theorem CochainComplex.IsKProjective.nonempty_homotopy_of_comp_quasiIso {A : Type u}
    [Category.{v} A] [Abelian A] {P K L : CochainComplex A ℤ} [P.IsKProjective] (α : L ⟶ K)
    [QuasiIso α] {β₁ β₂ : P ⟶ L} (h : Homotopy (β₁ ≫ α) (β₂ ≫ α)) :
    Nonempty (Homotopy β₁ β₂) :=
  ⟨HomotopyCategory.homotopyOfEq _ _ <| (bijective_postcomp_quotient_map α).injective <| by
    simpa only [← CategoryTheory.Functor.map_comp] using HomotopyCategory.eq_of_homotopy _ _ h⟩

end KProjective

section Localization

/-- An object `X` such that a functor `L` inverting `W` induces a bijection on morphisms out of
`X` into every object is `W`-colocal, i.e. postcomposition with any morphism of `W` is a
bijection on morphisms out of `X`. This is the converse of
`ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated` and needs no structure on the
categories involved. -/
private lemma isColocal_of_map_bijective {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {W : MorphismProperty C} {L : C ⥤ D} (hL : W.IsInvertedBy L) {X : C}
    (h : ∀ Y : C, Function.Bijective (L.map : (X ⟶ Y) → _)) :
    W.isColocal X := by
  intro Y Z g hg
  have := hL g hg
  rw [← (h Z).of_comp_iff' fun f : X ⟶ Y ↦ f ≫ g,
    show (L.map · : (X ⟶ Z) → _) ∘ (fun f : X ⟶ Y ↦ f ≫ g)
      = (fun x ↦ x ≫ L.map g) ∘ (L.map · : (X ⟶ Y) → _) from
      funext (CategoryTheory.Functor.map_comp L · g)]
  exact ((isIso_iff_yoneda_map_bijective (L.map g)).1 inferInstance _).comp (h Y)

/-- **Stacks 064B.** Let `A` be an abelian category and let `P` be a cochain complex in `A`. Then
`P` is K-projective — which a bounded above complex of projective objects is, by
`CochainComplex.isKProjective_of_projective` — if and only if for every object `L` of the homotopy
category `K(A)` the localization functor `Qh : K(A) ⥤ D(A)` induces a bijection
`Mor_{K(A)}(P, L) → Mor_{D(A)}(P, L)`. The Stacks lemma is the forward implication. -/
@[stacks 064B]
public theorem CochainComplex.isKProjective_iff_Qh_map_bijective {A : Type u} [Category.{v} A]
    [Abelian A] [HasDerivedCategory.{w} A] (P : CochainComplex A ℤ) :
    P.IsKProjective ↔ ∀ L : HomotopyCategory A (ComplexShape.up ℤ),
      Function.Bijective (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶ L) → _) := by
  refine ⟨fun _ L ↦ CochainComplex.IsKProjective.Qh_map_bijective P L, fun h ↦ ?_⟩
  rw [CochainComplex.isKProjective_iff_leftOrthogonal, ← ObjectProperty.isColocal_trW]
  exact isColocal_of_map_bijective (Localization.inverts _ _) h

end Localization

section Vanishing

/-- A morphism of cochain complexes from a complex concentrated in degrees `≥ n` to a complex
concentrated in degrees `≤ m` is zero as soon as `m < n`: in every degree `i`, one of the two
objects `P^i` and `L^i` is zero. -/
private lemma hom_eq_zero_of_isStrictlyGE_of_isStrictlyLE {A : Type u} [Category.{v} A]
    [Abelian A] (P L : CochainComplex A ℤ) (n m : ℤ) (hmn : m < n) [P.IsStrictlyGE n]
    [L.IsStrictlyLE m] (f : P ⟶ L) : f = 0 := by
  ext i
  rcases lt_or_ge i n with hi | hi
  · exact (P.isZero_of_isStrictlyGE n i hi).eq_of_src _ _
  · exact (L.isZero_of_isStrictlyLE m i (by omega)).eq_of_tgt _ _

/-- If `P` is K-projective, every morphism `Q P ⟶ Q L` in the derived category is the image of a
morphism of cochain complexes `P ⟶ L`. This is [Stacks 064B]
(`CochainComplex.IsKProjective.Qh_map_bijective`), stated along `DerivedCategory.Q` on cochain
complexes rather than along `DerivedCategory.Qh` on the homotopy category. -/
theorem CochainComplex.IsKProjective.Q_map_surjective {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P L : CochainComplex A ℤ) [P.IsKProjective] :
    Function.Surjective (DerivedCategory.Q.map : (P ⟶ L) → _) := by
  intro g
  obtain ⟨β, hβ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)).surjective
    ((DerivedCategory.quotientCompQhIso A).hom.app P ≫ g ≫
      (DerivedCategory.quotientCompQhIso A).inv.app L)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective β
  refine ⟨φ, ?_⟩
  have h := DerivedCategory.quotientCompQhIso_hom_naturality (C := A) φ
  rw [hβ] at h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
  exact ((cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app P)).1 h).symm

/-- If `P` is K-projective, two morphisms of cochain complexes `P ⟶ L` with the same image in
the derived category are homotopic. This is the injectivity half of [Stacks 064B]
(`CochainComplex.IsKProjective.Qh_map_bijective`): a morphism of the homotopy category out of
`P` is determined by its image in `D(A)`, and the homotopy category identifies two morphisms of
complexes exactly when they are homotopic. -/
theorem CochainComplex.IsKProjective.nonempty_homotopy_of_Q_map_eq {A : Type u} [Category.{v} A]
    [Abelian A] [HasDerivedCategory.{w} A] {P L : CochainComplex A ℤ} [P.IsKProjective]
    {f g : P ⟶ L} (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ((CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)).injective ?_)⟩
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app L),
    DerivedCategory.quotientCompQhIso_hom_naturality (C := A) f,
    DerivedCategory.quotientCompQhIso_hom_naturality (C := A) g, h]

/-- The vanishing in the derived category for a target which is *strictly* `≤ m`: such a target
receives no nonzero morphism from `P` even at the level of complexes. -/
private lemma hom_Q_eq_zero_of_isStrictlyLE {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P L : CochainComplex A ℤ) [P.IsKProjective] (n m : ℤ) (hmn : m < n)
    [P.IsStrictlyGE n] [L.IsStrictlyLE m]
    (g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) : g = 0 := by
  obtain ⟨φ, rfl⟩ := CochainComplex.IsKProjective.Q_map_surjective P L g
  rw [hom_eq_zero_of_isStrictlyGE_of_isStrictlyLE P L n m hmn φ,
    CategoryTheory.Functor.map_zero]

/-- The vanishing in the derived category, for a target with no cohomology above `m`: the
canonical map `τ_{≤ m} K ⟶ K` is a quasi-isomorphism, hence invertible in `D(A)`. -/
private lemma hom_Q_eq_zero {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P K : CochainComplex A ℤ) [P.IsKProjective] (n m : ℤ) (hmn : m < n) [P.IsStrictlyGE n]
    [K.IsLE m] (g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K) : g = 0 := by
  have h : g ≫ inv (DerivedCategory.Q.map (K.ιTruncLE m)) = 0 :=
    hom_Q_eq_zero_of_isStrictlyLE P (K.truncLE m) n m hmn _
  rw [← cancel_mono (inv (DerivedCategory.Q.map (K.ιTruncLE m))), h, Limits.zero_comp]

/-- The vanishing in the homotopy category: a morphism dying in `D(A)` dies in `K(A)`, because
`Qh` is injective on morphisms out of the K-projective complex `P` ([Stacks 064B]). -/
private lemma quotient_hom_eq_zero {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P K : CochainComplex A ℤ) [P.IsKProjective] (n m : ℤ) (hmn : m < n)
    [P.IsStrictlyGE n] [K.IsLE m]
    (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) : f = 0 := by
  refine (CochainComplex.IsKProjective.Qh_map_bijective P _).injective ?_
  have h := hom_Q_eq_zero P K n m hmn ((DerivedCategory.quotientCompQhIso A).inv.app P ≫
    DerivedCategory.Qh.map f ≫ (DerivedCategory.quotientCompQhIso A).hom.app K)
  rw [CategoryTheory.Functor.map_zero,
    ← cancel_epi ((DerivedCategory.quotientCompQhIso A).inv.app P),
    ← cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app K)]
  simp [h]

/-- **Stacks 064D.** Let `A` be an abelian category, let `P` be a K-projective cochain complex of
`A` with `P^i = 0` for `i < n` — for instance a bounded complex of projective objects with that
property, by `CochainComplex.isKProjective_of_projective` — and let `K` be a cochain complex with
`H^i(K) = 0` for `i > m`, where `m < n`. Then `Mor_{K(A)}(P, K) = Mor_{D(A)}(P, K) = 0`: every
morphism from `P` to `K` in the homotopy category, and every morphism from `P` to `K` in the
derived category, is zero. -/
@[stacks 064D]
public theorem CochainComplex.IsKProjective.hom_eq_zero_of_isStrictlyGE_of_isLE {A : Type u}
    [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] (P K : CochainComplex A ℤ)
    [P.IsKProjective] (n : ℤ) [P.IsStrictlyGE n] (m : ℤ) (hmn : m < n) [K.IsLE m] :
    (∀ f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, f = 0) ∧
      (∀ f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K, f = 0) :=
  ⟨fun f ↦ quotient_hom_eq_zero P K n m hmn f, fun f ↦ hom_Q_eq_zero P K n m hmn f⟩

end Vanishing

section Horseshoe

open Category Limits Preadditive

open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.ComposableArrows in
/-- **Two out of three for quasi-isomorphisms.** A morphism of short exact sequences of
homological complexes which is a quasi-isomorphism on the two outer terms is one on the
middle term. This is the `τ₂` analogue of
`HomologicalComplex.HomologySequence.quasiIso_τ₃`, which Mathlib has; both halves are
read off the five term exact sequences
`H ^ i (X₃) ⟶ H ^ j (X₁) ⟶ H ^ j (X₂) ⟶ H ^ j (X₃) ⟶ H ^ k (X₁)`
of the two short exact sequences by the four lemma, the degenerate cases (where `i` has
no predecessor, resp. no successor, in the complex shape) by the three term sequences. -/
private theorem quasiIso_τ₂_of_shortExact {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (homologyMap φ.τ₂ i) := by
    by_cases hk : ∃ k, c.Rel k i
    · obtain ⟨k, hki⟩ := hk
      exact Abelian.mono_of_epi_of_mono_of_mono
        ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ k i hki))
        (composableArrows₅_exact hS₁ k i hki).δ₀.δ₀
        (composableArrows₅_exact hS₂ k i hki).δ₀.δ₀
        (inferInstanceAs (Epi (homologyMap φ.τ₃ k)))
        (inferInstanceAs (Mono (homologyMap φ.τ₁ i)))
        (inferInstanceAs (Mono (homologyMap φ.τ₃ i)))
    · have := hS₂.mono_f
      exact ShortComplex.mono_of_mono_of_mono_of_mono
        ((homologyFunctor C c i).mapShortComplex.map φ) (hS₁.homology_exact₂ i)
        (mono_homologyMap_of_mono_of_not_rel S₂.f i (by simpa using hk))
        (inferInstanceAs (Mono (homologyMap φ.τ₁ i)))
        (inferInstanceAs (Mono (homologyMap φ.τ₃ i)))
  have hepi : Epi (homologyMap φ.τ₂ i) := by
    by_cases hj : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hj
      exact Abelian.epi_of_epi_of_epi_of_mono
        ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
        (composableArrows₅_exact hS₁ i j hij).δlast.δlast
        (composableArrows₅_exact hS₂ i j hij).δlast.δlast
        (inferInstanceAs (Epi (homologyMap φ.τ₁ i)))
        (inferInstanceAs (Epi (homologyMap φ.τ₃ i)))
        (inferInstanceAs (Mono (homologyMap φ.τ₁ j)))
    · have := hS₁.epi_g
      exact ShortComplex.epi_of_epi_of_epi_of_epi
        ((homologyFunctor C c i).mapShortComplex.map φ) (hS₂.homology_exact₂ i)
        (epi_homologyMap_of_epi_of_not_rel S₁.g i (by simpa using hj))
        (inferInstanceAs (Epi (homologyMap φ.τ₁ i)))
        (inferInstanceAs (Epi (homologyMap φ.τ₃ i)))
  exact isIso_of_mono_of_epi _

section Twist

variable {C : Type u} [Category.{v} C] [Abelian C] {P₁ P : CochainComplex C ℤ}
  (δ : ∀ m : ℤ, P.X m ⟶ P₁.X (m + 1))

variable (hδ : ∀ m : ℤ, δ m ≫ P₁.d (m + 1) (m + 1 + 1) + P.d m (m + 1) ≫ δ (m + 1) = 0)

/-- The short exact sequence `0 ⟶ P₁ ⟶ twist δ ⟶ P ⟶ 0`. -/
private lemma twist_shortExact :
    (ShortComplex.mk _ _
      (CochainComplex.twistι_comp_twistπ (CochainComplex.twistHom δ hδ))).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro m
  exact (ShortComplex.Splitting.ofHasBinaryBiproduct (P₁.X m) (P.X m)).shortExact

private lemma twist_projective (m : ℤ) [Projective (P₁.X m)] [Projective (P.X m)] :
    Projective ((CochainComplex.twist (CochainComplex.twistHom δ hδ)).X m) := by
  rw [CochainComplex.twist_X]; infer_instance

private lemma twist_isStrictlyLE (a : ℤ) [P₁.IsStrictlyLE a] [P.IsStrictlyLE a] :
    (CochainComplex.twist (CochainComplex.twistHom δ hδ)).IsStrictlyLE a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro m hm
  have h₁ := P₁.isZero_of_isStrictlyLE a m hm
  have h₂ := P.isZero_of_isStrictlyLE a m hm
  rw [CochainComplex.twist_X, IsZero.iff_id_eq_zero]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [comp_id]; exact h₁.eq_of_src _ _
  · rw [comp_id]; exact h₂.eq_of_src _ _

/-- A morphism out of the twisted complex: given `u : P₁ ⟶ B` and a family
`h ^ m : P ^ m ⟶ B ^ m` whose defect against the differentials is `δ ≫ u`. -/
private noncomputable def twistDesc {B : CochainComplex C ℤ} (u : P₁ ⟶ B)
    (h : ∀ m : ℤ, P.X m ⟶ B.X m)
    (hu : ∀ m : ℤ, δ m ≫ u.f (m + 1) + P.d m (m + 1) ≫ h (m + 1) = h m ≫ B.d m (m + 1)) :
    CochainComplex.twist (CochainComplex.twistHom δ hδ) ⟶ B where
  f m := biprod.desc (u.f m) (h m)
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    rw [CochainComplex.twist_d]
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [biprod.lift_desc, biprod.inl_desc_assoc, assoc, comp_add, add_comp,
        biprod.inl_fst_assoc, biprod.inl_snd_assoc, zero_comp, add_zero]
      rw [u.comm]
    · simp only [biprod.lift_desc, biprod.inr_desc_assoc, assoc, comp_add, add_comp,
        biprod.inr_fst_assoc, biprod.inr_snd_assoc, zero_comp, zero_add]
      exact (hu i).symm

private lemma twistDesc_f {B : CochainComplex C ℤ} (u : P₁ ⟶ B) (h : ∀ m : ℤ, P.X m ⟶ B.X m)
    (hu : ∀ m : ℤ, δ m ≫ u.f (m + 1) + P.d m (m + 1) ≫ h (m + 1) = h m ≫ B.d m (m + 1))
    (m : ℤ) : (twistDesc δ hδ u h hu).f m = biprod.desc (u.f m) (h m) := rfl

end Twist

/-- The horseshoe lemma for complexes, stated outside the `CochainComplex` namespace so that
`shiftFunctor` denotes the shift of the category of cochain complexes rather than
`CochainComplex.shiftFunctor`. -/
private theorem exists_shortExact_isProjectiveResolution_aux {C : Type u} [Category.{v} C]
    [Abelian C] [EnoughProjectives C] (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (n : ℤ) [S.X₁.IsStrictlyLE n] {P : CochainComplex C ℤ} (π : P ⟶ S.X₃)
    [CochainComplex.IsProjectiveResolution π] :
    ∃ (P₁ P₂ : CochainComplex C ℤ) (i : P₁ ⟶ P₂) (p : P₂ ⟶ P) (hip : i ≫ p = 0)
      (π₁ : P₁ ⟶ S.X₁) (π₂ : P₂ ⟶ S.X₂),
      (ShortComplex.mk i p hip).ShortExact ∧ CochainComplex.IsProjectiveResolution π₁ ∧
        CochainComplex.IsProjectiveResolution π₂ ∧ i ≫ π₂ = π₁ ≫ S.f ∧
          p ≫ π = π₂ ≫ S.g := by
  have hSd : ∀ m : ℤ, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) m)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  -- A projective resolution of `S.X₁` which is an epimorphism in every degree.
  obtain ⟨R, hRepi⟩ := ProjectiveResolutionLemma.statement3 n S.X₁ inferInstance
  have := R.boundedAbove
  have hR1 : QuasiIso R.α := R.quasiIso
  have hRproj : ∀ m : ℤ, Projective (R.complex.X m) := R.projective
  have hπ₁ : CochainComplex.IsProjectiveResolution R.α :=
    { toQuasiIso := R.quasiIso
      exists_isStrictlyLE := ⟨n, R.boundedAbove⟩
      projective := R.projective }
  -- The degreewise lifts `h` of `π` along `S.g`.
  have hPproj : ∀ m : ℤ, Projective (P.X m) :=
    CochainComplex.IsProjectiveResolution.projective (α := π)
  have hlift : ∀ m : ℤ, ∃ u : P.X m ⟶ S.X₂.X m, u ≫ S.g.f m = π.f m := by
    intro m
    have : Epi (S.g.f m) := (hSd m).epi_g
    exact ⟨Projective.factorThru (π.f m) (S.g.f m), Projective.factorThru_comp _ _⟩
  choose h hh using hlift
  -- Its defect against the differentials is killed by `S.g`, hence factors through `S.X₁`.
  have hw : ∀ m : ℤ,
      (h m ≫ S.X₂.d m (m + 1) - P.d m (m + 1) ≫ h (m + 1)) ≫ S.g.f (m + 1) = 0 := by
    intro m
    rw [sub_comp, assoc, ← S.g.comm m (m + 1), ← assoc, hh m, π.comm m (m + 1), assoc,
      hh (m + 1), sub_self]
  have hεex : ∀ m : ℤ, ∃ u : P.X m ⟶ S.X₁.X (m + 1),
      u ≫ S.f.f (m + 1) = h m ≫ S.X₂.d m (m + 1) - P.d m (m + 1) ≫ h (m + 1) := by
    intro m
    have := (hSd (m + 1)).mono_f
    exact ⟨(hSd (m + 1)).exact.lift _ (hw m), (hSd (m + 1)).exact.lift_f _ (hw m)⟩
  choose ε hε using hεex
  -- `P` is K-projective, so `ε : P ⟶ S.X₁⟦1⟧` lifts along `R.α⟦1⟧` on the nose.
  obtain ⟨dP, hdP⟩ := CochainComplex.IsProjectiveResolution.exists_isStrictlyLE (α := π)
  have := hdP
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P dP
  obtain ⟨δ, hδα, hδcoc⟩ : ∃ d : ∀ m : ℤ, P.X m ⟶ R.complex.X (m + 1),
      (∀ m : ℤ, d m ≫ R.α.f (m + 1) = ε m) ∧
        ∀ m : ℤ, d m ≫ R.complex.d (m + 1) (m + 1 + 1) + P.d m (m + 1) ≫ d (m + 1) = 0 := by
    let e : P ⟶ (shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj S.X₁ :=
      { f := fun m => ε m
        comm' := fun i j hij => by
          obtain rfl : j = i + 1 := hij.symm
          have : Mono (S.f.f (i + 1 + 1)) := (hSd (i + 1 + 1)).mono_f
          rw [CochainComplex.shiftFunctor_obj_d']
          simp only [Int.negOnePow_one, Units.neg_smul, one_smul]
          rw [← cancel_mono (S.f.f (i + 1 + 1))]
          have l : (ε i ≫ (-S.X₁.d (i + 1) (i + 1 + 1))) ≫ S.f.f (i + 1 + 1)
              = P.d i (i + 1) ≫ h (i + 1) ≫ S.X₂.d (i + 1) (i + 1 + 1) := by
            rw [comp_neg, neg_comp, assoc, ← S.f.comm (i + 1) (i + 1 + 1), ← assoc, hε i,
              sub_comp, assoc, HomologicalComplex.d_comp_d, comp_zero, zero_sub, neg_neg, assoc]
          have r : (P.d i (i + 1) ≫ ε (i + 1)) ≫ S.f.f (i + 1 + 1)
              = P.d i (i + 1) ≫ h (i + 1) ≫ S.X₂.d (i + 1) (i + 1 + 1) := by
            rw [assoc, hε (i + 1), comp_sub, sub_eq_self, ← assoc,
              HomologicalComplex.d_comp_d, zero_comp]
          rw [l, r] }
    obtain ⟨d, hd⟩ := (CochainComplex.IsKProjective.exists_lift_of_quasiIso
        ((shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map R.α) e).2 hPproj
      (fun m => by rw [CochainComplex.shiftFunctor_map_f']; exact hRepi (m + 1))
    refine ⟨fun m => d.f m, fun m => ?_, fun m => ?_⟩
    · have h1 := congrArg
        (fun φ : P ⟶ (shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj S.X₁ => φ.f m) hd
      simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f'] at h1
      exact h1
    · have h2 := d.comm m (m + 1)
      rw [CochainComplex.shiftFunctor_obj_d'] at h2
      simp only [Int.negOnePow_one, Units.neg_smul, one_smul, comp_neg] at h2
      rw [← h2, add_neg_cancel]
  -- The middle resolution.
  have hu : ∀ m : ℤ, δ m ≫ (R.α ≫ S.f).f (m + 1) + P.d m (m + 1) ≫ h (m + 1)
      = h m ≫ S.X₂.d m (m + 1) := by
    intro m
    rw [HomologicalComplex.comp_f, ← assoc, hδα m, hε m]
    abel
  have hcomm₁₂ : CochainComplex.twistι (CochainComplex.twistHom δ hδcoc) ≫
      twistDesc δ hδcoc (R.α ≫ S.f) h hu = R.α ≫ S.f := by
    ext m
    rw [HomologicalComplex.comp_f, CochainComplex.twistι_f, twistDesc_f, biprod.inl_desc]
  have hzero : ∀ m : ℤ, S.f.f m ≫ S.g.f m = 0 := by
    intro m
    rw [← HomologicalComplex.comp_f, S.zero, HomologicalComplex.zero_f]
  have hcomm₂₃ : CochainComplex.twistπ (CochainComplex.twistHom δ hδcoc) ≫ π =
      twistDesc δ hδcoc (R.α ≫ S.f) h hu ≫ S.g := by
    refine HomologicalComplex.hom_ext _ _ fun m => ?_
    have key : ∀ a b : (R.complex.X m ⊞ P.X m) ⟶ S.X₃.X m,
        biprod.inl ≫ a = biprod.inl ≫ b → biprod.inr ≫ a = biprod.inr ≫ b → a = b :=
      fun a b h₁ h₂ => biprod.hom_ext' _ _ h₁ h₂
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.twistπ_f, twistDesc_f]
    refine key _ _ ?_ ?_
    · simp [hzero m]
    · simp [hh m]
  refine ⟨R.complex, CochainComplex.twist (CochainComplex.twistHom δ hδcoc),
    CochainComplex.twistι (CochainComplex.twistHom δ hδcoc),
    CochainComplex.twistπ (CochainComplex.twistHom δ hδcoc),
    CochainComplex.twistι_comp_twistπ (CochainComplex.twistHom δ hδcoc), R.α,
    twistDesc δ hδcoc (R.α ≫ S.f) h hu,
    twist_shortExact δ hδcoc, hπ₁, ?_, hcomm₁₂, hcomm₂₃⟩
  have : R.complex.IsStrictlyLE (max n dP) :=
    CochainComplex.isStrictlyLE_of_le _ n (max n dP) (le_max_left _ _)
  have : P.IsStrictlyLE (max n dP) :=
    CochainComplex.isStrictlyLE_of_le _ dP (max n dP) (le_max_right _ _)
  have : (CochainComplex.twist (CochainComplex.twistHom δ hδcoc)).IsStrictlyLE (max n dP) :=
    twist_isStrictlyLE δ hδcoc _
  refine
    { toQuasiIso := ?_
      exists_isStrictlyLE := ⟨max n dP, inferInstance⟩
      projective := fun m => twist_projective δ hδcoc m }
  exact quasiIso_τ₂_of_shortExact
    (S₁ := ShortComplex.mk _ _
      (CochainComplex.twistι_comp_twistπ (CochainComplex.twistHom δ hδcoc))) (S₂ := S)
    { τ₁ := R.α
      τ₂ := twistDesc δ hδcoc (R.α ≫ S.f) h hu
      τ₃ := π
      comm₁₂ := hcomm₁₂.symm
      comm₂₃ := hcomm₂₃.symm }
    (twist_shortExact δ hδcoc) hS hR1 inferInstance

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let `C` be an abelian category with enough projectives, let
`S : 0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of cochain complexes
of `C` with `S.X₁` bounded above, and let `π : P ⟶ S.X₃` be a projective
resolution. Then there is a short exact sequence of complexes
`0 ⟶ P₁ ⟶ P₂ ⟶ P ⟶ 0` mapping to `S`, with `π` as its third component, whose
first two components `π₁ : P₁ ⟶ S.X₁` and `π₂ : P₂ ⟶ S.X₂` are projective
resolutions as well. -/
@[stacks 064C]
public theorem exists_shortExact_isProjectiveResolution
    [EnoughProjectives C] (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (n : ℤ) [S.X₁.IsStrictlyLE n] {P : CochainComplex C ℤ} (π : P ⟶ S.X₃)
    [IsProjectiveResolution π] :
    ∃ (P₁ P₂ : CochainComplex C ℤ) (i : P₁ ⟶ P₂) (p : P₂ ⟶ P) (hip : i ≫ p = 0)
      (π₁ : P₁ ⟶ S.X₁) (π₂ : P₂ ⟶ S.X₂),
      (ShortComplex.mk i p hip).ShortExact ∧ IsProjectiveResolution π₁ ∧
        IsProjectiveResolution π₂ ∧ i ≫ π₂ = π₁ ≫ S.f ∧ p ≫ π = π₂ ≫ S.g :=
  exists_shortExact_isProjectiveResolution_aux S hS n π

end CochainComplex

end Horseshoe

end

end
