module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksCore.Tactic.StacksAttribute

/-!
# `δ`-functors and pre-triangulated subcategories

This file collects the two notions attached to a functor which the definition of a
triangulated category brings with it: a `δ`-functor from an abelian category to a
triangulated category, and the inclusion of a pre-triangulated subcategory.

## `δ`-functors

Let `𝒜` be an abelian category and let `𝒟` be a triangulated category. A *`δ`-functor* from `𝒜`
to `𝒟` is a functor `G : 𝒜 ⥤ 𝒟` together with a rule assigning to every short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜` a morphism `δ = δ_{A → B → C} : G(C) ⟶ G(A)⟦1⟧` such that

1. the triangle `(G(A), G(B), G(C), G(a), G(b), δ_{A → B → C})` is a distinguished triangle
   of `𝒟`, and
2. `δ` is natural: for every morphism `(A → B → C) ⟶ (A' → B' → C')` of short exact sequences
   the square built from `δ_{A → B → C}`, `δ_{A' → B' → C'}`, `G(C) ⟶ G(C')` and
   `G(A)⟦1⟧ ⟶ G(A')⟦1⟧` commutes.

The distinguished triangle in (1) is called the image of the short exact sequence under the
`δ`-functor. A `δ`-functor is thus a functor *equipped with extra structure*: as the source
remarks, strictly speaking it does not make sense to say that a given functor `𝒜 ⥤ 𝒟` *is* a
`δ`-functor, and accordingly what is defined here is the type of `δ`-functor structures on a
given `G`. The basic example, [StackProject 0152], is the localization functor
`Q : Comp(𝒜) ⥤ D(𝒜)` with `δ = -p ∘ q⁻¹`.

## Pre-triangulated subcategories

Let `D` be a pre-triangulated category. A *pre-triangulated subcategory* of `D` is a pair
`(D', T')` where `D'` is an additive subcategory of `D` which is preserved by the shift
`[1]`, in such a way that `[1] : D' → D'` is an auto-equivalence, and where `T'` is a set of
distinguished triangles of `D` all of whose objects and morphisms lie in `D'`, such that
`(D', [1], T')` is itself a pre-triangulated category. If `D` is triangulated, then such a
pair is a *triangulated subcategory* when `(D', [1], T')` is moreover triangulated.

Such a pair is described here by its inclusion functor: the data are a pre-triangulated
category `C` (playing the role of `(D', [1], T')`, so that `T'` is `distTriang C`) together
with a faithful functor `ι : C ⥤ D` which commutes with the shift and carries distinguished
triangles to distinguished triangles, the latter being the inclusion `T' ⊆ T`.

## Main definitions

* `CategoryTheory.Functor.DeltaFunctorStructure`: the structure of a `δ`-functor on a functor
  `G : 𝒜 ⥤ 𝒟`, i.e. the connecting morphisms `δ` together with the two axioms above.
* `CategoryTheory.Functor.DeltaFunctorStructure.comp`, `….precomp`: a `δ`-functor composed with
  an exact functor of pre-triangulated categories, resp. precomposed with an exact functor of
  abelian categories, is a `δ`-functor ([Stacks, Tag 0151]).
* `CategoryTheory.Functor.IsPretriangulatedSubcategory`: the property of a functor
  `ι : C ⥤ D` between pre-triangulated categories, equipped with a commutation with the
  shift, that it exhibits `C` as a pre-triangulated subcategory of `D`.

## Implementation notes

### `δ`-functors

A short exact sequence of `𝒜` is a `CategoryTheory.ShortComplex 𝒜` `S` together with
`S.ShortExact`, and a morphism of short exact sequences is a morphism `φ : S₁ ⟶ S₂` of short
complexes; this is Mathlib's spelling of the source's `0 → A → B → C → 0` and of the morphisms
between two such, and it is what makes `δ` a rule with a single argument. The connecting
morphism takes the proof `S.ShortExact` as an argument (as Mathlib's `triangleOfSESδ` does);
since `ShortExact` is a `Prop`, `δ` is by proof irrelevance a function of the sequence alone.

Two hypotheses of the source are dropped because the definition does not use them. The
octahedron axiom TR4 plays no role — only the class `distTriang 𝒟` of distinguished triangles
does — so `𝒟` is only assumed pre-triangulated, and the definition applies verbatim to a
triangulated `𝒟`. Likewise the source's abelian `𝒜` enters only through short exact sequences
and their morphisms, which Mathlib defines for any category with zero morphisms, so `𝒜` carries
only `[HasZeroMorphisms 𝒜]`; instantiating at an abelian `𝒜` needs no bridge.

Axiom (1) is stated for the triangle `Triangle.mk (G.map S.f) (G.map S.g) (δ hS)`, which is the
source's `(G(A), G(B), G(C), G(a), G(b), δ)`; the image of the short exact sequence under the
`δ`-functor is that triangle, worth a named projection as soon as a dependent needs it. Axiom
(2) is the equation `δ h₁ ≫ (G.map φ.τ₁)⟦1⟧' = G.map φ.τ₃ ≫ δ h₂`, oriented exactly as
Mathlib's `DerivedCategory.triangleOfSESδ_naturality`; together with functoriality of `G` it is
equivalent to giving a morphism of triangles between the images of `S₁` and of `S₂`, of which
the first two squares commute for free (compare `DerivedCategory.triangleOfSES.map`).

Faithfulness to the source. (1) No hypothesis is dead: the instances on `𝒟` are exactly what
provides the shift `⟦1⟧` in the target of `δ` and the class `distTriang 𝒟` used by axiom (1),
and `HasZeroMorphisms 𝒜` is what makes `ShortComplex.ShortExact` meaningful; the two axioms
both quantify over all short exact sequences of `𝒜` and over all morphisms between them, so no
part of the data goes unconstrained. (2) There is no choice of scalars or base to get wrong: the
shift is the `ℤ`-shift of `𝒟` itself, at `1`, and `δ_{A → B → C}` is a morphism of `𝒟` from
`G(C)` to `G(A)⟦1⟧`, not to `G(A⟦1⟧)` or `G(A)⟦-1⟧`. (3) The source's `δ` is data, not an
existence statement, and it is pinned as the field `δ`: a `δ`-functor structure *is* the rule,
so two structures on the same `G` with different connecting morphisms are different terms, as
the source intends when it says a `δ`-functor comes equipped with additional structure. (4) The
instantiation is not degenerate: for `𝒜 = CochainComplex A ℤ` and `𝒟 = DerivedCategory A` over
an abelian `A` with `HasDerivedCategory A`, the fields are `DerivedCategory.triangleOfSESδ`,
`DerivedCategory.triangleOfSES_distinguished` and `DerivedCategory.triangleOfSESδ_naturality`
verbatim, which is [StackProject 0152]; that example is not trivial, since a nonsplit short
exact sequence forces `δ ≠ 0` (which is why `Comp(𝒜) ⥤ K(𝒜)` admits no such structure).

### Pre-triangulated subcategories

The set `T'` of triangles is not extra data here: it is the set of distinguished triangles
of `C`, and the source's conditions on it are exactly the two parents of the class. That
every object and morphism occurring in a triangle of `T'` lies in `D'` is automatic once the
triangle is a triangle of `C`, and `T' ⊆ T` is `CategoryTheory.Functor.map_distinguished`.

Condition (1) of the source — `D'` additive, preserved by `[1]`, with `[1] : D' → D'` an
auto-equivalence — is carried by the typeclass hypotheses of `Pretriangulated C`:
`Preadditive C` and `HasZeroObject C` for additivity, and `HasShift C ℤ`, a shift by the
*group* `ℤ`, for a shift acting by auto-equivalences. Additivity of the inclusion is not an
extra hypothesis either: `CategoryTheory.Functor.IsTriangulated.instAdditive` derives
`ι.Additive`. The source identifies `ι (X[1])` with `(ι X)[1]` by the identity; here that
identification is the datum `ι.CommShift ℤ`, a coherent isomorphism, which is what makes the
notion invariant under equivalences of `C`.

Injectivity of `ι` on objects is deliberately not imposed. For the inclusion of a literal
subcategory it holds, and then the objects `ι X` and the morphisms `ι f` do form a
pre-triangulated subcategory of `D` in the sense of the source, onto which `ι` is an
isomorphism of categories; but no statement about pre-triangulated subcategories uses it,
and imposing it would destroy invariance under equivalence.

For a *full* subcategory — the case the source's footnote singles out, and the subject of
Lemma 05QX — Mathlib's `CategoryTheory.ObjectProperty.IsTriangulated P` provides both
`Pretriangulated P.FullSubcategory` and `P.ι.IsTriangulated`, so that `P.ι` is a
pre-triangulated subcategory in the present sense, and `T'` is then the set of distinguished
triangles of `D` whose three objects all satisfy `P`, as the footnote asserts.

A *triangulated* subcategory needs no separate definition: it is a pre-triangulated
subcategory `ι : C ⥤ D` with `D` triangulated for which `CategoryTheory.IsTriangulated C`
holds as well. When `ι` is in addition full this is automatic, by
`CategoryTheory.IsTriangulated.of_fully_faithful_triangulated_functor`.

Faithfulness. (1) Both parents are used and neither is implied by the other: faithfulness of
`ι` is what makes `C` a subcategory of `D` rather than an arbitrary pre-triangulated
category over it, and `ι.IsTriangulated` is the source's `T' ⊆ T`. (2) The ambient data are
the source's: one pre-triangulated category `D`, one pre-triangulated category `C` for the
subcategory, and a single shift on each, compared along `ι.CommShift ℤ`; no other shift,
category or triangle set enters. (3) The inclusion is pinned as the datum `ι` rather than
asserted to exist, and the triangles of the subcategory are pinned as `distTriang C`, whose
`ι`-images the class places inside `distTriang D`. (4) Not degenerate: `𝟭 D` is an instance,
exhibiting `D` as a pre-triangulated subcategory of itself, and for any `P : ObjectProperty D`
with `P.IsTriangulated` the inclusion `P.ι` is one, which is the full-subcategory case above.

## References

* [StackProject 0150](https://stacks.math.columbia.edu/tag/0150)
* [StacksProject 05QM](https://stacks.math.columbia.edu/tag/05QM)
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Functor

section DeltaFunctor

universe v₁ v₂ u₁ u₂

variable (𝒜 : Type u₁) [Category.{v₁} 𝒜] [HasZeroMorphisms 𝒜]
  (𝒟 : Type u₂) [Category.{v₂} 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [Preadditive 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]

/-- The structure of a **`δ`-functor** from an abelian category `𝒜` to a (pre)triangulated
category `𝒟` on a functor `G : 𝒜 ⥤ 𝒟`: a rule assigning to every short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜` a connecting morphism `δ : G(C) ⟶ G(A)⟦1⟧` such that the triangle
`(G(A), G(B), G(C), G(a), G(b), δ)` — the image of the short exact sequence under the
`δ`-functor — is distinguished, and such that `δ` is natural in the short exact sequence. -/
@[stacks 0150]
public structure DeltaFunctorStructure (G : 𝒜 ⥤ 𝒟) where
  /-- The connecting morphism `δ = δ_{A → B → C} : G(C) ⟶ G(A)⟦1⟧` attached to a short exact
  sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜`. -/
  δ {S : ShortComplex 𝒜} (hS : S.ShortExact) : G.obj S.X₃ ⟶ (G.obj S.X₁)⟦(1 : ℤ)⟧
  /-- For every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜`, the triangle
  `(G(A), G(B), G(C), G(a), G(b), δ)` is a distinguished triangle of `𝒟`. -/
  distinguished {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Triangle.mk (G.map S.f) (G.map S.g) (δ hS) ∈ distTriang 𝒟
  /-- The connecting morphism is natural: for every morphism `φ` of short exact sequences of
  `𝒜`, the square formed by `δ`, `G(φ)` and `G(φ)⟦1⟧` commutes. -/
  δ_naturality {S₁ S₂ : ShortComplex 𝒜} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
      (φ : S₁ ⟶ S₂) : δ h₁ ≫ (G.map φ.τ₁)⟦(1 : ℤ)⟧' = G.map φ.τ₃ ≫ δ h₂

end DeltaFunctor

section DeltaFunctorComp

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [Preadditive 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] {G : 𝒜 ⥤ 𝒟}

/-- **Stacks 0151 (1).** If `G : 𝒜 ⥤ 𝒟` is a `δ`-functor and `F : 𝒟 ⥤ 𝒟'` is an exact functor
of pre-triangulated categories, then `F ∘ G` is a `δ`-functor, with connecting morphisms
`δ'_{A → B → C} = ξ_{G(A)} ∘ F(δ_{A → B → C})`, where `ξ : F(X⟦1⟧) ≅ F(X)⟦1⟧` is the
commutation of `F` with the shift (`DeltaFunctorStructure.comp_δ`). -/
@[stacks 0151 "(1)", simps]
public noncomputable def DeltaFunctorStructure.comp (d : G.DeltaFunctorStructure 𝒜 𝒟)
    {𝒟' : Type u₃} [Category.{v₃} 𝒟'] [HasZeroObject 𝒟'] [HasShift 𝒟' ℤ] [Preadditive 𝒟']
    [∀ n : ℤ, (shiftFunctor 𝒟' n).Additive] [Pretriangulated 𝒟']
    (F : 𝒟 ⥤ 𝒟') [F.CommShift ℤ] [F.IsTriangulated] :
    (G ⋙ F).DeltaFunctorStructure 𝒜 𝒟' where
  δ hS := F.map (d.δ hS) ≫ (F.commShiftIso (1 : ℤ)).hom.app (G.obj _)
  distinguished hS := F.map_distinguished _ (d.distinguished hS)
  δ_naturality h₁ h₂ φ := by
    have hξ := (F.commShiftIso (1 : ℤ)).hom.naturality (G.map φ.τ₁)
    simp only [Functor.comp_map] at hξ ⊢
    rw [Category.assoc, ← hξ, ← F.map_comp_assoc, d.δ_naturality h₁ h₂ φ, F.map_comp_assoc]

/-- **Stacks 0151 (2).** If `G : 𝒜 ⥤ 𝒟` is a `δ`-functor and `H : 𝒜' ⥤ 𝒜` is an exact functor
of abelian categories, then `G ∘ H` is a `δ`-functor, with connecting morphisms
`δ''_{A → B → C} = δ_{H(A) → H(B) → H(C)}` (`DeltaFunctorStructure.precomp_δ`). -/
@[stacks 0151 "(2)", simps]
public noncomputable def DeltaFunctorStructure.precomp (d : G.DeltaFunctorStructure 𝒜 𝒟)
    {𝒜' : Type u₄} [Category.{v₄} 𝒜'] [Abelian 𝒜'] (H : 𝒜' ⥤ 𝒜)
    [H.PreservesZeroMorphisms] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    (H ⋙ G).DeltaFunctorStructure 𝒜' 𝒟 where
  δ hS := d.δ (hS.map_of_exact H)
  distinguished hS := d.distinguished (hS.map_of_exact H)
  δ_naturality h₁ h₂ φ := by
    simpa using d.δ_naturality (h₁.map_of_exact H) (h₂.map_of_exact H) (H.mapShortComplex.map φ)

end DeltaFunctorComp

section PretriangulatedSubcategory

universe v v' u u'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- **Stacks 05QM.** A functor `ι : C ⥤ D` between pre-triangulated categories, equipped
with a commutation with the shift, *exhibits `C` as a pre-triangulated subcategory of `D`*
if it is faithful and sends distinguished triangles of `C` to distinguished triangles of
`D`. The set of triangles `T'` of the source is then `distTriang C`, and `T' ⊆ T` is
`CategoryTheory.Functor.map_distinguished`. If `D` is triangulated, `C` is a *triangulated
subcategory* of `D` when moreover `CategoryTheory.IsTriangulated C`. -/
@[stacks 05QM]
public class IsPretriangulatedSubcategory (ι : C ⥤ D) [ι.CommShift ℤ] : Prop
    extends ι.Faithful, ι.IsTriangulated

end PretriangulatedSubcategory

end CategoryTheory.Functor

end

section

@[expose] public section

/-
# Problem Description

This is Lemma 13.4.16 of the Stacks Project (Tag 05QX). It concerns
pre-triangulated and triangulated categories (Stacks Chapter 13, Section 13.3)
and characterizes when an additive full subcategory `D'` of a pre-triangulated
category `D` underlies a pre-triangulated subcategory.

We use Mathlib's notion of a pre-triangulated category, encoded as the typeclass
`CategoryTheory.Pretriangulated C` on an additive category `C` equipped with a
shift `[1] : C -> C` (an additive auto-equivalence, here `HasShift C Int`
together with `Preadditive C`, `HasZeroObject C` and additivity of all shift
functors). This typeclass packages exactly the conditions TR1, TR2, TR3 of
Definition 2 (Tag 0145):
* `isomorphic_distinguished`, `contractible_distinguished` and
  `distinguished_cocone_triangle` give TR1;
* `rotate_distinguished_triangle` gives TR2;
* `complete_distinguished_triangle_morphism` gives TR3.
The octahedral condition TR4 is `CategoryTheory.IsTriangulated C`.

A `Triangle C` (Tag 0144) is the sextuple `(X, Y, Z, f, g, h)` with
`f : X -> Y`, `g : Y -> Z`, `h : Z -> X[1]`; morphisms of triangles are
`TriangleMorphism`/the morphisms `T1 -> T2` in the category `Triangle C`, and the
distinguished triangles of `D` are `distinguishedTriangles`.

We model the additive full subcategory `D'` of `D` by a predicate
`P : ObjectProperty C` on objects (fullness means all morphisms between objects
of `D'` are already present, so `D'` is determined by its objects). "Additive
full subcategory" (Definition 4) is encoded as: `P` contains a zero object of
`D` and is closed under the formation of binary direct sums (biproducts) of `D`.

DESIGN OF THIS FORMALIZATION (addressing prior feedback).

1. The set `T'` is treated as honest *data*: we introduce a predicate
   `IsPretriangulatedSubcategoryWithTriangles P T'` (Definition 3) over an
   *arbitrary* set `T'` of ambient triangles, transcribing TR1-TR3 internally to
   `D'`.  Condition (1) of Statement 1 is then the literal existential
   `∃ T', IsPretriangulatedSubcategoryWithTriangles P T'`, and Statement 2 proves
   the *uniqueness* `∀ T', ... → T' = restrictedTriangles P` together with the
   fact that `restrictedTriangles P` itself satisfies the predicate.  We do NOT
   bake the distinguished triangles into the predicate via Mathlib's canonical
   `ObjectProperty.IsTriangulated`.

2. We do NOT assume `P.IsClosedUnderIsomorphisms` (repleteness). The Stacks
   statement only requires `D'` to be an additive full subcategory, and the cone
   object `Z` in condition (2) is required only to be *isomorphic* to an object
   of `D'`, not to literally lie in `D'`. All closure conditions below are
   stated in the non-replete-friendly *existence* form used by Mathlib's
   `CategoryTheory.Triangulated.Subcategory` (which likewise does NOT assume
   `IsClosedUnderIsomorphisms`): for the zero object via
   `ObjectProperty.ContainsZero` (`∃ Z, IsZero Z ∧ P Z`), and for biproducts via
   "there exists a biproduct cone whose apex lies in `D'`".

3. ADDRESSING THE LATEST FEEDBACK on `IsAdditiveFullSubcategory`. We do NOT use
   the universal closure condition
   `∀ (b : BinaryBicone X Y), b.IsBilimit → P b.pt`, which (as Mathlib proves via
   `IsClosedUnderBinaryProducts.closedUnderIsomorphisms`) forces repleteness and
   in particular could force `P 0` for the globally chosen ambient zero object.
   Instead we require only that *some* biproduct of `X` and `Y` (a binary bicone
   that is a bilimit) has its apex in `D'`. This is the existence/internal-closure
   condition appropriate for a possibly non-replete additive full subcategory and
   matches Mathlib's idiom (the closure axioms of `ObjectProperty.IsTriangulated`
   conclude `P.isoClosure (...)`, i.e. membership only up to isomorphism).

4. The contractible / zero-object axiom is stated as the existence, for each
   `X ∈ D'`, of *some* zero object `Z` of `D` lying in `D'` together with the
   contractible triangle `(X, X, Z, id, 0, 0)` lying in `T'`. This is the
   internal contractible triangle of `D'`: it uses a zero object of the
   subcategory `D'` (guaranteed to exist by `IsAdditiveFullSubcategory`), NOT the
   globally chosen ambient zero object `0 : C`. Since the subcategory need not be
   replete, different choices of subcategory zero object are related by
   isomorphisms of triangles, so this existence form is the correct internal
   transcription of TR1 for a non-replete full subcategory (combined with the
   isomorphism-closure axiom `isomorphic_mem`).

5. Definition 3(1) ("`D'` preserved under `[1]` and the induced functor
   `[1] : D' → D'` is an auto-equivalence") is formalized faithfully as
   `ShiftAutoEquiv`: closure of `P` under the ambient `[1]`, together with the
   statement that the *induced* functor on `P.FullSubcategory` is a categorical
   equivalence.  We do NOT impose literal closure under the chosen ambient `[-1]`.

6. Statement 3 encodes the full octahedral axiom TR4 internal to `D'`, including
   the two required morphism-of-triangles compatibility conditions (b) and (c).
-/

-- Background and context (as comments)
-- Definition 1 (Triangle; Tag 0144): a sextuple `(X, Y, Z, f, g, h)` with
--   `f : X -> Y`, `g : Y -> Z`, `h : Z -> X[1]`. In Mathlib this is
--   `CategoryTheory.Pretriangulated.Triangle C`, with morphisms of triangles
--   `TriangleMorphism` and isomorphisms of triangles `Triangle` isos.
-- Definition 2 (Pre-triangulated and triangulated category; Tag 0145): the
--   additive auto-equivalence `[1]` with conditions TR1-TR3 is
--   `Pretriangulated C`; adding TR4 gives `IsTriangulated C`.

namespace Stacks.Triangulated.SubcategoryWithTriangles

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

-- Main Definition(s)

/-- Definition 4 (Additive full subcategory). The predicate `P : ObjectProperty C`
describes a *full* subcategory `D'` of `D`; it is an *additive* full subcategory
when `D'` contains a zero object of `D` and is closed under the formation of
finite direct sums (binary biproducts) computed in `D`. (A full subcategory
closed under finite biproducts and containing a zero object is automatically an
additive category for which the inclusion is additive; the relevant additive
structure on the full subcategory is provided by Mathlib's instance
`CategoryTheory.Preadditive.fullSubcategory`.)

NON-REPLETE FORMULATION (matching Mathlib's `ObjectProperty.ContainsZero` and the
non-replete subcategory idiom of `CategoryTheory.Triangulated.Subcategory`).

* The zero-object condition only requires the existence of *some* zero object `Z`
  of `D` with `P Z`; it does not force `P` to hold for the globally chosen
  ambient zero object `0 : C`. This is exactly `ObjectProperty.ContainsZero`,
  whose Mathlib docstring states it is deliberately stated this way so as not to
  require closure under isomorphisms.
* The biproduct-closure condition requires, for `X, Y ∈ D'`, the *existence* of
  *some* binary biproduct of `X` and `Y` (a binary bicone which is a bilimit)
  whose apex lies in `D'`. We deliberately do NOT use the universal form
  `∀ (b : BinaryBicone X Y), b.IsBilimit → P b.pt`; the universal form is
  Mathlib's `IsClosedUnderBinaryProducts`, which (via
  `IsClosedUnderBinaryProducts.closedUnderIsomorphisms`) forces repleteness and
  could force `P 0` for the ambient zero object — contrary to the intended
  non-replete reading of an additive full subcategory. -/
structure IsAdditiveFullSubcategory (P : ObjectProperty C) : Prop where
  /-- `D'` contains a zero object of `D` (some zero object); this is
  `ObjectProperty.ContainsZero` and does not force `P 0` for the ambient zero
  object. -/
  containsZero : ∃ Z : C, IsZero Z ∧ P Z
  /-- `D'` is closed under (the formation of) binary biproducts of `D`: if
  `X, Y ∈ D'`, then *some* binary biproduct of `X` and `Y` in `D` (a binary
  bicone that is a bilimit) has its apex in `D'`. (Existence form; does not force
  repleteness.) -/
  closedUnderBiprod : ∀ {X Y : C}, P X → P Y →
    ∃ (b : BinaryBicone X Y), Nonempty b.IsBilimit ∧ P b.pt

/-- The functor `[1] : D' → D'` induced on the full subcategory `D'` from the
ambient shift `[1]`, given a proof that `D'` is preserved by `[1]`. -/
def inducedShiftFunctor (P : ObjectProperty C)
    (h : ∀ X : C, P X → P ((shiftFunctor C (1 : ℤ)).obj X)) :
    P.FullSubcategory ⥤ P.FullSubcategory :=
  ObjectProperty.lift P (P.ι ⋙ shiftFunctor C (1 : ℤ)) (fun X => h X.1 X.2)

/-- Definition 3(1): `D'` is *preserved under* the shift `[1]` and the *induced*
functor `[1] : D' → D'` is an auto-equivalence (a categorical equivalence). This
is exactly the shift requirement of a pre-triangulated subcategory (Tag 05QM).

We deliberately do *not* require literal closure of `D'` under the ambient `[-1]`:
for a (possibly non-replete) full subcategory, the requirement is that the
*restricted* functor be an auto-equivalence (essential surjectivity up to
isomorphism), not literal closure under a chosen ambient quasi-inverse. -/
structure ShiftAutoEquiv (P : ObjectProperty C) : Prop where
  /-- `D'` is preserved under the ambient shift `[1]`. -/
  shift_mem : ∀ X : C, P X → P ((shiftFunctor C (1 : ℤ)).obj X)
  /-- The induced functor `[1] : D' → D'` is an auto-equivalence. -/
  isEquiv : (inducedShiftFunctor P shift_mem).IsEquivalence

/-- The set `T'` canonically attached to a full subcategory `D'`: the set of all
distinguished triangles of `D` whose three vertices all lie in `D'`. This is the
set described in Statement 2 (and, by fullness, all the morphisms of such a
triangle automatically lie in `D'`). -/
def restrictedTriangles (P : ObjectProperty C) : Set (Triangle C) :=
  {T | T ∈ distinguishedTriangles (C := C) ∧ P T.obj₁ ∧ P T.obj₂ ∧ P T.obj₃}

/-- Definition 3 (Pre-triangulated subcategory; Tag 05QM), specialized to a full
subcategory `D'` described by `P`, with an *arbitrary* set `T'` of ambient
triangles supplied as data.

We spell out the conditions of Definition 3 directly. Since `D'` is full, the
condition that the morphisms of a triangle in `T'` lie in `D'` is automatic, and
the additive-subcategory condition is captured by `IsAdditiveFullSubcategory`
together with the shift auto-equivalence. The remaining content is that
`(D', [ ], T')` is itself a pre-triangulated category, i.e. it satisfies TR1, TR2,
TR3 *internally to* `D'`. We require:

* `D'` is preserved by `[1]` and the induced `[1] : D' → D'` is an
  auto-equivalence (`shiftAutoEquiv`) — Definition 3(1);
* every triangle in `T'` has its three vertices in `D'` (`mem_obj`) and is
  distinguished in `D` (`subset_distinguished`) — Definition 3(2);
* `(TR1)` closure under isomorphisms of triangles internal to `D'`
  (`isomorphic_mem`); the contractible triangle `(X, X, Z, id, 0, 0)` of every
  object `X ∈ D'`, built with *some* zero object `Z` of the subcategory `D'`,
  lies in `T'` (`contractible_mem`); and existence of a cocone triangle inside
  `D'` for every morphism between objects of `D'` (`cocone_mem`);
* `(TR2)` `T'` is stable under rotation (`rotate_mem`);
* `(TR3)` completion of triangle morphisms can be done inside `D'`
  (`complete_morphism`). -/
structure IsPretriangulatedSubcategoryWithTriangles (P : ObjectProperty C)
    (T' : Set (Triangle C)) : Prop where
  /-- Definition 3(1): `D'` is preserved by `[1]` and the induced functor
  `[1] : D' → D'` is an auto-equivalence. -/
  shiftAutoEquiv : ShiftAutoEquiv P
  /-- Definition 3(2): each triangle of `T'` has all vertices in `D'`. -/
  mem_obj : ∀ T ∈ T', P T.obj₁ ∧ P T.obj₂ ∧ P T.obj₃
  /-- Definition 3(2): each triangle of `T'` is distinguished in `D` (`T' ⊆ T`). -/
  subset_distinguished : T' ⊆ distinguishedTriangles (C := C)
  /-- TR1: closure under isomorphisms of triangles with vertices in `D'`. -/
  isomorphic_mem : ∀ T₁ ∈ T', ∀ (T₂ : Triangle C), P T₂.obj₁ → P T₂.obj₂ →
    P T₂.obj₃ → (T₂ ≅ T₁) → T₂ ∈ T'
  /-- TR1: the contractible triangle `(X, X, Z, id, 0, 0)` of an object `X ∈ D'`,
  built with *some* zero object `Z` of the subcategory `D'` (i.e. `IsZero Z` and
  `P Z`), belongs to `T'`. This is the contractible triangle internal to `D'`; it
  uses a zero object of `D'` rather than the globally chosen ambient zero object
  `0 : C` (which a non-replete `D'` need not contain). Different choices of such
  `Z` give isomorphic triangles, so combined with `isomorphic_mem` this is the
  faithful internal transcription of the contractible-triangle part of TR1. -/
  contractible_mem : ∀ X : C, P X → ∃ (Z : C) (_ : IsZero Z) (_ : P Z),
    Triangle.mk (𝟙 X) (0 : X ⟶ Z) (0 : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X) ∈ T'
  /-- TR1: existence of a cocone (distinguished) triangle inside `D'` for every
  morphism between objects of `D'`. -/
  cocone_mem : ∀ {X Y : C}, P X → P Y → ∀ f : X ⟶ Y,
    ∃ (Z : C) (_ : P Z) (g : Y ⟶ Z) (h : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X),
      Triangle.mk f g h ∈ T'
  /-- TR2: stability under rotation. -/
  rotate_mem : ∀ T : Triangle C, P T.obj₁ → P T.obj₂ → P T.obj₃ →
    (T ∈ T' ↔ T.rotate ∈ T')
  /-- TR3: completion of triangle morphisms inside `D'`. -/
  complete_morphism : ∀ T₁ ∈ T', ∀ T₂ ∈ T',
    ∀ (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
      T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
        ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
          T₁.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map a = c ≫ T₂.mor₃

/-- The internal octahedral axiom TR4 for the full subcategory `D'` (described by
`P`) with distinguished triangles `T'`. This is a faithful transcription of TR4
(Tag 0145) interpreted internally to `D'`:

Given objects `X, Y, Z ∈ D'` and morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`, together
with three triangles of `T'`
* `(X, Y, Q₁, f, p₁, d₁)`,
* `(X, Z, Q₂, g ∘ f, p₂, d₂)`,
* `(Y, Z, Q₃, g, p₃, d₃)`,
there exist morphisms `a : Q₁ ⟶ Q₂` and `b : Q₂ ⟶ Q₃` such that:
(a) the triangle `(Q₁, Q₂, Q₃, a, b, d₃ ≫ p₁[1])` lies in `T'`;
(b) `(id_X, g, a)` is a morphism of triangles
    `(X, Y, Q₁, f, p₁, d₁) → (X, Z, Q₂, g ∘ f, p₂, d₂)`, i.e.
      `p₁ ≫ a = g ≫ p₂` and `d₁ = a ≫ d₂`;
(c) `(f, id_Z, b)` is a morphism of triangles
    `(X, Z, Q₂, g ∘ f, p₂, d₂) → (Y, Z, Q₃, g, p₃, d₃)`, i.e.
      `p₂ ≫ b = p₃` and `d₂ ≫ f[1] = b ≫ d₃`.

Here `p₁[1]` is `(shiftFunctor C 1).map p₁` and `f[1]` is
`(shiftFunctor C 1).map f`. -/
def InternalTR4 (P : ObjectProperty C) (T' : Set (Triangle C)) : Prop :=
  ∀ {X Y Z : C}, P X → P Y → P Z → ∀ (f : X ⟶ Y) (g : Y ⟶ Z),
    ∀ (Q₁ Q₂ Q₃ : C) (_ : P Q₁) (_ : P Q₂) (_ : P Q₃)
      (p₁ : Y ⟶ Q₁) (d₁ : Q₁ ⟶ (shiftFunctor C (1 : ℤ)).obj X)
      (p₂ : Z ⟶ Q₂) (d₂ : Q₂ ⟶ (shiftFunctor C (1 : ℤ)).obj X)
      (p₃ : Z ⟶ Q₃) (d₃ : Q₃ ⟶ (shiftFunctor C (1 : ℤ)).obj Y),
      Triangle.mk f p₁ d₁ ∈ T' →
      Triangle.mk (f ≫ g) p₂ d₂ ∈ T' →
      Triangle.mk g p₃ d₃ ∈ T' →
        ∃ (a : Q₁ ⟶ Q₂) (b : Q₂ ⟶ Q₃),
          -- (a) the octahedron triangle is distinguished inside `D'`
          (Triangle.mk a b (d₃ ≫ (shiftFunctor C (1 : ℤ)).map p₁) ∈ T') ∧
          -- (b) `(id_X, g, a)` is a morphism of triangles
          (p₁ ≫ a = g ≫ p₂) ∧ (d₁ = a ≫ d₂) ∧
          -- (c) `(f, id_Z, b)` is a morphism of triangles
          (p₂ ≫ b = p₃) ∧ (d₂ ≫ (shiftFunctor C (1 : ℤ)).map f = b ≫ d₃)

/-- Definition 3 (Triangulated subcategory; Tag 05QM). When `D` is a triangulated
category, `(D', T')` is a *triangulated subcategory* if it is a pre-triangulated
subcategory and the resulting pre-triangulated category `D'` moreover satisfies
the octahedral axiom TR4 internally (`internalTR4`). -/
structure IsTriangulatedSubcategoryWithTriangles (P : ObjectProperty C)
    (T' : Set (Triangle C)) : Prop
    extends IsPretriangulatedSubcategoryWithTriangles P T' where
  /-- TR4, the octahedral axiom internal to `D'`. -/
  internalTR4 : InternalTR4 P T'

/-- Condition (1) of Statement 1: there *exists* a set of triangles `T'` making
`(D', T')` a pre-triangulated subcategory of `D` (Definition 3). This is the
literal existential of the source. -/
def Condition1 (P : ObjectProperty C) : Prop :=
  ∃ T' : Set (Triangle C), IsPretriangulatedSubcategoryWithTriangles P T'

/-- Condition (2) of Statement 1: `D'` is preserved under `[1]` and the induced
functor `[1] : D' → D'` is an auto-equivalence, and for every morphism
`f : X ⟶ Y` between objects of `D'` there exists a distinguished triangle
`(X, Y, Z, f, g, h)` of `D` whose third vertex `Z` is isomorphic in `D` to an
object of `D'`. -/
def Condition2 (P : ObjectProperty C) : Prop :=
  ShiftAutoEquiv P ∧
    ∀ {X Y : C}, P X → P Y → ∀ f : X ⟶ Y,
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X),
        Triangle.mk f g h ∈ distinguishedTriangles (C := C) ∧
          ∃ (W : C), P W ∧ Nonempty (Z ≅ W)

-- Helper lemmas

/-- Transporting a distinguished triangle along an isomorphism of its third vertex. -/
private lemma mk_comp_distinguished_of_iso_obj₃ {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X}
    (hT : Triangle.mk f g h ∈ distinguishedTriangles (C := C)) (e : Z ≅ W) :
    Triangle.mk f (g ≫ e.hom) (e.inv ≫ h) ∈ distinguishedTriangles (C := C) :=
  isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl X) (Iso.refl Y) e.symm (by simp [Triangle.mk])
      (by simp [Triangle.mk]) (by simp [Triangle.mk]))

/-- **Sub-lemma A (auxiliary, TR1 contractible for an arbitrary zero object).**
For any object `X` of `D` and any zero object `Z` of `D` (`IsZero Z`), the
triangle `(X, X, Z, 𝟙 X, 0, 0)` is distinguished.

INFORMAL ARGUMENT. Mathlib's axiom `contractible_distinguished X` states that the
contractible triangle `contractibleTriangle X = (X, X, 0, 𝟙 X, 0, 0)` built with
the *ambient* zero object `0 : C` is distinguished. Any two zero objects are
isomorphic: from `IsZero Z` and `IsZero (0 : C)` we obtain `e : Z ≅ 0` (e.g.
`hZ.iso (isZero_zero C)` / `IsZero.isoZero`). Build an isomorphism of triangles
`(X, X, Z, 𝟙 X, 0, 0) ≅ (X, X, 0, 𝟙 X, 0, 0)` via `Triangle.isoMk` with object
isos `Iso.refl X`, `Iso.refl X`, `e`; the three commutativity squares are between
zero morphisms / identities and hold by `simp` (all maps into/out of zero objects
are zero by `IsZero`). Then conclude with `isomorphic_distinguished`
(`Triangle isomorphic to a distinguished triangle is distinguished`). -/
lemma contractible_distinguished_of_isZero (X : C) {Z : C} (hZ : IsZero Z) :
    Triangle.mk (𝟙 X) (0 : X ⟶ Z) (0 : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X)
      ∈ distinguishedTriangles (C := C) := by
  simpa [contractibleTriangle] using
    mk_comp_distinguished_of_iso_obj₃ (contractible_distinguished X) (hZ.iso (isZero_zero C)).symm

/-- **Sub-lemma B (auxiliary, transport a distinguished triangle along an iso of
the third vertex).** If `(X, Y, Z, f, g, h)` is distinguished and `Z ≅ W`, then
there exist `g' : Y ⟶ W`, `h' : W ⟶ X⟦1⟧` with `(X, Y, W, f, g', h')`
distinguished.

INFORMAL ARGUMENT. Let `e : Z ≅ W`. Put `g' := g ≫ e.hom` and
`h' := e.inv ≫ h`. The triangle `(X, Y, W, f, g', h')` is isomorphic to
`(X, Y, Z, f, g, h)` via `Triangle.isoMk` with object isos `Iso.refl X`,
`Iso.refl Y`, `e.symm` (or `e`), the commutativity squares being
`f ≫ 𝟙 = 𝟙 ≫ f`, `g ≫ e.hom = ... `, `h = e.inv ≫ ... ` which hold by
`simp`/`Category` lemmas and `e.hom_inv_id`. Then it is distinguished by
`isomorphic_distinguished`. (Mathlib alternative: `Pretriangulated.isoTriangleOfIso₁₂`
is not directly applicable since the iso is on the third vertex; use the explicit
`Triangle.isoMk` route, or rotate twice to move `W` into first position. The
`Triangle.isoMk` route is the most direct.) -/
lemma exists_distinguished_of_iso_obj₃ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X}
    (hT : Triangle.mk f g h ∈ distinguishedTriangles (C := C))
    {W : C} (e : Z ≅ W) :
    ∃ (g' : Y ⟶ W) (h' : W ⟶ (shiftFunctor C (1 : ℤ)).obj X),
      Triangle.mk f g' h' ∈ distinguishedTriangles (C := C) :=
  ⟨_, _, mk_comp_distinguished_of_iso_obj₃ hT e⟩

/-- **Sub-lemma C (forward direction (1) ⇒ (2) of Statement 1).** From a witnessing
set of triangles `T'` making `(D', T')` a pre-triangulated subcategory, condition
(2) holds.

INFORMAL ARGUMENT. The shift auto-equivalence half is exactly
`h.shiftAutoEquiv`. For the cocone half: given `f : X ⟶ Y` with `P X`, `P Y`,
apply `h.cocone_mem` to obtain `Z`, `P Z`, `g`, `h₃` with
`Triangle.mk f g h₃ ∈ T'`. By `h.subset_distinguished` this triangle is
distinguished in `D`. Finally `Z` is isomorphic to an object of `D'` by taking
`W := Z` (we have `P Z`) and `Iso.refl Z`. -/
lemma condition2_of_isPretri {P : ObjectProperty C} {T' : Set (Triangle C)}
    (h : IsPretriangulatedSubcategoryWithTriangles P T') :
    Condition2 P := by
  refine ⟨h.shiftAutoEquiv, ?_⟩
  intro X Y hX hY f
  obtain ⟨Z, hZ, g, h₃, hmem⟩ := h.cocone_mem hX hY f
  exact ⟨Z, g, h₃, h.subset_distinguished hmem, Z, hZ, ⟨Iso.refl Z⟩⟩

/-- **Sub-lemma D (the (2) ⇒ (1) construction; validity of `restrictedTriangles`).**
Assuming condition (2) and that `D'` is an additive full subcategory, the
canonical set `restrictedTriangles P` makes `(D', restrictedTriangles P)` a
pre-triangulated subcategory. This is the technical heart, shared by Statements
1, 2 and 3.

INFORMAL ARGUMENT (field by field of `IsPretriangulatedSubcategoryWithTriangles`).
Write `R := restrictedTriangles P` (distinguished triangles of `D` with all three
vertices in `D'`). Let `hc2 := hP.cocone` part of condition (2), `hsa` its
`ShiftAutoEquiv`.
* `shiftAutoEquiv`: take `hsa` (first conjunct of `Condition2`).
* `mem_obj`: immediate from the definition of `R`.
* `subset_distinguished`: immediate from the definition of `R`.
* `isomorphic_mem`: if `T₁ ∈ R` (so distinguished, vertices in `D'`) and
  `T₂ ≅ T₁` with `P T₂.obj₁, P T₂.obj₂, P T₂.obj₃`, then `T₂` is distinguished by
  `isomorphic_distinguished T₁ (T₁∈distTriang) T₂ e`, and its vertices are in
  `D'` by hypothesis; hence `T₂ ∈ R`.
* `contractible_mem`: for `X` with `P X`, take a zero object `Z` of `D'` from
  `hP.containsZero` (`IsZero Z ∧ P Z`). The triangle `(X, X, Z, 𝟙 X, 0, 0)` is
  distinguished by `contractible_distinguished_of_isZero` (Sub-lemma A) and has
  vertices `X, X, Z` all in `D'`; hence it lies in `R`.
* `cocone_mem`: for `f : X ⟶ Y` with `P X`, `P Y`, condition (2) yields a
  distinguished `(X, Y, Z, f, g, h)` with `Z ≅ W` and `P W`. By
  `exists_distinguished_of_iso_obj₃` (Sub-lemma B) along `e : Z ≅ W` we get
  `g' : Y ⟶ W`, `h' : W ⟶ X⟦1⟧` with `(X, Y, W, f, g', h')` distinguished; its
  vertices `X, Y, W` are all in `D'`, so it lies in `R`, witnessing `cocone_mem`
  with cone object `W`.
* `rotate_mem`: for `T` with `P T.obj₁, P T.obj₂, P T.obj₃`: `T` distinguished iff
  `T.rotate` distinguished by `rotate_distinguished_triangle` (TR2 of `D`). The
  vertices of `T.rotate` are `(T.obj₂, T.obj₃, T.obj₁⟦1⟧)`; `T.obj₁⟦1⟧ ∈ D'` by
  `hsa.shift_mem`. Combining, `T ∈ R ↔ T.rotate ∈ R`.
* `complete_morphism`: for `T₁, T₂ ∈ R` (distinguished in `D`) and a commuting
  square `T₁.mor₁ ≫ b = a ≫ T₂.mor₁`, apply
  `complete_distinguished_triangle_morphism` in `D` to obtain
  `c : T₁.obj₃ ⟶ T₂.obj₃` with the two required compatibilities. (By fullness of
  `D'`, `c` is automatically a morphism of `D'`; nothing extra is needed since
  the predicate only records the morphism `c` and its equations.) -/
lemma restrictedTriangles_isPretri (P : ObjectProperty C)
    (hP : IsAdditiveFullSubcategory P) (h2 : Condition2 P) :
    IsPretriangulatedSubcategoryWithTriangles P (restrictedTriangles P) := by
  refine
    { shiftAutoEquiv := h2.1
      mem_obj := ?_
      subset_distinguished := ?_
      isomorphic_mem := ?_
      contractible_mem := ?_
      cocone_mem := ?_
      rotate_mem := ?_
      complete_morphism := ?_ }
  · -- mem_obj
    rintro T ⟨_, h1, h2', h3⟩
    exact ⟨h1, h2', h3⟩
  · -- subset_distinguished
    rintro T ⟨hd, _, _, _⟩
    exact hd
  · -- isomorphic_mem
    rintro T₁ ⟨hT₁dist, _, _, _⟩ T₂ hP1 hP2 hP3 e
    exact ⟨isomorphic_distinguished T₁ hT₁dist T₂ e, hP1, hP2, hP3⟩
  · -- contractible_mem
    intro X hX
    obtain ⟨Z, hZero, hPZ⟩ := hP.containsZero
    exact ⟨Z, hZero, hPZ, contractible_distinguished_of_isZero X hZero, hX, hX, hPZ⟩
  · -- cocone_mem
    intro X Y hX hY f
    obtain ⟨Z, g, h, hdist, W, hPW, ⟨e⟩⟩ := h2.2 hX hY f
    obtain ⟨g', h', hdist'⟩ := exists_distinguished_of_iso_obj₃ hdist e
    exact ⟨W, hPW, g', h', ⟨hdist', hX, hY, hPW⟩⟩
  · -- rotate_mem
    intro T hP1 hP2 hP3
    constructor
    · rintro ⟨hd, _, _, _⟩
      exact ⟨(rotate_distinguished_triangle T).mp hd, hP2, hP3, h2.1.shift_mem T.obj₁ hP1⟩
    · rintro ⟨hd, _, _, _⟩
      exact ⟨(rotate_distinguished_triangle T).mpr hd, hP1, hP2, hP3⟩
  · -- complete_morphism
    rintro T₁ ⟨hT₁dist, _, _, _⟩ T₂ ⟨hT₂dist, _, _, _⟩ a b sq
    exact complete_distinguished_triangle_morphism T₁ T₂ hT₁dist hT₂dist a b sq

/-- **Sub-lemma E (uniqueness of `T'`).** Any set `T'` making `(D', T')` a
pre-triangulated subcategory coincides with `restrictedTriangles P`.

INFORMAL ARGUMENT. Show `T' = R := restrictedTriangles P` by mutual inclusion
(`Set.ext` / `subset_antisymm`).
* `T' ⊆ R`: if `T ∈ T'` then `T` is distinguished by `h.subset_distinguished` and
  has vertices in `D'` by `h.mem_obj`; hence `T ∈ R`.
* `R ⊆ T'`: let `T = (X, Y, Z, f, g, h) ∈ R`, so distinguished with `P X, P Y,
  P Z`. By `h.cocone_mem (P X) (P Y) f` there is a triangle
  `T₀ = (X, Y, Z₀, f, g₀, h₀) ∈ T'`, which is distinguished (by
  `h.subset_distinguished`). Two distinguished triangles sharing the morphism `f`
  on their first two vertices are isomorphic by the identity on the first two
  vertices:   `Pretriangulated.isoTriangleOfIso₁₂ T T₀ hT_dist hT₀_dist (Iso.refl X)
  (Iso.refl Y) (by simp)` gives `eT : T ≅ T₀` (its `hom₁ = 𝟙 X`, `hom₂ = 𝟙 Y`,
  and `hom₃` an isomorphism). Since `h.isomorphic_mem` is stated as
  `∀ T₁ ∈ T', ∀ T₂, … → (T₂ ≅ T₁) → T₂ ∈ T'`, apply it with `T₁ := T₀ ∈ T'`,
  `T₂ := T`, and the iso `eT : T ≅ T₀` *directly* (NOT `eT.symm`), together with
  `P X, P Y, P Z`; this yields `T ∈ T'`. (Note: the vertices fed to
  `isomorphic_mem` are those of `T`, the eta-expansion `Triangle.mk T.obj₁ …` may
  need a `convert … using 1` to match `T`.) -/
lemma unique_restrictedTriangles (P : ObjectProperty C)
    (T' : Set (Triangle C))
    (h : IsPretriangulatedSubcategoryWithTriangles P T') :
    T' = restrictedTriangles P := by
  apply Set.eq_of_subset_of_subset
  · -- T' ⊆ R
    exact fun T hT => ⟨h.subset_distinguished hT, h.mem_obj T hT⟩
  · -- R ⊆ T'
    rintro T ⟨hTdist, hP1, hP2, hP3⟩
    obtain ⟨Z₀, hZ₀, g₀, h₀, hmem⟩ := h.cocone_mem hP1 hP2 T.mor₁
    exact h.isomorphic_mem _ hmem T hP1 hP2 hP3
      (isoTriangleOfIso₁₂ T (Triangle.mk T.mor₁ g₀ h₀) hTdist (h.subset_distinguished hmem)
        (Iso.refl _) (Iso.refl _) (by simp))

/-- **Sub-lemma F (internal octahedral axiom TR4 for `restrictedTriangles`).**
When `D` is triangulated, the canonical set `restrictedTriangles P` satisfies the
internal octahedral axiom `InternalTR4`.

INFORMAL ARGUMENT. Let `R := restrictedTriangles P`. Given `X, Y, Z ∈ D'`,
`f : X ⟶ Y`, `g : Y ⟶ Z`, and three triangles of `R`
`(X, Y, Q₁, f, p₁, d₁)`, `(X, Z, Q₂, f≫g, p₂, d₂)`, `(Y, Z, Q₃, g, p₃, d₃)`,
each is distinguished in `D` (by `R ⊆ distTriang`) with `Q₁, Q₂, Q₃ ∈ D'`. Apply
`D`'s octahedral axiom via `Triangulated.someOctahedron (comm := rfl) h₁₂ h₂₃ h₁₃`
with the identification of variables
`u₁₂ = f, u₂₃ = g, u₁₃ = f ≫ g` (so `comm : f ≫ g = f ≫ g` is `rfl`),
`Z₁₂ = Q₁, v₁₂ = p₁, w₁₂ = d₁`; `Z₂₃ = Q₃, v₂₃ = p₃, w₂₃ = d₃`;
`Z₁₃ = Q₂, v₁₃ = p₂, w₁₃ = d₂`. The octahedron provides `m₁ : Q₁ ⟶ Q₂`,
`m₃ : Q₂ ⟶ Q₃` with:
  `comm₁ : p₁ ≫ m₁ = g ≫ p₂`, `comm₂ : m₁ ≫ d₂ = d₁`, `comm₃ : p₂ ≫ m₃ = p₃`,
  `comm₄ : d₂ ≫ f⟦1⟧ = m₃ ≫ d₃`, and the octahedron triangle
  `Triangle.mk m₁ m₃ (d₃ ≫ p₁⟦1⟧) ∈ distTriang C`.
Set `a := m₁`, `b := m₃`. The octahedron triangle is exactly
`Triangle.mk a b (d₃ ≫ (shiftFunctor C 1).map p₁)` and has vertices `Q₁, Q₂, Q₃ ∈
D'`, so lies in `R` — clause (a). Clauses (b) `p₁ ≫ a = g ≫ p₂` and
`d₁ = a ≫ d₂` are `comm₁` and `comm₂.symm`; clauses (c) `p₂ ≫ b = p₃` and
`d₂ ≫ f⟦1⟧ = b ≫ d₃` are `comm₃` and `comm₄`. (The variable matching is exactly
the one recorded in Mathlib's `Octahedron` docstring, where `m₁`/`m₃` are the
morphisms `a`/`b` of Stacks TR4 and the octahedron triangle's third map is
`w₂₃ ≫ v₁₂⟦1⟧ = d₃ ≫ p₁⟦1⟧`.) -/
lemma internalTR4_restrictedTriangles (P : ObjectProperty C)
    [IsTriangulated C] :
    InternalTR4 P (restrictedTriangles P) := by
  intro X Y Z hX hY hZ f g Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ p₁ d₁ p₂ d₂ p₃ d₃ hT₁ hT₂ hT₃
  obtain ⟨h₁₂, _, _, _⟩ := hT₁
  obtain ⟨h₁₃, _, _, _⟩ := hT₂
  obtain ⟨h₂₃, _, _, _⟩ := hT₃
  obtain ⟨m₁, m₃, comm₁, comm₂, comm₃, comm₄, mem⟩ :=
    Triangulated.someOctahedron (rfl : f ≫ g = f ≫ g) h₁₂ h₂₃ h₁₃
  exact ⟨m₁, m₃, ⟨mem, hQ₁, hQ₂, hQ₃⟩, comm₁, comm₂.symm, comm₃, comm₄⟩

-- Main Statement(s)

/-- **Statement 1** (Tag 05QX, equivalence of (1) and (2)). For an additive full
subcategory `D'` (described by `P`) of a pre-triangulated category `D`,
condition (1) (there *exists* a set `T'` making `(D', T')` a pre-triangulated
subcategory) is equivalent to condition (2).

PROOF SKETCH. `(1) ⇒ (2)`: destruct the existential witness `T'` and apply
`condition2_of_isPretri` (Sub-lemma C). `(2) ⇒ (1)`: provide
`restrictedTriangles P` as the witness, valid by `restrictedTriangles_isPretri`
(Sub-lemma D). -/
@[stacks 05QX]
theorem statement1 (P : ObjectProperty C)
    (hP : IsAdditiveFullSubcategory P) :
    Condition1 P ↔ Condition2 P := by
  constructor
  · rintro ⟨T', hT'⟩
    exact condition2_of_isPretri hT'
  · intro h2
    exact ⟨restrictedTriangles P, restrictedTriangles_isPretri P hP h2⟩

/-- **Statement 2** (Tag 05QX, characterization of `T'`). When the equivalent
conditions hold, the set `T'` is uniquely determined: *any* `T'` making
`(D', T')` a pre-triangulated subcategory coincides with the set of all
distinguished triangles of `D` whose three vertices lie in `D'`
(`restrictedTriangles P`), and this set indeed makes `(D', T')` a
pre-triangulated subcategory.

The two conjuncts express precisely this: (a) any valid `T'` equals
`restrictedTriangles P` (uniqueness, quantified over an arbitrary candidate
`T'`), and (b) `restrictedTriangles P` is itself valid (given condition (2)).

PROOF SKETCH. The first conjunct is `unique_restrictedTriangles` (Sub-lemma E),
applied to each candidate `T'`. The second conjunct is
`restrictedTriangles_isPretri` (Sub-lemma D). -/
@[stacks 05QX]
theorem statement2 (P : ObjectProperty C)
    (hP : IsAdditiveFullSubcategory P) :
    (∀ T' : Set (Triangle C),
        IsPretriangulatedSubcategoryWithTriangles P T' →
          T' = restrictedTriangles P) ∧
      (Condition2 P →
        IsPretriangulatedSubcategoryWithTriangles P (restrictedTriangles P)) := by
  refine ⟨fun T' hT' => unique_restrictedTriangles P T' hT', fun h2 => ?_⟩
  exact restrictedTriangles_isPretri P hP h2

/-- **Statement 3** (Tag 05QX, the triangulated case). If `D` is moreover a
triangulated category (it satisfies the octahedral condition TR4), then
conditions (1) and (2) are further equivalent to:
`(D', restrictedTriangles P)` is a *triangulated* subcategory of `D`, i.e. it is
a pre-triangulated subcategory whose induced pre-triangulated structure on `D'`
again satisfies TR4 (the octahedral axiom internal to `D'`, with the full
morphism-of-triangles compatibility conditions).

PROOF SKETCH. First conjunct `Condition1 P ↔ Condition2 P`: this is exactly
`statement1 P hP`. Second conjunct `Condition2 P ↔
IsTriangulatedSubcategoryWithTriangles P (restrictedTriangles P)`:
* `(⇒)`: from `Condition2 P`, the pre-triangulated half is
  `restrictedTriangles_isPretri P hP h2` (Sub-lemma D), and the octahedral half
  is `internalTR4_restrictedTriangles P hP` (Sub-lemma F); package them into the
  `IsTriangulatedSubcategoryWithTriangles` structure (constructor from its
  `toIsPretriangulatedSubcategoryWithTriangles` field plus `internalTR4`).
* `(⇐)`: an `IsTriangulatedSubcategoryWithTriangles P (restrictedTriangles P)`
  contains (via `.toIsPretriangulatedSubcategoryWithTriangles`) a witness for
  `Condition1 P`; convert to `Condition2 P` through `condition2_of_isPretri`
  (Sub-lemma C), or equivalently the forward direction of `statement1`. -/
@[stacks 05QX]
theorem statement3 (P : ObjectProperty C)
    (hP : IsAdditiveFullSubcategory P) [IsTriangulated C] :
    (Condition1 P ↔ Condition2 P) ∧
      (Condition2 P ↔
        IsTriangulatedSubcategoryWithTriangles P (restrictedTriangles P)) := by
  refine ⟨statement1 P hP, ?_, ?_⟩
  · intro h2
    exact
      { toIsPretriangulatedSubcategoryWithTriangles :=
          restrictedTriangles_isPretri P hP h2
        internalTR4 := internalTR4_restrictedTriangles P }
  · intro h
    exact condition2_of_isPretri h.toIsPretriangulatedSubcategoryWithTriangles

end Stacks.Triangulated.SubcategoryWithTriangles

end

end

add_to_stacks 05QY CategoryTheory.Functor.IsTriangulated.instAdditive
