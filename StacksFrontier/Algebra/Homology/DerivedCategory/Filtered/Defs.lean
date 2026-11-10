module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Filtration.Basic
public import StacksCore.CategoryTheory.Filtration.GradedPieces
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered derived categories

Let `C` be a category. A *filtered object* of `C` is an object `X` together with a decreasing
`ℤ`-indexed filtration
`X ⊇ ⋯ ⊇ F^n X ⊇ F^{n + 1} X ⊇ ⋯`
by subobjects; these form the category `Fil(C)`, which `Mathlib` provides as
`CategoryTheory.FilteredObject C ℤᵒᵖ`, a filtration being a functor `ℤᵒᵖ ⥤ MonoOver X` (every
morphism of `MonoOver X` is a monomorphism over `X`, so such a functor is exactly a decreasing
family of subobjects of `X` together with its inclusions). The filtration is *finite* if
`F^n X = X` for some `n` and `F^m X = 0` for some `m`, and `Fil^f(C)` is the full subcategory of
`Fil(C)` on the filtered objects whose filtration is finite.

Now let `𝒜` be abelian. A filtered cochain complex of `𝒜` — equivalently, a complex of filtered
objects of `𝒜` — has `p`-th *graded piece* the quotient complex `gr^p K^• = F^p K^•/F^{p+1} K^•`,
and `gr^p` is a functor. A morphism `α : K^• ⟶ L^•` is a *filtered quasi-isomorphism* if every
`gr^p(α)` is a quasi-isomorphism, and `K^•` is *filtered acyclic* if every `gr^p K^•` is acyclic.
Both are conditions on the associated graded and not on the underlying complexes: an isomorphism
of complexes which shifts the filtration is not a filtered quasi-isomorphism. The **filtered
derived category** is the localisation

`DF(𝒜) = K(Fil^f(𝒜))/FAc(𝒜) = FQis(𝒜)^{-1}K(Fil^f(𝒜))`

of the complexes of finite filtered objects at the filtered quasi-isomorphisms `FQis(𝒜)`, whose
kernel is the class `FAc(𝒜)` of filtered acyclic complexes ([Stacks, Tag 05S1]); the two
descriptions agree because a quotient by a subcategory is by definition the localisation at the
morphisms whose cone lies in it. Its *bounded below*, *bounded above* and *bounded* parts
`DF^{+}(𝒜)`, `DF^{-}(𝒜)`, `DF^b(𝒜)` are the full subcategories on the objects `X` whose
associated graded `gr(X)` is bounded below, resp. above, resp. both, in the derived category:
`H^n(gr(X))` vanishes for `n ≪ 0`, resp. `n ≫ 0`, resp. `|n| ≫ 0`.

## Main definitions

* `CategoryTheory.Filtration.IsDegreewiseFinite`: a `ℤ`-indexed filtration of a homological
  complex is finite in each degree.
* `CategoryTheory.Filtration.ofDiagram`: the filtration attached to a diagram of subobjects.
* `CategoryTheory.FiniteFilteredObject`: the category `Fil^f(C)` of finite filtered objects, those
  whose filtration is `CategoryTheory.Filtration.IsFinite`.
* `CategoryTheory.FilteredObject.IsFilteredInjective`: the filtered injective objects of
  `Fil^f(C)`, those all of whose graded pieces are injective.
* `CochainComplex.evalFil`: the filtered object `(K^n, F^• K^n)` in degree `n` of a filtered
  cochain complex `K^•`.
* `CochainComplex.filteredQuasiIso`: the morphisms of filtered complexes all of whose graded
  pieces are quasi-isomorphisms.
* `CochainComplex.filteredAcyclic`: the filtered complexes all of whose graded pieces are acyclic.
* `CochainComplex.FilteredDerivedCategory`: the filtered derived category `DF(𝒜)`, the
  localisation of the filtered complexes with degreewise finite filtration at the filtered
  quasi-isomorphisms.
* `CochainComplex.filteredPlus`, `CochainComplex.filteredMinus`,
  `CochainComplex.filteredBounded`: the objects of `DF^{+}(𝒜)`, `DF^{-}(𝒜)`, `DF^b(𝒜)`.

## Implementation notes

*Filtered complexes rather than complexes of filtered objects.* A complex of filtered objects
`(K^n, F)` is the same datum as a complex `K^•` filtered by subcomplexes `F^p K^•`, and a
morphism of either kind is a morphism of complexes respecting `F`; so
`FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ` is the source's category of complexes of `Fil(𝒜)`, with
`ℤᵒᵖ` recording that the filtration decreases. Its graded pieces are the complexes
`(FilteredObject.gr p).obj K`, with `FilteredObject.gr p` the functor `gr^p` of
`StacksCore.CategoryTheory.Filtration.GradedPieces`. The category `Fil(𝒜)` is preadditive with a
zero
object and binary biproducts ([Stacks, Tag 0122]), but the triangulated structure of the homotopy
category `K(Fil^f(𝒜))` is not available, so the exactness of the functors induced on `DF(𝒜)`
cannot yet be stated, only their existence.

*Complexes rather than the homotopy category.* Filtered quasi-isomorphism, filtered acyclicity
and the vanishing conditions on the graded pieces are invariant under filtered homotopy — `gr^p`
is additive, so it carries a filtered homotopy between `α` and `β` to a homotopy between
`gr^p(α)` and `gr^p(β)`, and quasi-isomorphism is homotopy invariant — so they are the source's
conditions on `K(Fil^f(𝒜))` read through a representing morphism of complexes, and localising the
filtered complexes at `FQis(𝒜)` is localising `K(Fil^f(𝒜))` at `FQis(𝒜)`. This is also what
`Mathlib` does for the derived category itself: `DerivedCategory 𝒜` localises
`CochainComplex 𝒜 ℤ`, not `K(𝒜)`.

*`gr` is the family `(gr^p)_p`.* The source phrases both notions with the single functor
`gr = ⨁_p gr^p` into complexes of graded objects, and records at once that they are equivalent to
the conditions on the pieces. The pieces are the available reading — `GradedObject ℤ 𝒜` carries no
`Preadditive` instance, so `K(Gr(𝒜))` cannot be formed — and the correct one for a filtration that
is not finite, homology commuting with an infinite direct sum only when coproducts are exact.
Homology of a complex of graded objects is computed componentwise, so `H^n(gr(X)) = 0` says
`H^n(gr^p X) = 0` for every `p`, with `n` independent of `p`: that is why the existential
quantifier stands outside the quantifier over `p` in `filteredPlus` and `filteredMinus`. The
per-`p` condition is strictly weaker, both for these definitions and for the replacement of a
filtered complex by a bounded one, and with it the latter statement is
false: for `K^•` the complex `ℤ` in degree `-1` and `ℤ` in degree `0` over `𝒜 = ModuleCat ℤ`,
with zero differential and `F^p K^• = K^•` for `p ≤ -1`, `F^0 K^• = ℤ` in degree `-1` and
`F^p K^• = 0` for `p ≥ 1`, each `gr^p K^•` is concentrated in one degree, while a filtered
quasi-isomorphism `K^• ⟶ L^•` with `L^n = 0` for `n < 0` would give
`ℤ = H^{-1}(gr^0 K^•) ≅ H^{-1}(gr^0 L^•) = 0`.

*Bounded homology rather than membership in `D^b`.* For a cochain complex `K` of `𝒜`, membership
of `Q(K)` in the bounded below part of `D(𝒜)` is `K.IsGE n` for some `n`
(`DerivedCategory.isGE_Q_obj_iff`, and `DerivedCategory.isLE_Q_obj_iff` for `IsLE`), while
`DerivedCategory.Plus`, `.Minus` and `.Bounded` are cut out by `∃ n, IsGE X n`, `∃ n, IsLE X n`
and their meet for the canonical t-structure. Phrasing the condition on the complex drops the
hypothesis `[HasDerivedCategory 𝒜]`, which the notion does not need. `CochainComplex.IsGE` and
`CochainComplex.IsLE` are the *cohomological* conditions `H^i(K) = 0` for `i < n`, resp. `n < i`,
not the strict ones on the objects `K^i`.

*Finiteness of the filtration, where it is used and where it is not.* `filteredQuasiIso`,
`filteredAcyclic`, `filteredPlus`, `filteredMinus` and `filteredBounded` do not use it and read
verbatim on `Fil(𝒜)`; since `Fil^f(𝒜)` is a full subcategory of `Fil(𝒜)`, they restrict to the
source's setting. It is a hypothesis of the theorems about them, not of the definitions. In
`FilteredDerivedCategory` it cannot be dropped, being the identity of the category defined:
localising *all* filtered complexes gives the filtered derived category of `Fil(𝒜)`, in which
every `gr^p` of a constant filtration vanishes, so every object is filtered acyclic and every
morphism is inverted. There, and in the hypotheses of the two theorems, the finiteness is
*degreewise*, as in the source — for every `n` some `F^p K^n` is all of `K^n` and some `F^q K^n`
is zero: `Filtration.IsDegreewiseFinite`, the degreewise form of `Filtration.IsFinite` applied to
the filtration of `K^n`. That is strictly weaker than finiteness of the filtration of the complex
`K^•`, one `p` and one `q` serving all degrees at once (the uniformly bounded objects are
Illusie's smaller filtered derived category), and it is all the proofs use. Neither half of it can
be dropped from the theorems: with the constant filtration `F^p K^• = K^•` (no vanishing) or the
zero filtration `F^p K^• = 0` (no exhaustion) every graded piece is zero, so every morphism is a
filtered quasi-isomorphism and the underlying morphism of complexes is arbitrary; and for `K^•`
the module `⨁_{p ≥ 0} ℤ` in degree `0` filtered by `F^p K^• = ⨁_{q ≥ p} ℤ` for `p ≥ 0`, which
exhausts but never vanishes, every graded piece is `ℤ` in degree `0`, while a complex finitely
filtered in degree `0` has `gr^p = 0` in degree `0` for all large `p`, so no replacement of `K^•`
inside `K(Fil^f(𝒜))` exists at all.

*The localisation and its functor.* `DF(𝒜)` is `MorphismProperty.Localization` at `FQis(𝒜)`, and
the localisation functor `Q : K(Fil^f(𝒜)) ⥤ DF(𝒜)` is `MorphismProperty.Q` of that construction,
characterised by `Functor.q_isLocalization`; no separate name is introduced for it. It is an
`abbrev` so that `Mathlib`'s API for `W.Localization` — that it is a category, that `Q` inverts
`FQis(𝒜)` universally, and, once `Fil^f(𝒜)` is known to be additive, that it is triangulated with
`Q` exact — transfers by unfolding. `DF(𝒜)` therefore lives in the universe of the filtered
complexes; a user needing another universe has `W.Localization'` under `[W.HasLocalization]`, the
variant by which `Mathlib` fixes the universe of `D(𝒜)`, equivalent to this one as a localisation
at the same class. That `DF(𝒜)` is triangulated is not part of the definition: its content is
[Stacks, Tag 05S1] together with [Stacks, Tag 05R6], and it cannot yet be stated for want of a
shift and of distinguished triangles on the filtered complexes.

*The notions are distinct.* For `𝒜 = ModuleCat ℤ`, let `K^•` be `ℤ` in degree `0` with `F^p = K^•`
for `p ≤ 0` and `F^p = 0` for `p ≥ 1`, and `L^•` the same complex with `F^p = L^•` for `p ≤ 1` and
`F^p = 0` for `p ≥ 2`. The identity of `ℤ` is a morphism of filtered complexes `K^• ⟶ L^•` and an
isomorphism of the underlying complexes, while `gr^0(α) : ℤ ⟶ 0` is not a quasi-isomorphism: so
`filteredQuasiIso` is strictly finer than quasi-isomorphism of the underlying complexes, and `Q`
is not an equivalence. For `Y^•` with `Y^n = ℤ` for `n ≥ 0`, zero differentials, and
`F^p Y^n = Y^n` for `p ≤ n`, `F^p Y^n = 0` for `p > n` — a degreewise finite filtration — one has
`gr^p Y = ℤ` in degree `p` for `p ≥ 0` and `gr^p Y = 0` for `p < 0`. Every `gr^p Y` is bounded and
`Y` lies in `filteredPlus`, while `H^n(gr(Y)) ≠ 0` for every `n ≥ 0`, so `Y` lies in neither
`filteredMinus` nor `filteredBounded`: this is the witness that the per-`p` reading of
boundedness is weaker than the source's.

## References

* [Stacks, Tag 05RY](https://stacks.math.columbia.edu/tag/05RY)
* [Stacks, Tag 015P](https://stacks.math.columbia.edu/tag/015P)
* [Stacks, Tag 05RZ](https://stacks.math.columbia.edu/tag/05RZ)
* [Stacks, Tag 05S2](https://stacks.math.columbia.edu/tag/05S2)
* [Stacks, Tag 05S4](https://stacks.math.columbia.edu/tag/05S4)
* [Stacks, Tag 03TA](https://stacks.math.columbia.edu/tag/03TA)
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits Opposite

namespace Filtration

variable {C : Type u} [Category.{v} C] {X : C} {I : Type*} [Category I]

/-- The filtration of `X` attached to a diagram `D` in `C` over `X` all of whose structure maps
`η i : D i ⟶ X` are monomorphisms: the inverse construction to `Filtration.diagram` together with
`Filtration.ι`. -/
public def ofDiagram (D : I ⥤ C) (η : D ⟶ (Functor.const I).obj X) [∀ i, Mono (η.app i)] :
    Filtration X I where
  toMonoOver :=
    { obj i := MonoOver.mk (η.app i)
      map {i j} f := MonoOver.homMk (D.map f) (by simp)
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }

variable (D : I ⥤ C) (η : D ⟶ (Functor.const I).obj X) [∀ i, Mono (η.app i)]

/-- The underlying diagram of `Filtration.ofDiagram D η` is `D`. -/
@[simp]
public lemma ofDiagram_diagram : (ofDiagram D η).diagram = D := rfl

/-- The inclusion of `Filtration.ofDiagram D η` into `X` is `η`. -/
@[simp]
public lemma ofDiagram_ι : (ofDiagram D η).ι = η := rfl

namespace IsFinite

variable {F : Filtration X ℤᵒᵖ}

/-- A finite `ℤ`-indexed filtration exhausts the ambient object at some index: the inclusion
`F^n X ⟶ X` is an isomorphism for some `n`. -/
public lemma exists_isIso_ι (h : F.IsFinite) : ∃ n : ℤ, IsIso (F.ι.app (op n)) :=
  let ⟨i, hi⟩ := h.exists_isIso
  ⟨i.unop, hi⟩

/-- A finite `ℤ`-indexed filtration vanishes at some index: `F^m X` is a zero object for some
`m`. -/
public lemma exists_isZero_obj [HasZeroMorphisms C] (h : F.IsFinite) :
    ∃ m : ℤ, IsZero (F.obj (op m)) :=
  let ⟨j, ⟨hj⟩⟩ := h.exists_isInitial
  ⟨j.unop, hj.isZero⟩

/-- A `ℤ`-indexed filtration which exhausts the ambient object at some index and vanishes at some
index is finite. -/
public lemma of_exists [HasZeroMorphisms C] (h₁ : ∃ n : ℤ, IsIso (F.ι.app (op n)))
    (h₂ : ∃ m : ℤ, IsZero (F.obj (op m))) : F.IsFinite where
  exists_isIso := let ⟨n, hn⟩ := h₁; ⟨op n, hn⟩
  exists_isInitial := let ⟨m, hm⟩ := h₂; ⟨op m, ⟨hm.isInitial⟩⟩

end IsFinite

/-- A `ℤ`-indexed decreasing filtration `F` of a homological complex `K` is *degreewise finite*
if in every degree `n` the filtration `F^p K^n` of `K^n` is finite: it exhausts `K^n` at some
index, in the sense that `F^p K^n ⟶ K^n` is an isomorphism for some `p`, and vanishes at some
index, in the sense that `F^q K^n` is a zero object for some `q`. This is strictly weaker than
`Filtration.IsFinite`, which asks for one `p` and one `q` serving all degrees at once. -/
public abbrev IsDegreewiseFinite {A : Type*} [Category A] [HasZeroMorphisms A] {ι : Type*}
    {c : ComplexShape ι} {K : HomologicalComplex A c} (F : Filtration K ℤᵒᵖ) : Prop :=
  ∀ n : ι, ∃ p q : ℤ, IsIso ((F.ι.app (op p)).f n) ∧ IsZero ((F.obj (op q)).X n)

end Filtration

/-- The category `Fil^f(C)` of *finite filtered objects* of `C`: the full subcategory of the
category `Fil(C) = FilteredObject C ℤᵒᵖ` of filtered objects `(X, F)` on those whose filtration
`F` is finite. -/
@[stacks 05RY, ega "0 11.1.3"]
public abbrev FiniteFilteredObject (C : Type u) [Category.{v} C] :=
  ObjectProperty.FullSubcategory fun F : FilteredObject C ℤᵒᵖ => F.filtration.IsFinite

/-- An object `I` of `Fil^f(C)` is *filtered injective* if each graded piece
`gr^p(I) = F^p I / F^{p + 1} I` is an injective object of `C`. As a property of a filtered object
of `C`, it records that `I` lies in `Fil^f(C)`, i.e. that its filtration is finite. -/
@[stacks 015P]
public structure FilteredObject.IsFilteredInjective {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasCokernels C] (I : FilteredObject C ℤᵒᵖ) : Prop where
  /-- The filtration of `I` is finite, i.e. `I` is an object of `Fil^f(C)`. -/
  isFinite : I.filtration.IsFinite
  /-- Every graded piece `gr^p(I)` is an injective object. -/
  injective_gr (p : ℤ) : Injective ((FilteredObject.gr p).obj I)

end CategoryTheory

namespace CochainComplex

open CategoryTheory Limits Opposite

variable (A : Type u) [Category.{v} A] [Abelian A]

section EvalFil

variable {A}

/-- The filtered object `(K^n, F^• K^n)` of `A` in degree `n` of a filtered cochain complex `K^•`:
the filtration by the subcomplexes `F^p K^•` evaluates, degree by degree, to a filtration by
subobjects, because evaluation in degree `n` preserves monomorphisms. -/
@[implicit_reducible]
public noncomputable def evalFil
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (n : ℤ) : FilteredObject A ℤᵒᵖ where
  X := K.X.X n
  filtration := ⟨K.filtration.toMonoOver ⋙ MonoOver.lift
    (Over.post (HomologicalComplex.eval A (ComplexShape.up ℤ) n))
    (fun f => by have := f.2; dsimp [Over.post]; infer_instance)⟩

/-- The inclusion `F^i K^n ⟶ K^n` of the degree `n` filtered object of `K^•`. -/
public lemma evalFil_ι_app
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (n : ℤ) (i : ℤᵒᵖ) :
    (evalFil K n).filtration.ι.app i = (K.filtration.ι.app i).f n :=
  rfl

/-- Each step of the filtration of a filtered complex is, in each degree, a subobject of that
degree of the complex: evaluation in degree `n` preserves monomorphisms. -/
public lemma mono_ι_app_f (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (i : ℤᵒᵖ) (n : ℤ) :
    Mono ((K.filtration.ι.app i).f n) :=
  inferInstanceAs (Mono ((evalFil K n).filtration.ι.app i))

/-- The step `F^i K^n` of the degree `n` filtered object of `K^•`. -/
public lemma evalFil_obj
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (n : ℤ) (i : ℤᵒᵖ) :
    (evalFil K n).filtration.obj i = (K.filtration.obj i).X n :=
  rfl

/-- `gr^p` of a filtered complex, in degree `n`, is `gr^p` of its degree `n` filtered object:
evaluation preserves the cokernel that defines `gr^p`. -/
public noncomputable def evalGradedPieceIso (M : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (p n : ℤ) : ((FilteredObject.gr p).obj M).X n ≅
      (FilteredObject.gr p).obj (evalFil M n) :=
  PreservesCokernel.iso (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
    (M.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)

/-- The degree `n` filtered object of a filtered complex `K^•` is a filtered injective object of
`Fil^f(A)` exactly when the filtration of `K^n` is finite and every `gr^p(K^•)` is injective in
degree `n`. -/
public theorem isFilteredInjective_evalFil_iff
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (n : ℤ) :
    (evalFil K n).IsFilteredInjective ↔
      (∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
        IsZero ((K.filtration.obj (op q)).X n)) ∧
      ∀ p : ℤ, Injective (((FilteredObject.gr p).obj K).X n) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h.isFinite.exists_isIso_ι
    obtain ⟨q, hq⟩ := h.isFinite.exists_isZero_obj
    rw [evalFil_ι_app] at hp
    rw [evalFil_obj] at hq
    exact ⟨⟨p, q, hp, hq⟩,
      fun r => Injective.of_iso (evalGradedPieceIso K r n).symm (h.injective_gr r)⟩
  · rintro ⟨⟨p, q, hp, hq⟩, h⟩
    rw [← evalFil_ι_app] at hp
    rw [← evalFil_obj] at hq
    exact ⟨.of_exists ⟨p, hp⟩ ⟨q, hq⟩,
      fun r => Injective.of_iso (evalGradedPieceIso K r n) (h r)⟩

end EvalFil

/-- A morphism `α : K^• ⟶ L^•` of filtered cochain complexes of an abelian category `A` is a
**filtered quasi-isomorphism** if `gr^p(α) : gr^p K^• ⟶ gr^p L^•` is a quasi-isomorphism for
every `p : ℤ`, equivalently if `gr(α)` is a quasi-isomorphism. -/
@[stacks 05RZ "part (1)",
  sga "4 Vbis 2.5.1" "Σ: Gr_n quasi-iso",
  sga "4½ Rapport 4.4" "filtered quasi-iso"]
public def filteredQuasiIso : MorphismProperty (FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :=
  fun _ _ α => ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map α)

/-- A filtered cochain complex `K^•` of an abelian category `A` is **filtered acyclic** if the
complex `gr^p K^•` is acyclic for every `p : ℤ`, equivalently if `gr(K^•)` is acyclic. -/
@[stacks 05RZ "part (2)"]
public def filteredAcyclic : ObjectProperty (FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :=
  fun K => ∀ p : ℤ, ((FilteredObject.gr p).obj K).Acyclic

/-- The **filtered derived category** `DF(A)` of an abelian category `A`: the localisation of
`K(Fil^f(A))` at the class `FQis(A)` of filtered quasi-isomorphisms, equivalently the quotient
`K(Fil^f(A))/FAc(A)` by the filtered acyclic complexes ([Stacks, Tag 05S1]). Here `K(Fil^f(A))` is
modelled by the cochain complexes of `A` filtered by subcomplexes whose filtration is finite in
each degree — for every `n` some `F^p K^n` is all of `K^n` and some `F^q K^n` is zero — and the
localisation functor `Q : K(Fil^f(A)) ⥤ DF(A)` is `MorphismProperty.Q`, whose kernel is `FAc(A)`
([Stacks, Tag 05S1]). It is triangulated, with the structure induced along
`K(Fil^f(A)) ⥤ DF(A)` (`CochainComplex.FilteredDerivedCategory.Qh`), which is exact. -/
@[stacks 05S2]
public abbrev FilteredDerivedCategory :=
  ((filteredQuasiIso A).inverseImage
    (ObjectProperty.ι fun K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ => ∀ n : ℤ, ∃ p q : ℤ,
      IsIso ((K.filtration.ι.app (op p)).f n) ∧
        IsZero ((K.filtration.obj (op q)).X n))).Localization

/-- The filtered cochain complexes `X` of an abelian category `A` whose associated graded is
bounded below, i.e. such that `H^n(gr(X)) = 0` for `n ≪ 0`: there is an `n : ℤ`, independent of
`p`, with `H^i(gr^p X) = 0` for all `i < n` and all `p`. These are the objects of the **bounded
below filtered derived category** `DF^{+}(A)`, the full subcategory of `DF(A)` on the objects `X`
such that `gr(X)` lies in the bounded below derived category (`D^{+}(Gr(A))`, written `D^{+}(A)`
in the source). -/
@[stacks 05S4 "DF^+(A), the bounded below filtered derived category"]
public def filteredPlus : ObjectProperty (FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :=
  fun X => ∃ n : ℤ, ∀ p : ℤ, ((FilteredObject.gr p).obj X).IsGE n

/-- The filtered cochain complexes `X` of an abelian category `A` whose associated graded is
bounded above, i.e. such that `H^n(gr(X)) = 0` for `n ≫ 0`: there is an `n : ℤ`, independent of
`p`, with `H^i(gr^p X) = 0` for all `n < i` and all `p`. These are the objects of the **bounded
above filtered derived category** `DF^{-}(A)`, the full subcategory of `DF(A)` on the objects `X`
such that `gr(X)` lies in the bounded above derived category (`D^{-}(Gr(A))`, written `D^{-}(A)`
in the source). -/
@[stacks 05S4 "DF^-(A), the bounded above filtered derived category"]
public def filteredMinus : ObjectProperty (FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :=
  fun X => ∃ n : ℤ, ∀ p : ℤ, ((FilteredObject.gr p).obj X).IsLE n

/-- The filtered cochain complexes `X` of an abelian category `A` whose associated graded is
bounded, i.e. such that `H^n(gr(X)) = 0` for `|n| ≫ 0`: there are `a b : ℤ`, independent of `p`,
with `H^i(gr^p X) = 0` for `i < a` and for `b < i`, for every `p`. These are the objects of the
**bounded filtered derived category** `DF^b(A)`, the full subcategory of `DF(A)` on the objects
`X` such that `gr(X)` lies in the bounded derived category (`D^b(Gr(A))`, written `D^b(A)` in the
source). -/
@[stacks 05S4 "DF^b(A), the bounded filtered derived category"]
public def filteredBounded : ObjectProperty (FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :=
  filteredPlus A ⊓ filteredMinus A

end CochainComplex

end
