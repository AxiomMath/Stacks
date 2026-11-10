module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is Lemma 13.16.9 of the Stacks project (tag 015F), in the chapter on Derived
Categories, Section 13.16 (Higher derived functors).

Throughout, `F : A ⥤ B` is an *exact* additive functor between abelian categories
(i.e. `F` is additive and preserves both kernels and cokernels, equivalently `F`
carries short exact sequences to short exact sequences).  The functor `F` induces an
exact functor of triangulated categories `F : K(A) ⥤ K(B)` on the homotopy categories
of complexes, and likewise on the bounded-below variants `K⁺`.  Composing with the
localization functor `K(B) ⥤ D(B)` gives functors `F : K(A) ⥤ D(B)` and
`F : K⁺(A) ⥤ D⁺(B)` (Stacks, Situation 13.15.1, tag 05T4).  The right derived functor
`RF` is the right derived functor of these along the saturated multiplicative system
`Qis(A)` (resp. `Qis⁺(A)`) of quasi-isomorphisms.

The lemma asserts the following five statements for an exact functor `F`:

1. Every object of `A` is right acyclic for `F`; i.e. for every object `A` the complex
   `A[0]`, viewed in `K⁺(A)`, computes `RF : D⁺(A) ⥤ D⁺(B)`.
2. `RF : D⁺(A) ⥤ D⁺(B)` is everywhere defined.
3. `RF : D(A) ⥤ D(B)` is everywhere defined.
4. Every complex computes `RF`: for every complex `K` (bounded below in the `D⁺`
   setting, arbitrary in the `D` setting), the canonical map `F(K) ⟶ RF(K)` is an
   isomorphism in `D(B)` (resp. `D⁺(B)`).
5. `RⁱF = 0` for `i ≠ 0`, while `R⁰F ≅ F`.

The essential reason all five hold is that an exact functor `F` commutes with the
formation of cohomology, hence sends quasi-isomorphisms to quasi-isomorphisms.
Therefore the composite `F : K(A) ⥤ D(B)` already inverts `Qis(A)`, so the induced
functor `D(A) ⥤ D(B)` is itself the (everywhere defined) right derived functor, with
the canonical map `F ⟶ RF` an isomorphism on all complexes; the bounded-below
statements follow by restricting to `K⁺(A)`.

## Notes on the formalization

### General derived functor vocabulary (Stacks Definitions 1-3)

We use Mathlib's framework for derived functors of an exact functor of triangulated
categories `F : D ⥤ D'` relative to a multiplicative system `S` (Stacks Situation
13.14.1, tag 05S8).  For a localization functor `L : D ⥤ D_loc` of `S`:

- "`RF` is defined at `X`" (Stacks Definition 1, tag 05S9; the value of the
  essentially-constant ind-object `(X/S) ⥤ D'`) is
  `Functor.HasPointwiseRightDerivedFunctorAt F S X`, the existence of the pointwise
  left Kan extension of `F` along `L` at `L.obj X` — exactly the colimit over the
  comma category `X/S`.
- "`RF` is everywhere defined / `F` is right derivable" (Definition 2, tag 05SV) is
  `Functor.HasPointwiseRightDerivedFunctor F S`.
- The assembled exact functor `RF : D_loc ⥤ D'` together with the canonical
  transformation `α : F ⟶ L ⋙ RF` is recorded by `Functor.IsRightDerivedFunctor RF α S`:
  `RF` is *the* right derived functor of `F` (with respect to `α`).  This is the
  precise sense in which a chosen functor and a chosen comparison map "is the right
  derived functor".
- "`X` computes `RF`" (Definition 3, tag 05SX): `RF` is defined at `X` and the
  canonical map `F(X) ⟶ RF(X)` (the component of `α` at `X`) is an isomorphism in `D'`.

### The localized (derived) categories `D(A)`, `D⁺(A)`

- The unbounded derived category `D(A)` is `DerivedCategory A`, with the localization
  functor `DerivedCategory.Qh : K(A) ⥤ D(A)` of `Qis(A) = HomotopyCategory.quasiIso A`.
  For an exact `F`, the right derived functor `RF : D(A) ⥤ D(B)` is
  `F.mapDerivedCategory` and the canonical comparison `F ⟶ Qh ⋙ RF` is the inverse of
  the factorization isomorphism `F.mapDerivedCategoryFactorsh`.

- Mathlib has no dedicated type for the bounded-below derived category `D⁺(A)`, so we
  *construct* it as the genuine localization of `K⁺(A) = HomotopyCategory.Plus A` at
  its system of quasi-isomorphisms `Qis⁺(A) = HomotopyCategory.Plus.quasiIso A`, namely
  `DPlus A := (HomotopyCategory.Plus.quasiIso A).Localization`, with localization
  functor `QPlus A := MorphismProperty.Q (Qis⁺(A)) : K⁺(A) ⥤ D⁺(A)`.  This is a genuine
  `L.IsLocalization W`.  An exact `F` restricts to `mapPlus F : K⁺(A) ⥤ K⁺(B)` (an
  additive functor preserves bounded-below complexes), and the functor to be derived is
  `functorPlus F : K⁺(A) ⥤ D⁺(B)`, `K ↦ QPlus B (mapPlus F K)`.  Since `F` inverts
  quasi-isomorphisms, `functorPlus F` inverts `Qis⁺(A)`, so it factors (uniquely up to
  iso) through `D⁺(A)`, yielding the genuine right derived functor
  `RFPlus F : D⁺(A) ⥤ D⁺(B)` with comparison
  `canonicalPlus F : functorPlus F ⟶ QPlus A ⋙ RFPlus F`.

### Higher right derived functors (Stacks Definition 5)

`RⁱF = Hⁱ ∘ RF : A ⥤ B`, `A ↦ Hⁱ(RF(A[0]))`, encoded with `DerivedCategory.singleFunctor`
(`A[0]`) and `DerivedCategory.homologyFunctor` (`Hⁱ`).  This is degree-wise so it does
not matter whether one uses the bounded-below or unbounded `RF`; we use the unbounded
`F.mapDerivedCategory`, which agrees with `RFPlus` on single complexes.
-/

open CategoryTheory Limits

namespace Stacks.DerivedFunctor.HigherDerivedOfExact

universe v u v' u' w₂ w₁

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The chosen complex shape for cochain complexes (cohomological grading by `ℤ`). -/
abbrev shape : ComplexShape ℤ := ComplexShape.up ℤ

/-! ## The unbounded setting `K(A) ⥤ D(B)` -/

/-- The functor `F : K(A) ⥤ D(B)`, namely `F` applied termwise on the homotopy category
of complexes, followed by the localization `K(B) ⥤ D(B)` (Stacks, Situation 13.15.1,
tag 05T4).  This is the functor whose right derived functor along `Qis(A)` is `RF`. -/
noncomputable def functorKtoD : HomotopyCategory A shape ⥤ DerivedCategory B :=
  F.mapHomotopyCategory shape ⋙ DerivedCategory.Qh

/-- The multiplicative system `Qis(A)` of quasi-isomorphisms in `K(A)`, with respect to
which the localization `DerivedCategory.Qh : K(A) ⥤ D(A)` is performed. -/
abbrev qis : MorphismProperty (HomotopyCategory A shape) := HomotopyCategory.quasiIso A shape

/-- The right derived functor `RF : D(A) ⥤ D(B)` of the exact functor `F`.  For an exact
functor this is provided by `F.mapDerivedCategory`, the functor induced on derived
categories by applying `F` termwise. -/
noncomputable def RF : DerivedCategory A ⥤ DerivedCategory B := F.mapDerivedCategory

/-- The canonical natural transformation `F ⟶ RF` of Stacks Definition 2 (tag 05SV) in
the unbounded setting: for the functor `F : K(A) ⥤ D(B)` (`functorKtoD F`) and its right
derived functor `RF = F.mapDerivedCategory` relative to `Qh : K(A) ⥤ D(A)`, it is the
comparison `functorKtoD F ⟶ Qh ⋙ RF`, the inverse of the factorization isomorphism. -/
noncomputable def canonical :
    functorKtoD F ⟶ DerivedCategory.Qh ⋙ RF F :=
  (F.mapDerivedCategoryFactorsh).inv

/-! ## The bounded-below setting `K⁺(A) ⥤ D⁺(B)`

`K⁺(A) = HomotopyCategory.Plus A`.  We construct the genuine bounded-below derived
category `D⁺(A)` as the localization of `K⁺(A)` at `Qis⁺(A)`. -/

/-- The system `Qis⁺(A)` of quasi-isomorphisms in `K⁺(A)`, namely the pullback of
`Qis(A)` along the inclusion `K⁺(A) ↪ K(A)`. -/
abbrev qisPlus : MorphismProperty (HomotopyCategory.Plus A) := HomotopyCategory.Plus.quasiIso A

/-- The bounded-below derived category `D⁺(A)`, defined as the localization of the
bounded-below homotopy category `K⁺(A)` at the multiplicative system `Qis⁺(A)` of
quasi-isomorphisms (Stacks, Situation 13.15.1, tag 05T4). -/
abbrev DPlus (C : Type w₁) [Category.{w₂} C] [Abelian C] : Type (max w₁ w₂) :=
  (HomotopyCategory.Plus.quasiIso C).Localization

/-- The localization functor `QPlus : K⁺(A) ⥤ D⁺(A)` exhibiting `D⁺(A)` as the
localization of `K⁺(A)` at `Qis⁺(A)`. -/
noncomputable abbrev QPlus (C : Type w₁) [Category.{w₂} C] [Abelian C] :
    HomotopyCategory.Plus C ⥤ DPlus C :=
  MorphismProperty.Q (HomotopyCategory.Plus.quasiIso C)

omit [HasDerivedCategory A] [HasDerivedCategory B] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] in
/-- An additive functor preserves bounded-below complexes: if a complex `X` (viewed in
`K(A)`) is bounded below, then so is `F` applied termwise.  (Used to restrict `F` to a
functor `K⁺(A) ⥤ K⁺(B)`.) -/
lemma mapHomotopyCategory_preserves_plus
    (X : HomotopyCategory A shape) (hX : (HomotopyCategory.plus A) X) :
    (HomotopyCategory.plus B) ((F.mapHomotopyCategory shape).obj X) := by
  -- INFORMAL ARGUMENT.
  -- `HomotopyCategory.plus A` is the property "isomorphic (in `K(A)`) to a complex `K`
  -- that is bounded below", i.e. there is `n : ℤ` with `K.X i = 0` (or `K.IsStrictlyGE n`)
  -- for `i < n`.  `F` is additive, hence `F.obj 0 ≅ 0` (`Functor.Additive` ⟹ `F` preserves
  -- the zero object: `Functor.mapZeroObject` / `F.obj 0 ≅ 0`).  Applying `F` termwise
  -- (`F.mapHomologicalComplex shape`) sends a complex strictly bounded below by `n` to a
  -- complex strictly bounded below by the same `n`, because the degree-`i` term of the
  -- image is `F.obj (K.X i)`, which is `≅ 0` whenever `K.X i = 0`.  `F.mapHomotopyCategory`
  -- agrees with `F.mapHomologicalComplex` on objects up to the quotient `K(-)`, and the
  -- boundedness predicate is invariant under homotopy-equivalence/isomorphism, so the image
  -- of a bounded-below object is bounded below.
  -- STRATEGY HINT (formal phase).
  -- Unfold `HomotopyCategory.plus` to its `Subcategory`/`isoClosure` form
  -- (`HomotopyCategory.plus`, `HomotopyCategory.Plus`, `HomotopyCategory.subcategoryPlus`,
  -- and `CochainComplex.isStrictlyGE` / `HomologicalComplex.IsStrictlyGE`).  Extract the
  -- witness bound from `hX`, transport along the iso `(F.mapHomotopyCategory shape).obj` vs.
  -- the quotient of `(F.mapHomologicalComplex shape).obj`, and conclude via
  -- `Functor.Additive`'s `F.obj 0 ≅ 0` (`F.map_zero`/`Limits.IsZero.map`).  Search Mathlib
  -- for `HomotopyCategory.mem_plus_iff`, `HomologicalComplex.isStrictlyGE_map` (or the
  -- single-functor/boundedness preservation lemmas for `mapHomologicalComplex`).
  -- SANITY CHECK PASSED (true, non-vacuous; axle_disprove could not refute; F.Additive ⟹ F.obj 0 ≅
  -- 0
  -- preserves the bound. NOTE: mem_plus_iff / isStrictlyGE_map do NOT exist in `stacks`; unfold
  -- HomotopyCategory.plus (an ObjectProperty/isoClosure) and extract a CochainComplex.IsStrictlyGE
  -- witness.)
  -- `HomotopyCategory.plus C = (CochainComplex.plus C).strictMap (quotient C shape)`, whose sole
  -- constructor sends a cochain complex `K` with `CochainComplex.plus C K` (i.e. `∃ n,
  -- K.IsStrictlyGE n`)
  -- to `quotient.obj K`.  Destructuring `hX` yields such a `K`, `n` and `K.IsStrictlyGE n`.  Since
  -- `(F.mapHomotopyCategory shape).obj (quotient.obj K) = quotient.obj ((F.mapHomologicalComplex
  -- shape).obj K)`
  -- definitionally, it suffices to show the termwise image is strictly `≥ n`: in each degree `i'`
  -- not in
  -- the support its term is `F.obj (K.X i')` with `K.X i'` a zero object, and `F.map_isZero` keeps
  -- it zero.
  obtain ⟨K, n, hKn⟩ := hX
  have hge : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex shape).obj K) n := by
    refine ⟨fun i' hi' => ?_⟩
    have hz : IsZero (K.X i') := hKn.isZero i' hi'
    exact F.map_isZero hz
  exact ⟨(F.mapHomologicalComplex shape).obj K, n, hge⟩

/-- The restriction `F : K⁺(A) ⥤ K⁺(B)` of `F` to bounded-below homotopy categories:
include `K⁺(A) ↪ K(A)`, apply `F` termwise, and corestrict back into `K⁺(B)`. -/
noncomputable def mapPlus : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B :=
  (HomotopyCategory.plus B).lift
    (HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory shape)
    (fun X => mapHomotopyCategory_preserves_plus F X.1 X.2)

/-- The functor `F : K⁺(A) ⥤ D⁺(B)` to be derived in the bounded-below setting: restrict
`F` to `K⁺(A) ⥤ K⁺(B)` (`mapPlus F`), then localize `K⁺(B) ⥤ D⁺(B)` (`QPlus B`). -/
noncomputable def functorPlus : HomotopyCategory.Plus A ⥤ DPlus B :=
  mapPlus F ⋙ QPlus B

/-- **Heart of the matter (shared infrastructure).** An exact functor preserves homology
(`Functor.preservesHomologyOfExact`), hence the induced functor on homotopy categories
`F.mapHomotopyCategory shape : K(A) ⥤ K(B)` carries quasi-isomorphisms to
quasi-isomorphisms.  This single fact underlies the inverting statements for both the
unbounded and the bounded-below settings. -/
lemma mapHomotopyCategory_inverts_quasiIso :
    (HomotopyCategory.quasiIso A shape).IsInvertedBy
      (F.mapHomotopyCategory shape ⋙ DerivedCategory.Qh) := by
  -- INFORMAL ARGUMENT.
  -- A morphism `f` in `K(A)` is a quasi-isomorphism iff `Hⁿ(f)` is an isomorphism for all
  -- `n` (`HomotopyCategory.mem_quasiIso_iff`).  Since `F` is exact it preserves homology
  -- (`Functor.preservesHomologyOfExact F : F.PreservesHomology`), and the homology functor
  -- commutes with `F.mapHomotopyCategory` up to natural isomorphism, so `Hⁿ(F.map f) ≅
  -- F(Hⁿ(f))` is an isomorphism whenever `Hⁿ(f)` is.  Hence `F.mapHomotopyCategory shape`
  -- sends quasi-isos to quasi-isos, and composing with `Qh : K(B) ⥤ D(B)` (which inverts
  -- quasi-isos by construction of the derived category) sends them to isomorphisms in `D(B)`.
  -- STRATEGY HINT (formal phase).
  -- `intro X Y f hf`; rewrite `hf` with `HomotopyCategory.mem_quasiIso_iff`.  The chain-level
  -- statement is `HomologicalComplex.quasiIso_map_of_preservesHomology φ F` (needs
  -- `haveI := Functor.preservesHomologyOfExact F`).  Then `DerivedCategory.Qh` inverts
  -- quasi-isos: a `HomotopyCategory.quasiIso`-morphism becomes `IsIso` under `Qh`
  -- (`DerivedCategory.isIso_Qh_map_iff` / `DerivedCategory.Qh` is the localization at
  -- `HomotopyCategory.quasiIso`).  Equivalently use that `F.mapHomotopyCategory` preserves
  -- `HomotopyCategory.quasiIso` and `Qh.inverts (HomotopyCategory.quasiIso B shape)`.
  -- SANITY CHECK PASSED (true, non-vacuous, correctly stated; axle_disprove could not refute).
  rw [← MorphismProperty.IsInvertedBy.iff_of_iso _ F.mapDerivedCategoryFactorsh]
  exact MorphismProperty.IsInvertedBy.of_comp _ _
    (Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A shape))
    F.mapDerivedCategory

/-- **Key fact.** Since the exact functor `F` sends quasi-isomorphisms to
quasi-isomorphisms, the functor `functorPlus F : K⁺(A) ⥤ D⁺(B)` inverts the system
`Qis⁺(A)`.  This is what makes `functorPlus F` factor through `D⁺(A)`, exhibiting its
factorization as the right derived functor. -/
lemma functorPlus_isInvertedBy :
    (HomotopyCategory.Plus.quasiIso A).IsInvertedBy (functorPlus F) := by
  -- INFORMAL ARGUMENT.
  -- A morphism `s` in `K⁺(A)` lies in `Qis⁺(A)` iff its image `Plus.ι A s` in `K(A)` lies
  -- in `Qis(A)` (this is how `HomotopyCategory.Plus.quasiIso` is defined: the system
  -- pulled back along the inclusion `Plus.ι A : K⁺(A) ↪ K(A)`).  By definition
  -- `functorPlus F = mapPlus F ⋙ QPlus B`, and `mapPlus F` is the corestriction of
  -- `Plus.ι A ⋙ F.mapHomotopyCategory shape`, so on morphisms `functorPlus F` factors as
  -- "include into `K(A)`, apply `F.mapHomotopyCategory`, land in `K⁺(B)`, then localize".
  -- The composite `Plus.ι A ⋙ F.mapHomotopyCategory shape` sends `Qis⁺(A)` into `Qis(B)` by
  -- the shared lemma `mapHomotopyCategory_inverts_quasiIso` (its image under `Plus.ι` is a
  -- quasi-iso in `K(A)`, mapped to a quasi-iso in `K(B)`).  Finally `QPlus B` is the
  -- localization of `K⁺(B)` at `Qis⁺(B)`, so it inverts these images.  Hence `functorPlus F`
  -- inverts `Qis⁺(A)`.
  -- STRATEGY HINT (formal phase).
  -- `intro X Y s hs`.  Unfold `HomotopyCategory.Plus.quasiIso` / `mapPlus` / `functorPlus`.
  -- Reduce `hs` to a `HomotopyCategory.quasiIso A shape` statement about `(Plus.ι A).map s`
  -- (`HomotopyCategory.Plus.quasiIso` membership ↔ `Plus.ι` image in `quasiIso`); use the
  -- compatibility lemma `mapHomotopyCategory_inverts_quasiIso` (composed with the fact that
  -- `Plus.ι B ⋙ Qh ≅ QPlus B ⋙ (D⁺ ↪ D)` — or directly that `QPlus B` inverts `Qis⁺(B)` via
  -- `MorphismProperty.Q` being the localization, `Localization.inverts`).  Then `IsIso` of
  --   the `functorPlus F`-image follows.
  -- SANITY CHECK PASSED (true, non-vacuous, correctly stated; axle_disprove could not refute).
  intro X Y s hs
  rw [HomotopyCategory.Plus.quasiIso] at hs
  rw [MorphismProperty.inverseImage] at hs
  change HomotopyCategory.quasiIso A shape ((HomotopyCategory.Plus.ι A).map s) at hs
  have h1 : HomotopyCategory.quasiIso B shape
      ((F.mapHomotopyCategory shape).map ((HomotopyCategory.Plus.ι A).map s)) := by
    rw [← DerivedCategory.isIso_Qh_map_iff]
    exact mapHomotopyCategory_inverts_quasiIso F _ hs
  have h2 : HomotopyCategory.Plus.quasiIso B ((mapPlus F).map s) := by
    change HomotopyCategory.quasiIso B shape ((HomotopyCategory.Plus.ι B).map ((mapPlus F).map s))
    exact h1
  exact Localization.inverts (QPlus B) (HomotopyCategory.Plus.quasiIso B) _ h2

/-- The right derived functor `RF : D⁺(A) ⥤ D⁺(B)` in the bounded-below setting, defined
as the (essentially unique) factorization of `functorPlus F` through the localization
`QPlus A : K⁺(A) ⥤ D⁺(A)`, provided by the universal property of the localization. -/
noncomputable def RFPlus : DPlus A ⥤ DPlus B :=
  Localization.lift (functorPlus F) (functorPlus_isInvertedBy F) (QPlus A)

/-- The canonical natural transformation `F ⟶ RF` of Stacks Definition 2 (tag 05SV) in
the bounded-below setting: `functorPlus F ⟶ QPlus A ⋙ RFPlus F`, the inverse of the
factorization isomorphism `QPlus A ⋙ RFPlus F ≅ functorPlus F`. -/
noncomputable def canonicalPlus :
    functorPlus F ⟶ QPlus A ⋙ RFPlus F :=
  (Localization.fac (functorPlus F) (functorPlus_isInvertedBy F) (QPlus A)).inv

/-! ## Higher right derived functors -/

/-- Stacks Definition 5 (tag 015A): the `i`-th right derived functor `RⁱF = Hⁱ ∘ RF`,
sending `A ↦ Hⁱ(RF(A[0]))`.  Here `A[0]` is encoded by the single-object embedding
`DerivedCategory.singleFunctor A 0 : A ⥤ D(A)`, `RF` is `F.mapDerivedCategory`, and `Hⁱ`
is `DerivedCategory.homologyFunctor B i`. -/
noncomputable def higherDerived (i : ℤ) : A ⥤ B :=
  DerivedCategory.singleFunctor A 0 ⋙ RF F ⋙ DerivedCategory.homologyFunctor B i

/-! ## Main Statement(s) -/

/-- **Statement (2): `RF : D⁺(A) ⥤ D⁺(B)` is everywhere defined.**
`RF` relative to `Qis⁺(A)` is defined at every object of `K⁺(A)` (Stacks Definition 2,
tag 05SV), and the constructed functor `RFPlus F : D⁺(A) ⥤ D⁺(B)`, together with its
canonical comparison `canonicalPlus F`, *is* the right derived functor of
`functorPlus F : K⁺(A) ⥤ D⁺(B)` along `Qis⁺(A)` (it satisfies the universal property
`Functor.IsRightDerivedFunctor`). -/
@[stacks 015F "(2)"]
theorem everywhere_defined_plus :
    (functorPlus F).HasPointwiseRightDerivedFunctor (qisPlus (A := A)) ∧
      (RFPlus F).IsRightDerivedFunctor (canonicalPlus F) (qisPlus (A := A)) := by
  -- INFORMAL ARGUMENT.
  -- (a) Pointwise everywhere defined: `functorPlus F` inverts `Qis⁺(A)`
  --     (`functorPlus_isInvertedBy F`), and a functor that inverts `W` has a pointwise right
  --     derived functor relative to `W` (it is its own derived functor; the comma categories
  --     `K/W` have an initial-ish constancy because everything is already inverted).
  -- (b) `RFPlus F` is the right derived functor with comparison `canonicalPlus F`:
  --     `RFPlus F = Localization.lift (functorPlus F) (functorPlus_isInvertedBy F) (QPlus A)`
  --     and `canonicalPlus F` is the inverse of `Localization.fac …`, i.e. of the iso
  --     `QPlus A ⋙ RFPlus F ≅ functorPlus F`.  By definition `IsRightDerivedFunctor RF α W`
  --     means `RF.IsLeftKanExtension α`; the lift of a `W`-inverting functor along the
  --     localization `QPlus A` is exactly the left Kan extension, with the unit `α` the
  --     (inverse of the) factorization iso.
  -- STRATEGY HINT (formal phase).
  -- `refine ⟨?_, ?_⟩`.
  -- First goal: `exact Functor.hasPointwiseRightDerivedFunctor_of_inverts _
  -- (functorPlus_isInvertedBy F)`.
  -- Second goal: build `(RFPlus F).IsLeftKanExtension (canonicalPlus F)` (then
  --   `⟨·⟩`/`IsRightDerivedFunctor.mk`).  Since `QPlus A` is a localization at `Qis⁺(A)` and
  --   `functorPlus F` inverts it, the lift is a left Kan extension: look for
  --   `Localization.Lifting`/`Localization.lift` + `isLeftKanExtension` API
  --   (`CategoryTheory.Localization.isLeftKanExtension*`, or derive it from
  --   `Localization.lift_uniq`/the universal property), with `canonicalPlus F` = inverse of
  --   `Localization.fac`.  SUB-LEMMA worth isolating: "the localization-lift of a
  --   `W`-inverting functor is its right derived functor with the `fac⁻¹` comparison".
  -- SANITY CHECK PASSED (plausible; standard derived-functor fact, type-aligned;
  -- 1st conjunct closes by `hasPointwiseRightDerivedFunctor_of_inverts`, 2nd reduces
  -- via `Functor.isRightDerivedFunctor_iff_isLeftKanExtension` to `IsLeftKanExtension`).
  refine ⟨Functor.hasPointwiseRightDerivedFunctor_of_inverts _ (functorPlus_isInvertedBy F), ?_⟩
  exact Functor.instIsRightDerivedFunctorLiftInvFac
    (HomotopyCategory.Plus.quasiIso A) (functorPlus_isInvertedBy F)

/-- **Statement (3): `RF : D(A) ⥤ D(B)` is everywhere defined.**
`RF` relative to `Qis(A)` is defined at every object of `K(A)` (Stacks Definition 2,
tag 05SV), and the chosen functor `RF F = F.mapDerivedCategory`, together with its
canonical comparison `canonical F`, *is* the right derived functor of
`functorKtoD F : K(A) ⥤ D(B)` along `Qis(A)`. -/
@[stacks 015F "(3)"]
theorem everywhere_defined :
    (functorKtoD F).HasPointwiseRightDerivedFunctor (qis (A := A)) ∧
      (RF F).IsRightDerivedFunctor (canonical F) (qis (A := A)) := by
  -- INFORMAL ARGUMENT.
  -- (a) `functorKtoD F = F.mapHomotopyCategory shape ⋙ DerivedCategory.Qh` inverts `Qis(A)`
  --     by the shared lemma `mapHomotopyCategory_inverts_quasiIso F`.  A `W`-inverting
  --     functor has a pointwise right derived functor.
  -- (b) `RF F = F.mapDerivedCategory` and `canonical F = (F.mapDerivedCategoryFactorsh).inv`.
  --     The factorization `F.mapDerivedCategoryFactorsh : Qh ⋙ F.mapDerivedCategory ≅
  --     F.mapHomotopyCategory shape ⋙ Qh = functorKtoD F` is an ISO, so `canonical F` is an
  --     iso `functorKtoD F ≅ Qh ⋙ RF F`.  Since `Qh` is the localization of `K(A)` at
  --     `Qis(A)` and `functorKtoD F` inverts `Qis(A)`, the comparison being iso exhibits
  --     `RF F` as the (left Kan extension =) right derived functor.
  -- STRATEGY HINT (formal phase).
  -- `refine ⟨?_, ?_⟩`.
  -- First goal: `exact Functor.hasPointwiseRightDerivedFunctor_of_inverts _
  -- (mapHomotopyCategory_inverts_quasiIso F)`.
  -- Second goal: `canonical F` is `(F.mapDerivedCategoryFactorsh).inv`, hence
  --   `IsIso (canonical F)` (`inferInstance`/`IsIso.of_iso_inv` on `mapDerivedCategoryFactorsh`).
  --   Combined with `Qh` being
  --   `DerivedCategory.Qh.IsLocalization (HomotopyCategory.quasiIso A shape)` and `functorKtoD F`
  --   inverting `Qis(A)`, conclude `RF.IsLeftKanExtension (canonical F)`.
  --   SUB-LEMMA (shared with `everywhere_defined_plus`): "if `L` is a localization at `W`,
  --   `F` inverts `W`, and `α : F ⟶ L ⋙ RF` is an iso, then `RF.IsRightDerivedFunctor α W`".
  --   Mathlib may already package this for `mapDerivedCategory`; search
  --   `mapDerivedCategory` + `IsRightDerivedFunctor` / `isLeftKanExtension`.
  -- SANITY CHECK PASSED (plausible; standard derived-functor fact, type-aligned; 1st conjunct
  -- closes by `hasPointwiseRightDerivedFunctor_of_inverts`, 2nd is the unbounded analogue of L4).
  refine ⟨Functor.hasPointwiseRightDerivedFunctor_of_inverts _
      (mapHomotopyCategory_inverts_quasiIso F), ?_⟩
  exact (Functor.isRightDerivedFunctor_iff_of_inverts _ _
    (mapHomotopyCategory_inverts_quasiIso F)).2 (by delta canonical; infer_instance)

/-- **Statement (4), bounded-below: every bounded-below complex computes `RF`.**
For every object `K` of `K⁺(A)`, `RF` is defined at `K` relative to `Qis⁺(A)` and the
canonical map `F(K) ⟶ RF(K)`, i.e. the component `(canonicalPlus F).app K` of the
comparison transformation that exhibits `RFPlus F` as the right derived functor, is an
isomorphism in `D⁺(B)`. -/
@[sga "4 XVIII 3.1.4.8" "(ii), special case"]
theorem complexes_compute_plus (K : HomotopyCategory.Plus A) :
    (functorPlus F).HasPointwiseRightDerivedFunctorAt (qisPlus (A := A)) K ∧
      IsIso ((canonicalPlus F).app K) := by
  -- INFORMAL ARGUMENT.
  -- (a) Defined at `K`: pointwise-everywhere-defined (from `everywhere_defined_plus`, or
  --     directly `Functor.HasPointwiseRightDerivedFunctorAt` for a `W`-inverting functor)
  --     specializes to `K`.
  -- (b) The canonical map is an iso at every object: `canonicalPlus F` is the inverse of the
  --     factorization isomorphism `Localization.fac …`, hence a natural ISO; its component
  --     at any `K` is therefore an isomorphism.
  -- STRATEGY HINT (formal phase).
  -- `refine ⟨?_, ?_⟩`.
  -- First goal: `(everywhere_defined_plus F).1` gives `HasPointwiseRightDerivedFunctor`; obtain
  --   the `…At K` instance from it (`Functor.HasPointwiseRightDerivedFunctor.hasPointwiseAt`/
  --   the projection that pointwise-everywhere implies pointwise-at every object), OR use
  --   `Functor.hasPointwiseRightDerivedFunctorAt_of_inverts` if it exists, OR derive `At` from
  --   the global instance.
  -- Second goal: `canonicalPlus F = (Localization.fac …).inv`; an `Iso.inv` is `IsIso`, and the
  --   `app` of an `IsIso` natural transformation is `IsIso` (`NatTrans.isIso_app_of_isIso` /
  --   `inferInstance` since `canonicalPlus F` is `(Iso).inv`).  So `IsIso ((canonicalPlus F).app
  -- K)`.
  -- SANITY CHECK PASSED (true, provable; bounded-below twin of complexes_compute; both conjuncts
  -- via everywhere_defined_plus + canonicalPlus = Iso.inv).
  have := (everywhere_defined_plus F).2
  have := Functor.isIso_of_isRightDerivedFunctor_of_inverts _ (canonicalPlus F)
    (functorPlus_isInvertedBy F)
  exact ⟨(everywhere_defined_plus F).1 K, inferInstance⟩

/-- **Statement (4), unbounded: every complex computes `RF`.**
For every complex `K` of `A` (an object of `K(A)`), `RF` is defined at `K` and the
canonical map `F(K) ⟶ RF(K)`, i.e. the component `(canonical F).app K` of the comparison
transformation that exhibits `RF F` as the right derived functor, is an isomorphism in
`D(B)`. -/
@[stacks 015F "(4)"]
theorem complexes_compute (K : HomotopyCategory A shape) :
    (functorKtoD F).HasPointwiseRightDerivedFunctorAt (qis (A := A)) K ∧
      IsIso ((canonical F).app K) := by
  -- INFORMAL ARGUMENT.
  -- (a) Defined at `K`: from `everywhere_defined F` (pointwise everywhere defined) specialized
  --     to `K`, since `functorKtoD F` inverts `Qis(A)` (`mapHomotopyCategory_inverts_quasiIso F`).
  -- (b) `canonical F = (F.mapDerivedCategoryFactorsh).inv` is the inverse of an ISO, hence a
  --     natural iso, so its component at `K` is an isomorphism.
  -- STRATEGY HINT (formal phase).
  -- `refine ⟨?_, ?_⟩`.
  -- First goal: from `(everywhere_defined F).1 : HasPointwiseRightDerivedFunctor`, get the
  --   `…At K` form (projection from everywhere-defined, or
  --   `Functor.hasPointwiseRightDerivedFunctorAt_of_inverts`).
  -- Second goal: `canonical F` is `(F.mapDerivedCategoryFactorsh).inv`; therefore
  --   `IsIso (canonical F)` (instance on `Iso.inv`), and the `.app K` of an iso-NatTrans is
  --   `IsIso` (`inferInstance`).  So `IsIso ((canonical F).app K)`.
  -- SANITY CHECK PASSED (true, provable; both conjuncts via everywhere_defined + canonical =
  -- Iso.inv).
  have := (everywhere_defined F).2
  have := Functor.isIso_of_isRightDerivedFunctor_of_inverts _ (canonical F)
    (mapHomotopyCategory_inverts_quasiIso F)
  exact ⟨(everywhere_defined F).1 K, inferInstance⟩

/-- **Statement (1): Every object of `A` is right acyclic for `F` (bounded-below).**
For every object `X` of `A`, the complex `X[0]`, viewed in `K⁺(A)`, computes
`RF : D⁺(A) ⥤ D⁺(B)` (Stacks Definition 4, tag 0157): `RF` is defined at `X[0]` relative
to `Qis⁺(A)` and the canonical map `F(X[0]) ⟶ RF(X[0])`, i.e. the component of the
comparison `canonicalPlus F` exhibiting `RFPlus F` as the right derived functor, is an
isomorphism in `D⁺(B)`.  Here `X[0]` is `(HomotopyCategory.Plus.singleFunctor A 0).obj X`,
the single complex concentrated in degree `0` regarded in `K⁺(A)`. -/
@[stacks 015F "(1)"]
theorem objects_right_acyclic (X : A) :
    (functorPlus F).HasPointwiseRightDerivedFunctorAt (qisPlus (A := A))
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X) ∧
      IsIso ((canonicalPlus F).app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := by
  -- INFORMAL ARGUMENT.
  -- This is the special case of statement (4) bounded-below (`complexes_compute_plus`) at the
  -- particular object `K = X[0] = (HomotopyCategory.Plus.singleFunctor A 0).obj X`.  Since
  -- EVERY bounded-below complex computes `RF`, in particular the single complex `X[0]` does:
  -- `RF` is defined there and the canonical map `F(X[0]) ⟶ RF(X[0])` is an iso.  By Stacks
  -- Definition 4 this says exactly that `X` is right acyclic for `F`.
  -- STRATEGY HINT (formal phase).
  -- `exact complexes_compute_plus F ((HomotopyCategory.Plus.singleFunctor A 0).obj X)`.
  -- (Direct specialization — no new content.  Closable as soon as `complexes_compute_plus`
  -- is proved.)
  exact complexes_compute_plus F ((HomotopyCategory.Plus.singleFunctor A 0).obj X)

/-- **Statement (5a): `RⁱF = 0` for `i ≠ 0`.**
For every integer `i ≠ 0`, the functor `RⁱF = Hⁱ ∘ RF : A ⥤ B` is the zero functor;
equivalently `Hⁱ(RF(A[0])) = 0` for all objects `A` and all `i ≠ 0`. -/
@[stacks 015F "(5)"]
theorem higherDerived_eq_zero (i : ℤ) (hi : i ≠ 0) :
    IsZero (higherDerived F i) := by
  -- INFORMAL ARGUMENT.
  -- `higherDerived F i = singleFunctor A 0 ⋙ RF F ⋙ homologyFunctor B i` with `RF F =
  -- F.mapDerivedCategory`.  By `F.mapDerivedCategorySingleFunctor 0` there is a natural iso
  --   `singleFunctor A 0 ⋙ F.mapDerivedCategory ≅ F ⋙ singleFunctor B 0`,
  -- i.e. `RF(X[0]) ≅ (F X)[0]` naturally in `X`.  Composing with `homologyFunctor B i`:
  --   `higherDerived F i ≅ F ⋙ (singleFunctor B 0 ⋙ homologyFunctor B i)`.
  -- For `i ≠ 0`, the homology of a complex concentrated in degree `0` vanishes in degree `i`:
  -- `singleFunctor B 0 ⋙ homologyFunctor B i` is the zero functor (`Hⁱ((F X)[0]) = 0`).
  -- Hence `higherDerived F i` is naturally isomorphic to a functor landing in zero objects,
  -- so it is the zero functor (`IsZero`).
  -- STRATEGY HINT (formal phase).
  -- Rewrite `higherDerived` and reassociate to expose `F ⋙ (singleFunctor B 0 ⋙ homologyFunctor B
  -- i)`
  --   using `F.mapDerivedCategorySingleFunctor 0` (whiskered by `homologyFunctor B i`).
  -- Then `IsZero` of `F ⋙ G` follows from `IsZero G` (a functor into a category that is zero
  --   on objects), and `IsZero (singleFunctor B 0 ⋙ homologyFunctor B i)` for `i ≠ 0` is the
  --   homology-of-a-single-complex vanishing.  Search Mathlib for
  --   `DerivedCategory.isZero_homologyFunctor_obj_singleFunctor_obj` /
  --   `DerivedCategory.singleFunctorCompHomologyFunctorIso` (the `i = 0` iso) and its `i ≠ 0`
  --   counterpart, or `CochainComplex.single`/`HomologicalComplex.single` homology vanishing
  --   (`HomologicalComplex.isZero_single_obj_homology` with `i ≠ 0`).  SUB-LEMMA worth
  --   isolating:
  --   `IsZero (DerivedCategory.singleFunctor B 0 ⋙ DerivedCategory.homologyFunctor B i)` for
  --   `i ≠ 0`.
  -- SANITY CHECK PASSED (true, non-vacuous; key API: F.mapDerivedCategorySingleFunctor 0,
  -- DerivedCategory.homologyFunctorFactors, HomologicalComplex.isZero_single_obj_homology,
  -- Functor.isZero).
  apply Functor.isZero
  intro X
  change IsZero ((DerivedCategory.homologyFunctor B i).obj
    ((RF F).obj ((DerivedCategory.singleFunctor A 0).obj X)))
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor B i).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app X))
  -- Goal: IsZero ((homologyFunctor B i).obj ((singleFunctor B 0).obj (F.obj X)))
  refine IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 (F.obj X) i hi) ?_
  exact ((DerivedCategory.homologyFunctor B i).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ B 0).app (F.obj X))).trans
    ((DerivedCategory.homologyFunctorFactors B i).app
      ((CochainComplex.singleFunctor B 0).obj (F.obj X)))

/-- **Statement (5b): `R⁰F ≅ F`.**
The `0`-th right derived functor `R⁰F = H⁰ ∘ RF` is naturally isomorphic to `F`.
(The isomorphism is data, so we assert its existence as a proposition.) -/
theorem higherDerived_zero_iso :
    Nonempty (higherDerived F 0 ≅ F) := by
  -- INFORMAL ARGUMENT.
  -- `higherDerived F 0 = singleFunctor A 0 ⋙ F.mapDerivedCategory ⋙ homologyFunctor B 0`.
  -- Using `F.mapDerivedCategorySingleFunctor 0 : singleFunctor A 0 ⋙ F.mapDerivedCategory ≅
  -- F ⋙ singleFunctor B 0`, whisker by `homologyFunctor B 0`:
  --   `higherDerived F 0 ≅ F ⋙ (singleFunctor B 0 ⋙ homologyFunctor B 0)`.
  -- The `i = 0` homology of a single complex in degree `0` recovers the object:
  -- `singleFunctor B 0 ⋙ homologyFunctor B 0 ≅ 𝟭 B`
  -- (`DerivedCategory.singleFunctorCompHomologyFunctorIso B 0`).  Therefore
  --   `higherDerived F 0 ≅ F ⋙ 𝟭 B ≅ F`.
  -- STRATEGY HINT (formal phase).
  -- Provide the iso explicitly and wrap in `⟨·⟩`:
  --   `exact ⟨(isoWhiskerRight (F.mapDerivedCategorySingleFunctor 0) (homologyFunctor B 0)).trans
  --      (… reassociate …) ≪≫ isoWhiskerLeft F
  -- (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0)
  --      ≪≫ F.rightUnitor⟩`
  --   (up to `Functor.associator`/`leftUnitor`/`rightUnitor` bookkeeping).  Key iso names:
  --   `Functor.mapDerivedCategorySingleFunctor`,
  -- `DerivedCategory.singleFunctorCompHomologyFunctorIso`.
  -- SANITY CHECK PASSED (true, provable; key API: F.mapDerivedCategorySingleFunctor 0,
  -- DerivedCategory.singleFunctorCompHomologyFunctorIso; whiskering is
  -- Functor.isoWhiskerRight/Left).
  refine ⟨?_⟩
  unfold higherDerived RF
  exact
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapDerivedCategorySingleFunctor 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0) ≪≫
    F.rightUnitor

end Stacks.DerivedFunctor.HigherDerivedOfExact
