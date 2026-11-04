module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.PolynomialSurjection

/-!
# The category of projective schemes over a base with an ample invertible sheaf

For a scheme `S` carrying an ample invertible sheaf, `P_S` is the full subcategory of the
category of schemes over `S` whose structure morphism is projective. This file carries the
closure properties of that category: base change, composition, fibre products, finite disjoint
unions, and the fact that a finite morphism makes its source an object of `P_S`.

## Main definitions

* `AlgebraicGeometry.HasAmpleInvertibleSheaf`: a scheme carries an ample invertible sheaf.
* `AlgebraicGeometry.projectiveOver` and `AlgebraicGeometry.ProjectiveSchemesOver`: the property
  of a scheme over `S` of being projective over `S`, and the full subcategory `P_S` it cuts out.
* `AlgebraicGeometry.ProjectiveCriteriaOverAmpleBase`: conditions (1), (2) and (5) of Tag 0B45
  over a base with an ample invertible sheaf, as a quantified `Prop`. It is **proved** below, as
  `AlgebraicGeometry.projectiveCriteriaOverAmpleBase`.

## Main results

* `AlgebraicGeometry.ProjectiveSchemesOver.baseChange`: **clause (1)**, base change along
  `S' ⟶ S` is a functor `P_S ⥤ P_{S'}`.
* `AlgebraicGeometry.isProjective_comp_of_hasAmpleInvertibleSheaf`: **clause (2)**, if `X` is
  projective over `S` and `Y` is projective over `X` then `Y` is projective over `S`.
* `AlgebraicGeometry.isProjective_pullback_snd_comp`: **clause (3)**, `P_S` is closed under fibre
  products over `S`.
* `AlgebraicGeometry.projectiveOver_isClosedUnderFiniteCoproducts`: **clause (4)**, `P_S` is
  closed under finite disjoint unions.
* `AlgebraicGeometry.isProjective_of_isFinite_of_hasAmpleInvertibleSheaf`: **clause (5)**, a
  finite morphism `X ⟶ S` makes `X` an object of `P_S`.
* `AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf` and
  `AlgebraicGeometry.isProjective_iff_isProper_and_hasAmpleInvertibleSheaf`: conditions (1) ⟺ (2)
  and (1) ⟺ (5) of Tag 0B45, which are what the five clauses consume.
* `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver`: the linear embedding
  `ℙⁿ_S ⟶ ℙᴺ_S` for `n ≤ N`, which is what lets two H-projective morphisms be compared inside
  one projective space.

## Nothing is assumed

The source's hypothesis is that `S` has an ample invertible sheaf, and that is the only
hypothesis of every clause below. Three inputs used to be carried as named `Prop`s; all three
are now discharged, and the clauses take none of them:

* Tag 0B45. `AlgebraicGeometry.isProjective_tfae_seven_of_exists_isAmple` of
  `StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveOverAmpleBase` proves conditions
  (1) to (7) of it **with nothing assumed** over a base with an ample invertible sheaf — only
  clause (8) of that tag is still attached by hypothesis there, and no clause of Tag 0B46 uses
  clause (8). So `AlgebraicGeometry.ProjectiveCriteriaOverAmpleBase` is a theorem,
  `AlgebraicGeometry.projectiveCriteriaOverAmpleBase`, and the two criteria it packages are
  stated individually above.
* Tag 01O3 for the sheaf symmetric algebra,
  `AlgebraicGeometry.ProjectiveBundleBaseChangeComparison`, which clauses (1) and (3) used
  through Tag 02V6. It is proved as
  `AlgebraicGeometry.projectiveBundleBaseChangeComparison`, and
  `AlgebraicGeometry.IsProjective.of_isPullback` now discharges it internally, so this file
  passes nothing.
* Tag 0B3I's missing capability,
  `Stacks.FiniteMorphismProjective.PushforwardIsRelativeProj`, which clauses (4) and (5) used.
  It is **not** proved — Tag 0B3I is a statement about an arbitrary base — but it is not needed:
  over a base `T` with an ample invertible sheaf, a finite morphism `f : W ⟶ T` is proper and `𝒪_W`
  is `f`-ample (`Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule`
  applied to the quasi-affineness of a finite morphism), which is condition (6) of Tag 0B45, and
  condition (6) ⟹ condition (1) is part of the unconditional cycle. That is
  `AlgebraicGeometry.isProjective_of_isFinite_of_hasAmpleInvertibleSheaf`, and it is all that
  clauses (4) and (5) ever asked Tag 0B3I for.

`AlgebraicGeometry.ProjectiveCriteriaOverAmpleBase` is kept as a `Prop` quantified over all
schemes, following the rule recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`: quantifying a `Prop` costs nothing by proof
irrelevance, and the quantified form is what a caller that still takes it as a hypothesis —
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveCategoryClosure` names it —
can discharge with one term.

Base change of a projective morphism, Tag 02V6, is **not** among the assumptions: it is proved
unconditionally in `StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange`, so clauses
(1) and (3) carry no hypothesis from it.

## Implementation notes

Membership of `X` in `P_S` is `AlgebraicGeometry.IsProjective X.hom`, condition (1) of Tag 0B45
and clause (1) of Definition 01W8; that is the condition the repository's projectivity predicate
is, and the other conditions of Tag 0B45 are equivalent to it over a base with an ample
invertible sheaf, which is the content of the hypothesis above.

Clause (4) is stated as `CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts`, so it is
about *every* finite disjoint union, not only the binary one; it is assembled from the empty and
the binary cases by `CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'`. The
binary case follows the source's route through condition (2) of Tag 0B45: a closed immersion of
`X` into `ℙⁿ_S` and of `Y` into `ℙᵐ_S` are pushed into one `ℙᴺ_S` with `N = max n m` by the
linear embedding below, and the induced morphism `X ⨿ Y ⟶ ℙᴺ_S` is finite. `ℙᴺ_S ⟶ S` is
projective by Tag 01W9, so condition (5) of Tag 0B45 at the base `S` hands back an ample
invertible sheaf **on `ℙᴺ_S`**; clause (5) over that base makes `X ⨿ Y ⟶ ℙᴺ_S` projective, and
clause (2) composes the two. The source instead reads clause (4) off condition (5) directly, by
glueing an invertible module on `Y ⨿ Z` from ample modules on `Y` and on `Z` — "details
omitted" there, and not available here, since no construction in this repository descends a
module along a coproduct of schemes.

The linear embedding `ℙⁿ ⟶ ℙᴺ` is Tag 01N0 at a polynomial ring: `ℤ[T₀, …, Tₙ]` is generated in
degree one over `ℤ` by the `N + 1` elements `T₀, …, Tₙ, 0, …, 0`, so
`Stacks.AlgebraicGeometry.RelativeProjChain.isClosedImmersion_projToProjectiveSpace` applies to
the integral models, and the embedding over `S` is its base change.

## References

* [Stacks Project, Tag 0B46](https://stacks.math.columbia.edu/tag/0B46)
* [Stacks Project, Tag 0B45](https://stacks.math.columbia.edu/tag/0B45)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 02V6](https://stacks.math.columbia.edu/tag/02V6)
* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Bases with an ample invertible sheaf -/

/-- A scheme **has an ample invertible sheaf** when some invertible sheaf of modules on it is
ample in the sense of [Stacks, Tag 01PS]. This is the hypothesis on the base throughout
[Stacks, Section 0B44]. -/
def HasAmpleInvertibleSheaf (S : Scheme.{u}) : Prop :=
  ∃ (L : S.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible S.toRingedSpace.presheaf
      (structureSheafRing
        S.toRingedSpace).property L),
    @AlgebraicGeometry.Scheme.Modules.IsAmple S L hL

/-- **Having an ample invertible sheaf, in the spelling Tag 0B45 is stated at.** The two
developments of Tag 01PS in this repository are `AlgebraicGeometry.Scheme.Modules.IsAmple`,
which `AlgebraicGeometry.HasAmpleInvertibleSheaf` is written at, and `Stacks.Ample.IsAmple`,
which `AlgebraicGeometry.isProjective_tfae_seven_of_exists_isAmple` is stated at; they agree
with no hypothesis by `Stacks.AmpleBridge.isAmple_iff_isAmple`, and the two invertibility
classes are one constant with proof-irrelevant sheaf conditions, so the witness transports
unchanged. -/
theorem hasAmpleInvertibleSheaf_iff (S : Scheme.{u}) : HasAmpleInvertibleSheaf.{u} S ↔
    ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M := by
  constructor
  · rintro ⟨L, hL, h⟩
    exact ⟨L, hL, (Stacks.AmpleBridge.isAmple_iff_isAmple S L).mpr h⟩
  · rintro ⟨M, hM, h⟩
    exact ⟨M, hM, (Stacks.AmpleBridge.isAmple_iff_isAmple S M).mp h⟩

/-! ### The criteria of Tag 0B45 that the clauses consume -/

/-- **Stacks Project, Tag 0B45, conditions (1) ⟺ (2).** Over a base carrying an ample invertible
sheaf, a morphism is projective if and only if it is H-projective.

This is `AlgebraicGeometry.isProjective_tfae_seven_of_exists_isAmple`, the unconditional part of
Tag 0B45, read between its first two entries. -/
theorem isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf {X S : Scheme.{u}}
    (f : X ⟶ S) (hS : HasAmpleInvertibleSheaf.{u} S) :
    IsProjective f ↔ IsProjectiveMorphism f :=
  (isProjective_tfae_seven_of_exists_isAmple f ((hasAmpleInvertibleSheaf_iff S).mp hS)).out 1 2

/-- **Stacks Project, Tag 0B45, conditions (1) ⟺ (5).** Over a base carrying an ample invertible
sheaf, a morphism is projective if and only if it is proper and its source carries an ample
invertible sheaf.

This is `AlgebraicGeometry.isProjective_tfae_seven_of_exists_isAmple` read between its first and
fifth entries, with `AlgebraicGeometry.hasAmpleInvertibleSheaf_iff` putting the ample sheaf on
the source into the spelling of this file. -/
@[sga "6 VIII 3.1" "more general"]
theorem isProjective_iff_isProper_and_hasAmpleInvertibleSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : HasAmpleInvertibleSheaf.{u} S) :
    IsProjective f ↔ IsProper f ∧ HasAmpleInvertibleSheaf.{u} X :=
  ((isProjective_tfae_seven_of_exists_isAmple f
      ((hasAmpleInvertibleSheaf_iff S).mp hS)).out 1 5).trans
    (and_congr_right fun _ => (hasAmpleInvertibleSheaf_iff X).symm)

/-- **Stacks Project, Tag 0B45, conditions (1), (2) and (5), quantified over every base.** Over a
base carrying an ample invertible sheaf, a morphism is projective if and only if it is
H-projective, and if and only if it is proper with source carrying an ample invertible sheaf.

This is the shape in which the clauses below need the criteria, since each applies them at more
than one base; `AlgebraicGeometry.projectiveCriteriaOverAmpleBase` proves it. -/
def ProjectiveCriteriaOverAmpleBase : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), HasAmpleInvertibleSheaf S →
    (IsProjective f ↔ IsProjectiveMorphism f) ∧
      (IsProjective f ↔ IsProper f ∧ HasAmpleInvertibleSheaf X)

/-- **Stacks Project, Tag 0B45, conditions (1), (2) and (5) over a base with an ample invertible
sheaf, with nothing assumed.** The two criteria above, packaged in the quantified form. -/
theorem projectiveCriteriaOverAmpleBase : ProjectiveCriteriaOverAmpleBase.{u} := fun f hS =>
  ⟨isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf f hS,
    isProjective_iff_isProper_and_hasAmpleInvertibleSheaf f hS⟩

/-! ### The category `P_S` -/

/-- The property, of a scheme over `S`, of being projective over `S`. -/
def projectiveOver (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X => IsProjective X.hom

/-- **`P_S` of [Stacks, Tag 0B46]**: the full subcategory of the category of schemes over `S`
whose objects are projective over `S`. -/
abbrev ProjectiveSchemesOver (S : Scheme.{u}) :=
  (projectiveOver S).FullSubcategory

/-- Projectivity over the base is invariant under isomorphism of schemes over the base: an
isomorphism in `Over S` is an isomorphism of the sources compatible with the structure
morphisms. -/
instance projectiveOver_isClosedUnderIsomorphisms (S : Scheme.{u}) :
    (projectiveOver S).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    have : IsIso e.inv.left := (inferInstance : IsIso ((Over.forget S).map e.inv))
    change IsProjective Y.hom
    rw [← Over.w e.inv]
    exact IsProjective.comp_iso (asIso e.inv.left) hX

/-! ### Clause (1): base change -/

/-- **Stacks Project, Tag 0B46, clause (1).** For a morphism of bases `g : S' ⟶ S`, base change
along `g` is a functor `P_S ⥤ P_{S'}`: the fibre product `S' ×_S X` of a scheme `X` projective
over `S` is projective over `S'`.

The object part is the first assertion of Tag 02V6,
`AlgebraicGeometry.IsProjective.of_isPullback`, applied to the fibre-product square. Its Tag
01O3 input is `AlgebraicGeometry.projectiveBundleBaseChangeComparison`, a theorem, so nothing is
assumed. -/
@[stacks 0B46 "base change"]
def ProjectiveSchemesOver.baseChange
    {S S' : Scheme.{u}} (g : S' ⟶ S) : ProjectiveSchemesOver S ⥤ ProjectiveSchemesOver S' :=
  ObjectProperty.lift (projectiveOver S') ((projectiveOver S).ι ⋙ Over.pullback g) fun X =>
    IsProjective.of_isPullback (IsPullback.of_hasPullback X.obj.hom g).flip X.property

/-! ### Clause (2): composition -/

/-- **Stacks Project, Tag 0B46, clause (2).** Let `S` carry an ample invertible sheaf. If
`f : X ⟶ S` is projective and `g : Y ⟶ X` is projective, then `g ≫ f : Y ⟶ S` is projective.

This is the source's proof. Condition (5) of Tag 0B45 at the base `S` makes `f` proper with `X`
carrying an ample invertible sheaf; the same condition at the base `X` makes `g` proper with `Y`
carrying an ample invertible sheaf; a composition of proper morphisms is proper (Tag 01W3); and
condition (5) read backwards at the base `S` returns projectivity of `g ≫ f`. Condition (5) is
part of the unconditional cycle of Tag 0B45, so nothing is assumed. -/
@[stacks 0B46 "composition"]
theorem isProjective_comp_of_hasAmpleInvertibleSheaf
    {X Y S : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ S)
    (hS : HasAmpleInvertibleSheaf S) (hf : IsProjective f) (hg : IsProjective g) :
    IsProjective (g ≫ f) := by
  obtain ⟨hfproper, hX⟩ := (isProjective_iff_isProper_and_hasAmpleInvertibleSheaf f hS).mp hf
  obtain ⟨hgproper, hY⟩ := (isProjective_iff_isProper_and_hasAmpleInvertibleSheaf g hX).mp hg
  exact (isProjective_iff_isProper_and_hasAmpleInvertibleSheaf (g ≫ f) hS).mpr
    ⟨inferInstance, hY⟩

/-! ### Clause (3): fibre products -/

/-- **Stacks Project, Tag 0B46, clause (3). `P_S` is closed under fibre products over `S`.** For
`f : X ⟶ S` and `g : Y ⟶ S` projective and `S` carrying an ample invertible sheaf, the structure
morphism `X ×_S Y ⟶ S` is projective.

The source's proof: the projection `X ×_S Y ⟶ Y` is a base change of `f`, hence projective by
clause (1), and clause (2) composes it with `g`. -/
@[stacks 0B46 "fibre products"]
theorem isProjective_pullback_snd_comp
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hS : HasAmpleInvertibleSheaf S) (hf : IsProjective f) (hg : IsProjective g) :
    IsProjective (pullback.snd f g ≫ g) :=
  isProjective_comp_of_hasAmpleInvertibleSheaf _ _ hS hg
    (IsProjective.of_isPullback (IsPullback.of_hasPullback f g).flip hf)

/-! ### Linear embeddings of projective spaces -/

/-- **The integral model of `ℙⁿ` is a closed subscheme of the integral model of `ℙᴺ`** when
`n ≤ N`.

This is [Stacks, Tag 01N0] at a polynomial ring: the graded ring `ℤ[T₀, …, Tₙ]` is generated in
degree one over `ℤ` by the `N + 1` elements `T₀, …, Tₙ, 0, …, 0`, so the induced morphism to
`Proj ℤ[T₀, …, T_N]` is defined everywhere and is a closed immersion. -/
theorem exists_isClosedImmersion_projectiveSpaceAtUniverse {n N : ℕ} (hnN : n ≤ N) :
    ∃ e : projectiveSpaceAtUniverse.{u} n ⟶ projectiveSpaceAtUniverse.{u} N,
      IsClosedImmersion e := by
  let R := ULift.{u} ℤ
  let x : Fin (N + 1) → MvPolynomial (Fin (n + 1)) R := fun k =>
    MvPolynomial.X ⟨min (k : ℕ) n, by omega⟩
  have hgen : Algebra.adjoin R (Set.range x) = ⊤ := by
    rw [eq_top_iff, ← MvPolynomial.adjoin_range_X (σ := Fin (n + 1)) (R := R)]
    refine Algebra.adjoin_mono ?_
    rintro p ⟨j, rfl⟩
    refine ⟨Fin.castLE (by omega) j, ?_⟩
    simpa [x, Fin.ext_iff] using j.is_le
  exact ⟨_, Stacks.AlgebraicGeometry.RelativeProjChain.isClosedImmersion_projToProjectiveSpace
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (fun r => (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ r))
    x (fun _ => (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _))
    hgen⟩

/-- **`ℙⁿ_S` is a closed subscheme of `ℙᴺ_S` over `S`** when `n ≤ N`: the base change along
`S ⟶ Spec ℤ` of the linear embedding of the integral models. -/
theorem exists_isClosedImmersion_projectiveSpaceOver (S : Scheme.{u}) {n N : ℕ} (hnN : n ≤ N) :
    ∃ e : projectiveSpaceOver n S ⟶ projectiveSpaceOver N S, IsClosedImmersion e ∧
      e ≫ (projectiveSpaceOver N S ↘ S) = (projectiveSpaceOver n S ↘ S) := by
  obtain ⟨i, hi⟩ := exists_isClosedImmersion_projectiveSpaceAtUniverse.{u} hnN
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun a c ha hc => @IsClosedImmersion.comp _ _ _ a c ha hc⟩
  refine ⟨pullback.map (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} N)) (𝟙 S) i (𝟙 _)
      (by simp) (by simp), ?_, ?_⟩
  · exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance hi
      (Category.id_comp _).symm (by simp)
  · exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- **A closed immersion into `ℙⁿ_S` over `S` can be enlarged to one into `ℙᴺ_S`** for any
`N ≥ n`, by composing with the linear embedding. This is what lets the witnesses of
H-projectivity of two morphisms be compared inside one projective space. -/
theorem exists_isClosedImmersion_projectiveSpaceOver_of_le {X S : Scheme.{u}} {f : X ⟶ S}
    {n : ℕ} (i : X ⟶ projectiveSpaceOver n S) (hi : IsClosedImmersion i)
    (hif : i ≫ (projectiveSpaceOver n S ↘ S) = f) {N : ℕ} (hnN : n ≤ N) :
    ∃ j : X ⟶ projectiveSpaceOver N S, IsClosedImmersion j ∧
      j ≫ (projectiveSpaceOver N S ↘ S) = f := by
  obtain ⟨e, he, heover⟩ := exists_isClosedImmersion_projectiveSpaceOver S hnN
  exact ⟨i ≫ e, inferInstance, by rw [Category.assoc, heover, hif]⟩

/-! ### Clause (5): finite morphisms -/

/-- **Stacks Project, Tag 0B46, clause (5).** A finite morphism `f : X ⟶ S` over a base carrying
an ample invertible sheaf is projective, so `X` is an object of `P_S`.

The source cites Tag 0B3I, which is about an arbitrary base and whose proof in this repository
is conditional. Over the base of Tag 0B46 none of that is needed: a finite morphism is proper
and quasi-affine, so `𝒪_X` is `f`-ample by Tag 0891 in the form
`Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule`, which is
condition (6) of Tag 0B45, and condition (6) ⟹ condition (1) belongs to the unconditional cycle
of that tag. -/
@[stacks 0B46 "finite morphisms"]
theorem isProjective_of_isFinite_of_hasAmpleInvertibleSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] (hS : HasAmpleInvertibleSheaf.{u} S) : IsProjective f := by
  have h6 : IsProper f ∧
      ∃ (L : X.Modules) (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
          X.ringCatSheaf.2 L),
        let : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
          X.ringCatSheaf.2 L := hL
        Stacks.RelativeAmple.IsRelativelyAmple f L :=
    ⟨inferInstance, Stacks.Ample.unitModule X, inferInstance,
      Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule f _
        (Iso.refl _)⟩
  exact ((isProjective_tfae_seven_of_exists_isAmple f
    ((hasAmpleInvertibleSheaf_iff S).mp hS)).out 6 1).mp h6

/-! ### Clause (4): finite disjoint unions -/

/-- **The empty disjoint union is projective** over a base carrying an ample invertible sheaf. A
morphism whose source is empty is finite, so clause (5) applies. -/
theorem isProjective_of_isEmpty {X S : Scheme.{u}} [IsEmpty X] (f : X ⟶ S)
    (hS : HasAmpleInvertibleSheaf.{u} S) : IsProjective f :=
  isProjective_of_isFinite_of_hasAmpleInvertibleSheaf f hS

/-- **The disjoint union of two schemes projective over `S` is projective over `S`**, for `S`
carrying an ample invertible sheaf.

This is the source's proof of clause (4) read through condition (2) of Tag 0B45 rather than
through condition (5). Closed immersions `X ⟶ ℙⁿ_S` and `Y ⟶ ℙᵐ_S` over `S` are enlarged to
closed immersions into one `ℙᴺ_S` with `N = max n m`; the induced morphism `X ⨿ Y ⟶ ℙᴺ_S` is
finite; `ℙᴺ_S ⟶ S` is projective by Tag 01W9, so condition (5) of Tag 0B45 puts an ample
invertible sheaf on `ℙᴺ_S` and clause (5) over that base makes `X ⨿ Y ⟶ ℙᴺ_S` projective; and
clause (2) composes the two. -/
theorem isProjective_coprod_desc
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (hS : HasAmpleInvertibleSheaf S)
    (hf : IsProjective f) (hg : IsProjective g) : IsProjective (coprod.desc f g) := by
  obtain ⟨n, i, hi, hif⟩ :=
    (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf f hS).mp hf
  obtain ⟨m, j, hj, hjg⟩ :=
    (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf g hS).mp hg
  obtain ⟨i', hi', hif'⟩ :=
    exists_isClosedImmersion_projectiveSpaceOver_of_le i hi hif (le_max_left n m)
  obtain ⟨j', hj', hjg'⟩ :=
    exists_isClosedImmersion_projectiveSpaceOver_of_le j hj hjg (le_max_right n m)
  have hbase : IsProjective (projectiveSpaceOver (max n m) S ↘ S) :=
    IsProjectiveMorphism.isProjective ⟨max n m, 𝟙 _, inferInstance, Category.id_comp _⟩
  have heq : coprod.desc f g =
      coprod.desc i' j' ≫ (projectiveSpaceOver (max n m) S ↘ S) := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, ← Category.assoc, coprod.inl_desc, hif']
    · rw [coprod.inr_desc, ← Category.assoc, coprod.inr_desc, hjg']
  rw [heq]
  exact isProjective_comp_of_hasAmpleInvertibleSheaf _ _ hS hbase
    (isProjective_of_isFinite_of_hasAmpleInvertibleSheaf _
      ((isProjective_iff_isProper_and_hasAmpleInvertibleSheaf _ hS).mp hbase).2)

/-- The scheme `∅` over `S` is an initial object of the category of schemes over `S`. -/
def isInitialOverInitial (S : Scheme.{u}) :
    IsInitial (Over.mk (initial.to S) : Over S) :=
  IsInitial.ofUniqueHom (fun T => Over.homMk (initial.to T.left) (initialIsInitial.hom_ext _ _))
    fun _ _ => Over.OverMorphism.ext (initialIsInitial.hom_ext _ _)

/-- **Binary coproducts of schemes over `S` are computed on the sources.** The disjoint union of
the sources, with the morphism induced by the two structure morphisms, is the coproduct in the
category of schemes over `S`. -/
def isColimitOverBinaryCofan {S : Scheme.{u}} (A B : Over S) :
    IsColimit (BinaryCofan.mk
      (Over.homMk coprod.inl (coprod.inl_desc _ _) :
        A ⟶ Over.mk (coprod.desc A.hom B.hom))
      (Over.homMk coprod.inr (coprod.inr_desc _ _) :
        B ⟶ Over.mk (coprod.desc A.hom B.hom))) := by
  have key : ∀ {Z : Over S} (a : A ⟶ Z) (b : B ⟶ Z),
      coprod.desc a.left b.left ≫ Z.hom = coprod.desc A.hom B.hom := by
    intro Z a b
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc_assoc, coprod.inl_desc, Over.w a]
    · rw [coprod.inr_desc_assoc, coprod.inr_desc, Over.w b]
  refine BinaryCofan.IsColimit.mk _
    (fun {Z} a b => Over.homMk (coprod.desc a.left b.left) (key a b)) ?_ ?_ ?_
  · exact fun a b => Over.OverMorphism.ext (coprod.inl_desc _ _)
  · exact fun a b => Over.OverMorphism.ext (coprod.inr_desc _ _)
  · intro Z a b m h₁ h₂
    refine Over.OverMorphism.ext ?_
    change m.left = coprod.desc a.left b.left
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, ← h₁]
      rfl
    · rw [coprod.inr_desc, ← h₂]
      rfl

/-- **Stacks Project, Tag 0B46, clause (4). `P_S` is closed under finite disjoint unions**, for
`S` carrying an ample invertible sheaf. This includes the empty disjoint union.

The empty and the binary cases are `AlgebraicGeometry.isProjective_of_isEmpty` and
`AlgebraicGeometry.isProjective_coprod_desc`, and
`CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'` assembles them into every
finite disjoint union. -/
@[stacks 0B46 "finite disjoint unions", ega "II 5.5.6" "special case"]
theorem projectiveOver_isClosedUnderFiniteCoproducts (S : Scheme.{u})
    (hS : HasAmpleInvertibleSheaf S) :
    (projectiveOver S).IsClosedUnderFiniteCoproducts := by
  have h0 : (projectiveOver S).IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty) := by
    refine ⟨?_⟩
    rintro T ⟨p⟩
    have hT : IsInitial T := (IsColimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
      (by exact Cocone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isColimit
    exact ObjectProperty.prop_of_iso _ ((isInitialOverInitial S).uniqueUpToIso hT)
      (isProjective_of_isEmpty (initial.to S) hS)
  have h2 : (projectiveOver S).IsClosedUnderBinaryCoproducts := by
    refine ⟨?_⟩
    rintro T ⟨p⟩
    have hAB : HasColimit p.diag := p.hasColimit
    have hpair : HasColimit
        (pair (p.diag.obj ⟨WalkingPair.left⟩) (p.diag.obj ⟨WalkingPair.right⟩)) :=
      hasColimit_of_iso (diagramIsoPair p.diag).symm
    have e : T ≅ Over.mk (coprod.desc (p.diag.obj ⟨WalkingPair.left⟩).hom
        (p.diag.obj ⟨WalkingPair.right⟩).hom) :=
      (p.isColimit.coconePointUniqueUpToIso (colimit.isColimit p.diag)).trans
        ((HasColimit.isoOfNatIso (diagramIsoPair p.diag)).trans
          ((colimit.isColimit _).coconePointUniqueUpToIso (isColimitOverBinaryCofan _ _)))
    exact ObjectProperty.prop_of_iso _ e.symm
      (isProjective_coprod_desc _ _ hS (p.prop_diag_obj _) (p.prop_diag_obj _))
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-! ### Clause (5) over an arbitrary base -/

/- No `0B46` registration is attached to
`Stacks.FiniteMorphismProjective.isProjective_of_isFinite`. That declaration is Tag 0B3I -- clause
(5) over an *arbitrary* base, which is more than clause (5) asks for -- but it is conditional on
`Stacks.FiniteMorphismProjective.PushforwardIsRelativeProj`, and a tag counts only on a declaration
proved under the source's own hypotheses. Clause (5) over the tag's own hypothesis on the base is
`isProjective_of_isFinite_of_hasAmpleInvertibleSheaf` above, which assumes nothing, so coverage of
0B46 is unaffected by the absence of this attribute. -/

end AlgebraicGeometry

end
