module

public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleUniversalHomeomorphismDiagonal
public import StacksFrontier.AlgebraicGeometry.UniversalHomeomorphismLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Descent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical descent datum of an étale scheme, in the product spelling

Let `g : S' ⟶ S` be a universal homeomorphism and let `V` be a scheme étale over `S'`. Stacks
Project, Tag 0BTY produces a canonical descent datum on `V` relative to `S'/S`. This file
constructs it in the form asked for by `AlgebraicGeometry.DescentData`, and hence by the étale
descent data of Tag 0BTZ: the gluing isomorphism is an isomorphism over the product `A ⨯ A`
taken in the category `CategoryTheory.Over S`, where `A = Over.mk g`.

## Main definitions

* `CategoryTheory.Limits.prodTripleDiag` is the diagonal `A ⟶ (A ⨯ A) ⨯ A` of the
  left-associated triple product.
* `Stacks.Etale.prodGluing` is the gluing isomorphism of the canonical descent datum, as an
  isomorphism over `A ⨯ A`.
* `Stacks.Etale.canonicalEtaleDescentDatum` is the étale descent datum carried by a scheme
  étale over `S'`.
* `Stacks.Etale.etaleDescentDataSection` assembles those data into a functor, a section of
  `AlgebraicGeometry.etaleDescentDataForget`.

## Main results

* `CategoryTheory.Limits.isPullback_prodMap_id_left`,
  `CategoryTheory.Limits.isPullback_prodLift_left`,
  `CategoryTheory.Limits.isPullback_prodLift_right` and
  `CategoryTheory.Limits.isPullback_prodLift_triple` exhibit the maps of a product and the
  evident sections as base changes, in an arbitrary category with binary products.
* `Stacks.Etale.universalHomeomorphism_diag_left` and
  `Stacks.Etale.universalHomeomorphism_prodTripleDiag_left`: the diagonal and the triple
  diagonal of an object of `Over S` whose structure morphism is a universal homeomorphism are
  universal homeomorphisms.
* `Stacks.Etale.existsUnique_hom_over`: Tag 025H for morphisms over an object of `Over S`.
* `Stacks.Etale.hom_ext_over_of_restrict`: its uniqueness half, which needs only surjectivity.
* `Stacks.Etale.existsUnique_prodGluingHom` and `Stacks.Etale.isIso_prodGluingHom`: the gluing
  map of the canonical descent datum exists, is unique and is an isomorphism.
* `Stacks.Etale.hom_ext_prodTriple`: the uniqueness statement over the triple product.
* `Stacks.Etale.prodGluing_cocycle`: the cocycle condition of the canonical descent datum.
* `Stacks.Etale.prodGluing_naturality`: the gluing maps are natural.
* `Stacks.Etale.etaleDescentDataSectionForgetIso`: the composite of the section with the
  forgetful functor is the identity.
* `Stacks.Etale.exists_pullback_iso_of_essImage_etaleDescentFunctor` and
  `Stacks.Etale.etalePullback_isEquivalence_of_forall_essImage`: the essential-surjectivity half
  of Stacks Project, Tag 04DZ, and hence Tag 04DZ itself, follows from effectivity of these
  canonical descent data.

## Implementation notes

The restriction of a morphism over `T` along a morphism `d : A' ⟶ T` is taken to be
precomposition with a base change of `d`; the base change is supplied by the caller as a
morphism with the two required topological properties, rather than formed inside the statements,
so that the concrete sections `prod.lift (𝟙 W) h` and `prod.lift (prod.lift (𝟙 W) h) h` can be
used directly instead of a chosen fibre product.

## References

* [Stacks Project, Tag 025H](https://stacks.math.columbia.edu/tag/025H)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0BTZ](https://stacks.math.columbia.edu/tag/0BTZ)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

namespace CategoryTheory.Limits

open CategoryTheory

variable {C : Type*} [Category C] [HasBinaryProducts C]

/-- The map `prod.map (𝟙 X) h` is the base change of `h` along the second projection. This is
the mirror image of `CategoryTheory.IsPullback.of_prod_fst_with_id`. -/
@[ega "I 3.3.2" "partial"]
lemma isPullback_prodMap_id_left {A B : C} (h : A ⟶ B) (X : C) :
    IsPullback (prod.snd (X := X) (Y := A)) (prod.map (𝟙 X) h) h prod.snd := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro T φ φ' h₁ h₂
    refine prod.hom_ext ?_ (by simpa using h₁)
    simpa using congrArg (fun t => t ≫ prod.fst) h₂
  · intro T a b hab
    refine ⟨prod.lift (b ≫ prod.fst) a, by simp, ?_⟩
    exact prod.hom_ext (by simp) (by simp [← hab])

/-- The section `w ↦ (w, h w)` of the first projection of `W ⨯ A` is the base change of the
diagonal of `A` along `prod.map h (𝟙 A)`. -/
@[ega "IV 14.5.11.1" "special case"]
lemma isPullback_prodLift_left {W A : C} (h : W ⟶ A) :
    IsPullback (prod.lift (𝟙 W) h) h (prod.map h (𝟙 A)) (diag A) := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro T φ φ' h₁ _
    simpa using congrArg (fun t => t ≫ prod.fst) h₁
  · intro T a b hab
    have hfst : (a ≫ prod.fst) ≫ h = b := by
      simpa using congrArg (fun t => t ≫ prod.fst) hab
    have hsnd : a ≫ prod.snd = b := by
      simpa using congrArg (fun t => t ≫ prod.snd) hab
    exact ⟨a ≫ prod.fst, prod.hom_ext (by simp) (by simp [hfst, hsnd]), by simp [hfst]⟩

/-- The section `w ↦ (h w, w)` of the second projection of `A ⨯ W` is the base change of the
diagonal of `A` along `prod.map (𝟙 A) h`. -/
@[ega "IV 14.5.11.1" "special case"]
lemma isPullback_prodLift_right {W A : C} (h : W ⟶ A) :
    IsPullback (prod.lift h (𝟙 W)) h (prod.map (𝟙 A) h) (diag A) := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro T φ φ' h₁ _
    simpa using congrArg (fun t => t ≫ prod.snd) h₁
  · intro T a b hab
    have hfst : a ≫ prod.fst = b := by
      simpa using congrArg (fun t => t ≫ prod.fst) hab
    have hsnd : (a ≫ prod.snd) ≫ h = b := by
      simpa using congrArg (fun t => t ≫ prod.snd) hab
    exact ⟨a ≫ prod.snd, prod.hom_ext (by simp [hfst, hsnd]) (by simp), by simp [hsnd]⟩

/-- The diagonal of the left-associated triple product. -/
noncomputable abbrev prodTripleDiag (A : C) : A ⟶ (A ⨯ A) ⨯ A :=
  prod.lift (diag A) (𝟙 A)

/-- The triple diagonal is the diagonal followed by the diagonal in the first two factors. -/
lemma prodTripleDiag_eq_diag_comp (A : C) :
    prodTripleDiag A = diag A ≫ prod.map (diag A) (𝟙 A) := by
  simp [prodTripleDiag]

/-- The section `w ↦ ((w, h w), h w)` of `(W ⨯ A) ⨯ A` is the base change of the triple
diagonal of `A` along `prod.map (prod.map h (𝟙 A)) (𝟙 A)`. -/
@[ega "IV 14.5.11.1" "special case"]
lemma isPullback_prodLift_triple {W A : C} (h : W ⟶ A) :
    IsPullback (prod.lift (prod.lift (𝟙 W) h) h) h
      (prod.map (prod.map h (𝟙 A)) (𝟙 A)) (prodTripleDiag A) := by
  refine IsPullback.mk' (by simp [prodTripleDiag]) ?_ ?_
  · intro T φ φ' h₁ _
    simpa using congrArg (fun t => t ≫ prod.fst ≫ prod.fst) h₁
  · intro T a b hab
    have hfst : a ≫ prod.fst ≫ prod.fst ≫ h = b := by
      simpa using congrArg (fun t => t ≫ prod.fst ≫ prod.fst) hab
    have hmid : a ≫ prod.fst ≫ prod.snd = b := by
      simpa using congrArg (fun t => t ≫ prod.fst ≫ prod.snd) hab
    have hsnd : a ≫ prod.snd = b := by
      simpa using congrArg (fun t => t ≫ prod.snd) hab
    refine ⟨a ≫ prod.fst ≫ prod.fst, prod.hom_ext ?_ (by simp [hfst, hsnd]), by simp [hfst]⟩
    exact prod.hom_ext (by simp) (by simp [hfst, hmid])

section Components

variable {A B C₀ D E : C} (ψ : B ⨯ C₀ ⟶ D ⨯ E)

/-- The first factor of a left-associated triple product is untouched by
`CategoryTheory.Limits.prodMapLastTwo`. -/
@[reassoc (attr := simp)]
lemma prodMapLastTwo_fst_fst :
    prodMapLastTwo (A := A) ψ ≫ prod.fst ≫ prod.fst = prod.fst ≫ prod.fst := by
  simp [prodMapLastTwo]

/-- The second factor of the target of `CategoryTheory.Limits.prodMapLastTwo` is the first
factor of the target of `ψ`. -/
@[reassoc (attr := simp)]
lemma prodMapLastTwo_fst_snd :
    prodMapLastTwo (A := A) ψ ≫ prod.fst ≫ prod.snd =
      (prod.lift (prod.fst ≫ prod.snd) prod.snd : (A ⨯ B) ⨯ C₀ ⟶ B ⨯ C₀) ≫ ψ ≫ prod.fst := by
  simp [prodMapLastTwo]

/-- The third factor of the target of `CategoryTheory.Limits.prodMapLastTwo` is the second
factor of the target of `ψ`. -/
@[reassoc (attr := simp)]
lemma prodMapLastTwo_snd :
    prodMapLastTwo (A := A) ψ ≫ prod.snd =
      (prod.lift (prod.fst ≫ prod.snd) prod.snd : (A ⨯ B) ⨯ C₀ ⟶ B ⨯ C₀) ≫ ψ ≫ prod.snd := by
  simp [prodMapLastTwo]

variable (χ : A ⨯ C₀ ⟶ D ⨯ E)

/-- The first factor of the target of `CategoryTheory.Limits.prodMapFirstThird` is the first
factor of the target of `χ`. -/
@[reassoc (attr := simp)]
lemma prodMapFirstThird_fst_fst :
    prodMapFirstThird (B := B) χ ≫ prod.fst ≫ prod.fst =
      (prod.lift (prod.fst ≫ prod.fst) prod.snd : (A ⨯ B) ⨯ C₀ ⟶ A ⨯ C₀) ≫ χ ≫ prod.fst := by
  simp [prodMapFirstThird, prodMapLastTwo]

/-- The middle factor is untouched by `CategoryTheory.Limits.prodMapFirstThird`. -/
@[reassoc (attr := simp)]
lemma prodMapFirstThird_fst_snd :
    prodMapFirstThird (B := B) χ ≫ prod.fst ≫ prod.snd = prod.fst ≫ prod.snd := by
  simp [prodMapFirstThird, prodMapLastTwo]

/-- The third factor of the target of `CategoryTheory.Limits.prodMapFirstThird` is the second
factor of the target of `χ`. -/
@[reassoc (attr := simp)]
lemma prodMapFirstThird_snd :
    prodMapFirstThird (B := B) χ ≫ prod.snd =
      (prod.lift (prod.fst ≫ prod.fst) prod.snd : (A ⨯ B) ⨯ C₀ ⟶ A ⨯ C₀) ≫ χ ≫ prod.snd := by
  simp [prodMapFirstThird, prodMapLastTwo]

end Components

end CategoryTheory.Limits

namespace Stacks.Etale

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {S : Scheme.{u}}

section Transport

variable (P : MorphismProperty Scheme.{u})

/-- A morphism property stable under base change passes from `h` to `prod.map h (𝟙 X)`, the
products being taken in `Over S`. -/
lemma prodMap_id_right_left_mem [P.IsStableUnderBaseChange] {A B : Over S} (h : A ⟶ B)
    (hP : P h.left) (X : Over S) : P (prod.map h (𝟙 X)).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((IsPullback.of_prod_fst_with_id h X).map (Over.forget S)) hP

/-- A morphism property stable under base change passes from `h` to `prod.map (𝟙 X) h`, the
products being taken in `Over S`. -/
lemma prodMap_id_left_left_mem [P.IsStableUnderBaseChange] {A B : Over S} (h : A ⟶ B)
    (hP : P h.left) (X : Over S) : P (prod.map (𝟙 X) h).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((isPullback_prodMap_id_left h X).map (Over.forget S)) hP

/-- A morphism property stable under base change passes from the diagonal of `A` to the
section `prod.lift (𝟙 W) h` of the first projection of `W ⨯ A`. -/
lemma prodLift_left_mem [P.IsStableUnderBaseChange] {W A : Over S} (h : W ⟶ A)
    (hP : P (diag A).left) : P (prod.lift (𝟙 W) h).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((isPullback_prodLift_left h).flip.map (Over.forget S)) hP

/-- A morphism property stable under base change passes from the diagonal of `A` to the
section `prod.lift h (𝟙 W)` of the second projection of `A ⨯ W`. -/
lemma prodLift_right_mem [P.IsStableUnderBaseChange] {W A : Over S} (h : W ⟶ A)
    (hP : P (diag A).left) : P (prod.lift h (𝟙 W)).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((isPullback_prodLift_right h).flip.map (Over.forget S)) hP

/-- A morphism property stable under base change passes from the triple diagonal of `A` to the
section `prod.lift (prod.lift (𝟙 W) h) h` of `(W ⨯ A) ⨯ A`. -/
lemma prodLift_triple_mem [P.IsStableUnderBaseChange] {W A : Over S} (h : W ⟶ A)
    (hP : P (prodTripleDiag A).left) : P (prod.lift (prod.lift (𝟙 W) h) h).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((isPullback_prodLift_triple h).flip.map (Over.forget S)) hP

/-- The diagonal of an object of `Over S`, read as a morphism of schemes, is the diagonal of its
structure morphism. -/
lemma diag_left_comp_prodLeftIsoPullback (A : Over S) :
    (diag A).left ≫ (Over.prodLeftIsoPullback A A).hom = pullback.diagonal A.hom := by
  apply pullback.hom_ext <;> simp [← Over.comp_left]

/-- A morphism property of the diagonal of `A.hom` transfers to the diagonal of `A` in
`Over S`. -/
lemma diag_left_mem [P.RespectsIso] (A : Over S) (hP : P (pullback.diagonal A.hom)) :
    P (diag A).left := by
  rw [← MorphismProperty.cancel_right_of_respectsIso P _ (Over.prodLeftIsoPullback A A).hom,
    diag_left_comp_prodLeftIsoPullback]
  exact hP

end Transport

section Diagonals

variable (A : Over S) [UniversalHomeomorphism A.hom]

/-- The diagonal of an object of `Over S` whose structure morphism is a universal homeomorphism
is itself a universal homeomorphism. -/
theorem universalHomeomorphism_diag_left : UniversalHomeomorphism (diag A).left :=
  diag_left_mem _ A (universalHomeomorphism_diagonal A.hom)

/-- A morphism property stable under base change and composition passes from the diagonal of `A`
to the triple diagonal of `A`. -/
private theorem prodTripleDiag_left_mem (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] (A : Over S) (hP : P (diag A).left) :
    P (prodTripleDiag A).left := by
  rw [prodTripleDiag_eq_diag_comp, Over.comp_left]
  exact MorphismProperty.comp_mem _ _ _ hP (prodMap_id_right_left_mem P (diag A) hP A)

/-- The triple diagonal of an object of `Over S` whose structure morphism is a universal
homeomorphism is a universal homeomorphism. -/
theorem universalHomeomorphism_prodTripleDiag_left :
    UniversalHomeomorphism (prodTripleDiag A).left :=
  have : MorphismProperty.IsStableUnderComposition (@UniversalHomeomorphism.{u}) :=
    universalHomeomorphism_hasTwoOutOfThreeProperty.toIsStableUnderComposition
  prodTripleDiag_left_mem _ A (universalHomeomorphism_diag_left A)

/-- The diagonal of an object of `Over S` whose structure morphism is a universal homeomorphism
is a closed immersion. -/
theorem isClosedImmersion_diag_left : IsClosedImmersion (diag A).left :=
  diag_left_mem _ A (isClosedImmersion_diagonal_of_universalHomeomorphism A.hom)

/-- The triple diagonal of an object of `Over S` whose structure morphism is a universal
homeomorphism is a closed immersion. -/
theorem isClosedImmersion_prodTripleDiag_left :
    IsClosedImmersion (prodTripleDiag A).left :=
  have : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{u}) :=
    ⟨fun _ _ _ _ => inferInstance⟩
  prodTripleDiag_left_mem (@IsClosedImmersion) A (isClosedImmersion_diag_left A)

/-- The diagonal of an object of `Over S` whose structure morphism is a universal homeomorphism
is surjective on points. -/
theorem surjective_diag_left : Surjective (diag A).left :=
  have := universalHomeomorphism_diag_left A
  surjective_of_universalHomeomorphism (diag A).left

/-- The triple diagonal of an object of `Over S` whose structure morphism is a universal
homeomorphism is surjective on points. -/
theorem surjective_prodTripleDiag_left : Surjective (prodTripleDiag A).left :=
  have := universalHomeomorphism_prodTripleDiag_left A
  surjective_of_universalHomeomorphism (prodTripleDiag A).left

end Diagonals

section Relative

variable {T X Y Z : Over S}

/-- **Uniqueness of a morphism over `T` through a surjection.** Two morphisms over `T` into an
object whose structure morphism to `T` is étale which agree after precomposition with a morphism
that is surjective on points are equal. -/
theorem hom_ext_over_of_restrict (p : X ⟶ T) [Etale p.left] (j : Z ⟶ Y)
    (hj : Function.Surjective j.left.base) (φ ψ : Y ⟶ X) (hpq : φ ≫ p = ψ ≫ p)
    (hres : j ≫ φ = j ≫ ψ) : φ = ψ := by
  apply Over.OverMorphism.ext
  refine hom_ext_of_surjective j.left hj p.left φ.left ψ.left ?_ ?_
  · rw [← Over.comp_left, ← Over.comp_left, hpq]
  · rw [← Over.comp_left, ← Over.comp_left, hres]

/-- **Stacks Project, Tag 025H over a base object.** Let `T` be an object of `Over S` and let
`p : X ⟶ T` have étale underlying morphism. A morphism `Y ⟶ X` over `T` is uniquely determined
by its restriction along a thickening `j : Z ⟶ Y`, and every morphism `u : Z ⟶ X` over `T`
arises as such a restriction. -/
theorem existsUnique_hom_over (p : X ⟶ T) [Etale p.left] (q : Y ⟶ T) (j : Z ⟶ Y)
    (hj : IsClosedImmersion j.left) (hjs : Function.Surjective j.left.base) (u : Z ⟶ X)
    (hu : u ≫ p = j ≫ q) :
    ∃! φ : Y ⟶ X, φ ≫ p = q ∧ j ≫ φ = u := by
  have hu' : j.left ≫ q.left = u.left ≫ p.left := by
    rw [← Over.comp_left, ← Over.comp_left, hu]
  obtain ⟨f, hfq, hfj⟩ :=
    exists_lift_of_surjective_closedImmersion p.left q.left j.left hjs u.left hu'
  have hfw : f ≫ X.hom = Y.hom := by
    rw [← Over.w p, ← Category.assoc, hfq, Over.w q]
  refine ⟨Over.homMk f hfw, ⟨Over.OverMorphism.ext (by simpa using hfq),
    Over.OverMorphism.ext (by simpa using hfj)⟩, ?_⟩
  rintro φ ⟨hφp, hφj⟩
  refine hom_ext_over_of_restrict p j hjs φ (Over.homMk f hfw) ?_ ?_
  · rw [hφp]
    exact (Over.OverMorphism.ext (by simpa using hfq)).symm
  · rw [hφj]
    exact (Over.OverMorphism.ext (by simpa using hfj)).symm

/-- Two morphisms `φ : X ⟶ Y` and `ψ : Y ⟶ X` over `T` that are inverse to each other after
restriction along a surjection `j : Z ⟶ X` have `φ ≫ ψ = 𝟙 X` when `X ⟶ T` is étale. -/
private theorem comp_eq_id_of_restrict (p : X ⟶ T) [Etale p.left] (q : Y ⟶ T) (j : Z ⟶ X)
    (j' : Z ⟶ Y) (hj : Function.Surjective j.left.base) (φ : X ⟶ Y) (ψ : Y ⟶ X)
    (hφ : φ ≫ q = p) (hψ : ψ ≫ p = q) (hjφ : j ≫ φ = j') (hjψ : j' ≫ ψ = j) : φ ≫ ψ = 𝟙 X :=
  hom_ext_over_of_restrict p j hj _ _ (by rw [Category.assoc, hψ, hφ, Category.id_comp])
    (by rw [← Category.assoc, hjφ, hjψ, Category.comp_id])

end Relative

section Gluing

variable (A : Over S) [UniversalHomeomorphism A.hom] {W : Over S} (h : W ⟶ A) [Etale h.left]

/-- **The gluing map of the canonical descent datum, in the product spelling.** Let `A` be an
object of `Over S` whose structure morphism is a universal homeomorphism and let `h : W ⟶ A`
have étale underlying morphism. There is a unique morphism `W ⨯ A ⟶ A ⨯ W` over `A ⨯ A` whose
restriction along the diagonal of `A` is the identity of `W`, the two restrictions being
identified with `W` by the sections `prod.lift (𝟙 W) h` and `prod.lift h (𝟙 W)`. -/
theorem existsUnique_prodGluingHom :
    ∃! φ : W ⨯ A ⟶ A ⨯ W,
      φ ≫ prod.map (𝟙 A) h = prod.map h (𝟙 A) ∧
        prod.lift (𝟙 W) h ≫ φ = prod.lift h (𝟙 W) := by
  have hp : Etale (prod.map (𝟙 A) h).left :=
    prodMap_id_left_left_mem (P := @Etale) h inferInstance A
  have hci : IsClosedImmersion (prod.lift (𝟙 W) h).left :=
    prodLift_left_mem _ h (isClosedImmersion_diag_left A)
  have hsj : Surjective (prod.lift (𝟙 W) h).left :=
    prodLift_left_mem _ h (surjective_diag_left A)
  exact existsUnique_hom_over (prod.map (𝟙 A) h) (prod.map h (𝟙 A)) (prod.lift (𝟙 W) h) hci
    hsj.surj (prod.lift h (𝟙 W)) (by simp)

/-- The mirror image of `Stacks.Etale.existsUnique_prodGluingHom`: there is a unique morphism
`A ⨯ W ⟶ W ⨯ A` over `A ⨯ A` whose restriction along the diagonal of `A` is the identity of
`W`. -/
theorem existsUnique_prodGluingHom' :
    ∃! ψ : A ⨯ W ⟶ W ⨯ A,
      ψ ≫ prod.map h (𝟙 A) = prod.map (𝟙 A) h ∧
        prod.lift h (𝟙 W) ≫ ψ = prod.lift (𝟙 W) h := by
  have hp : Etale (prod.map h (𝟙 A)).left :=
    prodMap_id_right_left_mem (P := @Etale) h inferInstance A
  have hci : IsClosedImmersion (prod.lift h (𝟙 W)).left :=
    prodLift_right_mem _ h (isClosedImmersion_diag_left A)
  have hsj : Surjective (prod.lift h (𝟙 W)).left :=
    prodLift_right_mem _ h (surjective_diag_left A)
  exact existsUnique_hom_over (prod.map h (𝟙 A)) (prod.map (𝟙 A) h) (prod.lift h (𝟙 W)) hci
    hsj.surj (prod.lift (𝟙 W) h) (by simp)

/-- The gluing map of the canonical descent datum is an isomorphism: a morphism
`W ⨯ A ⟶ A ⨯ W` over `A ⨯ A` whose restriction along the diagonal of `A` is the identity of `W`
is an isomorphism. -/
theorem isIso_prodGluingHom (φ : W ⨯ A ⟶ A ⨯ W)
    (hφ : φ ≫ prod.map (𝟙 A) h = prod.map h (𝟙 A))
    (hφd : prod.lift (𝟙 W) h ≫ φ = prod.lift h (𝟙 W)) : IsIso φ := by
  obtain ⟨ψ, ⟨hψ, hψd⟩, -⟩ := existsUnique_prodGluingHom' A h
  have hpr : Etale (prod.map h (𝟙 A)).left :=
    prodMap_id_right_left_mem (P := @Etale) h inferInstance A
  have hpl : Etale (prod.map (𝟙 A) h).left :=
    prodMap_id_left_left_mem (P := @Etale) h inferInstance A
  exact ⟨ψ, comp_eq_id_of_restrict _ _ _ _
      (prodLift_left_mem _ h (surjective_diag_left A)).surj _ _ hφ hψ hφd hψd,
    comp_eq_id_of_restrict _ _ _ _
      (prodLift_right_mem _ h (surjective_diag_left A)).surj _ _ hψ hφ hψd hφd⟩

/-- **The gluing isomorphism of the canonical descent datum, over `A ⨯ A`.** -/
noncomputable def prodGluing :
    Over.mk (prod.map h (𝟙 A)) ≅ Over.mk (prod.map (𝟙 A) h) :=
  have hφ := (existsUnique_prodGluingHom A h).choose_spec.1
  have : IsIso (existsUnique_prodGluingHom A h).choose := isIso_prodGluingHom A h _ hφ.1 hφ.2
  Over.isoMk (asIso (existsUnique_prodGluingHom A h).choose) (by simpa using hφ.1)

/-- The underlying morphism of `Stacks.Etale.prodGluing` lies over `A ⨯ A`. -/
lemma prodGluing_hom_left_comp :
    (prodGluing A h).hom.left ≫ prod.map (𝟙 A) h = prod.map h (𝟙 A) :=
  (existsUnique_prodGluingHom A h).choose_spec.1.1

/-- The underlying morphism of `Stacks.Etale.prodGluing` restricts along the diagonal of `A` to
the identity of `W`. -/
lemma prodGluing_hom_left_restrict :
    prod.lift (𝟙 W) h ≫ (prodGluing A h).hom.left = prod.lift h (𝟙 W) :=
  (existsUnique_prodGluingHom A h).choose_spec.1.2

end Gluing

section Cocycle

variable (A : Over S) [UniversalHomeomorphism A.hom] {W : Over S} (h : W ⟶ A) [Etale h.left]

/-- Two morphisms `(W ⨯ A) ⨯ A ⟶ (A ⨯ A) ⨯ W` over the triple product `(A ⨯ A) ⨯ A` which
agree after restriction along the triple diagonal of `A` are equal. -/
theorem hom_ext_prodTriple (φ ψ : (W ⨯ A) ⨯ A ⟶ (A ⨯ A) ⨯ W)
    (hφ : φ ≫ prod.map (𝟙 (A ⨯ A)) h = prod.map (prod.map h (𝟙 A)) (𝟙 A))
    (hψ : ψ ≫ prod.map (𝟙 (A ⨯ A)) h = prod.map (prod.map h (𝟙 A)) (𝟙 A))
    (hres : prod.lift (prod.lift (𝟙 W) h) h ≫ φ = prod.lift (prod.lift (𝟙 W) h) h ≫ ψ) :
    φ = ψ := by
  have hp : Etale (prod.map (𝟙 (A ⨯ A)) h).left :=
    prodMap_id_left_left_mem (P := @Etale) h inferInstance (A ⨯ A)
  have hs : Surjective (prod.lift (prod.lift (𝟙 W) h) h).left :=
    prodLift_triple_mem _ h (surjective_prodTripleDiag_left A)
  exact hom_ext_over_of_restrict (prod.map (𝟙 (A ⨯ A)) h)
    (prod.lift (prod.lift (𝟙 W) h) h) hs.surj φ ψ (hφ.trans hψ.symm) hres

/-- The gluing map preserves the first factor of `A ⨯ A`. -/
@[reassoc (attr := simp)]
lemma prodGluing_hom_left_fst :
    (prodGluing A h).hom.left ≫ prod.fst = prod.fst ≫ h := by
  simpa using congrArg (fun t => t ≫ prod.fst) (prodGluing_hom_left_comp A h)

/-- The gluing map preserves the second factor of `A ⨯ A`. -/
@[reassoc (attr := simp)]
lemma prodGluing_hom_left_snd :
    (prodGluing A h).hom.left ≫ prod.snd ≫ h = prod.snd := by
  simpa using congrArg (fun t => t ≫ prod.snd) (prodGluing_hom_left_comp A h)

/-- The restriction of the gluing map along the diagonal is the identity, read in the second
factor. -/
@[reassoc (attr := simp)]
lemma prodGluing_hom_left_restrict_snd :
    prod.lift (𝟙 W) h ≫ (prodGluing A h).hom.left ≫ prod.snd = 𝟙 W := by
  simpa using congrArg (fun t => t ≫ prod.snd) (prodGluing_hom_left_restrict A h)

/-- One way around the cocycle triangle lies over the triple product. -/
lemma prodMapLastTwo_prodGluing_over :
    (prod.map (prodGluing A h).hom.left (𝟙 A) ≫
        prodMapLastTwo (prodGluing A h).hom.left) ≫ prod.map (𝟙 (A ⨯ A)) h =
      prod.map (prod.map h (𝟙 A)) (𝟙 A) := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;> simp [prod.comp_lift]

/-- The other way around the cocycle triangle lies over the triple product. -/
lemma prodMapFirstThird_prodGluing_over :
    prodMapFirstThird (prodGluing A h).hom.left ≫ prod.map (𝟙 (A ⨯ A)) h =
      prod.map (prod.map h (𝟙 A)) (𝟙 A) := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;> simp [prod.comp_lift]

/-- The restriction of one way around the cocycle triangle along the triple diagonal. -/
lemma prodMapLastTwo_prodGluing_restrict :
    prod.lift (prod.lift (𝟙 W) h) h ≫ prod.map (prodGluing A h).hom.left (𝟙 A) ≫
        prodMapLastTwo (prodGluing A h).hom.left =
      prod.lift (prod.lift h h) (𝟙 W) := by
  have hstep : prod.lift (prod.lift (𝟙 W) h) h ≫
      prod.map (prodGluing A h).hom.left (𝟙 A) = prod.lift (prod.lift h (𝟙 W)) h := by
    refine prod.hom_ext ?_ (by simp)
    simpa using prodGluing_hom_left_restrict A h
  rw [← Category.assoc, hstep]
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;> simp only [← Category.assoc] <;>
    simp [prod.comp_lift]

/-- The restriction of the other way around the cocycle triangle along the triple diagonal. -/
lemma prodMapFirstThird_prodGluing_restrict :
    prod.lift (prod.lift (𝟙 W) h) h ≫ prodMapFirstThird (prodGluing A h).hom.left =
      prod.lift (prod.lift h h) (𝟙 W) := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;> simp only [← Category.assoc] <;>
    simp [prod.comp_lift]

/-- **The cocycle condition for the canonical descent datum.** The two ways around the triangle
over the triple product `(A ⨯ A) ⨯ A` agree. -/
theorem prodGluing_cocycle :
    prod.map (prodGluing A h).hom.left (𝟙 A) ≫
        prodMapLastTwo (prodGluing A h).hom.left =
      prodMapFirstThird (prodGluing A h).hom.left :=
  hom_ext_prodTriple A h _ _ (prodMapLastTwo_prodGluing_over A h)
    (prodMapFirstThird_prodGluing_over A h)
    ((prodMapLastTwo_prodGluing_restrict A h).trans
      (prodMapFirstThird_prodGluing_restrict A h).symm)

/-- **Naturality of the gluing map.** A morphism `m : W ⟶ W'` over `A` commutes with the
gluing maps of its source and target. -/
theorem prodGluing_naturality {W' : Over S} (h' : W' ⟶ A) [Etale h'.left] (m : W ⟶ W')
    (hm : m ≫ h' = h) :
    prod.map m (𝟙 A) ≫ (prodGluing A h').hom.left =
      (prodGluing A h).hom.left ≫ prod.map (𝟙 A) m := by
  have hp : Etale (prod.map (𝟙 A) h').left :=
    prodMap_id_left_left_mem (P := @Etale) h' inferInstance A
  have hs : Surjective (prod.lift (𝟙 W) h).left :=
    prodLift_left_mem _ h (surjective_diag_left A)
  refine hom_ext_over_of_restrict (prod.map (𝟙 A) h') (prod.lift (𝟙 W) h) hs.surj _ _ ?_ ?_
  · have e₁ : prod.map m (𝟙 A) ≫ (prodGluing A h').hom.left ≫ prod.map (𝟙 A) h' =
        prod.map h (𝟙 A) := by
      rw [prodGluing_hom_left_comp, prod.map_map, Category.comp_id, hm]
    have e₂ : (prodGluing A h).hom.left ≫ prod.map (𝟙 A) m ≫ prod.map (𝟙 A) h' =
        prod.map h (𝟙 A) := by
      rw [prod.map_map, Category.id_comp, hm, prodGluing_hom_left_comp]
    simp only [Category.assoc]
    rw [e₁, e₂]
  · have hmj : prod.lift (𝟙 W) h ≫ prod.map m (𝟙 A) = m ≫ prod.lift (𝟙 W') h' := by
      refine prod.hom_ext (by simp) ?_
      simp [hm]
    rw [← Category.assoc, hmj, Category.assoc, prodGluing_hom_left_restrict,
      ← Category.assoc, prodGluing_hom_left_restrict]
    refine prod.hom_ext ?_ (by simp)
    simp [hm]

end Cocycle

section Datum

variable {S S' : Scheme.{u}} (g : S' ⟶ S) [UniversalHomeomorphism g]

/-- An `S`-scheme of the form `Over.mk g` has `g` as its structure morphism, so it inherits the
hypothesis on `g`. -/
instance universalHomeomorphism_overMk_hom :
    UniversalHomeomorphism (Over.mk g).hom :=
  inferInstanceAs (UniversalHomeomorphism g)

/-- An `S'`-scheme of the form `Over.mk p` is étale when `p` is. -/
instance etale_overMk_hom {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p] :
    Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)

/-- The structure morphism of an étale `S'`-scheme, read as a morphism over `Over.mk g`, is
étale. -/
instance etale_structureMap_left (V : Over S') [Etale V.hom] :
    Etale (AlgebraicGeometry.structureMap g V).left :=
  inferInstanceAs (Etale V.hom)

/-- **The canonical étale descent datum of Stacks Project, Tag 0BTY.** A scheme `V` étale over
`S'` carries a descent datum relative to the universal homeomorphism `g : S' ⟶ S`, whose
underlying `S'`-scheme is `V` itself: the gluing isomorphism is `Stacks.Etale.prodGluing` and
the cocycle condition is `Stacks.Etale.prodGluing_cocycle`. -/
noncomputable def canonicalEtaleDescentDatum (V : Over S') [Etale V.hom] :
    AlgebraicGeometry.EtaleDescentData g where
  obj :=
    { obj _ := V
      gluing _ _ := prodGluing (Over.mk g) (AlgebraicGeometry.structureMap g V)
      cocycle _ _ _ := prodGluing_cocycle (Over.mk g) (AlgebraicGeometry.structureMap g V) }
  property := inferInstanceAs (Etale V.hom)

/-- The canonical descent datum of `V` has `V` as its underlying `S'`-scheme. -/
@[simp]
lemma canonicalEtaleDescentDatum_obj_obj (V : Over S') [Etale V.hom] :
    (canonicalEtaleDescentDatum g V).obj.obj () = V :=
  rfl

/-- **A section of the forgetful functor of Stacks Project, Tag 0BTZ.** Every scheme étale over
`S'` is the underlying scheme of an étale descent datum relative to `g`, functorially. -/
noncomputable def etaleDescentDataSection :
    AlgebraicGeometry.EtaleOver S' ⥤ AlgebraicGeometry.EtaleDescentData g where
  obj V :=
    letI : Etale V.obj.hom := V.property
    canonicalEtaleDescentDatum g V.obj
  map {V V'} u :=
    letI : Etale V.obj.hom := V.property
    letI : Etale V'.obj.hom := V'.property
    ObjectProperty.homMk
      { hom _ := u.hom
        comm _ _ := prodGluing_naturality (Over.mk g) (AlgebraicGeometry.structureMap g V.obj)
          (AlgebraicGeometry.structureMap g V'.obj) ((Over.map g).map u.hom)
          (by apply Over.OverMorphism.ext; simp) }
  map_id V := by
    apply ObjectProperty.hom_ext
    exact AlgebraicGeometry.DescentData.hom_ext fun _ => rfl
  map_comp u v := by
    apply ObjectProperty.hom_ext
    exact AlgebraicGeometry.DescentData.hom_ext fun _ => rfl

/-- Forgetting the descent datum `(Stacks.Etale.etaleDescentDataSection g).obj V` recovers
`V`. -/
@[simp]
lemma etaleDescentDataForget_obj_etaleDescentDataSection
    (V : AlgebraicGeometry.EtaleOver S') :
    (AlgebraicGeometry.etaleDescentDataForget g).obj ((etaleDescentDataSection g).obj V) = V :=
  rfl

/-- The natural isomorphism exhibiting `Stacks.Etale.etaleDescentDataSection` as a section. -/
noncomputable def etaleDescentDataSectionForgetIso :
    etaleDescentDataSection g ⋙ AlgebraicGeometry.etaleDescentDataForget g ≅
      CategoryTheory.Functor.id (AlgebraicGeometry.EtaleOver S') :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro V V' u; rfl)

/-- **Essential surjectivity of étale pullback, reduced to effectivity.** If the canonical
descent datum of a scheme `U` étale over `S'` lies in the essential image of
`AlgebraicGeometry.etaleDescentFunctor`, then `U` is, over `S'`, the base change along `g` of a
scheme étale over `S`. -/
theorem exists_pullback_iso_of_essImage_etaleDescentFunctor (U : Over S') [Etale U.hom]
    (hE : (AlgebraicGeometry.etaleDescentFunctor g).essImage
      (canonicalEtaleDescentDatum g U)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ S) (_ : Etale q) (e : Limits.pullback q g ≅ U.left),
      e.hom ≫ U.hom = Limits.pullback.snd q g := by
  obtain ⟨V₀, ⟨eD⟩⟩ := hE
  let W₀ : Over S := (Scheme.Etale.forget S).obj V₀
  let P := AlgebraicGeometry.DescentData.pullbackFunctor (𝟙 S) g (𝟙 S) g (by simp)
  let D₀ := (AlgebraicGeometry.DescentData.trivialFunctor S).obj W₀
  let e₁ := ((AlgebraicGeometry.IsEtaleDescentData g).ι).mapIso eD
  let e₂ := (AlgebraicGeometry.DescentData.evaluation ()).mapIso e₁
  have e₃ : (Over.pullback g).obj W₀ ≅ U :=
    (P.objIso D₀).symm ≪≫ (e₂ : (P.functor.obj D₀).obj () ≅ U)
  exact ⟨W₀.left, W₀.hom, V₀.prop, (Over.forget S').mapIso e₃, Over.w e₃.hom⟩

/-- **Stacks Project, Tag 04DZ, reduced to effectivity of étale descent.** If every scheme étale
over `S'` has an effective canonical descent datum relative to the universal homeomorphism
`g : S' ⟶ S` — that is, if the canonical descent datum lies in the essential image of
`AlgebraicGeometry.etaleDescentFunctor` — then base change along `g` is an equivalence of small
étale sites. -/
theorem etalePullback_isEquivalence_of_forall_essImage
    (H : ∀ (U : Scheme.{u}) (p : U ⟶ S') (_ : Etale p),
      (AlgebraicGeometry.etaleDescentFunctor g).essImage
        (canonicalEtaleDescentDatum g (Over.mk p))) :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) g := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) g :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show S.Etale ⥤ S'.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ g).IsEquivalence :=
  etalePullback_isEquivalence_of_forall_exists_pullback_iso g fun U p hp =>
    have := hp
    exists_pullback_iso_of_essImage_etaleDescentFunctor g (Over.mk p) (H U p hp)

end Datum

end Stacks.Etale

end
