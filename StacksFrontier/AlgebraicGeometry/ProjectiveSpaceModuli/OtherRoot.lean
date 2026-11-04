module

public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkCoordinate
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The other root of a binary quadratic form

Let `T` be a scheme, `M` an invertible `𝒪_T`-module with global sections `A, B, C` without
common zero, and `(L, (z₀, z₁))` an invertible module with two generating sections, that is, a
morphism `T ⟶ ℙ¹_ℤ` ([Stacks, Tag 01NE]). Suppose that `(z₀ : z₁)` is a root of the binary
quadratic form `A X² + B X Y + C Y²`:

  `A z₀² + B z₀ z₁ + C z₁² = 0` in `M ⊗ L ⊗ L`.

The *other root* is the morphism `σ : T ⟶ ℙ¹_ℤ` which, by Vieta, is given by the pair of
sections `(-(B z₁ + A z₀), A z₁)` of `M ⊗ L` where this pair generates, and by the pair
`(C z₀, -(B z₀ + C z₁))` where that pair generates. These two opens cover `T`: where `z₁` is
invertible the first pair generates and where `z₀` is invertible the second does, because `A, B,
C` have no common zero and `z₀, z₁` generate. On the overlap the two pairs cross-multiply, their
cross-product being `B (A z₀² + B z₀ z₁ + C z₁²) = 0`, so the two chartwise morphisms glue by the
cross-multiplication criterion. The result has the expected properties:

* the other root is again a root, and the other root of the other root is the root;
* it is natural in `T` and only depends on the data up to the identification of Tag 01NE;
* the pullback `N = σ^*𝒪(1)` satisfies `N ⊗ L² ≅ M ⊗ L`, by an isomorphism carrying
  `T'ᵢ ⊗ z₁²` to `(-(B z₁ + A z₀), A z₁)` and `T'ᵢ ⊗ z₀²` to `(C z₀, -(B z₀ + C z₁))`.

All identities are checked at stalks, in the coordinates of `Stacks.InvertibleStalk.stalkCoord`,
where they become identities between elements of a local ring; these are collected in the first
section.

## Main definitions

* `Stacks.BinaryQuadric.eval`: the value `A z₀² + B z₀ z₁ + C z₁²`, and
  `Stacks.BinaryQuadric.IsRoot`: its vanishing.
* `Stacks.BinaryQuadric.otherRootPairA`, `Stacks.BinaryQuadric.otherRootPairC`: the two pairs of
  homogeneous coordinates of the other root, and `Stacks.BinaryQuadric.otherRootChart` the opens
  where they generate.
* `Stacks.BinaryQuadric.otherRoot`: the other root, a morphism `T ⟶ ℙ¹_ℤ`.
* `Stacks.BinaryQuadric.otherRootTwistIso`: the isomorphism `N ⊗ L² ≅ M ⊗ L`.
* `Stacks.ProjectiveSpaceModuli.familyPullbackTuple`: the pullback of a family of sections along a
  morphism into the locus where the family generates.

## Main results

* `Stacks.BinaryQuadric.crossMultiplies_otherRoot` and
  `Stacks.BinaryQuadric.eq_otherRoot_of_crossMultiplies`: the other root is the unique morphism
  whose pair of sections cross-multiplies with both pairs of homogeneous coordinates.
* `Stacks.BinaryQuadric.isRoot_otherRoot` and `Stacks.BinaryQuadric.otherRoot_otherRoot`.
* `Stacks.BinaryQuadric.otherRoot_pullbackTuple` and `Stacks.BinaryQuadric.otherRoot_congr`.
* `Stacks.BinaryQuadric.isomorphic_otherRootTwistTuple`.
* `Stacks.ProjectiveSpaceModuli.CrossMultiplies.pullbackGlobalSections` and
  `Stacks.ProjectiveSpaceModuli.crossMultiplies_at_of_pullbackGlobalSections`: cross-multiplication
  pulls back, and descends along morphisms injective on stalks.

## Implementation notes

The coefficients `A, B, C` are packaged as a `Stacks.ProjectiveSpaceModuli.GeneratingTuple` with
three sections, which is the hypothesis that they have no common zero. The other root is
characterized through cross-multiplication with both pairs of homogeneous coordinates *at every
point*, not only on the chart where a pair generates; this global characterization is what makes
the involution, the naturality and the line-bundle identity stalkwise computations.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ProjectiveFromSections Stacks.InvertibleStalk
open scoped TensorProduct

universe u

namespace Stacks.ProjectiveSpaceModuli

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X Y : Scheme.{u}} {n : ℕ}

/-- Every point of `ℙⁿ_ℤ` lies in the nonvanishing locus of one of the homogeneous
coordinates `T₀, …, Tₙ`. -/
theorem exists_mem_nonvanishingLocus_coordGlobalSection (p : projectiveSpaceAtUniverse.{u} n) :
    ∃ i, p ∈ Stacks.Ample.nonvanishingLocus
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n)
        (Stacks.TwistPullbackPinned.coordGlobalSection.{u} n i) := by
  have hint : ⨆ i : Fin (n + 1), AlgebraicGeometry.Proj.basicOpen
      (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i) = ⊤ :=
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_top _ _
      (AlgebraicGeometry.projectiveSpaceOver.irrelevant_coordGrading_le_span_X n)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hint.ge
    (show p ∈ (⊤ : (projectiveSpaceAtUniverse.{u} n).Opens) from trivial))
  exact ⟨i, Stacks.TwistPullbackPinned.mem_nonvanishingLocus_coordGlobalSection i hi⟩

/-- The stalk maps of an open immersion are injective. -/
theorem injective_stalkMap_of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    Function.Injective (f.stalkMap y).hom :=
  (ConcreteCategory.bijective_of_isIso _).1

/-- Every point lies in the nonvanishing locus of one of the sections of a generating tuple. -/
theorem GeneratingTuple.exists_mem_nonvanishingLocus (t : GeneratingTuple X n) (x : X) :
    ∃ i, x ∈ Stacks.Ample.nonvanishingLocus t.bundle (t.coord i) :=
  exists_mem_nvCover_of_generatesStalks t.coord t.generates x

/-- **The coordinates of the tautological pair of a morphism** `g : X ⟶ ℙⁿ_ℤ` at `x` are the
images under `g^♯` of the coordinates of the homogeneous coordinates at `g x`. -/
theorem stalkCoord_tautological_coord (g : X ⟶ projectiveSpaceAtUniverse.{u} n) {x : X}
    {j : Fin (n + 1)}
    (hp : g x ∈ Stacks.Ample.nonvanishingLocus
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n)
      (Stacks.TwistPullbackPinned.coordGlobalSection.{u} n j)) (i : Fin (n + 1)) :
    stalkCoord (tautological g).bundle (mem_nonvanishingLocus_pullbackGlobalSections g hp)
        ((tautological g).coord i) =
      (g.stalkMap x).hom
        (stalkCoord _ hp (Stacks.TwistPullbackPinned.coordGlobalSection.{u} n i)) :=
  stalkCoord_pullbackGlobalSections g hp _

/-! ### Pulling a family of sections back into the locus where it generates -/

section FamilyPullback

variable {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **The pullback of a family of sections, along a morphism into the locus where the family
generates**, as an invertible module with generating sections. -/
def familyPullbackTuple (f : Y ⟶ X) (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : ∀ y : Y, ∃ i, f y ∈ Stacks.Ample.nonvanishingLocus L (s i)) : GeneratingTuple Y n where
  bundle := (Scheme.Modules.pullback f).obj L
  isInvertible := inferInstance
  coord i := pullbackGlobalSections f L (s i)
  generates := Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun y =>
    (hs y).elim fun i hi => ⟨i, mem_nonvanishingLocus_pullbackGlobalSections f hi⟩

/-- The pullback of a family along a composite is the pullback of the pullback. -/
theorem isomorphic_pullbackTuple_familyPullbackTuple {Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : ∀ y : Y, ∃ i, f y ∈ Stacks.Ample.nonvanishingLocus L (s i))
    (hs' : ∀ z : Z, ∃ i, (g ≫ f) z ∈ Stacks.Ample.nonvanishingLocus L (s i)) :
    Isomorphic (pullbackTuple g (familyPullbackTuple f s hs)) (familyPullbackTuple (g ≫ f) s hs') :=
  ⟨(Scheme.Modules.pullbackComp g f).app L, fun i =>
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp g f L (s i)⟩

/-- The pullback of a family only depends on the morphism. -/
theorem isomorphic_familyPullbackTuple_of_eq {f f' : Y ⟶ X} (e : f = f')
    (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : ∀ y : Y, ∃ i, f y ∈ Stacks.Ample.nonvanishingLocus L (s i))
    (hs' : ∀ y : Y, ∃ i, f' y ∈ Stacks.Ample.nonvanishingLocus L (s i)) :
    Isomorphic (familyPullbackTuple f s hs) (familyPullbackTuple f' s hs') := by
  subst e
  exact isomorphic_refl _

end FamilyPullback

/-! ### Cross-multiplication under pullback and isomorphism -/

section CrossMultiplication

variable {M N : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
  [Stacks.Ample.IsInvertibleModule X N] {ι : Type*}

/-- **Cross-multiplication is preserved by pullback**, for arbitrary families of global
sections of invertible modules that are generated at every point by a global section. -/
theorem CrossMultiplies.pullbackGlobalSections {s : ι → Γ(M, ⊤)} {s' : ι → Γ(N, ⊤)}
    (hM : ∀ x : X, ∃ e : Γ(M, ⊤), x ∈ Stacks.Ample.nonvanishingLocus M e)
    (hN : ∀ x : X, ∃ e : Γ(N, ⊤), x ∈ Stacks.Ample.nonvanishingLocus N e)
    (h : CrossMultiplies s s') (f : Y ⟶ X) :
    CrossMultiplies (fun i => pullbackGlobalSections f M (s i))
      (fun i => pullbackGlobalSections f N (s' i)) := by
  intro y
  obtain ⟨e, he⟩ := hM (f y)
  obtain ⟨e', he'⟩ := hN (f y)
  have hx := (crossMultiplies_at_iff_stalkCoord he he' s s').1 (h (f y))
  refine (crossMultiplies_at_iff_stalkCoord (mem_nonvanishingLocus_pullbackGlobalSections f he)
    (mem_nonvanishingLocus_pullbackGlobalSections f he') _ _).2 fun i j => ?_
  rw [stalkCoord_pullbackGlobalSections f he, stalkCoord_pullbackGlobalSections f he',
    stalkCoord_pullbackGlobalSections f he, stalkCoord_pullbackGlobalSections f he', ← map_mul,
    ← map_mul, hx i j]

/-- **Cross-multiplication descends along a morphism injective on the stalk**: if the pullbacks
cross-multiply at `y` and `f^♯ : 𝒪_{X, f y} → 𝒪_{Y, y}` is injective, the families
cross-multiply at `f y`. -/
theorem crossMultiplies_at_of_pullbackGlobalSections (f : Y ⟶ X) {y : Y}
    (hinj : Function.Injective (f.stalkMap y).hom) {e : Γ(M, ⊤)} {e' : Γ(N, ⊤)}
    (he : f y ∈ Stacks.Ample.nonvanishingLocus M e)
    (he' : f y ∈ Stacks.Ample.nonvanishingLocus N e') {s : ι → Γ(M, ⊤)} {s' : ι → Γ(N, ⊤)}
    (h : CrossMultiplies (fun i => pullbackGlobalSections f M (s i))
      (fun i => pullbackGlobalSections f N (s' i))) :
    ∀ i j, (M.presheaf.Γgerm (f y)).hom (s i) ⊗ₜ[X.presheaf.stalk (f y)]
        (N.presheaf.Γgerm (f y)).hom (s' j) =
      (M.presheaf.Γgerm (f y)).hom (s j) ⊗ₜ[X.presheaf.stalk (f y)]
        (N.presheaf.Γgerm (f y)).hom (s' i) := by
  have hy := (crossMultiplies_at_iff_stalkCoord (mem_nonvanishingLocus_pullbackGlobalSections f he)
    (mem_nonvanishingLocus_pullbackGlobalSections f he') _ _).1 (h y)
  refine (crossMultiplies_at_iff_stalkCoord he he' s s').2 fun i j => hinj ?_
  have := hy i j
  rw [stalkCoord_pullbackGlobalSections f he, stalkCoord_pullbackGlobalSections f he',
    stalkCoord_pullbackGlobalSections f he, stalkCoord_pullbackGlobalSections f he', ← map_mul,
    ← map_mul] at this
  exact this

/-- **Cross-multiplication with a generating tuple only depends on the tuple up to the
identification of Tag 01NE.** -/
theorem crossMultiplies_coord_iff_of_isomorphic {t t' : GeneratingTuple X n}
    (ht : Isomorphic t t') {s : Fin (n + 1) → Γ(N, ⊤)}
    (hN : ∀ x : X, ∃ e : Γ(N, ⊤), x ∈ Stacks.Ample.nonvanishingLocus N e) :
    CrossMultiplies t.coord s ↔ CrossMultiplies t'.coord s := by
  obtain ⟨β, hβ⟩ := ht
  refine forall_congr' fun x => ?_
  obtain ⟨j, hj⟩ := t.exists_mem_nonvanishingLocus x
  obtain ⟨e, he⟩ := hN x
  have hj' : x ∈ Stacks.Ample.nonvanishingLocus t'.bundle (t'.coord j) := by
    rw [← hβ j, mem_nonvanishingLocus_app_hom_iff]
    exact hj
  rw [crossMultiplies_at_iff_stalkCoord hj he, crossMultiplies_at_iff_stalkCoord hj' he]
  have hc : ∀ i, stalkCoord t'.bundle hj' (t'.coord i) = stalkCoord t.bundle hj (t.coord i) :=
    fun i => by
      have hj'' : x ∈ Stacks.Ample.nonvanishingLocus t'.bundle
          (Scheme.Modules.Hom.app β.hom ⊤ (t.coord j)) := by rw [hβ j]; exact hj'
      rw [← stalkCoord_app_hom β hj hj'' (t.coord i)]
      simp only [hβ]
  simp only [hc]

/-- **Cross-multiplication of generating tuples is invariant under the identification of
Tag 01NE on both sides.** -/
theorem CrossMultiplies.of_isomorphic {t₁ t₂ t₁' t₂' : GeneratingTuple X n}
    (h : CrossMultiplies t₁.coord t₂.coord) (h₁ : Isomorphic t₁ t₁') (h₂ : Isomorphic t₂ t₂') :
    CrossMultiplies t₁'.coord t₂'.coord :=
  crossMultiplies_of_isomorphic (isomorphic_trans (isomorphic_symm h₁)
    (isomorphic_trans (isomorphic_of_crossMultiplies h) h₂))

end CrossMultiplication

end Stacks.ProjectiveSpaceModuli

namespace Stacks.BinaryQuadric

open Stacks.ProjectiveSpaceModuli

/-! ### The algebra of the other root -/

section Algebra

variable {R : Type*} [CommRing R]

/-- The value `a z₀² + b z₀ z₁ + c z₁²` of the binary quadratic form with coefficients
`α = (a, b, c)` at `ζ = (z₀, z₁)`. -/
def quadPoly (α : Fin 3 → R) (ζ : Fin 2 → R) : R :=
  α 0 * ζ 0 * ζ 0 + α 1 * ζ 0 * ζ 1 + α 2 * ζ 1 * ζ 1

/-- The two pairs of homogeneous coordinates `(-(b z₁ + a z₀), a z₁)` and
`(c z₀, -(b z₀ + c z₁))` of the other root of the binary quadratic form. -/
def pairPoly (α : Fin 3 → R) (ζ : Fin 2 → R) : Fin 2 → Fin 2 → R :=
  ![![-(α 1 * ζ 1 + α 0 * ζ 0), α 0 * ζ 1], ![α 2 * ζ 0, -(α 1 * ζ 0 + α 2 * ζ 1)]]

/-- Two families cross-multiply: `uᵢ vⱼ = uⱼ vᵢ` for all `i, j`. -/
def Cross {ι : Type*} (u v : ι → R) : Prop := ∀ i j, u i * v j = u j * v i

/-- Two pairs cross-multiply exactly when their two-by-two minor vanishes. -/
theorem cross_fin_two {u v : Fin 2 → R} : Cross u v ↔ u 0 * v 1 = u 1 * v 0 := by
  refine ⟨fun h => h 0 1, fun h i j => ?_⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact h
  · exact h.symm
  · rfl

/-- Cross-multiplication is symmetric. -/
theorem Cross.symm {ι : Type*} {u v : ι → R} (h : Cross u v) : Cross v u := fun i j => by
  rw [mul_comm (v i), h j i, mul_comm]

/-- An element of `Fin 2` is `0` or `1`. -/
theorem fin_two_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- Cross-multiplication is preserved by ring homomorphisms. -/
theorem cross_map {S : Type*} [CommRing S] (φ : R →+* S) {ι : Type*} {u v : ι → R}
    (h : Cross u v) : Cross (fun i => φ (u i)) (fun i => φ (v i)) := fun i j => by
  rw [← map_mul, ← map_mul, h i j]

/-- The value of the form commutes with ring homomorphisms. -/
theorem map_quadPoly {S : Type*} [CommRing S] (φ : R →+* S) (α : Fin 3 → R) (ζ : Fin 2 → R) :
    φ (quadPoly α ζ) = quadPoly (fun i => φ (α i)) (fun j => φ (ζ j)) := by
  simp only [quadPoly, map_add, map_mul]

/-- The coordinates of the other root commute with ring homomorphisms. -/
theorem map_pairPoly {S : Type*} [CommRing S] (φ : R →+* S) (α : Fin 3 → R) (ζ : Fin 2 → R)
    (a i : Fin 2) :
    φ (pairPoly α ζ a i) = pairPoly (fun i => φ (α i)) (fun j => φ (ζ j)) a i := by
  fin_cases a <;> fin_cases i <;> simp [pairPoly]

/-- The two pairs of coordinates of the other root cross-multiply on the quadric: the
cross-product is `b` times the value of the form. -/
theorem cross_pairPoly {α : Fin 3 → R} {ζ : Fin 2 → R} (hq : quadPoly α ζ = 0) (a b : Fin 2) :
    Cross (pairPoly α ζ a) (pairPoly α ζ b) := by
  rw [cross_fin_two]
  unfold quadPoly at hq
  rcases fin_two_cases a with rfl | rfl <;> rcases fin_two_cases b with rfl | rfl <;>
    simp [pairPoly]
  · ring
  · linear_combination (α 1) * hq
  · linear_combination (-(α 1)) * hq
  · ring

/-- An element whose product with a unit lies in the maximal ideal lies in it. -/
theorem mem_maximalIdeal_of_mul_isUnit [IsLocalRing R] {x u : R} (hu : IsUnit u)
    (h : x * u ∈ IsLocalRing.maximalIdeal R) : x ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨v, rfl⟩ := hu
  simpa using Ideal.mul_mem_right (↑v⁻¹ : R) _ h

/-- If `z₁` is a unit and the first pair of coordinates of the other root lies in the maximal
ideal, so do all coefficients. -/
private theorem mem_maximalIdeal_of_pairPoly_zero [IsLocalRing R] {α : Fin 3 → R} {ζ : Fin 2 → R}
    (hq : quadPoly α ζ = 0) (hw : IsUnit (ζ 1))
    (hm : ∀ i, pairPoly α ζ 0 i ∈ IsLocalRing.maximalIdeal R) (i : Fin 3) :
    α i ∈ IsLocalRing.maximalIdeal R := by
  unfold quadPoly at hq
  have h0 : α 0 ∈ IsLocalRing.maximalIdeal R :=
    mem_maximalIdeal_of_mul_isUnit hw (by simpa [pairPoly] using hm 1)
  have h1 : α 1 ∈ IsLocalRing.maximalIdeal R := by
    refine mem_maximalIdeal_of_mul_isUnit hw ?_
    have e : α 1 * ζ 1 = -pairPoly α ζ 0 0 - α 0 * ζ 0 := by simp [pairPoly]
    rw [e]
    exact sub_mem (neg_mem (hm 0)) (Ideal.mul_mem_right _ _ h0)
  have h2 : α 2 ∈ IsLocalRing.maximalIdeal R := by
    refine mem_maximalIdeal_of_mul_isUnit (hw.mul hw) ?_
    have e : α 2 * (ζ 1 * ζ 1) = -(α 0 * ζ 0 * ζ 0) - α 1 * ζ 0 * ζ 1 := by
      linear_combination hq
    rw [e]
    exact sub_mem (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h0)))
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1))
  fin_cases i <;> assumption

/-- If `z₀` is a unit and the second pair of coordinates of the other root lies in the maximal
ideal, so do all coefficients. -/
private theorem mem_maximalIdeal_of_pairPoly_one [IsLocalRing R] {α : Fin 3 → R} {ζ : Fin 2 → R}
    (hq : quadPoly α ζ = 0) (hz : IsUnit (ζ 0))
    (hm : ∀ i, pairPoly α ζ 1 i ∈ IsLocalRing.maximalIdeal R) (i : Fin 3) :
    α i ∈ IsLocalRing.maximalIdeal R := by
  unfold quadPoly at hq
  have h2 : α 2 ∈ IsLocalRing.maximalIdeal R :=
    mem_maximalIdeal_of_mul_isUnit hz (by simpa [pairPoly] using hm 0)
  have h1 : α 1 ∈ IsLocalRing.maximalIdeal R := by
    refine mem_maximalIdeal_of_mul_isUnit hz ?_
    have e : α 1 * ζ 0 = -pairPoly α ζ 1 1 - α 2 * ζ 1 := by simp [pairPoly]
    rw [e]
    exact sub_mem (neg_mem (hm 1)) (Ideal.mul_mem_right _ _ h2)
  have h0 : α 0 ∈ IsLocalRing.maximalIdeal R := by
    refine mem_maximalIdeal_of_mul_isUnit (hz.mul hz) ?_
    have e : α 0 * (ζ 0 * ζ 0) = -(α 1 * ζ 0 * ζ 1) - α 2 * ζ 1 * ζ 1 := by
      linear_combination hq
    rw [e]
    exact sub_mem (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)))
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h2))
  fin_cases i <;> assumption

/-- **One of the four coordinates of the other root is a unit**, at a point of the quadric over
a local ring where the coefficients and the coordinates generate. -/
theorem exists_isUnit_pairPoly [IsLocalRing R] {α : Fin 3 → R} {ζ : Fin 2 → R}
    (hq : quadPoly α ζ = 0) (hα : ∃ i, IsUnit (α i)) (hζ : ∃ j, IsUnit (ζ j)) :
    ∃ a i, IsUnit (pairPoly α ζ a i) := by
  by_contra hno
  simp only [not_exists] at hno
  have hm : ∀ a i, pairPoly α ζ a i ∈ IsLocalRing.maximalIdeal R := fun a i =>
    (IsLocalRing.mem_maximalIdeal _).2 (hno a i)
  obtain ⟨i, hi⟩ := hα
  refine (IsLocalRing.mem_maximalIdeal _).1 ?_ hi
  obtain ⟨j, hj⟩ := hζ
  fin_cases j
  · exact mem_maximalIdeal_of_pairPoly_one hq hj (hm 1) i
  · exact mem_maximalIdeal_of_pairPoly_zero hq hj (hm 0) i

/-- Where `z₁` is a unit, the first pair of coordinates has a unit. -/
theorem exists_isUnit_pairPoly_zero [IsLocalRing R] {α : Fin 3 → R} {ζ : Fin 2 → R}
    (hq : quadPoly α ζ = 0) (hα : ∃ i, IsUnit (α i)) (hw : IsUnit (ζ 1)) :
    ∃ i, IsUnit (pairPoly α ζ 0 i) := by
  by_contra hno
  simp only [not_exists] at hno
  obtain ⟨i, hi⟩ := hα
  exact (IsLocalRing.mem_maximalIdeal _).1 (mem_maximalIdeal_of_pairPoly_zero hq hw
    (fun i => (IsLocalRing.mem_maximalIdeal _).2 (hno i)) i) hi

/-- Where `z₀` is a unit, the second pair of coordinates has a unit. -/
theorem exists_isUnit_pairPoly_one [IsLocalRing R] {α : Fin 3 → R} {ζ : Fin 2 → R}
    (hq : quadPoly α ζ = 0) (hα : ∃ i, IsUnit (α i)) (hz : IsUnit (ζ 0)) :
    ∃ i, IsUnit (pairPoly α ζ 1 i) := by
  by_contra hno
  simp only [not_exists] at hno
  obtain ⟨i, hi⟩ := hα
  exact (IsLocalRing.mem_maximalIdeal _).1 (mem_maximalIdeal_of_pairPoly_one hq hz
    (fun i => (IsLocalRing.mem_maximalIdeal _).2 (hno i)) i) hi

/-- **Cross-multiplication is transitive through a family with a unit entry.** -/
theorem Cross.trans_of_isUnit {ι : Type*} {u v w : ι → R} (huv : Cross u v) (hvw : Cross v w)
    {k : ι} (hk : IsUnit (v k)) : Cross u w := fun i j => by
  refine hk.mul_left_cancel ?_
  linear_combination (u i) * hvw k j + (w k) * huv i j + (u j) * hvw i k

/-- On the quadric, `Q(λ) p₀² = λ₀² Q(p)` for a family `λ` cross-multiplying with `p`. -/
theorem quadPoly_mul_sq_zero (α : Fin 3 → R) {l p : Fin 2 → R} (h : l 0 * p 1 = l 1 * p 0) :
    quadPoly α l * (p 0 * p 0) = l 0 * l 0 * quadPoly α p := by
  unfold quadPoly
  linear_combination (-(α 1 * l 0 * p 0 + α 2 * (l 1 * p 0 + l 0 * p 1))) * h

/-- On the quadric, `Q(λ) p₁² = λ₁² Q(p)` for a family `λ` cross-multiplying with `p`. -/
theorem quadPoly_mul_sq_one (α : Fin 3 → R) {l p : Fin 2 → R} (h : l 0 * p 1 = l 1 * p 0) :
    quadPoly α l * (p 1 * p 1) = l 1 * l 1 * quadPoly α p := by
  unfold quadPoly
  linear_combination (α 0 * (l 0 * p 1 + l 1 * p 0) + α 1 * l 1 * p 1) * h

/-- The form at the first pair of coordinates of the other root is `a²` times its value. -/
theorem quadPoly_pairPoly_zero (α : Fin 3 → R) (ζ : Fin 2 → R) :
    quadPoly α (pairPoly α ζ 0) = α 0 * α 0 * quadPoly α ζ := by
  simp only [quadPoly, pairPoly, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The form at the second pair of coordinates of the other root is `c²` times its value. -/
theorem quadPoly_pairPoly_one (α : Fin 3 → R) (ζ : Fin 2 → R) :
    quadPoly α (pairPoly α ζ 1) = α 2 * α 2 * quadPoly α ζ := by
  simp only [quadPoly, pairPoly, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **A family cross-multiplying with a pair of coordinates of the other root having a unit
entry is a root.** -/
theorem quadPoly_eq_zero_of_cross {α : Fin 3 → R} {ζ l : Fin 2 → R} (hq : quadPoly α ζ = 0)
    {a k : Fin 2} (hl : Cross l (pairPoly α ζ a)) (hk : IsUnit (pairPoly α ζ a k)) :
    quadPoly α l = 0 := by
  have hQ : quadPoly α (pairPoly α ζ a) = 0 := by
    rcases fin_two_cases a with rfl | rfl
    · rw [quadPoly_pairPoly_zero, hq, mul_zero]
    · rw [quadPoly_pairPoly_one, hq, mul_zero]
  have h := cross_fin_two.1 hl
  rcases fin_two_cases k with rfl | rfl
  · have e := quadPoly_mul_sq_zero α h
    rw [hQ, mul_zero] at e
    exact (hk.mul hk).mul_left_eq_zero.1 e
  · have e := quadPoly_mul_sq_one α h
    rw [hQ, mul_zero] at e
    exact (hk.mul hk).mul_left_eq_zero.1 e

/-- **The other root of the other root is the root**: if `λ` cross-multiplies with the `a`-th
pair of coordinates of the other root of `ζ`, then `ζ` cross-multiplies with the `a`-th pair of
coordinates of the other root of `λ`. -/
theorem cross_pairPoly_swap {α : Fin 3 → R} {ζ l : Fin 2 → R} {a : Fin 2}
    (hl : Cross l (pairPoly α ζ a)) : Cross ζ (pairPoly α l a) := by
  have h := cross_fin_two.1 hl
  rw [cross_fin_two]
  rcases fin_two_cases a with rfl | rfl <;> simp [pairPoly] at h ⊢ <;> linear_combination h

/-- **The twisted cross-multiplication**: on the quadric, for `λ` cross-multiplying with both
pairs `σ`, `υ` of coordinates of the other root, the families
`(λ₀ z₀², λ₁ z₀², λ₀ z₁², λ₁ z₁²)` and `(υ₀, υ₁, σ₀, σ₁)` cross-multiply. -/
theorem cross_twist {α : Fin 3 → R} {ζ l : Fin 2 → R} (hq : quadPoly α ζ = 0)
    (hA : Cross l (pairPoly α ζ 0)) (hC : Cross l (pairPoly α ζ 1)) :
    Cross ![l 0 * (ζ 0 * ζ 0), l 1 * (ζ 0 * ζ 0), l 0 * (ζ 1 * ζ 1), l 1 * (ζ 1 * ζ 1)]
      ![pairPoly α ζ 1 0, pairPoly α ζ 1 1, pairPoly α ζ 0 0, pairPoly α ζ 0 1] := by
  have hA' := cross_fin_two.1 hA
  have hC' := cross_fin_two.1 hC
  simp only [pairPoly, Matrix.cons_val_zero, Matrix.cons_val_one] at hA' hC' ⊢
  unfold quadPoly at hq
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
  · linear_combination (ζ 0 * ζ 0) * hC'
  · linear_combination (-(l 0 * ζ 0)) * hq
  · linear_combination (l 0 * ζ 1) * hq + (ζ 1 * ζ 1) * hC'
  · linear_combination (-(ζ 0 * ζ 0)) * hC'
  · linear_combination (-(l 1 * ζ 0)) * hq - (ζ 1 * ζ 1) * hC'
  · linear_combination (l 1 * ζ 1) * hq
  · linear_combination (l 0 * ζ 0) * hq
  · linear_combination (l 1 * ζ 0) * hq + (ζ 1 * ζ 1) * hC'
  · linear_combination (ζ 1 * ζ 1) * hA'
  · linear_combination (-(l 0 * ζ 1)) * hq - (ζ 1 * ζ 1) * hC'
  · linear_combination (-(l 1 * ζ 1)) * hq
  · linear_combination (-(ζ 1 * ζ 1)) * hA'

end Algebra

variable {T : Scheme.{u}}

/-- `tsa s t` is the product `s ⊗ t` of two global sections over `T`, a global section of the
tensor product. -/
local macro "tsa " s:term:max t:term:max : term =>
  `(Stacks.SheafOfModules.tensorSectionsAt $(Lean.mkIdent `T.sheaf.obj)
    $(Lean.mkIdent `T.ringCatSheaf.property) (op ⊤) _ _ $s $t)

variable (c : GeneratingTuple T 2) (t : GeneratingTuple T 1)

/-- **The value of a binary quadratic form at a point of `ℙ¹`.** For coefficients
`(A, B, C) = c` — global sections of an invertible module `M` — and a point `t = (L, (z₀, z₁))`,
the global section `A z₀² + B z₀ z₁ + C z₁²` of `(M ⊗ L) ⊗ L`. -/
@[sga "7 XII 1.1" "partial"]
def eval : Γ(Scheme.Modules.tensorObj (Scheme.Modules.tensorObj c.bundle t.bundle) t.bundle, ⊤) :=
  tsa (tsa (c.coord 0) (t.coord 0)) (t.coord 0) + tsa (tsa (c.coord 1) (t.coord 0)) (t.coord 1) +
    tsa (tsa (c.coord 2) (t.coord 1)) (t.coord 1)

/-- **`t` is a root of the binary quadratic form `c`**: `A z₀² + B z₀ z₁ + C z₁² = 0`. -/
def IsRoot : Prop := eval c t = 0

/-- The homogeneous coordinates `(-(B z₁ + A z₀), A z₁)` of the other root, the form used where
`z₁` does not vanish. -/
def otherRootPairA : Fin 2 → Γ(Scheme.Modules.tensorObj c.bundle t.bundle, ⊤) :=
  ![-(tsa (c.coord 1) (t.coord 1) + tsa (c.coord 0) (t.coord 0)), tsa (c.coord 0) (t.coord 1)]

/-- The homogeneous coordinates `(C z₀, -(B z₀ + C z₁))` of the other root, the form used where
`z₀` does not vanish. -/
def otherRootPairC : Fin 2 → Γ(Scheme.Modules.tensorObj c.bundle t.bundle, ⊤) :=
  ![tsa (c.coord 2) (t.coord 0), -(tsa (c.coord 1) (t.coord 0) + tsa (c.coord 2) (t.coord 1))]

/-! ### Coordinates -/

section Coordinates

variable {c t} {x : T} {i₀ : Fin 3} {j₀ : Fin 2}
  (hc : x ∈ Stacks.Ample.nonvanishingLocus c.bundle (c.coord i₀))
  (ht : x ∈ Stacks.Ample.nonvanishingLocus t.bundle (t.coord j₀))

/-- The coordinate of the value of the form, relative to `(A_{i₀} ⊗ z_{j₀}) ⊗ z_{j₀}`. -/
theorem stalkCoord_eval :
    stalkCoord _ (mem_nonvanishingLocus_tensorSectionsAt (mem_nonvanishingLocus_tensorSectionsAt
        hc ht) ht) (eval c t) =
      stalkCoord _ hc (c.coord 0) * stalkCoord _ ht (t.coord 0) * stalkCoord _ ht (t.coord 0) +
        stalkCoord _ hc (c.coord 1) * stalkCoord _ ht (t.coord 0) *
          stalkCoord _ ht (t.coord 1) +
        stalkCoord _ hc (c.coord 2) * stalkCoord _ ht (t.coord 1) *
          stalkCoord _ ht (t.coord 1) :=
  (stalkCoord_add _ _ _).trans (congrArg₂ (· + ·) ((stalkCoord_add _ _ _).trans
    (congrArg₂ (· + ·)
      ((stalkCoord_tensorSectionsAt _ ht _ _).trans
        (congrArg (· * _) (stalkCoord_tensorSectionsAt hc ht _ _)))
      ((stalkCoord_tensorSectionsAt _ ht _ _).trans
        (congrArg (· * _) (stalkCoord_tensorSectionsAt hc ht _ _)))))
    ((stalkCoord_tensorSectionsAt _ ht _ _).trans
      (congrArg (· * _) (stalkCoord_tensorSectionsAt hc ht _ _))))

/-- The coordinate of `-(B z₁ + A z₀)`. -/
theorem stalkCoord_otherRootPairA_zero :
    stalkCoord _ (mem_nonvanishingLocus_tensorSectionsAt hc ht) (otherRootPairA c t 0) =
      -(stalkCoord _ hc (c.coord 1) * stalkCoord _ ht (t.coord 1) +
        stalkCoord _ hc (c.coord 0) * stalkCoord _ ht (t.coord 0)) :=
  (stalkCoord_neg _ _).trans (congrArg Neg.neg ((stalkCoord_add _ _ _).trans
    (congrArg₂ (· + ·) (stalkCoord_tensorSectionsAt hc ht _ _)
      (stalkCoord_tensorSectionsAt hc ht _ _))))

/-- The coordinate of `A z₁`. -/
theorem stalkCoord_otherRootPairA_one :
    stalkCoord _ (mem_nonvanishingLocus_tensorSectionsAt hc ht) (otherRootPairA c t 1) =
      stalkCoord _ hc (c.coord 0) * stalkCoord _ ht (t.coord 1) :=
  stalkCoord_tensorSectionsAt hc ht _ _

/-- The coordinate of `C z₀`. -/
theorem stalkCoord_otherRootPairC_zero :
    stalkCoord _ (mem_nonvanishingLocus_tensorSectionsAt hc ht) (otherRootPairC c t 0) =
      stalkCoord _ hc (c.coord 2) * stalkCoord _ ht (t.coord 0) :=
  stalkCoord_tensorSectionsAt hc ht _ _

/-- The coordinate of `-(B z₀ + C z₁)`. -/
theorem stalkCoord_otherRootPairC_one :
    stalkCoord _ (mem_nonvanishingLocus_tensorSectionsAt hc ht) (otherRootPairC c t 1) =
      -(stalkCoord _ hc (c.coord 1) * stalkCoord _ ht (t.coord 0) +
        stalkCoord _ hc (c.coord 2) * stalkCoord _ ht (t.coord 1)) :=
  (stalkCoord_neg _ _).trans (congrArg Neg.neg ((stalkCoord_add _ _ _).trans
    (congrArg₂ (· + ·) (stalkCoord_tensorSectionsAt hc ht _ _)
      (stalkCoord_tensorSectionsAt hc ht _ _))))

end Coordinates

/-! ### Coordinates of tuples -/

/-- The coordinates at `x` of the sections of a tuple, relative to the member `t.coord j`, which
does not vanish at `x`. -/
abbrev tupleCoord {n : ℕ} (t : GeneratingTuple T n) {x : T} {j : Fin (n + 1)}
    (ht : x ∈ Stacks.Ample.nonvanishingLocus t.bundle (t.coord j)) :
    Fin (n + 1) → T.presheaf.stalk x :=
  fun i => stalkCoord _ ht (t.coord i)

section Coordinates

variable {c t} {x : T} {i₀ : Fin 3} {j₀ : Fin 2}
  (hc : x ∈ Stacks.Ample.nonvanishingLocus c.bundle (c.coord i₀))
  (ht : x ∈ Stacks.Ample.nonvanishingLocus t.bundle (t.coord j₀))

/-- The coordinate of the value of the form is the value of the form at the coordinates. -/
theorem stalkCoord_eval_eq_quadPoly :
    stalkCoord _ (mem_nonvanishingLocus_tensorSectionsAt (mem_nonvanishingLocus_tensorSectionsAt
        hc ht) ht) (eval c t) = quadPoly (tupleCoord c hc) (tupleCoord t ht) :=
  stalkCoord_eval hc ht

/-- **At a point of the zero locus the coordinates are a root.** -/
theorem quadPoly_tupleCoord_eq_zero (h : IsRoot c t) :
    quadPoly (tupleCoord c hc) (tupleCoord t ht) = 0 :=
  (stalkCoord_eval_eq_quadPoly hc ht).symm.trans
    ((congrArg (stalkCoord _ (mem_nonvanishingLocus_tensorSectionsAt
      (mem_nonvanishingLocus_tensorSectionsAt hc ht) ht)) h).trans (stalkCoord_zero _))

end Coordinates

/-- **A root, read in coordinates**: `t` is a root of `c` as soon as at every point the
coordinates are a root. -/
theorem isRoot_of_forall_quadPoly
    (H : ∀ x : T, ∃ (i₀ : Fin 3) (j₀ : Fin 2)
      (hc : x ∈ Stacks.Ample.nonvanishingLocus c.bundle (c.coord i₀))
      (ht : x ∈ Stacks.Ample.nonvanishingLocus t.bundle (t.coord j₀)),
      quadPoly (tupleCoord c hc) (tupleCoord t ht) = 0) : IsRoot c t := by
  refine eq_zero_of_forall_stalkCoord_eq_zero _ fun x => ?_
  obtain ⟨i₀, j₀, hc, ht, hq⟩ := H x
  exact ⟨_, _, (stalkCoord_eval_eq_quadPoly hc ht).trans hq⟩

/-! ### The two charts of the other root -/

/-- The two pairs of homogeneous coordinates of the other root, `otherRootPairA` and
`otherRootPairC`. -/
def otherRootPair : Fin 2 → Fin 2 → Γ(Scheme.Modules.tensorObj c.bundle t.bundle, ⊤) :=
  ![otherRootPairA c t, otherRootPairC c t]

section Coordinates

variable {c t} {x : T} {i₀ : Fin 3} {j₀ : Fin 2}
  (hc : x ∈ Stacks.Ample.nonvanishingLocus c.bundle (c.coord i₀))
  (ht : x ∈ Stacks.Ample.nonvanishingLocus t.bundle (t.coord j₀))

/-- The coordinates of the two pairs of homogeneous coordinates of the other root. -/
theorem stalkCoord_otherRootPair (a i : Fin 2) :
    stalkCoord _ (mem_nonvanishingLocus_tensorSectionsAt hc ht) (otherRootPair c t a i) =
      pairPoly (tupleCoord c hc) (tupleCoord t ht) a i := by
  rcases fin_two_cases a with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl
  · exact stalkCoord_otherRootPairA_zero hc ht
  · exact stalkCoord_otherRootPairA_one hc ht
  · exact stalkCoord_otherRootPairC_zero hc ht
  · exact stalkCoord_otherRootPairC_one hc ht

end Coordinates

/-- The module `M ⊗ L` carrying the coordinates of the other root has a global section not
vanishing at any given point. -/
theorem exists_mem_nonvanishingLocus_tensorObj (x : T) :
    ∃ e : Γ(Scheme.Modules.tensorObj c.bundle t.bundle, ⊤),
      x ∈ Stacks.Ample.nonvanishingLocus _ e := by
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus x
  exact ⟨_, mem_nonvanishingLocus_tensorSectionsAt hc ht⟩

variable {c t}

/-- **At every point of the zero locus one of the four coordinates of the other root does not
vanish**: the coefficients have no common zero and the coordinates of `t` generate. -/
theorem exists_mem_nonvanishingLocus_otherRootPair (h : IsRoot c t) (x : T) :
    ∃ a i, x ∈ Stacks.Ample.nonvanishingLocus _ (otherRootPair c t a i) := by
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus x
  obtain ⟨a, i, hai⟩ := exists_isUnit_pairPoly (quadPoly_tupleCoord_eq_zero hc ht h)
    ⟨i₀, by simp [tupleCoord, stalkCoord_self]⟩ ⟨j₀, by simp [tupleCoord, stalkCoord_self]⟩
  refine ⟨a, i, (mem_nonvanishingLocus_iff_isUnit_stalkCoord
    (mem_nonvanishingLocus_tensorSectionsAt hc ht) _).2 ?_⟩
  rw [stalkCoord_otherRootPair hc ht]
  exact hai

/-- **The two pairs of coordinates of the other root cross-multiply** on the zero locus. -/
theorem crossMultiplies_otherRootPair (h : IsRoot c t) (a b : Fin 2) :
    CrossMultiplies (otherRootPair c t a) (otherRootPair c t b) := by
  intro x
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus x
  refine (crossMultiplies_at_iff_stalkCoord (mem_nonvanishingLocus_tensorSectionsAt hc ht)
    (mem_nonvanishingLocus_tensorSectionsAt hc ht) _ _).2 fun i j => ?_
  rw [stalkCoord_otherRootPair hc ht, stalkCoord_otherRootPair hc ht,
    stalkCoord_otherRootPair hc ht, stalkCoord_otherRootPair hc ht]
  exact cross_pairPoly (quadPoly_tupleCoord_eq_zero hc ht h) a b i j

variable (c t) in
/-- The `a`-th chart of the other root: the open where the `a`-th pair of its homogeneous
coordinates generates. -/
def otherRootChart (a : Fin 2) : T.Opens :=
  ⨆ i, nvOpen (Scheme.Modules.tensorObj c.bundle t.bundle) (otherRootPair c t a i)

/-- **The two charts of the other root cover the zero locus.** -/
theorem isOpenCover_otherRootChart (h : IsRoot c t) : IsOpenCover (otherRootChart c t) := by
  refine top_le_iff.1 fun x _ => ?_
  obtain ⟨a, i, hai⟩ := exists_mem_nonvanishingLocus_otherRootPair h x
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, TopologicalSpace.Opens.mem_iSup.2 ⟨i, hai⟩⟩

variable (c t) in
/-- The other root on its `a`-th chart, as an invertible module with two generating sections:
the pullback of the `a`-th pair of homogeneous coordinates. -/
def otherRootChartTuple (a : Fin 2) : GeneratingTuple (otherRootChart c t a) 1 :=
  familyPullbackTuple (otherRootChart c t a).ι (otherRootPair c t a) fun y =>
    TopologicalSpace.Opens.mem_iSup.1 y.2

/-- **The chartwise descriptions of the other root agree on the overlaps.** -/
theorem crossMultiplies_otherRootChartTuple (h : IsRoot c t) (a b : Fin 2) :
    CrossMultiplies
      (pullbackTuple (pullback.fst (otherRootChart c t a).ι (otherRootChart c t b).ι)
        (otherRootChartTuple c t a)).coord
      (pullbackTuple (pullback.snd (otherRootChart c t a).ι (otherRootChart c t b).ι)
        (otherRootChartTuple c t b)).coord := by
  set j := pullback.fst (otherRootChart c t a).ι (otherRootChart c t b).ι ≫
    (otherRootChart c t a).ι
  have hja : ∀ y, ∃ i, j y ∈ Stacks.Ample.nonvanishingLocus _ (otherRootPair c t a i) :=
    fun y => TopologicalSpace.Opens.mem_iSup.1
      ((pullback.fst (otherRootChart c t a).ι (otherRootChart c t b).ι) y).2
  have hjb' : ∀ y, ∃ i, (pullback.snd (otherRootChart c t a).ι (otherRootChart c t b).ι ≫
      (otherRootChart c t b).ι) y ∈ Stacks.Ample.nonvanishingLocus _ (otherRootPair c t b i) :=
    fun y => TopologicalSpace.Opens.mem_iSup.1
      ((pullback.snd (otherRootChart c t a).ι (otherRootChart c t b).ι) y).2
  have hjb : ∀ y, ∃ i, j y ∈ Stacks.Ample.nonvanishingLocus _ (otherRootPair c t b i) := by
    intro y
    rw [show j = _ from pullback.condition]
    exact hjb' y
  refine CrossMultiplies.of_isomorphic (t₁ := familyPullbackTuple j (otherRootPair c t a) hja)
    (t₂ := familyPullbackTuple j (otherRootPair c t b) hjb) ?_
    (isomorphic_symm (isomorphic_pullbackTuple_familyPullbackTuple _ _ _ _ hja))
    (isomorphic_symm (isomorphic_trans (isomorphic_pullbackTuple_familyPullbackTuple _ _ _ _ hjb')
      (isomorphic_familyPullbackTuple_of_eq pullback.condition.symm _ _ hjb)))
  exact (crossMultiplies_otherRootPair h a b).pullbackGlobalSections
    (exists_mem_nonvanishingLocus_tensorObj c t) (exists_mem_nonvanishingLocus_tensorObj c t) j

/-- The other root exists and is unique as a morphism to `ℙ¹_ℤ` with the chartwise
descriptions. -/
theorem existsUnique_otherRoot (h : IsRoot c t) :
    ∃! g : T ⟶ projectiveSpaceAtUniverse.{u} 1,
      ∀ a, pointsOfHom ((otherRootChart c t a).ι ≫ g) = ⟦otherRootChartTuple c t a⟧ :=
  exists_unique_hom_of_crossMultiplies _ (isOpenCover_otherRootChart h) _
    (crossMultiplies_otherRootChartTuple h)

/-- **The other root** of the binary quadratic form `c` at its root `t`: the morphism
`T ⟶ ℙ¹_ℤ` given by `(-(B z₁ + A z₀) : A z₁)` where this pair generates and by
`(C z₀ : -(B z₀ + C z₁))` where that pair generates. -/
def otherRoot (h : IsRoot c t) : T ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  (existsUnique_otherRoot h).exists.choose

/-- **The chartwise description of the other root.** -/
theorem pointsOfHom_ι_comp_otherRoot (h : IsRoot c t) (a : Fin 2) :
    pointsOfHom ((otherRootChart c t a).ι ≫ otherRoot h) = ⟦otherRootChartTuple c t a⟧ :=
  (existsUnique_otherRoot h).exists.choose_spec a

/-! ### Characterization of the other root -/

section Characterization

variable {x : T} {i₀ : Fin 3} {j₀ : Fin 2}
  (hc : x ∈ Stacks.Ample.nonvanishingLocus c.bundle (c.coord i₀))
  (ht : x ∈ Stacks.Ample.nonvanishingLocus t.bundle (t.coord j₀))

/-- Cross-multiplication with a pair of coordinates of the other root, read in coordinates. -/
theorem crossMultiplies_at_otherRootPair_iff (s : GeneratingTuple T 1) {j : Fin 2}
    (hs : x ∈ Stacks.Ample.nonvanishingLocus s.bundle (s.coord j)) (a : Fin 2) :
    (∀ i k, (s.bundle.presheaf.Γgerm x).hom (s.coord i) ⊗ₜ[T.presheaf.stalk x]
        ((Scheme.Modules.tensorObj c.bundle t.bundle).presheaf.Γgerm x).hom
          (otherRootPair c t a k) =
      (s.bundle.presheaf.Γgerm x).hom (s.coord k) ⊗ₜ[T.presheaf.stalk x]
        ((Scheme.Modules.tensorObj c.bundle t.bundle).presheaf.Γgerm x).hom
          (otherRootPair c t a i)) ↔
      Cross (tupleCoord s hs) (pairPoly (tupleCoord c hc) (tupleCoord t ht) a) := by
  refine (crossMultiplies_at_iff_stalkCoord hs (mem_nonvanishingLocus_tensorSectionsAt hc ht)
    _ _).trans (forall₂_congr fun i k => ?_)
  rw [stalkCoord_otherRootPair hc ht, stalkCoord_otherRootPair hc ht]

/-- A member of a pair of coordinates of the other root not vanishing at `x` has a unit
coordinate. -/
theorem isUnit_pairPoly_of_mem {a i : Fin 2}
    (hx : x ∈ Stacks.Ample.nonvanishingLocus _ (otherRootPair c t a i)) :
    IsUnit (pairPoly (tupleCoord c hc) (tupleCoord t ht) a i) := by
  rw [← stalkCoord_otherRootPair hc ht]
  exact (mem_nonvanishingLocus_iff_isUnit_stalkCoord _ _).1 hx

end Characterization

/-- **The tautological pair of the other root cross-multiplies with both pairs of homogeneous
coordinates of the other root**, at every point. On the chart where a pair generates this is
the defining property, read on stalks of the open subscheme; elsewhere it follows because the
two pairs cross-multiply with each other. -/
theorem crossMultiplies_otherRoot (h : IsRoot c t) (a : Fin 2) :
    CrossMultiplies (tautological (otherRoot h)).coord (otherRootPair c t a) := by
  intro x
  obtain ⟨a', i', hx⟩ := exists_mem_nonvanishingLocus_otherRootPair h x
  have hxa : x ∈ otherRootChart c t a' := TopologicalSpace.Opens.mem_iSup.2 ⟨i', hx⟩
  have hiso : Isomorphic (pullbackTuple (otherRootChart c t a').ι (tautological (otherRoot h)))
      (otherRootChartTuple c t a') := by
    have e := pointsOfHom_ι_comp_otherRoot h a'
    rw [pointsOfHom_comp] at e
    exact Quotient.exact e
  obtain ⟨j, hj⟩ := (tautological (otherRoot h)).exists_mem_nonvanishingLocus x
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus x
  have hcm := crossMultiplies_of_isomorphic hiso
  have hinj := injective_stalkMap_of_isOpenImmersion (otherRootChart c t a').ι ⟨x, hxa⟩
  have hd := crossMultiplies_at_of_pullbackGlobalSections (otherRootChart c t a').ι hinj
    (s := (tautological (otherRoot h)).coord) (s' := otherRootPair c t a') hj
    (mem_nonvanishingLocus_tensorSectionsAt hc ht) hcm
  have hl := (crossMultiplies_at_otherRootPair_iff hc ht _ hj a').1 hd
  exact (crossMultiplies_at_otherRootPair_iff hc ht _ hj a).2
    (hl.trans_of_isUnit (cross_pairPoly (quadPoly_tupleCoord_eq_zero hc ht h) a' a)
      (isUnit_pairPoly_of_mem hc ht hx))

/-- **The other root is the only morphism whose tautological pair cross-multiplies with both
pairs of homogeneous coordinates of the other root.** -/
theorem eq_otherRoot_of_crossMultiplies (h : IsRoot c t) {g : T ⟶ projectiveSpaceAtUniverse.{u} 1}
    (hg : ∀ a, CrossMultiplies (tautological g).coord (otherRootPair c t a)) :
    g = otherRoot h := by
  refine pointsOfHom_injective (Quotient.sound (isomorphic_of_crossMultiplies fun x => ?_))
  obtain ⟨a, i, hx⟩ := exists_mem_nonvanishingLocus_otherRootPair h x
  obtain ⟨j, hj⟩ := (tautological g).exists_mem_nonvanishingLocus x
  obtain ⟨j', hj'⟩ := (tautological (otherRoot h)).exists_mem_nonvanishingLocus x
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus x
  have h₁ := (crossMultiplies_at_otherRootPair_iff hc ht _ hj a).1 (hg a x)
  have h₂ := (crossMultiplies_at_otherRootPair_iff hc ht _ hj' a).1
    (crossMultiplies_otherRoot h a x)
  exact (crossMultiplies_at_iff_stalkCoord hj hj' _ _).2
    (h₁.trans_of_isUnit h₂.symm (isUnit_pairPoly_of_mem hc ht hx))

/-- **The other root is a root.** -/
theorem isRoot_otherRoot (h : IsRoot c t) : IsRoot c (tautological (otherRoot h)) := by
  refine isRoot_of_forall_quadPoly _ _ fun x => ?_
  obtain ⟨a, i, hx⟩ := exists_mem_nonvanishingLocus_otherRootPair h x
  obtain ⟨j, hj⟩ := (tautological (otherRoot h)).exists_mem_nonvanishingLocus x
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus x
  exact ⟨i₀, j, hc, hj, quadPoly_eq_zero_of_cross (quadPoly_tupleCoord_eq_zero hc ht h)
    ((crossMultiplies_at_otherRootPair_iff hc ht _ hj a).1 (crossMultiplies_otherRoot h a x))
    (isUnit_pairPoly_of_mem hc ht hx)⟩

/-- **The other root of the other root is the root**: the other root of `c` at the other root of
`t` is the morphism classifying `t`. -/
theorem otherRoot_otherRoot (h : IsRoot c t) :
    otherRoot (isRoot_otherRoot h) = (pointsEquiv T 1).symm ⟦t⟧ := by
  refine (eq_otherRoot_of_crossMultiplies (isRoot_otherRoot h) fun a => ?_).symm
  have hiso : Isomorphic t (tautological ((pointsEquiv T 1).symm ⟦t⟧)) :=
    Quotient.exact ((pointsEquiv T 1).apply_symm_apply ⟦t⟧).symm
  refine (crossMultiplies_coord_iff_of_isomorphic hiso
    (exists_mem_nonvanishingLocus_tensorObj c _)).1 fun x => ?_
  obtain ⟨j, hj⟩ := (tautological (otherRoot h)).exists_mem_nonvanishingLocus x
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus x
  exact (crossMultiplies_at_otherRootPair_iff hc hj _ ht a).2 (cross_pairPoly_swap
    ((crossMultiplies_at_otherRootPair_iff hc ht _ hj a).1 (crossMultiplies_otherRoot h a x)))

/-! ### Naturality -/

section Naturality

variable {Y : Scheme.{u}}

/-- The coordinates of a pulled-back tuple are the images of the coordinates under `f^♯`. -/
theorem tupleCoord_pullbackTuple {n : ℕ} (f : Y ⟶ T) (s : GeneratingTuple T n) {y : Y}
    {j : Fin (n + 1)} (hs : f y ∈ Stacks.Ample.nonvanishingLocus s.bundle (s.coord j)) :
    tupleCoord (pullbackTuple f s) (mem_nonvanishingLocus_pullbackGlobalSections f hs) =
      fun i => (f.stalkMap y).hom (tupleCoord s hs i) :=
  funext fun _ => stalkCoord_pullbackGlobalSections f hs _

/-- **Roots pull back.** -/
theorem isRoot_pullbackTuple (h : IsRoot c t) (f : Y ⟶ T) :
    IsRoot (pullbackTuple f c) (pullbackTuple f t) := by
  refine isRoot_of_forall_quadPoly _ _ fun y => ?_
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus (f y)
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus (f y)
  refine ⟨i₀, j₀, mem_nonvanishingLocus_pullbackGlobalSections f hc,
    mem_nonvanishingLocus_pullbackGlobalSections f ht, ?_⟩
  rw [tupleCoord_pullbackTuple f c hc, tupleCoord_pullbackTuple f t ht, ← map_quadPoly,
    quadPoly_tupleCoord_eq_zero hc ht h, map_zero]

/-- **The other root is natural**: the other root of the pulled-back form at the pulled-back
root is the composite with the other root. -/
theorem otherRoot_pullbackTuple (h : IsRoot c t) (f : Y ⟶ T) :
    otherRoot (isRoot_pullbackTuple h f) = f ≫ otherRoot h := by
  refine (eq_otherRoot_of_crossMultiplies _ fun a => ?_).symm
  have hiso : Isomorphic (pullbackTuple f (tautological (otherRoot h)))
      (tautological (f ≫ otherRoot h)) :=
    isomorphic_symm (Quotient.exact (pointsOfHom_comp f (otherRoot h)))
  refine (crossMultiplies_coord_iff_of_isomorphic hiso
    (exists_mem_nonvanishingLocus_tensorObj (pullbackTuple f c) (pullbackTuple f t))).1
      fun y => ?_
  obtain ⟨j, hj⟩ := (tautological (otherRoot h)).exists_mem_nonvanishingLocus (f y)
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus (f y)
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus (f y)
  refine (crossMultiplies_at_otherRootPair_iff (c := pullbackTuple f c) (t := pullbackTuple f t)
    (mem_nonvanishingLocus_pullbackGlobalSections f hc)
    (mem_nonvanishingLocus_pullbackGlobalSections f ht)
    (pullbackTuple f (tautological (otherRoot h)))
    (mem_nonvanishingLocus_pullbackGlobalSections f hj) a).2 ?_
  rw [tupleCoord_pullbackTuple f c hc, tupleCoord_pullbackTuple f t ht,
    tupleCoord_pullbackTuple f _ hj]
  have e := cross_map (f.stalkMap y).hom
    ((crossMultiplies_at_otherRootPair_iff hc ht _ hj a).1 (crossMultiplies_otherRoot h a (f y)))
  rwa [show (fun i => (f.stalkMap y).hom (pairPoly (tupleCoord c hc) (tupleCoord t ht) a i)) =
    pairPoly (fun i => (f.stalkMap y).hom (tupleCoord c hc i))
      (fun i => (f.stalkMap y).hom (tupleCoord t ht i)) a from
    funext (map_pairPoly _ _ _ a)] at e

end Naturality

/-! ### Invariance under the identification of Tag 01NE -/

section Congr

/-- Isomorphic tuples have the same coordinates relative to corresponding members. -/
theorem exists_tupleCoord_eq_of_isomorphic {n : ℕ} {s s' : GeneratingTuple T n}
    (hiso : Isomorphic s s') {x : T} {j : Fin (n + 1)}
    (hj : x ∈ Stacks.Ample.nonvanishingLocus s.bundle (s.coord j)) :
    ∃ hj' : x ∈ Stacks.Ample.nonvanishingLocus s'.bundle (s'.coord j),
      tupleCoord s' hj' = tupleCoord s hj := by
  obtain ⟨β, hβ⟩ := hiso
  have hj'' : x ∈ Stacks.Ample.nonvanishingLocus s'.bundle
      (Scheme.Modules.Hom.app β.hom ⊤ (s.coord j)) :=
    (mem_nonvanishingLocus_app_hom_iff β _ x).2 hj
  have hj' : x ∈ Stacks.Ample.nonvanishingLocus s'.bundle (s'.coord j) := by
    rw [← hβ j]
    exact hj''
  refine ⟨hj', funext fun i => ?_⟩
  show stalkCoord _ hj' (s'.coord i) = stalkCoord _ hj (s.coord i)
  rw [← stalkCoord_app_hom β hj hj'' (s.coord i)]
  simp only [hβ]

variable {c' : GeneratingTuple T 2} {t' : GeneratingTuple T 1}

/-- **Being a root is invariant under the identification of Tag 01NE.** -/
theorem isRoot_of_isomorphic (h : IsRoot c t) (hc : Isomorphic c c') (ht : Isomorphic t t') :
    IsRoot c' t' := by
  refine isRoot_of_forall_quadPoly _ _ fun x => ?_
  obtain ⟨i₀, hx⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, hy⟩ := t.exists_mem_nonvanishingLocus x
  obtain ⟨hx', ex⟩ := exists_tupleCoord_eq_of_isomorphic hc hx
  obtain ⟨hy', ey⟩ := exists_tupleCoord_eq_of_isomorphic ht hy
  exact ⟨i₀, j₀, hx', hy', by rw [ex, ey]; exact quadPoly_tupleCoord_eq_zero hx hy h⟩

/-- **The other root is invariant under the identification of Tag 01NE.** -/
theorem otherRoot_congr (h : IsRoot c t) (hc : Isomorphic c c') (ht : Isomorphic t t') :
    otherRoot (isRoot_of_isomorphic h hc ht) = otherRoot h := by
  refine (eq_otherRoot_of_crossMultiplies _ fun a x => ?_).symm
  obtain ⟨j, hj⟩ := (tautological (otherRoot h)).exists_mem_nonvanishingLocus x
  obtain ⟨i₀, hx⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, hy⟩ := t.exists_mem_nonvanishingLocus x
  obtain ⟨hx', ex⟩ := exists_tupleCoord_eq_of_isomorphic hc hx
  obtain ⟨hy', ey⟩ := exists_tupleCoord_eq_of_isomorphic ht hy
  refine (crossMultiplies_at_otherRootPair_iff hx' hy' _ hj a).2 ?_
  rw [ex, ey]
  exact (crossMultiplies_at_otherRootPair_iff hx hy _ hj a).1 (crossMultiplies_otherRoot h a x)

end Congr

/-! ### The pullback of `𝒪(1)` along the other root -/

section Twist

variable (h : IsRoot c t)

/-- The sections `T'₀ ⊗ z₀², T'₁ ⊗ z₀², T'₀ ⊗ z₁², T'₁ ⊗ z₁²` of `N ⊗ L²`, for `N` the pullback
of `𝒪(1)` along the other root with its sections `T'ᵢ`, and `L` with sections `zᵢ` the root. -/
def otherRootTwistTuple : GeneratingTuple T 3 where
  bundle := Scheme.Modules.tensorObj (tautological (otherRoot h)).bundle
    (Scheme.Modules.tensorObj t.bundle t.bundle)
  isInvertible := inferInstance
  coord := ![tsa ((tautological (otherRoot h)).coord 0) (tsa (t.coord 0) (t.coord 0)),
    tsa ((tautological (otherRoot h)).coord 1) (tsa (t.coord 0) (t.coord 0)),
    tsa ((tautological (otherRoot h)).coord 0) (tsa (t.coord 1) (t.coord 1)),
    tsa ((tautological (otherRoot h)).coord 1) (tsa (t.coord 1) (t.coord 1))]
  generates := by
    refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
    obtain ⟨j, hj⟩ := (tautological (otherRoot h)).exists_mem_nonvanishingLocus x
    obtain ⟨l, hl⟩ := t.exists_mem_nonvanishingLocus x
    have hm := mem_nonvanishingLocus_tensorSectionsAt hj
      (mem_nonvanishingLocus_tensorSectionsAt hl hl)
    rcases fin_two_cases j with rfl | rfl <;> rcases fin_two_cases l with rfl | rfl
    · exact ⟨0, hm⟩
    · exact ⟨2, hm⟩
    · exact ⟨1, hm⟩
    · exact ⟨3, hm⟩

/-- The four homogeneous coordinates `C z₀, -(B z₀ + C z₁), -(B z₁ + A z₀), A z₁` of the other
root, as generating sections of `M ⊗ L`. -/
def otherRootPairTuple : GeneratingTuple T 3 where
  bundle := Scheme.Modules.tensorObj c.bundle t.bundle
  isInvertible := inferInstance
  coord := ![otherRootPair c t 1 0, otherRootPair c t 1 1, otherRootPair c t 0 0,
    otherRootPair c t 0 1]
  generates := by
    refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
    obtain ⟨a, i, hx⟩ := exists_mem_nonvanishingLocus_otherRootPair h x
    rcases fin_two_cases a with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl
    · exact ⟨2, hx⟩
    · exact ⟨3, hx⟩
    · exact ⟨0, hx⟩
    · exact ⟨1, hx⟩

/-- **The pullback of `𝒪(1)` along the other root**: `N ⊗ L² ≅ M ⊗ L`, by an isomorphism carrying
`T'₀ ⊗ z₀², T'₁ ⊗ z₀², T'₀ ⊗ z₁², T'₁ ⊗ z₁²` to `C z₀, -(B z₀ + C z₁), -(B z₁ + A z₀), A z₁`. On
`z₁ ≠ 0` the other root is `(-(B z₁ + A z₀) : A z₁)` and the isomorphism is `T'ᵢ ⊗ z₁² ↦ ` that
pair; on `z₀ ≠ 0` it is `(C z₀ : -(B z₀ + C z₁))` and the isomorphism is `T'ᵢ ⊗ z₀² ↦ ` that
pair; the two agree because `(C z₀, -(B z₀ + C z₁)) z₁² = (-(B z₁ + A z₀), A z₁) z₀²` on the
quadric. -/
theorem isomorphic_otherRootTwistTuple :
    Isomorphic (otherRootTwistTuple h) (otherRootPairTuple h) := by
  refine isomorphic_of_crossMultiplies fun x => ?_
  obtain ⟨j, hj⟩ := (tautological (otherRoot h)).exists_mem_nonvanishingLocus x
  obtain ⟨i₀, hc⟩ := c.exists_mem_nonvanishingLocus x
  obtain ⟨j₀, ht⟩ := t.exists_mem_nonvanishingLocus x
  have hm := mem_nonvanishingLocus_tensorSectionsAt hj
    (mem_nonvanishingLocus_tensorSectionsAt ht ht)
  have hct := mem_nonvanishingLocus_tensorSectionsAt hc ht
  have e₁ : (fun k => stalkCoord (otherRootTwistTuple h).bundle hm
      ((otherRootTwistTuple h).coord k)) =
      ![tupleCoord _ hj 0 * (tupleCoord t ht 0 * tupleCoord t ht 0),
        tupleCoord _ hj 1 * (tupleCoord t ht 0 * tupleCoord t ht 0),
        tupleCoord _ hj 0 * (tupleCoord t ht 1 * tupleCoord t ht 1),
        tupleCoord _ hj 1 * (tupleCoord t ht 1 * tupleCoord t ht 1)] := by
    funext k
    fin_cases k <;>
      exact (stalkCoord_tensorSectionsAt hj
          (mem_nonvanishingLocus_tensorSectionsAt ht ht) _ _).trans
        (congrArg (_ * ·) (stalkCoord_tensorSectionsAt ht ht _ _))
  have e₂ : (fun k => stalkCoord (otherRootPairTuple h).bundle hct
      ((otherRootPairTuple h).coord k)) =
      ![pairPoly (tupleCoord c hc) (tupleCoord t ht) 1 0,
        pairPoly (tupleCoord c hc) (tupleCoord t ht) 1 1,
        pairPoly (tupleCoord c hc) (tupleCoord t ht) 0 0,
        pairPoly (tupleCoord c hc) (tupleCoord t ht) 0 1] := by
    funext k
    fin_cases k
    · exact stalkCoord_otherRootPair hc ht 1 0
    · exact stalkCoord_otherRootPair hc ht 1 1
    · exact stalkCoord_otherRootPair hc ht 0 0
    · exact stalkCoord_otherRootPair hc ht 0 1
  have key : Cross (fun k => stalkCoord (otherRootTwistTuple h).bundle hm
      ((otherRootTwistTuple h).coord k))
      (fun k => stalkCoord (otherRootPairTuple h).bundle hct ((otherRootPairTuple h).coord k)) := by
    rw [e₁, e₂]
    exact cross_twist (quadPoly_tupleCoord_eq_zero hc ht h)
      ((crossMultiplies_at_otherRootPair_iff hc ht _ hj 0).1 (crossMultiplies_otherRoot h 0 x))
      ((crossMultiplies_at_otherRootPair_iff hc ht _ hj 1).1 (crossMultiplies_otherRoot h 1 x))
  exact (crossMultiplies_at_iff_stalkCoord hm hct _ _).2 key

/-- **The pullback of `𝒪(1)` along the other root**, as an isomorphism `N ⊗ L² ≅ M ⊗ L` of
invertible modules: see `Stacks.BinaryQuadric.isomorphic_otherRootTwistTuple`. -/
def otherRootTwistIso :
    Scheme.Modules.tensorObj (tautological (otherRoot h)).bundle
        (Scheme.Modules.tensorObj t.bundle t.bundle) ≅
      Scheme.Modules.tensorObj c.bundle t.bundle :=
  (isomorphic_otherRootTwistTuple h).choose

end Twist

end Stacks.BinaryQuadric

end
