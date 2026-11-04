module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantIdeal
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.LocalUnitBasis

/-!
# Sections of a finite locally free morphism on a basis whose first vector is the unit

Let `f : Y ⟶ X` be finite locally free and let `x` be a point of `X` lying in the image of `f`.
Then `x` has an affine open neighbourhood `U` such that `Γ(Y, f⁻¹(U))` is free of positive rank
over `Γ(X, U)` on a basis whose first vector is `1`.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_basis_one`: the neighbourhood, the rank and the basis.

## Implementation notes

Two shrinkings of an affine open neighbourhood are needed, each to a principal open, and each
transports a statement about the sections along the two localizations
`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen` on the two schemes.

The first produces freeness: over an affine open the sections are a finite projective module
(Tag 02KA), hence become free after inverting one element outside the prime of `x`, and
`Stacks.Discriminant.free_of_localized_free` transports that freeness to the sections over the
principal open cut out by the element.

The second produces the unit as the first basis vector: the coordinates of `1` in any basis
generate the unit ideal (Tag 05YQ), so one of them, say the `i`-th, is nonzero at `x`; over the
principal open that coordinate cuts out, the basis localizes
(`Module.Basis.localizationLocalization`) and the `i`-th coordinate of `1` becomes invertible,
which is the hypothesis of `AlgebraicGeometry.FiniteFreeAlgebra.basisOne`. That step is stated
for abstract localizations, in `AlgebraicGeometry.exists_basis_one_of_isLocalization`.

Positivity of the rank is where the hypothesis on the image is used: a basis indexed by `Fin 0`
makes the sections subsingleton, while a point of the fibre makes them nontrivial.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Discriminant

universe u v

namespace AlgebraicGeometry

/-- Inverting one coordinate of `1` in a basis of a free algebra produces a basis whose first
vector is the unit: that coordinate becomes invertible in the localization, while the basis
localizes. -/
theorem exists_basis_one_of_isLocalization (R A R' A' : Type v) [CommRing R] [CommRing A]
    [CommRing R'] [CommRing A'] (a : R) [Algebra R A] [Algebra R R']
    [IsLocalization (.powers a) R'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    [IsLocalization (Algebra.algebraMapSubmonoid A (.powers a)) A']
    [Algebra R' A'] [IsScalarTower R R' A'] {d : ℕ} [NeZero d]
    (b : Module.Basis (Fin d) R A) (i : Fin d) (ha : a = b.repr 1 i) :
    ∃ c : Module.Basis (Fin d) R' A', c 0 = 1 := by
  let c := b.localizationLocalization R' (.powers a) A'
  have hunit : IsUnit (c.repr 1 i) := by
    rw [← map_one (algebraMap A A'), Module.Basis.localizationLocalization_repr_algebraMap, ← ha]
    exact IsLocalization.map_units R' (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)
  exact ⟨_, FiniteFreeAlgebra.basisOne_zero c i hunit⟩

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [Stacks.Morphisms.IsFiniteLocallyFree f]

/-- A property of the algebra of sections over the principal open of `a`, which holds for every
pair of localizations of the sections over `V` at the powers of `a`. -/
private theorem property_basicOpen_sections {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V))
    (P : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S], Prop)
    (h : letI := (f.app V).hom.toAlgebra
      ∀ (R' A' : Type u) [CommRing R'] [CommRing A'] [Algebra R' A'] [Algebra Γ(X, V) R']
        [Algebra Γ(X, V) A'] [Algebra Γ(Y, f ⁻¹ᵁ V) A'] [IsScalarTower Γ(X, V) Γ(Y, f ⁻¹ᵁ V) A']
        [IsScalarTower Γ(X, V) R' A'] [IsLocalization (.powers a) R']
        [IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ V) (.powers a)) A'],
        P R' A') :
    letI := (f.app (X.basicOpen a)).hom.toAlgebra
    P Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) := by
  let : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let : Algebra Γ(X, V) Γ(X, X.basicOpen a) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let : IsLocalization (.powers a) Γ(X, X.basicOpen a) := hV.isLocalization_basicOpen a
  let : Algebra Γ(Y, f ⁻¹ᵁ V) Γ(Y, Y.basicOpen (f.app V a)) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le (f.app V a))).op).hom.toAlgebra
  let : Algebra Γ(X, V) Γ(Y, Y.basicOpen (f.app V a)) :=
    ((algebraMap Γ(Y, f ⁻¹ᵁ V) Γ(Y, Y.basicOpen (f.app V a))).comp
      (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V))).toAlgebra
  let : IsScalarTower Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, Y.basicOpen (f.app V a)) :=
    IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  let : Algebra Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen (f.app V a)) :=
    (f.appLE (X.basicOpen a) (Y.basicOpen (f.app V a))
      (Scheme.preimage_basicOpen f a).ge).hom.toAlgebra
  let : IsScalarTower Γ(X, V) Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen (f.app V a)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have hX : f.app V ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le (f.app V a))).op =
        f.appLE V (Y.basicOpen (f.app V a)) (Y.basicOpen_le (f.app V a)) := by
      rw [f.app_eq_appLE, f.appLE_map]
    have hY : X.presheaf.map (homOfLE (X.basicOpen_le a)).op ≫
        f.appLE (X.basicOpen a) (Y.basicOpen (f.app V a))
          (Scheme.preimage_basicOpen f a).ge =
        f.appLE V (Y.basicOpen (f.app V a)) (Y.basicOpen_le (f.app V a)) := by
      rw [f.map_appLE]
    have h := congrArg CommRingCat.Hom.hom (hX.trans hY.symm)
    simpa only [CommRingCat.hom_comp, RingHom.algebraMap_toAlgebra] using h
  have hb : f.app V a = algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V) a := rfl
  let : IsLocalization.Away (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V) a)
      Γ(Y, Y.basicOpen (f.app V a)) := by
    rw [← hb]
    exact (IsAffineHom.isAffine_preimage V hV).isLocalization_basicOpen (f.app V a)
  let : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ V) (.powers a))
      Γ(Y, Y.basicOpen (f.app V a)) := inferInstance
  have hh := (f.appLE_congr le_rfl rfl (Scheme.preimage_basicOpen f a)
    (fun {R S} g ↦ let := g.hom.toAlgebra; P R S)).mpr
    (h Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen (f.app V a)))
  rwa [Scheme.Hom.appLE_eq_app] at hh

/-- **A finite locally free morphism is, over a small enough affine open, free on a basis whose
first vector is the unit.** Every point `x` of the target lying in the image of `f` has an affine
open neighbourhood `U` over which `Γ(Y, f⁻¹(U))` is free of positive rank `d` over `Γ(X, U)` on a
basis `b` with `b 0 = 1`. -/
theorem exists_isAffineOpen_basis_one (x : X) (hx : ∃ y : Y, f.base y = x) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (d : ℕ) (_ : NeZero d),
      letI := (f.app U).hom.toAlgebra
      ∃ b : Module.Basis (Fin d) Γ(X, U) Γ(Y, f ⁻¹ᵁ U), b 0 = 1 := by
  classical
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show f.base y ∈ (⊤ : X.Opens) from trivial)
  let : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let : Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) :=
    (Stacks.Norm.module_finite_and_projective_sections f ⟨V, hV⟩).1
  let : Module.Projective Γ(X, V) Γ(Y, f ⁻¹ᵁ V) :=
    (Stacks.Norm.module_finite_and_projective_sections f ⟨V, hV⟩).2
  obtain ⟨a, haV, hfree⟩ := exists_away_free_at_prime Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
    (hV.primeIdealOf ⟨_, hxV⟩)
  have hxa : f.base y ∈ X.basicOpen a := by
    rw [← hV.fromSpec_image_basicOpen]
    exact ⟨hV.primeIdealOf ⟨_, hxV⟩, haV, hV.fromSpec_primeIdealOf ⟨_, hxV⟩⟩
  have hVa : IsAffineOpen (X.basicOpen a) := hV.basicOpen a
  -- the first shrinking: over `X.basicOpen a` the sections are free
  have hfreeAway : let := (f.app (X.basicOpen a)).hom.toAlgebra
      Module.Free Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    property_basicOpen_sections f hV a (fun R S _ _ _ ↦ Module.Free R S)
      fun R' A' _ _ _ _ _ _ _ _ _ _ ↦ free_of_localized_free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) R' A' a hfree
  let : Algebra Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    (f.app (X.basicOpen a)).hom.toAlgebra
  let : Module.Free Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) := hfreeAway
  let : Module.Finite Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    (Stacks.Norm.module_finite_and_projective_sections f ⟨X.basicOpen a, hVa⟩).1
  -- a basis of the free sections, indexed by `Fin d`
  set d := Fintype.card
    (Module.Free.ChooseBasisIndex Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a))
  let b : Module.Basis (Fin d) Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    (Module.Free.chooseBasis Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).reindex
      (Fintype.equivFin _)
  -- the rank is positive, since the fibre over `x` is nonempty
  have hntY : Nontrivial Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    ((IsAffineHom.isAffine_preimage (X.basicOpen a) hVa).primeIdealOf ⟨y, hxa⟩).nontrivial
  have hdne : NeZero d := by
    refine ⟨fun h => ?_⟩
    have : IsEmpty (Fin d) := h ▸ inferInstance
    have hsum := b.sum_repr 1
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact one_ne_zero hsum.symm
  -- the second shrinking: the unit becomes the first basis vector
  obtain ⟨i, hi⟩ : ∃ i : Fin d, b.repr 1 i ∉ (hVa.primeIdealOf ⟨_, hxa⟩).asIdeal := by
    by_contra! hc
    refine (hVa.primeIdealOf ⟨_, hxa⟩).isPrime.ne_top (top_le_iff.mp ?_)
    rw [← FiniteFreeAlgebra.span_range_repr_one_eq_top b]
    exact Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hc j)
  obtain ⟨c, hcdef⟩ : ∃ c : Γ(X, X.basicOpen a), c = b.repr 1 i := ⟨_, rfl⟩
  have hxc : f.base y ∈ X.basicOpen c := by
    rw [hcdef, ← hVa.fromSpec_image_basicOpen]
    exact ⟨hVa.primeIdealOf ⟨_, hxa⟩, hi, hVa.fromSpec_primeIdealOf ⟨_, hxa⟩⟩
  refine ⟨X.basicOpen c, hVa.basicOpen c, hxc, d, hdne, ?_⟩
  exact property_basicOpen_sections f hVa c
    (fun R S _ _ _ ↦ ∃ b : Module.Basis (Fin d) R S, b 0 = 1)
    fun R' A' _ _ _ _ _ _ _ _ _ _ ↦
      exists_basis_one_of_isLocalization Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) R' A' c b i
        hcdef

end AlgebraicGeometry

end
