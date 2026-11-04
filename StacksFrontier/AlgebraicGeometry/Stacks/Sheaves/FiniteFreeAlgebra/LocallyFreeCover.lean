module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.LocalUnitBasis

/-!
# A finite locally free algebra is a free structure over a standard open cover

Let `A` be a commutative algebra over a commutative ring `R` which is finite locally free of
rank `d > 0` as an `R`-module — not assumed free. Then the spectrum of `R` is covered by
standard opens over each of which `A` becomes the algebra of a free `d`-dimensional structure.

This is clause (b) of the proof of Stacks 05YQ over an affine base, carrying the hypothesis the
source carries. The sibling file
`StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.LocalUnitBasis` proves the same
conclusion for an algebra that is already *free* on a given basis; here the basis is produced,
after a first localization, from finite local freeness itself.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.awayBasis`: a basis of the away-localization of `A`,
  read as a basis of the base change of `A` along that localization.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.exists_span_eq_top_structure`: there is a family of
  elements of `R` generating the unit ideal such that over each of the localizations away from
  them `A` is the algebra of a free `d`-dimensional structure.
* `AlgebraicGeometry.FiniteFreeAlgebra.exists_span_eq_top_specOverIso`: the same, read as an
  isomorphism of schemes over the localized base.
* `AlgebraicGeometry.FiniteFreeAlgebra.exists_span_eq_top_structure_of_specMap`: the same, with
  the hypothesis in the form of the morphism property of the structural morphism of spectra,
  which is the shape in which a degree-`d` finite locally free cover of an affine base arrives.

## Implementation notes

Two localizations are needed and they are taken in one step. Finite local freeness supplies a
family `f : ι → R` generating the unit ideal with `A` free over each `R_{f i}`; the coordinates
of `1` in such a basis generate the unit ideal of `R_{f i}`, so a second localization is needed
before the unit can be used as the first basis vector. Rather than localize twice, each
coordinate `s` of `1` is written as `a / (f i)^n` with `a : R` through
`IsLocalization.Away.sec`, and the single element `a * f i` of `R` is used: the localization of
`R` away from it receives `R_{f i}` by `IsLocalization.Away.awayToAwayLeft`, and `s` becomes
invertible there because it is associated to the image of `a`. The conclusion is therefore
stated for `Localization.Away` of an element of `R`, with no iterated localization and no
appeal to uniqueness of localizations.

That the resulting family generates the unit ideal is proved by contradiction at a maximal
ideal `𝔪`: some `f i` avoids `𝔪`, so `𝔪` is disjoint from the powers of `f i` and its extension
to `R_{f i}` is prime, hence proper; every coordinate of `1` lies in that extension, which
contradicts the fact that those coordinates generate the unit ideal.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ} [NeZero d]

/-- A basis of the localization of `A` away from `r`, transported along the identification of
that localization with the base change of `A` to `Localization.Away r`. -/
noncomputable def awayBasis (r : R)
    (b : Module.Basis (Fin d) (Localization.Away r)
      (LocalizedModule (Submonoid.powers r) A)) :
    Module.Basis (Fin d) (Localization.Away r) (Localization.Away r ⊗[R] A) :=
  b.map (LocalizedModule.isBaseChange (Submonoid.powers r) A).equiv.symm

/-- The single localization that makes a coordinate of the unit invertible. If `a : R` becomes,
in the localization away from `r`, an associate of the `j`-th coordinate of `1` in a basis `b`
of the base change of `A`, then over the localization away from `a * r` the algebra `A` is the
algebra of a free `d`-dimensional structure. -/
private theorem exists_structure_away_mul (r a : R)
    (b : Module.Basis (Fin d) (Localization.Away r) (Localization.Away r ⊗[R] A)) (j : Fin d)
    (hu : Associated (algebraMap R (Localization.Away r) a) (b.repr 1 j)) :
    ∃ m : FiniteFreeAlgebra (Localization.Away (a * r)) d,
      Nonempty ((Localization.Away (a * r) ⊗[R] A) ≃ₐ[Localization.Away (a * r)] Carrier m) := by
  let : Algebra (Localization.Away r) (Localization.Away (a * r)) :=
    (IsLocalization.Away.awayToAwayLeft (S := Localization.Away r)
      (P := Localization.Away (a * r)) r a).toAlgebra
  have : IsScalarTower R (Localization.Away r) (Localization.Away (a * r)) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away r)
        (P := Localization.Away (a * r)) r a x).symm
  have hA : IsUnit (algebraMap (Localization.Away r) (Localization.Away (a * r))
      (algebraMap R (Localization.Away r) a)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (a * r)) (a * r)
      (dvd_mul_right a r)
  obtain ⟨u, hu⟩ := hu
  have hunit : IsUnit (algebraMap (Localization.Away r) (Localization.Away (a * r))
      (b.repr 1 j)) := by
    rw [← hu, map_mul]
    exact hA.mul (IsUnit.map _ u.isUnit)
  exact ⟨structureOfIsUnit _ b j hunit,
    ⟨(Algebra.TensorProduct.cancelBaseChange R (Localization.Away r) _ _ A).symm.trans
      (algEquivCarrierOfIsUnit _ b j hunit)⟩⟩

/-- **Clause (b) of the proof of Stacks 05YQ over an affine base.** A commutative algebra that
is finite locally free of positive rank `d` over `R` is, over each member of a standard open
cover of `Spec R`, the algebra of a free `d`-dimensional structure. -/
theorem exists_span_eq_top_structure (h : Module.IsFiniteLocallyFreeOfRank R A d) :
    ∃ (ι : Type u) (g : ι → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, ∃ m : FiniteFreeAlgebra (Localization.Away (g i)) d,
        Nonempty ((Localization.Away (g i) ⊗[R] A) ≃ₐ[Localization.Away (g i)] Carrier m) := by
  classical
  obtain ⟨ι, f, hspan, hb⟩ := h
  let b i := awayBasis (f i) (hb i).some
  refine ⟨Σ _ : ι, Fin d,
    fun p => (IsLocalization.Away.sec (f p.1) ((b p.1).repr 1 p.2)).1 * f p.1, ?_, ?_⟩
  · by_contra hne
    obtain ⟨M, hM, hsub⟩ := Ideal.exists_le_maximal _ hne
    have hprime : M.IsPrime := hM.isPrime
    have hex : ∃ i, f i ∉ M := by
      by_contra hc
      push Not at hc
      have hle : Ideal.span (Set.range f) ≤ M :=
        Ideal.span_le.mpr (by rintro x ⟨i, rfl⟩; exact hc i)
      rw [hspan, top_le_iff] at hle
      exact hM.ne_top hle
    obtain ⟨i, hi⟩ := hex
    have hdisj : Disjoint ((Submonoid.powers (f i) : Submonoid R) : Set R) (M : Set R) := by
      rw [Set.disjoint_left]
      rintro x hx hxM
      obtain ⟨n, rfl⟩ := hx
      exact hi (hprime.mem_of_pow_mem n hxM)
    have hPprime : (Ideal.map (algebraMap R (Localization.Away (f i))) M).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (f i))
        (Localization.Away (f i)) M hprime hdisj
    have hle : Ideal.span (Set.range fun j => (b i).repr 1 j) ≤
        Ideal.map (algebraMap R (Localization.Away (f i))) M := by
      refine Ideal.span_le.mpr ?_
      rintro x ⟨j, rfl⟩
      dsimp only
      have ha : (IsLocalization.Away.sec (f i) ((b i).repr 1 j)).1 ∈ M := by
        have hmem : (IsLocalization.Away.sec (f i) ((b i).repr 1 j)).1 * f i ∈ M :=
          hsub (Ideal.subset_span ⟨⟨i, j⟩, rfl⟩)
        rcases hprime.mem_or_mem hmem with hc | hc
        · exact hc
        · exact absurd hc hi
      obtain ⟨u, hu⟩ := IsLocalization.Away.associated_sec_fst (x := f i) ((b i).repr 1 j)
      rw [← hu]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    rw [span_range_repr_one_eq_top (b i), top_le_iff] at hle
    exact hPprime.ne_top hle
  · rintro ⟨i, j⟩
    exact exists_structure_away_mul (f i) _ (b i) j
      (IsLocalization.Away.associated_sec_fst (x := f i) ((b i).repr 1 j))

/-- **Clause (b) of the proof of Stacks 05YQ over an affine base, for spectra.** The spectrum of
a commutative algebra that is finite locally free of positive rank `d` over `R` is, over each
member of a standard open cover of `Spec R`, the spectrum of a free `d`-dimensional
structure. -/
theorem exists_span_eq_top_specOverIso (h : Module.IsFiniteLocallyFreeOfRank R A d) :
    ∃ (ι : Type u) (g : ι → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, ∃ m : FiniteFreeAlgebra (Localization.Away (g i)) d,
        Nonempty (specOver (Localization.Away (g i)) (Localization.Away (g i) ⊗[R] A) ≅
          specCover m) := by
  obtain ⟨ι, g, hspan, hcov⟩ := exists_span_eq_top_structure h
  refine ⟨ι, g, hspan, fun i => ?_⟩
  obtain ⟨m, ⟨e⟩⟩ := hcov i
  exact ⟨m, ⟨specOverMapIso e.symm⟩⟩

/-- **Clause (b) of the proof of Stacks 05YQ over an affine base**, with the hypothesis in the
form of the morphism property: if `Spec A ⟶ Spec R` is finite locally free of degree `d > 0`,
then over each member of a standard open cover of `Spec R` the algebra `A` is the algebra of a
free `d`-dimensional structure. -/
theorem exists_span_eq_top_structure_of_specMap
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) d) :
    ∃ (ι : Type u) (g : ι → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, ∃ m : FiniteFreeAlgebra (Localization.Away (g i)) d,
        Nonempty ((Localization.Away (g i) ⊗[R] A) ≃ₐ[Localization.Away (g i)] Carrier m) :=
  exists_span_eq_top_structure ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff d).mp h)

end AlgebraicGeometry.FiniteFreeAlgebra

end
