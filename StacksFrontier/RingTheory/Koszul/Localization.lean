module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange

/-!
# Koszul-regularity and `H₁`-regularity are local on the spectrum

Let `R` be a commutative ring and `f₁, …, f_r ∈ R`. The Koszul complex `K_•(f₁, …, f_r)` is a
bounded complex of finite free modules, so each of its homology modules is an `R`-module whose
formation commutes with flat base change
(`KoszulC.homology_baseChange_linearEquiv`). Since an `R`-module is zero as soon as all of its
localizations at maximal ideals are zero, the vanishing conditions defining Koszul-regularity
and `H₁`-regularity can be tested one maximal ideal at a time. This file proves that, in both
directions.

This is the local-global step of [Stacks, Tag 063G]. There the passage between the sheaf-level
and the ring-level Koszul complex over an affine open `U = Spec A` is made by the equivalence
`Mod_A ≃ QCoh(O_U)` and its exactness; the stalkwise form of that comparison is
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk`, whose
`seqComplexIsoStalkComplex` identifies the stalk of the sheaf Koszul complex at a point with
the ring-level Koszul complex of the sequence of *germs*, i.e. of the images of the `fᵢ` in a
localization of `A`. What that form leaves open — and what is proved here — is that the family
of localized conditions it produces is equivalent to the single condition over `A`.

## Main results

* `Koszul.isKoszulRegular_iff_forall_localization_maximal` and
  `Koszul.isH1Regular_iff_forall_localization_maximal`: a sequence is Koszul-regular
  (respectively `H₁`-regular) if and only if its image in the localization at every maximal
  ideal is.
* `Koszul.isKoszulRegular_of_forall_localization_prime` and
  `Koszul.isH1Regular_of_forall_localization_prime`: the same sufficient condition stated over
  all prime ideals, which is the form a stalkwise hypothesis on `Spec R` supplies.
* `Koszul.isKoszulRegularOn_of_forall_localization_maximal` and
  `Koszul.isH1RegularOn_of_forall_localization_maximal`: the versions with coefficients in a
  module `M`, where the localized coefficients are `Rₚ ⊗[R] M`.
* `Koszul.subsingleton_homology_of_forall_localization_maximal`: the engine, stated for a single
  homological degree.

## Main definitions

* `Koszul.seqComplexTensorCongr`: a linear equivalence of coefficient modules induces an
  isomorphism of Koszul complexes, and `Koszul.homologyTensorCongr` the induced isomorphism on
  homology. These are what let a condition stated with coefficients in `Rₚ ⊗[R] R` be read as
  one with coefficients in `Rₚ`.
* `Koszul.ridLocalization`: the `Rₚ`-linear identification `Rₚ ⊗[R] R ≃ Rₚ`.

## Implementation notes

**The naturality square is a separate lemma, and that is what removes the transparency lever.**
`Koszul.lTensor_toModuleIso_naturality` states that `lTensor` in the coefficient variable
commutes with `rTensor` in the exterior-power variable, for an *arbitrary* pair of modules in
the second slot. Stated that way the square closes by `simp` with no option set. Written
inline inside `seqComplexTensorCongr`, where the two slots are the concrete
`⋀ⁿ⁺¹(Rʳ)` and `⋀ⁿ(Rʳ)` and the two sides are the complex's own differentials, the same step
fails with Lean's "the target expression is not type-correct under the `implicit` transparency
level": `HomologicalComplex.Hom.isoOfComponents` asks for a square between
`(seqComplexTensor f M).X (j + 1)` and `ModuleCat.of R (⋀ⁿ⁺¹(Rʳ) ⊗[R] M)`, which agree only
after unfolding `ChainComplex.of`. `Koszul.rid_toModuleIso_naturality` in
`StacksFrontier.RingTheory.Koszul.Defs` is factored out for exactly the same reason.

**The coefficient module lives in its own universe.** `seqComplexTensorCongr` and
`isKoszulRegularOn_of_linearEquiv` leave the universe of `M` and `N` independent of the universe
of `R`, so they apply both to the localizations `Rₚ ⊗[R] M` used here and to coefficient modules
of the ring's own universe.

**Why maximal ideals in the hypothesis and primes in the corollary.** Mathlib's local-global
principle for modules, `Module.subsingleton_of_localization_maximal`, tests maximal ideals, and
a hypothesis over maximal ideals only is the stronger theorem. A stalkwise hypothesis on
`Spec R` ranges over all primes, so the prime-indexed corollaries are stated as well.

## References

* [Stacks Project, Lemma 31.20.4 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Tag 062E](https://stacks.math.columbia.edu/tag/062E)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-! ### Changing the coefficient module -/

/-- `lTensor` in the second variable commutes with `rTensor` in the first, as a square in
`ModuleCat R`. The two modules in the first slot are arbitrary; see the implementation notes
for why that generality is what makes the square close without an elaboration option. -/
theorem lTensor_toModuleIso_naturality {A B : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {M N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : A →ₗ[R] B) (e : M ≃ₗ[R] N) :
    (LinearEquiv.lTensor A e).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.rTensor N g) =
      ModuleCat.ofHom (LinearMap.rTensor M g) ≫ (LinearEquiv.lTensor B e).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' fun x y => ?_
  simp

/-- A linear equivalence of coefficient modules induces an isomorphism of Koszul complexes,
degreewise `⋀ⁿ(Rʳ) ⊗[R] M ≃ ⋀ⁿ(Rʳ) ⊗[R] N`. -/
noncomputable def seqComplexTensorCongr (f : Fin r → R) {M N : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    seqComplexTensor f M ≅ seqComplexTensor f N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (LinearEquiv.lTensor (⋀[R]^n (Fin r → R)) e).toModuleIso)
    (fun i j hij => by
      obtain rfl : j + 1 = i := hij
      rw [seqComplexTensor_d, seqComplexTensor_d]
      exact lTensor_toModuleIso_naturality (d (seqDual f) j) e)

/-- The isomorphism on Koszul homology induced by a linear equivalence of coefficient
modules. -/
noncomputable def homologyTensorCongr (f : Fin r → R) {M N : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (i : ℕ) :
    (seqComplexTensor f M).homology i ≅ (seqComplexTensor f N).homology i :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (seqComplexTensorCongr f e)

/-- Koszul-regularity with coefficients depends on the coefficient module only up to linear
equivalence. -/
theorem isKoszulRegularOn_of_linearEquiv (f : Fin r → R) {M N : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (hf : IsKoszulRegularOn f M) : IsKoszulRegularOn f N :=
  fun i hi => (hf i hi).of_iso (homologyTensorCongr f e i).symm

/-- `H₁`-regularity with coefficients depends on the coefficient module only up to linear
equivalence. -/
theorem isH1RegularOn_of_linearEquiv (f : Fin r → R) {M N : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (hf : IsH1RegularOn f M) : IsH1RegularOn f N :=
  hf.of_iso (homologyTensorCongr f e 1).symm

/-! ### The local-global engine -/

/-- **The engine.** If, for every maximal ideal `P`, the degree-`i` Koszul homology of
`f₁, …, f_r` with coefficients in `Rₚ ⊗[R] M` vanishes over `Rₚ`, then the degree-`i` Koszul
homology over `R` vanishes. -/
theorem subsingleton_homology_of_forall_localization_maximal
    (f : Fin r → R) (M : Type u) [AddCommGroup M] [Module R M] (i : ℕ)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Subsingleton ((seqComplexTensor (R := Localization.AtPrime P)
        (fun j => algebraMap R (Localization.AtPrime P) (f j))
        (Localization.AtPrime P ⊗[R] M)).homology i : Type u)) :
    Subsingleton ((seqComplexTensor f M).homology i : Type u) := by
  refine Module.subsingleton_of_localization_maximal
    (fun P _ => Localization.AtPrime P ⊗[R] ((seqComplexTensor f M).homology i : Type u))
    (fun P _ => TensorProduct.mk R (Localization.AtPrime P) _ 1) ?_
  intro P hP
  have := h P
  obtain ⟨e⟩ := KoszulC.homology_baseChange_linearEquiv
    (S := Localization.AtPrime P) f M i
  exact e.symm.toEquiv.subsingleton

/-! ### Koszul-regularity and `H₁`-regularity with coefficients -/

/-- Koszul-regularity with coefficients is detected on the localizations at maximal ideals. -/
theorem isKoszulRegularOn_of_forall_localization_maximal
    (f : Fin r → R) (M : Type u) [AddCommGroup M] [Module R M]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      IsKoszulRegularOn (R := Localization.AtPrime P)
        (fun j => algebraMap R (Localization.AtPrime P) (f j))
        (Localization.AtPrime P ⊗[R] M)) :
    IsKoszulRegularOn f M := by
  intro i hi
  rw [ModuleCat.isZero_iff_subsingleton]
  exact subsingleton_homology_of_forall_localization_maximal f M i
    (fun P _ => ModuleCat.isZero_iff_subsingleton.1 (h P i hi))

/-- `H₁`-regularity with coefficients is detected on the localizations at maximal ideals. -/
theorem isH1RegularOn_of_forall_localization_maximal
    (f : Fin r → R) (M : Type u) [AddCommGroup M] [Module R M]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      IsH1RegularOn (R := Localization.AtPrime P)
        (fun j => algebraMap R (Localization.AtPrime P) (f j))
        (Localization.AtPrime P ⊗[R] M)) :
    IsH1RegularOn f M := by
  rw [IsH1RegularOn, ModuleCat.isZero_iff_subsingleton]
  exact subsingleton_homology_of_forall_localization_maximal f M 1
    (fun P _ => ModuleCat.isZero_iff_subsingleton.1 (h P))

/-! ### Koszul-regularity and `H₁`-regularity of the sequence -/

/-- Taking coefficients in `R` and then localizing is the same as taking coefficients in the
localization: the `Rₚ`-linear identification `Rₚ ⊗[R] R ≃ Rₚ`. -/
noncomputable def ridLocalization (P : Ideal R) [P.IsPrime] :
    (Localization.AtPrime P ⊗[R] R) ≃ₗ[Localization.AtPrime P] Localization.AtPrime P :=
  (Algebra.TensorProduct.rid R (Localization.AtPrime P) (Localization.AtPrime P)).toLinearEquiv

/-- A Koszul-regular sequence stays Koszul-regular in a flat algebra. This is
`KoszulC.isKoszulRegular_baseChange` with the coefficients cancelled. -/
theorem isKoszulRegular_map_of_flat {S : Type u} [CommRing S] [Algebra R S] [Module.Flat R S]
    (f : Fin r → R) (hf : IsKoszulRegular f) :
    IsKoszulRegular (fun j => algebraMap R S (f j)) :=
  (isKoszulRegularOn_self_iff _).1
    (isKoszulRegularOn_of_linearEquiv _ (TensorProduct.AlgebraTensorModule.rid R S S)
      (KoszulC.isKoszulRegular_baseChange f R ((isKoszulRegularOn_self_iff f).2 hf)))

/-- An `H₁`-regular sequence stays `H₁`-regular in a flat algebra. -/
theorem isH1Regular_map_of_flat {S : Type u} [CommRing S] [Algebra R S] [Module.Flat R S]
    (f : Fin r → R) (hf : IsH1Regular f) :
    IsH1Regular (fun j => algebraMap R S (f j)) :=
  (isH1RegularOn_self_iff _).1
    (isH1RegularOn_of_linearEquiv _ (TensorProduct.AlgebraTensorModule.rid R S S)
      (KoszulC.isH1Regular_baseChange f R ((isH1RegularOn_self_iff f).2 hf)))

/-- A sequence is Koszul-regular as soon as its image in the localization at every maximal
ideal is. -/
theorem isKoszulRegular_of_forall_localization_maximal (f : Fin r → R)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      IsKoszulRegular (fun j => algebraMap R (Localization.AtPrime P) (f j))) :
    IsKoszulRegular f := by
  rw [← isKoszulRegularOn_self_iff]
  refine isKoszulRegularOn_of_forall_localization_maximal f R fun P hP i hi => ?_
  exact ((isKoszulRegularOn_self_iff _).2 (h P) i hi).of_iso
    (homologyTensorCongr _ (ridLocalization P) i)

/-- A sequence is `H₁`-regular as soon as its image in the localization at every maximal ideal
is. -/
theorem isH1Regular_of_forall_localization_maximal (f : Fin r → R)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      IsH1Regular (fun j => algebraMap R (Localization.AtPrime P) (f j))) :
    IsH1Regular f := by
  rw [← isH1RegularOn_self_iff]
  refine isH1RegularOn_of_forall_localization_maximal f R fun P hP => ?_
  exact ((isH1RegularOn_self_iff _).2 (h P)).of_iso
    (homologyTensorCongr _ (ridLocalization P) 1)

/-- **Koszul-regularity is local on `Spec R`.** -/
theorem isKoszulRegular_iff_forall_localization_maximal (f : Fin r → R) :
    IsKoszulRegular f ↔
      ∀ (P : Ideal R) [P.IsMaximal],
        IsKoszulRegular (fun j => algebraMap R (Localization.AtPrime P) (f j)) :=
  ⟨fun h _ _ => isKoszulRegular_map_of_flat f h,
    isKoszulRegular_of_forall_localization_maximal f⟩

/-- **`H₁`-regularity is local on `Spec R`.** -/
theorem isH1Regular_iff_forall_localization_maximal (f : Fin r → R) :
    IsH1Regular f ↔
      ∀ (P : Ideal R) [P.IsMaximal],
        IsH1Regular (fun j => algebraMap R (Localization.AtPrime P) (f j)) :=
  ⟨fun h _ _ => isH1Regular_map_of_flat f h,
    isH1Regular_of_forall_localization_maximal f⟩

/-- The prime-indexed form of the sufficient condition, which is what a stalkwise hypothesis on
`Spec R` supplies. -/
theorem isKoszulRegular_of_forall_localization_prime (f : Fin r → R)
    (h : ∀ (P : Ideal R) [P.IsPrime],
      IsKoszulRegular (fun j => algebraMap R (Localization.AtPrime P) (f j))) :
    IsKoszulRegular f :=
  isKoszulRegular_of_forall_localization_maximal f fun P _ => h P

/-- The prime-indexed form of the sufficient condition for `H₁`-regularity. -/
theorem isH1Regular_of_forall_localization_prime (f : Fin r → R)
    (h : ∀ (P : Ideal R) [P.IsPrime],
      IsH1Regular (fun j => algebraMap R (Localization.AtPrime P) (f j))) :
    IsH1Regular f :=
  isH1Regular_of_forall_localization_maximal f fun P _ => h P

end Koszul

end
