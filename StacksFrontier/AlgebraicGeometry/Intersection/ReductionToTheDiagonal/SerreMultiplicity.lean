module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.SupportLength
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafVanishing
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalIntersection
public import StacksFrontier.RingTheory.Tor.Finiteness
public import StacksCore.Tactic.StacksAttribute

/-!
# The Euler characteristic of the Tor modules of two finite modules

Let `(A, 𝔪, κ)` be a regular local ring and let `M`, `N` be nonzero finite `A`-modules whose
tensor product `M ⊗_A N` is supported in `{𝔪}`. This file defines

`χ(M, N) = ∑ᵢ (-1)ⁱ length_A Torᵢ^A(M, N)`

and proves that it is finite: each term is the length of a module of finite length, and all but
finitely many terms vanish.

Writing `r = dim(Supp M)` and `s = dim(Supp N)`, Serre's multiplicity conjectures [Serre, *Algèbre
locale. Multiplicités*][Serre_algebre_locale] assert:

1. if `r + s < dim A`, then `χ(M, N) = 0`, and
2. if `r + s = dim A`, then `χ(M, N) > 0`.

They are stated here as the `Prop`-valued definitions
`Stacks.Intersection.SerreVanishingConjecture` and `Stacks.Intersection.SerrePositivityConjecture`,
and are not proved.

## Main definitions

* `Stacks.Intersection.torEulerCharacteristic` — the Euler characteristic
  `χ(M, N) = ∑ᵢ (-1)ⁱ length_A Torᵢ^A(M, N)` of a pair of modules.
* `Stacks.Intersection.SerreVanishingConjecture` and
  `Stacks.Intersection.SerrePositivityConjecture` — Serre's vanishing and positivity conjectures.

## Main results

* `Stacks.Intersection.nontrivial_tensorProduct_of_isLocalRing` — over a local ring the tensor
  product of two nonzero finite modules is nonzero.
* `Stacks.Intersection.support_tensorProduct_eq_inter` — `Supp(M ⊗_A N) = Supp M ∩ Supp N` for
  finite modules.
* `Stacks.Intersection.support_tor_subset_inter` — `Supp Torᵢ^A(M, N) ⊆ Supp M ∩ Supp N`.
* `Stacks.Intersection.supportDim_le_zero_of_support_subset_closedPoint` — a module supported in
  the closed point has support of dimension at most zero.
* `Stacks.Intersection.length_tor_ne_top` — each term of `χ(M, N)` is finite.
* `Stacks.Intersection.torEulerCharacteristic_eq_sum_range` — the alternating sum has only finitely
  many nonzero terms.

## Implementation notes

`Tor` is Mathlib's derived tensor product on `ModuleCat`, derived in the second variable. The
alternating sum is an unbounded `tsum` over `ℕ`, and the `ℕ∞`-valued lengths are converted to `ℕ`
before being cast to `ℚ`.

## References

* [Stacks Project, Tag 0B0X](https://stacks.math.columbia.edu/tag/0B0X)
* [Serre, *Algèbre locale. Multiplicités*][Serre_algebre_locale]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Intersection

/-! ### Nakayama: over a local ring a tensor product of nonzero finite modules is nonzero -/

/-- Over a local ring the reduction `M ⊗_A κ` of a nonzero finite module modulo the maximal ideal
is nonzero. -/
@[ega "0 1.7.5" "Nakayama step", ega "0 7.1.13" "special case"]
private theorem nontrivial_tensorProduct_quotient_maximalIdeal (A : Type u) [CommRing A]
    [IsLocalRing A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] :
    Nontrivial ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] M) := by
  have h : (⊤ : Submodule A M) ≠ IsLocalRing.maximalIdeal A • ⊤ :=
    Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)
  have : Nontrivial (M ⧸ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :=
    Submodule.Quotient.nontrivial_iff.mpr h.symm
  exact (TensorProduct.quotTensorEquivQuotSMul M
    (IsLocalRing.maximalIdeal A)).toEquiv.nontrivial

/-- **Over a local ring the tensor product of two nonzero finite modules is nonzero.** -/
@[ega "0 1.7.5", ega "IV 2.5.5.4" "more general"]
theorem nontrivial_tensorProduct_of_isLocalRing (A : Type u) [CommRing A] [IsLocalRing A]
    (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N] :
    Nontrivial (M ⊗[A] N) := by
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have hM : Nontrivial ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] M) :=
    nontrivial_tensorProduct_quotient_maximalIdeal A M
  have hN : Nontrivial ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] N) :=
    nontrivial_tensorProduct_quotient_maximalIdeal A N
  have : Nontrivial (((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] M)
      ⊗[A ⧸ IsLocalRing.maximalIdeal A] ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] N)) :=
    inferInstance
  have : Nontrivial ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] (M ⊗[A] N)) :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange A
      (A ⧸ IsLocalRing.maximalIdeal A) M N).toEquiv.nontrivial
  have : Nontrivial ((M ⊗[A] N) ⧸
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A (M ⊗[A] N))) :=
    (TensorProduct.quotTensorEquivQuotSMul (M ⊗[A] N)
      (IsLocalRing.maximalIdeal A)).toEquiv.symm.nontrivial
  exact (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (M ⊗[A] N))).mkQ_surjective.nontrivial

/-! ### The support of a tensor product and of a Tor module -/

/-- The annihilator of a module annihilates its tensor product with any module. -/
private theorem annihilator_le_annihilator_tensorProduct_left {A : Type u} [CommRing A]
    (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    Module.annihilator A M ≤ Module.annihilator A (M ⊗[A] N) := by
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  induction x using TensorProduct.inductionOn with
  | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  | tmul m n => rw [TensorProduct.smul_tmul', ha m, TensorProduct.zero_tmul]

/-- The annihilator of a module annihilates the tensor product of any module with it. -/
private theorem annihilator_le_annihilator_tensorProduct_right {A : Type u} [CommRing A]
    (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    Module.annihilator A N ≤ Module.annihilator A (M ⊗[A] N) := by
  rw [(TensorProduct.comm A M N).annihilator_eq]
  exact annihilator_le_annihilator_tensorProduct_left N M

/-- A module whose annihilator contains those of two finite modules is supported in both. -/
private theorem support_subset_inter_of_annihilator_le {A : Type u} [CommRing A]
    {M N X : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup N]
    [Module A N] [Module.Finite A N] [AddCommGroup X] [Module A X] [Module.Finite A X]
    (hM : Module.annihilator A M ≤ Module.annihilator A X)
    (hN : Module.annihilator A N ≤ Module.annihilator A X) :
    Module.support A X ⊆ Module.support A M ∩ Module.support A N := fun p hp => by
  rw [Module.mem_support_iff_of_finite] at hp
  exact ⟨Module.mem_support_iff_of_finite.2 (hM.trans hp),
    Module.mem_support_iff_of_finite.2 (hN.trans hp)⟩

/-- **The support of a tensor product of two finite modules is the intersection of their
supports.** -/
@[ega "0 1.7.5"]
theorem support_tensorProduct_eq_inter {A : Type u} [CommRing A] (M N : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] :
    Module.support A (M ⊗[A] N) = Module.support A M ∩ Module.support A N := by
  refine Set.Subset.antisymm
    (support_subset_inter_of_annihilator_le (annihilator_le_annihilator_tensorProduct_left M N)
      (annihilator_le_annihilator_tensorProduct_right M N)) fun p hp => ?_
  · obtain ⟨hpM, hpN⟩ := hp
    set S := p.asIdeal.primeCompl
    have hM : Nontrivial (LocalizedModule S M) := hpM
    have hN : Nontrivial (LocalizedModule S N) := hpN
    have : IsLocalRing (Localization S) := Localization.AtPrime.isLocalRing p.asIdeal
    have key : Nontrivial (LocalizedModule S M ⊗[Localization S] LocalizedModule S N) :=
      nontrivial_tensorProduct_of_isLocalRing (Localization S)
        (LocalizedModule S M) (LocalizedModule S N)
    have : Nontrivial (LocalizedModule S M ⊗[A] LocalizedModule S N) :=
      (IsLocalization.moduleTensorEquiv S (Localization S)
        (LocalizedModule S M) (LocalizedModule S N)).toEquiv.symm.nontrivial
    exact (IsLocalizedModule.iso S (TensorProduct.map (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N))).toEquiv.nontrivial

/-- The annihilator of the first variable annihilates every `Tor` module. -/
private theorem annihilator_le_annihilator_tor_left {A : Type u} [CommRing A]
    [IsNoetherianRing A] (M N : ModuleCat.{u} A) [Module.Finite A N] (i : ℕ) :
    Module.annihilator A M ≤
      Module.annihilator A (((Tor (ModuleCat.{u} A) i).obj M).obj N) := by
  obtain ⟨P, -⟩ := exists_finite_projectiveResolution N
  set F : ModuleCat.{u} A ⥤ ModuleCat.{u} A := (MonoidalCategory.tensoringLeft _).obj M
  have hiso : ((Tor (ModuleCat.{u} A) i).obj M).obj N ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.down ℕ) i).obj
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) :=
    P.isoLeftDerivedObj F i
  set K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have h1 : Module.annihilator A M ≤ Module.annihilator A (K.X i) :=
    annihilator_le_annihilator_tensorProduct_left (M : Type u) (P.complex.X i : Type u)
  have h2 : Module.annihilator A (K.X i) ≤ Module.annihilator A (K.cycles i) :=
    LinearMap.annihilator_le_of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have h3 : Module.annihilator A (K.cycles i) ≤ Module.annihilator A (K.homology i) :=
    LinearMap.annihilator_le_of_surjective (K.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  rw [hiso.toLinearEquiv.annihilator_eq]
  exact h1.trans (h2.trans h3)

/-- The annihilator of the second variable annihilates every `Tor` module. -/
private theorem annihilator_le_annihilator_tor_right {A : Type u} [CommRing A]
    [IsNoetherianRing A] (M N : ModuleCat.{u} A) [Module.Finite A M] (i : ℕ) :
    Module.annihilator A N ≤
      Module.annihilator A (((Tor (ModuleCat.{u} A) i).obj M).obj N) := by
  obtain ⟨e⟩ := tor_symm_canonically_iso A i
  have hiso : ((Tor (ModuleCat.{u} A) i).obj M).obj N ≅
      ((Tor (ModuleCat.{u} A) i).obj N).obj M := (e.app M).app N
  rw [hiso.toLinearEquiv.annihilator_eq]
  exact annihilator_le_annihilator_tor_left N M i

/-- **The support of `Torᵢ^A(M, N)` is contained in the intersection of the supports of `M` and
`N`.** -/
@[sga "6 X 3.3" "special case"]
theorem support_tor_subset_inter {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M N : ModuleCat.{u} A) [Module.Finite A M] [Module.Finite A N] (i : ℕ) :
    Module.support A (((Tor (ModuleCat.{u} A) i).obj M).obj N) ⊆
      Module.support A M ∩ Module.support A N := by
  intro q hq
  have : Module.Finite A (((Tor (ModuleCat.{u} A) i).obj M).obj N) :=
    tor_finite_of_noetherian A M N i
  exact support_subset_inter_of_annihilator_le (annihilator_le_annihilator_tor_left M N i)
    (annihilator_le_annihilator_tor_right M N i) hq

/-! ### The Euler characteristic and its finiteness -/

/-- **The Euler characteristic of the `Tor` modules of two modules**: the alternating sum
`χ(M, N) = ∑ᵢ (-1)ⁱ length_A Torᵢ^A(M, N)`, with each length converted from `ℕ∞` to `ℕ`. -/
@[sga "4½ Cycle 2.3.9"]
def torEulerCharacteristic (A : Type u) [CommRing A] (M N : Type u)
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] : ℚ :=
  ∑' i : ℕ, (-1 : ℚ) ^ i *
    ((Module.length A (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A N))).toNat : ℚ)

/-- The Tor-formula intersection multiplicity of an ideal `I` and a module `M` is the Euler
characteristic of the pair `(A ⧸ I, M)`. -/
theorem localIntersectionMultiplicity_eq_torEulerCharacteristic {A : Type u} [CommRing A]
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] :
    I.localIntersectionMultiplicity M = torEulerCharacteristic A (A ⧸ I) M :=
  rfl

/-- A module supported in the closed point has support of dimension at most zero. -/
private theorem supportDim_le_zero_of_subset_closedPoint {A : Type u} [CommRing A]
    [IsLocalRing A] (X : Type u) [AddCommGroup X] [Module A X]
    (hX : Module.support A X ⊆ {IsLocalRing.closedPoint A}) :
    Module.supportDim A X ≤ 0 := by
  have hsingle : Order.krullDim ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) = 0 :=
    Order.krullDim_eq_zero_of_unique
  unfold Module.supportDim
  simpa [hsingle] using
    Order.krullDim_le_of_strictMono (Set.inclusion hX) (Subtype.strictMono_coe _)

/-- **A module supported in the closed point has support of dimension at most zero.** -/
public alias supportDim_le_zero_of_support_subset_closedPoint :=
  supportDim_le_zero_of_subset_closedPoint

/-- **Each term of `χ(M, N)` is finite**, for `A` Noetherian local and `M ⊗_A N` supported in the
maximal ideal. -/
theorem length_tor_ne_top_of_support_subset {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {IsLocalRing.closedPoint A}) (i : ℕ) :
    Module.length A (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A N)) ≠ ⊤ := by
  have hsub : Module.support A (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A N)) ⊆ {IsLocalRing.closedPoint A} :=
    (support_tor_subset_inter (ModuleCat.of A M) (ModuleCat.of A N) i).trans
      ((support_tensorProduct_eq_inter M N).ge.trans hMN)
  have : Module.Finite A (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A N)) :=
    tor_finite_of_noetherian A (ModuleCat.of A M) (ModuleCat.of A N) i
  rw [Module.length_ne_top_iff]
  exact AlgebraicGeometry.finite_length_of_supportDim_le_zero
    (supportDim_le_zero_of_subset_closedPoint _ hsub)

/-- **Finiteness of the individual terms of `χ(M, N)`.** Let `A` be a regular local ring and let
`M`, `N` be nonzero finite `A`-modules with `M ⊗_A N` supported in the maximal ideal. Then
`length_A Torᵢ^A(M, N)` is finite for every `i`. -/
@[stacks 0B0X "finiteness of each term `length_A Tor_i^A(M, N)` of the sum `χ(M, N)`"]
theorem length_tor_ne_top {A : Type u} [CommRing A] [IsRegularLocalRing A] (M N : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {IsLocalRing.closedPoint A}) (i : ℕ) :
    Module.length A (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A N)) ≠ ⊤ :=
  length_tor_ne_top_of_support_subset M N hMN i

/-- **Finiteness of the number of nonzero terms of `χ(M, N)`.** Over a regular local ring of
dimension at most `d`, the alternating sum defining `χ(M, N)` is the finite sum over `i = 0, …, d`.
-/
@[stacks 0B0X "the sum `χ(M, N)` has finitely many nonzero terms: `Tor_i = 0` for `i > dim A`"]
theorem torEulerCharacteristic_eq_sum_range {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    torEulerCharacteristic A M N =
      ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
        ((Module.length A (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A N))).toNat : ℚ) := by
  rw [torEulerCharacteristic]
  refine tsum_eq_sum fun b hb => ?_
  rw [Finset.mem_range, not_lt] at hb
  have hzero : IsZero (((Tor (ModuleCat.{u} A) b).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A N)) :=
    AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing _ _ d b hd (by omega)
  rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hzero)]
  simp

/-! ### Serre's multiplicity conjectures -/

/-- **Serre's vanishing conjecture**: for `A` a regular local ring and `M`, `N` nonzero finite
`A`-modules with `M ⊗_A N` supported in the maximal ideal, if `dim(Supp M) + dim(Supp N) < dim A`
then `χ(M, N) = 0`.

This is a theorem of Roberts and of Gillet–Soulé; it is not proved here. -/
def SerreVanishingConjecture : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [IsRegularLocalRing A] (M N : Type u) [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Nontrivial M] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Nontrivial N],
    Module.support A (M ⊗[A] N) ⊆ {IsLocalRing.closedPoint A} →
    Module.supportDim A M + Module.supportDim A N < ringKrullDim A →
    torEulerCharacteristic A M N = 0

/-- **Serre's positivity conjecture**: for `A` a regular local ring and `M`, `N` nonzero finite
`A`-modules with `M ⊗_A N` supported in the maximal ideal, if `dim(Supp M) + dim(Supp N) = dim A`
then `χ(M, N) > 0`.

Gabber proved the weaker `χ(M, N) ≥ 0`; positivity is open in general. -/
def SerrePositivityConjecture : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [IsRegularLocalRing A] (M N : Type u) [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Nontrivial M] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Nontrivial N],
    Module.support A (M ⊗[A] N) ⊆ {IsLocalRing.closedPoint A} →
    Module.supportDim A M + Module.supportDim A N = ringKrullDim A →
    0 < torEulerCharacteristic A M N

end Stacks.Intersection

end
