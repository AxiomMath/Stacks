module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksFrontier.RingTheory.Koszul.TorComparison.Resolution
public import StacksFrontier.RingTheory.Tor.Balancing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Tor` against a quotient by a Koszul-regular sequence

Let `R` be a commutative ring and `f₁, …, f_r ∈ R` a Koszul-regular sequence, so that the Koszul
complex `K_•(f₁, …, f_r)` of `StacksFrontier.RingTheory.Koszul.Defs` is a free resolution of
`R ⧸ (f₁, …, f_r)` (`Koszul.koszulAugmentation_quasiIso`). Packaging that resolution as a
`CategoryTheory.ProjectiveResolution` and feeding it to
`CategoryTheory.ProjectiveResolution.isoLeftDerivedObj` computes `Tor` against the quotient as the
Koszul homology with coefficients:

`Torₙ^R(R ⧸ (f₁, …, f_r), M) = Hₙ(K_•(f₁, …, f_r) ⊗_R M)`.

Three consequences are recorded. The right-hand side is by definition what the `M`-coefficient
regularity predicates of Tag 062E talk about, so Koszul-regularity of `f` *on* `M` is exactly the
vanishing of these `Tor` groups in positive degrees; the Koszul complex is zero above degree `r`,
so these `Tor` groups vanish there too; and with coefficients in the quotient itself the Koszul
differential dies, because each of its coefficients lies in `(f₁, …, f_r)`, which gives
`Tor_*^R(B, B) = ⋀^*(Rʳ) ⊗_R B` for `B = R ⧸ (f₁, …, f_r)`.

## Main definitions

* `Koszul.seqProjectiveResolution`: the Koszul complex of a Koszul-regular sequence, read as a
  projective resolution of `R ⧸ (f₁, …, f_r)`.
* `Koszul.tensoringRightSeqComplexIso`: the image of `K_•(f)` under `- ⊗_R M` is
  `Koszul.seqComplexTensor f M`.
* `Koszul.torIsoHomologySeqComplexTensor`: the identification
  `Torₙ^R(R ⧸ (f), M) ≅ Hₙ(K_•(f) ⊗_R M)`.
* `Koszul.torIsoHomologySeqComplexTensorOfIsRegular`: the same identification read through
  `CategoryTheory.Tor` instead of `CategoryTheory.Tor'`, for a regular sequence and an ideal
  presented as the one it generates.
* `Koszul.homologySeqComplexTensorQuotientIso`: with coefficients in the quotient, the homology of
  the Koszul complex is its term.
* `Koszul.torSelfIsoExteriorPowerTensor`: the identification
  `Torₙ^R(R ⧸ (f), R ⧸ (f)) ≅ ⋀ⁿ(Rʳ) ⊗_R (R ⧸ (f))`.

## Main results

* `Koszul.isKoszulRegularOn_iff_isZero_tor`: for a Koszul-regular `f`, the sequence is
  Koszul-regular on `M` if and only if `Torₙ^R(R ⧸ (f), M) = 0` for every `n ≠ 0`.
* `Koszul.isZero_tor_of_lt`: `Torₙ^R(R ⧸ (f), M) = 0` for `n > r`.
* `Koszul.d_seqDual_eq_sum_smul`: the Koszul differential of `f₁, …, f_r` is
  `∑ i, fᵢ • (Koszul differential of the i-th coordinate projection)`, so all its coefficients
  lie in the ideal `(f₁, …, f_r)`.
* `Koszul.rTensor_quotient_d_eq_zero`, `Koszul.seqComplexTensor_quotient_d_eq_zero`: consequently
  `K_•(f) ⊗_R (R ⧸ (f₁, …, f_r))` has zero differentials.

## Implementation notes

`CategoryTheory.Tor'` rather than `CategoryTheory.Tor`: the left derived functor is taken in the
first variable, which is the quotient being resolved. The balancing isomorphism of Tag 00M1,
`Tor_iso_Tor'`, carries that over to `CategoryTheory.Tor`;
`Koszul.torIsoHomologySeqComplexTensorOfIsRegular` is that form.

`Koszul.seqComplexTensor f M` has `⋀ⁿ(Rʳ) ⊗[R] M` in degree `n` with differential
`LinearMap.rTensor M (Koszul.d (Koszul.seqDual f) n)`, while the monoidal functor `- ⊗ M` of
`ModuleCat R` sends the Koszul differential to `ModuleCat.hom_whiskerRight`, which is the same
`LinearMap.rTensor`. The comparison isomorphism is therefore the identity in each degree.

`Koszul.seqProjectiveResolution` is stated under `Koszul.IsKoszulRegular`, which is what Tag 062F
deduces from regularity; a regular sequence is Koszul-regular by
`Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular`.

## References

* [Stacks Project, Tag 062E](https://stacks.math.columbia.edu/tag/062E)
* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped TensorProduct

universe u

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **The Koszul complex of a Koszul-regular sequence as a projective resolution.** Its terms are
the free modules `⋀ⁿ(Rʳ)` and its augmentation onto `R ⧸ (f₁, …, f_r)` is a
quasi-isomorphism by `Koszul.koszulAugmentation_quasiIso`. -/
@[sga "3 III 4.6.1" "partial, special case",
  sga "6 III 1.1.2" "special case",
  sga "6 VII 1.1" "special case",
  sga "6 VIII 1.4" "partial"]
def seqProjectiveResolution (f : Fin r → R) (hf : IsKoszulRegular f) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) where
  complex := seqComplex f
  π := koszulAugmentation f
  quasiIso := koszulAugmentation_quasiIso f hf

/-- The complex underlying `Koszul.seqProjectiveResolution f hf` is the Koszul complex
`Koszul.seqComplex f`. -/
@[simp]
theorem seqProjectiveResolution_complex (f : Fin r → R) (hf : IsKoszulRegular f) :
    (seqProjectiveResolution f hf).complex = seqComplex f :=
  rfl

/-- Tensoring the Koszul complex `K_•(f₁, …, f_r)` with `M` through the monoidal structure of
`ModuleCat R` gives the Koszul complex with coefficients in `M`. In each degree both sides are
`⋀ⁿ(Rʳ) ⊗[R] M` and both differentials are `LinearMap.rTensor M` of the Koszul differential. -/
def tensoringRightSeqComplexIso (f : Fin r → R) (M : Type u) [AddCommGroup M] [Module R M] :
    (((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R M)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (seqComplex f) ≅ seqComplexTensor f M :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j (rfl : j + 1 = i)
    dsimp
    rw [seqComplexTensor_d, seqComplex_d]
    apply ModuleCat.hom_ext
    rfl)

/-- **The Koszul complex computes `Tor` against the quotient.** For a Koszul-regular sequence
`f₁, …, f_r` and an `R`-module `M`,
`Torₙ^R(R ⧸ (f₁, …, f_r), M) ≅ Hₙ(K_•(f₁, …, f_r) ⊗_R M)`. -/
@[sga "6 VII 1.2" "Tor_i^A(B"]
def torIsoHomologySeqComplexTensor (f : Fin r → R) (hf : IsKoszulRegular f)
    (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ) :
    ((Tor' (ModuleCat.{u} R) n).obj (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).obj
        (ModuleCat.of R M) ≅ (seqComplexTensor f M).homology n :=
  (seqProjectiveResolution f hf).isoLeftDerivedObj
      ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R M)) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (tensoringRightSeqComplexIso f M)

/-- **Tor against the quotient by a regular sequence is the homology of the Koszul complex with
coefficients.** The `CategoryTheory.Tor` reading of `Koszul.torIsoHomologySeqComplexTensor`,
for a sequence that is regular rather than merely Koszul-regular and for an ideal presented as
the one the sequence generates. The two readings are exchanged by the balancing isomorphism of
Tag 00M1. -/
def torIsoHomologySeqComplexTensorOfIsRegular (f : Fin r → R)
    (hf : RingTheory.Sequence.IsRegular R (List.ofFn f)) (I : Ideal R)
    (hI : I = Ideal.span (Set.range f)) (M : Type u) [AddCommGroup M] [Module R M] (i : ℕ) :
    (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)) ≅
      ModuleCat.of R ((seqComplexTensor f M).homology i) := by
  subst I
  let P := seqProjectiveResolution f
    ((isKoszulRegularOn_and_isKoszulRegular_of_regular (M := R)).2.2 hf)
  let e₁ := (Tor_iso_Tor' R i).app (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))
  let e₂ := P.isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R M)) i
  have hC : (((tensoringRight (ModuleCat.{u} R)).obj
      (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (seqComplex f) = seqComplexTensor f M := by
    unfold Koszul.seqComplex Koszul.complex Koszul.seqComplexTensor
    rw [ChainComplex.map_chain_complex_of]
    rfl
  simpa [Tor', tensoringRight, HomologicalComplex.homologyFunctor, P,
    seqProjectiveResolution, hC] using e₁.app (ModuleCat.of R M) ≪≫ e₂

/-- For a Koszul-regular sequence `f₁, …, f_r`, Koszul-regularity on `M` is the vanishing of
`Torₙ^R(R ⧸ (f₁, …, f_r), M)` in every nonzero degree. -/
theorem isKoszulRegularOn_iff_isZero_tor (f : Fin r → R) (hf : IsKoszulRegular f)
    (M : Type u) [AddCommGroup M] [Module R M] :
    IsKoszulRegularOn f M ↔ ∀ n ≠ 0,
      IsZero (((Tor' (ModuleCat.{u} R) n).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).obj (ModuleCat.of R M)) :=
  forall₂_congr fun n _ => (torIsoHomologySeqComplexTensor f hf M n).isZero_iff.symm

/-! ### `Tor` of the quotient with itself -/

/-- Contraction against `Koszul.seqDual f` is the combination `∑ i, fᵢ • (contraction against the
`i`-th coordinate projection)`, because `Koszul.seqDual f = ∑ i, fᵢ • prᵢ` and
`CliffordAlgebra.contractLeft` is linear in the functional. Every coefficient of the Koszul
differential therefore lies in the ideal `(f₁, …, f_r)`. -/
theorem d_seqDual_eq_sum_smul (f : Fin r → R) (n : ℕ) :
    d (seqDual f) n = ∑ i, f i • d (LinearMap.proj i) n := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have hc : contraction (seqDual f)
      = ∑ i, f i • contraction (LinearMap.proj (R := R) (φ := fun _ : Fin r => R) i) := by
    rw [seqDual_eq_sum_smul_proj]
    simp only [contraction, map_sum, map_smul]
  rw [d_apply_coe, hc]
  simp [LinearMap.sum_apply]

/-- The Koszul differential dies after tensoring with `R ⧸ (f₁, …, f_r)`: each of its
coefficients lies in `(f₁, …, f_r)`, which acts as zero on the quotient. -/
theorem rTensor_quotient_d_eq_zero (f : Fin r → R) (n : ℕ) :
    LinearMap.rTensor (R ⧸ Ideal.span (Set.range f)) (d (seqDual f) n) = 0 := by
  refine TensorProduct.ext' fun x m => ?_
  have hm : ∀ k : Fin r, f k • m = 0 := fun k => by
    have h0 : (Ideal.Quotient.mk (Ideal.span (Set.range f))) (f k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, h0]
  rw [LinearMap.rTensor_tmul, LinearMap.zero_apply, d_seqDual_eq_sum_smul]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [TensorProduct.sum_tmul]
  exact Finset.sum_eq_zero fun k _ => by
    rw [TensorProduct.smul_tmul, hm k, TensorProduct.tmul_zero]

/-- The Koszul complex of `f₁, …, f_r` with coefficients in `R ⧸ (f₁, …, f_r)` has vanishing
differentials. -/
theorem seqComplexTensor_quotient_d_eq_zero (f : Fin r → R) (i j : ℕ) :
    (seqComplexTensor f (R ⧸ Ideal.span (Set.range f))).d i j = 0 := by
  by_cases hij : j + 1 = i
  · subst hij
    rw [seqComplexTensor_d, rTensor_quotient_d_eq_zero, ModuleCat.ofHom_zero]
    rfl
  · exact (seqComplexTensor f (R ⧸ Ideal.span (Set.range f))).shape i j (by simpa using hij)

/-- The homology of `K_•(f₁, …, f_r) ⊗_R (R ⧸ (f₁, …, f_r))` is its term, the differentials being
zero. -/
def homologySeqComplexTensorQuotientIso (f : Fin r → R) (n : ℕ) :
    (seqComplexTensor f (R ⧸ Ideal.span (Set.range f))).homology n ≅
      ModuleCat.of R ((⋀[R]^n (Fin r → R)) ⊗[R] (R ⧸ Ideal.span (Set.range f))) :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((seqComplexTensor f (R ⧸ Ideal.span (Set.range f))).sc n)
    (seqComplexTensor_quotient_d_eq_zero f _ n)
    (seqComplexTensor_quotient_d_eq_zero f n _)).homologyIso

/-- **`Tor` of a quotient by a Koszul-regular sequence with itself is the exterior algebra on the
conormal module.** For a Koszul-regular sequence `f₁, …, f_r` generating `I`, writing
`B = R ⧸ I`,

`Torₙ^R(B, B) ≅ ⋀ⁿ(Rʳ) ⊗_R B`,

a free `B`-module of rank `r.choose n`. This is the computation Quillen's criterion for the
cotangent complex of a quotient by a Koszul-regular ideal takes as its input; the criterion itself
is the spectral sequence of [Stacks, Tag 08RF], which this library does not have. -/
@[sga "4 XVIII 1.3.17" "(f)", sga "6 VII 2.5" "partial"]
def torSelfIsoExteriorPowerTensor (f : Fin r → R) (hf : IsKoszulRegular f) (n : ℕ) :
    ((Tor' (ModuleCat.{u} R) n).obj (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) ≅
      ModuleCat.of R ((⋀[R]^n (Fin r → R)) ⊗[R] (R ⧸ Ideal.span (Set.range f))) :=
  torIsoHomologySeqComplexTensor f hf (R ⧸ Ideal.span (Set.range f)) n ≪≫
    homologySeqComplexTensorQuotientIso f n

/-- `Torₙ^R(R ⧸ (f₁, …, f_r), M)` vanishes above degree `r`: the Koszul complex of a sequence of
length `r` has no terms there. -/
theorem isZero_tor_of_lt (f : Fin r → R) (hf : IsKoszulRegular f)
    (M : Type u) [AddCommGroup M] [Module R M] {n : ℕ} (hn : r < n) :
    IsZero (((Tor' (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).obj (ModuleCat.of R M)) := by
  refine IsZero.of_iso ?_ (torIsoHomologySeqComplexTensor f hf M n)
  refine ShortComplex.isZero_homology_of_isZero_X₂ ((seqComplexTensor f M).sc n) ?_
  have : Subsingleton (⋀[R]^n (Fin r → R)) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt
      (Pi.basisFun R (Fin r)) (Pi.basisFun R (Fin r)).span_eq n (by simpa using hn)
  have hz : IsZero (ModuleCat.of R ((⋀[R]^n (Fin r → R)) ⊗[R] M)) :=
    ModuleCat.isZero_of_subsingleton _
  exact hz

end Koszul

end
