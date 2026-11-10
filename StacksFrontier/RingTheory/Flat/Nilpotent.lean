module


import StacksCore.RingTheory.Nakayama
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Tactic.Continuity
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import StacksFrontier.RingTheory.Flat.LocalCriteria
import StacksFrontier.RingTheory.Flat.TorCriterion
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.TensorProduct.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness over a nilpotent thickening

Results about a flat module and its reduction along a nilpotent, or merely an arbitrary,
thickening.

## Main results

* `flat_quotient_map_quotient`: flatness of `M ⧸ KM` over `R ⧸ K` passes to the further
  quotient by a second ideal `L`.
* `injective_lift_lsmul_of_rTensor_injective`: injectivity of the multiplication map
  `J ⊗ (M ⧸ LM) → M ⧸ LM` from injectivity of `J ⊗_R M → (R ⧸ L) ⊗_R M`.
* `Module.Flat.linearIndependent_and_span_eq_top_mkQ_comp_iff_of_isNilpotent`: a family in a
  flat module is an `R`-basis exactly when its reduction modulo a nilpotent ideal `I` is an
  `R ⧸ I`-basis of the reduction.
* `Module.Flat.iff_flat_quotient_and_isZero_Tor'_one`: the local criterion for flatness over a
  local ring with nilpotent maximal ideal: for a proper ideal `I`, `M` is flat over `R` exactly
  when `M/IM` is flat over `R/I` and `Tor₁^R(R/I, M) = 0`.
* `quotientMap_pow_bijective_of_flat`: for a flat algebra, an isomorphism modulo an ideal
  induces isomorphisms modulo all its powers.

## References

* [StacksProject 0584](https://stacks.math.columbia.edu/tag/0584)
* [StacksProject 051F](https://stacks.math.columbia.edu/tag/051F)
* [StacksProject 051K](https://stacks.math.columbia.edu/tag/051K)
-/

@[expose] public section

open TensorProduct

/-- Flatness of `M ⧸ KM` over `R ⧸ K` is inherited by the image of `K` in a further quotient
`R ⧸ L`. -/
theorem flat_quotient_map_quotient {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (K L : Ideal R)
    (h1 : Module.Flat (R ⧸ K) (M ⧸ K • (⊤ : Submodule R M))) :
    Module.Flat ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K)
      ((M ⧸ L • (⊤ : Submodule R M)) ⧸
        Ideal.map (Ideal.Quotient.mk L) K •
          (⊤ : Submodule (R ⧸ L) (M ⧸ L • (⊤ : Submodule R M)))) := by
  let alg : Algebra (R ⧸ K) ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  let _ : Module (R ⧸ K) ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K) := alg.toModule
  let _tower : IsScalarTower R (R ⧸ K) ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K) :=
    Ideal.Quotient.tower_quotient_map_quotient
  have hfN : IsBaseChange (R ⧸ L) ((L • (⊤ : Submodule R M)).mkQ) :=
    isBaseChange_mkQ_smul_top L
  have hgN : IsBaseChange ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K)
      ((Ideal.map (Ideal.Quotient.mk L) K •
        (⊤ : Submodule (R ⧸ L) (M ⧸ L • (⊤ : Submodule R M)))).mkQ) :=
    isBaseChange_mkQ_smul_top (Ideal.map (Ideal.Quotient.mk L) K)
  have hf0 : IsBaseChange (R ⧸ K) ((K • (⊤ : Submodule R M)).mkQ) :=
    isBaseChange_mkQ_smul_top K
  let e3 := (hfN.comp hgN).equiv
  let e2 := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ K)
    ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K)
    ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K) M
  let e1 := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K)
      ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K))
    hf0.equiv.symm
  have hflatbc : Module.Flat ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K)
      (((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K) ⊗[R ⧸ K]
        (M ⧸ K • (⊤ : Submodule R M))) :=
    Module.Flat.baseChange (R ⧸ K) ((R ⧸ L) ⧸ Ideal.map (Ideal.Quotient.mk L) K)
      (M ⧸ K • (⊤ : Submodule R M))
  exact Module.Flat.of_linearEquiv (e1.trans (e2.trans e3)).symm

/-- Injectivity of the multiplication map `J ⊗_{R ⧸ L} (M ⧸ LM) → M ⧸ LM`, for an ideal `J` of
`R ⧸ L`, follows from injectivity of the `R`-linear map `J ⊗_R M → (R ⧸ L) ⊗_R M`. -/
theorem injective_lift_lsmul_of_rTensor_injective {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (L : Ideal R) (J : Ideal (R ⧸ L))
    (hcore : Function.Injective (LinearMap.rTensor M (J.subtype.restrictScalars R))) :
    Function.Injective (TensorProduct.lift
      ((LinearMap.lsmul (R ⧸ L) (M ⧸ L • (⊤ : Submodule R M))).comp J.subtype)) := by
  set S := R ⧸ L with hS
  set N := M ⧸ L • (⊤ : Submodule R M) with hN
  have hsurj : Function.Surjective (algebraMap R S) := Ideal.Quotient.mk_surjective
  let qN : (S ⊗[R] M) ≃ₗ[S] N :=
    LinearEquiv.extendScalarsOfSurjective hsurj (TensorProduct.quotTensorEquivQuotSMul M L)
  let cb : (↥J) ⊗[S] (S ⊗[R] M) ≃ₗ[S] (↥J) ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (↥J) M
  let Θ : (↥J) ⊗[S] N ≃ₗ[S] (↥J) ⊗[R] M :=
    (TensorProduct.congr (LinearEquiv.refl S (↥J)) qN.symm).trans cb
  set ιR : (↥J) →ₗ[R] S := J.subtype.restrictScalars R with hιR
  let μS : (↥J) ⊗[S] N →ₗ[S] N :=
    (TensorProduct.lid S N).toLinearMap.comp (LinearMap.rTensor N J.subtype)
  have hsquare : (μS.restrictScalars R).comp (Θ.symm.toLinearMap.restrictScalars R)
      = (qN.toLinearMap.restrictScalars R).comp (LinearMap.rTensor M ιR) := by
    apply TensorProduct.ext'
    intro j m
    simp only [LinearMap.coe_comp, LinearMap.restrictScalars_apply, Function.comp_apply,
      LinearEquiv.coe_coe]
    have hΘsymm : Θ.symm (j ⊗ₜ[R] m) = j ⊗ₜ[S] qN (1 ⊗ₜ[R] m) := by
      simp only [Θ, LinearEquiv.trans_symm, LinearEquiv.trans_apply, cb,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        TensorProduct.congr_symm, LinearEquiv.refl_symm, LinearEquiv.symm_symm,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    rw [hΘsymm]
    change (TensorProduct.lid S N) (LinearMap.rTensor N J.subtype (j ⊗ₜ[S] qN (1 ⊗ₜ[R] m)))
        = qN ((LinearMap.rTensor M ιR) (j ⊗ₜ[R] m))
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.rTensor_tmul, ← map_smul qN]
    congr 1
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  have hLHS : Function.Injective
      ((μS.restrictScalars R).comp (Θ.symm.toLinearMap.restrictScalars R)) := by
    rw [hsquare, LinearMap.coe_comp]
    exact qN.injective.comp hcore
  have hμS : Function.Injective μS := Function.Injective.of_comp_right
    (f := μS.restrictScalars R) (g := Θ.symm.toLinearMap.restrictScalars R) hLHS Θ.symm.surjective
  have hgoal : (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype))
      = (TensorProduct.lid S N).toLinearMap.comp (LinearMap.rTensor N J.subtype) := by
    apply TensorProduct.ext'; intro j n; simp
  rw [hgoal]
  exact hμS

end

/-!
# Bases of a flat module modulo a nilpotent ideal

Let `R` be a commutative ring, let `I ⊆ R` be a nilpotent ideal and let `M` be a flat `R`-module.
Then a family `(xₐ)` of elements of `M`, indexed by an arbitrary type, is an `R`-basis of `M` if
and only if the family of its reductions is an `R/I`-basis of `M/IM`; so over such a ring a basis
of a flat module may be read off its reduction, with no finiteness hypothesis on `M` or on the
index type.

## Main results

* `Module.Flat.linearIndependent_and_span_eq_top_mkQ_comp_iff_of_isNilpotent`: a family in a flat
  module is an `R`-basis if and only if its reduction modulo a nilpotent ideal is an `R/I`-basis of
  the reduced module.

## Implementation notes

The statement is made for an arbitrary nilpotent ideal of an arbitrary commutative ring; the case
of a local ring `(R, 𝔪)` with `𝔪` nilpotent is `I = IsLocalRing.maximalIdeal R`.

"Forms a basis" is spelled, on both sides, as the conjunction `LinearIndependent ∧ span … = ⊤`,
the hypotheses of `Module.Basis.mk`; the index type is arbitrary. Compare
`Module.IsLocalRing.linearCombination_bijective_of_flat`, the analogue for a finite module over an
arbitrary local ring.

`M/IM` is `M ⧸ I • (⊤ : Submodule R M)` with the `R/I`-action induced by the `R`-action, and the
reduction map is `Submodule.mkQ`. It agrees with `(R ⧸ I) ⊗[R] M` by
`TensorProduct.quotTensorEquivQuotSMul M I`, under which `1 ⊗ x` corresponds to the reduction
of `x`.

## References

* [Stacks Project, Tag 051F](https://stacks.math.columbia.edu/tag/051F)
-/

@[expose] public section

namespace Module.Flat

section Aux

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*}

/-- The reduction modulo an ideal `I` of an `R`-basis of `M` is an `R ⧸ I`-basis of `M ⧸ IM`. -/
@[sga "3 VIII 6.2" "(c), special case"]
private noncomputable def basisQuotSMulTop (I : Ideal R) (b : Module.Basis ι R M) :
    Module.Basis ι (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
  (Algebra.TensorProduct.basis (R ⧸ I) b).map
    ((TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective)

/-- The basis `basisQuotSMulTop I b` is the family of reductions of the members of `b`. -/
private lemma coe_basisQuotSMulTop (I : Ideal R) (b : Module.Basis ι R M) :
    ⇑(basisQuotSMulTop I b) = (I • (⊤ : Submodule R M)).mkQ ∘ b := by
  funext i
  simp [basisQuotSMulTop, Algebra.TensorProduct.basis_apply]

/-- If a family in `M` is an `R`-basis, its reduction modulo an ideal `I` is linearly independent
over `R ⧸ I` and spans `M ⧸ IM`. -/
private lemma linearIndependent_mkQ_comp_and_span_eq_top (I : Ideal R) {x : ι → M}
    (hli : LinearIndependent R x) (hsp : Submodule.span R (Set.range x) = ⊤) :
    LinearIndependent (R ⧸ I) ((I • (⊤ : Submodule R M)).mkQ ∘ x) ∧
      Submodule.span (R ⧸ I) (Set.range ((I • (⊤ : Submodule R M)).mkQ ∘ x)) = ⊤ := by
  have h := coe_basisQuotSMulTop I (Module.Basis.mk hli hsp.ge)
  rw [show ⇑(Module.Basis.mk hli hsp.ge) = x from funext fun i => Module.Basis.mk_apply ..] at h
  exact ⟨h ▸ (basisQuotSMulTop I _).linearIndependent, h ▸ (basisQuotSMulTop I _).span_eq⟩

/-- Nakayama's lemma for a nilpotent ideal `I`: a family whose reduction spans `M ⧸ IM` as an
`R ⧸ I`-module spans `M`. -/
@[sga "3 III 4.6.4" "more general", sga "3 VIB 6.2.2" "partial"]
private lemma span_eq_top_of_span_mkQ_comp_eq_top_of_isNilpotent {I : Ideal R}
    (hI : IsNilpotent I) {x : ι → M}
    (hsp : Submodule.span (R ⧸ I) (Set.range ((I • (⊤ : Submodule R M)).mkQ ∘ x)) = ⊤) :
    Submodule.span R (Set.range x) = ⊤ := by
  refine Submodule.span_eq_top_of_span_image_mkQ_eq_top_of_isNilpotent I hI _ ?_
  have hset : (Submodule.Quotient.mk '' Set.range x : Set (M ⧸ I • (⊤ : Submodule R M)))
      = Set.range ((I • (⊤ : Submodule R M)).mkQ ∘ x) := (Set.range_comp _ _).symm
  rw [hset, ← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, hsp,
    Submodule.restrictScalars_top]

/-- A finitely supported function all of whose values lie in an ideal `I` lies in
`I • (ι →₀ R)`. -/
private lemma mem_ideal_smul_top_of_forall_mem (I : Ideal R) {l : ι →₀ R} (h : ∀ i, l i ∈ I) :
    l ∈ I • (⊤ : Submodule R (ι →₀ R)) := by
  classical
  rw [← Finsupp.sum_single l]
  change (∑ i ∈ l.support, Finsupp.single i (l i)) ∈ I • (⊤ : Submodule R (ι →₀ R))
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← Finsupp.smul_single_one i (l i)]
  exact Submodule.smul_mem_smul (h i) Submodule.mem_top

/-- Linear independence of the reduction of `x` modulo `I` confines the relations among the `x` to
those with every coefficient in `I`. -/
private lemma ker_linearCombination_le_smul_top (I : Ideal R) {x : ι → M}
    (hli : LinearIndependent (R ⧸ I) ((I • (⊤ : Submodule R M)).mkQ ∘ x)) :
    LinearMap.ker (Finsupp.linearCombination R x) ≤ I • (⊤ : Submodule R (ι →₀ R)) := by
  intro l hl
  refine mem_ideal_smul_top_of_forall_mem I fun i => ?_
  have hcomb : (l.sum fun j a => (I • (⊤ : Submodule R M)).mkQ (a • x j)) = 0 := by
    rw [← map_finsuppSum, ← Finsupp.linearCombination_apply, LinearMap.mem_ker.mp hl, map_zero]
  have h0 : Finsupp.linearCombination (R ⧸ I) ((I • (⊤ : Submodule R M)).mkQ ∘ x)
      (l.mapRange (Ideal.Quotient.mk I) (map_zero _)) = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
    refine Eq.trans (Finsupp.sum_congr fun j _ => ?_) hcomb
    exact _root_.Module.Quotient.mk_smul_mk M I (l j) (x j)
  have hz := linearIndependent_iff.mp hli _ h0
  have hi : Ideal.Quotient.mk I (l i) = 0 := by
    simpa using congrArg (fun t : ι →₀ (R ⧸ I) => t i) hz
  exact Ideal.Quotient.eq_zero_iff_mem.mp hi

/-- Over an arbitrary commutative ring, a spanning family in a flat module whose reduction modulo a
nilpotent ideal `I` is linearly independent over `R ⧸ I` is itself linearly independent. -/
@[sga "3 VIB 6.2.2" "partial"]
private lemma linearIndependent_of_linearIndependent_mkQ_comp_of_flat [Module.Flat R M]
    {I : Ideal R} (hI : IsNilpotent I) {x : ι → M}
    (hli : LinearIndependent (R ⧸ I) ((I • (⊤ : Submodule R M)).mkQ ∘ x))
    (hsp : Submodule.span R (Set.range x) = ⊤) : LinearIndependent R x := by
  have hsurj : Function.Surjective (Finsupp.linearCombination R x) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hsp
  refine linearIndependent_iff_ker.2 (Submodule.eq_bot_of_le_smul_of_isNilpotent I _ hI ?_)
  rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat I _ hsurj]
  exact le_inf le_rfl (ker_linearCombination_le_smul_top I hli)

end Aux

/-- Let `R` be a commutative ring, let `I ⊆ R` be a nilpotent ideal and let `M` be a flat
`R`-module. A family `x : ι → M`, indexed by an arbitrary type, is an `R`-basis of `M` if and only
if the family of its reductions is an `R/I`-basis of `M/IM`. "Is a basis" is read as
`LinearIndependent … ∧ Submodule.span … = ⊤`, the hypotheses of `Module.Basis.mk`. -/
@[stacks 051F "Stated for an arbitrary nilpotent ideal `I` of an arbitrary commutative ring, the
source's local ring being the case `I = IsLocalRing.maximalIdeal R`; `M/IM` is `M ⧸ I • ⊤` over
`R ⧸ I` with reduction map `Submodule.mkQ`, and `forms a basis` is
`LinearIndependent … ∧ Submodule.span … = ⊤`. See the module docstring.",
  sga "3 VIIA 7.4.3" "special case",
  sga "3 VIII 6.2" "flat clause"]
theorem linearIndependent_and_span_eq_top_mkQ_comp_iff_of_isNilpotent {R : Type*}
    [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Flat R M] (I : Ideal R)
    (hI : IsNilpotent I) {ι : Type*} (x : ι → M) :
    (LinearIndependent (R ⧸ I) ((I • (⊤ : Submodule R M)).mkQ ∘ x) ∧
        Submodule.span (R ⧸ I) (Set.range ((I • (⊤ : Submodule R M)).mkQ ∘ x)) = ⊤) ↔
      (LinearIndependent R x ∧ Submodule.span R (Set.range x) = ⊤) := by
  refine ⟨fun ⟨hli, hsp⟩ => ?_, fun ⟨hli, hsp⟩ =>
    linearIndependent_mkQ_comp_and_span_eq_top _ hli hsp⟩
  have hspan := span_eq_top_of_span_mkQ_comp_eq_top_of_isNilpotent hI hsp
  exact ⟨linearIndependent_of_linearIndependent_mkQ_comp_of_flat hI hli hspan, hspan⟩

universe u

/-! ### The local criterion over a local ring with nilpotent maximal ideal

Over a local ring `R` whose maximal ideal is nilpotent, `M` is flat over `R` if and only if, for a
proper ideal `I`, `M/IM` is flat over `R/I` and `Tor₁^R(R/I, M) = 0`. Here `Tor₁^R(R/I, M)` derives
the first variable (`Tor'`).
-/

open CategoryTheory Limits in
/-- The local criterion for flatness over a local ring with nilpotent maximal ideal (an Artinian
local ring, for instance). Let `R` be such a ring, let `M` be an `R`-module and
let `I ⊆ R` be a proper ideal. Then `M` is flat over `R` if and only if `M/IM` is flat over `R/I`
and `Tor₁^R(R/I, M) = 0`. Here `Tor₁^R(R/I, M)` is
`((Tor' (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)`, the first left
derived functor of `- ⊗ M` evaluated at `R ⧸ I`. -/
@[stacks 051K "The source's Artinian local `R` is weakened to `R` local with nilpotent maximal
ideal, the hypothesis of 051G; `Tor_1^R(R/I, M)` is `Tor'`, which derives the first variable, as
in 00MJ and 00M5. See the module docstring.",
  ega "0 10.1.3" "(i): c ⇔ d, c ⇔ d",
  ega "0 10.2.1" "a ⇒ b, a ⇔ b",
  ega "IV 11.2.5" "special case", sga "1 IV 5.5" "(i)⇔(ii), special case"]
theorem iff_flat_quotient_and_isZero_Tor'_one {R : Type u} [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (I : Ideal R)
    (hR : IsNilpotent (IsLocalRing.maximalIdeal R)) (hI : I ≠ ⊤) :
    Module.Flat R M ↔
      Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)) ∧
        IsZero (((Tor' (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)) := by
  have hbal := Iso.isZero_iff
    (((Tor_iso_Tor' R 1).app (ModuleCat.of R (R ⧸ I))).app (ModuleCat.of R M))
  constructor
  · intro hM
    exact ⟨Module.Flat.of_linearEquiv (LinearEquiv.extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective (TensorProduct.quotTensorEquivQuotSMul M I)).symm,
      (Iso.isZero_iff (((torFlip_iso_Tor' R 1).app (ModuleCat.of R (R ⧸ I))).app
        (ModuleCat.of R M))).1
        (Tor_iso_Tor'.tor_flat_isZero R (ModuleCat.of R M) (ModuleCat.of R (R ⧸ I)) 0)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨n, hn⟩ := hR
    refine flat_of_nilpotent I h1 (hbal.2 h2) ⟨max n 1, le_max_right _ _, le_antisymm ?_ bot_le⟩
    calc I ^ max n 1 ≤ IsLocalRing.maximalIdeal R ^ max n 1 :=
          Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hI) _
      _ ≤ IsLocalRing.maximalIdeal R ^ n := Ideal.pow_le_pow_right (le_max_left _ _)
      _ = ⊥ := hn

end Module.Flat

/-! ### Flatness and bijectivity modulo an ideal and its powers -/

/-- Flatness descends to the quotients by an ideal of the base and its extension. -/
public theorem flat_quotient_map {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (I : Ideal R) :
    let : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  let : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv

/-- A map intertwined with a bijection by equivalences on both sides is bijective. -/
private theorem bijective_of_equiv_comp_eq {α β γ δ : Type*} {f : α → β} {g : γ → δ}
    (eα : α ≃ γ) (eβ : β ≃ δ) (hg : Function.Bijective g) (h : ∀ x, eβ (f x) = g (eα x)) :
    Function.Bijective f := by
  have : f = eβ.symm ∘ g ∘ eα := funext fun x => eβ.eq_symm_apply.2 (h x)
  rw [this]
  exact eβ.symm.bijective.comp (hg.comp eα.bijective)

/-- For a flat algebra and a nilpotent ideal of the base, bijectivity of the induced map on
quotients lifts to bijectivity of the structure map itself. -/
public theorem bijective_algebraMap_of_flat_of_nilpotent {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I : Ideal A) (hI : IsNilpotent I)
    (h : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B))
       (algebraMap A B) Ideal.le_comap_map)) :
    Function.Bijective (algebraMap A B) := by
  let : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let E : (B ⧸ I • (⊤ : Submodule A B)) ≃ₗ[A]
      (B ⧸ I.map (algebraMap A B)) :=
    (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I)) ≪≫ₗ
      (Submodule.Quotient.restrictScalarsEquiv A (I.map (algebraMap A B)))
  let l : (A ⧸ I) →ₗ[A ⧸ I] (B ⧸ I • (⊤ : Submodule A B)) :=
    { toFun := fun a => a • ((I • (⊤ : Submodule A B)).mkQ 1)
      map_add' := by intro a b; simp [add_smul]
      map_smul' := by intro a b; simp [mul_smul] }
  have hc (a : A ⧸ I) : E (l a) = (Ideal.quotientMap (I.map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map) a := by
    induction a using Quotient.inductionOn with
    | _ a =>
      calc
        E (l (Ideal.Quotient.mk I a)) =
            E ((I • (⊤ : Submodule A B)).mkQ (a • (1 : B))) :=
              congrArg E (Module.Quotient.mk_smul_mk B I a (1 : B))
        _ = Ideal.Quotient.mk (I.map (algebraMap A B)) (a • (1 : B)) := rfl
        _ = (Ideal.quotientMap (I.map (algebraMap A B))
            (algebraMap A B) Ideal.le_comap_map) (Ideal.Quotient.mk I a) := by
              simp [Algebra.smul_def]
  have hl : Function.Bijective l :=
    bijective_of_equiv_comp_eq (Equiv.refl _) E.toEquiv h hc
  let b : Module.Basis Unit (A ⧸ I) (B ⧸ I • (⊤ : Submodule A B)) :=
    (Module.Basis.singleton Unit (A ⧸ I)).map (LinearEquiv.ofBijective l hl)
  have hb (i : Unit) : b i = (I • (⊤ : Submodule A B)).mkQ 1 := by
    simp [b, l, Module.Basis.singleton_apply]
  have hfun : ((I • (⊤ : Submodule A B)).mkQ ∘ fun _ : Unit => (1 : B)) = b :=
    funext fun i => (hb i).symm
  have hh := (Module.Flat.linearIndependent_and_span_eq_top_mkQ_comp_iff_of_isNilpotent I hI
    (fun _ : Unit => (1 : B))).mp (hfun ▸ ⟨b.linearIndependent, b.span_eq⟩)
  let bb : Module.Basis Unit A B := Module.Basis.mk hh.1 hh.2.ge
  have hbb (i : Unit) : bb i = 1 := Module.Basis.mk_apply hh.1 hh.2.ge i
  let F : A ≃ₗ[A] B := (Finsupp.uniqueLinearEquiv A A ()).symm ≪≫ₗ bb.repr.symm
  have hF (a : A) : F a = algebraMap A B a := by
    simp only [F, LinearEquiv.trans_apply, Finsupp.uniqueLinearEquiv_symm_apply,
      Module.Basis.repr_symm_single, hbb, Algebra.smul_def, mul_one]
  exact (funext hF : ⇑F = algebraMap A B) ▸ F.bijective

/-- Bijectivity of the map of quotients by a larger ideal passes to the quotients of the
quotients by a smaller one. -/
public theorem bijective_quotientMap_of_le_of_bijective {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    (I J : Ideal A) (hIJ : I ≤ J)
    (hJ : Function.Bijective (Ideal.quotientMap (J.map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map)) :
    let : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    Function.Bijective (Ideal.quotientMap
      ((J.map (Ideal.Quotient.mk I)).map
        (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))))
      (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))) Ideal.le_comap_map) := by
  let : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let f := algebraMap A B
  let fI := algebraMap (A ⧸ I) (B ⧸ I.map f)
  let IA := J.map (Ideal.Quotient.mk I)
  let JB := J.map f
  let IB := IA.map fI
  have hIB : IB = JB.map (Ideal.Quotient.mk (I.map f)) := by
    simp only [IB, IA, JB, Ideal.map_map]
    exact congrArg (fun g : A →+* (B ⧸ I.map f) => J.map g)
      (Ideal.quotientMap_comp_mk Ideal.le_comap_map)
  let eA : (A ⧸ I) ⧸ IA ≃+* A ⧸ J := DoubleQuot.quotQuotEquivQuotOfLE hIJ
  let eB : (B ⧸ I.map f) ⧸ JB.map (Ideal.Quotient.mk (I.map f)) ≃+* B ⧸ JB :=
    DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hIJ)
  let eB' : (B ⧸ I.map f) ⧸ IB ≃+* B ⧸ JB :=
    (Ideal.quotEquivOfEq hIB).trans eB
  have hcomm (x : (A ⧸ I) ⧸ IA) : eB' ((Ideal.quotientMap IB fI Ideal.le_comap_map) x) =
      (Ideal.quotientMap JB f Ideal.le_comap_map) (eA x) := by
    induction x using Quotient.inductionOn with
    | _ x =>
      induction x using Quotient.inductionOn with
      | _ a =>
        change eB ((Ideal.quotEquivOfEq hIB)
          (Ideal.Quotient.mk IB (fI (Ideal.Quotient.mk I a)))) =
          (Ideal.quotientMap JB f Ideal.le_comap_map)
            (eA (DoubleQuot.quotQuotMk I J a))
        rw [show fI (Ideal.Quotient.mk I a) = Ideal.Quotient.mk (I.map f) (f a) from rfl,
          Ideal.quotEquivOfEq_mk, DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk]
        change eB (DoubleQuot.quotQuotMk (I.map f) JB (f a)) =
          Ideal.Quotient.mk JB (f a)
        exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk _ _
  change Function.Bijective (Ideal.quotientMap IB fI Ideal.le_comap_map)
  exact bijective_of_equiv_comp_eq eA.toEquiv eB'.toEquiv hJ hcomm

/-- For a flat algebra, an isomorphism modulo an ideal induces isomorphisms modulo
all its powers. -/
@[sga "3 III 3.3" "special case"]
public theorem quotientMap_pow_bijective_of_flat {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (J : Ideal A)
    (hJ : Function.Bijective (Ideal.quotientMap (J.map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map)) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((J ^ n).map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map) := by
  rcases n with _ | n
  · have : Subsingleton (A ⧸ J ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    have : Subsingleton (B ⧸ (J ^ 0).map (algebraMap A B)) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp [Ideal.map_top])
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  let I := J ^ (n + 1)
  have hIJ : I ≤ J := Ideal.pow_le_self (Nat.succ_ne_zero n)
  let : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := flat_quotient_map I
  have hnil : IsNilpotent (J.map (Ideal.Quotient.mk I)) := by
    refine ⟨n + 1, ?_⟩
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self I
  exact bijective_algebraMap_of_flat_of_nilpotent _ hnil
    (bijective_quotientMap_of_le_of_bijective I J hIJ hJ)

end
