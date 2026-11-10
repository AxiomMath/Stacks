module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.RingTheory.Etale.DirectedColimitPresentation
public import StacksFrontier.RingTheory.FinitePresentation.QuotientMapBijectiveDescent

/-!
# The commutative algebra of an affine stage, for a directed system of quotients

Let `s, t : C →+* E` be two ring maps, and let `(K i)` be a directed family of ideals of `C` such
that `(K i) E` is the same ideal whether `E` is a `C`-algebra through `s` or through `t`. Put
`Cᵢ = C ⧸ K i` and `Eᵢ = E ⧸ (K i) E`, with the induced maps `s̄ᵢ, t̄ᵢ : Cᵢ ⇉ Eᵢ`, and
`K∞ = ⨆ K i`.
This is the shape of an affine étale chart `V = Spec C` of an algebraic space with affine
relation `R = Spec E`, restricted to a directed system of closed subspaces: `Cᵢ` and `Eᵢ` are
the rings of the restricted chart and of its relation.

This file proves the commutative-algebra steps of Stacks 07SQ for such a system.

## Main definitions

* `Stacks.AffineStageCore.sBar`, `Stacks.AffineStageCore.tBar`: the maps `C ⧸ I ⇉ E ⧸ I E`.
* `Stacks.AffineStageCore.eqStage`: their equalizer, as a subring of `C ⧸ I`.

## Main results

* `Stacks.AffineStageCore.range_eq_eqLocus_of_bijective`: if `A → D` is faithfully flat and
  `D ⊗_A D → F` is bijective, then the image of `A` is the equalizer of `D ⇉ F`.
* `Stacks.AffineStageCore.exists_eqStage_of_mem_eqStage_iSup` and
  `Stacks.AffineStageCore.exists_eqStage_eq_zero_of_factor_eq_zero`: the equalizer of the
  colimit is the colimit of the stagewise equalizers.
* `Stacks.AffineStageCore.exists_presentation_of_etale`: an étale algebra has a global
  presentation by a square system of polynomials with invertible Jacobian determinant
  (Stacks 00U9).

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public section

noncomputable section

open TensorProduct

universe u v

namespace Stacks.AffineStageCore

variable {C E : Type u} [CommRing C] [CommRing E] (s t : C →+* E)

/-! ### The two maps of a quotient, and their equalizer -/

/-- The map `C ⧸ I →+* E ⧸ I E` induced by `s`, where `I E` is the extension along `s`. -/
def sBar (I : Ideal C) : C ⧸ I →+* E ⧸ I.map s :=
  Ideal.quotientMap (I.map s) s Ideal.le_comap_map

/-- The map `C ⧸ I →+* E ⧸ I E` induced by `t`, when the extensions of `I` along `s` and `t`
agree. -/
def tBar (I : Ideal C) (h : I.map t = I.map s) : C ⧸ I →+* E ⧸ I.map s :=
  Ideal.quotientMap (I.map s) t (by rw [← h]; exact Ideal.le_comap_map)

/-- `sBar s I` sends the class of `c` to the class of `s c`. -/
@[simp] theorem sBar_mk (I : Ideal C) (c : C) :
    sBar s I (Ideal.Quotient.mk I c) = Ideal.Quotient.mk (I.map s) (s c) := rfl

/-- `tBar s t I h` sends the class of `c` to the class of `t c`. -/
@[simp] theorem tBar_mk (I : Ideal C) (h : I.map t = I.map s) (c : C) :
    tBar s t I h (Ideal.Quotient.mk I c) = Ideal.Quotient.mk (I.map s) (t c) := rfl

/-- The equalizer of `C ⧸ I ⇉ E ⧸ I E`. -/
def eqStage (I : Ideal C) (h : I.map t = I.map s) : Subring (C ⧸ I) :=
  (sBar s I).eqLocus (tBar s t I h)

/-- Membership in `eqStage` is equality of the two images. -/
theorem mem_eqStage_iff (I : Ideal C) (h : I.map t = I.map s) (x : C ⧸ I) :
    x ∈ eqStage s t I h ↔ sBar s I x = tBar s t I h x := Iff.rfl

/-- The extension along `s` of a quotient map of ideals: for `I ≤ J`, the map
`E ⧸ I E → E ⧸ J E`. -/
def factorE {I J : Ideal C} (hIJ : I ≤ J) : E ⧸ I.map s →+* E ⧸ J.map s :=
  Ideal.Quotient.factor (Ideal.map_mono hIJ)

/-- `sBar` commutes with the quotient maps along `I ≤ J`. -/
theorem sBar_factor {I J : Ideal C} (hIJ : I ≤ J) (x : C ⧸ I) :
    sBar s J (Ideal.Quotient.factor hIJ x) = factorE s hIJ (sBar s I x) := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- `tBar` commutes with the quotient maps along `I ≤ J`. -/
theorem tBar_factor {I J : Ideal C} (hIJ : I ≤ J) (hI : I.map t = I.map s)
    (hJ : J.map t = J.map s) (x : C ⧸ I) :
    tBar s t J hJ (Ideal.Quotient.factor hIJ x) = factorE s hIJ (tBar s t I hI x) := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The transition map of equalizers along `I ≤ J`. -/
def eqStageMap {I J : Ideal C} (hIJ : I ≤ J) (hI : I.map t = I.map s)
    (hJ : J.map t = J.map s) : eqStage s t I hI →+* eqStage s t J hJ :=
  ((Ideal.Quotient.factor hIJ).comp (eqStage s t I hI).subtype).codRestrict _ fun x => by
    change sBar s J (Ideal.Quotient.factor hIJ x.1) = tBar s t J hJ (Ideal.Quotient.factor hIJ x.1)
    rw [sBar_factor, tBar_factor s t hIJ hI hJ, x.2]

/-- The transition map of equalizers is the quotient map on underlying elements. -/
@[simp] theorem coe_eqStageMap {I J : Ideal C} (hIJ : I ≤ J) (hI : I.map t = I.map s)
    (hJ : J.map t = J.map s) (x : eqStage s t I hI) :
    (eqStageMap s t hIJ hI hJ x : C ⧸ J) = Ideal.Quotient.factor hIJ x := rfl

/-! ### The equalizer of the colimit is the colimit of the equalizers -/

section Directed

variable {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (K : ι → Ideal C)
  (hK : Monotone K) (hinv : ∀ i, (K i).map t = (K i).map s)

include hK in
/-- An element lies in the supremum of a monotone directed family of ideals exactly when it lies
in one of them. -/
theorem mem_iSup_iff_exists (c : C) : c ∈ ⨆ i, K i ↔ ∃ i, c ∈ K i :=
  Submodule.mem_iSup_of_directed K (hK.directed_le)

omit [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] in
include hinv in
/-- The extensions along `s` and `t` of `⨆ K i` agree. -/
theorem map_iSup_inv : (⨆ i, K i).map t = (⨆ i, K i).map s := by
  rw [Ideal.map_iSup, Ideal.map_iSup]
  exact iSup_congr hinv

include hK in
/-- An element lies in the extension along `s` of `⨆ i, K i` exactly when it lies in the extension
of some `K i`. -/
theorem map_iSup_mem_iff_exists (e : E) : e ∈ (⨆ i, K i).map s ↔ ∃ i, e ∈ (K i).map s := by
  rw [Ideal.map_iSup]
  exact Submodule.mem_iSup_of_directed _ (fun i j => by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact ⟨k, Ideal.map_mono (hK hik), Ideal.map_mono (hK hjk)⟩)

include hK in
/-- **Every element of the equalizer of the colimit comes from a stage.** -/
theorem exists_eqStage_of_mem_eqStage_iSup (x : C ⧸ ⨆ i, K i)
    (hx : x ∈ eqStage s t (⨆ i, K i) (map_iSup_inv s t K hinv)) :
    ∃ (i : ι) (y : eqStage s t (K i) (hinv i)),
      Ideal.Quotient.factor (le_iSup K i) (y : C ⧸ K i) = x := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : s c - t c ∈ (⨆ i, K i).map s := by
    rw [← Ideal.Quotient.eq]
    exact hx
  obtain ⟨i, hi⟩ := (map_iSup_mem_iff_exists s K hK _).1 hx'
  refine ⟨i, ⟨Ideal.Quotient.mk (K i) c, ?_⟩, rfl⟩
  change Ideal.Quotient.mk _ (s c) = Ideal.Quotient.mk _ (t c)
  exact Ideal.Quotient.eq.2 hi

include hK in
/-- **An element of a stagewise equalizer which dies in the colimit dies at a later stage.** -/
theorem exists_eqStage_eq_zero_of_factor_eq_zero (i : ι) (y : C ⧸ K i)
    (hy : Ideal.Quotient.factor (le_iSup K i) y = 0) :
    ∃ (j : ι) (hij : i ≤ j), Ideal.Quotient.factor (hK hij) y = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hc : c ∈ ⨆ i, K i := Ideal.Quotient.eq_zero_iff_mem.1 hy
  obtain ⟨j, hj⟩ := (mem_iSup_iff_exists K hK c).1 hc
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  exact ⟨k, hik, Ideal.Quotient.eq_zero_iff_mem.2 (hK hjk hj)⟩

end Directed

/-! ### A faithfully flat effective quotient is the equalizer -/

section Effective

variable {D D' F A : Type u} [CommRing D] [CommRing D'] [CommRing F] [CommRing A] [Algebra A D]
  [Algebra A D'] (σ : D →+* F) (τ : D' →+* F)

/-- The map `D ⊗_A D' → F`, `d ⊗ d' ↦ σ d * τ d'`, for two ring maps agreeing on `A`. -/
def tensorLift (hστ : σ.comp (algebraMap A D) = τ.comp (algebraMap A D')) : D ⊗[A] D' →+* F :=
  letI : Algebra A F := (σ.comp (algebraMap A D)).toAlgebra
  (Algebra.TensorProduct.lift
    (⟨σ, fun _ => rfl⟩ : D →ₐ[A] F)
    (⟨τ, fun a => by
      change τ (algebraMap A D' a) = σ (algebraMap A D a)
      exact (congrArg (fun f : A →+* F => f a) hστ).symm⟩ : D' →ₐ[A] F)
    (fun _ _ => Commute.all _ _)).toRingHom

/-- `tensorLift σ τ hστ` sends `d ⊗ d'` to `σ d * τ d'`. -/
@[simp] theorem tensorLift_tmul (hστ : σ.comp (algebraMap A D) = τ.comp (algebraMap A D'))
    (d : D) (d' : D') : tensorLift σ τ hστ (d ⊗ₜ d') = σ d * τ d' := by
  simp [tensorLift]

/-- **A faithfully flat effective quotient is the equalizer.** If `A → D` is faithfully flat and
`D ⊗_A D → F` (through `σ` and `τ`) is bijective, then the image of `A` in `D` is the equalizer
of `σ` and `τ`. -/
theorem range_eq_eqLocus_of_bijective [Module.FaithfullyFlat A D] (σ τ : D →+* F)
    (hστ : σ.comp (algebraMap A D) = τ.comp (algebraMap A D))
    (hbij : Function.Bijective (tensorLift σ τ hστ)) :
    Set.range (algebraMap A D) = σ.eqLocus τ := by
  rw [← (Algebra.IsEffective.of_faithfullyFlat (R := A) (S := D)).eqLocus_includeLeft_includeRight]
  ext d
  change d ⊗ₜ[A] (1 : D) = (1 : D) ⊗ₜ[A] d ↔ σ d = τ d
  constructor
  · intro h
    have := congrArg (tensorLift σ τ hστ) h
    simpa using this
  · intro h
    apply hbij.1
    simp [h]

end Effective

/-! ### A global presentation of an étale algebra -/

/-- **Stacks 00U9, a global standard presentation of an étale algebra.** An étale `A`-algebra `D`
is `A[x_k : k ∈ κ] ⧸ (g_k)` for a finite square family of polynomials whose Jacobian determinant
is invertible in the quotient. -/
theorem exists_presentation_of_etale {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.Etale A D] :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (g : κ → MvPolynomial κ A),
      Nonempty ((MvPolynomial κ A ⧸ Ideal.span (Set.range g)) ≃ₐ[A] D) ∧
      IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.detJacobian g)) := by
  classical
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension 0 A D :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 inferInstance
  obtain ⟨ι, σ, _, _, P, hP⟩ := hstd.out
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype σ := Fintype.ofFinite σ
  have hcard : Nat.card ι ≤ Nat.card σ := by
    have : Nat.card ι - Nat.card σ = 0 := hP
    omega
  have hbij : Function.Bijective P.map :=
    (Function.Injective.bijective_of_nat_card_le P.map_inj hcard)
  let e : σ ≃ ι := Equiv.ofBijective P.map hbij
  let Q := P.reindex (Equiv.refl ι) e.symm
  have hmap : ∀ k, Q.map k = k := fun k => e.apply_symm_apply k
  refine ⟨ι, inferInstance, inferInstance, Q.relation, ⟨?_⟩, ?_⟩
  · have hspan : Ideal.span (Set.range Q.relation) = Q.ker := Q.span_range_relation_eq_ker
    exact (Ideal.quotientEquivAlgOfEq A hspan).trans
      (Q.quotientEquiv.restrictScalars A)
  · have hjac : Q.jacobian = algebraMap Q.Ring D (MvPolynomial.detJacobian Q.relation) := by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
      congr 2
      ext a b
      rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hmap]
      rfl
    have hunit : IsUnit Q.jacobian := Q.jacobian_isUnit
    rw [hjac] at hunit
    have hspan : Ideal.span (Set.range Q.relation) = Q.ker := Q.span_range_relation_eq_ker
    let φ : (MvPolynomial ι A ⧸ Ideal.span (Set.range Q.relation)) ≃+* D :=
      ((Ideal.quotientEquivAlgOfEq A hspan).trans (Q.quotientEquiv.restrictScalars A)).toRingEquiv
    have hφ : φ (Ideal.Quotient.mk _ (MvPolynomial.detJacobian Q.relation)) =
        algebraMap Q.Ring D (MvPolynomial.detJacobian Q.relation) := rfl
    rw [← hφ] at hunit
    exact (isUnit_map_iff φ _).1 hunit

/-! ### The colimit maps to the effective quotient -/

section Colimit

variable {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (K : ι → Ideal C)
  (hK : Monotone K) (hinv : ∀ i, (K i).map t = (K i).map s)
  (A : Type u) [CommRing A] [Algebra A (C ⧸ ⨆ i, K i)]
  [Module.FaithfullyFlat A (C ⧸ ⨆ i, K i)]
  (hst : (sBar s (⨆ i, K i)).comp (algebraMap A _) =
    (tBar s t _ (map_iSup_inv s t K hinv)).comp (algebraMap A _))
  (hbij : Function.Bijective (tensorLift (sBar s _) (tBar s t _ (map_iSup_inv s t K hinv)) hst))

omit [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] in
include hbij in
/-- `A` maps isomorphically onto the equalizer of `C∞ ⇉ E∞`. -/
theorem bijective_colimRestrict :
    Function.Bijective ((algebraMap A (C ⧸ ⨆ i, K i)).codRestrict
      (eqStage s t (⨆ i, K i) (map_iSup_inv s t K hinv)) fun a => by
        change sBar s _ (algebraMap A _ a) = tBar s t _ _ (algebraMap A _ a)
        exact congrArg (fun f : A →+* E ⧸ _ => f a) hst) := by
  refine ⟨fun a b hab => FaithfulSMul.algebraMap_injective A (C ⧸ ⨆ i, K i)
    (congrArg Subtype.val hab), fun ⟨x, hx⟩ => ?_⟩
  have hr :=
    range_eq_eqLocus_of_bijective (sBar s _) (tBar s t _ (map_iSup_inv s t K hinv)) hst hbij
  have : x ∈ Set.range (algebraMap A (C ⧸ ⨆ i, K i)) := by rw [hr]; exact hx
  obtain ⟨a, rfl⟩ := this
  exact ⟨a, rfl⟩

/-- The isomorphism of `A` onto the equalizer of `C∞ ⇉ E∞`. -/
def colimEquiv : A ≃+* eqStage s t (⨆ i, K i) (map_iSup_inv s t K hinv) :=
  RingEquiv.ofBijective _ (bijective_colimRestrict s t K hinv A hst hbij)

omit [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- `colimEquiv` is `algebraMap A (C ⧸ ⨆ i, K i)` on underlying elements. -/
@[simp] theorem coe_colimEquiv (a : A) :
    (colimEquiv s t K hinv A hst hbij a : C ⧸ ⨆ i, K i) = algebraMap A _ a := rfl

/-- The map from the stagewise equalizer to `A`. -/
def colimMap (i : ι) : eqStage s t (K i) (hinv i) →+* A :=
  (colimEquiv s t K hinv A hst hbij).symm.toRingHom.comp
    (eqStageMap s t (le_iSup K i) (hinv i) (map_iSup_inv s t K hinv))

omit [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- The image in `C∞` of `colimMap` of a stagewise equalizer element is its class in `C∞`. -/
theorem algebraMap_colimMap (i : ι) (y : eqStage s t (K i) (hinv i)) :
    algebraMap A (C ⧸ ⨆ i, K i) (colimMap s t K hinv A hst hbij i y) =
      Ideal.Quotient.factor (le_iSup K i) (y : C ⧸ K i) := by
  rw [← coe_colimEquiv s t K hinv A hst hbij]
  simp [colimMap]

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- `colimMap` is compatible with the transition maps of equalizers. -/
theorem colimMap_comp {i j : ι} (hij : i ≤ j) (y : eqStage s t (K i) (hinv i)) :
    colimMap s t K hinv A hst hbij j (eqStageMap s t (hK hij) (hinv i) (hinv j) y) =
      colimMap s t K hinv A hst hbij i y := by
  apply FaithfulSMul.algebraMap_injective A (C ⧸ ⨆ i, K i)
  rw [algebraMap_colimMap, algebraMap_colimMap, coe_eqStageMap, Ideal.Quotient.factor_comp_apply]

include hK in
/-- Every element of `A` is `colimMap` of an element of some stagewise equalizer. -/
theorem exists_colimMap_eq (a : A) :
    ∃ (i : ι) (y : eqStage s t (K i) (hinv i)), colimMap s t K hinv A hst hbij i y = a := by
  obtain ⟨i, y, hy⟩ := exists_eqStage_of_mem_eqStage_iSup s t K hK hinv
    (algebraMap A _ a) (colimEquiv s t K hinv A hst hbij a).2
  refine ⟨i, y, FaithfulSMul.algebraMap_injective A (C ⧸ ⨆ i, K i) ?_⟩
  rw [algebraMap_colimMap, hy]

include hK in
/-- A stagewise equalizer element whose `colimMap` vanishes already vanishes at a later stage. -/
theorem exists_eqStageMap_eq_zero (i : ι) (y : eqStage s t (K i) (hinv i))
    (hy : colimMap s t K hinv A hst hbij i y = 0) :
    ∃ (j : ι) (hij : i ≤ j), eqStageMap s t (hK hij) (hinv i) (hinv j) y = 0 := by
  have h0 : Ideal.Quotient.factor (le_iSup K i) (y : C ⧸ K i) = 0 := by
    rw [← algebraMap_colimMap s t K hinv A hst hbij, hy, map_zero]
  obtain ⟨j, hij, hj⟩ := exists_eqStage_eq_zero_of_factor_eq_zero K hK i y h0
  exact ⟨j, hij, Subtype.ext hj⟩

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
include hK in
/-- The stagewise equalizers, with the maps `eqStageMap`, form a directed system. -/
theorem directedSystem_eqStageMap :
    DirectedSystem (fun i => eqStage s t (K i) (hinv i))
      (fun i j h => eqStageMap s t (hK h) (hinv i) (hinv j)) where
  map_self i y := Subtype.ext (by simp)
  map_map k j i hij hjk y := Subtype.ext (by simp [Ideal.Quotient.factor_comp_apply])

include hK in
/-- **The étale presentation of `C∞` over `A` descends to a stage**, above any given stage, as
an étale algebra with surjective spectrum map over the equalizer at that stage. -/
theorem exists_stage_presentation [Algebra.Etale A (C ⧸ ⨆ i, K i)] (i₀ : ι) :
    ∃ (m : ι) (_ : i₀ ≤ m) (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
      (q : κ → MvPolynomial κ (eqStage s t (K m) (hinv m))),
      Algebra.Etale (eqStage s t (K m) (hinv m))
        (MvPolynomial κ (eqStage s t (K m) (hinv m)) ⧸ Ideal.span (Set.range q)) ∧
      Function.Surjective (PrimeSpectrum.comap (algebraMap (eqStage s t (K m) (hinv m))
        (MvPolynomial κ (eqStage s t (K m) (hinv m)) ⧸ Ideal.span (Set.range q)))) ∧
      Nonempty ((MvPolynomial κ A ⧸ Ideal.span (Set.range fun k =>
          MvPolynomial.map (colimMap s t K hinv A hst hbij m) (q k))) ≃ₐ[A] C ⧸ ⨆ i, K i) := by
  classical
  have := directedSystem_eqStageMap s t K hK hinv
  have hφ : ∀ i j (h : i ≤ j) (x : eqStage s t (K i) (hinv i)),
      colimMap s t K hinv A hst hbij j (eqStageMap s t (hK h) (hinv i) (hinv j) x) =
        colimMap s t K hinv A hst hbij i x :=
    fun i j h x => colimMap_comp s t K hK hinv A hst hbij h x
  have hsurj := exists_colimMap_eq s t K hK hinv A hst hbij
  have hzero : ∀ (i : ι) (x : eqStage s t (K i) (hinv i)),
      colimMap s t K hinv A hst hbij i x = 0 → ∃ (j : ι) (h : i ≤ j),
        eqStageMap s t (hK h) (hinv i) (hinv j) x = 0 :=
    fun i x hx => exists_eqStageMap_eq_zero s t K hK hinv A hst hbij i x hx
  obtain ⟨κ, _, _, g, ⟨e⟩, hdet⟩ := exists_presentation_of_etale (A := A) (D := C ⧸ ⨆ i, K i)
  obtain ⟨j₀, hj₀, q₀, hq₀⟩ := MvPolynomial.exists_ge_forall_map_eq_square_of_directed
    (f := fun i j h => eqStageMap s t (hK h) (hinv i) (hinv j)) hφ hsurj g i₀
  let θ₀ : (MvPolynomial κ (eqStage s t (K j₀) (hinv j₀)) ⧸ Ideal.span (Set.range q₀)) →+*
      C ⧸ ⨆ i, K i :=
    e.toRingHom.comp (Ideal.quotientMap _ (MvPolynomial.map (colimMap s t K hinv A hst hbij j₀))
      (by
        rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        exact Ideal.subset_span ⟨k, by rw [← hq₀ k]⟩))
  have hcomm : (algebraMap A (C ⧸ ⨆ i, K i)).comp (colimMap s t K hinv A hst hbij j₀) =
      θ₀.comp (algebraMap _ _) := by
    ext x
    simp [θ₀, MvPolynomial.map_C]
    rfl
  obtain ⟨j₁, hj₁, hsurj₁⟩ := MvPolynomial.exists_ge_surjective_comap_quotient_of_directed
    (f := fun i j h => eqStageMap s t (hK h) (hinv i) (hinv j)) hφ hsurj hzero q₀
    (algebraMap A (C ⧸ ⨆ i, K i)) θ₀ hcomm PrimeSpectrum.comap_surjective_of_faithfullyFlat
  have hmap : ∀ (i j : ι) (h : i ≤ j) (p : MvPolynomial κ (eqStage s t (K i) (hinv i))),
      MvPolynomial.map (colimMap s t K hinv A hst hbij j)
        (MvPolynomial.map (eqStageMap s t (hK h) (hinv i) (hinv j)) p) =
        MvPolynomial.map (colimMap s t K hinv A hst hbij i) p := fun i j h p => by
    rw [MvPolynomial.map_map]
    exact congrArg (fun f => MvPolynomial.map f p) (RingHom.ext (hφ i j h))
  let q₁ := fun k => MvPolynomial.map (eqStageMap s t (hK hj₁) (hinv j₀) (hinv j₁)) (q₀ k)
  have hq₁ : ∀ k, MvPolynomial.map (colimMap s t K hinv A hst hbij j₁) (q₁ k) = g k :=
    fun k => (hmap j₀ j₁ hj₁ _).trans (hq₀ k)
  -- invertibility of the Jacobian at a stage `m ≥ j₁`
  have hq₁g : (fun k => MvPolynomial.map (colimMap s t K hinv A hst hbij j₁) (q₁ k)) = g :=
    funext hq₁
  obtain ⟨m, hm, hunit⟩ := MvPolynomial.exists_ge_isUnit_detJacobian_of_directed
    (f := fun i j h => eqStageMap s t (hK h) (hinv i) (hinv j)) hφ hsurj hzero q₁
    (by rw [hq₁g]; exact hdet)
  let q := fun k => MvPolynomial.map (eqStageMap s t (hK hm) (hinv j₁) (hinv m)) (q₁ k)
  refine ⟨m, hj₀.trans (hj₁.trans hm), κ, inferInstance, inferInstance, q,
    Algebra.etale_mvPolynomialQuotient_of_isUnit_det _ hunit, ?_, ?_⟩
  · -- surjectivity transports from `j₁` to `m` by base change
    obtain ⟨eq⟩ := MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_le
      (f := fun i j h => eqStageMap s t (hK h) (hinv i) (hinv j)) hm q₁
    let := (eqStageMap s t (hK hm) (hinv j₁) (hinv m)).toAlgebra
    refine PrimeSpectrum.surjective_comap_algebraMap_of_algEquiv eq fun x => ?_
    exact PrimeSpectrum.mem_range_comap_tensorProduct_of_mem_range_comap x (hsurj₁ _)
  · have hqm : (fun k => MvPolynomial.map (colimMap s t K hinv A hst hbij m) (q k)) = g :=
      funext fun k => (hmap j₁ m hm _).trans (hq₁ k)
    rw [hqm]
    exact ⟨e⟩

end Colimit

/-! ### Reducing a tensor product modulo an ideal of the base -/

section QuotientTensor

variable {A' R B Q D F : Type u} [CommRing A'] [CommRing R] [CommRing B] [CommRing Q]
  [CommRing D] [CommRing F] [Algebra A' R] [Algebra A' B] [Algebra R Q] [Algebra A' D]
  (φ : R ⊗[A'] B →ₐ[R] Q) (J : Ideal R) (e₁ : R ⧸ J ≃+* D)
  (he₁ : ∀ a, e₁ (Ideal.Quotient.mk J (algebraMap A' R a)) = algebraMap A' D a)
  (e₂ : Q ⧸ J.map (algebraMap R Q) ≃+* F) (σ : D →+* F) (τ : B →+* F)
  (hστ : σ.comp (algebraMap A' D) = τ.comp (algebraMap A' B))
  (hσ : ∀ r, σ (e₁ (Ideal.Quotient.mk J r)) =
    e₂ (Ideal.Quotient.mk _ (algebraMap R Q r)))
  (hτ : ∀ b, τ b = e₂ (Ideal.Quotient.mk _ (φ (1 ⊗ₜ b))))

include he₁ hσ hτ in
/-- **Reducing `φ : R ⊗_{A'} B → Q` modulo an ideal `J` of `R`.** If `R ⧸ J ≅ D` and
`Q ⧸ J Q ≅ F` are compatible with the maps, then `φ` is bijective modulo `J` exactly when the
map `D ⊗_{A'} B → F` it induces is bijective. -/
theorem bijective_quotientMap_iff_bijective_tensorLift :
    Function.Bijective (Ideal.quotientMap (J.map (algebraMap R Q)) φ.toRingHom
      (φ.map_algebraMap_le_comap J)) ↔ Function.Bijective (tensorLift σ τ hστ) := by
  let e₁' : (R ⧸ J) ≃ₐ[A'] D :=
    { e₁ with
      commutes' := fun a => by
        change e₁ (algebraMap A' (R ⧸ J) a) = _
        exact he₁ a }
  let ε : (R ⊗[A'] B) ⧸ J.map (algebraMap R (R ⊗[A'] B)) ≃+* D ⊗[A'] B :=
    ((Algebra.TensorProduct.quotientTensorEquiv (R := A') R B R J).symm.toRingEquiv).trans
      (Algebra.TensorProduct.congr e₁' AlgEquiv.refl).toRingEquiv
  have key : (Ideal.quotientMap (J.map (algebraMap R Q)) φ.toRingHom
      (φ.map_algebraMap_le_comap J)) =
      (e₂.symm.toRingHom.comp (tensorLift σ τ hστ)).comp ε.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply Algebra.TensorProduct.ringHom_ext
    · ext r
      apply e₂.injective
      simp only [RingHom.comp_apply, Ideal.quotientMap_mk, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      change e₂ (Ideal.Quotient.mk _ (φ (r ⊗ₜ 1))) =
        tensorLift σ τ hστ (ε (Ideal.Quotient.mk _ (r ⊗ₜ 1)))
      have : φ (r ⊗ₜ 1) = algebraMap R Q r := by
        have h1 : (r ⊗ₜ (1 : B) : R ⊗[A'] B) = r • (1 : R ⊗[A'] B) := by
          rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h1, map_smul, map_one, Algebra.smul_def, mul_one]
      rw [this, ← hσ]
      simp [ε, e₁']
    · ext b
      apply e₂.injective
      simp only [RingHom.comp_apply, Ideal.quotientMap_mk, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      change e₂ (Ideal.Quotient.mk _ (φ (1 ⊗ₜ b))) =
        tensorLift σ τ hστ (ε (Ideal.Quotient.mk _ (1 ⊗ₜ b)))
      rw [← hτ]
      simp [ε, e₁']
  rw [key]
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [Function.Bijective.of_comp_iff _ ε.bijective,
    Function.Bijective.of_comp_iff' e₂.symm.bijective]

end QuotientTensor

/-! ### Changing the base of an effective quotient -/

section ChangeBase

variable {A' A D F B : Type u} [CommRing A'] [CommRing A] [CommRing D] [CommRing F] [CommRing B]
  [Algebra A' A] [Algebra A D] [Algebra A' D] [IsScalarTower A' A D] [Algebra A' B]
  (σ τ : D →+* F) (hστ : σ.comp (algebraMap A D) = τ.comp (algebraMap A D)) (θ : B →ₐ[A'] D)

include hστ in
/-- The compatibility on `A'` needed to form `tensorLift σ (τ.comp θ)`. -/
theorem tensorLift_comp_cond :
    σ.comp (algebraMap A' D) = (τ.comp θ.toRingHom).comp (algebraMap A' B) := by
  ext a
  have h := congrArg (fun f : A →+* F => f (algebraMap A' A a)) hστ
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply] at h
  simpa using h

/-- **Bijectivity of an effective quotient survives a change of base presenting `D`.** If
`D ⊗_A D → F` is bijective and `A ⊗_{A'} B → D`, `a ⊗ b ↦ a θ(b)`, is bijective, then
`D ⊗_{A'} B → F`, `d ⊗ b ↦ σ d · τ (θ b)`, is bijective. -/
theorem bijective_tensorLift_comp
    (hΞ : Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId A D) θ
      (fun _ _ => Commute.all _ _)))
    (hbij : Function.Bijective (tensorLift σ τ hστ)) :
    Function.Bijective
      (tensorLift σ (τ.comp θ.toRingHom) (tensorLift_comp_cond (A := A) σ τ hστ θ)) := by
  let Ξ : A ⊗[A'] B ≃ₐ[A] D := AlgEquiv.ofBijective _ hΞ
  let ε : D ⊗[A'] B ≃+* D ⊗[A] D :=
    ((Algebra.TensorProduct.cancelBaseChange A' A A D B).symm.toRingEquiv).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[A] D) Ξ).toRingEquiv
  have key : tensorLift σ (τ.comp θ.toRingHom) (tensorLift_comp_cond (A := A) σ τ hστ θ) =
      (tensorLift σ τ hστ).comp ε.toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext d
      have : Ξ (1 ⊗ₜ[A'] 1) = 1 := by rw [← Algebra.TensorProduct.one_def, map_one]
      simp [ε, this]
    · ext b
      simp [ε, Ξ]
  rw [key, RingHom.coe_comp]
  exact hbij.comp ε.bijective

end ChangeBase

section Lift

variable {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (K : ι → Ideal C)
  (hK : Monotone K) (hinv : ∀ i, (K i).map t = (K i).map s)

include hK in
/-- **The coordinates of a presentation lift to a stage.** A ring map from a finitely presented
algebra over the stagewise equalizer at `m` to `C∞`, which is the inclusion on the equalizer,
factors through `C ⧸ K k` for some `k ≥ m`. -/
theorem exists_stage_lift {m : ι} {κ : Type} [Finite κ]
    (q : κ → MvPolynomial κ (eqStage s t (K m) (hinv m)))
    (θ : (MvPolynomial κ (eqStage s t (K m) (hinv m)) ⧸ Ideal.span (Set.range q)) →+*
      C ⧸ ⨆ i, K i)
    (hθ : ∀ a : eqStage s t (K m) (hinv m),
      θ (algebraMap (eqStage s t (K m) (hinv m)) _ a) =
        Ideal.Quotient.factor (le_iSup K m) (a : C ⧸ K m)) :
    ∃ (k : ι) (hmk : m ≤ k)
      (h : (MvPolynomial κ (eqStage s t (K m) (hinv m)) ⧸ Ideal.span (Set.range q)) →+* C ⧸ K k),
      (∀ a : eqStage s t (K m) (hinv m), h (algebraMap (eqStage s t (K m) (hinv m)) _ a) =
        Ideal.Quotient.factor (hK hmk) (a : C ⧸ K m)) ∧
      (Ideal.Quotient.factor (le_iSup K k)).comp h = θ := by
  classical
  have := Fintype.ofFinite κ
  choose c hc using fun ν : κ => Ideal.Quotient.mk_surjective
    (θ (Ideal.Quotient.mk _ (MvPolynomial.X ν)))
  let H : MvPolynomial κ (eqStage s t (K m) (hinv m)) →+* C ⧸ K m :=
    MvPolynomial.eval₂Hom (eqStage s t (K m) (hinv m)).subtype fun ν => Ideal.Quotient.mk _ (c ν)
  have hH : (Ideal.Quotient.factor (le_iSup K m)).comp H = θ.comp (Ideal.Quotient.mk _) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, RingHom.comp_apply,
        show Ideal.Quotient.mk (Ideal.span (Set.range q)) (MvPolynomial.C a) =
          algebraMap (eqStage s t (K m) (hinv m)) _ a from rfl, hθ a]
      simp [H]
    · intro ν
      simp [H, hc ν]
  have hzero : ∀ ν : κ, ∃ (k : ι) (h : m ≤ k), Ideal.Quotient.factor (hK h) (H (q ν)) = 0 := by
    intro ν
    refine exists_eqStage_eq_zero_of_factor_eq_zero K hK m (H (q ν)) ?_
    have := congrArg (fun f => f (q ν)) hH
    simp only [RingHom.comp_apply] at this
    rw [this, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self ν)), map_zero]
  choose kν hkν hkν0 using hzero
  obtain ⟨k, hk⟩ := Finset.exists_le (insert m (Finset.univ.image kν))
  have hmk : m ≤ k := hk m (Finset.mem_insert_self _ _)
  have hνk : ∀ ν, kν ν ≤ k := fun ν => hk _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
    (Finset.mem_univ ν)))
  have hker : Ideal.span (Set.range q) ≤ RingHom.ker ((Ideal.Quotient.factor (hK hmk)).comp H) := by
    rw [Ideal.span_le]
    rintro _ ⟨ν, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply,
      ← Ideal.Quotient.factor_comp_apply (hK (hkν ν)) (hK (hνk ν)), hkν0 ν, map_zero]
  refine ⟨k, hmk, Ideal.Quotient.lift _ _ fun x hx => hker hx, fun a => ?_, ?_⟩
  · change Ideal.Quotient.factor (hK hmk) (H (MvPolynomial.C a)) = _
    simp [H]
  · apply Ideal.Quotient.ringHom_ext
    rw [← hH]
    refine RingHom.ext fun p => ?_
    change Ideal.Quotient.factor (le_iSup K k) (Ideal.Quotient.factor (hK hmk) (H p)) =
      Ideal.Quotient.factor (le_iSup K m) (H p)
    exact Ideal.Quotient.factor_comp_apply _ _ _

end Lift

/-- `tensorLift` depends only on the maps, not on the proof of their compatibility. -/
theorem tensorLift_congr {D D' F A : Type u} [CommRing D] [CommRing D'] [CommRing F] [CommRing A]
    [Algebra A D] [Algebra A D'] (σ : D →+* F) {τ τ' : D' →+* F} (hτ : τ = τ')
    (h : σ.comp (algebraMap A D) = τ.comp (algebraMap A D')) :
    tensorLift σ τ h = tensorLift σ τ' (hτ ▸ h) := by
  subst hτ; rfl

/-- An element of the equalizer at `I` stays in the equalizer at any larger `J`. -/
theorem sBar_factor_eq_tBar_factor {I J : Ideal C} (hIJ : I ≤ J) (hI : I.map t = I.map s)
    (hJ : J.map t = J.map s) (a : eqStage s t I hI) :
    sBar s J (Ideal.Quotient.factor hIJ (a : C ⧸ I)) =
      tBar s t J hJ (Ideal.Quotient.factor hIJ (a : C ⧸ I)) := by
  rw [sBar_factor, tBar_factor s t hIJ hI hJ, a.2]

/-! ### The ring core of Stacks 07SQ -/

section Core

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (K : ι → Ideal C)
  (hK : Monotone K) (hinv : ∀ i, (K i).map t = (K i).map s)
  (A : Type u) [CommRing A] [Algebra A (C ⧸ ⨆ i, K i)]
  [Module.FaithfullyFlat A (C ⧸ ⨆ i, K i)] [Algebra.Etale A (C ⧸ ⨆ i, K i)]
  (hst : (sBar s (⨆ i, K i)).comp (algebraMap A _) =
    (tBar s t _ (map_iSup_inv s t K hinv)).comp (algebraMap A _))
  (hbij : Function.Bijective (tensorLift (sBar s _) (tBar s t _ (map_iSup_inv s t K hinv)) hst))

/-- With `E` a `C`-algebra through `s`, `sBar s I` is the `algebraMap` of the quotients. -/
theorem sBar_eq_algebraMap (I : Ideal C) (x : C ⧸ I) :
    letI := s.toAlgebra
    sBar s I x = algebraMap (C ⧸ I) (E ⧸ I.map (algebraMap C E)) x := by
  let := s.toAlgebra
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
  rfl

include hK hbij in
/-- **The ring core of Stacks 07SQ, for a directed system of quotients.** Suppose that `E` is
finitely presented over `C` through `s`, and that `C∞ = C ⧸ ⨆ K i` is an étale, faithfully flat
`A`-algebra with `C∞ ⊗_A C∞ ≅ E∞`. Then for some `m ≤ k` there is an étale algebra `P` over the
equalizer `A_m` of `C ⧸ K m ⇉ E ⧸ (K m) E`, with surjective spectrum map, and a ring map
`ψ : P → C ⧸ K k` over `A_m`, such that `(C ⧸ K k) ⊗_{A_m} P → E ⧸ (K k) E`,
`c ⊗ p ↦ s̄ c · t̄ (ψ p)`, is bijective. This is the ring-theoretic content of display 084U being
cartesian at a stage. -/
theorem exists_stage_data (hfp : @Algebra.FinitePresentation C E _ _ s.toAlgebra) (i₀ : ι) :
    ∃ (m k : ι) (_ : i₀ ≤ m) (hmk : m ≤ k) (P : Type u) (_ : CommRing P)
      (_ : Algebra (eqStage s t (K m) (hinv m)) P)
      (α : eqStage s t (K m) (hinv m) →+* C ⧸ K k) (ψ : P →+* C ⧸ K k),
      Algebra.Etale (eqStage s t (K m) (hinv m)) P ∧
      Function.Surjective (PrimeSpectrum.comap (algebraMap (eqStage s t (K m) (hinv m)) P)) ∧
      (∀ a, α a = Ideal.Quotient.factor (hK hmk) (a : C ⧸ K m)) ∧
      ψ.comp (algebraMap (eqStage s t (K m) (hinv m)) P) = α ∧
      letI := α.toAlgebra
      ∃ h, Function.Bijective (tensorLift (A := eqStage s t (K m) (hinv m)) (sBar s (K k))
        ((tBar s t (K k) (hinv k)).comp ψ) h) := by
  classical
  obtain ⟨m, hi₀m, κ, _, _, q, het, hsurj, ⟨e⟩⟩ :=
    exists_stage_presentation s t K hK hinv A hst hbij i₀
  let θ : (MvPolynomial κ (eqStage s t (K m) (hinv m)) ⧸ Ideal.span (Set.range q)) →+*
      C ⧸ ⨆ i, K i :=
    e.toRingHom.comp (Ideal.quotientMap _ (MvPolynomial.map (colimMap s t K hinv A hst hbij m))
      (by
        rw [Ideal.span_le]
        rintro _ ⟨ν, rfl⟩
        exact Ideal.subset_span (Set.mem_range_self ν)))
  have hθ : ∀ a : eqStage s t (K m) (hinv m), θ (algebraMap (eqStage s t (K m) (hinv m)) _ a) =
      Ideal.Quotient.factor (le_iSup K m) (a : C ⧸ K m) := by
    intro a
    change e (Ideal.Quotient.mk _ (MvPolynomial.map _ (MvPolynomial.C a))) = _
    rw [MvPolynomial.map_C, ← algebraMap_colimMap s t K hinv A hst hbij m a]
    exact e.commutes _
  obtain ⟨k₀, hmk₀, h₀, hh₀, hcomp⟩ := exists_stage_lift s t K hK hinv q θ hθ
  -- the base ring `R = C ⧸ K k₀` and the target `Q = E ⧸ (K k₀) E`
  let : Algebra C E := s.toAlgebra
  let iGR : Algebra (eqStage s t (K m) (hinv m)) (C ⧸ K k₀) :=
    ((Ideal.Quotient.factor (hK hmk₀)).comp (eqStage s t (K m) (hinv m)).subtype).toAlgebra
  let iGQ : Algebra (eqStage s t (K m) (hinv m)) (E ⧸ (K k₀).map (algebraMap C E)) :=
    ((algebraMap (C ⧸ K k₀) (E ⧸ (K k₀).map (algebraMap C E))).comp
      (algebraMap (eqStage s t (K m) (hinv m)) (C ⧸ K k₀))).toAlgebra
  have : IsScalarTower (eqStage s t (K m) (hinv m)) (C ⧸ K k₀)
      (E ⧸ (K k₀).map (algebraMap C E)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hRQ : ∀ x : C ⧸ K k₀, algebraMap (C ⧸ K k₀) (E ⧸ (K k₀).map (algebraMap C E)) x =
      sBar s (K k₀) x := fun x => (sBar_eq_algebraMap s (K k₀) x).symm
  let g : (MvPolynomial κ (eqStage s t (K m) (hinv m)) ⧸ Ideal.span (Set.range q))
      →ₐ[eqStage s t (K m) (hinv m)] E ⧸ (K k₀).map (algebraMap C E) :=
    { (tBar s t (K k₀) (hinv k₀)).comp h₀ with
      commutes' := fun a => by
        change ((tBar s t (K k₀) (hinv k₀)).comp h₀) (algebraMap (eqStage s t (K m) (hinv m)) _ a) =
          algebraMap (C ⧸ K k₀) (E ⧸ (K k₀).map (algebraMap C E))
            (Ideal.Quotient.factor (hK hmk₀) (a : C ⧸ K m))
        rw [RingHom.comp_apply, hh₀ a, hRQ]
        exact (sBar_factor_eq_tBar_factor s t (hK hmk₀) (hinv m) (hinv k₀) a).symm }
  let φ := Algebra.TensorProduct.lift (Algebra.ofId (C ⧸ K k₀) (E ⧸ (K k₀).map (algebraMap C E)))
    g (fun _ _ => Commute.all _ _)
  have : Algebra.FinitePresentation (eqStage s t (K m) (hinv m))
      (MvPolynomial κ (eqStage s t (K m) (hinv m)) ⧸ Ideal.span (Set.range q)) :=
    (Algebra.Presentation.naive (v := q)).finitePresentation_of_isFinite
  have : Algebra.FinitePresentation (C ⧸ K k₀) (E ⧸ (K k₀).map (algebraMap C E)) :=
    Algebra.FinitePresentation.equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor E (K k₀)).symm
  -- the comparison of `φ` modulo an ideal with the stage map
  have key : ∀ (J' : Ideal C) (hJ : K k₀ ≤ J') (hJinv : J'.map t = J'.map s)
      (Jb : Ideal (C ⧸ K k₀)) (hJb : Jb = J'.map (Ideal.Quotient.mk (K k₀))),
      let : Algebra (eqStage s t (K m) (hinv m)) (C ⧸ J') :=
        ((Ideal.Quotient.factor hJ).comp
          (algebraMap (eqStage s t (K m) (hinv m)) (C ⧸ K k₀))).toAlgebra
      ∃ hc, (Function.Bijective (Ideal.quotientMap (Jb.map (algebraMap _ _)) φ.toRingHom
        (φ.map_algebraMap_le_comap Jb)) ↔
        Function.Bijective (tensorLift (A := eqStage s t (K m) (hinv m)) (sBar s J')
          ((tBar s t J' hJinv).comp ((Ideal.Quotient.factor hJ).comp h₀)) hc)) := by
    intro J' hJ hJinv Jb hJb
    let : Algebra (eqStage s t (K m) (hinv m)) (C ⧸ J') :=
      ((Ideal.Quotient.factor hJ).comp
        (algebraMap (eqStage s t (K m) (hinv m)) (C ⧸ K k₀))).toAlgebra
    have hc : (sBar s J').comp (algebraMap (eqStage s t (K m) (hinv m)) (C ⧸ J')) =
        ((tBar s t J' hJinv).comp ((Ideal.Quotient.factor hJ).comp h₀)).comp
          (algebraMap _ _) := by
      ext a
      change sBar s J' (Ideal.Quotient.factor hJ (Ideal.Quotient.factor (hK hmk₀) (a : C ⧸ K m))) =
        tBar s t J' hJinv (Ideal.Quotient.factor hJ (h₀ (algebraMap _ _ a)))
      rw [hh₀ a, Ideal.Quotient.factor_comp_apply]
      exact sBar_factor_eq_tBar_factor s t _ (hinv m) hJinv a
    refine ⟨hc, ?_⟩
    have hmapQ : Jb.map (algebraMap (C ⧸ K k₀) (E ⧸ (K k₀).map (algebraMap C E))) =
        (J'.map s).map (Ideal.Quotient.mk ((K k₀).map s)) := by
      rw [hJb, Ideal.map_map, Ideal.map_map]
      congr 1
    let e₁ : (C ⧸ K k₀) ⧸ Jb ≃+* C ⧸ J' :=
      (Ideal.quotEquivOfEq hJb).trans (DoubleQuot.quotQuotEquivQuotOfLE hJ)
    let e₂ : (E ⧸ (K k₀).map (algebraMap C E)) ⧸
        Jb.map (algebraMap (C ⧸ K k₀) (E ⧸ (K k₀).map (algebraMap C E))) ≃+* E ⧸ J'.map s :=
      (Ideal.quotEquivOfEq hmapQ).trans (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hJ))
    have he₁ : ∀ x : C ⧸ K k₀, e₁ (Ideal.Quotient.mk Jb x) = Ideal.Quotient.factor hJ x := by
      intro x
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have he₂ : ∀ x : E ⧸ (K k₀).map s,
        e₂ (Ideal.Quotient.mk _ x) = factorE s hJ x := by
      intro x
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    refine bijective_quotientMap_iff_bijective_tensorLift φ Jb e₁ (fun a => he₁ _) e₂ _ _ hc
      (fun r => ?_) (fun b => ?_)
    · rw [he₁, he₂, hRQ, sBar_factor]
    · rw [he₂]
      change tBar s t J' hJinv (Ideal.Quotient.factor hJ (h₀ b)) =
        factorE s hJ (φ (1 ⊗ₜ b))
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact tBar_factor s t hJ (hinv k₀) hJinv (h₀ b)
  -- the stages above `k₀`
  have : Nonempty {k : ι // k₀ ≤ k} := ⟨⟨k₀, le_rfl⟩⟩
  have : IsDirected {k : ι // k₀ ≤ k} (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  let I : {k : ι // k₀ ≤ k} → Ideal (C ⧸ K k₀) := fun k => (K k.1).map (Ideal.Quotient.mk (K k₀))
  have hI : Monotone I := fun a b hab => Ideal.map_mono (hK hab)
  have hsupK : (⨆ k : {k : ι // k₀ ≤ k}, K k.1) = ⨆ i, K i :=
    le_antisymm (iSup_le fun k => le_iSup K k.1) (iSup_le fun i => by
      obtain ⟨c, hic, hkc⟩ := directed_of (· ≤ ·) i k₀
      exact (hK hic).trans (le_iSup (fun k : {k : ι // k₀ ≤ k} => K k.1) ⟨c, hkc⟩))
  have hsupI : (⨆ k, I k) = (⨆ i, K i).map (Ideal.Quotient.mk (K k₀)) := by
    rw [← hsupK, Ideal.map_iSup]
  -- bijectivity modulo the union, from the effective quotient over `A`
  obtain ⟨hcInf, hiffInf⟩ :=
    key (⨆ i, K i) (le_iSup K k₀) (map_iSup_inv s t K hinv) (⨆ k, I k) hsupI
  have hbijInf : Function.Bijective (Ideal.quotientMap ((⨆ k, I k).map (algebraMap _ _))
      φ.toRingHom (φ.map_algebraMap_le_comap _)) := by
    refine hiffInf.2 ?_
    let : Algebra (eqStage s t (K m) (hinv m)) (C ⧸ ⨆ i, K i) :=
      ((Ideal.Quotient.factor (le_iSup K k₀)).comp
        (algebraMap (eqStage s t (K m) (hinv m)) (C ⧸ K k₀))).toAlgebra
    let : Algebra (eqStage s t (K m) (hinv m)) A := (colimMap s t K hinv A hst hbij m).toAlgebra
    have : IsScalarTower (eqStage s t (K m) (hinv m)) A (C ⧸ ⨆ i, K i) :=
      IsScalarTower.of_algebraMap_eq fun a => by
        change Ideal.Quotient.factor (le_iSup K k₀)
            (Ideal.Quotient.factor (hK hmk₀) (a : C ⧸ K m)) =
          algebraMap A _ (colimMap s t K hinv A hst hbij m a)
        rw [algebraMap_colimMap, Ideal.Quotient.factor_comp_apply]
    let θ' : (MvPolynomial κ (eqStage s t (K m) (hinv m)) ⧸ Ideal.span (Set.range q))
        →ₐ[eqStage s t (K m) (hinv m)] C ⧸ ⨆ i, K i :=
      { (Ideal.Quotient.factor (le_iSup K k₀)).comp h₀ with
        commutes' := fun a => by
          change Ideal.Quotient.factor (le_iSup K k₀) (h₀ (algebraMap _ _ a)) = _
          rw [hh₀ a]
          rfl }
    have hθ' : ∀ x, θ' x = θ x := fun x => congrArg (fun f => f x) hcomp
    let ε := (Algebra.tensorQuotientSpanEquiv (eqStage s t (K m) (hinv m)) A q).trans e
    have hε : ∀ x, ε ((1 : A) ⊗ₜ x) = θ x := by
      have hr : (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) = θ := by
        apply Ideal.Quotient.ringHom_ext
        apply MvPolynomial.ringHom_ext
        · intro a
          change ε ((1 : A) ⊗ₜ algebraMap (eqStage s t (K m) (hinv m)) _ a) =
            e (Ideal.Quotient.mk _ (MvPolynomial.map _ (MvPolynomial.C a)))
          rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul, MvPolynomial.map_C]
          exact (ε.commutes (algebraMap _ A a)).trans (e.commutes _).symm
        · intro ν
          change e (Algebra.tensorQuotientSpanEquiv _ A q ((1 : A) ⊗ₜ
            Ideal.Quotient.mk _ (MvPolynomial.X ν))) =
            e (Ideal.Quotient.mk _ (MvPolynomial.map _ (MvPolynomial.X ν)))
          congr 1
          rw [MvPolynomial.map_X]
          change _ = (Ideal.Quotient.mk (Ideal.span (Set.range fun k =>
            MvPolynomial.map (algebraMap (eqStage s t (K m) (hinv m)) A) (q k)))) (MvPolynomial.X ν)
          rw [← AlgEquiv.apply_symm_apply
            (Algebra.tensorQuotientSpanEquiv _ A q) (Ideal.Quotient.mk _ (MvPolynomial.X ν)),
            Algebra.tensorQuotientSpanEquiv_symm_mk, MvPolynomial.aeval_X]
      exact fun x => congrArg (fun f => f x) hr
    have hΞ : Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId A (C ⧸ ⨆ i, K i)) θ'
        (fun _ _ => Commute.all _ _)) := by
      have : ⇑(Algebra.TensorProduct.lift (Algebra.ofId A (C ⧸ ⨆ i, K i)) θ'
          (fun _ _ => Commute.all _ _)) = ε := by
        funext x
        induction x with
        | add x y hx hy => rw [map_add, map_add, hx, hy]
        | tmul a x =>
          rw [Algebra.TensorProduct.lift_tmul, hθ', ← hε, Algebra.ofId_apply,
            ← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact ε.bijective
    exact bijective_tensorLift_comp (A' := eqStage s t (K m) (hinv m)) (A := A)
      (sBar s _) (tBar s t _ (map_iSup_inv s t K hinv)) hst θ' hΞ hbij
  obtain ⟨k, hk⟩ := Algebra.FinitePresentation.exists_bijective_quotientMap_of_bijective_iSup
    φ I hI hbijInf
  obtain ⟨hck, hiffk⟩ := key (K k.1) (hK k.2) (hinv k.1) (I k) rfl
  refine ⟨m, k.1, hi₀m, hmk₀.trans k.2, _, inferInstance, inferInstance,
    (Ideal.Quotient.factor (hK k.2)).comp (algebraMap (eqStage s t (K m) (hinv m)) (C ⧸ K k₀)),
    (Ideal.Quotient.factor (hK k.2)).comp h₀, het, hsurj, fun a => ?_, ?_, hck, hiffk.1 hk⟩
  · change Ideal.Quotient.factor (hK k.2) (Ideal.Quotient.factor (hK hmk₀) (a : C ⧸ K m)) = _
    exact Ideal.Quotient.factor_comp_apply _ _ _
  · ext a
    simp only [RingHom.comp_apply, hh₀]
    rfl

end Core

/-! ### Transport along isomorphisms -/

/-- Bijectivity of `D ⊗_A P → F` transports along compatible ring isomorphisms `D' ≅ D` and
`F' ≅ F`. -/
theorem bijective_tensorLift_of_ringEquiv {A D D' F F' P : Type u} [CommRing A] [CommRing D]
    [CommRing D'] [CommRing F] [CommRing F'] [CommRing P] [Algebra A D] [Algebra A D']
    [Algebra A P] (eD : D' ≃+* D) (heD : ∀ a, eD (algebraMap A D' a) = algebraMap A D a)
    (eF : F' ≃+* F) (σ : D →+* F) (τ : P →+* F) (σ' : D' →+* F') (τ' : P →+* F')
    (hσ : ∀ x, eF (σ' x) = σ (eD x)) (hτ : ∀ p, eF (τ' p) = τ p)
    (h : σ.comp (algebraMap A D) = τ.comp (algebraMap A P))
    (h' : σ'.comp (algebraMap A D') = τ'.comp (algebraMap A P))
    (hb : Function.Bijective (tensorLift σ τ h)) : Function.Bijective (tensorLift σ' τ' h') := by
  let eD' : D' ≃ₐ[A] D := { eD with commutes' := heD }
  let ε : D' ⊗[A] P ≃+* D ⊗[A] P :=
    (Algebra.TensorProduct.congr eD' (AlgEquiv.refl : P ≃ₐ[A] P)).toRingEquiv
  have key :
      tensorLift σ' τ' h' = (eF.symm.toRingHom.comp (tensorLift σ τ h)).comp ε.toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext x
      apply eF.injective
      simp [ε, eD', hσ]
    · ext p
      apply eF.injective
      have h1 : eD 1 = 1 := map_one eD
      simp [ε, eD', hτ, h1]
  rw [key]
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (eF.symm.bijective.comp hb).comp ε.bijective

/-- `Stacks.AffineStageCore.exists_stage_data` with the colimit ideal given as any ideal equal to
`⨆ i, K i`. -/
theorem exists_stage_data_of_eq {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (K : ι → Ideal C) (hK : Monotone K) (hinv : ∀ i, (K i).map t = (K i).map s)
    (Kinf : Ideal C) (hKinf : Kinf = ⨆ i, K i) (hinvInf : Kinf.map t = Kinf.map s)
    (A : Type u) [CommRing A] [Algebra A (C ⧸ Kinf)]
    [Module.FaithfullyFlat A (C ⧸ Kinf)] [Algebra.Etale A (C ⧸ Kinf)]
    (hst : (sBar s Kinf).comp (algebraMap A _) = (tBar s t Kinf hinvInf).comp (algebraMap A _))
    (hbij : Function.Bijective (tensorLift (sBar s Kinf) (tBar s t Kinf hinvInf) hst))
    (hfp : @Algebra.FinitePresentation C E _ _ s.toAlgebra) (i₀ : ι) :
    ∃ (m k : ι) (_ : i₀ ≤ m) (hmk : m ≤ k) (P : Type u) (_ : CommRing P)
      (_ : Algebra (eqStage s t (K m) (hinv m)) P)
      (α : eqStage s t (K m) (hinv m) →+* C ⧸ K k) (ψ : P →+* C ⧸ K k),
      Algebra.Etale (eqStage s t (K m) (hinv m)) P ∧
      Function.Surjective (PrimeSpectrum.comap (algebraMap (eqStage s t (K m) (hinv m)) P)) ∧
      (∀ a, α a = Ideal.Quotient.factor (hK hmk) (a : C ⧸ K m)) ∧
      ψ.comp (algebraMap (eqStage s t (K m) (hinv m)) P) = α ∧
      letI := α.toAlgebra
      ∃ h, Function.Bijective (tensorLift (A := eqStage s t (K m) (hinv m)) (sBar s (K k))
        ((tBar s t (K k) (hinv k)).comp ψ) h) := by
  subst hKinf
  exact exists_stage_data s t K hK hinv A hst hbij hfp i₀

end Stacks.AffineStageCore

end
