module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Triangulated
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Homology.HomotopyCofiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of a bounded complex of finite locally free modules

The alternating sum `Σᵢ (-1)ⁱ [ℰⁱ]` of the classes of the terms of a cochain complex of
`𝒪_X`-modules, as an element of the Grothendieck group `K₀(Vect(X))` of finite locally free
modules on a scheme `X`. On bounded complexes of finite locally free modules it is additive on
mapping cones and vanishes on acyclic complexes whose modules of cycles are finite locally free.

## Main definitions

* `Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex`: the alternating sum
  `Σᵢ (-1)ⁱ [ℰⁱ]` in `K₀(Vect(X))`.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_eq_sum`: on a complex strictly
  supported in the degrees `a ≤ i ≤ b` the Euler characteristic is the finite sum over
  `Finset.Icc a b`.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_mappingCone`: the Euler
  characteristic of the mapping cone of `f : 𝒦 ⟶ ℒ` is `-χ(𝒦) + χ(ℒ)`.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_eq_zero_of_acyclic`: a bounded
  acyclic complex of finite locally free modules whose modules of cycles are finite locally
  free has Euler characteristic zero.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_eq_of_quasiIso`:
  quasi-isomorphic bounded complexes of finite locally free modules have the same Euler
  characteristic, provided bounded acyclic such complexes have finite locally free cycles.

## References

* [Stacks Project, Tag 0FDJ](https://stacks.math.columbia.edu/tag/0FDJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.FiniteLocallyFree StrictlyPerfect
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

variable (X : Scheme.{u})

/-! ### Classes of modules, unconditionally -/

/-- Isomorphic `𝒪_X`-modules have the same class in `K₀(Vect(X))`; no finite local freeness is
assumed. -/
theorem classOf_eq_of_iso' {M N : X.Modules} (e : M ≅ N) :
    VectorBundleKZero.classOf X M = VectorBundleKZero.classOf X N := by
  by_cases hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M
  · exact VectorBundleKZero.classOf_eq_of_iso e hM
  · rw [VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M hM,
      VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree N
        (fun hN => hM (@IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _ e.symm hN))]

/-- The class of a zero `𝒪_X`-module in `K₀(Vect(X))` is zero. -/
theorem classOf_eq_zero_of_isZero {M : X.Modules} (hM : IsZero M) :
    VectorBundleKZero.classOf X M = 0 :=
  (classOf_eq_of_iso' X (hM.iso (isZero_zero _))).trans (VectorBundleKZero.classOf_zero X)

/-! ### Mapping cones -/

/-- The mapping cone of a morphism of bounded complexes of finite locally free modules is a
bounded complex of finite locally free modules. -/
theorem mappingCone_mem {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (hK : boundedFiniteLocallyFreeComplex X K) (hL : boundedFiniteLocallyFreeComplex X L) :
    boundedFiniteLocallyFreeComplex X (CochainComplex.mappingCone f) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := (CochainComplex.plus_iff X.Modules K).mp hK.1.1
    obtain ⟨b, hb⟩ := (CochainComplex.plus_iff X.Modules L).mp hL.1.1
    apply (CochainComplex.plus_iff X.Modules _).mpr
    refine ⟨min (a - 1) b, ?_⟩
    exact CochainComplex.isStrictlyGE_mappingCone f a b _
  · obtain ⟨a, ha⟩ := (CochainComplex.minus_iff K).mp hK.1.2
    obtain ⟨b, hb⟩ := (CochainComplex.minus_iff L).mp hL.1.2
    apply (CochainComplex.minus_iff _).mpr
    refine ⟨max a b, ?_⟩
    exact CochainComplex.isStrictlyLE_mappingCone f a b _
  · intro i
    let Y : RingedSpace.{u, u} := X.toRingedSpace
    let M : OXMod.{u} Y := K.X (i + 1)
    let N : OXMod.{u} Y := L.X i
    have : IsFiniteLocallyFree (R := structureSheafOfRings Y) M := hK.2 (i + 1)
    have : IsFiniteLocallyFree (R := structureSheafOfRings Y) N := hL.2 i
    let : HasBinaryBiproduct (K.X (i + 1)) (L.X i) := inferInstanceAs (HasBinaryBiproduct M N)
    exact IsFiniteLocallyFree.of_iso (h := finiteLocallyFree_biprod (Y := Y) M N)
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)).symm

/-- The class of the degree `i` term of the mapping cone of `f : K ⟶ L` is
`[K^{i+1}] + [L^i]`. -/
theorem classOf_mappingCone_X {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (hK : boundedFiniteLocallyFreeComplex X K) (hL : boundedFiniteLocallyFreeComplex X L)
    (i : ℤ) :
    VectorBundleKZero.classOf X ((CochainComplex.mappingCone f).X i) =
      VectorBundleKZero.classOf X (K.X (i + 1)) + VectorBundleKZero.classOf X (L.X i) := by
  have hcone := (mappingCone_mem X f hK hL).2 i
  let Y : RingedSpace.{u, u} := X.toRingedSpace
  let M : OXMod.{u} Y := K.X (i + 1)
  let N : OXMod.{u} Y := L.X i
  let e : (CochainComplex.mappingCone f).X i ≅ M ⊞ N :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)
  let ι : M ⟶ M ⊞ N := biprod.inl
  let π : M ⊞ N ⟶ N := biprod.snd
  have hw : ι ≫ π = 0 := biprod.inl_snd
  have hmono : Mono ι := inferInstanceAs (Mono (biprod.inl : M ⟶ M ⊞ N))
  have hepi : Epi π := inferInstanceAs (Epi (biprod.snd : M ⊞ N ⟶ N))
  exact (VectorBundleKZero.classOf_eq_of_iso e hcone).trans
    (@VectorBundleKZero.classOf_shortExact X M _ N ι π hmono hepi hw (hK.2 (i + 1))
      (@IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _ e hcone) (hL.2 i)
      (ShortComplex.Splitting.ofHasBinaryBiproduct M N).exact)

/-! ### The Euler characteristic -/

/-- The **Euler characteristic in `K₀(Vect(X))`** of a cochain complex of `𝒪_X`-modules: the
alternating sum `Σᵢ (-1)ⁱ [ℰⁱ]` of the classes of its terms. The sum is taken as a `finsum`, so
no boundedness hypothesis enters the definition; for a bounded complex it is the finite sum over
any interval containing the degrees where the complex is nonzero. -/
@[sga "6 0 3.1" "partial"]
def eulerCharComplex (E : CochainComplex X.Modules ℤ) : VectorBundleKZero X :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (E.X i)

/-- On a complex strictly supported in the degrees `a ≤ i ≤ b`, the summands of the Euler
characteristic vanish outside `Finset.Icc a b`. -/
theorem eulerCharComplex_support_subset (E : CochainComplex X.Modules ℤ) (a b : ℤ)
    (hge : E.IsStrictlyGE a) (hle : E.IsStrictlyLE b) :
    (Function.support fun i : ℤ => (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (E.X i)) ⊆
      (Finset.Icc a b : Set ℤ) := by
  intro i hi
  by_contra hnot
  have hout : i < a ∨ b < i := by
    simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hnot
  have hz : IsZero (E.X i) :=
    hout.elim (fun h => E.isZero_of_isStrictlyGE a i h) fun h => E.isZero_of_isStrictlyLE b i h
  refine hi ?_
  simp only [classOf_eq_zero_of_isZero X hz, smul_zero]

/-- On a complex strictly supported in the degrees `a ≤ i ≤ b`, the Euler characteristic is the
finite sum over `Finset.Icc a b`. -/
theorem eulerCharComplex_eq_sum (E : CochainComplex X.Modules ℤ) (a b : ℤ)
    (hge : E.IsStrictlyGE a) (hle : E.IsStrictlyLE b) :
    eulerCharComplex X E =
      ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (E.X i) :=
  finsum_eq_sum_of_support_subset _ (eulerCharComplex_support_subset X E a b hge hle)

/-- Isomorphic complexes have the same Euler characteristic. -/
theorem eulerCharComplex_eq_of_iso {E F : CochainComplex X.Modules ℤ} (e : E ≅ F) :
    eulerCharComplex X E = eulerCharComplex X F :=
  finsum_congr fun i => congrArg _ (classOf_eq_of_iso' X
    ((HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) i).mapIso e))

/-- The summands of the Euler characteristic of a bounded complex of finite locally free
modules have finite support. -/
theorem eulerCharComplex_support_finite (E : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) :
    (Function.support fun i : ℤ =>
      (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (E.X i)).Finite := by
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff X.Modules E).mp hE.1.1
  obtain ⟨b, hb⟩ := (CochainComplex.minus_iff E).mp hE.1.2
  exact (Finset.finite_toSet (Finset.Icc a b)).subset
    (eulerCharComplex_support_subset X E a b ha hb)

/-- `(-1)^(i+1) • x = -((-1)^i • x)` in an additive commutative group. -/
theorem negOnePow_succ_smul {A : Type*} [AddCommGroup A] (i : ℤ) (x : A) :
    ((i + 1).negOnePow : ℤ) • x = -((i.negOnePow : ℤ) • x) := by
  rw [Int.negOnePow_succ, Units.val_neg, neg_smul]

/-- **The Euler characteristic of a mapping cone.** For a morphism `f : K ⟶ L` of bounded
complexes of finite locally free modules, `χ(cone f) = -χ(K) + χ(L)`. -/
theorem eulerCharComplex_mappingCone {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (hK : boundedFiniteLocallyFreeComplex X K) (hL : boundedFiniteLocallyFreeComplex X L) :
    eulerCharComplex X (CochainComplex.mappingCone f) =
      -eulerCharComplex X K + eulerCharComplex X L := by
  let x : ℤ → VectorBundleKZero X := fun i =>
    (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (K.X i)
  let y : ℤ → VectorBundleKZero X := fun i =>
    (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (L.X i)
  have hxshift : (Function.support fun i : ℤ => -x (i + 1)).Finite :=
    ((eulerCharComplex_support_finite X K hK).preimage (f := fun i : ℤ => i + 1)
      (Set.injOn_of_injective (add_left_injective 1))).subset fun i hi => by simpa [x] using hi
  have hcone : eulerCharComplex X (CochainComplex.mappingCone f) =
      ∑ᶠ i : ℤ, (-x (i + 1) + y i) :=
    finsum_congr fun i => by
      simp only [classOf_mappingCone_X X f hK hL, smul_add, x, y, negOnePow_succ_smul, neg_neg]
  rw [hcone, finsum_add_distrib hxshift (eulerCharComplex_support_finite X L hL),
    show (∑ᶠ i : ℤ, -x (i + 1)) = ∑ᶠ i : ℤ, -x i from
      finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun i : ℤ => -x i),
    finsum_neg_distrib]
  rfl

/-! ### Acyclic complexes -/

private theorem epi_toCycles_of_acyclic (E : CochainComplex X.Modules ℤ)
    (hE : E.Acyclic) (n m : ℤ) (h : n + 1 = m) : Epi (E.toCycles n m) := by
  subst h
  have e : (ComplexShape.up ℤ).prev (n + 1) = n := by simp
  have h' : Epi (E.toCycles ((ComplexShape.up ℤ).prev (n + 1)) (n + 1)) := (hE (n + 1)).epi_toCycles
  rwa [e] at h'

private theorem cycles_shortExact_of_acyclic (E : CochainComplex X.Modules ℤ)
    (hE : E.Acyclic) (n : ℤ) :
    (ShortComplex.mk (E.iCycles n) (E.toCycles n (n + 1))
      (by simp [← cancel_mono (E.iCycles (n + 1))])).ShortExact := by
  have := epi_toCycles_of_acyclic X E hE n (n + 1) rfl
  refine { exact := ?_ }
  let S := ShortComplex.mk (E.iCycles n) (E.d n (n + 1)) (E.iCycles_d _ _)
  let φ : ShortComplex.mk (E.iCycles n) (E.toCycles n (n + 1))
      (by simp [← cancel_mono (E.iCycles (n + 1))]) ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := E.iCycles (n + 1)
      comm₂₃ := by simp [S] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (ShortComplex.exact_of_f_is_kernel S (E.cyclesIsKernel n (n + 1) (by simp)))

/-- In a bounded acyclic complex with finite locally free terms and cycles, the class of a term
is the sum of the classes of the two neighbouring modules of cycles. -/
theorem classOf_term_eq_classOf_cycles (E : CochainComplex X.Modules ℤ)
    (hterms : ∀ i : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (E.X i))
    (hcyc : ∀ i : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (E.cycles i))
    (hE : E.Acyclic) (i : ℤ) :
    VectorBundleKZero.classOf X (E.X i) =
      VectorBundleKZero.classOf X (E.cycles i) +
        VectorBundleKZero.classOf X (E.cycles (i + 1)) := by
  have hS := cycles_shortExact_of_acyclic X E hE i
  have := hS.mono_f
  have := hS.epi_g
  exact VectorBundleKZero.classOf_shortExact (E.iCycles i) (E.toCycles i (i + 1))
    (by simp [← cancel_mono (E.iCycles (i + 1))]) (hcyc i) (hterms i) (hcyc (i + 1)) hS.exact

private theorem sum_Icc_eq_zero_of_telescope {A : Type*} [AddCommGroup A]
    (F g : ℤ → A) (a b : ℤ) (hab : a ≤ b + 1)
    (h : ∀ i : ℤ, F i = g (i + 1) - g i) (ha : g a = 0) (hb : g (b + 1) = 0) :
    ∑ i ∈ Finset.Icc a b, F i = 0 := by
  suffices hsum : ∀ c : ℤ, a - 1 ≤ c →
      ∑ i ∈ Finset.Icc a c, F i = g (c + 1) - g a by
    rw [hsum b (by omega), ha, hb, sub_zero]
  intro c hc
  induction c, hc using Int.leInduction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty,
      show a - 1 + 1 = a from by omega, sub_self]
  | succ c hc ih =>
    have hins : Finset.Icc a (c + 1) = insert (c + 1) (Finset.Icc a c) := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih, h (c + 1)]
    abel

/-- **A bounded acyclic complex of finite locally free modules whose modules of cycles are finite
locally free has Euler characteristic zero.** -/
theorem eulerCharComplex_eq_zero_of_acyclic (E : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E)
    (hcyc : ∀ i : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (E.cycles i))
    (hac : E.Acyclic) : eulerCharComplex X E = 0 := by
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff X.Modules E).mp hE.1.1
  obtain ⟨b, hb⟩ := (CochainComplex.minus_iff E).mp hE.1.2
  rw [eulerCharComplex_eq_sum X E a b ha hb]
  by_cases hab : a ≤ b
  · have hlo : IsZero (E.cycles a) := by
      have hsrc : IsZero (E.X (a - 1)) := E.isZero_of_isStrictlyGE a (a - 1) (by omega)
      have hepi := epi_toCycles_of_acyclic X E hac (a - 1) a (by omega)
      exact IsZero.of_epi (E.toCycles (a - 1) a) hsrc
    have hhi : IsZero (E.cycles (b + 1)) := by
      have hterm : IsZero (E.X (b + 1)) := E.isZero_of_isStrictlyLE b (b + 1) (by omega)
      exact IsZero.of_mono (E.iCycles (b + 1)) hterm
    let z : ℤ → VectorBundleKZero X := fun i => VectorBundleKZero.classOf X (E.cycles i)
    let g : ℤ → VectorBundleKZero X := fun i => ((i - 1).negOnePow : ℤ) • z i
    have hsign (i : ℤ) : ((i - 1).negOnePow : ℤ) = -((i.negOnePow : ℤ)) := by
      have : ((i - 1) + 1).negOnePow = -(i - 1).negOnePow := Int.negOnePow_succ (i - 1)
      rw [show (i - 1) + 1 = i from by omega] at this
      rw [this, Units.val_neg, neg_neg]
    have hstep (i : ℤ) :
        (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (E.X i) = g (i + 1) - g i := by
      rw [classOf_term_eq_classOf_cycles X E hE.2 hcyc hac i, smul_add]
      show (i.negOnePow : ℤ) • z i + (i.negOnePow : ℤ) • z (i + 1) =
        (((i + 1) - 1).negOnePow : ℤ) • z (i + 1) - ((i - 1).negOnePow : ℤ) • z i
      rw [show (i + 1) - 1 = i from by omega, hsign i, neg_smul, sub_neg_eq_add]
      abel
    refine sum_Icc_eq_zero_of_telescope _ g a b (by omega) hstep ?_ ?_
    · show ((a - 1).negOnePow : ℤ) • VectorBundleKZero.classOf X (E.cycles a) = 0
      rw [classOf_eq_zero_of_isZero X hlo, smul_zero]
    · show (((b + 1) - 1).negOnePow : ℤ) •
        VectorBundleKZero.classOf X (E.cycles (b + 1)) = 0
      rw [classOf_eq_zero_of_isZero X hhi, smul_zero]
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-! ### Quasi-isomorphisms -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Quasi-isomorphic bounded complexes of finite locally free modules have the same Euler
characteristic**, provided every bounded acyclic complex of finite locally free modules has finite
locally free modules of cycles. -/
theorem eulerCharComplex_eq_of_quasiIso {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    [QuasiIso f] (hK : boundedFiniteLocallyFreeComplex X K)
    (hL : boundedFiniteLocallyFreeComplex X L)
    (hcyc : ∀ C : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X C →
      C.Acyclic → ∀ i : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (C.cycles i)) :
    eulerCharComplex X K = eulerCharComplex X L := by
  have hT := DerivedCategory.mappingCone_triangle_distinguished f
  have hz : IsZero (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) :=
    Triangle.isZero₃_of_isIso₁ _ hT (by change IsIso (DerivedCategory.Q.map f); infer_instance)
  have hac : (CochainComplex.mappingCone f).Acyclic := by
    intro i
    exact ((CochainComplex.mappingCone f).exactAt_iff_isZero_homology i).mpr
      (((DerivedCategory.homologyFunctorFactors X.Modules i).app _).isZero_iff.mp
        ((DerivedCategory.homologyFunctor X.Modules i).map_isZero hz))
  have hcone := mappingCone_mem X f hK hL
  have h := eulerCharComplex_eq_zero_of_acyclic X _ hcone (hcyc _ hcone hac) hac
  rw [eulerCharComplex_mappingCone X f hK hL] at h
  exact neg_add_eq_zero.mp h

end Derived

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
