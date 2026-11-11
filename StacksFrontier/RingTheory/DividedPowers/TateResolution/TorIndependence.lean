module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DividedPowerDGALift
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TorDividedPowerAlgebra

/-!
# The divided power algebra `Tor_*^R(S, T)` does not depend on the Tate resolution

Let `R` be a commutative ring and let `S` and `T` be commutative `R`-algebras. Tag 09PQ puts a
strictly graded-commutative `R`-algebra structure with divided powers on `⨁ n, Tor_n^R(S, T)`,
computed from a Tate resolution `A` of `S` as the homology of `T ⊗[R] A`, and asserts that the
structure does not depend on the choice of `A`. The structure itself is transported from one
choice of `A` in `StacksFrontier.RingTheory.DividedPowers.TateResolution.TorDividedPowerAlgebra`.
This file proves that the class map of *every* Tate resolution is a map of divided power
algebras onto it, which is the independence.

Following the proof of Tag 09PQ, given two Tate resolutions `A'` and `A` of `S`, Tag 09PP
(`exists_dividedPowerDGAMap_lift`) supplies a map `A' → A` of divided power differential graded
algebras over `S`. Its base change `T ⊗[R] A' → T ⊗[R] A` preserves gradings, differentials,
products and divided powers, and it commutes with the identifications of the two homologies with
`⨁ n, Tor_n^R(S, T)`: the identification is the composite of the comparison of the complexes of
homogeneous pieces (natural in the map) with the computation of `Tor` by a projective resolution
(natural by `ProjectiveResolution.isoLeftDerivedObj_hom_naturality`, the map of resolutions lying
over the identity of `S`).

## Main definitions

* `DividedPowers.TateResolution.Resolution.zerothHomologyAugmentation` — the augmentation on the
  zeroth homology algebra of a Tate resolution.
* `DividedPowers.TateResolution.lTensorAlgHom` — the base change `T ⊗[R] A' → T ⊗[R] A` of a map
  of algebras.
* `DividedPowers.TateResolution.Resolution.complexMap` — a map of Tate resolutions as a map of
  their underlying chain complexes.
* `DividedPowers.TateResolution.gradedChainComplexMap` — a map of differential graded algebras as
  a map of their complexes of homogeneous pieces.

## Main results

* `DividedPowers.TateResolution.Resolution.bijective_zerothHomologyAugmentation` — the
  augmentation identifies the zeroth homology algebra of a Tate resolution with `S`.
* `DividedPowers.TateResolution.Resolution.exists_resolutionMap` — Tag 09PP applied to two Tate
  resolutions of `S`.
* `DividedPowers.TateResolution.lTensorAlgHom_dpow` — the base change of a divided power map
  preserves the base-changed divided powers.
* `DividedPowers.TateResolution.Resolution.torIsoHomology_hom_comp_homologyMap` — the
  computation of `Tor` by a Tate resolution is natural in the resolution.
* `DividedPowers.TateResolution.Resolution.directSumClass_lTensorAlgHom` — the class maps of two
  Tate resolutions agree through a map of resolutions.
* `DividedPowers.TateResolution.exists_dividedPowerStructure_torDirectSum_forall_resolution` —
  Tag 09PQ: the divided power algebra structure on `⨁ n, Tor_n^R(S, T)`, together with its
  independence of the Tate resolution.

## References

* [Stacks Project, Tag 09PQ](https://stacks.math.columbia.edu/tag/09PQ)
* [Stacks Project, Tag 09PP](https://stacks.math.columbia.edu/tag/09PP)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

open TensorProduct

universe u v w

section DegreeZeroComponent

variable {R : Type u} {A : Type v} {C : Type w} [CommRing R] [Ring A] [Algebra R A]
  [Semiring C] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- A ring map killing every positive-degree homogeneous element depends on the degree-zero
component. -/
public theorem ringHom_eq_decompose_zero (f : A →+* C)
    (hf : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → f a = 0) (x : A) :
    f x = f (DirectSum.decompose 𝒜 x 0 : A) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 x]
  rw [map_sum, Finset.sum_eq_single 0]
  · intro b _ hb
    exact hf b _ (Nat.pos_of_ne_zero hb) (SetLike.coe_mem _)
  · intro h0
    rw [DFinsupp.notMem_support_iff.1 h0]
    simp

end DegreeZeroComponent

section ZerothHomology

attribute [local instance] Resolution.ring Resolution.algebra Resolution.graded
  Resolution.strict Resolution.dga Resolution.compatible

variable {R S σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {φ : MvPolynomial σ R →ₐ[R] S} (Res : Resolution R S σ φ)

/-- The augmentation of a Tate resolution kills the congruence cutting out the zeroth
homology. -/
public theorem Resolution.zerothHomologyCongruence_le_ker :
    zerothHomologyCongruence Res.grade Res.differential ≤
      RingCon.ker Res.augmentation.toRingHom := by
  rw [zerothHomologyCongruence, RingCon.ringConGen_le]
  rintro x y ⟨rfl, (⟨n, hn, hx⟩ | ⟨z, -, rfl⟩)⟩
  · rw [RingCon.ker_apply]
    simpa using Res.augmentation_positive n x hn hx
  · rw [RingCon.ker_apply]
    simpa using Res.augmentation_differential z

/-- The augmentation of a Tate resolution, on its zeroth homology algebra. -/
public def Resolution.zerothHomologyAugmentation :
    zerothHomology Res.grade Res.differential →ₐ[R] S :=
  RingCon.liftₐ _ Res.augmentation Res.zerothHomologyCongruence_le_ker

/-- The augmentation on zeroth homology is the augmentation on representatives. -/
@[simp]
public theorem Resolution.zerothHomologyAugmentation_mk' (a : Res.A) :
    Res.zerothHomologyAugmentation
        ((zerothHomologyCongruence Res.grade Res.differential).mk' a) =
      Res.augmentation a :=
  rfl

/-- **The augmentation identifies the zeroth homology algebra with `S`.** It is onto because the
augmentation is, and one to one because an element killed by the augmentation has degree-zero
component killed by it, which is a boundary by `exact_zero`. -/
public theorem Resolution.bijective_zerothHomologyAugmentation :
    Function.Bijective Res.zerothHomologyAugmentation := by
  set c := zerothHomologyCongruence Res.grade Res.differential
  refine ⟨?_, ?_⟩
  · have hzero : ∀ x : Res.A, Res.augmentation x = 0 → c.mk' x = 0 := by
      intro x hx
      have hpos : ∀ (n : ℕ) (a : Res.A), 0 < n → a ∈ Res.grade n → c.mk' a = 0 := by
        intro n a hn ha
        apply (RingCon.eq c).2
        apply RingCon.le_ringConGen
        exact ⟨rfl, Or.inl ⟨n, hn, ha⟩⟩
      have hx₀ : Res.augmentation (DirectSum.decompose Res.grade x 0 : Res.A) = 0 := by
        rw [← hx]
        exact (ringHom_eq_decompose_zero Res.grade Res.augmentation.toRingHom
          (fun n a hn ha => Res.augmentation_positive n a hn ha) x).symm
      obtain ⟨b, hb, hdb⟩ := Res.exact_zero _ (SetLike.coe_mem _) hx₀
      rw [ringHom_eq_decompose_zero Res.grade c.mk' hpos x]
      apply (RingCon.eq c).2
      apply RingCon.le_ringConGen
      exact ⟨rfl, Or.inr ⟨b, hb, hdb⟩⟩
    intro p q hpq
    obtain ⟨a, rfl⟩ := c.mk'_surjective p
    obtain ⟨b, rfl⟩ := c.mk'_surjective q
    have hab : Res.augmentation (a - b) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hpq
    have h := hzero (a - b) hab
    rw [map_sub, sub_eq_zero] at h
    exact h
  · intro s
    obtain ⟨a, rfl⟩ := Res.augmentation_surjective s
    exact ⟨c.mk' a, rfl⟩

/-- The positive-degree homology of a Tate resolution vanishes, in the form Tag 09PP asks. -/
public theorem Resolution.exists_boundary_of_positive (n : ℕ) (b : Res.A) (hn : 0 < n)
    (hb : b ∈ Res.grade n) (hdb : Res.differential b = 0) :
    ∃ c : Res.A, c ∈ Res.grade (n + 1) ∧ Res.differential c = b :=
  Res.exact_positive n b hn hb hdb

variable {σ' : Type u} {φ' : MvPolynomial σ' R →ₐ[R] S}

/-- **Comparison of two Tate resolutions (Tag 09PP).** Given two Tate resolutions of `S`, there
is a map of divided power differential graded `R`-algebras from the first to the second,
preserving the gradings, the differentials and the divided powers, and compatible with the two
augmentations to `S`. -/
public theorem Resolution.exists_resolutionMap (Res' : Resolution R S σ' φ') :
    ∃ g : Res'.A →ₐ[R] Res.A,
      (∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n) ∧
      (∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a)) ∧
      (∀ (n : ℕ) (a : Res'.A), a ∈ positiveEvenPart Res'.grade →
        g (Res'.gamma.dpow n a) = Res.gamma.dpow n (g a)) ∧
      (∀ a : Res'.A, Res.augmentation (g a) = Res'.augmentation a) := by
  let e := AlgEquiv.ofBijective Res.zerothHomologyAugmentation
    Res.bijective_zerothHomologyAugmentation
  let φ₀ : zerothHomology Res'.grade Res'.differential →ₐ[R]
      zerothHomology Res.grade Res.differential :=
    (e.symm : S →ₐ[R] zerothHomology Res.grade Res.differential).comp
      Res'.zerothHomologyAugmentation
  obtain ⟨g, hgrade, hd, hdpow, hφ₀⟩ :=
    exists_dividedPowerDGAMap_lift Res'.grade Res.grade Res'.gamma Res.gamma
      Res'.differential Res.differential Res'.coefficient Res'.polynomial
      Res.exists_boundary_of_positive φ₀
  refine ⟨g, hgrade, hd, hdpow, fun a => ?_⟩
  have h := congrArg Res.zerothHomologyAugmentation (hφ₀ a)
  rw [Res.zerothHomologyAugmentation_mk'] at h
  rw [← h]
  exact e.apply_symm_apply (Res'.zerothHomologyAugmentation _)

end ZerothHomology

section CommRTensor

variable {R : Type u} {T : Type*} {M N : Type*} [CommRing R] [CommRing T] [Algebra R T]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Reading `M ⊗[R] T` inside `T ⊗[R] N` turns `rTensor` of a map into its base change. -/
public theorem baseChange_subtype_comm_rTensor (p : Submodule R N) (f : M →ₗ[R] p)
    (u : M ⊗[R] T) :
    LinearMap.baseChange T p.subtype (TensorProduct.comm R p T (LinearMap.rTensor T f u)) =
      LinearMap.baseChange T (p.subtype.comp f) (TensorProduct.comm R M T u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a t => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end CommRTensor

section BaseChangeMap

variable {R : Type u} {A : Type v} {A' : Type w} {T : Type*} [CommRing R] [Ring A] [Ring A']
  [Algebra R A] [Algebra R A'] [CommRing T] [Algebra R T]

/-- The base change `T ⊗[R] A' → T ⊗[R] A` of a map of `R`-algebras `A' → A`. -/
public def lTensorAlgHom (g : A' →ₐ[R] A) : T ⊗[R] A' →ₐ[R] T ⊗[R] A :=
  Algebra.TensorProduct.map (AlgHom.id R T) g

/-- `lTensorAlgHom g` applies `g` to the second factor of a pure tensor. -/
@[simp]
public theorem lTensorAlgHom_tmul (g : A' →ₐ[R] A) (t : T) (a : A') :
    lTensorAlgHom (T := T) g (t ⊗ₜ[R] a) = t ⊗ₜ[R] g a := rfl

/-- `lTensorAlgHom g` is `T`-linear. -/
public theorem lTensorAlgHom_smul (g : A' →ₐ[R] A) (t : T) (x : T ⊗[R] A') :
    lTensorAlgHom g (t • x) = t • lTensorAlgHom g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q a => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

/-- `lTensorAlgHom g` is the base change of `g` as a linear map. -/
public theorem lTensorAlgHom_eq_baseChange (g : A' →ₐ[R] A) (x : T ⊗[R] A') :
    lTensorAlgHom g x = LinearMap.baseChange T g.toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q a => simp
  | add x y hx hy => simp [hx, hy]

/-- `lTensorAlgHom g` takes a base-changed submodule into a base-changed submodule, when `g`
takes the first submodule into the second. -/
public theorem lTensorAlgHom_mem_baseChange (g : A' →ₐ[R] A) (p : Submodule R A')
    (q : Submodule R A) (hg : ∀ a ∈ p, g a ∈ q) {x : T ⊗[R] A'} (hx : x ∈ p.baseChange T) :
    lTensorAlgHom g x ∈ q.baseChange T := by
  rw [Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      simpa using Submodule.tmul_mem_baseChange_of_mem (1 : T) (hg a ha)
  | zero => simp
  | add x y _ _ ihx ihy => simpa [map_add] using Submodule.add_mem _ ihx ihy
  | smul t x _ ih =>
      rw [lTensorAlgHom_smul]
      exact Submodule.smul_mem _ _ ih

/-- `lTensorAlgHom g` commutes with base-changed differentials when `g` commutes with the
differentials. -/
public theorem lTensorAlgHom_baseChange (g : A' →ₐ[R] A) (d' : A' →ₗ[R] A') (d : A →ₗ[R] A)
    (hg : ∀ a, g (d' a) = d (g a)) (x : T ⊗[R] A') :
    lTensorAlgHom g (LinearMap.baseChange T d' x) =
      LinearMap.baseChange T d (lTensorAlgHom g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q a => simp [hg]
  | add x y hx hy => simp [map_add, hx, hy]

variable (𝒜' : ℕ → Submodule R A') (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜'] [GradedAlgebra 𝒜]

omit [GradedAlgebra 𝒜'] [GradedAlgebra 𝒜] in
/-- A grade-preserving map preserves the positive even part. -/
public theorem apply_mem_positiveEvenPart (g : A' →ₐ[R] A)
    (hg : ∀ (n : ℕ) (a : A'), a ∈ 𝒜' n → g a ∈ 𝒜 n) {a : A'} (ha : a ∈ positiveEvenPart 𝒜') :
    g a ∈ positiveEvenPart 𝒜 := by
  have h : positiveEvenPart 𝒜' ≤ (positiveEvenPart 𝒜).comap g.toLinearMap :=
    iSup_le fun d x hx => Submodule.mem_iSup_of_mem d (hg _ x hx)
  exact h ha

omit [GradedAlgebra 𝒜'] [GradedAlgebra 𝒜] in
/-- The base change of a grade-preserving map preserves the positive even parts of the base
changes. -/
public theorem lTensorAlgHom_mem_positiveEvenPart (g : A' →ₐ[R] A)
    (hg : ∀ (n : ℕ) (a : A'), a ∈ 𝒜' n → g a ∈ 𝒜 n) {z : T ⊗[R] A'}
    (hz : z ∈ positiveEvenPart (restrictGrade R fun i => (𝒜' i).baseChange T)) :
    lTensorAlgHom g z ∈ positiveEvenPart (restrictGrade R fun i => (𝒜 i).baseChange T) := by
  rw [mem_positiveEvenPart_restrictGrade, positiveEvenPart_baseChange_eq] at hz ⊢
  exact lTensorAlgHom_mem_baseChange g _ _ (fun a ha => apply_mem_positiveEvenPart 𝒜' 𝒜 g hg ha) hz

variable [IsStrictlyGradedComm 𝒜'] [IsStrictlyGradedComm 𝒜]

/-- **Base change of a divided power map.** If `g` preserves gradings and divided powers, then
its base change preserves the divided powers of any two divided power structures on the base
changes normalized by their values on `1 ⊗ x`. -/
public theorem lTensorAlgHom_dpow (γ' : DividedPowerStructure 𝒜') (γ : DividedPowerStructure 𝒜)
    (g : A' →ₐ[R] A) (hg : ∀ (n : ℕ) (a : A'), a ∈ 𝒜' n → g a ∈ 𝒜 n)
    (hgγ : ∀ (n : ℕ) (a : A'), a ∈ positiveEvenPart 𝒜' → g (γ'.dpow n a) = γ.dpow n (g a))
    [IsStrictlyGradedComm (restrictGrade R fun i => (𝒜' i).baseChange T)]
    [IsStrictlyGradedComm (restrictGrade R fun i => (𝒜 i).baseChange T)]
    (δ' : DividedPowerStructure (restrictGrade R fun i => (𝒜' i).baseChange T))
    (δ : DividedPowerStructure (restrictGrade R fun i => (𝒜 i).baseChange T))
    (hδ' : ∀ (n : ℕ) (x : A'), x ∈ positiveEvenPart 𝒜' →
      δ'.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] γ'.dpow n x)
    (hδ : ∀ (n : ℕ) (x : A), x ∈ positiveEvenPart 𝒜 →
      δ.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] γ.dpow n x)
    (n : ℕ) {z : T ⊗[R] A'}
    (hz : z ∈ positiveEvenPart (restrictGrade R fun i => (𝒜' i).baseChange T)) :
    lTensorAlgHom g (δ'.dpow n z) = δ.dpow n (lTensorAlgHom g z) := by
  have hspan : ∀ w : T ⊗[R] A',
      w ∈ positiveEvenPart (restrictGrade R fun i => (𝒜' i).baseChange T) ↔
        w ∈ Submodule.span T ((positiveEvenPart 𝒜').map (TensorProduct.mk R T A' 1)) := by
    intro w
    rw [mem_positiveEvenPart_restrictGrade, positiveEvenPart_baseChange_eq,
      Submodule.baseChange_eq_span]
  have hmemT : ∀ w : T ⊗[R] A',
      w ∈ positiveEvenPart (restrictGrade R fun i => (𝒜' i).baseChange T) →
        lTensorAlgHom g w ∈ positiveEvenPart (restrictGrade R fun i => (𝒜 i).baseChange T) := by
    intro w hw
    rw [mem_positiveEvenPart_restrictGrade, positiveEvenPart_baseChange_eq] at hw ⊢
    exact lTensorAlgHom_mem_baseChange g _ _
      (fun a ha => apply_mem_positiveEvenPart 𝒜' 𝒜 g hg ha) hw
  have hsmul' : ∀ (q : T) {m : ℕ}, m ≠ 0 → ∀ {w : T ⊗[R] A'},
      w ∈ positiveEvenPart (restrictGrade R fun i => (𝒜' i).baseChange T) →
        δ'.dpow m (q • w) = (q ⊗ₜ[R] (1 : A')) ^ m * δ'.dpow m w := by
    intro q m hm w hw
    rw [smul_eq_tmul_one_mul q w, δ'.dpow_mul_even hm
      ((mem_evenPart_restrictGrade R _ _).2 (tmul_one_mem_evenPart_baseChange 𝒜' q)) hw]
  have hsmul : ∀ (q : T) {m : ℕ}, m ≠ 0 → ∀ {w : T ⊗[R] A},
      w ∈ positiveEvenPart (restrictGrade R fun i => (𝒜 i).baseChange T) →
        δ.dpow m (q • w) = (q ⊗ₜ[R] (1 : A)) ^ m * δ.dpow m w := by
    intro q m hm w hw
    rw [smul_eq_tmul_one_mul q w, δ.dpow_mul_even hm
      ((mem_evenPart_restrictGrade R _ _).2 (tmul_one_mem_evenPart_baseChange 𝒜 q)) hw]
  have key : ∀ z ∈ Submodule.span T ((positiveEvenPart 𝒜').map (TensorProduct.mk R T A' 1)),
      ∀ m : ℕ, lTensorAlgHom g (δ'.dpow m z) = δ.dpow m (lTensorAlgHom g z) := by
    intro z hz
    have hmem : ∀ w ∈ Submodule.span T ((positiveEvenPart 𝒜').map (TensorProduct.mk R T A' 1)),
        w ∈ positiveEvenPart (restrictGrade R fun i => (𝒜' i).baseChange T) :=
      fun w hw => (hspan w).2 hw
    have h0 : ∀ w ∈ Submodule.span T ((positiveEvenPart 𝒜').map (TensorProduct.mk R T A' 1)),
        lTensorAlgHom g (δ'.dpow 0 w) = δ.dpow 0 (lTensorAlgHom g w) := fun w hw => by
      rw [δ'.dpow_zero (hmem w hw), map_one, δ.dpow_zero (hmemT w (hmem w hw))]
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, ha, rfl⟩ := hz
        intro m
        simp only [TensorProduct.mk_apply]
        rw [hδ' m a ha, lTensorAlgHom_tmul, lTensorAlgHom_tmul, hgγ m a ha,
          hδ m (g a) (apply_mem_positiveEvenPart 𝒜' 𝒜 g hg ha)]
    | zero =>
        intro m
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact h0 0 (Submodule.zero_mem _)
        · rw [DividedPowerStructure.dpow_eval_zero _ δ' hm.ne', map_zero,
            DividedPowerStructure.dpow_eval_zero _ δ hm.ne']
    | add z w hz hw ihz ihw =>
        intro m
        rw [δ'.dpow_add (hmem z hz) (hmem w hw), map_add,
          δ.dpow_add (hmemT z (hmem z hz)) (hmemT w (hmem w hw)), map_sum]
        exact Finset.sum_congr rfl fun ij _ => by rw [map_mul, ihz ij.1, ihw ij.2]
    | smul q z hz ih =>
        intro m
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact h0 _ (Submodule.smul_mem _ _ hz)
        · rw [lTensorAlgHom_smul, hsmul' q hm.ne' (hmem z hz),
            hsmul q hm.ne' (hmemT z (hmem z hz)), map_mul, map_pow, lTensorAlgHom_tmul,
            map_one, ih m]
  exact key z ((hspan z).1 hz) n

end BaseChangeMap

section ComplexMap

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] Resolution.ring Resolution.algebra Resolution.graded
  Resolution.strict Resolution.dga Resolution.compatible

variable {R S σ σ' : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {φ : MvPolynomial σ R →ₐ[R] S} {φ' : MvPolynomial σ' R →ₐ[R] S}
  (Res : Resolution R S σ φ) (Res' : Resolution R S σ' φ')
  (g : Res'.A →ₐ[R] Res.A) (hg : ∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n)

/-- A grade-preserving map between two Tate resolutions, on the degree-`n` pieces. -/
public def Resolution.gradeMap (n : ℕ) : Res'.grade n →ₗ[R] Res.grade n :=
  (g.toLinearMap.comp (Res'.grade n).subtype).codRestrict _ fun x => hg n x x.2

/-- The map on degree-`n` pieces does not change the underlying element. -/
@[simp]
public theorem Resolution.coe_gradeMap (n : ℕ) (x : Res'.grade n) :
    (Res.gradeMap Res' g hg n x : Res.A) = g x := rfl

variable (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a))

/-- A grade-preserving map between two Tate resolutions commuting with the differentials, as a
map of their underlying chain complexes. -/
public def Resolution.complexMap : Res'.complex ⟶ Res.complex where
  f n := ModuleCat.ofHom (Res.gradeMap Res' g hg n)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    simp only [Resolution.complex, ChainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    exact (hd x.1).symm

/-- The chain map lies over the identity of `S`. -/
public theorem Resolution.complexMap_comm
    (haug : ∀ a : Res'.A, Res.augmentation (g a) = Res'.augmentation a)
    (hφ : Function.Surjective φ) (hφ' : Function.Surjective φ') :
    (Res.complexMap Res' g hg hd).f 0 ≫ (Res.projectiveResolution hφ).π.f 0 =
      (Res'.projectiveResolution hφ').π.f 0 ≫ 𝟙 _ := by
  rw [Category.comp_id]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp only [Resolution.projectiveResolution, Resolution.augmentationHom, Resolution.complexMap]
  exact haug x.1

/-- The identification of `Tor` with homology is the composite of the balancing isomorphism with
the computation of the left derived functor by the projective resolution. -/
public theorem Resolution.torIsoHomology_hom (hφ : Function.Surjective φ) (M : ModuleCat.{u} R)
    (n : ℕ) :
    (Res.torIsoHomology hφ M n).hom =
      (((Tor_iso_Tor' R n).app (ModuleCat.of R S)).app M).hom ≫
        ((Res.projectiveResolution hφ).isoLeftDerivedObj
          ((tensoringRight (ModuleCat.{u} R)).obj M) n).hom :=
  rfl

/-- **The identifications of `Tor` with homology are compatible with a map of resolutions.** -/
public theorem Resolution.torIsoHomology_hom_comp_homologyMap
    (haug : ∀ a : Res'.A, Res.augmentation (g a) = Res'.augmentation a)
    (hφ : Function.Surjective φ) (hφ' : Function.Surjective φ') (M : ModuleCat.{u} R) (n : ℕ) :
    (Res'.torIsoHomology hφ' M n).hom ≫
        HomologicalComplex.homologyMap
          ((((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex
            (ComplexShape.down ℕ)).map (Res.complexMap Res' g hg hd)) n =
      (Res.torIsoHomology hφ M n).hom := by
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 (ModuleCat.of R S))
    (Res'.projectiveResolution hφ') (Res.projectiveResolution hφ) (Res.complexMap Res' g hg hd)
    (Res.complexMap_comm Res' g hg hd haug hφ hφ') ((tensoringRight (ModuleCat.{u} R)).obj M) n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [Res.torIsoHomology_hom, Res'.torIsoHomology_hom, h]
  exact Category.assoc _ _ _

end ComplexMap

section HomologyElement

open CategoryTheory

variable {R : Type u} [CommRing R] {K L : ChainComplex (ModuleCat.{u} R) ℕ} (ψ : K ⟶ L) (n : ℕ)

/-- A chain map sends the class of a cycle to the class of its image. -/
public theorem homologyMap_homologyπ_apply (k : K.cycles n) :
    (HomologicalComplex.homologyMap ψ n).hom ((K.homologyπ n).hom k) =
      (L.homologyπ n).hom ((HomologicalComplex.cyclesMap ψ n).hom k) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality,
    ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The map on cycles induced by a chain map is the chain map on underlying elements. -/
public theorem iCycles_cyclesMap_apply (k : K.cycles n) :
    (L.iCycles n).hom ((HomologicalComplex.cyclesMap ψ n).hom k) =
      (ψ.f n).hom ((K.iCycles n).hom k) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.cyclesMap_i,
    ModuleCat.hom_comp, LinearMap.comp_apply]

end HomologyElement


section GradedMap

open CategoryTheory

variable {R : Type u} {B : Type v} {B' : Type v} [CommRing R] [Ring B] [Ring B'] [Algebra R B]
  [Algebra R B'] (ℬ : ℕ → Submodule R B) (ℬ' : ℕ → Submodule R B') [GradedAlgebra ℬ]
  [GradedAlgebra ℬ'] (dB : B →ₗ[R] B) (dB' : B' →ₗ[R] B') [IsDifferentialGradedAlgebra ℬ dB]
  [IsDifferentialGradedAlgebra ℬ' dB'] (h0 : ∀ r : R, algebraMap R B r ∈ ℬ 0)
  (h0' : ∀ r : R, algebraMap R B' r ∈ ℬ' 0) (f : B' →ₗ[R] B)

/-- A grade-preserving map of differential graded algebras commuting with the differentials, as a
map of the complexes of homogeneous pieces. -/
public def gradedChainComplexMap (hf : ∀ (n : ℕ) (x : B'), x ∈ ℬ' n → f x ∈ ℬ n)
    (hfd : ∀ x : B', f (dB' x) = dB (f x)) :
    gradedChainComplex ℬ' dB' h0' ⟶ gradedChainComplex ℬ dB h0 where
  f n := ModuleCat.ofHom ((f.comp (coefficientGrade ℬ' h0' n).subtype).codRestrict
    (coefficientGrade ℬ h0 n) fun x => hf n x x.2)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [gradedChainComplex_d, gradedChainComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (hfd x.1).symm)

/-- The map on degree-`n` cycles. -/
public def gradeCyclesMap (hf : ∀ (n : ℕ) (x : B'), x ∈ ℬ' n → f x ∈ ℬ n)
    (hfd : ∀ x : B', f (dB' x) = dB (f x)) (n : ℕ) :
    gradeCycles ℬ' dB' n →ₗ[R] gradeCycles ℬ dB n where
  toFun w := ⟨⟨f w.1.1, hf n _ w.1.2⟩, (mem_gradeCycles_iff ℬ dB).2 (by
    rw [← hfd, (mem_gradeCycles_iff ℬ' dB').1 w.2, map_zero])⟩
  map_add' _ _ := Subtype.ext (Subtype.ext (map_add f _ _))
  map_smul' _ _ := Subtype.ext (Subtype.ext (map_smul f _ _))

/-- **The degreewise comparison with the complex of homogeneous pieces is natural.** -/
public theorem homologyMap_gradedChainComplexMap_apply
    (hf : ∀ (n : ℕ) (x : B'), x ∈ ℬ' n → f x ∈ ℬ n)
    (hfd : ∀ x : B', f (dB' x) = dB (f x)) (n : ℕ) (w : gradeCycles ℬ' dB' n) :
    (HomologicalComplex.homologyMap (gradedChainComplexMap ℬ ℬ' dB dB' h0 h0' f hf hfd) n).hom
        ((gradedChainComplexHomologyEquiv ℬ' dB' h0' n).symm
          (gradeHomologyEquivCoefficientHomology ℬ' dB' h0' n (Submodule.Quotient.mk w))) =
      (gradedChainComplexHomologyEquiv ℬ dB h0 n).symm
        (gradeHomologyEquivCoefficientHomology ℬ dB h0 n
          (Submodule.Quotient.mk (gradeCyclesMap ℬ ℬ' dB dB' f hf hfd n w))) := by
  rw [gradeHomologyEquivCoefficientHomology_mk, gradeHomologyEquivCoefficientHomology_mk,
    gradedChainComplexHomologyEquiv_symm_apply, gradedChainComplexHomologyEquiv_symm_apply]
  let cmap : coefficientCycles ℬ' dB' h0' n →ₗ[R] coefficientCycles ℬ dB h0 n :=
    f.restrict fun x hx => ⟨hf n x hx.1, by rw [← hfd, hx.2, map_zero]⟩
  have hz : gradeCyclesEquivCoefficientCycles ℬ dB h0 n (gradeCyclesMap ℬ ℬ' dB dB' f hf hfd n w) =
      cmap (gradeCyclesEquivCoefficientCycles ℬ' dB' h0' n w) := rfl
  rw [hz]
  generalize gradeCyclesEquivCoefficientCycles ℬ' dB' h0' n w = z'
  have hcyc : toCyclesGradedChainComplex ℬ' dB' h0' n ≫
      HomologicalComplex.cyclesMap (gradedChainComplexMap ℬ ℬ' dB dB' h0 h0' f hf hfd) n =
        ModuleCat.ofHom cmap ≫ toCyclesGradedChainComplex ℬ dB h0 n := by
    rw [← cancel_mono ((gradedChainComplex ℬ dB h0).iCycles n), Category.assoc, Category.assoc,
      HomologicalComplex.cyclesMap_i, toCyclesGradedChainComplex_iCycles, ← Category.assoc,
      toCyclesGradedChainComplex_iCycles]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext rfl)
  have key : toCyclesGradedChainComplex ℬ' dB' h0' n ≫
      (gradedChainComplex ℬ' dB' h0').homologyπ n ≫
        HomologicalComplex.homologyMap (gradedChainComplexMap ℬ ℬ' dB dB' h0 h0' f hf hfd) n =
      ModuleCat.ofHom cmap ≫ toCyclesGradedChainComplex ℬ dB h0 n ≫
        (gradedChainComplex ℬ dB h0).homologyπ n := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc, hcyc, Category.assoc]
  have h := congrArg (fun φ => φ.hom z') key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  rw [coefficientCyclesToHomology, coefficientCyclesToHomology, ModuleCat.hom_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, h]

end GradedMap

section TorComparisonSquare

open CategoryTheory

variable {R : Type u} [CommRing R] {K' K L' L : ChainComplex (ModuleCat.{v} R) ℕ}

/-- The comparison of homology through two commuting squares, read on elements. -/
public theorem inv_homologyMap_of_comm (β' : K' ≅ L') (β : K ≅ L) (G : K' ⟶ K) (Fm : L' ⟶ L)
    (hcomm : β'.hom ≫ Fm = G ≫ β.hom) {X : ModuleCat.{v} R} (n : ℕ)
    (τ' : X ≅ L'.homology n) (τ : X ≅ L.homology n)
    (hτ : τ'.hom ≫ HomologicalComplex.homologyMap Fm n = τ.hom) (y : K'.homology n) :
    τ.inv.hom ((HomologicalComplex.homologyMap β.hom n).hom
        ((HomologicalComplex.homologyMap G n).hom y)) =
      τ'.inv.hom ((HomologicalComplex.homologyMap β'.hom n).hom y) := by
  have h1 : HomologicalComplex.homologyMap G n ≫ HomologicalComplex.homologyMap β.hom n =
      HomologicalComplex.homologyMap β'.hom n ≫ HomologicalComplex.homologyMap Fm n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hcomm]
  have h2 : HomologicalComplex.homologyMap Fm n ≫ τ.inv = τ'.inv := by
    rw [← cancel_epi τ'.hom, ← Category.assoc, hτ, Iso.hom_inv_id, Iso.hom_inv_id]
  have h3 : HomologicalComplex.homologyMap G n ≫ HomologicalComplex.homologyMap β.hom n ≫ τ.inv =
      HomologicalComplex.homologyMap β'.hom n ≫ τ'.inv := by
    rw [← Category.assoc, h1, Category.assoc, h2]
  have h4 := congrArg (fun φ => φ.hom y) h3
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h4

end TorComparisonSquare

section ClassMapComparison

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] Resolution.ring Resolution.algebra Resolution.graded
  Resolution.strict Resolution.dga Resolution.compatible

attribute [local instance] isDifferentialGradedAlgebra_baseChange

variable {R S σ σ' : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {φ : MvPolynomial σ R →ₐ[R] S} {φ' : MvPolynomial σ' R →ₐ[R] S}
  (Res : Resolution R S σ φ) (Res' : Resolution R S σ' φ') (T : Type u) [CommRing T]
  [Algebra R T]
  (g : Res'.A →ₐ[R] Res.A)

/-- The base change of a grade-preserving map preserves the gradings of the base changes. -/
public theorem Resolution.lTensorAlgHom_mem_grade
    (hg : ∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n) (n : ℕ) {x : T ⊗[R] Res'.A}
    (hx : x ∈ restrictGrade R (fun i => (Res'.grade i).baseChange T) n) :
    lTensorAlgHom g x ∈ restrictGrade R (fun i => (Res.grade i).baseChange T) n :=
  lTensorAlgHom_mem_baseChange g _ _ (fun a ha => hg n a ha) hx

/-- The base change of a map commuting with the differentials commutes with the base-changed
differentials. -/
public theorem Resolution.lTensorAlgHom_differential
    (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a)) (x : T ⊗[R] Res'.A) :
    lTensorAlgHom g ((LinearMap.baseChange T Res'.differential).restrictScalars R x) =
      (LinearMap.baseChange T Res.differential).restrictScalars R (lTensorAlgHom g x) :=
  lTensorAlgHom_baseChange g _ _ hd x

/-- The base change of a map of resolutions, on cycles. -/
public def Resolution.cyclesBaseChangeMap
    (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a)) :
    cycles ((LinearMap.baseChange T Res'.differential).restrictScalars R) →ₗ[R]
      cycles ((LinearMap.baseChange T Res.differential).restrictScalars R) :=
  (lTensorAlgHom (T := T) g).toLinearMap.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [AlgHom.toLinearMap_apply, ← Res.lTensorAlgHom_differential Res' T g hd, hx, map_zero]

/-- The base change of a map of resolutions, on homology. -/
public def Resolution.homologyBaseChangeMap
    (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a)) :
    Homology (𝒜 := restrictGrade R fun i => (Res'.grade i).baseChange T)
        ((LinearMap.baseChange T Res'.differential).restrictScalars R) →ₗ[R]
      Homology (𝒜 := restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R) :=
  Submodule.mapQ _ _ (Res.cyclesBaseChangeMap Res' T g hd) fun y hy => by
    obtain ⟨x, rfl⟩ := hy
    exact ⟨lTensorAlgHom g x,
      Subtype.ext (Res.lTensorAlgHom_differential Res' T g hd x).symm⟩

/-- **The term comparison is natural in the resolution.** -/
public theorem Resolution.rTensor_gradeMap_baseChangeCoefficientGradeEquiv
    (hg : ∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n) (n : ℕ)
    (x : ↥(coefficientGrade (restrictGrade R fun i => (Res'.grade i).baseChange T)
      (algebraMap_mem_baseChange_zero (T := T) Res'.grade) n))
    (hx : lTensorAlgHom g (x : T ⊗[R] Res'.A) ∈
      coefficientGrade (restrictGrade R fun i => (Res.grade i).baseChange T)
        (algebraMap_mem_baseChange_zero (T := T) Res.grade) n) :
    LinearMap.rTensor T (Res.gradeMap Res' g hg n)
        (baseChangeCoefficientGradeEquiv (T := T) Res'.grade n x) =
      baseChangeCoefficientGradeEquiv (T := T) Res.grade n ⟨lTensorAlgHom g x, hx⟩ := by
  apply injective_rTensorGradeInclusion (T := T) Res.grade n
  rw [rTensorGradeInclusion_baseChangeCoefficientGradeEquiv, rTensorGradeInclusion_apply,
    baseChange_subtype_comm_rTensor]
  have hcomp : (Res.grade n).subtype.comp (Res.gradeMap Res' g hg n) =
      g.toLinearMap.comp (Res'.grade n).subtype := rfl
  rw [hcomp, LinearMap.baseChange_comp, LinearMap.comp_apply,
    comm_baseChangeCoefficientGradeEquiv, baseChange_subtype_baseChangeGradeEquiv,
    LinearEquiv.coe_ofEq_apply]
  exact (lTensorAlgHom_eq_baseChange g (x : T ⊗[R] Res'.A)).symm

/-- `Resolution.lTensorAlgHom_mem_grade`, for the underlying linear map. -/
public theorem Resolution.toLinearMap_lTensorAlgHom_mem_grade
    (hg : ∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n) (n : ℕ)
    (x : T ⊗[R] Res'.A) (hx : x ∈ restrictGrade R (fun i => (Res'.grade i).baseChange T) n) :
    (lTensorAlgHom (T := T) g).toLinearMap x ∈
      restrictGrade R (fun i => (Res.grade i).baseChange T) n :=
  Res.lTensorAlgHom_mem_grade Res' T g hg n hx

/-- `Resolution.lTensorAlgHom_differential`, for the underlying linear map. -/
public theorem Resolution.toLinearMap_lTensorAlgHom_differential
    (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a)) (x : T ⊗[R] Res'.A) :
    (lTensorAlgHom (T := T) g).toLinearMap
        ((LinearMap.baseChange T Res'.differential).restrictScalars R x) =
      (LinearMap.baseChange T Res.differential).restrictScalars R
        ((lTensorAlgHom (T := T) g).toLinearMap x) :=
  Res.lTensorAlgHom_differential Res' T g hd x

/-- The base change of a map of resolutions, as a map of the complexes of homogeneous pieces. -/
public def Resolution.gradedChainComplexBaseChangeMap
    (hg : ∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n)
    (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a)) :
    gradedChainComplex (restrictGrade R fun i => (Res'.grade i).baseChange T)
        ((LinearMap.baseChange T Res'.differential).restrictScalars R)
        (algebraMap_mem_baseChange_zero (T := T) Res'.grade) ⟶
      gradedChainComplex (restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R)
        (algebraMap_mem_baseChange_zero (T := T) Res.grade) :=
  gradedChainComplexMap (restrictGrade R fun i => (Res.grade i).baseChange T)
    (restrictGrade R fun i => (Res'.grade i).baseChange T)
    ((LinearMap.baseChange T Res.differential).restrictScalars R)
    ((LinearMap.baseChange T Res'.differential).restrictScalars R)
    (algebraMap_mem_baseChange_zero (T := T) Res.grade)
    (algebraMap_mem_baseChange_zero (T := T) Res'.grade) (lTensorAlgHom (T := T) g).toLinearMap
    (Res.toLinearMap_lTensorAlgHom_mem_grade Res' T g hg)
    (Res.toLinearMap_lTensorAlgHom_differential Res' T g hd)

/-- **The comparison of complexes (b) is natural in the resolution.** -/
public theorem Resolution.baseChangeComplexIso_hom_comp_map
    (hg : ∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n)
    (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a)) :
    (baseChangeComplexIso Res' T).hom ≫
        (((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R T)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (Res.complexMap Res' g hg hd) =
      Res.gradedChainComplexBaseChangeMap Res' T g hg hd ≫ (baseChangeComplexIso Res T).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply]
  exact Res.rTensor_gradeMap_baseChangeCoefficientGradeEquiv Res' T g hg n x
    (Res.lTensorAlgHom_mem_grade Res' T g hg n x.2)

/-- The Tor identification, unfolded into its three comparisons. -/
public theorem Resolution.gradeHomologyEquivTor_apply (hφ : Function.Surjective φ) (n : ℕ)
    (c : gradeHomology (restrictGrade R fun i => (Res.grade i).baseChange T)
      ((LinearMap.baseChange T Res.differential).restrictScalars R) n) :
    gradeHomologyEquivTor Res T hφ n c =
      (Res.torIsoHomology hφ (ModuleCat.of R T) n).inv.hom
        ((HomologicalComplex.homologyMap (baseChangeComplexIso Res T).hom n).hom
          ((gradedChainComplexHomologyEquiv
              (restrictGrade R fun i => (Res.grade i).baseChange T)
              ((LinearMap.baseChange T Res.differential).restrictScalars R)
              (algebraMap_mem_baseChange_zero (T := T) Res.grade) n).symm
            (gradeHomologyEquivCoefficientHomology
              (restrictGrade R fun i => (Res.grade i).baseChange T)
              ((LinearMap.baseChange T Res.differential).restrictScalars R)
              (algebraMap_mem_baseChange_zero (T := T) Res.grade) n c))) :=
  rfl

/-- **The Tor identification is natural in the resolution.** A map of Tate resolutions over the
identity of `S` carries the class of a degree-`n` cycle to a class with the same image in
`Tor_n^R(S, T)`. -/
public theorem Resolution.gradeHomologyEquivTor_gradeCyclesMap
    (hg : ∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n)
    (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a))
    (haug : ∀ a : Res'.A, Res.augmentation (g a) = Res'.augmentation a)
    (hφ : Function.Surjective φ) (hφ' : Function.Surjective φ') (n : ℕ)
    (w : gradeCycles (restrictGrade R fun i => (Res'.grade i).baseChange T)
      ((LinearMap.baseChange T Res'.differential).restrictScalars R) n) :
    gradeHomologyEquivTor Res T hφ n (Submodule.Quotient.mk
        (gradeCyclesMap (restrictGrade R fun i => (Res.grade i).baseChange T)
          (restrictGrade R fun i => (Res'.grade i).baseChange T)
          ((LinearMap.baseChange T Res.differential).restrictScalars R)
          ((LinearMap.baseChange T Res'.differential).restrictScalars R)
          (lTensorAlgHom (T := T) g).toLinearMap
          (Res.toLinearMap_lTensorAlgHom_mem_grade Res' T g hg)
          (Res.toLinearMap_lTensorAlgHom_differential Res' T g hd) n w)) =
      gradeHomologyEquivTor Res' T hφ' n (Submodule.Quotient.mk w) := by
  rw [Res.gradeHomologyEquivTor_apply T hφ, Res'.gradeHomologyEquivTor_apply T hφ']
  have hA := homologyMap_gradedChainComplexMap_apply
    (restrictGrade R fun i => (Res.grade i).baseChange T)
    (restrictGrade R fun i => (Res'.grade i).baseChange T)
    ((LinearMap.baseChange T Res.differential).restrictScalars R)
    ((LinearMap.baseChange T Res'.differential).restrictScalars R)
    (algebraMap_mem_baseChange_zero (T := T) Res.grade)
    (algebraMap_mem_baseChange_zero (T := T) Res'.grade) (lTensorAlgHom (T := T) g).toLinearMap
    (Res.toLinearMap_lTensorAlgHom_mem_grade Res' T g hg)
    (Res.toLinearMap_lTensorAlgHom_differential Res' T g hd) n w
  rw [← hA]
  exact inv_homologyMap_of_comm (baseChangeComplexIso Res' T) (baseChangeComplexIso Res T)
    (Res.gradedChainComplexBaseChangeMap Res' T g hg hd)
    ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R T)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (Res.complexMap Res' g hg hd))
    (Res.baseChangeComplexIso_hom_comp_map Res' T g hg hd) n
    (Res'.torIsoHomology hφ' (ModuleCat.of R T) n) (Res.torIsoHomology hφ (ModuleCat.of R T) n)
    (Res.torIsoHomology_hom_comp_homologyMap Res' g hg hd haug hφ hφ' (ModuleCat.of R T) n) _

/-- **The identifications of the graded Tor module with homology are compatible with a map of
Tate resolutions.** -/
public theorem Resolution.homologyBaseChangeMap_comp_torDirectSumEquivHomology
    (hg : ∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n)
    (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a))
    (haug : ∀ a : Res'.A, Res.augmentation (g a) = Res'.augmentation a)
    (hφ : Function.Surjective φ) (hφ' : Function.Surjective φ') :
    (Res.homologyBaseChangeMap Res' T g hd).comp
        (torDirectSumEquivHomology Res' T hφ').toLinearMap =
      (torDirectSumEquivHomology Res T hφ).toLinearMap := by
  refine DirectSum.linearMap_ext R fun n => LinearMap.ext fun y => ?_
  obtain ⟨⟨⟨x, hx⟩, hdx⟩, hw⟩ := Submodule.mkQ_surjective
    ((gradeBoundaries (restrictGrade R fun i => (Res'.grade i).baseChange T)
      ((LinearMap.baseChange T Res'.differential).restrictScalars R) n).comap
      (gradeCycles (restrictGrade R fun i => (Res'.grade i).baseChange T)
        ((LinearMap.baseChange T Res'.differential).restrictScalars R) n).subtype)
    ((gradeHomologyEquivTor Res' T hφ' n).symm y)
  have hy : y = gradeHomologyEquivTor Res' T hφ' n (Submodule.Quotient.mk ⟨⟨x, hx⟩, hdx⟩) := by
    rw [← Submodule.mkQ_apply, hw, LinearEquiv.apply_symm_apply]
  subst hy
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe]
  have hT := Res.gradeHomologyEquivTor_gradeCyclesMap Res' T g hg hd haug hφ hφ' n ⟨⟨x, hx⟩, hdx⟩
  have hT' := (LinearEquiv.symm_apply_eq (gradeHomologyEquivTor Res T hφ n)).2 hT.symm
  have e1 : ((gradeHomologyEquivTotalGrade (restrictGrade R fun i => (Res'.grade i).baseChange T)
        ((LinearMap.baseChange T Res'.differential).restrictScalars R) n
        (Submodule.Quotient.mk ⟨⟨x, hx⟩, hdx⟩) :
      ↥(totalHomologyGrade (restrictGrade R fun i => (Res'.grade i).baseChange T)
        ((LinearMap.baseChange T Res'.differential).restrictScalars R) n)) :
      Homology (𝒜 := restrictGrade R fun i => (Res'.grade i).baseChange T)
        ((LinearMap.baseChange T Res'.differential).restrictScalars R)) =
      Submodule.Quotient.mk ⟨x, hdx⟩ :=
    gradeHomologyEquivTotalGrade_mk _ _ n ⟨x, hdx⟩ hx
  have e2 : ((gradeHomologyEquivTotalGrade (restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R) n
        (Submodule.Quotient.mk
          (gradeCyclesMap (restrictGrade R fun i => (Res.grade i).baseChange T)
            (restrictGrade R fun i => (Res'.grade i).baseChange T)
            ((LinearMap.baseChange T Res.differential).restrictScalars R)
            ((LinearMap.baseChange T Res'.differential).restrictScalars R)
            (lTensorAlgHom (T := T) g).toLinearMap
            (Res.toLinearMap_lTensorAlgHom_mem_grade Res' T g hg)
            (Res.toLinearMap_lTensorAlgHom_differential Res' T g hd) n ⟨⟨x, hx⟩, hdx⟩)) :
      ↥(totalHomologyGrade (restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R) n)) :
      Homology (𝒜 := restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R)) =
      Submodule.Quotient.mk (Res.cyclesBaseChangeMap Res' T g hd ⟨x, hdx⟩) :=
    gradeHomologyEquivTotalGrade_mk _ _ n (Res.cyclesBaseChangeMap Res' T g hd ⟨x, hdx⟩)
      (Res.lTensorAlgHom_mem_grade Res' T g hg n hx)
  have h1 : torDirectSumEquivHomology Res' T hφ'
      (DirectSum.lof R ℕ (fun m => torGraded R S T m) n
        (gradeHomologyEquivTor Res' T hφ' n (Submodule.Quotient.mk ⟨⟨x, hx⟩, hdx⟩))) =
      Submodule.Quotient.mk ⟨x, hdx⟩ :=
    (torDirectSumEquivHomology_lof Res' T hφ' n
      (gradeHomologyEquivTor Res' T hφ' n (Submodule.Quotient.mk ⟨⟨x, hx⟩, hdx⟩))).trans
      ((congrArg (fun c => ((gradeHomologyEquivTotalGrade
          (restrictGrade R fun i => (Res'.grade i).baseChange T)
          ((LinearMap.baseChange T Res'.differential).restrictScalars R) n c :
          ↥(totalHomologyGrade (restrictGrade R fun i => (Res'.grade i).baseChange T)
            ((LinearMap.baseChange T Res'.differential).restrictScalars R) n)) :
          Homology (𝒜 := restrictGrade R fun i => (Res'.grade i).baseChange T)
            ((LinearMap.baseChange T Res'.differential).restrictScalars R)))
        ((gradeHomologyEquivTor Res' T hφ' n).symm_apply_apply
          (Submodule.Quotient.mk ⟨⟨x, hx⟩, hdx⟩))).trans e1)
  have h2 : torDirectSumEquivHomology Res T hφ
      (DirectSum.lof R ℕ (fun m => torGraded R S T m) n
        (gradeHomologyEquivTor Res' T hφ' n (Submodule.Quotient.mk ⟨⟨x, hx⟩, hdx⟩))) =
      Submodule.Quotient.mk (Res.cyclesBaseChangeMap Res' T g hd ⟨x, hdx⟩) :=
    (torDirectSumEquivHomology_lof Res T hφ n
      (gradeHomologyEquivTor Res' T hφ' n (Submodule.Quotient.mk ⟨⟨x, hx⟩, hdx⟩))).trans
      ((congrArg (fun c => ((gradeHomologyEquivTotalGrade
          (restrictGrade R fun i => (Res.grade i).baseChange T)
          ((LinearMap.baseChange T Res.differential).restrictScalars R) n c :
          ↥(totalHomologyGrade (restrictGrade R fun i => (Res.grade i).baseChange T)
            ((LinearMap.baseChange T Res.differential).restrictScalars R) n)) :
          Homology (𝒜 := restrictGrade R fun i => (Res.grade i).baseChange T)
            ((LinearMap.baseChange T Res.differential).restrictScalars R))) hT').trans e2)
  rw [h1, h2]
  exact Submodule.mapQ_apply _ _ _ _

/-- **The class map of a Tate resolution factors through any map of Tate resolutions.** -/
public theorem Resolution.directSumClass_lTensorAlgHom
    (hg : ∀ (n : ℕ) (a : Res'.A), a ∈ Res'.grade n → g a ∈ Res.grade n)
    (hd : ∀ a : Res'.A, g (Res'.differential a) = Res.differential (g a))
    (haug : ∀ a : Res'.A, Res.augmentation (g a) = Res'.augmentation a)
    (hφ : Function.Surjective φ) (hφ' : Function.Surjective φ') (x : T ⊗[R] Res'.A)
    (hx : (LinearMap.baseChange T Res'.differential).restrictScalars R x = 0)
    (hgx : (LinearMap.baseChange T Res.differential).restrictScalars R (lTensorAlgHom g x) = 0) :
    directSumClass (torDirectSumEquivHomology Res T hφ) ⟨lTensorAlgHom g x, hgx⟩ =
      directSumClass (torDirectSumEquivHomology Res' T hφ') ⟨x, hx⟩ := by
  have h := LinearMap.congr_fun
    (Res.homologyBaseChangeMap_comp_torDirectSumEquivHomology Res' T g hg hd haug hφ hφ')
    ((torDirectSumEquivHomology Res' T hφ').symm (Submodule.Quotient.mk ⟨x, hx⟩))
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at h
  rw [directSumClass_apply, directSumClass_apply]
  have hmk : (Submodule.Quotient.mk ⟨lTensorAlgHom g x, hgx⟩ :
      Homology (𝒜 := restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R)) =
      Res.homologyBaseChangeMap Res' T g hd (Submodule.Quotient.mk ⟨x, hx⟩) := rfl
  rw [hmk, h, LinearEquiv.symm_apply_apply]

end ClassMapComparison

section TorAlgebra

attribute [local instance] Resolution.ring Resolution.algebra Resolution.graded
  Resolution.strict Resolution.dga Resolution.compatible

attribute [local instance] isDifferentialGradedAlgebra_baseChange

/-- **The divided power algebra `Tor_*^R(S, T)`, independent of the Tate resolution.** For a
commutative ring `R` and commutative `R`-algebras `S` and `T`, the direct sum
`⨁ n, Tor_n^R(S, T)` carries a ring structure and an `R`-algebra structure, with the direct sum's
own addition and scalar multiplication, a grading whose degree-`n` piece is the range of the
`n`-th inclusion, a graded algebra structure for that grading, strict graded commutativity, and a
divided power structure, such that for **every** Tate resolution `A` of `S` (a
`DividedPowers.TateResolution.Resolution` along any surjection `φ` from a polynomial algebra
onto `S`) the following holds. The base change `T ⊗[R] A` is a strictly graded-commutative
differential graded algebra with divided powers compatible with its differential, and normalized
by `γₙ(1 ⊗ x) = 1 ⊗ γₙ(x)`; and the class map `κ` of `torDirectSumEquivHomology`, which sends a
cycle of `T ⊗[R] A` to the element of the direct sum corresponding to its homology class, is onto,
takes a cycle of degree `n` into the degree-`n` piece, and is unital, multiplicative and
compatible with the divided powers.

Since `κ` is onto, these conditions determine the multiplication, the unit and the divided powers
of the direct sum from any one Tate resolution: the structure built from two choices of `A` is the
same. The proof transports the structure from the Tate resolution of the tautological
presentation of `S` (`exists_dividedPowerStructure_torDirectSum`), and compares an arbitrary
Tate resolution `A` with it through a map of divided power differential graded algebras over `S`
supplied by Tag 09PP (`Resolution.exists_resolutionMap`); its base change commutes with the two
identifications of homology with `Tor` (`Resolution.directSumClass_lTensorAlgHom`), and preserves
products and divided powers. -/
@[stacks 09PQ "divided power algebra structure on Tor, independent of the Tate resolution"]
public theorem exists_dividedPowerStructure_torDirectSum_forall_resolution
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    ∃ hRing : Ring (DirectSum ℕ fun n => torGraded R S T n),
      ∃ hAlgebra : @Algebra R (DirectSum ℕ fun n => torGraded R S T n) _ hRing.toSemiring,
        hRing.toAddCommGroup =
          (inferInstance : AddCommGroup (DirectSum ℕ fun n => torGraded R S T n)) ∧
        @Algebra.toSMul R (DirectSum ℕ fun n => torGraded R S T n) _
            hRing.toSemiring hAlgebra =
          (inferInstance : SMul R (DirectSum ℕ fun n => torGraded R S T n)) ∧
        (letI := hRing
         letI := hAlgebra
         letI : AddCommMonoid (DirectSum ℕ fun n => torGraded R S T n) :=
           hRing.toAddCommMonoid
         letI : Module R (DirectSum ℕ fun n => torGraded R S T n) := Algebra.toModule
         ∃ 𝒟 : ℕ → Submodule R (DirectSum ℕ fun n => torGraded R S T n),
           (∀ n, (𝒟 n : Set (DirectSum ℕ fun m => torGraded R S T m)) =
             Set.range (DirectSum.lof R ℕ (fun m => torGraded R S T m) n)) ∧
           ∃ hGraded : GradedAlgebra 𝒟,
             letI := hGraded
             ∃ hStrictD : IsStrictlyGradedComm 𝒟,
               letI := hStrictD
               ∃ γD : @DividedPowerStructure R
                   (DirectSum ℕ fun n => torGraded R S T n) _ hRing hAlgebra 𝒟
                   hGraded hStrictD,
                 ∀ (σ : Type u) (φ : MvPolynomial σ R →ₐ[R] S) (hφ : Function.Surjective φ)
                   (Res : Resolution R S σ φ),
                   let ℬ : ℕ → Submodule R (T ⊗[R] Res.A) :=
                     restrictGrade R fun i => (Res.grade i).baseChange T
                   let dB : T ⊗[R] Res.A →ₗ[R] T ⊗[R] Res.A :=
                     (LinearMap.baseChange T Res.differential).restrictScalars R
                   ∃ hStrict : IsStrictlyGradedComm ℬ,
                     letI := hStrict
                     ∃ γB : DividedPowerStructure ℬ,
                       IsCompatibleWithDifferential γB dB ∧
                       (∀ (n : ℕ) (x : Res.A), x ∈ positiveEvenPart Res.grade →
                         γB.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] Res.gamma.dpow n x) ∧
                       (let κ := directSumClass (torDirectSumEquivHomology Res T hφ)
                        Function.Surjective κ ∧
                        (∀ (n : ℕ) (x : T ⊗[R] Res.A) (h : dB x = 0), x ∈ ℬ n →
                          κ ⟨x, h⟩ ∈ 𝒟 n) ∧
                        (∃ h1 : dB (1 : T ⊗[R] Res.A) = 0, κ ⟨1, h1⟩ = 1) ∧
                        (∀ {x y : T ⊗[R] Res.A} (hx : dB x = 0) (hy : dB y = 0),
                          ∃ hxy : dB (x * y) = 0,
                            κ ⟨x * y, hxy⟩ = κ ⟨x, hx⟩ * κ ⟨y, hy⟩) ∧
                        (∀ {n : ℕ} {x : T ⊗[R] Res.A}, x ∈ positiveEvenPart ℬ →
                          ∀ hd : dB x = 0,
                            ∃ hγ : dB (γB.dpow n x) = 0,
                              γD.dpow n (κ ⟨x, hd⟩) = κ ⟨γB.dpow n x, hγ⟩))) := by
  obtain ⟨Res₀, -, hbody⟩ := exists_dividedPowerStructure_homology_tateResolution R S T
  obtain ⟨hStrict₀, hDGA₀, γB₀, hcompat₀, hγB₀, hind₀⟩ := hbody
  have hφ₀ := surjective_tautologicalPresentation R S
  obtain ⟨hRing, hAlgebra, hadd, hsmul, hrest⟩ :=
    exists_dividedPowerStructure_directSum _ _ γB₀ hind₀
      (torDirectSumEquivHomology Res₀ T hφ₀) (map_torDirectSumEquivHomology_range_lof Res₀ T hφ₀)
  refine ⟨hRing, hAlgebra, hadd, hsmul, ?_⟩
  let := hRing
  let := hAlgebra
  let : AddCommMonoid (DirectSum ℕ fun n => torGraded R S T n) := hRing.toAddCommMonoid
  let : Module R (DirectSum ℕ fun n => torGraded R S T n) := Algebra.toModule
  obtain ⟨𝒟, h𝒟, hGraded, hStrictD, γD, hκgrade, hκone, hκmul, hκdpow⟩ := hrest
  refine ⟨𝒟, h𝒟, hGraded, hStrictD, γD, fun σ φ hφ Res => ?_⟩
  obtain ⟨hStrict, hDGA, γB, hcompat, hγB, hind⟩ :=
    exists_dividedPowerStructure_homology_baseChange (P := MvPolynomial T R) Res.grade
      Res.gamma Res.differential Res.exact_positive (tautologicalPresentation R T)
      (surjective_tautologicalPresentation R T)
  refine ⟨hStrict, γB, hcompat, hγB, ?_⟩
  let := hStrict
  let := hStrict₀
  obtain ⟨g, hg, hd, hgγ, haug⟩ := Res₀.exists_resolutionMap Res
  obtain ⟨_, _, _, _, _, _, _, _, hone, hmul, hdp⟩ := hind
  have hgx : ∀ x : T ⊗[R] Res.A,
      (LinearMap.baseChange T Res.differential).restrictScalars R x = 0 →
        (LinearMap.baseChange T Res₀.differential).restrictScalars R (lTensorAlgHom g x) = 0 :=
    fun x hx => by rw [← Res₀.lTensorAlgHom_differential Res T g hd, hx, map_zero]
  have hκ : ∀ (x : T ⊗[R] Res.A)
      (hx : (LinearMap.baseChange T Res.differential).restrictScalars R x = 0),
      directSumClass (torDirectSumEquivHomology Res T hφ) ⟨x, hx⟩ =
        directSumClass (torDirectSumEquivHomology Res₀ T hφ₀) ⟨lTensorAlgHom g x, hgx x hx⟩ :=
    fun x hx => (Res₀.directSumClass_lTensorAlgHom Res T g hg hd haug hφ₀ hφ x hx
      (hgx x hx)).symm
  refine ⟨surjective_directSumClass (torDirectSumEquivHomology Res T hφ), ?_, ?_, ?_, ?_⟩
  · intro n x h hx
    have hmem := hκgrade n (lTensorAlgHom g x) (hgx x h)
      (Res₀.lTensorAlgHom_mem_grade Res T g hg n hx)
    rwa [← hκ x h] at hmem
  · obtain ⟨h1, -⟩ := hone
    obtain ⟨h10, h10'⟩ := hκone
    refine ⟨h1, ?_⟩
    have h1eq : (⟨lTensorAlgHom g 1, hgx 1 h1⟩ :
        cycles ((LinearMap.baseChange T Res₀.differential).restrictScalars R)) = ⟨1, h10⟩ :=
      Subtype.ext (map_one _)
    exact (hκ 1 h1).trans ((congrArg
      (fun c => directSumClass (torDirectSumEquivHomology Res₀ T hφ₀) c) h1eq).trans h10')
  · intro x y hx hy
    obtain ⟨hxy, -⟩ := hmul hx hy
    obtain ⟨hxy₀, hm⟩ := hκmul (hgx x hx) (hgx y hy)
    refine ⟨hxy, ?_⟩
    have hxyeq : (⟨lTensorAlgHom g (x * y), hgx (x * y) hxy⟩ :
        cycles ((LinearMap.baseChange T Res₀.differential).restrictScalars R)) =
          ⟨lTensorAlgHom g x * lTensorAlgHom g y, hxy₀⟩ :=
      Subtype.ext (map_mul _ _ _)
    exact (hκ (x * y) hxy).trans ((congrArg
      (fun c => directSumClass (torDirectSumEquivHomology Res₀ T hφ₀) c) hxyeq).trans
        (hm.trans (congrArg₂ (· * ·) (hκ x hx).symm (hκ y hy).symm)))
  · intro n x hx hdx
    obtain ⟨hγ, -⟩ := hdp (n := n) hx hdx
    refine ⟨hγ, ?_⟩
    have hx₀ := lTensorAlgHom_mem_positiveEvenPart Res.grade Res₀.grade g hg hx
    obtain ⟨hγ₀, hd₀⟩ := hκdpow (n := n) hx₀ (hgx x hdx)
    have hγeq : (⟨lTensorAlgHom g (γB.dpow n x), hgx (γB.dpow n x) hγ⟩ :
        cycles ((LinearMap.baseChange T Res₀.differential).restrictScalars R)) =
          ⟨γB₀.dpow n (lTensorAlgHom g x), hγ₀⟩ :=
      Subtype.ext (lTensorAlgHom_dpow Res.grade Res₀.grade Res.gamma Res₀.gamma g hg hgγ
        γB γB₀ hγB hγB₀ n hx)
    exact (congrArg (fun c => γD.dpow n c) (hκ x hdx)).trans (hd₀.trans ((congrArg
      (fun c => directSumClass (torDirectSumEquivHomology Res₀ T hφ₀) c) hγeq).symm.trans
        (hκ (γB.dpow n x) hγ).symm))

end TorAlgebra

end DividedPowers.TateResolution

end
