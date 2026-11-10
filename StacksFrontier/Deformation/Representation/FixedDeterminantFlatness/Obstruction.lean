module

public import StacksFrontier.Deformation.Representation.FixedDeterminantFlatness.ObstructionLift
public import StacksFrontier.Deformation.Representation.FixedDeterminantFlatness.TangentBound
public import StacksFrontier.RingTheory.Rig.AdicBasic

/-!
# The obstruction classes of a fixed-determinant universal deformation ring

Let `R` be the universal deformation ring of `ρ₀ : π → GLₙ(𝐅_ℓ)` with determinant `δ`, let
`F : P → R` be a surjection from a complete Noetherian local `ℤ_[ℓ]`-algebra `P` whose kernel `J`
lies in `𝔪_P² + ℓP`, and let `f₁, …, f_r` be a minimal generating family of `J`. Lifting the
universal representation to `ρ̃ : π → GLₙ(P)` with determinant `δ`, the matrices
`ρ̃(g) ρ̃(h) ρ̃(gh)⁻¹ - 1` have entries in `J`, and their images under the coefficient functionals
`φ_a` are locally constant `2`-cocycles `ob_a : π × π → ad⁰ ρ₀`, linear in `a ∈ 𝐅_ℓ^r`.

**Mazur's bound.** If `ob_a` is a coboundary then `a = 0`. Indeed `ob_a = d x` lets one correct
the image of `ρ̃` in `S = P/I_a`, `I_a = ker (φ_a|_J)`, to a deformation `(1 - εx) ρ̃` of `ρ₀`
with determinant `δ`; its classifying map `ψ : R → S` is a section of `S → R`, and since
`J ⊆ 𝔪_P² + ℓP` the generator `ε` of `J/I_a ≅ 𝐅_ℓ` lies in `ψ(R) ∩ ker(S → R) = 0`, so
`φ_a = 0`.

## Main results

* `Deformation.IsUniversalFixedDeterminantDeformation.exists_obstruction_cocycles`.
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.GroupCohomology groupCohomology

universe u v

/-! ### Continuity for the adic topology from local constancy modulo powers -/

/-- A function to `S` is continuous for the `I`-adic topology if its reductions modulo every power
`I ^ k` are locally constant. -/
lemma continuous_adic_of_forall_isLocallyConstant {X S : Type*} [TopologicalSpace X]
    [CommRing S] (I : Ideal S) (f : X → S)
    (hf : ∀ k, IsLocallyConstant fun x => Ideal.Quotient.mk (I ^ k) (f x)) :
    @Continuous X S _ I.adicTopology f := by
  let : TopologicalSpace S := I.adicTopology
  have : IsTopologicalRing S := I.ringFilterBasis.isTopologicalRing
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, (I.hasBasis_nhds_adic (f x₀)).tendsto_right_iff]
  intro k _
  filter_upwards [(hf k).isOpen_fiber _ |>.mem_nhds (Set.mem_ofPred_eq ▸ rfl :
    x₀ ∈ (fun x => Ideal.Quotient.mk (I ^ k) (f x)) ⁻¹' {Ideal.Quotient.mk (I ^ k) (f x₀)})]
    with x hx
  simp only [Ideal.Quotient.eq] at hx
  exact ⟨f x - f x₀, hx, by simp⟩

/-- A function to `GLₙ(S)`, where `S` carries the `I`-adic topology, is continuous if its
reductions modulo every power `I ^ k` are locally constant. -/
lemma Matrix.GeneralLinearGroup.continuous_adic_of_forall_isLocallyConstant {X S : Type*}
    [TopologicalSpace X] [CommRing S] {n : ℕ} (I : Ideal S) [tS : TopologicalSpace S]
    (htS : tS = I.adicTopology) (f : X → Matrix.GeneralLinearGroup (Fin n) S)
    (hf : ∀ k, IsLocallyConstant fun x =>
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ k)) (f x)) : Continuous f := by
  subst htS
  let : TopologicalSpace S := I.adicTopology
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    refine _root_.continuous_adic_of_forall_isLocallyConstant I
      (fun x => ((f x : Matrix (Fin n) (Fin n) S)) i j) fun k => ?_
    exact (hf k).comp fun A : Matrix.GeneralLinearGroup (Fin n) (S ⧸ I ^ k) =>
      (A : Matrix (Fin n) (Fin n) (S ⧸ I ^ k)) i j
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    refine _root_.continuous_adic_of_forall_isLocallyConstant I
      (fun x => (((f x)⁻¹ : Matrix.GeneralLinearGroup _ _) : Matrix (Fin n) (Fin n) S) i j)
      fun k => ?_
    have e : (fun x => Ideal.Quotient.mk (I ^ k)
        ((((f x)⁻¹ : Matrix.GeneralLinearGroup _ _) : Matrix (Fin n) (Fin n) S) i j)) =
        (fun A : Matrix.GeneralLinearGroup (Fin n) (S ⧸ I ^ k) =>
          ((A⁻¹ : Matrix.GeneralLinearGroup _ _) : Matrix (Fin n) (Fin n) (S ⧸ I ^ k)) i j) ∘
          fun x => Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ k)) (f x) := by
      funext x
      simp only [Function.comp_apply, ← map_inv]
      rfl
    rw [e]
    exact (hf k).comp fun A : Matrix.GeneralLinearGroup (Fin n) (S ⧸ I ^ k) =>
      ((A⁻¹ : Matrix.GeneralLinearGroup _ _) : Matrix (Fin n) (Fin n) (S ⧸ I ^ k)) i j

/-- A function that is determined by a locally constant function is locally constant. -/
lemma IsLocallyConstant.of_determined {X A B : Type*} [TopologicalSpace X] {T : X → A}
    (hT : IsLocallyConstant T) (f : X → B) (hf : ∀ x x', T x = T x' → f x = f x') :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x₀
  exact ⟨T ⁻¹' {T x₀}, hT.isOpen_fiber _, rfl, fun x hx => hf x x₀ hx⟩

/-! ### Two pieces of commutative algebra -/

/-- `det (1 + X) ≡ 1 + tr X` modulo `I²` for a matrix with entries in `I`. -/
lemma Matrix.det_one_add_sub_mem_sq {P : Type*} [CommRing P] {n : ℕ} (I : Ideal P)
    (X : Matrix (Fin n) (Fin n) P) (hX : ∀ i j, X i j ∈ I) :
    (1 + X).det - (1 + X.trace) ∈ I ^ 2 := by
  set mk := Ideal.Quotient.mk (I ^ 2)
  set I' : Ideal (P ⧸ I ^ 2) := I.map mk
  have hI' : ∀ x ∈ I', ∀ y ∈ I', x * y = 0 := by
    intro x hx y hy
    have : x * y ∈ I' * I' := Ideal.mul_mem_mul hx hy
    rwa [← Ideal.map_mul, ← pow_two, Ideal.map_quotient_self, Ideal.mem_bot] at this
  have h1 := Matrix.det_one_add_of_mul_eq_zero I' hI' (X.map mk)
    (fun i j => Ideal.mem_map_of_mem mk (hX i j))
  have htr : mk X.trace = (X.map mk).trace := by
    simp [Matrix.trace, map_sum]
  have hmap : mk.mapMatrix (1 + X) = 1 + X.map mk := by
    rw [map_add, map_one]
    rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, hmap, h1, map_add, map_one,
    htr, sub_self]

/-- **A section of `P/I → R` forces `ker F ⊆ I`.** Let `t ∈ 𝔪_P` with `ker F ⊆ 𝔪_P² + tP`, and
let `𝔪_P ker F ⊆ I ⊆ ker F`. If `ψ : R → P/I` is a section of `P/I → R` sending `F(𝔪_P)` into the
image of `𝔪_P` and `F t` to the class of `t`, then `ker F ⊆ I`. -/
lemma ker_le_of_section {P R : Type*} [CommRing P] [IsLocalRing P] [CommRing R]
    (F : P →+* R) (I : Ideal P) (hIJ : I ≤ RingHom.ker F)
    (hmJ : maximalIdeal P * RingHom.ker F ≤ I) (t : P) (ht : t ∈ maximalIdeal P)
    (hJ : RingHom.ker F ≤ maximalIdeal P ^ 2 ⊔ Ideal.span {t})
    (ψ : R →+* P ⧸ I) (hψ : (Ideal.Quotient.lift I F hIJ).comp ψ = RingHom.id R)
    (hψm : ∀ y : P, y ∈ maximalIdeal P → ∃ z ∈ maximalIdeal P, ψ (F y) = Ideal.Quotient.mk I z)
    (hψt : ψ (F t) = Ideal.Quotient.mk I t) : RingHom.ker F ≤ I := by
  set mk := Ideal.Quotient.mk I
  set p := Ideal.Quotient.lift I F hIJ
  have hΔ : ∀ y : P, ∃ w ∈ RingHom.ker F, mk y - ψ (F y) = mk w := by
    intro y
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (mk y - ψ (F y))
    refine ⟨w, ?_, hw.symm⟩
    rw [RingHom.mem_ker]
    have := congrArg p hw
    rw [map_sub] at this
    have e1 : p (mk w) = F w := Ideal.Quotient.lift_mk _ _ _
    have e2 : p (mk y) = F y := Ideal.Quotient.lift_mk _ _ _
    rw [← e1, this, e2]
    have h2 : p (ψ (F y)) = F y := by
      simpa using congrArg (fun φ : R →+* R => φ (F y)) hψ
    rw [h2, sub_self]
  have hkill : ∀ z ∈ maximalIdeal P, ∀ w ∈ RingHom.ker F, mk z * mk w = 0 := by
    intro z hz w hw
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hmJ (Ideal.mul_mem_mul hz hw)
  have hΔmul : ∀ a b : P, mk (a * b) - ψ (F (a * b)) =
      mk a * (mk b - ψ (F b)) + (mk a - ψ (F a)) * ψ (F b) := fun a b => by
    rw [map_mul, map_mul, map_mul]
    ring
  have hsq : ∀ y ∈ maximalIdeal P ^ 2, mk y = ψ (F y) := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨wa, hwa, ea⟩ := hΔ a
      obtain ⟨wb, hwb, eb⟩ := hΔ b
      obtain ⟨zb, hzb, ezb⟩ := hψm b hb
      rw [← sub_eq_zero, hΔmul, eb, ea, ezb, hkill a ha wb hwb, mul_comm, hkill zb hzb wa hwa,
        add_zero]
    · rw [map_add, map_add, map_add, ha, hb]
  have hspan : ∀ y ∈ Ideal.span {t}, mk y = ψ (F y) := by
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨wc, hwc, ec⟩ := hΔ c
    rw [← sub_eq_zero, hΔmul, hψt, sub_self, mul_zero, zero_add, ec, mul_comm,
      hkill t ht wc hwc]
  intro j hj
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hJ hj)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, hsq y hy, hspan z hz, ← map_add, ← map_add,
    (RingHom.mem_ker).mp hj, map_zero]

namespace Deformation.IsUniversalFixedDeterminantDeformation

variable {ℓ n : ℕ} [Fact ℓ.Prime] {π : Type u} [Group π] [TopologicalSpace π]
  [IsTopologicalGroup π]
  {ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} {δ : π →ₜ* ℤ_[ℓ]ˣ}
  {R : Type v} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
  {reduce : R →+* ZMod ℓ} {ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R}

local notation "AD" => AdZero (ρ₀.toMonoidHom)

/-! ### The calculus of `J`-matrices and coefficient functionals -/

section Calculus

variable {P : Type*} [CommRing P] [IsLocalRing P] (res : P →+* ZMod ℓ)
  (hres : RingHom.ker res = maximalIdeal P) {r : ℕ} (f : Fin r → P)
  (hmin : ∀ p : Fin r → P, ∑ i, p i * f i = 0 → ∀ i, p i ∈ maximalIdeal P)

local notation "J" => Ideal.span (Set.range f)

include hres hmin in
/-- The coefficient functional `φ_a` is additive on finite sums of elements of `J`. -/
lemma coeffFunctional_sum (a : Fin r → ZMod ℓ) {ι : Type*} (s : Finset ι) (x : ι → P)
    (hx : ∀ i ∈ s, x i ∈ J) :
    IsLocalRing.coeffFunctional res f a (∑ i ∈ s, x i) =
      ∑ i ∈ s, IsLocalRing.coeffFunctional res f a (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsLocalRing.coeffFunctional_zero res hres f hmin]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      IsLocalRing.coeffFunctional_add res hres f hmin (hx j (Finset.mem_insert_self _ _))
        (Ideal.sum_mem _ fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

include hres hmin in
/-- For a matrix `X` with entries in `J`, applying `φ_a` entrywise gives
`φ_a(M X) = res(M) φ_a(X)`. -/
lemma map_coeffFunctional_mul_left (a : Fin r → ZMod ℓ) (M X : Matrix (Fin n) (Fin n) P)
    (hX : ∀ i j, X i j ∈ J) :
    (M * X).map (IsLocalRing.coeffFunctional res f a) =
      M.map res * X.map (IsLocalRing.coeffFunctional res f a) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [coeffFunctional_sum res hres f hmin a _ _ fun k _ => Ideal.mul_mem_left _ _ (hX k j)]
  exact Finset.sum_congr rfl fun k _ => IsLocalRing.coeffFunctional_mul res hres f hmin _ (hX k j) a

include hres hmin in
/-- For a matrix `X` with entries in `J`, applying `φ_a` entrywise gives
`φ_a(X M) = φ_a(X) res(M)`. -/
lemma map_coeffFunctional_mul_right (a : Fin r → ZMod ℓ) (X M : Matrix (Fin n) (Fin n) P)
    (hX : ∀ i j, X i j ∈ J) :
    (X * M).map (IsLocalRing.coeffFunctional res f a) =
      X.map (IsLocalRing.coeffFunctional res f a) * M.map res := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [coeffFunctional_sum res hres f hmin a _ _ fun k _ => Ideal.mul_mem_right _ _ (hX i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, IsLocalRing.coeffFunctional_mul res hres f hmin _ (hX i k) a, mul_comm]

include hres hmin in
/-- Applied entrywise, `φ_a` is additive on matrices with entries in `J`. -/
lemma map_coeffFunctional_add (a : Fin r → ZMod ℓ) (X Y : Matrix (Fin n) (Fin n) P)
    (hX : ∀ i j, X i j ∈ J) (hY : ∀ i j, Y i j ∈ J) :
    (X + Y).map (IsLocalRing.coeffFunctional res f a) =
      X.map (IsLocalRing.coeffFunctional res f a) +
        Y.map (IsLocalRing.coeffFunctional res f a) := by
  ext i j
  exact IsLocalRing.coeffFunctional_add res hres f hmin (hX i j) (hY i j) a

include hres hmin in
/-- If `J ⊆ 𝔪_P`, then `φ_a`, applied entrywise, vanishes on the product of two matrices with
entries in `J`. -/
lemma map_coeffFunctional_mul_eq_zero (a : Fin r → ZMod ℓ) (hJm : J ≤ maximalIdeal P)
    (X Y : Matrix (Fin n) (Fin n) P) (hX : ∀ i j, X i j ∈ J) (hY : ∀ i j, Y i j ∈ J) :
    (X * Y).map (IsLocalRing.coeffFunctional res f a) = 0 := by
  rw [map_coeffFunctional_mul_left res hres f hmin a X Y hY]
  have : X.map res = 0 := by
    ext i j
    have := hJm (hX i j)
    rw [← hres] at this
    exact this
  rw [this, Matrix.zero_mul]

include hres hmin in
/-- The kernel of the coefficient functional `φ_a` on `J`. -/
private def coeffKer (a : Fin r → ZMod ℓ) : Ideal P where
  carrier := {y | y ∈ J ∧ IsLocalRing.coeffFunctional res f a y = 0}
  add_mem' {y z} hy hz := ⟨Ideal.add_mem _ hy.1 hz.1, by
    rw [IsLocalRing.coeffFunctional_add res hres f hmin hy.1 hz.1, hy.2, hz.2, add_zero]⟩
  zero_mem' := ⟨Ideal.zero_mem _, IsLocalRing.coeffFunctional_zero res hres f hmin a⟩
  smul_mem' c y hy := ⟨Ideal.mul_mem_left _ c hy.1, by
    rw [smul_eq_mul, IsLocalRing.coeffFunctional_mul res hres f hmin c hy.1, hy.2, mul_zero]⟩

/-- `𝔪_P J` lies in the kernel of `φ_a` on `J`. -/
private lemma mul_le_coeffKer (a : Fin r → ZMod ℓ) :
    maximalIdeal P * J ≤ coeffKer res hres f hmin a := fun _ hy =>
  ⟨(Submodule.mul_le.mpr fun q _ _ hj => Ideal.mul_mem_left _ q hj) hy,
    IsLocalRing.coeffFunctional_eq_zero_of_mem res hres f hmin a hy⟩

/-- If `φ_a e = 1` and `res c = φ_a j`, then `j - c e` lies in the kernel of `φ_a` on `J`. -/
private lemma sub_mul_mem_coeffKer (a : Fin r → ZMod ℓ) {e : P} (he : e ∈ J)
    (hφe : IsLocalRing.coeffFunctional res f a e = 1) {j : P} (hj : j ∈ J) {c : P}
    (hc : res c = IsLocalRing.coeffFunctional res f a j) :
    j - c * e ∈ coeffKer res hres f hmin a := by
  refine ⟨Ideal.sub_mem _ hj (Ideal.mul_mem_left _ _ he), ?_⟩
  rw [sub_eq_add_neg, ← neg_mul, IsLocalRing.coeffFunctional_add res hres f hmin hj
    (Ideal.mul_mem_left _ _ he), IsLocalRing.coeffFunctional_mul res hres f hmin _ he, hφe,
    mul_one, map_neg, hc, add_neg_cancel]

end Calculus

/-! ### The setting -/

section Setting

variable (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
  (hred : ∀ g, Matrix.GeneralLinearGroup.map reduce (ρuniv g) = ρ₀ g)
  {P : Type} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
  [IsAdicComplete (maximalIdeal P) P] [Algebra ℤ_[ℓ] P]
  (F : P →+* R) (hF : Function.Surjective F)
  (hFalg : ∀ c, F (algebraMap ℤ_[ℓ] P c) = algebraMap ℤ_[ℓ] R c)

include h hF in
omit [IsTopologicalGroup π] [IsNoetherianRing P] [IsAdicComplete (maximalIdeal P) P]
    [Algebra ℤ_[ℓ] P] in
/-- The kernel of `reduce ∘ F : P → 𝐅_ℓ` is the maximal ideal of `P`. -/
lemma ker_reduce_comp : RingHom.ker (reduce.comp F) = maximalIdeal P := by
  rw [← RingHom.comap_ker, h.ker_reduce]
  exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective F hF)

include h hF in
omit [IsTopologicalGroup π] [IsNoetherianRing P] [IsAdicComplete (maximalIdeal P) P]
    [Algebra ℤ_[ℓ] P] in
/-- The kernel of `F` is contained in the maximal ideal of `P`. -/
lemma ker_le_maximalIdeal : RingHom.ker F ≤ maximalIdeal P := by
  rw [← ker_reduce_comp h F hF, ← RingHom.comap_ker]
  exact Ideal.comap_mono bot_le

/-- The `2`-cochain `(g, h) ↦ ρ̃(g) ρ̃(h) ρ̃(gh)⁻¹ - 1` of a lift `ρ̃`. -/
def liftDefect (ρt : π → Matrix.GeneralLinearGroup (Fin n) P) (g h : π) :
    Matrix (Fin n) (Fin n) P :=
  ((ρt g * ρt h * (ρt (g * h))⁻¹ : Matrix.GeneralLinearGroup (Fin n) P) :
    Matrix (Fin n) (Fin n) P) - 1

omit [IsTopologicalGroup π] [IsLocalRing R] [IsLocalRing P] [IsNoetherianRing P]
    [IsAdicComplete (maximalIdeal P) P] in
/-- If `ρ̃` lifts `ρuniv` along `F`, every entry of `liftDefect ρ̃ g h` lies in `ker F`. -/
lemma liftDefect_mem {ρt : π → Matrix.GeneralLinearGroup (Fin n) P}
    (hρt : ∀ g, Matrix.GeneralLinearGroup.map F (ρt g) = ρuniv g) (g h : π) (i j : Fin n) :
    liftDefect ρt g h i j ∈ RingHom.ker F := by
  have e : Matrix.GeneralLinearGroup.map F (ρt g * ρt h * (ρt (g * h))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hρt, hρt, hρt, map_mul, mul_inv_cancel]
  have := congrArg (fun A : Matrix.GeneralLinearGroup (Fin n) R =>
    (A : Matrix (Fin n) (Fin n) R) i j) e
  rw [RingHom.mem_ker, liftDefect, Matrix.sub_apply, map_sub]
  change ((Matrix.GeneralLinearGroup.map F (ρt g * ρt h * (ρt (g * h))⁻¹) :
    Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i j -
      F ((1 : Matrix _ _ P) i j) = 0
  rw [this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end Setting


omit [IsTopologicalGroup π] in
/-- The reduction of the universal representation modulo `𝔪_R ^ N` is locally constant. -/
lemma isLocallyConstant_map_mk_pow
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) (N : ℕ) :
    IsLocallyConstant fun g =>
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal R ^ N)) (ρuniv g) := by
  have : IsTopologicalRing R := h.isTopologicalRing
  let : TopologicalSpace (R ⧸ maximalIdeal R ^ N) := ⊥
  have : DiscreteTopology (R ⧸ maximalIdeal R ^ N) := ⟨rfl⟩
  refine (IsLocallyConstant.iff_continuous _).mpr
    ((Matrix.GeneralLinearGroup.continuous_map _ ?_).comp ρuniv.continuous)
  rw [h.isAdicTopology]
  exact RingHom.continuous_adic_of_pow_le_ker (maximalIdeal R)
    (Ideal.Quotient.mk (maximalIdeal R ^ N)) N (by rw [Ideal.mk_ker])

section Cocycles

variable (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
  (hred : ∀ g, Matrix.GeneralLinearGroup.map reduce (ρuniv g) = ρ₀ g)
  {P : Type} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
  [IsAdicComplete (maximalIdeal P) P] [Algebra ℤ_[ℓ] P]
  (F : P →+* R) (hF : Function.Surjective F)
  {r : ℕ} (f : Fin r → P) (hf : Ideal.span (Set.range f) = RingHom.ker F)
  (hmin : ∀ p : Fin r → P, ∑ i, p i * f i = 0 → ∀ i, p i ∈ maximalIdeal P)
  (ρt : π → Matrix.GeneralLinearGroup (Fin n) P)
  (hρtF : ∀ g, Matrix.GeneralLinearGroup.map F (ρt g) = ρuniv g)
  (hρtdet : ∀ g, Matrix.GeneralLinearGroup.det (ρt g) = Units.map (algebraMap ℤ_[ℓ] P) (δ g))

include hred hρtF in
omit [IsTopologicalGroup π] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLocalRing P] [IsNoetherianRing P]
    [IsAdicComplete (maximalIdeal P) P] [Algebra ℤ_[ℓ] P] in
/-- The reduction of `ρ̃(g)` along `reduce ∘ F` is `ρ₀(g)`. -/
lemma map_res_lift (g : π) :
    ((ρt g : Matrix (Fin n) (Fin n) P)).map (reduce.comp F) = ρ₀ g := by
  simpa [Matrix.map_map] using congrArg (fun A : Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ) =>
    (A : Matrix (Fin n) (Fin n) (ZMod ℓ))) ((congrArg (Matrix.GeneralLinearGroup.map reduce)
      (hρtF g)).trans (hred g))

include hred hρtF in
omit [IsTopologicalGroup π] [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsLocalRing P] [IsNoetherianRing P]
    [IsAdicComplete (maximalIdeal P) P] [Algebra ℤ_[ℓ] P] in
/-- The reduction of `ρ̃(g)⁻¹` along `reduce ∘ F` is `ρ₀(g)⁻¹`. -/
lemma map_res_lift_inv (g : π) :
    (((ρt g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) P) : Matrix (Fin n) (Fin n) P).map
      (reduce.comp F) = ((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) := by
  have e1 : Matrix.GeneralLinearGroup.map (reduce.comp F) (ρt g) = ρ₀ g :=
    Units.ext (map_res_lift hred F ρt hρtF g)
  have e2 : Matrix.GeneralLinearGroup.map (reduce.comp F) (ρt g)⁻¹ = (ρ₀ g)⁻¹ := by
    rw [map_inv, e1]
  exact congrArg Units.val e2

/-- The obstruction cocycle attached to the coefficient functional `φ_a`. -/
def obstruction (a : Fin r → ZMod ℓ) (htr : ∀ g h, ((liftDefect ρt g h).map
    (IsLocalRing.coeffFunctional (reduce.comp F) f a)).trace = 0) (p : π × π) : AD :=
  AdZero.mk ((liftDefect ρt p.1 p.2).map (IsLocalRing.coeffFunctional (reduce.comp F) f a))
    (htr p.1 p.2)

include h hF hf hmin hρtF hρtdet in
omit [IsTopologicalGroup π] [IsNoetherianRing P] [IsAdicComplete (maximalIdeal P) P] in
/-- If the lift `ρ̃` has determinant `δ`, then the image of `liftDefect ρ̃ g h` under `φ_a` has
trace zero. -/
lemma trace_liftDefect (a : Fin r → ZMod ℓ) (g h' : π) :
    ((liftDefect ρt g h').map (IsLocalRing.coeffFunctional (reduce.comp F) f a)).trace = 0 := by
  have hres := ker_reduce_comp h F hF
  have hJm := ker_le_maximalIdeal h F hF
  have hD : ∀ i j, liftDefect ρt g h' i j ∈ Ideal.span (Set.range f) := fun i j =>
    hf ▸ liftDefect_mem F hρtF g h' i j
  have hdet1 : (1 + liftDefect ρt g h').det = 1 := by
    rw [liftDefect, add_sub_cancel, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul,
      map_inv, hρtdet, hρtdet, hρtdet, ← map_mul, ← map_mul, ← map_inv, ← map_mul, map_mul δ,
      mul_inv_cancel, map_one, Units.val_one]
  have hmem := Matrix.det_one_add_sub_mem_sq (Ideal.span (Set.range f)) _ hD
  rw [hdet1, sub_add_eq_sub_sub, sub_self, zero_sub, neg_mem_iff] at hmem
  have hsq : Ideal.span (Set.range f) ^ 2 ≤ maximalIdeal P * Ideal.span (Set.range f) := by
    rw [pow_two]
    exact Ideal.mul_mono_left (hf ▸ hJm)
  have h0 := IsLocalRing.coeffFunctional_eq_zero_of_mem (reduce.comp F) hres f hmin a (hsq hmem)
  rw [← h0, Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.map_apply]
  rw [coeffFunctional_sum (reduce.comp F) hres f hmin a _ _ fun i _ => hD i i]


/-- If every entry of `X` lies in `J`, so does every entry of `M * X`. -/
lemma mul_mem_of_right {P : Type*} [CommRing P] (J : Ideal P) (M X : Matrix (Fin n) (Fin n) P)
    (hX : ∀ i j, X i j ∈ J) (i j : Fin n) : (M * X) i j ∈ J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hX k j)

/-- If every entry of `X` lies in `J`, so does every entry of `X * M`. -/
lemma mul_mem_of_left {P : Type*} [CommRing P] (J : Ideal P) (X M : Matrix (Fin n) (Fin n) P)
    (hX : ∀ i j, X i j ∈ J) (i j : Fin n) : (X * M) i j ∈ J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hX i k)

omit [TopologicalSpace π] [IsTopologicalGroup π] in
/-- The defect identity `D(g,h) + D(gh,k) + D(g,h) D(gh,k) = X + D(g,hk) + X D(g,hk)`, where
`D = liftDefect ρ̃` and `X = ρ̃(g) D(h,k) ρ̃(g)⁻¹`. -/
private lemma liftDefect_add_mul {P : Type} [CommRing P]
    (ρt : π → Matrix.GeneralLinearGroup (Fin n) P) (g h k : π) :
    liftDefect ρt g h + liftDefect ρt (g * h) k + liftDefect ρt g h * liftDefect ρt (g * h) k =
      (ρt g : Matrix (Fin n) (Fin n) P) * liftDefect ρt h k *
          (((ρt g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) P) : Matrix (Fin n) (Fin n) P) +
        liftDefect ρt g (h * k) +
        (ρt g : Matrix (Fin n) (Fin n) P) * liftDefect ρt h k *
          (((ρt g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) P) : Matrix (Fin n) (Fin n) P) *
          liftDefect ρt g (h * k) := by
  set A : Matrix (Fin n) (Fin n) P := Units.val (ρt g)
  set Ai : Matrix (Fin n) (Fin n) P := Units.val (ρt g)⁻¹
  set D1 := liftDefect ρt g h
  set D2 := liftDefect ρt (g * h) k
  set D3 := liftDefect ρt h k
  set D4 := liftDefect ρt g (h * k)
  have hAAi : A * Ai = 1 := Units.mul_inv _
  have hGL : (1 + D1) * (1 + D2) = A * (1 + D3) * Ai * (1 + D4) := by
    simp only [D1, D2, D3, D4, liftDefect, add_sub_cancel, A, Ai, ← Units.val_mul]
    congr 1
    rw [mul_assoc g h k]
    group
  have hGL' : (1 + D1) * (1 + D2) = (1 + A * D3 * Ai) * (1 + D4) := by
    rw [hGL]
    congr 1
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hAAi]
  calc D1 + D2 + D1 * D2 = (1 + D1) * (1 + D2) - 1 := by noncomm_ring
    _ = (1 + A * D3 * Ai) * (1 + D4) - 1 := by rw [hGL']
    _ = A * D3 * Ai + D4 + A * D3 * Ai * D4 := by noncomm_ring

include h hred hF hf hmin hρtF hρtdet in
omit [IsTopologicalGroup π] [IsNoetherianRing P] [IsAdicComplete (maximalIdeal P) P] in
/-- **The obstruction cochain is a `2`-cocycle.** -/
lemma isCocycle₂_obstruction (a : Fin r → ZMod ℓ) :
    IsCocycle₂ (obstruction (ρ₀ := ρ₀) F f ρt a
      (trace_liftDefect h F hF f hf hmin ρt hρtF hρtdet a)) := by
  have hres := ker_reduce_comp h F hF
  have hJm : Ideal.span (Set.range f) ≤ maximalIdeal P := hf ▸ ker_le_maximalIdeal h F hF
  set φ := IsLocalRing.coeffFunctional (reduce.comp F) f a
  have hD : ∀ g h' i j, liftDefect ρt g h' i j ∈ Ideal.span (Set.range f) := fun g h' i j =>
    hf ▸ liftDefect_mem F hρtF g h' i j
  intro g h₁ k
  apply AdZero.ext
  simp only [obstruction, AdZero.val_add, AdZero.val_mk, AdZero.val_smul_group]
  set A : Matrix (Fin n) (Fin n) P := Units.val (ρt g)
  set Ai : Matrix (Fin n) (Fin n) P := Units.val (ρt g)⁻¹
  set D1 := liftDefect ρt g h₁
  set D2 := liftDefect ρt (g * h₁) k
  set D3 := liftDefect ρt h₁ k
  set D4 := liftDefect ρt g (h₁ * k)
  have key : D1 + D2 + D1 * D2 = A * D3 * Ai + D4 + A * D3 * Ai * D4 :=
    liftDefect_add_mul ρt g h₁ k
  have hD1 : ∀ i j, D1 i j ∈ Ideal.span (Set.range f) := hD _ _
  have hD2 : ∀ i j, D2 i j ∈ Ideal.span (Set.range f) := hD _ _
  have hD3 : ∀ i j, D3 i j ∈ Ideal.span (Set.range f) := hD _ _
  have hD4 : ∀ i j, D4 i j ∈ Ideal.span (Set.range f) := hD _ _
  set X3 := A * D3 * Ai
  have hX3 : ∀ i j, X3 i j ∈ Ideal.span (Set.range f) :=
    mul_mem_of_left _ _ _ (mul_mem_of_right _ _ _ hD3)
  have hφ : ∀ A B : Matrix (Fin n) (Fin n) P, (∀ i j, A i j ∈ Ideal.span (Set.range f)) →
      (∀ i j, B i j ∈ Ideal.span (Set.range f)) → (A + B + A * B).map φ = A.map φ + B.map φ :=
    fun A B hA hB => by
    rw [map_coeffFunctional_add (reduce.comp F) hres f hmin a (A + B) (A * B)
        (fun i j => Ideal.add_mem _ (hA i j) (hB i j)) (mul_mem_of_left _ _ _ hA),
      map_coeffFunctional_add (reduce.comp F) hres f hmin a A B hA hB,
      map_coeffFunctional_mul_eq_zero (reduce.comp F) hres f hmin a hJm A B hA hB, add_zero]
  have h1 := congrArg (fun X => X.map φ) key
  rw [hφ D1 D2 hD1 hD2, hφ X3 D4 hX3 hD4] at h1
  have hX3φ : X3.map φ = ρ₀ g * D3.map φ * ((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _) := by
    simp only [X3]
    rw [map_coeffFunctional_mul_right (reduce.comp F) hres f hmin a (A * D3) Ai
      (mul_mem_of_right _ _ _ hD3),
      map_coeffFunctional_mul_left (reduce.comp F) hres f hmin a A D3 hD3,
      map_res_lift hred F ρt hρtF, map_res_lift_inv hred F ρt hρtF]
  rw [hX3φ] at h1
  rwa [add_comm (D2.map φ)]



include h hF hf hmin hρtF in
omit [IsNoetherianRing P] [IsAdicComplete (maximalIdeal P) P] [Algebra ℤ_[ℓ] P] in
/-- **The obstruction cochain is locally constant** when the lift is locally constant modulo an
ideal `Q` with `J ∩ Q ⊆ 𝔪 J`. -/
lemma isLocallyConstant_obstruction (a : Fin r → ZMod ℓ) (htr : ∀ g h,
    ((liftDefect ρt g h).map (IsLocalRing.coeffFunctional (reduce.comp F) f a)).trace = 0)
    (Q : Ideal P)
    (hρtlc : IsLocallyConstant fun g =>
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q) (ρt g))
    (hJQ : ∀ x ∈ RingHom.ker F, x ∈ Q → x ∈ maximalIdeal P * RingHom.ker F) :
    IsLocallyConstant (obstruction (ρ₀ := ρ₀) F f ρt a htr) := by
  have hres := ker_reduce_comp h F hF
  have hT : IsLocallyConstant fun p : π × π =>
      (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q) (ρt p.1),
        Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q) (ρt p.2),
        Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q) (ρt (p.1 * p.2))) :=
    (hρtlc.comp_continuous continuous_fst).prodMk
      ((hρtlc.comp_continuous continuous_snd).prodMk
        (hρtlc.comp_continuous (continuous_fst.mul continuous_snd)))
  refine hT.of_determined (obstruction (ρ₀ := ρ₀) F f ρt a htr) fun p p' hpp' => ?_
  simp only [Prod.mk.injEq] at hpp'
  obtain ⟨e1, e2, e3⟩ := hpp'
  apply AdZero.ext
  ext i j
  simp only [obstruction, AdZero.val_mk, Matrix.map_apply]
  have hGQ : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q)
      (ρt p.1 * ρt p.2 * (ρt (p.1 * p.2))⁻¹) =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q)
      (ρt p'.1 * ρt p'.2 * (ρt (p'.1 * p'.2))⁻¹) := by
    simp only [map_mul, map_inv, e1, e2, e3]
  have hentry := congrArg (fun A : Matrix.GeneralLinearGroup (Fin n) (P ⧸ Q) =>
    (A : Matrix (Fin n) (Fin n) (P ⧸ Q)) i j) hGQ
  have hQ : liftDefect ρt p.1 p.2 i j - liftDefect ρt p'.1 p'.2 i j ∈ Q := by
    rw [← Ideal.Quotient.eq]
    simp only [liftDefect, Matrix.sub_apply, map_sub]
    exact congrArg (· - _) hentry
  have hJ1 := liftDefect_mem F hρtF p.1 p.2 i j
  have hJ2 := liftDefect_mem F hρtF p'.1 p'.2 i j
  have hmJ := hJQ _ (Ideal.sub_mem _ hJ1 hJ2) hQ
  rw [← hf] at hJ1 hJ2 hmJ
  have h0 := IsLocalRing.coeffFunctional_eq_zero_of_mem (reduce.comp F) hres f hmin a hmJ
  have hsplit : liftDefect ρt p.1 p.2 i j = liftDefect ρt p'.1 p'.2 i j +
      (liftDefect ρt p.1 p.2 i j - liftDefect ρt p'.1 p'.2 i j) := by ring
  rw [hsplit, IsLocalRing.coeffFunctional_add (reduce.comp F) hres f hmin hJ2
    (Ideal.sub_mem _ hJ1 hJ2), h0, add_zero]

omit [IsTopologicalGroup π] [IsLocalRing R] [TopologicalSpace R] [IsLocalRing P] [Algebra ℤ_[ℓ] R]
    [IsNoetherianRing P] [IsAdicComplete (maximalIdeal P) P] [Algebra ℤ_[ℓ] P] in
/-- **Linearity of the obstruction in `a`.** -/
lemma sum_smul_obstruction (a : Fin r → ZMod ℓ) (htr : ∀ b : Fin r → ZMod ℓ, ∀ g h,
    ((liftDefect ρt g h).map (IsLocalRing.coeffFunctional (reduce.comp F) f b)).trace = 0) :
    ∑ i, a i • obstruction (ρ₀ := ρ₀) F f ρt (Pi.single i 1) (htr _) =
      obstruction (ρ₀ := ρ₀) F f ρt a (htr a) := by
  classical
  funext p
  apply AdZero.ext
  ext i j
  simp only [Finset.sum_apply, Pi.smul_apply, AdZero.val_sum, AdZero.val_smul, obstruction,
    AdZero.val_mk, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [← IsLocalRing.coeffFunctional_sum_left (reduce.comp F) f a
    (fun k => (Pi.single k 1 : Fin r → ZMod ℓ)) (liftDefect ρt p.1 p.2 i j)]
  congr 1
  ext k
  simp [Finset.sum_apply, Pi.single_apply]


include h hF hρtF in
omit [IsTopologicalGroup π] [IsNoetherianRing P] [IsAdicComplete (maximalIdeal P) P]
    [Algebra ℤ_[ℓ] P] in
/-- If `ρ̃` is locally constant modulo `Q₀ ⊇ 𝔪_P ^ k₀` and `ker F ∩ Q₀ ⊆ 𝔪_P ker F ⊆ I`, then `ρ̃`
is locally constant modulo `I ⊔ 𝔪_P ^ K` for every `K`. -/
private lemma isLocallyConstant_map_mk_sup_pow (I Q₀ : Ideal P) (k₀ : ℕ)
    (hQ₀ : maximalIdeal P ^ k₀ ≤ Q₀)
    (hρtlc : IsLocallyConstant fun g =>
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q₀) (ρt g))
    (hJQ : ∀ y ∈ RingHom.ker F, y ∈ Q₀ → y ∈ maximalIdeal P * RingHom.ker F)
    (hmJI : maximalIdeal P * RingHom.ker F ≤ I) (K : ℕ) :
    IsLocallyConstant fun g =>
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ⊔ maximalIdeal P ^ K)) (ρt g) := by
  refine ((isLocallyConstant_map_mk_pow h (K + k₀)).prodMk hρtlc).of_determined _
    fun g g' hgg' => ?_
  simp only [Prod.mk.injEq] at hgg'
  obtain ⟨e1, e2⟩ := hgg'
  refine Units.ext (Matrix.ext fun i j => ?_)
  change Ideal.Quotient.mk _ ((ρt g : Matrix (Fin n) (Fin n) P) i j) =
    Ideal.Quotient.mk _ ((ρt g' : Matrix (Fin n) (Fin n) P) i j)
  rw [Ideal.Quotient.eq]
  set y := (ρt g : Matrix (Fin n) (Fin n) P) i j - (ρt g' : Matrix (Fin n) (Fin n) P) i j
  have hy1 : F y ∈ maximalIdeal R ^ (K + k₀) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, sub_eq_zero]
    have hF1 : ∀ g'', F ((ρt g'' : Matrix (Fin n) (Fin n) P) i j) =
        (ρuniv g'' : Matrix (Fin n) (Fin n) R) i j := fun g'' => by
      rw [← hρtF g'']
      rfl
    rw [hF1, hF1]
    exact congrArg (fun A : Matrix.GeneralLinearGroup (Fin n) _ =>
      (A : Matrix (Fin n) (Fin n) (R ⧸ maximalIdeal R ^ (K + k₀))) i j) e1
  have hy2 : y ∈ Q₀ := by
    rw [← Ideal.Quotient.eq]
    exact congrArg (fun A : Matrix.GeneralLinearGroup (Fin n) (P ⧸ Q₀) =>
      (A : Matrix (Fin n) (Fin n) (P ⧸ Q₀)) i j) e2
  have hmPk : (maximalIdeal P ^ (K + k₀)).map F = maximalIdeal R ^ (K + k₀) := by
    rw [Ideal.map_pow, map_maximalIdeal_of_surjective F hF]
  rw [← hmPk] at hy1
  obtain ⟨t, ht, htF⟩ := (Ideal.mem_map_iff_of_surjective F hF).mp hy1
  have hyt : y - t ∈ RingHom.ker F := by rw [RingHom.mem_ker, map_sub, htF, sub_self]
  have hyt2 : y - t ∈ Q₀ := Q₀.sub_mem hy2 (hQ₀ (Ideal.pow_le_pow_right (by omega) ht))
  rw [show y = (y - t) + t by ring]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (hmJI (hJQ _ hyt hyt2)))
    (Ideal.mem_sup_right (Ideal.pow_le_pow_right (by omega) ht))

include h hred hF hf hmin hρtF hρtdet in
omit [IsTopologicalGroup π] in
/-- **Mazur's bound: a coboundary obstruction forces `a = 0`.** -/
theorem eq_zero_of_obstruction_eq_dOne
    (hFalg : ∀ c, F (algebraMap ℤ_[ℓ] P c) = algebraMap ℤ_[ℓ] R c)
    (hJ : RingHom.ker F ≤ maximalIdeal P ^ 2 ⊔ Ideal.span {algebraMap ℤ_[ℓ] P ℓ})
    (Q₀ : Ideal P) (k₀ : ℕ) (hQ₀ : maximalIdeal P ^ k₀ ≤ Q₀)
    (hρtlc : IsLocallyConstant fun g =>
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q₀) (ρt g))
    (hJQ : ∀ y ∈ RingHom.ker F, y ∈ Q₀ → y ∈ maximalIdeal P * RingHom.ker F)
    (a : Fin r → ZMod ℓ) (x : π → AD) (hxl : IsLocallyConstant x)
    (hx : dOne x = obstruction (ρ₀ := ρ₀) F f ρt a
      (trace_liftDefect h F hF f hf hmin ρt hρtF hρtdet a)) : a = 0 := by
  classical
  by_contra ha
  obtain ⟨k', hk'⟩ := Function.ne_iff.mp ha
  set res := reduce.comp F with hresdef
  have hres : RingHom.ker res = maximalIdeal P := ker_reduce_comp h F hF
  have hJm : RingHom.ker F ≤ maximalIdeal P := ker_le_maximalIdeal h F hF
  set J := Ideal.span (Set.range f) with hJdef
  have hJF : J = RingHom.ker F := hf
  let liftZ : ZMod ℓ → ℤ_[ℓ] :=
    Function.surjInv (ZMod.ringHom_surjective (PadicInt.toZMod (p := ℓ)))
  let lift : ZMod ℓ → P := fun z => algebraMap ℤ_[ℓ] P (liftZ z)
  have hreslift : ∀ z, res (lift z) = z := fun z => by
    simp only [res, lift, RingHom.comp_apply, hFalg, h.reduce_algebraMap]
    exact Function.surjInv_eq _ z
  have hsubm : ∀ y : P, y - lift (res y) ∈ maximalIdeal P := fun y => by
    rw [← hres, RingHom.mem_ker, map_sub, hreslift, sub_self]
  set e : P := lift (a k')⁻¹ * f k'
  have heJ : e ∈ J := Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k', rfl⟩)
  have heF : e ∈ RingHom.ker F := hJF ▸ heJ
  have hφe : (IsLocalRing.coeffFunctional res f a) e = 1 := by
    rw [IsLocalRing.coeffFunctional_mul res hres f hmin _ (Ideal.subset_span ⟨k', rfl⟩),
      IsLocalRing.coeffFunctional_generator res hres f hmin, hreslift, inv_mul_cancel₀ hk']
  let I : Ideal P := coeffKer res hres f hmin a
  have hIJ : I ≤ RingHom.ker F := fun y hy => hJF ▸ hy.1
  have hmJI : maximalIdeal P * RingHom.ker F ≤ I := by
    rw [← hJF]
    exact mul_le_coeffKer res hres f hmin a
  have hdec : ∀ j ∈ J, j - lift ((IsLocalRing.coeffFunctional res f a) j) * e ∈ I := fun j hj =>
    sub_mul_mem_coeffKer res hres f hmin a heJ hφe hj (hreslift _)
  have hIne : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal P).ne_top
    (hIJ.trans hJm)
  set S := P ⧸ I
  set mkS : P →+* S := Ideal.Quotient.mk I
  have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing S := IsLocalRing.of_surjective' mkS Ideal.Quotient.mk_surjective
  have hmS : (maximalIdeal P).map mkS = maximalIdeal S :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hcS : IsAdicComplete (maximalIdeal S) S :=
    hmS ▸ Rig.isAdicComplete_quotient (maximalIdeal P) I
  let tS : TopologicalSpace S := (maximalIdeal S).adicTopology
  set ε : S := mkS e
  have hεm : ∀ y ∈ maximalIdeal P, ε * mkS y = 0 := fun y hy => by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, mul_comm]
    exact hmJI (Ideal.mul_mem_mul hy heF)
  have hεres : ∀ y : P, ε * mkS y = ε * mkS (lift (res y)) := fun y => by
    rw [← sub_eq_zero, ← mul_sub, ← map_sub]
    exact hεm _ (hsubm y)
  have hεε : ε * ε = 0 := hεm e (hJm heF)
  have hdec' : ∀ j ∈ J, mkS j = ε * mkS (lift ((IsLocalRing.coeffFunctional res f a) j)) :=
      fun j hj => by
    rw [mul_comm, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hdec j hj
  let E : Matrix (Fin n) (Fin n) (ZMod ℓ) → Matrix (Fin n) (Fin n) S :=
    fun X => Matrix.of fun i j => ε * mkS (lift (X i j))
  have hEapp : ∀ X i j, E X i j = ε * mkS (lift (X i j)) := fun _ _ _ => rfl
  have hmlift0 : ∀ z : ZMod ℓ, z = 0 → ε * mkS (lift z) = 0 := fun z hz =>
    hεm _ (by rw [← hres, RingHom.mem_ker, hreslift, hz])
  have hE_add : ∀ X Y, E (X + Y) = E X + E Y := fun X Y => by
    ext i j
    rw [Matrix.add_apply, hEapp, hEapp, hEapp, ← mul_add, ← map_add,
      hεres (lift (X i j) + lift (Y i j)), map_add, hreslift, hreslift, Matrix.add_apply]
  have hE_neg : ∀ X, E (-X) = -E X := map_neg (AddMonoidHom.mk' E hE_add)
  have hE_sub : ∀ X Y, E (X - Y) = E X - E Y := map_sub (AddMonoidHom.mk' E hE_add)
  have hEE : ∀ X Y, E X * E Y = 0 := fun X Y => by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hEapp, hEapp, mul_mul_mul_comm, hεε, zero_mul]
  have hME : ∀ (M : Matrix (Fin n) (Fin n) P) X, M.map mkS * E X = E (M.map res * X) := by
    intro M X
    ext i j
    rw [Matrix.mul_apply, hEapp, Matrix.mul_apply]
    have h1 : ∑ k, M.map mkS i k * E X k j = ε * mkS (∑ k, M i k * lift (X k j)) := by
      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hEapp, Matrix.map_apply, map_mul]; ring
    rw [h1, hεres, map_sum]
    simp only [map_mul, hreslift, Matrix.map_apply]
  have hEM : ∀ (M : Matrix (Fin n) (Fin n) P) X, E X * M.map mkS = E (X * M.map res) := by
    intro M X
    ext i j
    rw [Matrix.mul_apply, hEapp, Matrix.mul_apply]
    have h1 : ∑ k, E X i k * M.map mkS k j = ε * mkS (∑ k, lift (X i k) * M k j) := by
      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hEapp, Matrix.map_apply, map_mul]; ring
    rw [h1, hεres, map_sum]
    simp only [map_mul, hreslift, Matrix.map_apply]
  have hEJ : ∀ Y : Matrix (Fin n) (Fin n) P, (∀ i j, Y i j ∈ J) →
      Y.map mkS = E (Y.map (IsLocalRing.coeffFunctional res f a)) := fun Y hY => by
    ext i j
    rw [Matrix.map_apply, hEapp, Matrix.map_apply]
    exact hdec' _ (hY i j)
  have htrE : ∀ X : Matrix (Fin n) (Fin n) (ZMod ℓ), X.trace = 0 → (E X).trace = 0 := by
    intro X hX
    have : (E X).trace = ε * mkS (∑ i, lift (X i i)) := by
      rw [Matrix.trace, map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Matrix.diag_apply, hEapp]
    rw [this, hεres, map_sum]
    simp only [hreslift]
    exact hmlift0 _ hX
  have hdetE : ∀ X : Matrix (Fin n) (Fin n) (ZMod ℓ), X.trace = 0 → (1 + E X).det = 1 := by
    intro X hX
    have hK : ∀ y ∈ Ideal.span {ε}, ∀ z ∈ Ideal.span {ε}, y * z = 0 := by
      intro y hy z hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      rw [mul_mul_mul_comm, hεε, mul_zero]
    rw [Matrix.det_one_add_of_mul_eq_zero (Ideal.span {ε}) hK (E X) (fun i j => by
      rw [hEapp]; exact Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩), htrE X hX, add_zero]
  have hU1 : ∀ X, (1 - E X) * (1 + E X) = 1 := fun X => by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hEE, add_zero]
    abel
  have hU2 : ∀ X, (1 + E X) * (1 - E X) = 1 := fun X => mul_eq_one_comm.mp (hU1 X)
  let U : Matrix (Fin n) (Fin n) (ZMod ℓ) → Matrix.GeneralLinearGroup (Fin n) S := fun X =>
    ⟨1 - E X, 1 + E X, hU1 X, hU2 X⟩
  have hres_ρt : ∀ g, (ρt g : Matrix (Fin n) (Fin n) P).map res = ρ₀ g :=
    map_res_lift hred F ρt hρtF
  have hD : ∀ g h' i j, liftDefect ρt g h' i j ∈ J := fun g h' i j =>
    hJF ▸ liftDefect_mem F hρtF g h' i j
  have hprod : ∀ g h', (ρt g : Matrix (Fin n) (Fin n) P).map mkS *
      (ρt h' : Matrix (Fin n) (Fin n) P).map mkS =
      (1 + E (obstruction (ρ₀ := ρ₀) F f ρt a
        (trace_liftDefect h F hF f hf hmin ρt hρtF hρtdet a) (g, h')).val) *
        (ρt (g * h') : Matrix (Fin n) (Fin n) P).map mkS := by
    intro g h'
    have e1 : (ρt g : Matrix (Fin n) (Fin n) P) * ρt h' =
        (1 + liftDefect ρt g h') * ρt (g * h') := by
      rw [liftDefect, add_sub_cancel, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
    have e2 := congrArg mkS.mapMatrix e1
    simp only [map_mul, map_add, map_one] at e2
    change mkS.mapMatrix _ * mkS.mapMatrix _ = _
    have e3 : mkS.mapMatrix (liftDefect ρt g h') =
        E ((liftDefect ρt g h').map (IsLocalRing.coeffFunctional res f a)) := hEJ _ (hD g h')
    rw [e2, e3]
    rfl
  have hcoc : ∀ g h', (obstruction (ρ₀ := ρ₀) F f ρt a
      (trace_liftDefect h F hF f hf hmin ρt hρtF hρtdet a) (g, h')).val =
      (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * (x h').val *
        ((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _) - (x (g * h')).val + (x g).val := by
    intro g h'
    rw [← hx]
    simp only [dOne_apply, AdZero.val_add, AdZero.val_sub, AdZero.val_smul_group]
    rfl
  let ρfun : π → Matrix.GeneralLinearGroup (Fin n) S := fun g =>
    U (x g).val * Matrix.GeneralLinearGroup.map mkS (ρt g)
  have hmul : ∀ g h', ρfun (g * h') = ρfun g * ρfun h' := by
    intro g h'
    refine Units.ext ?_
    simp only [ρfun, Units.val_mul]
    change (1 - E (x (g * h')).val) * (ρt (g * h') : Matrix (Fin n) (Fin n) P).map mkS =
      (1 - E (x g).val) * (ρt g : Matrix (Fin n) (Fin n) P).map mkS *
        ((1 - E (x h').val) * (ρt h' : Matrix (Fin n) (Fin n) P).map mkS)
    have hW : (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * (x h').val *
        (ρt h' : Matrix (Fin n) (Fin n) P).map res =
        ((ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * (x h').val *
          ((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _)) *
          (ρt (g * h') : Matrix (Fin n) (Fin n) P).map res := by
      rw [hres_ρt, hres_ρt, map_mul, Units.val_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _) :
        Matrix (Fin n) (Fin n) (ZMod ℓ)), Units.inv_mul, Matrix.one_mul]
    have h1 : (ρt g : Matrix (Fin n) (Fin n) P).map mkS * E (x h').val *
        (ρt h' : Matrix (Fin n) (Fin n) P).map mkS =
        E ((ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * (x h').val *
          ((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _)) *
          (ρt (g * h') : Matrix (Fin n) (Fin n) P).map mkS := by
      rw [hME, hEM, hEM, hres_ρt, hW]
    have hO := hcoc g h'
    have key : (1 - E (x g).val) * (ρt g : Matrix (Fin n) (Fin n) P).map mkS *
        ((1 - E (x h').val) * (ρt h' : Matrix (Fin n) (Fin n) P).map mkS) =
        (1 - E (x g).val) * ((ρt g : Matrix (Fin n) (Fin n) P).map mkS *
          (ρt h' : Matrix (Fin n) (Fin n) P).map mkS -
          (ρt g : Matrix (Fin n) (Fin n) P).map mkS * E (x h').val *
            (ρt h' : Matrix (Fin n) (Fin n) P).map mkS) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
    rw [key, hprod, h1, ← Matrix.sub_mul, ← Matrix.mul_assoc]
    congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      hEE, sub_zero]
    rw [hO, hE_add, hE_sub]
    abel
  have hlcK := isLocallyConstant_map_mk_sup_pow h F hF ρt hρtF I Q₀ k₀ hQ₀ hρtlc hJQ hmJI
  have hmSK : ∀ K, (maximalIdeal P ^ K).map mkS = maximalIdeal S ^ K := fun K => by
    rw [Ideal.map_pow, hmS]
  have hcont : Continuous ρfun := by
    refine Matrix.GeneralLinearGroup.continuous_adic_of_forall_isLocallyConstant
      (maximalIdeal S) rfl ρfun fun K => ?_
    set θ := Ideal.Quotient.mk (maximalIdeal S ^ K)
    have hker : I ⊔ maximalIdeal P ^ K ≤ RingHom.ker (θ.comp mkS) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero]
      · rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← hmSK]
        exact Ideal.mem_map_of_mem _ hy
    set lam := Ideal.Quotient.lift (I ⊔ maximalIdeal P ^ K) (θ.comp mkS) hker
    have hfac : ∀ g, Matrix.GeneralLinearGroup.map θ (ρfun g) =
        Matrix.GeneralLinearGroup.map θ (U (x g).val) *
          Matrix.GeneralLinearGroup.map lam
            (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ⊔ maximalIdeal P ^ K))
              (ρt g)) := by
      intro g
      simp only [ρfun, map_mul]
      congr 1
    rw [show (fun g => Matrix.GeneralLinearGroup.map θ (ρfun g)) = _ from funext hfac]
    exact (hxl.comp fun X : AD => Matrix.GeneralLinearGroup.map θ (U X.val)).comp₂
      ((hlcK K).comp (Matrix.GeneralLinearGroup.map lam)) (· * ·)
  let ρ' : π →ₜ* Matrix.GeneralLinearGroup (Fin n) S :=
    { toMonoidHom := MonoidHom.mk' ρfun hmul
      continuous_toFun := hcont }
  have hρ'apply : ∀ g, ρ' g = ρfun g := fun _ => rfl
  have hIres : ∀ y ∈ I, res y = 0 := fun y hy => by
    rw [← RingHom.mem_ker, hres]
    exact hJm (hIJ hy)
  set redS : S →+* ZMod ℓ := Ideal.Quotient.lift I res hIres
  have hredS_mk : ∀ y, redS (mkS y) = res y := fun y => Ideal.Quotient.lift_mk _ _ _
  have hredS_surj : Function.Surjective redS := fun z =>
    ⟨mkS (lift z), by rw [hredS_mk, hreslift]⟩
  have hkerS : RingHom.ker redS = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hredS_surj)
  have hredS_cont : Continuous redS :=
    RingHom.continuous_adic_of_pow_le_ker (maximalIdeal S) redS 1 (by rw [pow_one, hkerS])
  have hredS_alg : ∀ c, redS (algebraMap ℤ_[ℓ] S c) = PadicInt.toZMod c := fun c => by
    change redS (mkS (algebraMap ℤ_[ℓ] P c)) = _
    rw [hredS_mk]
    simp only [res, RingHom.comp_apply, hFalg, h.reduce_algebraMap]
  have hres_e : res e = 0 := by
    rw [← RingHom.mem_ker, hres]
    exact hJm heF
  have hmapE : ∀ (θ : S →+* ZMod ℓ), θ ε = 0 → ∀ X, θ.mapMatrix (E X) = 0 := fun θ hθ X => by
    ext i j
    simp [RingHom.mapMatrix_apply, hEapp, hθ]
  have hρ'red : ∀ g, Matrix.GeneralLinearGroup.map redS (ρ' g) = ρ₀ g := by
    intro g
    refine Units.ext ?_
    rw [hρ'apply]
    change redS.mapMatrix ((1 - E (x g).val) * (ρt g : Matrix (Fin n) (Fin n) P).map mkS) = _
    rw [map_mul, map_sub, map_one, hmapE redS (by rw [hredS_mk, hres_e]), sub_zero, one_mul]
    rw [← hres_ρt g]
    ext i j
    simp [RingHom.mapMatrix_apply, hredS_mk]
  have hdet' : ∀ g, Matrix.GeneralLinearGroup.det (ρ' g) =
      Units.map (algebraMap ℤ_[ℓ] S) (δ g) := by
    intro g
    refine Units.ext ?_
    rw [hρ'apply, Matrix.GeneralLinearGroup.val_det_apply]
    change ((1 - E (x g).val) * (ρt g : Matrix (Fin n) (Fin n) P).map mkS).det = _
    rw [Matrix.det_mul, sub_eq_add_neg, ← hE_neg, hdetE _ (by rw [Matrix.trace_neg,
      AdZero.trace_val, neg_zero]), one_mul, show (ρt g : Matrix (Fin n) (Fin n) P).map mkS =
      mkS.mapMatrix (ρt g) from rfl, ← RingHom.map_det]
    have := congrArg Units.val (hρtdet g)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at this
    rw [this]
    rfl
  obtain ⟨ψ, hψc, hψconj⟩ := h.exists_of_small S rfl hcS redS hredS_surj hredS_cont hredS_alg ρ'
    ⟨1, fun g => by
      change ρ₀ g = 1 * Matrix.GeneralLinearGroup.map redS (ρ' g) * 1⁻¹
      rw [one_mul, inv_one, mul_one, hρ'red]⟩ hdet'
  set pr : S →+* R := Ideal.Quotient.lift I F hIJ
  have hpr_mk : ∀ y, pr (mkS y) = F y := fun y => Ideal.Quotient.lift_mk _ _ _
  have hprC : ∀ c, pr (algebraMap ℤ_[ℓ] S c) = algebraMap ℤ_[ℓ] R c := fun c => by
    change pr (mkS (algebraMap ℤ_[ℓ] P c)) = _
    rw [hpr_mk, hFalg]
  let prA : S →ₐ[ℤ_[ℓ]] R := { pr with commutes' := hprC }
  have hprρ' : ∀ g, Matrix.GeneralLinearGroup.map pr (ρ' g) = ρuniv g := by
    intro g
    refine Units.ext ?_
    rw [hρ'apply]
    change pr.mapMatrix ((1 - E (x g).val) * (ρt g : Matrix (Fin n) (Fin n) P).map mkS) = _
    rw [map_mul, map_sub, map_one]
    have hE0 : pr.mapMatrix (E (x g).val) = 0 := by
      ext i j
      have : pr ε = 0 := by rw [hpr_mk]; exact (RingHom.mem_ker).mp heF
      simp [RingHom.mapMatrix_apply, hEapp, this]
    rw [hE0, sub_zero, one_mul, ← hρtF g]
    ext i j
    simp [RingHom.mapMatrix_apply, hpr_mk]
  have hprψ : prA.comp ψ = AlgHom.id ℤ_[ℓ] R := by
    obtain ⟨_, _, huniq⟩ := h.universal R h.isAdicTopology h.isAdicComplete reduce
      h.reduce_surjective h.reduce_continuous h.reduce_algebraMap ρuniv h.reduce_rep h.det_rep
    have hprm : (maximalIdeal S).map pr ≤ maximalIdeal R := by
      rw [← hmS, Ideal.map_map]
      have : pr.comp mkS = F := Ideal.Quotient.lift_comp_mk _ _ _
      rw [this, map_maximalIdeal_of_surjective F hF]
    have hprc : Continuous pr := by
      rw [h.isAdicTopology]
      exact continuous_adic_of_map_maximalIdeal_le pr hprm
    have c1 : Continuous ((prA.comp ψ : R →ₐ[ℤ_[ℓ]] R) : R → R) := hprc.comp hψc
    have conj1 : IsConjugate (fun g => Matrix.GeneralLinearGroup.map
        (prA.comp ψ).toRingHom (ρuniv g)) (fun g => ρuniv g) := by
      obtain ⟨Pm, hPm⟩ := hψconj
      refine ⟨Matrix.GeneralLinearGroup.map pr Pm, fun g => ?_⟩
      have := congrArg (Matrix.GeneralLinearGroup.map pr) (hPm g)
      simp only [map_mul, map_inv] at this
      have e : Matrix.GeneralLinearGroup.map pr (Matrix.GeneralLinearGroup.map ψ.toRingHom
          (ρuniv g)) = Matrix.GeneralLinearGroup.map (prA.comp ψ).toRingHom (ρuniv g) := by
        ext; rfl
      change ρuniv g = Matrix.GeneralLinearGroup.map pr Pm *
        Matrix.GeneralLinearGroup.map (prA.comp ψ).toRingHom (ρuniv g) *
        (Matrix.GeneralLinearGroup.map pr Pm)⁻¹
      calc ρuniv g = Matrix.GeneralLinearGroup.map pr (ρ' g) := (hprρ' g).symm
        _ = _ := this
        _ = _ := by rw [e]
    have conj2 : IsConjugate (fun g => Matrix.GeneralLinearGroup.map
        (AlgHom.id ℤ_[ℓ] R).toRingHom (ρuniv g)) (fun g => ρuniv g) :=
      ⟨1, fun g => by rw [one_mul, inv_one, mul_one]; ext; rfl⟩
    exact (huniq _ ⟨c1, conj1⟩).trans (huniq _ ⟨continuous_id, conj2⟩).symm
  have hℓm : algebraMap ℤ_[ℓ] P ℓ ∈ maximalIdeal P := by
    refine (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu => ?_)
    have := hu.map F
    rw [hFalg] at this
    exact (mem_maximalIdeal _).mp h.algebraMap_mem_maximalIdeal this
  have hsec := ker_le_of_section F I hIJ hmJI (algebraMap ℤ_[ℓ] P ℓ) hℓm hJ ψ.toRingHom
    (by
      ext y
      exact congrArg (fun φ : R →ₐ[ℤ_[ℓ]] R => φ y) hprψ)
    (by
      intro y hy
      have h1 : redS (ψ (F y)) = 0 := by
        let χ : R →+* ZMod ℓ := redS.comp ψ.toRingHom
        have hχ : Function.Surjective χ := fun z => by
          obtain ⟨c, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := ℓ)) z
          exact ⟨algebraMap ℤ_[ℓ] R c, by
            simp only [χ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
              AlgHom.commutes, hredS_alg]⟩
        have hkχ := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective χ hχ)
        change F y ∈ RingHom.ker χ
        rw [hkχ, ← map_maximalIdeal_of_surjective F hF]
        exact Ideal.mem_map_of_mem F hy
      have h2 : ψ (F y) ∈ (maximalIdeal P).map mkS := by
        rw [hmS, ← hkerS]
        exact h1
      obtain ⟨z, hz, hzeq⟩ := (Ideal.mem_map_iff_of_surjective mkS
        Ideal.Quotient.mk_surjective).mp h2
      exact ⟨z, hz, hzeq.symm⟩)
    (by
      change ψ (F (algebraMap ℤ_[ℓ] P ℓ)) = mkS (algebraMap ℤ_[ℓ] P ℓ)
      rw [hFalg, AlgHom.commutes]
      rfl)
  have := (hsec heF).2
  rw [hφe] at this
  exact one_ne_zero this

end Cocycles

end Deformation.IsUniversalFixedDeterminantDeformation
