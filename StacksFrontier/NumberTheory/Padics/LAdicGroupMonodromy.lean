module

public import StacksFrontier.NumberTheory.Padics.LAdicCongruenceDisc
public import StacksFrontier.NumberTheory.Padics.LAdicCharacterFiniteOrder
public import StacksFrontier.NumberTheory.Padics.LAdicDeterminantalWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CliffordSemisimple
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeterminantalWeightEigenvalues
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The monodromy of an `ℓ`-adic representation of an arithmetic group

Let `Γ` be a compact group (the arithmetic fundamental group `π₁(X₀)` of a variety over a finite
field), `H ⊴ Γ` a normal subgroup (the geometric fundamental group) and `φ ∈ Γ` (a Frobenius
element).  For a continuous representation `ρ : Γ → GL_n(K)`, `K` a complete algebraically closed
ultrametric field over `ℚ_ℓ` (such as `ℂ_ℓ`), this file packages the linear-algebra results on the
`ℓ`-adic disc at the level of groups:

* there is an open normal subgroup `U ⊴ Γ` with `ρ(U)` in the disc `‖g - 1‖ < ℓ⁻¹`
  (`Stacks.LAdic.exists_normal_isOpen_map_mem_matrixDiscSubgroup`);
* the determinant of `R ∘ ρ` on a subspace stable under `R ρ(H)` and `R ρ(φ)` has finite order
  on `H`, for every continuous `R`, as soon as `H` has no `φ`-invariant continuous homomorphism to
  `K` (`Stacks.LAdic.exists_pow_det_stabRestrict_eq_one`; Weil II, 1.3.4);
* for `V = K^n` semisimple under `Γ`, with `G = ρ(H ∩ U)` and `u = ρ(φ^[Γ:U])`, a power
  `u ^ ℓ ^ N` is `exp A * exp B` with `A` in the Lie algebra of `G` and `B` commuting with `G`,
  `u` and `A` (`Stacks.LAdic.exists_monodromy_decomposition`; Weil II, 1.3.9), the restriction of
  `V` to `G` being semisimple by Clifford's theorem.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.3.
* K. Kedlaya, *Fourier transforms and p-adic Weil II*, §6.1.
-/

@[expose] public noncomputable section

open Filter Topology NormedSpace Matrix

namespace Stacks.LAdic

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

section Stabilizer

variable (W : Submodule K (m → K))

/-- The invertible matrices `g` such that `g` and `g⁻¹` preserve `W`. -/
def unitsStabilizer : Subgroup (Matrix m m K)ˣ where
  carrier := {g | (g : Matrix m m K) ∈ stabilizerSubalgebra W ∧
    ((g⁻¹ : (Matrix m m K)ˣ) : Matrix m m K) ∈ stabilizerSubalgebra W}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' {a b} ha hb := ⟨Subalgebra.mul_mem _ ha.1 hb.1,
    by simpa only [_root_.mul_inv_rev, Units.val_mul] using Subalgebra.mul_mem _ hb.2 ha.2⟩
  inv_mem' {a} ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

omit [CharZero K] [CompleteSpace K] in
/-- An invertible matrix preserving a subspace of `K^m` preserves it with its inverse. -/
theorem mem_unitsStabilizer_of_mem {W : Submodule K (m → K)} {g : (Matrix m m K)ˣ}
    (hg : (g : Matrix m m K) ∈ stabilizerSubalgebra W) : g ∈ unitsStabilizer W := by
  refine ⟨hg, fun w hw => ?_⟩
  have hinj : Function.Injective (stabRestrict (g : Matrix m m K) hg) := fun a b hab => by
    apply Subtype.ext
    have := congrArg (fun x : W => ((g⁻¹ : (Matrix m m K)ˣ) : Matrix m m K) *ᵥ (x : m → K)) hab
    simpa [stabRestrict_apply, Matrix.mulVec_mulVec] using this
  obtain ⟨w', hw'⟩ := LinearMap.surjective_of_injective hinj ⟨w, hw⟩
  have h := congrArg (fun x : W => ((g⁻¹ : (Matrix m m K)ˣ) : Matrix m m K) *ᵥ (x : m → K)) hw'
  simp only [stabRestrict_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
  exact h ▸ w'.2

omit [CharZero K] [CompleteSpace K] in
/-- The determinant on `W` of an element of `unitsStabilizer W`, as a homomorphism. -/
def stabDetHom : unitsStabilizer W →* K where
  toFun g := LinearMap.det (stabRestrict ((g : (Matrix m m K)ˣ) : Matrix m m K) g.2.1)
  map_one' := by
    rw [show stabRestrict (((1 : unitsStabilizer W) : (Matrix m m K)ˣ) : Matrix m m K)
        (1 : unitsStabilizer W).2.1 = 1 from
      LinearMap.ext fun w => Subtype.ext (by simp [stabRestrict_apply]), map_one]
  map_mul' a b := by
    rw [stabRestrict_congr (show (((a * b : unitsStabilizer W) : (Matrix m m K)ˣ) :
        Matrix m m K) = ((a : (Matrix m m K)ˣ) : Matrix m m K) * ((b : (Matrix m m K)ˣ) :
          Matrix m m K) by simp) _ (Subalgebra.mul_mem _ a.2.1 b.2.1),
      stabRestrict_mul, map_mul]

omit [CharZero K] in
/-- The determinant of the restriction to an invariant subspace depends continuously on the
matrix. -/
theorem continuous_det_stabRestrict {X : Type*} [TopologicalSpace X] {W : Submodule K (m → K)}
    (F : X → Matrix m m K) (hF : Continuous F) (hW : ∀ x, F x ∈ stabilizerSubalgebra W) :
    Continuous fun x => LinearMap.det (stabRestrict (F x) (hW x)) := by
  set b := Module.finBasis K W
  have hb : Continuous (b.equivFun : W → (Fin (Module.finrank K W) → K)) :=
    LinearMap.continuous_of_finiteDimensional b.equivFun.toLinearMap
  have e : ∀ x, LinearMap.det (stabRestrict (F x) (hW x)) =
      (Matrix.of fun i j => b.equivFun (⟨F x *ᵥ (b j : m → K), hW x _ (b j).2⟩ : W) i).det := by
    intro x
    rw [← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.of_apply, Module.Basis.equivFun_apply]
    congr 2
  simp_rw [e]
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [Matrix.of_apply]
  exact (continuous_apply i).comp (hb.comp
    ((hF.matrix_mulVec continuous_const).subtype_mk _))

end Stabilizer

variable (K) in
/-- The image in `GL_n(K)` of an invertible matrix over `ℚ_ℓ`. -/
def ratToUnitsMatrix : GL n ℚ_[ℓ] →* (Matrix n n K)ˣ :=
  Units.map (algebraMap ℚ_[ℓ] K).mapMatrix.toMonoidHom

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The matrix underlying `ratToUnitsMatrix K g` is `g` with `algebraMap ℚ_[ℓ] K` applied to each
entry. -/
theorem coe_ratToUnitsMatrix (g : GL n ℚ_[ℓ]) :
    ((ratToUnitsMatrix K g : (Matrix n n K)ˣ) : Matrix n n K) =
      (g : Matrix n n ℚ_[ℓ]).map fun x => algebraMap ℚ_[ℓ] K x := rfl

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- A continuous `ℓ`-adic representation stays continuous after extending scalars to `K`. -/
theorem continuous_ratToUnitsMatrix_comp {Γ : Type*} [TopologicalSpace Γ] {ρ : Γ → GL n ℚ_[ℓ]}
    (hρ : Continuous ρ) : Continuous fun g => (ratToUnitsMatrix K (ρ g) : Matrix n n K) :=
  (Units.continuous_val.comp hρ).matrix_map (continuous_algebraMap ℚ_[ℓ] K)

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

omit [CharZero K] [CompleteSpace K] [NormedAlgebra ℚ_[ℓ] K] in
/-- **An open normal subgroup lands in the disc.**  For a continuous representation
`ρ : Γ → GL_n(K)` of a compact group there is an open normal subgroup `U` with `‖ρ g - 1‖ < ℓ⁻¹`
for `g ∈ U`. -/
theorem exists_normal_isOpen_map_mem_matrixDiscSubgroup (ρ : Γ →* (Matrix n n K)ˣ)
    (hρ : Continuous fun g => (ρ g : Matrix n n K)) :
    ∃ U : Subgroup Γ, U.Normal ∧ IsOpen (U : Set Γ) ∧
      ∀ g ∈ U, ρ g ∈ matrixDiscSubgroup ℓ K n := by
  set U₀ : Subgroup Γ := (matrixDiscSubgroup ℓ K n).comap ρ
  have hU₀ : IsOpen (U₀ : Set Γ) := by
    show IsOpen {g : Γ | ‖(ρ g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹}
    exact isOpen_lt (continuous_norm.comp (hρ.sub continuous_const)) continuous_const
  have : Finite (Γ ⧸ U₀) := Subgroup.quotient_finite_of_isOpen U₀ hU₀
  have : U₀.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact ⟨U₀.normalCore, inferInstance, Subgroup.isOpen_of_isClosed_of_finiteIndex _
    (U₀.normalCore_isClosed (Subgroup.isClosed_of_isOpen U₀ hU₀)),
    fun g hg => U₀.normalCore_le hg⟩

variable (ℓ) in
include ℓ in
/-- **Finite determinants on the geometric monodromy** (Weil II, 1.3.4, group form).  Let
`R : Γ → GL_m(K)` be continuous, `H ≤ Γ` and `φ ∈ Γ`, and let `W ⊆ K^m` be stable under `R(H)`
and `R(φ)`.  If every continuous homomorphism `H → K` invariant under conjugation by `φ` vanishes,
then `det (R h |_W)` has finite order for every `h ∈ H`. -/
theorem exists_pow_det_stabRestrict_eq_one (R : Γ →* (Matrix m m K)ˣ)
    (hR : Continuous fun g => (R g : Matrix m m K)) (H : Subgroup Γ) (φ : Γ)
    (hH : ∀ ψ : H → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
      (∀ a b : H, (b : Γ) = φ * a * φ⁻¹ → ψ b = ψ a) → ψ = 0)
    {W : Submodule K (m → K)} (hHW : ∀ h ∈ H, (R h : Matrix m m K) ∈ stabilizerSubalgebra W)
    (hφW : (R φ : Matrix m m K) ∈ stabilizerSubalgebra W) {h : Γ} (hh : h ∈ H) :
    ∃ k : ℕ, 0 < k ∧ ∀ hh' : (R h : Matrix m m K) ∈ stabilizerSubalgebra W,
      LinearMap.det (stabRestrict (R h : Matrix m m K) hh') ^ k = 1 := by
  set S : Subgroup Γ := (unitsStabilizer W).comap R
  have hSc : IsClosed (S : Set Γ) := by
    have e : (S : Set Γ) = (fun g => (R g : Matrix m m K)) ⁻¹' (stabilizerSubalgebra W) ∩
        (fun g => (R g⁻¹ : Matrix m m K)) ⁻¹' (stabilizerSubalgebra W) := by
      ext g
      simp [S, unitsStabilizer, map_inv]
    rw [e]
    exact ((isClosed_stabilizerSubalgebra W).preimage hR).inter
      ((isClosed_stabilizerSubalgebra W).preimage (hR.comp continuous_inv))
  have : CompactSpace S := isCompact_iff_compactSpace.mp hSc.isCompact
  have hHS : ∀ a ∈ H, a ∈ S := fun a ha => mem_unitsStabilizer_of_mem (hHW a ha)
  have hφS : φ ∈ S := mem_unitsStabilizer_of_mem hφW
  set H' : Subgroup S := H.comap S.subtype
  set χ : S →* Kˣ := (stabDetHom W).toHomUnits.comp (R.subgroupComap (unitsStabilizer W))
  have hχ : Continuous fun g => (χ g : K) := continuous_det_stabRestrict (W := W)
    (fun g : S => (R g : Matrix m m K)) (hR.comp continuous_subtype_val) fun g => g.2.1
  have hH' : ∀ ψ : H' → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
      (∀ a b : H', (b : S) = ⟨φ, hφS⟩ * a * (⟨φ, hφS⟩ : S)⁻¹ → ψ b = ψ a) → ψ = 0 := by
    intro ψ hadd hcont hinv
    set ψ₀ : H → K := fun a => ψ ⟨⟨a, hHS a a.2⟩, a.2⟩
    have h0 : ψ₀ = 0 := hH ψ₀ (fun a b => hadd ⟨⟨a, hHS a a.2⟩, a.2⟩ ⟨⟨b, hHS b b.2⟩, b.2⟩)
      (hcont.comp ((continuous_subtype_val.subtype_mk _).subtype_mk _))
      (fun a b hab => hinv _ _ (Subtype.ext hab))
    funext x
    exact congrFun h0 ⟨x.1.1, x.2⟩
  obtain ⟨k, hk, hχk⟩ := exists_pow_eq_one_of_forall_conj_invariant ℓ H' ⟨φ, hφS⟩ hH' χ hχ
  refine ⟨k, hk, fun hh' => ?_⟩
  have := congrArg Units.val (hχk ⟨h, hHS h hh⟩ hh)
  rw [Units.val_pow_eq_pow_val, Units.val_one] at this
  exact this

omit [CharZero K] [CompleteSpace K] in
/-- The determinant on a `ρ(Γ)`-stable subspace, as a character of `Γ`. -/
def detCharacter (ρ : Γ →* (Matrix m m K)ˣ) {W : Submodule K (m → K)}
    (hW : ∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W) : Γ →* K where
  toFun g := LinearMap.det (stabRestrict (ρ g : Matrix m m K) (hW g))
  map_one' := by
    rw [show stabRestrict (ρ 1 : Matrix m m K) (hW 1) = 1 from
      LinearMap.ext fun w => Subtype.ext (by simp [stabRestrict_apply]), map_one]
  map_mul' a b := by
    rw [stabRestrict_congr (show (ρ (a * b) : Matrix m m K) = (ρ a : Matrix m m K) * ρ b by
        rw [map_mul, Units.val_mul]) _ (Subalgebra.mul_mem _ (hW a) (hW b)),
      stabRestrict_mul, map_mul]

variable (ℓ) in
include ℓ in
/-- **Determinantal weights are read on a single Frobenius** (Weil II, 1.3.4 and 1.3.5).  Let
`W` be stable under a continuous `ρ`, and assume no nonzero continuous homomorphism `H → K` is
invariant under conjugation by `φ`.  Then for `g ∈ φ ^ d H` (a Frobenius element at a point of
degree `d`), `‖ι det (ρ g |_W)‖ = ‖ι det (ρ φ |_W)‖ ^ d`. -/
theorem norm_detCharacter_eq_pow (ι : K →+* ℂ) (ρ : Γ →* (Matrix m m K)ˣ)
    (hρ : Continuous fun g => (ρ g : Matrix m m K)) (H : Subgroup Γ) (φ : Γ)
    (hH : ∀ ψ : H → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
      (∀ a b : H, (b : Γ) = φ * a * φ⁻¹ → ψ b = ψ a) → ψ = 0)
    {W : Submodule K (m → K)} (hW : ∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W)
    {g : Γ} {d : ℕ} (hg : (φ ^ d)⁻¹ * g ∈ H) :
    ‖ι (detCharacter ρ hW g)‖ = ‖ι (detCharacter ρ hW φ)‖ ^ d := by
  obtain ⟨k, hk, hdk⟩ := exists_pow_det_stabRestrict_eq_one ℓ ρ hρ H φ hH (fun h _ => hW h)
    (hW φ) hg
  have h1 : ‖ι (detCharacter ρ hW ((φ ^ d)⁻¹ * g))‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by
      rw [← map_pow]
      exact (congrArg ι (hdk (hW _))).trans (map_one ι)) hk.ne'
  have e : g = φ ^ d * ((φ ^ d)⁻¹ * g) := by group
  rw [e, map_mul, map_mul, norm_mul, h1, mul_one, map_pow, map_pow, norm_pow]

section Clifford

/-- Invertible matrices as invertible endomorphisms of `K^n`. -/
def unitsToEnd : (Matrix n n K)ˣ →* (Module.End K (n → K))ˣ :=
  Units.map (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] Module.End K (n → K)).toMonoidHom

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- A subspace `W` of `K^n` is stable under the image of `G` in `(Module.End K (n → K))ˣ` if and
only if every element of `G` lies in `stabilizerSubalgebra W`. -/
theorem isStableUnder_map_unitsToEnd_iff {G : Subgroup (Matrix n n K)ˣ}
    {W : Submodule K (n → K)} :
    Stacks.EtaleCohomology.IsStableUnder
        (Units.val '' ((G.map unitsToEnd : Subgroup (Module.End K (n → K))ˣ) :
          Set (Module.End K (n → K))ˣ)) W ↔
      ∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra W := by
  constructor
  · intro h g hg w hw
    have := h _ ⟨unitsToEnd g, ⟨g, hg, rfl⟩, rfl⟩ hw
    change Matrix.toLinAlgEquiv' (g : Matrix n n K) w ∈ W at this
    rwa [Matrix.toLinAlgEquiv'_apply] at this
  · rintro h _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩ w hw
    show Matrix.toLinAlgEquiv' (g : Matrix n n K) w ∈ W
    rw [Matrix.toLinAlgEquiv'_apply]
    exact h g hg w hw

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- **Clifford, for groups of matrices.**  If `K^n` is semisimple under a group `Γ` of invertible
matrices, it is semisimple under every subgroup `N ≤ Γ` normalized by `Γ`. -/
theorem exists_isCompl_stabilizerSubalgebra_of_normal (Γ N : Subgroup (Matrix n n K)ˣ)
    (hNΓ : N ≤ Γ) (hnormal : ∀ γ ∈ Γ, ∀ g ∈ N, γ * g * γ⁻¹ ∈ N)
    (hss : ∀ W : Submodule K (n → K), (∀ g ∈ Γ, (g : Matrix n n K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (n → K), IsCompl W W' ∧
        ∀ g ∈ Γ, (g : Matrix n n K) ∈ stabilizerSubalgebra W')
    {W : Submodule K (n → K)} (hW : ∀ g ∈ N, (g : Matrix n n K) ∈ stabilizerSubalgebra W) :
    ∃ W' : Submodule K (n → K), IsCompl W W' ∧
      ∀ g ∈ N, (g : Matrix n n K) ∈ stabilizerSubalgebra W' := by
  have h1 := (isStableUnder_map_unitsToEnd_iff (G := N) (W := W)).mpr hW
  have h2 : ∀ γ ∈ Γ.map unitsToEnd, ∀ g ∈ N.map unitsToEnd, γ * g * γ⁻¹ ∈ N.map unitsToEnd := by
    rintro _ ⟨γ, hγ, rfl⟩ _ ⟨g, hg, rfl⟩
    exact ⟨γ * g * γ⁻¹, hnormal γ hγ g hg, by rw [map_mul, map_mul, map_inv]⟩
  have h3 : ∀ W : Submodule K (n → K), Stacks.EtaleCohomology.IsStableUnder
      (Units.val '' ((Γ.map unitsToEnd : Subgroup (Module.End K (n → K))ˣ) :
        Set (Module.End K (n → K))ˣ)) W →
      ∃ W', IsCompl W W' ∧ Stacks.EtaleCohomology.IsStableUnder
        (Units.val '' ((Γ.map unitsToEnd : Subgroup (Module.End K (n → K))ˣ) :
          Set (Module.End K (n → K))ˣ)) W' := by
    intro W hW
    obtain ⟨W', hc, hW'⟩ := hss W ((isStableUnder_map_unitsToEnd_iff (G := Γ)).mp hW)
    exact ⟨W', hc, (isStableUnder_map_unitsToEnd_iff (G := Γ)).mpr hW'⟩
  obtain ⟨W', hc, hW'⟩ := Stacks.EtaleCohomology.exists_isCompl_of_normal (K := K) (V := n → K)
    (Γ.map unitsToEnd) (N.map unitsToEnd) (Subgroup.map_mono hNΓ) h2 h3 h1
  exact ⟨W', hc, (isStableUnder_map_unitsToEnd_iff (G := N)).mp hW'⟩

end Clifford

/-- **The monodromy decomposition of Frobenius** (Weil II, 1.3.9, `ℓ`-adic form).  Let
`ρ : Γ → GL_n(K)` be a continuous representation of a compact group, `K` complete, algebraically
closed and ultrametric over `ℚ_ℓ`, for which `K^n` is semisimple, `H ⊴ Γ` and `φ ∈ Γ`.  There
is an open normal subgroup `U ⊴ Γ` with `ρ(U)` in the disc `‖g - 1‖ < ℓ⁻¹` such that, for
`G = ρ(H ∩ U)` and `u = ρ(φ ^ [Γ : U])`: `u` lies in the disc and normalizes `G`, and
`u ^ ℓ ^ N = exp A * exp B` with `A` in the Lie algebra spanned by `log G`, and `B` commuting with
`G`, with `u` and with `A`, and `ℓ ^ N • log u = A + B`. -/
theorem exists_monodromy_decomposition [IsAlgClosed K] (ρ : Γ →* (Matrix n n K)ˣ)
    (hρ : Continuous fun g => (ρ g : Matrix n n K)) (H : Subgroup Γ) [H.Normal] (φ : Γ)
    (hss : ∀ W : Submodule K (n → K), (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (n → K), IsCompl W W' ∧
        ∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W') :
    ∃ U : Subgroup Γ, U.Normal ∧ IsOpen (U : Set Γ) ∧
      (∀ g ∈ U, ‖(ρ g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) ∧
      (∀ g ∈ (H ⊓ U).map ρ, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) ∧
      ‖(ρ (φ ^ U.index) : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹ ∧
      (∀ g ∈ (H ⊓ U).map ρ, ρ (φ ^ U.index) * g * (ρ (φ ^ U.index))⁻¹ ∈ (H ⊓ U).map ρ) ∧
      (∀ W : Submodule K (n → K), (∀ g ∈ (H ⊓ U).map ρ, (g : Matrix n n K) ∈
          stabilizerSubalgebra W) →
        ∃ W' : Submodule K (n → K), IsCompl W W' ∧
          ∀ g ∈ (H ⊓ U).map ρ, (g : Matrix n n K) ∈ stabilizerSubalgebra W') ∧
      ∃ N : ℕ, ∃ A B : Matrix n n K,
        Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ ((H ⊓ U).map ρ) ∧ ‖A‖ < (ℓ : ℝ)⁻¹ ∧
        ‖B‖ < (ℓ : ℝ)⁻¹ ∧ (∀ g ∈ (H ⊓ U).map ρ, Commute B (g : Matrix n n K)) ∧
        Commute B (ρ (φ ^ U.index) : Matrix n n K) ∧ Commute A B ∧
        (ℓ ^ N : ℕ) • ladicLog ℓ (ρ (φ ^ U.index) : Matrix n n K) = A + B ∧
        (ρ (φ ^ U.index) : Matrix n n K) ^ (ℓ ^ N) = exp A * exp B := by
  obtain ⟨U, hUn, hUo, hU⟩ := exists_normal_isOpen_map_mem_matrixDiscSubgroup (ℓ := ℓ) ρ hρ
  set G := (H ⊓ U).map ρ
  have hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹ := by
    rintro _ ⟨g, hg, rfl⟩
    exact hU g hg.2
  have hu : ‖(ρ (φ ^ U.index) : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹ := hU _ (U.pow_index_mem φ)
  have hconj : ∀ (γ : Γ), ∀ g ∈ G, ρ γ * g * (ρ γ)⁻¹ ∈ G := by
    rintro γ _ ⟨g, hg, rfl⟩
    exact ⟨γ * g * γ⁻¹, ⟨‹H.Normal›.conj_mem g hg.1 γ, hUn.conj_mem g hg.2 γ⟩, by
      simp [map_mul, map_inv]⟩
  have hssG : ∀ W : Submodule K (n → K), (∀ g ∈ G, (g : Matrix n n K) ∈
      stabilizerSubalgebra W) → ∃ W' : Submodule K (n → K), IsCompl W W' ∧
        ∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra W' := by
    intro W hW
    refine exists_isCompl_stabilizerSubalgebra_of_normal ρ.range G
      (by rintro _ ⟨g, -, rfl⟩; exact ⟨g, rfl⟩) ?_ ?_ hW
    · rintro _ ⟨γ, rfl⟩
      exact hconj γ
    · intro W hW
      obtain ⟨W', hc, hW'⟩ := hss W fun g => hW _ ⟨g, rfl⟩
      exact ⟨W', hc, by rintro _ ⟨g, rfl⟩; exact hW' g⟩
  exact ⟨U, hUn, hUo, hU, hG, hu, hconj _, hssG,
    exists_pow_eq_exp_mul_exp_of_normalizes hG hssG hu (hconj _)⟩

section Relative

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A subspace `X` of an `f`-stable `W` is stable under the restriction of `f` to `W` if and only
if its image in `V` is `f`-stable. -/
theorem le_comap_restrict_iff {f : Module.End F V} {W : Submodule F V} (hf : W ≤ W.comap f)
    {X : Submodule F W} :
    X ≤ X.comap (f.restrict hf) ↔ X.map W.subtype ≤ (X.map W.subtype).comap f := by
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    exact ⟨_, h hx, rfl⟩
  · intro h x hx
    obtain ⟨y, hy, hxy⟩ := h ⟨x, hx, rfl⟩
    have e : y = f.restrict hf x := Subtype.ext hxy
    rwa [Submodule.mem_comap, ← e]

/-- The determinant of an endomorphism restricted to a stable subspace is unchanged by transport
along an injective linear map intertwining it with another endomorphism. -/
private theorem det_restrict_eq_of_injective {M M' : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup M'] [Module F M'] {j : M →ₗ[F] M'} (hj : Function.Injective j)
    {f : Module.End F M} {f' : Module.End F M'} (hf : ∀ x, j (f x) = f' (j x))
    {X : Submodule F M} (hX : X ≤ X.comap f) (hX' : X.map j ≤ (X.map j).comap f') :
    LinearMap.det (f'.restrict hX') = LinearMap.det (f.restrict hX) := by
  set e := Submodule.equivMapOfInjective j hj X
  have key : f'.restrict hX' = e.toLinearMap ∘ₗ f.restrict hX ∘ₗ e.symm.toLinearMap := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact (hf x).symm
  rw [key, LinearMap.det_conj]

/-- The determinant of `f` on a subspace `X` of an `f`-stable `W`, computed in `W` or in `V`. -/
theorem det_restrict_restrict {f : Module.End F V} {W : Submodule F V} (hf : W ≤ W.comap f)
    {X : Submodule F W} (hX : X ≤ X.comap (f.restrict hf))
    (hX' : X.map W.subtype ≤ (X.map W.subtype).comap f) :
    LinearMap.det ((f.restrict hf).restrict hX) = LinearMap.det (f.restrict hX') :=
  (det_restrict_eq_of_injective W.injective_subtype (fun _ => rfl) hX hX').symm

/-- The restrictions to a stable subspace `W` of the elements of a group `Γ`. -/
def restrictUnitsHom (Γ : Subgroup (Module.End F V)ˣ) (W : Submodule F V)
    (hW : ∀ γ ∈ Γ, W ≤ W.comap ((γ : (Module.End F V)ˣ) : Module.End F V)) :
    Γ →* (Module.End F W)ˣ where
  toFun γ :=
    { val := ((γ : (Module.End F V)ˣ) : Module.End F V).restrict (hW γ γ.2)
      inv := (((γ : (Module.End F V)ˣ)⁻¹ : (Module.End F V)ˣ) : Module.End F V).restrict
        (hW _ (inv_mem γ.2))
      val_inv := LinearMap.ext fun w => Subtype.ext (by
        change ((γ : (Module.End F V)ˣ) : Module.End F V)
          ((((γ : (Module.End F V)ˣ)⁻¹ : (Module.End F V)ˣ) : Module.End F V) w) = w
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Module.End.one_apply])
      inv_val := LinearMap.ext fun w => Subtype.ext (by
        change (((γ : (Module.End F V)ˣ)⁻¹ : (Module.End F V)ˣ) : Module.End F V)
          (((γ : (Module.End F V)ˣ) : Module.End F V) w) = w
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply]) }
  map_one' := Units.ext (LinearMap.ext fun w => Subtype.ext rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun w => Subtype.ext rfl)

/-- The restriction `restrictUnitsHom Γ W hW γ` acts on `w ∈ W` as `γ` acts on `w` in `V`. -/
theorem coe_restrictUnitsHom_apply (Γ : Subgroup (Module.End F V)ˣ) (W : Submodule F V)
    (hW : ∀ γ ∈ Γ, W ≤ W.comap ((γ : (Module.End F V)ˣ) : Module.End F V)) (γ : Γ) (w : W) :
    (((restrictUnitsHom Γ W hW γ : (Module.End F W)ˣ) : Module.End F W) w : V) =
      ((γ : (Module.End F V)ˣ) : Module.End F V) w := rfl

/-- The determinant of `f` on `γ X` is that of `γ⁻¹ f γ` on `X`. -/
theorem det_restrict_map_unit {f f' : Module.End F V} {γ : (Module.End F V)ˣ}
    (hf : (γ : Module.End F V) * f' = f * γ) {X : Submodule F V} (hX : X ≤ X.comap f')
    (hX' : X.map (γ : Module.End F V) ≤ (X.map (γ : Module.End F V)).comap f) :
    LinearMap.det (f.restrict hX') = LinearMap.det (f'.restrict hX) := by
  have hinj : Function.Injective (γ : Module.End F V) := fun a b hab => by
    have := congrArg ((γ⁻¹ : (Module.End F V)ˣ) : Module.End F V) hab
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply, Module.End.one_apply] at this
  exact det_restrict_eq_of_injective (j := (γ : Module.End F V)) hinj
    (LinearMap.congr_fun hf) hX hX'

variable [FiniteDimensional F V] [IsAlgClosed F]

omit [IsAlgClosed F] in
/-- An eigenvalue of `z` is an eigenvalue of its restriction to one of a family of `z`-stable
subspaces spanning `V`. -/
theorem exists_hasEigenvalue_restrict_of_sSup_eq_top {z : Module.End F V}
    {T : Set (Submodule F V)} (hT : sSup T = ⊤) (hz : ∀ W ∈ T, W ≤ W.comap z) {μ : F}
    (hμ : z.HasEigenvalue μ) :
    ∃ W, ∃ hW : W ∈ T, Module.End.HasEigenvalue (z.restrict (hz W hW)) μ := by
  by_contra hne
  push Not at hne
  set f : Module.End F V := z - algebraMap F (Module.End F V) μ
  have hW : ∀ W ∈ T, W ≤ LinearMap.range f := by
    intro W hWT
    have hfW : W ≤ W.comap f := fun w hw =>
      W.sub_mem (hz W hWT hw) (by simpa using W.smul_mem μ hw)
    have hinj : Function.Injective (f.restrict hfW) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro w hw
      by_contra hw0
      refine hne W hWT (Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hw0⟩)
      rw [Module.End.mem_eigenspace_iff]
      have h0 : ((f.restrict hfW w : W) : V) = 0 := by
        rw [LinearMap.mem_ker] at hw
        rw [hw]
        rfl
      apply Subtype.ext
      have h1 : z w - μ • (w : V) = 0 := by simpa [f] using h0
      simpa [sub_eq_zero] using h1
    intro w hw
    obtain ⟨w', hw'⟩ := LinearMap.surjective_of_injective hinj ⟨w, hw⟩
    exact ⟨w', congrArg Subtype.val hw'⟩
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hT]
    exact sSup_le hW
  have hinj := LinearMap.injective_iff_surjective.mpr hsurj
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  apply hv.2
  apply hinj
  rw [map_zero]
  simp [f, hv.apply_eq_smul]

/-- **A single weight on an irreducible subrepresentation.**  The relative form of
`Stacks.EtaleCohomology.exists_forall_hasEigenvalue_norm_eq`: under its hypotheses on `V`, for
every subspace `W` stable under `S` and `Γ` and irreducible under `Γ`, the eigenvalues of `z` on
`W` have a single absolute value. -/
theorem exists_forall_hasEigenvalue_restrict_norm_eq (ι : F →+* ℂ) (S : Set (Module.End F V))
    (Γ : Subgroup (Module.End F V)ˣ) {U z : Module.End F V} (hUS : U ∈ S)
    (hzS : ∀ s ∈ S, Commute z s)
    (hz : ∀ W : Submodule F V, (∀ s ∈ S, W ≤ W.comap s) → W ≤ W.comap z)
    (hdet : ∀ (W : Submodule F V) (hW : ∀ s ∈ S, W ≤ W.comap s),
      LinearMap.det (U.restrict (hW U hUS)) = LinearMap.det (z.restrict (hz W hW)))
    (hnormal : ∀ γ ∈ Γ, ∀ W : Submodule F V, (∀ s ∈ S, W ≤ W.comap s) →
      ∀ s ∈ S, W.map ((γ : (Module.End F V)ˣ) : Module.End F V) ≤
        (W.map ((γ : (Module.End F V)ˣ) : Module.End F V)).comap s)
    (hconj : ∀ γ ∈ Γ, ∀ (W : Submodule F V) (hW : ∀ s ∈ S, W ≤ W.comap s)
      (hW' : ∀ s ∈ S, W.map ((γ : (Module.End F V)ˣ) : Module.End F V) ≤
        (W.map ((γ : (Module.End F V)ˣ) : Module.End F V)).comap s),
      ‖ι (LinearMap.det (U.restrict (hW' U hUS)))‖ = ‖ι (LinearMap.det (U.restrict (hW U hUS)))‖)
    {W : Submodule F V} (hWS : ∀ s ∈ S, W ≤ W.comap s)
    (hWΓ : ∀ γ ∈ Γ, W ≤ W.comap ((γ : (Module.End F V)ˣ) : Module.End F V))
    (hirr : ∀ W' ≤ W, W' ≠ ⊥ →
      (∀ γ ∈ Γ, W' ≤ W'.comap ((γ : (Module.End F V)ˣ) : Module.End F V)) → W' = W) :
    ∃ r : ℝ, ∀ μ, Module.End.HasEigenvalue (z.restrict (hz W hWS)) μ → ‖ι μ‖ = r := by
  set S' : Set (Module.End F W) := {s' | ∃ s ∈ S, ∃ h : W ≤ W.comap s, s' = s.restrict h}
  set Γ' := (restrictUnitsHom Γ W hWΓ).range
  have hS' : ∀ X : Submodule F W, (∀ s' ∈ S', X ≤ X.comap s') ↔
      ∀ s ∈ S, X.map W.subtype ≤ (X.map W.subtype).comap s := by
    intro X
    refine ⟨fun h s hs => (le_comap_restrict_iff (hWS s hs)).mp (h _ ⟨s, hs, hWS s hs, rfl⟩), ?_⟩
    rintro h _ ⟨s, hs, hsW, rfl⟩
    exact (le_comap_restrict_iff hsW).mpr (h s hs)
  have hmapγ : ∀ (γ : Γ) (X : Submodule F W),
      (X.map ((restrictUnitsHom Γ W hWΓ γ : (Module.End F W)ˣ) : Module.End F W)).map W.subtype =
        (X.map W.subtype).map ((γ : (Module.End F V)ˣ) : Module.End F V) := by
    intro γ X
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    rfl
  have hU' := hWS U hUS
  refine Stacks.EtaleCohomology.exists_forall_hasEigenvalue_norm_eq ι S' Γ' (U := U.restrict hU')
    ⟨U, hUS, hU', rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨s, hs, hsW, rfl⟩
    exact LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun (hzS s hs).eq (w : V))
  · intro X hX
    exact (le_comap_restrict_iff (hz W hWS)).mpr (hz _ ((hS' X).mp hX))
  · intro X hX
    have hXS := (hS' X).mp hX
    rw [det_restrict_restrict hU' _ (hXS U hUS), det_restrict_restrict (hz W hWS) _ (hz _ hXS)]
    exact hdet _ hXS
  · rintro _ ⟨γ, rfl⟩ X hX
    rw [hS', hmapγ]
    exact hnormal γ γ.2 _ ((hS' X).mp hX)
  · rintro _ ⟨γ, rfl⟩ X hX hX'
    have hXS := (hS' X).mp hX
    have hXS' := (hS' _).mp hX'
    rw [det_restrict_restrict hU' _ (hXS' U hUS), det_restrict_restrict hU' _ (hXS U hUS),
      Stacks.EtaleCohomology.norm_det_restrict_congr ι U (hmapγ γ X) _
        (hnormal γ γ.2 _ hXS U hUS)]
    exact hconj γ γ.2 _ hXS _
  · intro X hX0 hXΓ
    have hle : X.map W.subtype ≤ W := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hne : X.map W.subtype ≠ ⊥ := by
      rw [Ne, ← Submodule.map_bot W.subtype]
      exact fun h => hX0 (Submodule.map_injective_of_injective W.injective_subtype h)
    have hXW := hirr _ hle hne fun γ hγ =>
      (le_comap_restrict_iff (hWΓ γ hγ)).mp (hXΓ _ ⟨⟨γ, hγ⟩, rfl⟩)
    rw [eq_top_iff]
    intro x _
    have : (x : V) ∈ X.map W.subtype := by rw [hXW]; exact x.2
    obtain ⟨y, hy, hxy⟩ := this
    rwa [← Subtype.ext hxy]

end Relative

section Weights

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- A subspace `X` of `K^n` is stable under `Matrix.toLin' M` if and only if `M` lies in
`stabilizerSubalgebra X`. -/
theorem le_comap_toLin'_iff {M : Matrix n n K} {X : Submodule K (n → K)} :
    X ≤ X.comap (Matrix.toLin' M) ↔ M ∈ stabilizerSubalgebra X :=
  ⟨fun h w hw => by simpa [Matrix.toLin'_apply] using h hw,
    fun h w hw => by simpa [Matrix.toLin'_apply] using h w hw⟩

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- Commuting matrices give commuting linear endomorphisms of `K^n` under `Matrix.toLin'`. -/
theorem commute_toLin' {M M' : Matrix n n K} (h : Commute M M') :
    Commute (Matrix.toLin' M) (Matrix.toLin' M') := by
  unfold Commute SemiconjBy
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
    h.eq]

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The endomorphism underlying `unitsToEnd g` is `Matrix.toLin' g`. -/
theorem coe_unitsToEnd (g : (Matrix n n K)ˣ) :
    ((unitsToEnd g : (Module.End K (n → K))ˣ) : Module.End K (n → K)) =
      Matrix.toLin' (g : Matrix n n K) :=
  LinearMap.ext fun v => by
    show Matrix.toLinAlgEquiv' (g : Matrix n n K) v = _
    rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- In an arithmetic group with abelian quotient `Γ / H`, conjugation moves an element of `H ⊓ U`
or a power `φ ^ j ∈ U` (`U` normal) only by an element of `H ⊓ U`. -/
theorem inv_mul_conj_mem {H U : Subgroup Γ} [H.Normal] [U.Normal]
    (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H) {c : Γ} (hc : c ∈ U) (a : Γ) :
    c⁻¹ * (a⁻¹ * c * a) ∈ H ⊓ U := by
  refine ⟨?_, U.mul_mem (U.inv_mem hc) (by simpa using ‹U.Normal›.conj_mem c hc a⁻¹)⟩
  simpa [mul_assoc] using hcomm c⁻¹ a⁻¹

/-- **Mondetwt: a single weight on an irreducible constituent** (Weil II, 1.3; Kedlaya,
Proposition 6.1.4).  In the situation of `Stacks.LAdic.exists_monodromy_decomposition`, with
`Γ / H` abelian and `H ⊓ U` without nonzero continuous homomorphisms to `K` invariant under
conjugation by `φ ^ k`: on every `Γ`-irreducible subspace `W ⊆ K^n` the eigenvalues of `exp B`
have a single absolute value `r` under `ι`, and `r ^ dim W = ‖ι det (u ^ ℓ ^ N |_W)‖` for
`u = ρ(φ ^ k)`. -/
theorem exists_forall_hasEigenvalue_norm_eq_of_irreducible [IsAlgClosed K] (ι : K →+* ℂ)
    (ρ : Γ →* (Matrix n n K)ˣ) (hρ : Continuous fun g => (ρ g : Matrix n n K))
    (H U : Subgroup Γ) [H.Normal] [U.Normal] (φ : Γ) {k : ℕ} (hk : φ ^ k ∈ U)
    (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hD1 : ∀ ψ : ↥(H ⊓ U) → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
      (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ k * a * (φ ^ k)⁻¹ → ψ b = ψ a) → ψ = 0)
    (hG : ∀ g ∈ (H ⊓ U).map ρ, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    (hu : ‖(ρ (φ ^ k) : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) {N : ℕ} {A B : Matrix n n K}
    (hA : Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ ((H ⊓ U).map ρ)) (hAn : ‖A‖ < (ℓ : ℝ)⁻¹)
    (hBn : ‖B‖ < (ℓ : ℝ)⁻¹) (hBG : ∀ g ∈ (H ⊓ U).map ρ, Commute B (g : Matrix n n K))
    (hBu : Commute B (ρ (φ ^ k) : Matrix n n K)) (hAB : Commute A B)
    (hsum : (ℓ ^ N : ℕ) • ladicLog ℓ (ρ (φ ^ k) : Matrix n n K) = A + B)
    {W : Submodule K (n → K)} (hWΓ : ∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W)
    (hirr : ∀ W' ≤ W, W' ≠ ⊥ → (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W') →
      W' = W) :
    ∃ hz : exp B ∈ stabilizerSubalgebra W,
      ∃ hu' : (ρ (φ ^ k) : Matrix n n K) ^ (ℓ ^ N) ∈ stabilizerSubalgebra W, ∃ r : ℝ,
        (∀ μ, Module.End.HasEigenvalue (stabRestrict (exp B) hz) μ → ‖ι μ‖ = r) ∧
        ‖ι (LinearMap.det (stabRestrict _ hu'))‖ = r ^ Module.finrank K W := by
  set G := (H ⊓ U).map ρ
  set c₀ : Γ := φ ^ (k * ℓ ^ N)
  have hc₀ : (ρ c₀ : Matrix n n K) = (ρ (φ ^ k) : Matrix n n K) ^ (ℓ ^ N) := by
    rw [show c₀ = (φ ^ k) ^ (ℓ ^ N) from pow_mul φ k _, map_pow, Units.val_pow_eq_pow_val]
  have hc₀U : c₀ ∈ U := by
    rw [show c₀ = (φ ^ k) ^ (ℓ ^ N) from pow_mul φ k _]
    exact U.pow_mem hk _
  set T : Set Γ := (H ⊓ U : Set Γ) ∪ {φ ^ k, c₀}
  have hTU : ∀ c ∈ T, c ∈ U := by
    rintro c (hc | rfl | rfl)
    · exact hc.2
    · exact hk
    · exact hc₀U
  set S : Set (Module.End K (n → K)) := (fun c => Matrix.toLin' (ρ c : Matrix n n K)) '' T
  -- `S`-stable subspaces are the subspaces stable under `G` and `u`
  have hSiff : ∀ X : Submodule K (n → K), (∀ s ∈ S, X ≤ X.comap s) ↔
      (∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra X) ∧
        (ρ (φ ^ k) : Matrix n n K) ∈ stabilizerSubalgebra X := by
    intro X
    constructor
    · intro h
      refine ⟨?_, le_comap_toLin'_iff.mp (h _ ⟨φ ^ k, Or.inr (Or.inl rfl), rfl⟩)⟩
      rintro _ ⟨g, hg, rfl⟩
      exact le_comap_toLin'_iff.mp (h _ ⟨g, Or.inl hg, rfl⟩)
    · rintro ⟨hG', hu'⟩ _ ⟨c, hc, rfl⟩
      rw [le_comap_toLin'_iff]
      rcases hc with hc | rfl | rfl
      · exact hG' _ ⟨c, hc, rfl⟩
      · exact hu'
      · rw [hc₀]
        exact Subalgebra.pow_mem _ hu' _
  -- finite determinants on the geometric monodromy
  have hdetfin : ∀ X : Submodule K (n → K), (∀ s ∈ S, X ≤ X.comap s) → ∀ g ∈ G,
      ∃ m : ℕ, 0 < m ∧ ∀ hg : (g : Matrix n n K) ∈ stabilizerSubalgebra X,
        LinearMap.det (stabRestrict (g : Matrix n n K) hg) ^ m = 1 := by
    intro X hX
    obtain ⟨hXG, hXu⟩ := (hSiff X).mp hX
    rintro _ ⟨h, hh, rfl⟩
    exact exists_pow_det_stabRestrict_eq_one ℓ ρ hρ (H ⊓ U) (φ ^ k) hD1
      (fun a ha => hXG _ ⟨a, ha, rfl⟩) hXu hh
  -- `exp B` preserves `S`-stable subspaces and has the determinants of `u ^ ℓ ^ N` there
  have hzst : ∀ X : Submodule K (n → K), (∀ s ∈ S, X ≤ X.comap s) →
      X ≤ X.comap (Matrix.toLin' (exp B)) ∧
        ∃ hz : exp B ∈ stabilizerSubalgebra X,
          ∃ hu' : (ρ (φ ^ k) : Matrix n n K) ^ (ℓ ^ N) ∈ stabilizerSubalgebra X,
            LinearMap.det (stabRestrict _ hu') = LinearMap.det (stabRestrict (exp B) hz) := by
    intro X hX
    obtain ⟨hXG, hXu⟩ := (hSiff X).mp hX
    obtain ⟨-, hz, hu', hdet⟩ := det_stabRestrict_construction hG (MonoidHom.id _) LieHom.id
      (fun _ h => h) (fun g hg => (exp_ladicLog hg).symm) hu hA hAn hBn hBG hAB hsum hXG hXu
      (hdetfin X hX)
    exact ⟨le_comap_toLin'_iff.mpr hz, hz, hu', hdet⟩
  set Γe : Subgroup (Module.End K (n → K))ˣ := (unitsToEnd.comp ρ).range
  -- conjugating an element of `T` by `a` multiplies it by an element of `H ⊓ U`
  have hconjT : ∀ c ∈ T, ∀ a : Γ, ∃ h ∈ H ⊓ U, a⁻¹ * c * a = c * h := fun c hc a =>
    ⟨c⁻¹ * (a⁻¹ * c * a), inv_mul_conj_mem hcomm (hTU c hc) a, by group⟩
  have hρmul : ∀ a b : Γ, Matrix.toLin' (ρ (a * b) : Matrix n n K) =
      Matrix.toLin' (ρ a : Matrix n n K) * Matrix.toLin' (ρ b : Matrix n n K) := fun a b => by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl
  have hnormal : ∀ γ ∈ Γe, ∀ X : Submodule K (n → K), (∀ s ∈ S, X ≤ X.comap s) →
      ∀ s ∈ S, X.map (γ : Module.End K (n → K)) ≤
        (X.map (γ : Module.End K (n → K))).comap s := by
    rintro _ ⟨a, rfl⟩ X hX _ ⟨c, hc, rfl⟩
    obtain ⟨h, hh, hah⟩ := hconjT c hc a
    rintro _ ⟨x, hx, rfl⟩
    have hxh : Matrix.toLin' (ρ h : Matrix n n K) x ∈ X := hX _ ⟨h, Or.inl hh, rfl⟩ hx
    have hxc := hX _ ⟨c, hc, rfl⟩ hxh
    refine ⟨_, hxc, ?_⟩
    simp only [MonoidHom.comp_apply, coe_unitsToEnd]
    have e : a * (c * h) = c * a := by rw [← hah]; group
    have := congrArg (fun g => Matrix.toLin' (ρ g : Matrix n n K) x) e
    simpa only [hρmul, Module.End.mul_apply] using this
  have hconj : ∀ γ ∈ Γe, ∀ (X : Submodule K (n → K)) (hX : ∀ s ∈ S, X ≤ X.comap s)
      (hX' : ∀ s ∈ S, X.map (γ : Module.End K (n → K)) ≤
        (X.map (γ : Module.End K (n → K))).comap s),
      ‖ι (LinearMap.det ((Matrix.toLin' (ρ c₀ : Matrix n n K)).restrict
        (hX' _ ⟨c₀, Or.inr (Or.inr rfl), rfl⟩)))‖ =
      ‖ι (LinearMap.det ((Matrix.toLin' (ρ c₀ : Matrix n n K)).restrict
        (hX _ ⟨c₀, Or.inr (Or.inr rfl), rfl⟩)))‖ := by
    rintro _ ⟨a, rfl⟩ X hX hX'
    obtain ⟨h, hh, hah⟩ := hconjT c₀ (Or.inr (Or.inr rfl)) a
    have hXh := hX _ ⟨h, Or.inl hh, rfl⟩
    have hXc := hX _ ⟨c₀, Or.inr (Or.inr rfl), rfl⟩
    have hXch : X ≤ X.comap (Matrix.toLin' (ρ (c₀ * h) : Matrix n n K)) := by
      rw [hρmul]
      intro x hx
      exact hXc (hXh hx)
    rw [det_restrict_map_unit (f' := Matrix.toLin' (ρ (c₀ * h) : Matrix n n K)) ?_ hXch]
    · have e : (Matrix.toLin' (ρ (c₀ * h) : Matrix n n K)).restrict hXch =
          (Matrix.toLin' (ρ c₀ : Matrix n n K)).restrict hXc *
            (Matrix.toLin' (ρ h : Matrix n n K)).restrict hXh :=
        LinearMap.ext fun x => Subtype.ext (by
          show Matrix.toLin' (ρ (c₀ * h) : Matrix n n K) x = _
          rw [hρmul]
          rfl)
      rw [e, map_mul, map_mul, norm_mul]
      obtain ⟨m, hm, hdm⟩ := hdetfin X hX _ ⟨h, hh, rfl⟩
      have h1 : ‖ι (LinearMap.det ((Matrix.toLin' (ρ h : Matrix n n K)).restrict hXh))‖ = 1 :=
        Complex.norm_eq_one_of_pow_eq_one (by
          rw [← map_pow]
          exact (congrArg ι (hdm (le_comap_toLin'_iff.mp hXh))).trans (map_one ι)) hm.ne'
      rw [h1, mul_one]
    · simp only [MonoidHom.comp_apply, coe_unitsToEnd]
      rw [← hρmul, ← hρmul, ← hah, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hWS : ∀ s ∈ S, W ≤ W.comap s := by
    rintro _ ⟨c, -, rfl⟩
    exact le_comap_toLin'_iff.mpr (hWΓ c)
  have hWΓe : ∀ γ ∈ Γe, W ≤ W.comap (γ : Module.End K (n → K)) := by
    rintro _ ⟨a, rfl⟩
    simp only [MonoidHom.comp_apply, coe_unitsToEnd]
    exact le_comap_toLin'_iff.mpr (hWΓ a)
  have hirr' : ∀ W' ≤ W, W' ≠ ⊥ → (∀ γ ∈ Γe, W' ≤ W'.comap (γ : Module.End K (n → K))) →
      W' = W := by
    intro W' hle hne hst
    refine hirr W' hle hne fun g => le_comap_toLin'_iff.mp ?_
    have := hst _ ⟨g, rfl⟩
    simpa only [MonoidHom.comp_apply, coe_unitsToEnd] using this
  have hdetS : ∀ (X : Submodule K (n → K)) (hX : ∀ s ∈ S, X ≤ X.comap s),
      LinearMap.det ((Matrix.toLin' (ρ c₀ : Matrix n n K)).restrict
        (hX _ ⟨c₀, Or.inr (Or.inr rfl), rfl⟩)) =
      LinearMap.det ((Matrix.toLin' (exp B)).restrict ((hzst X hX).1)) := by
    intro X hX
    obtain ⟨-, hz, hu', hdet⟩ := hzst X hX
    have e1 : (Matrix.toLin' (ρ c₀ : Matrix n n K)).restrict
        (hX _ ⟨c₀, Or.inr (Or.inr rfl), rfl⟩) = stabRestrict _ hu' :=
      LinearMap.ext fun x => Subtype.ext (by
        rw [stabRestrict_apply, LinearMap.restrict_coe_apply, Matrix.toLin'_apply, hc₀])
    rw [e1, hdet]
    rfl
  have hzS : ∀ s ∈ S, Commute (Matrix.toLin' (exp B)) s := by
    rintro _ ⟨c, hc, rfl⟩
    have hBc : Commute B (ρ c : Matrix n n K) := by
      rcases hc with hc | rfl | rfl
      · exact hBG _ ⟨c, hc, rfl⟩
      · exact hBu
      · rw [hc₀]
        exact hBu.pow_right _
    exact commute_toLin' hBc.exp_left
  obtain ⟨r, hr⟩ := exists_forall_hasEigenvalue_restrict_norm_eq ι S Γe
    (U := Matrix.toLin' (ρ c₀ : Matrix n n K)) (z := Matrix.toLin' (exp B))
    ⟨c₀, Or.inr (Or.inr rfl), rfl⟩ hzS (fun X hX => (hzst X hX).1) hdetS hnormal hconj hWS
    hWΓe hirr'
  obtain ⟨-, hz, hu', hdet⟩ := hzst W hWS
  refine ⟨hz, hu', r, fun μ hμ => hr μ hμ, ?_⟩
  rw [hdet]
  exact Stacks.EtaleCohomology.norm_det_restrict_of_le_absEigenPart _
    (Stacks.EtaleCohomology.le_absEigenPart _ hr)

/-- **Determinantal weights of an `ℓ`-adic representation** (Weil II, 1.3, group form).  Let
`ρ : Γ → GL_n(K)` be a continuous representation of a compact group with `K^n` semisimple, `H ⊴ Γ`
with `Γ / H` abelian, `φ ∈ Γ`, and assume that for every open normal `U ⊴ Γ` no nonzero
continuous homomorphism `H ⊓ U → K` is invariant under conjugation by `φ ^ [Γ : U]` (the
geometric input of Weil II, 1.3.4).  Then there are `k > 0`, `N` and a matrix `B`, with
`z = exp B` commuting with `ρ(φ ^ k)` and with a finite-index part `ρ(H ⊓ U)` of the geometric
monodromy, and `ρ(φ ^ k) ^ ℓ ^ N = exp A * z` for some `A` in the Lie algebra of `ρ(H ⊓ U)`, such
that on every `Γ`-irreducible subspace `W ⊆ K^n` the eigenvalues of `z` have a single absolute
value `r` under `ι`, with `r ^ dim W = ‖ι det (ρ(φ ^ k) ^ ℓ ^ N |_W)‖`. -/
theorem exists_monodromy_weights [IsAlgClosed K] (ι : K →+* ℂ) (ρ : Γ →* (Matrix n n K)ˣ)
    (hρ : Continuous fun g => (ρ g : Matrix n n K)) (H : Subgroup Γ) [H.Normal] (φ : Γ)
    (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hD1 : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) →
      ∀ ψ : ↥(H ⊓ U) → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) → ψ = 0)
    (hss : ∀ W : Submodule K (n → K), (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (n → K), IsCompl W W' ∧
        ∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W') :
    ∃ U : Subgroup Γ, U.Normal ∧ IsOpen (U : Set Γ) ∧ 0 < U.index ∧
      (∀ g ∈ (H ⊓ U).map ρ, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) ∧
      ‖(ρ (φ ^ U.index) : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹ ∧
      ∃ N : ℕ, ∃ A B : Matrix n n K,
        Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ ((H ⊓ U).map ρ) ∧ ‖A‖ < (ℓ : ℝ)⁻¹ ∧
        ‖B‖ < (ℓ : ℝ)⁻¹ ∧ (∀ g ∈ (H ⊓ U).map ρ, Commute B (g : Matrix n n K)) ∧
        Commute B (ρ (φ ^ U.index) : Matrix n n K) ∧ Commute A B ∧
        (ℓ ^ N : ℕ) • ladicLog ℓ (ρ (φ ^ U.index) : Matrix n n K) = A + B ∧
        ∀ W : Submodule K (n → K), (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W) →
          (∀ W' ≤ W, W' ≠ ⊥ → (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W') →
            W' = W) →
          ∃ hz : exp B ∈ stabilizerSubalgebra W,
            ∃ hu' : (ρ (φ ^ U.index) : Matrix n n K) ^ (ℓ ^ N) ∈ stabilizerSubalgebra W,
              ∃ r : ℝ, (∀ μ, Module.End.HasEigenvalue (stabRestrict (exp B) hz) μ →
                ‖ι μ‖ = r) ∧ ‖ι (LinearMap.det (stabRestrict _ hu'))‖ = r ^ Module.finrank K W := by
  obtain ⟨U, hUn, hUo, -, hG, hu, -, -, N, A, B, hA, hAn, hBn, hBG, hBu, hAB, hsum, -⟩ :=
    exists_monodromy_decomposition (ℓ := ℓ) ρ hρ H φ hss
  have := hUn
  have : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUo
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact ⟨U, hUn, hUo, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, hG, hu, N, A, B,
    hA, hAn, hBn, hBG, hBu, hAB, hsum, fun W hWΓ hirr =>
      exists_forall_hasEigenvalue_norm_eq_of_irreducible ι ρ hρ H U φ (U.pow_index_mem φ) hcomm
        (hD1 U hUn hUo) hG hu hA hAn hBn hBG hBu hAB hsum hWΓ hirr⟩

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- **Eigenvalue bounds from the irreducible constituents.**  If `K^n` is semisimple under `ρ`
and on every `Γ`-irreducible subspace the eigenvalues of `Z` (which preserves it) satisfy
`a ≤ ‖ι μ‖ ≤ b`, then every eigenvalue of `Z` does. -/
theorem eigenNormIn_of_forall_irreducible (ι : K →+* ℂ) (ρ : Γ →* (Matrix n n K)ˣ)
    (hss : ∀ W : Submodule K (n → K), (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (n → K), IsCompl W W' ∧
        ∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W')
    {Z : Matrix n n K} {a b : ℝ}
    (hW : ∀ W : Submodule K (n → K), W ≠ ⊥ →
      (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W) →
      (∀ W' ≤ W, W' ≠ ⊥ → (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W') → W' = W) →
      ∃ hz : Z ∈ stabilizerSubalgebra W, ∀ μ,
        Module.End.HasEigenvalue (stabRestrict Z hz) μ → a ≤ ‖ι μ‖ ∧ ‖ι μ‖ ≤ b) :
    EigenNormIn ι Z a b := by
  set S : Set (Module.End K (n → K)) := Set.range fun g => Matrix.toLin' (ρ g : Matrix n n K)
  have hSiff : ∀ X : Submodule K (n → K), Stacks.EtaleCohomology.IsStableUnder S X ↔
      ∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra X := by
    intro X
    refine ⟨fun h g => le_comap_toLin'_iff.mp (h _ ⟨g, rfl⟩), ?_⟩
    rintro h _ ⟨g, rfl⟩
    exact le_comap_toLin'_iff.mpr (h g)
  have htop := Stacks.EtaleCohomology.sSup_isIrreducibleUnder_eq_top (S := S) fun X hX => by
    obtain ⟨X', hc, hX'⟩ := hss X ((hSiff X).mp hX)
    exact ⟨X', hc, (hSiff X').mpr hX'⟩
  have hT : ∀ X ∈ {X | Stacks.EtaleCohomology.IsIrreducibleUnder S X},
      ∃ hz : Z ∈ stabilizerSubalgebra X, ∀ μ,
        Module.End.HasEigenvalue (stabRestrict Z hz) μ → a ≤ ‖ι μ‖ ∧ ‖ι μ‖ ≤ b := by
    intro X hX
    exact hW X hX.1 ((hSiff X).mp hX.2.1) fun W' hle hne hW' =>
      (hX.2.2 W' hle ((hSiff W').mpr hW')).resolve_left hne
  intro μ hμ
  obtain ⟨X, hX, hμX⟩ := exists_hasEigenvalue_restrict_of_sSup_eq_top htop
    (fun X hX => le_comap_toLin'_iff.mpr (hT X hX).1) hμ
  exact (hT X hX).2 μ hμX

omit [CharZero K] [CompleteSpace K] in
/-- The determinant of a matrix on the line spanned by one of its eigenvectors is the
eigenvalue. -/
theorem det_stabRestrict_span_singleton {M : Matrix m m K} {v : m → K} (hv : v ≠ 0) {lam : K}
    (hMv : M *ᵥ v = lam • v) (hM : M ∈ stabilizerSubalgebra (K ∙ v)) :
    LinearMap.det (stabRestrict M hM) = lam := by
  have e : stabRestrict M hM = lam • LinearMap.id := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.2
    rw [stabRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul, ← hc,
      Matrix.mulVec_smul, hMv, smul_comm]
  rw [e, LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_span_singleton hv, pow_one]

/-- **Frobenius on the geometric invariants of a tensor construction** (the group-theoretic core
of Weil II, 1.5.2 and 1.8.1: the weights of `H⁰(X̄, -)` are bounded by the determinantal weights).
In the situation of `Stacks.LAdic.TensorConstruction.norm_det_pow_mem_Icc`, a vector fixed by
`C.R G` on which `C.R u` acts by `λ` satisfies `a ≤ ‖ι λ‖ ^ ℓ ^ N ≤ b` whenever the eigenvalues
of `C.R (exp B)` lie in `[a, b]`. -/
theorem TensorConstruction.norm_pow_mem_Icc_of_invariant [IsAlgClosed K]
    (C : TensorConstruction ℓ K n m) (ι : K →+* ℂ)
    {G : Subgroup (Matrix n n K)ˣ} (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    {u : (Matrix n n K)ˣ} (hu : ‖(u : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) {N : ℕ}
    {A B : Matrix n n K} (hA : Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ G)
    (hAn : ‖A‖ < (ℓ : ℝ)⁻¹) (hBn : ‖B‖ < (ℓ : ℝ)⁻¹)
    (hBG : ∀ g ∈ G, Commute B (g : Matrix n n K)) (hAB : Commute A B)
    (hsum : (ℓ ^ N : ℕ) • ladicLog ℓ (u : Matrix n n K) = A + B)
    {z : (Matrix n n K)ˣ} (hz : (z : Matrix n n K) = exp B) {a b : ℝ} (ha : 0 ≤ a)
    (hab : EigenNormIn ι (C.R z : Matrix m m K) a b) {v : m → K} (hv : v ≠ 0)
    (hGv : ∀ g ∈ G, (C.R g : Matrix m m K) *ᵥ v = v) {lam : K}
    (huv : (C.R u : Matrix m m K) *ᵥ v = lam • v) :
    a ≤ ‖ι lam‖ ^ (ℓ ^ N) ∧ ‖ι lam‖ ^ (ℓ ^ N) ≤ b := by
  have hspan : ∀ (M : Matrix m m K) (c : K), M *ᵥ v = c • v → M ∈ stabilizerSubalgebra (K ∙ v) := by
    intro M c hMv w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [Matrix.mulVec_smul, hMv]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  have hGv' : ∀ g ∈ G, (C.R g : Matrix m m K) *ᵥ v = (1 : K) • v := fun g hg => by
    rw [hGv g hg, one_smul]
  have hGW : ∀ g ∈ G, (C.R g : Matrix m m K) ∈ stabilizerSubalgebra (K ∙ v) := fun g hg =>
    hspan _ _ (hGv' g hg)
  have huW := hspan _ _ huv
  have hdetW : ∀ g ∈ G, ∃ k : ℕ, 0 < k ∧ ∀ hg : (C.R g : Matrix m m K) ∈
      stabilizerSubalgebra (K ∙ v), LinearMap.det (stabRestrict (C.R g : Matrix m m K) hg) ^ k =
        1 := fun g hg => ⟨1, one_pos, fun hg' => by
    rw [det_stabRestrict_span_singleton hv (hGv' g hg) hg', one_pow]⟩
  have hu' : (C.R u : Matrix m m K) ^ (ℓ ^ N) ∈ stabilizerSubalgebra (K ∙ v) :=
    Subalgebra.pow_mem _ huW _
  have hpow : ∀ j : ℕ, (C.R u : Matrix m m K) ^ j *ᵥ v = lam ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← Matrix.mulVec_mulVec, huv, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  have h := C.norm_det_pow_mem_Icc ι hG hu hA hAn hBn hBG hAB hsum hz ha hab hGW huW hdetW hu'
  rwa [det_stabRestrict_span_singleton hv (hpow _) hu', finrank_span_singleton hv, pow_one,
    pow_one, map_pow, norm_pow] at h

/-- **Determinantal weights at Frobenius elements** (Weil II, 1.3, group form).  Under the
hypotheses of `Stacks.LAdic.exists_monodromy_weights` there are `k > 0`, `N` and `B`, with
`exp B` commuting with `ρ(φ ^ k)`, such that on every `Γ`-irreducible `W ⊆ K^n` the eigenvalues of
`exp B` have a single absolute value `r` under `ι`, and every `g ∈ φ ^ d H` (a Frobenius element
at a point of degree `d`) satisfies `‖ι det (ρ g |_W)‖ ^ (k ℓ ^ N) = r ^ (d dim W)`. -/
theorem exists_monodromy_weights_frobenius [IsAlgClosed K] (ι : K →+* ℂ)
    (ρ : Γ →* (Matrix n n K)ˣ) (hρ : Continuous fun g => (ρ g : Matrix n n K)) (H : Subgroup Γ)
    [H.Normal] (φ : Γ) (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hD1 : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) →
      ∀ ψ : ↥(H ⊓ U) → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) → ψ = 0)
    (hss : ∀ W : Submodule K (n → K), (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (n → K), IsCompl W W' ∧
        ∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W') :
    ∃ k : ℕ, 0 < k ∧ ∃ N : ℕ, ∃ B : Matrix n n K, ‖B‖ < (ℓ : ℝ)⁻¹ ∧
      Commute B (ρ (φ ^ k) : Matrix n n K) ∧
      ∀ W : Submodule K (n → K), ∀ hW : (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W),
        (∀ W' ≤ W, W' ≠ ⊥ → (∀ g, (ρ g : Matrix n n K) ∈ stabilizerSubalgebra W') →
          W' = W) →
        ∃ hz : exp B ∈ stabilizerSubalgebra W, ∃ r : ℝ,
          (∀ μ, Module.End.HasEigenvalue (stabRestrict (exp B) hz) μ → ‖ι μ‖ = r) ∧
          ∀ (g : Γ) (d : ℕ), (φ ^ d)⁻¹ * g ∈ H →
            ‖ι (detCharacter ρ hW g)‖ ^ (k * ℓ ^ N) = r ^ (d * Module.finrank K W) := by
  obtain ⟨U, -, -, hk, -, -, N, -, B, -, -, hBn, -, hBu, -, -, hW⟩ :=
    exists_monodromy_weights (ℓ := ℓ) ι ρ hρ H φ hcomm hD1 hss
  -- the geometric input for `H` itself is the case `U = Γ`
  have hH : ∀ ψ : H → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
      (∀ a b : H, (b : Γ) = φ * a * φ⁻¹ → ψ b = ψ a) → ψ = 0 := by
    intro ψ hadd hcont hinv
    have hmem : ∀ a : ↥(H ⊓ ⊤), (a : Γ) ∈ H := fun a => a.2.1
    set ψ' : ↥(H ⊓ ⊤) → K := fun a => ψ ⟨a, hmem a⟩
    have h0 := hD1 ⊤ inferInstance isOpen_univ ψ'
      (fun a b => hadd ⟨a, hmem a⟩ ⟨b, hmem b⟩)
      (hcont.comp (continuous_subtype_val.subtype_mk _))
      (fun a b hab => hinv _ _ (by rwa [Subgroup.index_top, pow_one] at hab))
    funext a
    exact congrFun h0 ⟨a, a.2, Subgroup.mem_top _⟩
  refine ⟨U.index, hk, N, B, hBn, hBu, fun W hWΓ hirr => ?_⟩
  obtain ⟨hz, hu', r, hr, hdet⟩ := hW W hWΓ hirr
  refine ⟨hz, r, hr, fun g d hg => ?_⟩
  have e1 : LinearMap.det (stabRestrict _ hu') = detCharacter ρ hWΓ (φ ^ (U.index * ℓ ^ N)) := by
    show _ = LinearMap.det (stabRestrict _ (hWΓ _))
    rw [stabRestrict_congr (show (ρ (φ ^ U.index) : Matrix n n K) ^ (ℓ ^ N) =
      (ρ (φ ^ (U.index * ℓ ^ N)) : Matrix n n K) by
        rw [pow_mul, map_pow ρ (φ ^ U.index), Units.val_pow_eq_pow_val]) hu' (hWΓ _)]
  rw [e1, map_pow, map_pow, norm_pow] at hdet
  rw [norm_detCharacter_eq_pow ℓ ι ρ hρ H φ hH hWΓ hg, ← pow_mul, mul_comm d, pow_mul, hdet,
    ← pow_mul, mul_comm (Module.finrank K W)]

end Weights

end Stacks.LAdic
