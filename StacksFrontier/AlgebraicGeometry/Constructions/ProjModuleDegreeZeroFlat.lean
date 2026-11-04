module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureSheaf
public import StacksFrontier.RingTheory.Flat.DirectLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of the degree-zero localization of a graded module

Let `A` be an `ℕ`-graded ring, `M` an `ℤ`-graded `A`-module, and `f ∈ A_d` a homogeneous element.
The degree-zero part `M_(f)` of the localization of `M` away from `f` is spanned over `A_(f)` by
the fractions `x / f^n` with `x` homogeneous of degree `n • d`, and every element of it is such a
fraction.

If moreover `M` is a module over a base ring `R` whose action is compatible with that of `A`
through a map `R → A_0`, then `M_(f)` is the direct limit of the pieces `M_{n • d}` along
multiplication by `f`, so `M_(f)` is a flat `R`-module as soon as those pieces are flat for all
large `n`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroFraction_surjective`: every element of the
  degree-zero localization is a homogeneous fraction.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.flat_degreeZeroLocalization`: the degree-zero
  localization is flat over the base ring when the graded pieces of all large degrees are.

## References

* [Stacks Project, Tag 0D4C](https://stacks.math.columbia.edu/tag/0D4C)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 05UT](https://stacks.math.columbia.edu/tag/05UT)
-/

@[expose] public noncomputable section

open DirectSum

universe u v w

/-- The grading action of natural-number ring degrees on integer module degrees, by addition. -/
local instance natVAddIntDegree : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

/-- The degree action adds the cast. -/
private theorem nat_vadd_int (n : ℕ) (z : ℤ) : n +ᵥ z = (n : ℤ) + z := vadd_nat_int n z

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A M σ τ : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ)
  [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒜 𝒨]

/-- Multiplying by `f ^ k` with `f ∈ A_d` raises the degree of a homogeneous element by `k • d`. -/
private theorem pow_smul_mem_nsmul {ι : Type*} [SetLike ι M] (ℬ : ℤ → ι) [SetLike.GradedSMul 𝒜 ℬ]
    {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) {n m k : ℕ} (h : m = k + n)
    {a : M} (ha : a ∈ ℬ (n • (d : ℤ))) : f ^ k • a ∈ ℬ (m • (d : ℤ)) := by
  subst h
  convert SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℬ) (SetLike.pow_mem_graded k hf) ha using 1
  simp [Nat.cast_mul, add_mul]

/-- Every element of the degree-zero localization `M_(f)` of a graded module is a fraction
`x / f^n` with `x` homogeneous of degree `n • d`. -/
@[ega "II 2.2.7" "special case"]
public theorem degreeZeroFraction_surjective {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :
    ∃ n m hm, degreeZeroFraction 𝒜 𝒨 hf n m hm = z := by
  classical
  let _ := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := A) f M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  suffices ∃ (n : ℕ) (m : M) (hm : m ∈ 𝒨 (n • (d : ℤ))),
      (z : LocalizedModule.Away f M) =
        LocalizedModule.mk (S := Submonoid.powers f) m ⟨f ^ n, ⟨n, rfl⟩⟩ by
    obtain ⟨n, m, hm, he⟩ := this
    exact ⟨n, m, hm, Subtype.ext he.symm⟩
  by_cases hf0 : f = 0
  · let _ : Subsingleton (LocalizedModule.Away f M) :=
      LocalizedModule.subsingleton ⟨1, by simpa using hf0⟩
    exact ⟨0, 0, zero_mem _, Subsingleton.elim _ _⟩
  have hspan := z.2
  change (z : LocalizedModule.Away f M) ∈ Submodule.span _ _ at hspan
  generalize (z : LocalizedModule.Away f M) = x at hspan ⊢
  induction hspan using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨e, n, hfe, m, hm, rfl⟩ := hx
      obtain rfl := DirectSum.degree_eq_of_mem_mem 𝒜 hfe hf hf0
      exact ⟨n, m, hm, rfl⟩
  | zero => exact ⟨0, 0, zero_mem _, (LocalizedModule.zero_mk _).symm⟩
  | add x y _ _ hx hy =>
      obtain ⟨n, a, ha, rfl⟩ := hx
      obtain ⟨m, b, hb, rfl⟩ := hy
      refine ⟨n + m, f ^ m • a + f ^ n • b, ?_, ?_⟩
      · exact add_mem (pow_smul_mem_nsmul 𝒜 𝒨 hf (Nat.add_comm n m) ha)
          (pow_smul_mem_nsmul 𝒜 𝒨 hf rfl hb)
      · rw [LocalizedModule.mk_add_mk]
        congr 1
        exact Subtype.ext (pow_add f n m).symm
  | smul c x _ hx =>
      obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf c
      obtain ⟨m, b, hb, rfl⟩ := hx
      refine ⟨n + m, a • b, ?_, ?_⟩
      · convert SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒨) ha hb using 1
        simp [Nat.cast_mul, add_mul]
      · show (HomogeneousLocalization.Away.mk 𝒜 hf n a ha).val •
          LocalizedModule.mk (S := Submonoid.powers f) b ⟨f ^ m, ⟨m, rfl⟩⟩ = _
        rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
        congr 1
        exact Subtype.ext (pow_add f n m).symm

/-- Let the base ring `R` act on `M` through `φ : R → A_0`, and let `f ∈ A_d`. If for every `n`
the graded piece `M_{(N + n) • d}`, given as the `R`-submodule `G n` of `M`, is flat over `R`,
then the degree-zero localization `M_(f)` is flat over `R`. -/
public theorem flat_degreeZeroLocalization {R : Type*} [CommRing R] (φ : R →+* 𝒜 0)
    {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (N : ℕ)
    (G : ℕ → @Submodule R M _ _ (Module.compHom M ((algebraMap (𝒜 0) A).comp φ)))
    (hG : ∀ n x, x ∈ G n ↔ x ∈ 𝒨 ((N + n) • (d : ℤ)))
    (hflat : ∀ n, Module.Flat R (G n)) :
    letI : Module R (GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :=
      Module.compHom _ ((HomogeneousLocalization.fromZeroRingHom 𝒜
        (Submonoid.powers f)).comp φ)
    Module.Flat R (GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) := by
  classical
  let _ : Module R M := Module.compHom M ((algebraMap (𝒜 0) A).comp φ)
  let P : Type _ := GradedModuleDegreeZeroLocalization 𝒜 𝒨 f
  let _ : Module R P := Module.compHom _
    ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp φ)
  let T : ∀ i j : ℕ, i ≤ j → G i →ₗ[R] G j := fun i j hij =>
    { toFun := fun x => ⟨f ^ (j - i) • (x : M), (hG j _).mpr
        (pow_smul_mem_nsmul 𝒜 𝒨 hf (by omega) ((hG i _).mp x.2))⟩
      map_add' := fun x y => Subtype.ext (smul_add _ _ _)
      map_smul' := fun r x => Subtype.ext (by
        show f ^ (j - i) • ((φ r : A) • (x : M)) = (φ r : A) • f ^ (j - i) • (x : M)
        rw [smul_smul, smul_smul, mul_comm]) }
  let _ : DirectedSystem (fun i => G i) (fun i j h => T i j h) := by
    refine ⟨fun i x => Subtype.ext (by simp [T]), fun k j i hij hjk x => Subtype.ext ?_⟩
    show f ^ (k - j) • f ^ (j - i) • (x : M) = f ^ (k - i) • (x : M)
    rw [smul_smul, ← pow_add, show k - j + (j - i) = k - i by omega]
  let g : ∀ i, G i →ₗ[R] P := fun i =>
    { toFun := fun x => degreeZeroFraction 𝒜 𝒨 hf (N + i) (x : M) ((hG i _).mp x.2)
      map_add' := by
        intro x y
        refine Subtype.ext ?_
        show LocalizedModule.mk (S := Submonoid.powers f) ((x : M) + y) _ =
          LocalizedModule.mk (x : M) _ + LocalizedModule.mk (y : M) _
        rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
        exact ⟨1, by simp [Submonoid.smul_def, smul_add, smul_smul]⟩
      map_smul' := by
        intro r x
        refine Subtype.ext ?_
        show LocalizedModule.mk (S := Submonoid.powers f) ((φ r : A) • (x : M)) _ =
          (Localization.mk (φ r : A) 1 : Localization (Submonoid.powers f)) •
            LocalizedModule.mk (S := Submonoid.powers f) (x : M) _
        rw [LocalizedModule.mk_smul_mk, one_mul] }
  have hg : ∀ i j (h : i ≤ j) (x : G i), g j (T i j h x) = g i x := by
    intro i j hij x
    refine Subtype.ext ?_
    show LocalizedModule.mk (S := Submonoid.powers f) (f ^ (j - i) • (x : M))
        ⟨f ^ (N + j), ⟨N + j, rfl⟩⟩ =
      LocalizedModule.mk (S := Submonoid.powers f) (x : M) ⟨f ^ (N + i), ⟨N + i, rfl⟩⟩
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_smul, ← pow_add]
    rw [show N + i + (j - i) = N + j by omega]
  let q := Module.DirectLimit.lift R ℕ (fun i => G i) T g hg
  have hq (i) (x : G i) : q (Module.DirectLimit.of R ℕ (fun i => G i) T i x) = g i x :=
    Module.DirectLimit.lift_of g hg x
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨n, a, ha, rfl⟩ := degreeZeroFraction_surjective 𝒜 𝒨 hf z
    have hmem : f ^ N • a ∈ G n := (hG n _).mpr (pow_smul_mem_nsmul 𝒜 𝒨 hf rfl ha)
    refine ⟨Module.DirectLimit.of R ℕ (fun i => G i) T n ⟨f ^ N • a, hmem⟩, ?_⟩
    rw [hq]
    refine Subtype.ext ?_
    show LocalizedModule.mk (S := Submonoid.powers f) (f ^ N • a)
        ⟨f ^ (N + n), ⟨N + n, rfl⟩⟩ =
      LocalizedModule.mk (S := Submonoid.powers f) a ⟨f ^ n, ⟨n, rfl⟩⟩
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_smul, ← pow_add]
    rw [Nat.add_comm n N]
  have hinj : Function.Injective q := by
    refine (injective_iff_map_eq_zero q).mpr fun z hz => ?_
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    rw [hq] at hz
    have he := congrArg Subtype.val hz
    change LocalizedModule.mk (S := Submonoid.powers f) (x : M)
      ⟨f ^ (N + i), ⟨N + i, rfl⟩⟩ = 0 at he
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at he
    obtain ⟨a, ha⟩ := he
    obtain ⟨k, hk⟩ := a.2
    change f ^ k = (a : A) at hk
    have ht : T i (i + k) (Nat.le_add_right i k) x = 0 := by
      refine Subtype.ext ?_
      show f ^ (i + k - i) • (x : M) = 0
      rw [Nat.add_sub_cancel_left, hk]
      simpa only [one_smul, smul_zero, Submonoid.smul_def] using ha
    rw [← Module.DirectLimit.of_f (hij := Nat.le_add_right i k), ht, map_zero]
  let _ : ∀ i, Module.Flat R (G i) := hflat
  exact (Module.Flat.equiv_iff (LinearEquiv.ofBijective q ⟨hinj, hsurj⟩)).mp
    (colimit_flat_of_flat (fun i => G i) T)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
