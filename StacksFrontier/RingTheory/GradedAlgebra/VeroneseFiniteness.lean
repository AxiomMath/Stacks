module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.Noetherian
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseGrading
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness over a Veronese subring

Let `A = ⨁_{i ≥ 0} 𝒜 i` be a graded ring generated over its degree-zero part by finitely many
homogeneous elements `f₁, …, f_r` of positive degrees `deg₁, …, deg_r`, and let `d` be the least
common multiple of those degrees. Then `A` is a finite module over the Veronese subring `A⁽ᵈ⁾`:
each `fᵢ ^ (d / degᵢ)` is homogeneous of degree `d`, hence lies in `A⁽ᵈ⁾`, so every `fᵢ` is
integral over `A⁽ᵈ⁾` and the adjunction of finitely many integral elements is finite.

If moreover `A` is Noetherian then `A⁽ᵈ⁾` is Noetherian, by the Artin–Tate lemma applied to the
tower `𝒜 0 ⊆ A⁽ᵈ⁾ ⊆ A`, and the Veronese part `T⁽ᵈ⁾` of every finite graded `A`-module `T` is a
finite `A⁽ᵈ⁾`-module.

## Main results

* `Stacks.Veronese.finite_veroneseSubring`: the graded ring is finite over its Veronese subring.
* `Stacks.Veronese.isNoetherianRing_veroneseSubring`: the Veronese subring is Noetherian.
* `Stacks.Veronese.finite_veroneseSubmodule`: the Veronese part of a finite graded module is
  finite over the Veronese subring.

## Implementation notes

The Veronese subring and the Veronese part of a graded module are
`Stacks.Veronese.veroneseSubring` and `Stacks.Veronese.veroneseSubmodule`; the restriction of
scalars making an `A`-module an `A⁽ᵈ⁾`-module is the instance
`Stacks.Veronese.veroneseModule`. A graded module is represented by an internal direct-sum
decomposition indexed by `ℤ`, compatible with the `ℕ`-grading on the ring through the `VAdd ℕ ℤ`
instance `Stacks.Veronese.instVAddNatInt`.

The degree-zero subring appears in two guises: `Stacks.Veronese.gradeZero 𝒜`, a `Subring A`, which
is what the generation hypothesis is phrased with, and `𝒜 0`, which is what the Noetherian
criterion for a graded ring produces. They are transported into each other by the evident ring
isomorphism.

## References

* [Stacks Project, Tag 00JW](https://stacks.math.columbia.edu/tag/00JW)
* [Stacks Project, Tag 00IS](https://stacks.math.columbia.edu/tag/00IS)
-/

@[expose] public section

namespace Stacks.Veronese

variable {A : Type*} [CommRing A]
variable {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-zero subring lies in every Veronese subring. -/
private theorem gradeZero_le_veroneseSubring (d : ℕ) :
    gradeZero 𝒜 ≤ veroneseSubring 𝒜 d := fun _ hx =>
  mem_veroneseSubring_of_mem 𝒜 (n := 0) (by rwa [zero_mul])

/-- A graded ring generated over its degree-zero part by positive-degree homogeneous elements is
finite over the Veronese subring associated with the least common multiple of their degrees. -/
public lemma finite_veroneseSubring {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hdeg : ∀ i, 0 < deg i) (hf : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤) :
    Module.Finite (veroneseSubring 𝒜 (Finset.univ.lcm deg)) A := by
  classical
  let d := Finset.univ.lcm deg
  let V := veroneseSubring 𝒜 d
  have hdvd (i : Fin r) : deg i ∣ d := Finset.dvd_lcm (Finset.mem_univ i)
  have hpow (i : Fin r) : f i ^ (d / deg i) ∈ V :=
    mem_veroneseSubring_of_mem 𝒜 (n := 1) (by
      simpa only [one_mul, Nat.div_mul_cancel (hdvd i)] using
        pow_mem_grade 𝒜 f deg hf i (d / deg i))
  have hdpos : 0 < d := by
    simp [d, Nat.pos_iff_ne_zero, ne_of_gt (hdeg _)]
  have hint (i : Fin r) : IsIntegral V (f i) :=
    IsIntegral.of_pow (Nat.div_pos (Nat.le_of_dvd hdpos (hdvd i)) (hdeg i))
      (isIntegral_algebraMap (x := (⟨_, hpow i⟩ : V)))
  have hadjoin : Algebra.adjoin V (Set.range f) = ⊤ :=
    eq_top_iff.2 fun x _ =>
      Algebra.adjoin_induction (p := fun x _ => x ∈ Algebra.adjoin V (Set.range f))
      (fun _ hx => Algebra.subset_adjoin hx)
      (fun (a : gradeZero 𝒜) => (Algebra.adjoin V (Set.range f)).algebraMap_mem
        ⟨a, gradeZero_le_veroneseSubring 𝒜 d a.2⟩)
      (fun _ _ _ _ hx hy => add_mem hx hy) (fun _ _ _ _ hx hy => mul_mem hx hy)
      (by simp [hgen])
  have := Algebra.finite_adjoin_of_finite_of_isIntegral
    (R := V) (A := A) (Set.finite_range f) (Set.forall_mem_range.2 hint)
  exact Module.Finite.of_surjective
    (Subalgebra.val (Algebra.adjoin V (Set.range f))).toLinearMap fun x =>
      ⟨⟨x, by simp [hadjoin]⟩, rfl⟩

/-- The Veronese subring associated with the least common multiple of the degrees of positive
homogeneous generators of a Noetherian graded ring is Noetherian. -/
public lemma isNoetherianRing_veroneseSubring [IsNoetherianRing A]
    {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hdeg : ∀ i, 0 < deg i) (hf : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤) :
    IsNoetherianRing (veroneseSubring 𝒜 (Finset.univ.lcm deg)) := by
  classical
  let R := gradeZero 𝒜
  let d := Finset.univ.lcm deg
  let V := veroneseSubring 𝒜 d
  have hR0 : IsNoetherianRing (𝒜 0) :=
    (GradedRing.isNoetherianRing_iff_isNoetherianRing_gradeZero_and_irrelevant_fg 𝒜).mp
      ‹IsNoetherianRing A› |>.1
  let e : R ≃+* 𝒜 0 :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv (𝒜 0) e.symm
  have hRV : (R : Subring A) ≤ V := gradeZero_le_veroneseSubring 𝒜 d
  let : Algebra R V := (Subring.inclusion hRV).toAlgebra
  let : Algebra V A := V.subtype.toAlgebra
  have : IsScalarTower R V A := ⟨fun _ _ _ => mul_assoc _ _ _⟩
  have : Algebra.FiniteType R V :=
    ⟨_root_.fg_of_fg_of_fg (A := R) (B := V) (C := A)
      (Subalgebra.fg_def.2 ⟨_, Set.finite_range f, hgen⟩)
      (finite_veroneseSubring 𝒜 f deg hdeg hf hgen).fg_top Subtype.val_injective⟩
  exact Algebra.FiniteType.isNoetherianRing R V

/-- For a finite graded module, the sum of the homogeneous pieces in degrees divisible by the
least common multiple of the degrees of positive homogeneous ring generators is finite over the
corresponding Veronese subring. -/
@[ega "II 2.1.6" "(iii), special case"]
public lemma finite_veroneseSubmodule [IsNoetherianRing A]
    {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hdeg : ∀ i, 0 < deg i) (hf : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤)
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (ℳ : ℤ → AddSubgroup M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] :
    Module.Finite (veroneseSubring 𝒜 (Finset.univ.lcm deg))
      (veroneseSubmodule 𝒜 ℳ (Finset.univ.lcm deg)) := by
  let V := veroneseSubring 𝒜 (Finset.univ.lcm deg)
  have : IsNoetherianRing V := isNoetherianRing_veroneseSubring 𝒜 f deg hdeg hf hgen
  have hst : IsScalarTower V A M := ⟨fun _ _ _ => mul_smul _ _ _⟩
  have : Module.Finite V M := @Module.Finite.trans V A M _ _ _ _ _ _ hst
    (finite_veroneseSubring 𝒜 f deg hdeg hf hgen) inferInstance
  exact Module.IsNoetherian.finite V _

end Stacks.Veronese
