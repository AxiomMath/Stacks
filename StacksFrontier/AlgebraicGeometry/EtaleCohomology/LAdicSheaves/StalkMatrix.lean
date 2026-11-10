module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FrobeniusStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFiniteness

/-!
# The ℓ-adic stalk from compatible trivialisations of the finite-level stalks

Let `F` be an ℓ-adic sheaf and `x̄` a geometric point. If every finite-level stalk `F_{n, x̄}` is
identified with `(ℤ/ℓ^{n+1}ℤ)^r`, compatibly with the transition maps and reduction, then the
ℓ-adic stalk `F_x̄ = lim_n F_{n, x̄}` is `ℤ_ℓ^r`. If moreover an endomorphism `a` of `x̄` acts on
each finite-level stalk by the reduction of one matrix `M ∈ M_r(ℤ_ℓ)`, then it acts on the
ℓ-adic stalk by `M`, and its characteristic polynomial on the rational stalk is that of `M`.

## Main results

* `Stacks.EtaleCohomology.exists_toZModPow_eq`: a compatible family of residues modulo the
  powers `ℓ ^ (n + 1)` comes from an ℓ-adic integer.
* `Stacks.EtaleCohomology.LAdicSheaf.stalkEquivOfLevel`: the ℓ-adic stalk is `ℤ_ℓ^r`.
* `Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkEnd_of_level`: the characteristic
  polynomial of `a` on the rational stalk is that of `M`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

section Residues

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **A compatible family of residues modulo `ℓ ^ (n + 1)` comes from an ℓ-adic integer.** -/
public theorem exists_toZModPow_eq (a : ∀ n : ℕ, ZMod (ℓ ^ (n + 1)))
    (ha : ∀ n, levelRingHom (n + 1) (a (n + 1)) = a n) :
    ∃ t : ℤ_[ℓ], ∀ n, PadicInt.toZModPow (n + 1) t = a n := by
  let seq : ℕ → ℤ := fun n => if n = 0 then 0 else ((a (n - 1)).val : ℤ)
  have hdvd : ∀ n, (ℓ : ℤ) ^ (n + 1) ∣ ((a (n + 1)).val : ℤ) - ((a n).val : ℤ) := by
    intro n
    have hcast := ha n
    have hnat : ((a (n + 1)).val : ZMod (ℓ ^ (n + 1))) = (a n).val := by
      rw [← ZMod.natCast_zmod_val (a (n + 1)), ← ZMod.natCast_zmod_val (a n)] at hcast
      simpa [levelRingHom, ZMod.castHom_apply] using hcast
    have hh : (((a (n + 1)).val : ℤ) : ZMod (ℓ ^ (n + 1))) = ((a n).val : ℤ) := by
      exact_mod_cast hnat
    obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hh
    refine ⟨-c, ?_⟩
    have hneg : ((a (n + 1)).val : ℤ) - ((a n).val : ℤ) =
        -(((a n).val : ℤ) - ((a (n + 1)).val : ℤ)) := by ring
    rw [hneg, hc]
    push_cast
    ring_nf
  have hseq : ∀ i, (ℓ : ℤ) ^ i ∣ seq (i + 1) - seq i := by
    intro i
    cases i with
    | zero => simp [seq]
    | succ i => simpa [seq] using hdvd i
  refine ⟨PadicInt.ofIntSeq seq (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub seq ℓ hseq),
    fun n => ?_⟩
  have h := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub seq ℓ hseq (n + 1)
  simpa [seq, ZMod.natCast_zmod_val] using h

/-- Two ℓ-adic integers with the same residues modulo every `ℓ ^ (n + 1)` are equal. -/
public theorem eq_of_toZModPow_succ_eq {s t : ℤ_[ℓ]}
    (h : ∀ n, PadicInt.toZModPow (n + 1) s = PadicInt.toZModPow (n + 1) t) : s = t := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
    have : Subsingleton (ZMod (ℓ ^ 0)) := by
      rw [show ℓ ^ 0 = 1 by simp]
      infer_instance
    exact Subsingleton.elim _ _
  | succ n => exact h n

end Residues

section Sheaf

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime] {r : ℕ}

variable {B X ℓ} in
/-- Trivialisations of the finite-level stalks compatible with the transitions. -/
public structure LAdicSheaf.LevelTrivialization (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1)
    (r : ℕ) where
  /-- The trivialisation at level `n`. -/
  equiv (n : ℕ) : finiteLevelStalk B X ℓ F s n ≃+ (Fin r → ZMod (ℓ ^ (n + 1)))
  /-- Compatibility with transitions and reduction. -/
  transition (n : ℕ) (y : finiteLevelStalk B X ℓ F s (n + 1)) :
    equiv n (LAdicSheaf.stalkTransition B X ℓ F s n y) = levelReduction (n + 1) (equiv (n + 1) y)

variable {B X ℓ} {F : LAdicSheaf B X ℓ} {s : GeometricPoint X.1}

/-- The map from `ℤ_ℓ^r` to the ℓ-adic stalk given by compatible trivialisations. -/
public def LAdicSheaf.LevelTrivialization.symmLinear (T : LAdicSheaf.LevelTrivialization F s r) :
    (Fin r → ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] LAdicSheaf.stalk B X ℓ F s where
  toFun w := ⟨fun n => (T.equiv n).symm (fun i => PadicInt.toZModPow (n + 1) (w i)), fun n => by
    apply (T.equiv n).injective
    rw [T.transition, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact funext fun i => levelRingHom_toZModPow (n + 1) (w i)⟩
  map_add' v w := by
    apply Subtype.ext
    funext n
    change (T.equiv n).symm _ = (T.equiv n).symm _ + (T.equiv n).symm _
    rw [← map_add]
    congr 1
    funext i
    simp
  map_smul' c w := by
    apply Subtype.ext
    funext n
    change (T.equiv n).symm _ = PadicInt.toZModPow (n + 1) c • (T.equiv n).symm _
    have hv : (fun i => PadicInt.toZModPow (n + 1) ((c • w) i)) =
        PadicInt.toZModPow (n + 1) c • fun i => PadicInt.toZModPow (n + 1) (w i) := by
      funext i
      simp
    rw [hv]
    exact ZMod.map_smul (T.equiv n).symm.toAddMonoidHom _ _

/-- The level components of `symmLinear`. -/
public theorem LAdicSheaf.LevelTrivialization.symmLinear_apply_coe
    (T : LAdicSheaf.LevelTrivialization F s r) (w : Fin r → ℤ_[ℓ]) (n : ℕ) :
    (T.symmLinear w).1 n = (T.equiv n).symm (fun i => PadicInt.toZModPow (n + 1) (w i)) :=
  rfl

/-- **The ℓ-adic stalk is `ℤ_ℓ^r`**, given compatible trivialisations of the finite-level
stalks. -/
public def LAdicSheaf.LevelTrivialization.stalkEquiv (T : LAdicSheaf.LevelTrivialization F s r) :
    LAdicSheaf.stalk B X ℓ F s ≃ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ]) :=
  (LinearEquiv.ofBijective T.symmLinear ⟨fun v w h => by
      funext i
      apply eq_of_toZModPow_succ_eq
      intro n
      have h' := congrArg (fun z : LAdicSheaf.stalk B X ℓ F s => T.equiv n (z.1 n)) h
      simp only [symmLinear_apply_coe, AddEquiv.apply_symm_apply] at h'
      exact congrFun h' i,
    fun z => by
      choose t ht using fun i => exists_toZModPow_eq (fun n => T.equiv n (z.1 n) i) (fun n =>
        z.2 n ▸ (congrFun (T.transition n (z.1 (n + 1))) i).symm)
      refine ⟨t, Subtype.ext (funext fun n => ?_)⟩
      apply (T.equiv n).injective
      rw [symmLinear_apply_coe, AddEquiv.apply_symm_apply]
      exact funext fun i => ht i n⟩).symm

/-- The trivialisation of the ℓ-adic stalk reduces to the level trivialisations. -/
public theorem LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv
    (T : LAdicSheaf.LevelTrivialization F s r) (v : LAdicSheaf.stalk B X ℓ F s) (n : ℕ)
    (i : Fin r) :
    PadicInt.toZModPow (n + 1) (T.stalkEquiv v i) = T.equiv n (v.1 n) i := by
  obtain ⟨w, rfl⟩ := T.stalkEquiv.symm.surjective v
  rw [LinearEquiv.apply_symm_apply]
  change _ = T.equiv n ((T.symmLinear w).1 n) i
  rw [symmLinear_apply_coe, AddEquiv.apply_symm_apply]

/-- **An endomorphism of the geometric point acting at every level by the reduction of one
matrix `M` acts on the ℓ-adic stalk by `M`**, and so has the characteristic polynomial of `M`
on the ℓ-adic stalk. -/
public theorem LAdicSheaf.LevelTrivialization.charpoly_stalkEnd
    (T : LAdicSheaf.LevelTrivialization F s r)
    (a : GeometricPoint.Hom s s) (M : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hM : ∀ n y, T.equiv n ((finiteLevelStalkEnd B X ℓ F a n).hom y) =
      (M.map (PadicInt.toZModPow (n + 1))) *ᵥ T.equiv n y) :
    haveI : Module.Free ℤ_[ℓ] (LAdicSheaf.stalk B X ℓ F s) :=
      Module.Free.of_equiv T.stalkEquiv.symm
    (LAdicSheaf.stalkEnd B X ℓ F a).charpoly = M.charpoly := by
  have : Module.Free ℤ_[ℓ] (LAdicSheaf.stalk B X ℓ F s) := Module.Free.of_equiv T.stalkEquiv.symm
  have hconj : T.stalkEquiv.conj (LAdicSheaf.stalkEnd B X ℓ F a) = Matrix.toLin' M := by
    apply LinearMap.ext
    intro w
    funext i
    apply eq_of_toZModPow_succ_eq
    intro n
    rw [LinearEquiv.conj_apply_apply, toZModPow_stalkEquiv, Matrix.toLin'_apply]
    change T.equiv n ((finiteLevelStalkEnd B X ℓ F a n).hom ((T.stalkEquiv.symm w).1 n)) i = _
    rw [hM, RingHom.map_mulVec]
    congr 2
    funext j
    rw [Function.comp_apply, ← toZModPow_stalkEquiv, LinearEquiv.apply_symm_apply]
  rw [← T.stalkEquiv.charpoly_conj, hconj, Matrix.charpoly_toLin']

/-- **The characteristic polynomial on the rational stalk** of an endomorphism of the geometric
point acting at every level by the reduction of `M` is that of `M`. -/
public theorem LAdicSheaf.LevelTrivialization.charpoly_rationalStalkEnd
    (T : LAdicSheaf.LevelTrivialization F s r) (a : GeometricPoint.Hom s s)
    (M : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hM : ∀ n y, T.equiv n ((finiteLevelStalkEnd B X ℓ F a n).hom y) =
      (M.map (PadicInt.toZModPow (n + 1))) *ᵥ T.equiv n y) :
    (LAdicSheaf.rationalStalkEnd B X ℓ F a).charpoly =
      M.charpoly.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
  have : Module.Free ℤ_[ℓ] (LAdicSheaf.stalk B X ℓ F s) := Module.Free.of_equiv T.stalkEquiv.symm
  exact (LinearMap.charpoly_baseChange _ _).trans
    (congrArg (Polynomial.map _) (T.charpoly_stalkEnd a M hM))

end Sheaf

end Stacks.EtaleCohomology

end
