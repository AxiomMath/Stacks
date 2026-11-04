module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRootsOfUnityPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DisjointUnionPullbackTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceInput
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePicardTorsionFree

/-!
# The traces of `φ^*` on `Hⁱ(C, μ_{ℓⁿ})` of a smooth proper curve

For a smooth proper curve `C` over an algebraically closed field `k`, a nonconstant endomorphism
`φ` of `C` over `k` and a prime `ℓ` invertible in `k`, every `Hⁱ(C, μ_{ℓⁿ})` is a finite free
`ℤ/ℓⁿ`-module, and the traces of `φ^*` are

`Tr(φ^* | H⁰) = 1`, `Tr(φ^* | H¹) = Tr(φ^* | Pic(C)[ℓⁿ])`, `Tr(φ^* | H²) = deg φ`,
`Tr(φ^* | Hⁱ) = 0` for `i ≥ 3`.

## Main definitions

* `Stacks.EtaleCohomology.curvePullbackTraceValue`: the four values.

## Main results

* `Stacks.EtaleCohomology.exists_curveModel`: for every `i` a finite free model of
  `Hⁱ(C, μ_{ℓⁿ})` in which the trace of `φ^*` is `curvePullbackTraceValue i`, for every `φ`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Kummer

universe u

namespace Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (g : C ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] [IsProper g] (ℓ m : ℕ) [Fact ℓ.Prime]

/-- **The trace of `φ^*` on `Hⁱ(C, μ_{ℓ^m})`**: `1`, `Tr(φ^* | Pic(C)[ℓ^m])`, `deg φ`, then `0`. -/
def curvePullbackTraceValue (φ : C ⟶ C) (w : φ ≫ g = g) (hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y) :
    ℕ → ZMod (ℓ ^ m)
  | 0 => 1
  | 1 =>
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    picardTorsionTrace C (Stacks.Picard.schemePullbackClassHom φ) ℓ m
  | 2 => ((@degreeOver C C φ _ _ (locallyOfFiniteType_of_isCurve_comp k g g φ w)
      (isDominant_of_not_constant k g g φ hnc) : ℕ) : ZMod (ℓ ^ m))
  | _ + 3 => 0

/-- The model trace of a scalar multiplication on `ℤ/N`, read on `Fin 1 → ℤ/N`. -/
theorem modelTrace_funUnique_of_eq_mul {N : ℕ} [Fact (1 < N)] {A : Type*} [AddCommGroup A]
    (e : A ≃+ ZMod N) (f : A →+ A) (c : ZMod N) (hf : ∀ x, e (f x) = c * e x) :
    modelTrace N (e.trans (AddEquiv.funUnique (Fin 1) (ZMod N)).symm) f = c := by
  have hlin : ((e.trans (AddEquiv.funUnique (Fin 1) (ZMod N)).symm).toAddMonoidHom.comp
      (f.comp (e.trans (AddEquiv.funUnique (Fin 1)
        (ZMod N)).symm).symm.toAddMonoidHom)).toZModLinearMap N = c • LinearMap.id := by
    ext z i
    fin_cases i
    simp [hf]
  rw [modelTrace, hlin, map_smul, LinearMap.trace_id, Module.finrank_fin_fun, smul_eq_mul,
    Nat.cast_one, mul_one]

variable {ℓ m}

/-- A nonzero natural number `ℓ` in a field has `ℓ ^ m` a unit. -/
private theorem isUnit_natCast_pow_of_ne_zero {k : Type*} [Field k] {ℓ : ℕ} (m : ℕ)
    (hℓ : (ℓ : k) ≠ 0) : IsUnit ((ℓ ^ m : ℕ) : k) := by
  rw [Nat.cast_pow]; exact (isUnit_iff_ne_zero.mpr hℓ).pow m

include g in
/-- **A finite free model of `H⁰(C, μ_{ℓ^m})`** on which the trace of `φ^*` is `1`, for every
nonconstant endomorphism `φ` of `C` over `k`. -/
theorem exists_curveModel_zero (hm : 1 ≤ m) (hℓ : (ℓ : k) ≠ 0) :
    ∃ (r : ℕ) (e : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} C (ℓ ^ m)) 0 ≃+
      (Fin r → ZMod (ℓ ^ m))), ∀ (φ : C ⟶ C) (w : φ ≫ g = g)
        (hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y),
        modelTrace (ℓ ^ m) e (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ (ℓ ^ m) 0) =
          curvePullbackTraceValue g ℓ m φ w hnc 0 := by
  have hp : ℓ.Prime := Fact.out
  have : Fact (1 < ℓ ^ m) := ⟨Nat.one_lt_pow (by lia) hp.one_lt⟩
  have hn := isUnit_natCast_pow_of_ne_zero m hℓ
  obtain ⟨e, he⟩ := exists_h0_addEquiv_rootsOfUnityPullbackMap g hn
  exact ⟨1, e.trans (AddEquiv.funUnique (Fin 1) (ZMod (ℓ ^ m))).symm, fun φ w hnc =>
    (modelTrace_funUnique_of_eq_mul e _ 1 fun x => by rw [he φ w x, one_mul])⟩

include g in
/-- **A finite free model of `H²(C, μ_{ℓ^m})`** on which the trace of `φ^*` is `deg φ`, for every
nonconstant endomorphism `φ` of `C` over `k`. -/
theorem exists_curveModel_two (hm : 1 ≤ m) (hℓ : (ℓ : k) ≠ 0) :
    ∃ (r : ℕ) (e : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} C (ℓ ^ m)) 2 ≃+
      (Fin r → ZMod (ℓ ^ m))), ∀ (φ : C ⟶ C) (w : φ ≫ g = g)
        (hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y),
        modelTrace (ℓ ^ m) e (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ (ℓ ^ m) 2) =
          curvePullbackTraceValue g ℓ m φ w hnc 2 := by
  have hp : ℓ.Prime := Fact.out
  have : Fact (1 < ℓ ^ m) := ⟨Nat.one_lt_pow (by lia) hp.one_lt⟩
  have hn := isUnit_natCast_pow_of_ne_zero m hℓ
  obtain ⟨e, he⟩ := exists_h2_addEquiv_rootsOfUnityPullbackMap g hn
  exact ⟨1, e.trans (AddEquiv.funUnique (Fin 1) (ZMod (ℓ ^ m))).symm, fun φ w hnc =>
    modelTrace_funUnique_of_eq_mul e _ _ (he φ w hnc)⟩

include g in
/-- **A finite free model of `H¹(C, μ_{ℓ^m})`** on which the trace of `φ^*` is the trace of `φ^*`
on `Pic(C)[ℓ^m]`, for every nonconstant endomorphism `φ` of `C` over `k`. -/
theorem exists_curveModel_one (hℓ : (ℓ : k) ≠ 0) :
    ∃ (r : ℕ) (e : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} C (ℓ ^ m)) 1 ≃+
      (Fin r → ZMod (ℓ ^ m))), ∀ (φ : C ⟶ C) (w : φ ≫ g = g)
        (hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y),
        modelTrace (ℓ ^ m) e (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ (ℓ ^ m) 1) =
          curvePullbackTraceValue g ℓ m φ w hnc 1 := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have hn := isUnit_natCast_pow_of_ne_zero m hℓ
  obtain ⟨e1, he1⟩ := exists_h1_addEquiv_rootsOfUnityPullbackMap g hn
  obtain ⟨r, ⟨f⟩⟩ := Stacks.Picard.exists_torsionBy_addEquiv_pi_zmod g (ℓ ^ m) hn
  have hsub : Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ m) =
      Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) (((ℓ ^ m : ℕ) : ℤ)) := by
    rw [Nat.cast_pow]
  let f' := (LinearEquiv.ofEq _ _ hsub).toAddEquiv.trans f
  refine ⟨r, e1.trans f', fun φ w hnc => ?_⟩
  rw [modelTrace_eq_of_addEquiv (ℓ ^ m) (e1.trans f') e1]
  show LinearMap.trace _ _ _ = picardTorsionTrace C (Stacks.Picard.schemePullbackClassHom φ) ℓ m
  rw [picardTorsionTrace]
  congr 1
  ext t
  show ((e1 (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ (ℓ ^ m) 1 (e1.symm t)) :
      Stacks.Picard.ofScheme C)) = ((Stacks.Picard.torsionByRestrict (A := Stacks.Picard.ofScheme C)
        (Stacks.Picard.schemePullbackClassHom φ) ((ℓ : ℤ) ^ m) t) : Stacks.Picard.ofScheme C)
  rw [he1 φ, AddEquiv.apply_symm_apply]

omit [IsProper g] [Fact (Nat.Prime ℓ)] in
include g in
/-- **A finite free model of `H^q(C, μ_{ℓ^m})` for `q ≥ 3`**: the zero module, on which the trace
of `φ^*` is `0` for every endomorphism `φ` of `C`. -/
theorem exists_curveModel_ge_three {q : ℕ} (hq : 3 ≤ q) (hℓ : (ℓ : k) ≠ 0) :
    ∃ (r : ℕ) (e : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} C (ℓ ^ m)) q ≃+
      (Fin r → ZMod (ℓ ^ m))), ∀ (φ : C ⟶ C),
        modelTrace (ℓ ^ m) e (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ (ℓ ^ m) q) = 0 := by
  have hn := isUnit_natCast_pow_of_ne_zero m hℓ
  have := subsingleton_sheafH_rootsOfUnitySheaf_of_isCurve g hn q hq
  refine ⟨0, AddEquiv.ofBijective (0 : _ →+ (Fin 0 → ZMod (ℓ ^ m)))
    ⟨fun a b _ => Subsingleton.elim a b, fun z => ⟨0, Subsingleton.elim _ _⟩⟩, fun φ => ?_⟩
  have hz : ∀ F : (Fin 0 → ZMod (ℓ ^ m)) →ₗ[ZMod (ℓ ^ m)] (Fin 0 → ZMod (ℓ ^ m)),
      LinearMap.trace (ZMod (ℓ ^ m)) _ F = 0 := fun F => by
    rw [show F = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
  exact hz _

include g in
/-- **Finite free models of `Hⁱ(C, μ_{ℓ^m})` with the traces of `φ^*`**, in every degree. -/
theorem exists_curveModel (hm : 1 ≤ m) (hℓ : (ℓ : k) ≠ 0) (q : ℕ) :
    ∃ (r : ℕ) (e : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} C (ℓ ^ m)) q ≃+
      (Fin r → ZMod (ℓ ^ m))), ∀ (φ : C ⟶ C) (w : φ ≫ g = g)
        (hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y),
        modelTrace (ℓ ^ m) e (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ (ℓ ^ m) q) =
          curvePullbackTraceValue g ℓ m φ w hnc q := by
  match q with
  | 0 => exact exists_curveModel_zero g hm hℓ
  | 1 => exact exists_curveModel_one g hℓ
  | 2 => exact exists_curveModel_two g hm hℓ
  | q + 3 =>
    obtain ⟨r, e, he⟩ := exists_curveModel_ge_three g (q := q + 3) (by lia) hℓ
    exact ⟨r, e, fun φ w hnc => he φ⟩

end Stacks.EtaleCohomology

end
