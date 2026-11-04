module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveCupProductLevel

/-!
# The tower `n ↦ H¹(X, ℤ/ℓⁿ)` of a smooth proper curve

Let `X` be a smooth proper curve over an algebraically closed field `k` and `ℓ` a prime
invertible in `k`. For `N = ℓᵃ ℓᵇ` the reduction `π : ℤ/N_X ⟶ ℤ/ℓᵃ_X`
(`Stacks.EtaleCohomology.LevelChange.reduction`) induces on
`H¹(X, -) = Ext¹_{ℤ/N}(ℤ/N_X, -)`:

* a surjection `H¹(X, ℤ/N) ⟶ H¹(X, ℤ/ℓᵃ)`
  (`Stacks.EtaleCohomology.LevelChange.surjective_comp_reduction_ext_one`);
* whose kernel is `ℓᵃ H¹(X, ℤ/N)`
  (`Stacks.EtaleCohomology.LevelChange.exists_eq_nsmul_of_comp_reduction_eq_zero`);

and the classes of `H¹(X, ℤ/N)` killed by `ℓᵇ` are divisible by `ℓᵃ`
(`Stacks.EtaleCohomology.LevelChange.exists_eq_nsmul_of_nsmul_eq_zero`). These are the
statements that `H¹(X, ℤ/ℓⁿ)` looks like `(ℤ/ℓⁿ)^r` compatibly in `n`, which make
`lim_n H¹(X, ℤ/ℓⁿ)` a free `ℤ_ℓ`-module whose reductions are the finite levels.

All three come from the long exact `Ext` sequences of `0 → ℤ/ℓᵇ → ℤ/N → ℤ/ℓᵃ → 0`
(`Stacks.EtaleCohomology.LevelChange.inclusionShortComplex_shortExact`) and the counting facts
`#H²(X, ℤ/m) = m`, `H³ = 0` of
`Stacks.EtaleCohomology.LevelChange.injective_two_and_surjective_one`, with
`ℤ/N --π--> ℤ/ℓᵇ --ℓᵃ--> ℤ/N` equal to multiplication by `ℓᵃ`
(`Stacks.EtaleCohomology.LevelChange.reduction_comp_inclusion`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.LevelChange

open ExtensionTorsor

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f] {ℓ : ℕ} [Fact ℓ.Prime]

include f in
/-- `Pic⁰(X)` is `ℓʲ`-divisible, in the shape the counting lemmas consume. -/
theorem picDiv_pow (hℓ : IsUnit (ℓ : k)) (j : ℕ) : PicDiv f (ℓ ^ j) :=
  exists_pow_nsmul_eq f (Fact.out : ℓ.Prime).ne_zero
    (fun L hL => Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero f _ hℓ L hL) j

omit [IsAlgClosed k] [Fact (Nat.Prime ℓ)] in
/-- If `ℓ` is invertible in `k`, then so is `ℓ ^ j` for every `j`. -/
theorem isUnit_pow_natCast (hℓ : IsUnit (ℓ : k)) (j : ℕ) : IsUnit ((ℓ ^ j : ℕ) : k) := by
  rw [Nat.cast_pow]
  exact hℓ.pow j

/-- If `ℓ ^ a * ℓ ^ b = N`, then `N` is nonzero. -/
private theorem neZero_of_pow_mul_pow {a b N : ℕ} (hN : ℓ ^ a * ℓ ^ b = N) : NeZero N :=
  ⟨by rw [← hN, ← pow_add]; exact (pow_pos (Fact.out : ℓ.Prime).pos _).ne'⟩

/-- `ℤ/N --π--> ℤ/n --m--> ℤ/N` acts on `Ext¹(ℤ/N_X, ℤ/N)` as multiplication by `m`. -/
private theorem comp_reduction_comp_inclusion_eq {m n N : ℕ} (hN : m * n = N) [NeZero N]
    (h : n ∣ N) (y : Ext (unitSheaf (X := X) N) (unitSheaf N) 1) :
    (y.comp (Ext.mk₀ (reduction X h)) (add_zero 1)).comp (Ext.mk₀ (inclusion X hN))
      (add_zero 1) = m • y := by
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    reduction_comp_inclusion, mk₀_nsmul, comp_nsmul, Ext.comp_mk₀_id]

include f in
/-- **`H¹(X, ℤ/N) → H¹(X, ℤ/ℓᵃ)` is onto**, for `N = ℓᵃ ℓᵇ`, read on
`Ext¹_{ℤ/N}(ℤ/N_X, -)`. -/
theorem surjective_comp_reduction_ext_one (hℓ : IsUnit (ℓ : k)) {a b N : ℕ}
    (hN : ℓ ^ a * ℓ ^ b = N) (h : ℓ ^ a ∣ N) :
    haveI : NeZero N := ⟨by rw [← hN, ← pow_add]; exact (pow_pos (Fact.out : ℓ.Prime).pos _).ne'⟩
    Function.Surjective (fun y : Ext (unitSheaf (X := X) N) (unitSheaf N) 1 =>
      y.comp (Ext.mk₀ (reduction X h)) (add_zero 1)) := by
  subst hN
  have := neZero_of_pow_mul_pow (ℓ := ℓ) (rfl : ℓ ^ a * ℓ ^ b = _)
  have hNk : IsUnit (((ℓ ^ a * ℓ ^ b : ℕ)) : k) := by
    rw [← pow_add]; exact isUnit_pow_natCast hℓ _
  have hdivN : PicDiv f (ℓ ^ a * ℓ ^ b) := by rw [← pow_add]; exact picDiv_pow f hℓ _
  exact (injective_two_and_surjective_one f rfl (isUnit_pow_natCast hℓ a)
    (isUnit_pow_natCast hℓ b) hNk (picDiv_pow f hℓ a) (picDiv_pow f hℓ b) hdivN).2

include f in
/-- **The kernel of `H¹(X, ℤ/N) → H¹(X, ℤ/ℓᵃ)` is `ℓᵃ H¹(X, ℤ/N)`**, for `N = ℓᵃ ℓᵇ`: a class
killed by the reduction comes from `H¹(X, ℤ/ℓᵇ)` along `ℤ/ℓᵇ --ℓᵃ--> ℤ/N`, every class of
`H¹(X, ℤ/ℓᵇ)` is the reduction of a class of `H¹(X, ℤ/N)`, and
`ℤ/N --π--> ℤ/ℓᵇ --ℓᵃ--> ℤ/N` is multiplication by `ℓᵃ`. -/
theorem exists_eq_nsmul_of_comp_reduction_eq_zero (hℓ : IsUnit (ℓ : k)) {a b N : ℕ}
    (hN : ℓ ^ a * ℓ ^ b = N) (h : ℓ ^ a ∣ N)
    (y : Ext (unitSheaf (X := X) N) (unitSheaf N) 1)
    (hy : haveI : NeZero N :=
        ⟨by rw [← hN, ← pow_add]; exact (pow_pos (Fact.out : ℓ.Prime).pos _).ne'⟩
      y.comp (Ext.mk₀ (reduction X h)) (add_zero 1) = 0) :
    ∃ y' : Ext (unitSheaf (X := X) N) (unitSheaf N) 1, y = ℓ ^ a • y' := by
  have := neZero_of_pow_mul_pow (ℓ := ℓ) hN
  set S := inclusionShortComplex X hN
  have hS : S.ShortExact := inclusionShortComplex_shortExact X hN
  obtain ⟨b', hb'⟩ := Ext.covariant_sequence_exact₂ (unitSheaf (X := X) N) hS y hy
  have hN' : ℓ ^ b * ℓ ^ a = N := (mul_comm _ _).trans hN
  obtain ⟨y', hy'⟩ := surjective_comp_reduction_ext_one f hℓ hN' (dvd_of_mul_eq_left hN) b'
  refine ⟨y', ?_⟩
  rw [← hb', ← hy', comp_reduction_comp_inclusion_eq hN]

include f in
/-- **Classes of `H¹(X, ℤ/N)` killed by `ℓᵇ` are divisible by `ℓᵃ`**, for `N = ℓᵃ ℓᵇ`: such a
class comes from `H¹(X, ℤ/ℓᵇ)` along `ℤ/ℓᵇ --ℓᵃ--> ℤ/N`, and every class of `H¹(X, ℤ/ℓᵇ)` is
the reduction of a class of `H¹(X, ℤ/N)`. -/
theorem exists_eq_nsmul_of_nsmul_eq_zero (hℓ : IsUnit (ℓ : k)) {a b N : ℕ}
    (hN : ℓ ^ a * ℓ ^ b = N) (x : Ext (unitSheaf (X := X) N) (unitSheaf N) 1)
    (hx : ℓ ^ b • x = 0) :
    ∃ y : Ext (unitSheaf (X := X) N) (unitSheaf N) 1, x = ℓ ^ a • y := by
  have := neZero_of_pow_mul_pow (ℓ := ℓ) hN
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have : ConnectedSpace X := inferInstanceAs (ConnectedSpace X)
  have hN' : ℓ ^ b * ℓ ^ a = N := (mul_comm _ _).trans hN
  obtain ⟨b', hb'⟩ := exists_comp_inclusion_eq_of_nsmul_eq_zero hN' x hx
  obtain ⟨y, hy⟩ := surjective_comp_reduction_ext_one f hℓ hN' (dvd_of_mul_eq_left hN) b'
  refine ⟨y, ?_⟩
  rw [← hb', ← hy, comp_reduction_comp_inclusion_eq hN]

end Stacks.EtaleCohomology.LevelChange

end
