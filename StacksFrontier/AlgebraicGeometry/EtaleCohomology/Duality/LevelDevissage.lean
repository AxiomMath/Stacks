module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelChangeDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.OpenClosedDuality

/-!
# Duality with coefficients `ℤ/pᵐ` from duality with coefficients `ℤ/p`

Let `p` be a prime, `m ≥ 1`, `D` a flat sheaf of `ℤ/pᵐ`-modules on the small étale site of a
scheme `X` and `t` a trace on `Ext^n_{ℤ/pᵐ}(ℤ/pᵐ, D)` with values in `ℤ/pᵐ`. Every sheaf `F` of
`ℤ/pᵐ`-modules sits in the short exact sequence

`0 → R(F[p]) → F → F / F[p] → 0`,

whose first term is the `p`-torsion `F[p]` (`Stacks.EtaleCohomology.LevelChange.coextend`), a
sheaf of `ℤ/p`-modules read through restriction of scalars `R`
(`Stacks.EtaleCohomology.LevelChange.restrict`), and whose last term is killed by one power of `p`
less than `F`. Duality at `R(F[p])` for `t` is duality at `F[p]`
with coefficients `ℤ/p`, for the level trace and the dualizing object `D[p]`
(`Stacks.EtaleCohomology.LevelChange.isDualityPerfect_restrict_iff`); the five lemma
`CategoryTheory.Abelian.Ext.isDualityPerfect_X₂` and an induction on the exponent of `p` killing
`F` then give duality at every member `F` of a class `P` stable under `F ↦ F / F[p]`, from duality
with coefficients `ℤ/p` at the sheaves `F[p]` and the vanishing in degree `n + 1` of
`Ext^{n+1}_{ℤ/p}(ℤ/p, F[p])` and `Ext^{n+1}_{ℤ/pᵐ}(F, D)`.

For a lisse sheaf on a curve this reduces Poincaré duality with coefficients `ℤ/ℓⁿ` to Poincaré
duality with coefficients `ℤ/ℓ`.

## Main results

* `Stacks.EtaleCohomology.LevelChange.pow_nsmul_id_cokernel_counit`: `F / F[p]` is killed by `pᵏ`
  when `F` is killed by `pᵏ⁺¹`.
* `Stacks.EtaleCohomology.LevelChange.isDualityPerfect_of_coextend`: the dévissage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.LevelChange

open ExtensionTorsor

variable {p : ℕ} [Fact p.Prime] {m : ℕ} [NeZero m] (X : Scheme.{u})

omit [Fact p.Prime] in
/-- `p ∣ pᵐ` for `m ≥ 1`. -/
theorem dvd_pow_self_of_neZero : p ∣ p ^ m := dvd_pow_self p (NeZero.ne m)

/-- The inclusion `R(F[p]) ⟶ F` of the `p`-torsion. -/
abbrev torsionCounit (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) :
    (restrict X (dvd_pow_self_of_neZero (p := p) (m := m))).obj
      ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj F) ⟶ F :=
  (restrictCoextendAdj X (dvd_pow_self_of_neZero (p := p) (m := m))).counit.app F

omit [Fact p.Prime] in
/-- `R(F[p]) ⟶ F` exhibits `R(F[p])` as the `p`-torsion of `F`. -/
theorem isTorsionKernel_torsionCounit (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) :
    IsTorsionKernel p (torsionCounit X F) :=
  isTorsionKernel_etaleModuleTorsionι (X := X) (N := p)
    (hN := dvd_pow_self_of_neZero (p := p) (m := m)) F

/-- The inclusion `R(F[p]) ⟶ F` is a monomorphism. -/
instance mono_torsionCounit (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) :
    Mono (torsionCounit X F) :=
  (isTorsionKernel_torsionCounit X F).mono

omit [Fact p.Prime] in
/-- `0 → R(F[p]) → F → F / F[p] → 0` is short exact. -/
private theorem shortExact_torsionCounit (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) :
    (ShortComplex.mk (torsionCounit X F) (cokernel.π (torsionCounit X F))
      (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_cokernel (torsionCounit X F) }

omit [Fact p.Prime] in
/-- **`F / F[p]` is killed by `pᵏ` when `F` is killed by `pᵏ⁺¹`.** -/
theorem pow_nsmul_id_cokernel_counit (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) {k : ℕ}
    (hk : (p ^ (k + 1)) • 𝟙 F = 0) : (p ^ k) • 𝟙 (cokernel (torsionCounit X F)) = 0 := by
  obtain ⟨s, hs⟩ := (isTorsionKernel_torsionCounit X F).exists_lift ((p ^ k) • 𝟙 F)
    (by rw [Preadditive.nsmul_comp, Category.id_comp, smul_smul, ← pow_succ, hk])
  rw [← cancel_epi (cokernel.π (torsionCounit X F)), comp_zero, Preadditive.comp_nsmul,
    Category.comp_id, ← Category.id_comp (cokernel.π _), ← Preadditive.nsmul_comp, ← hs,
    Category.assoc, cokernel.condition, comp_zero]

/-- Dévissage induction: a property `Q` holding for sheaves killed by `1` and passing from
`F / F[p]` to `F` holds for every member `F` of a class `P` stable under `F ↦ F / F[p]`. -/
private theorem induction_of_cokernel_torsionCounit
    (P Q : ObjectProperty (EtaleModules.{u, 0} (ZMod (p ^ m)) X))
    (hP : ∀ F, P F → P (cokernel (torsionCounit X F)))
    (h₀ : ∀ F, P F → 𝟙 F = 0 → Q F)
    (hs : ∀ F, P F → Q (cokernel (torsionCounit X F)) → Q F)
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) (hF : P F) : Q F := by
  exact Nat.rec (motive := fun k => ∀ F, P F → (p ^ k) • 𝟙 F = 0 → Q F)
    (fun F hF hk => h₀ F hF (by simpa using hk))
    (fun k ih F hF hk => hs F hF (ih _ (hP F hF) (pow_nsmul_id_cokernel_counit X F hk)))
    m F hF (etaleModules_pow_nsmul_id F)

/-- **Duality with coefficients `ℤ/pᵐ` from duality with coefficients `ℤ/p`.** Let `D` be a flat
sheaf of `ℤ/pᵐ`-modules, `t` a trace on `Ext^n_{ℤ/pᵐ}(ℤ/pᵐ, D)` and `P` a class of sheaves of
`ℤ/pᵐ`-modules stable under `F ↦ F / F[p]`. Suppose that for every `F` in `P` duality holds at
`F[p]` with coefficients `ℤ/p` for the level trace and the dualizing object `D[p]`, and that
`Ext^{n+1}_{ℤ/p}(ℤ/p, F[p])` and `Ext^{n+1}_{ℤ/pᵐ}(F, D)` vanish. Then duality holds at every
member of `P`. -/
theorem isDualityPerfect_of_coextend {D : EtaleModules.{u, 0} (ZMod (p ^ m)) X}
    (hD : PowExact p m D) {n : ℕ} (t : Ext (unitSheaf (X := X) (p ^ m)) D n →+ ZMod (p ^ m))
    (P : ObjectProperty (EtaleModules.{u, 0} (ZMod (p ^ m)) X))
    (hP : ∀ F, P F → P (cokernel (torsionCounit X F)))
    (h₁ : ∀ F, P F → Ext.IsDualityPerfect (unitSheaf (X := X) p)
      ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj D) n
      (levelTrace X (dvd_pow_self_of_neZero (p := p) (m := m)) t)
      ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj F))
    (hv₁ : ∀ F, P F → Subsingleton (Ext (unitSheaf (X := X) p)
      ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj F) (n + 1)))
    (hv₂ : ∀ F, P F → Subsingleton (Ext F D (n + 1)))
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) (hF : P F) :
    Ext.IsDualityPerfect (unitSheaf (X := X) (p ^ m)) D n t F := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hdv := dvd_pow_self_of_neZero (p := p) (m := m)
  have htors : ∀ F, P F → Ext.IsDualityPerfect (unitSheaf (X := X) (p ^ m)) D n t
      ((restrict X hdv).obj ((coextend X hdv).obj F)) := fun F hF =>
    (isDualityPerfect_restrict_iff X hdv (Nat.one_le_iff_ne_zero.2 (NeZero.ne m)) (pow_one p).symm
      hD t _).2 (h₁ F hF)
  refine induction_of_cokernel_torsionCounit X P
    (Q := Ext.IsDualityPerfect (unitSheaf (X := X) (p ^ m)) D n t) hP
    (fun F hF hk => Ext.isDualityPerfect_of_retract (0 : F ⟶ _) 0 (by rw [hk, comp_zero])
      (htors F hF)) (fun F hF ih => ?_) F hF
  have hv : Subsingleton (Ext (unitSheaf (X := X) (p ^ m))
      ((restrict X hdv).obj ((coextend X hdv).obj F)) (n + 1)) :=
    have := hv₁ F hF
    (extMap_bijective X hdv ((coextend X hdv).obj F) (n + 1)).surjective.subsingleton
  exact Ext.isDualityPerfect_X₂ (shortExact_torsionCounit X F) (htors F hF) ih hv
    (hv₂ _ (hP F hF)) (fun M j H φ => Ext.exists_extend_zmodPow H φ)

/-- **Vanishing of `Ext^q(F, D)` with coefficients `ℤ/pᵐ` from the vanishing with coefficients
`ℤ/p`**, along the same dévissage: if `Ext^q_{ℤ/p}(F[p], D[p]) = 0` for `q > n` and every `F` in a
class `P` stable under `F ↦ F / F[p]`, then `Ext^q_{ℤ/pᵐ}(F, D) = 0` for `q > n` and `F` in `P`. -/
theorem subsingleton_ext_of_coextend {D : EtaleModules.{u, 0} (ZMod (p ^ m)) X}
    (hD : PowExact p m D) {n : ℕ} (P : ObjectProperty (EtaleModules.{u, 0} (ZMod (p ^ m)) X))
    (hP : ∀ F, P F → P (cokernel (torsionCounit X F)))
    (hv : ∀ F, P F → ∀ q, n < q → Subsingleton (Ext
      ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj F)
      ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj D) q))
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) (hF : P F) (q : ℕ) (hq : n < q) :
    Subsingleton (Ext F D q) := by
  have hdv := dvd_pow_self_of_neZero (p := p) (m := m)
  have htors : ∀ F, P F → Subsingleton (Ext ((restrict X hdv).obj ((coextend X hdv).obj F)) D q) :=
    fun F hF =>
      have := hv F hF q hq
      (extMap_coextendScalars_bijective X hdv
        (Nat.one_le_iff_ne_zero.2 (NeZero.ne m)) (pow_one p).symm _ D hD q).2.subsingleton
  refine induction_of_cokernel_torsionCounit X P (Q := fun F => Subsingleton (Ext F D q)) hP
    (fun F _ hk => ⟨fun a b => by
      rw [← Ext.mk₀_id_comp a, ← Ext.mk₀_id_comp b, hk, Ext.mk₀_zero, Ext.zero_comp,
        Ext.zero_comp]⟩)
    (fun F hF ih => Ext.subsingleton_ext_left_X₂_of_shortExact (shortExact_torsionCounit X F) D
      (htors F hF) ih) F hF

end Stacks.EtaleCohomology.LevelChange

end
