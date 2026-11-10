module

public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FixedClassCount
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PeriodicClosedPoints
public import StacksFrontier.RingTheory.PowerSeries.ZetaRationality
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion

/-!
# The reciprocal roots of the zeta function of a curve with a twisted Frobenius

Let `Ω` be an algebraically closed field of characteristic `p`, algebraic over `𝔽_p`, `C` a
smooth proper curve of genus `γ` over `Ω`, and `Ψ` an automorphism of the scheme `C` which is
`q`-semilinear, `q = p ^ f`, `f ≥ 1` (for instance `Ψ ≫ φ = F ^ f` for an endomorphism `φ` of
`C` over `Ω`, `F` the absolute Frobenius). For `m ≥ 1` let

* `N m` be the number of closed points of `C` fixed by `Ψ ^ m`,
* `h m` be the number of classes in `Pic⁰(C)` fixed by `(Ψ^*) ^ m`.

Both are finite, and **there are `r ≤ 2γ` algebraic integers `α_1, …, α_r` in `ℚ̄` with, for all
`m ≥ 1`,**

* `N m = 1 + q ^ m - ∑ α_i ^ m`,
* `h m = ∏ (1 - α_i ^ m)`,
* `q ^ (m (2γ - r)) ∏ (q ^ m - α_i ^ m) = q ^ (m γ) h m`

(`Stacks.Zeta.exists_zeta_roots_of_isCurve`; in the setting of a twisted Frobenius,
`Stacks.Zeta.exists_zeta_roots_of_twistedFrobenius`, `Ψ` being semilinear by
`Stacks.Zeta.hom_comp_eq_of_hom_comp_eq_absoluteFrobeniusPow`). This is the zeta-function input
of Weil's theorem ([Stacks, Tag 03U1]).

The zeta series `Z_m = ∑_d A_m(d) T ^ d` of `Ψ ^ m`, `A_m(d)` the number of `Ψ ^ m`-invariant
effective divisors of degree `d`, has logarithmic derivative `∑_k N(m k) T ^ k`
(`Stacks.Zeta.coeff_logDerivative_invariantCount`, the fixed points of every power being finite,
`Stacks.Zeta.finite_setOf_isClosed_fixed`), and its tail is given by Riemann–Roch and Lang's
theorem (`Stacks.Zeta.exists_period_invariantCount`, which needs a periodic closed point: every
closed point is periodic, `Stacks.Zeta.exists_iterate_closedPointPerm_eq`). The rationality
argument (`Stacks.Zeta.exists_zeta_roots`) concludes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory PowerSeries

universe u

namespace Stacks.Zeta

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
  {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω)) [IsProper g] [Smooth g] [IsCurve Ω g]

/-- The closed points of `C` fixed by `Ψ ^ m` correspond to the points of `ClosedPoint C` fixed by
`σ ^ m`. -/
theorem natCard_setOf_iterate_closedPointPerm (Ψ : C ≅ C) (m : ℕ) :
    Nat.card {y : ClosedPoint C | (⇑(closedPointPerm Ψ))^[m] y = y} =
      Nat.card {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[m] x = x} := by
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1.1, y.1.2, by rw [← iterate_closedPointPerm_val, y.2]⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (by
        rw [iterate_closedPointPerm_val]; exact x.2.2)⟩
      left_inv := fun y => rfl
      right_inv := fun x => rfl }

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsCurve Ω g] in
/-- **A twisted Frobenius is semilinear.** If `φ` is an endomorphism of `C` over `Ω` and
`Ψ ≫ φ = F ^ f`, `F` the absolute Frobenius of `C`, then `Ψ` is `p ^ f`-semilinear:
`Ψ ≫ g = g ≫ Spec (c ↦ c ^ p ^ f)`. -/
theorem hom_comp_eq_of_hom_comp_eq_absoluteFrobeniusPow (φ : C ⟶ C) (w : φ ≫ g = g)
    (hC : Stacks.Frobenius.IsInCharacteristic C p) (f : ℕ) (Ψ : C ≅ C)
    (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow C p hC f) :
    Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p f)) := by
  have hS : Stacks.Frobenius.IsInCharacteristic (Spec (.of Ω)) p :=
    isInCharacteristic_spec Ω p (CharP.cast_eq_zero Ω p)
  rw [specMap_eq_absoluteFrobeniusPow (iterateFrobenius Ω p f) p f hS (fun a => rfl),
    ← absoluteFrobeniusPow_naturality g p hC hS f, ← hΨ, Category.assoc, w]

variable (f : ℕ) (hf : 0 < f) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p f)))

include hf hΨ in
/-- **The reciprocal roots of the zeta function of a curve.** For a `q`-semilinear automorphism
`Ψ` (`q = p ^ f`, `f ≥ 1`) of a smooth proper curve of genus `γ` over an algebraically closed
field algebraic over `𝔽_p`: for every `m ≥ 1` the closed points fixed by `Ψ ^ m` and the classes
of `Pic⁰` fixed by `(Ψ^*) ^ m` are finite in number, `N m` and `h m`, and there are `r ≤ 2γ`
algebraic integers `α_i ∈ ℚ̄` with `N m = 1 + q ^ m - ∑ α_i ^ m`, `h m = ∏ (1 - α_i ^ m)` and
`q ^ (m (2γ - r)) ∏ (q ^ m - α_i ^ m) = q ^ (m γ) h m` for all `m ≥ 1`. -/
theorem exists_zeta_roots_of_isCurve
    (halg : letI := ZMod.algebra Ω p; Algebra.IsAlgebraic (ZMod p) Ω) :
    (∀ m, 0 < m → {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[m] x = x}.Finite) ∧
    (∀ m, 0 < m → Finite {c : Stacks.Picard.ofScheme C //
      Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c = 0 ∧
      (Stacks.Picard.schemePullbackClassHom Ψ.hom)^[m] c = c}) ∧
    ∃ (r : ℕ) (α : Fin r → AlgebraicClosure ℚ), r ≤ 2 * genus g ∧ (∀ i, IsIntegral ℤ (α i)) ∧
      ∀ m, 0 < m →
        (Nat.card {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[m] x = x} :
            AlgebraicClosure ℚ) =
          1 + ((p ^ f : ℕ) : AlgebraicClosure ℚ) ^ m - ∑ i, α i ^ m ∧
        (Nat.card {c : Stacks.Picard.ofScheme C //
            Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c = 0 ∧
            (Stacks.Picard.schemePullbackClassHom Ψ.hom)^[m] c = c} : AlgebraicClosure ℚ) =
          ∏ i, (1 - α i ^ m) ∧
        ((p ^ f : ℕ) : AlgebraicClosure ℚ) ^ (m * (2 * genus g - r)) *
            ∏ i, (((p ^ f : ℕ) : AlgebraicClosure ℚ) ^ m - α i ^ m) =
          ((p ^ f : ℕ) : AlgebraicClosure ℚ) ^ (m * genus g) *
            (Nat.card {c : Stacks.Picard.ofScheme C //
              Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c = 0 ∧
              (Stacks.Picard.schemePullbackClassHom Ψ.hom)^[m] c = c} : AlgebraicClosure ℚ) := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian g
  set σ := closedPointPerm Ψ
  set deg := Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g)
  set P := Stacks.Picard.schemePullbackClassHom Ψ.hom
  -- the powers of `Ψ`
  set Ψm : ℕ → (C ≅ C) := fun m => ((Aut.of Ψ) ^ m).asIso
  have hΨm : ∀ m, (Ψm m).hom ≫ g =
      g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (f * m))) :=
    aut_pow_hom_comp g p f Ψ hΨ
  have hσm : ∀ m, closedPointPerm (Ψm m) = σ ^ m := closedPointPerm_aut_pow Ψ
  have hPm : ∀ m c, Stacks.Picard.schemePullbackClassHom (Ψm m).hom c = P^[m] c :=
    schemePullbackClassHom_aut_pow Ψ
  have hE : ∀ m, {c : Stacks.Picard.ofScheme C // deg c = 0 ∧
      Stacks.Picard.schemePullbackClassHom (Ψm m).hom c = c} ≃
      {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ P^[m] c = c} := fun m =>
    Equiv.subtypeEquivRight fun c => by rw [hPm]
  -- a closed point
  obtain ⟨x₀, hx₀⟩ := (Stacks.EtaleCohomology.infinite_closedPoints_of_isCurve (f := g)).nonempty
  -- the count for each power
  have key : ∀ m, 0 < m →
      Finite {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ P^[m] c = c} ∧
      ∃ δ : ℕ, 0 < δ ∧ ∀ d : ℕ, (¬ δ ∣ d → invariantCount (σ ^ m) d = 0) ∧
        (δ ∣ d → 2 * genus g ≤ d + 1 →
          (((p ^ f : ℕ) : ℤ) ^ m - 1) * invariantCount (σ ^ m) d =
            Nat.card {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ P^[m] c = c} *
              ((((p ^ f : ℕ) : ℤ) ^ m) ^ (d + 1 - genus g) - 1)) := by
    intro m hm
    have hper := exists_iterate_closedPointPerm_eq g p (f * m) (Ψm m) (hΨm m) halg ⟨x₀, hx₀⟩
    obtain ⟨hfin, δ, hδ, hR⟩ := exists_period_invariantCount g p (f * m) (Nat.mul_pos hf hm)
      (Ψm m) (hΨm m) ⟨_, hper⟩
    have hq : (((p ^ (f * m) : ℕ) : ℤ)) = ((p ^ f : ℕ) : ℤ) ^ m := by push_cast; ring
    refine ⟨Finite.of_equiv _ (hE m), δ, hδ, fun d => ⟨fun h => ?_, fun h1 h2 => ?_⟩⟩
    · rw [← hσm]; exact (hR d).1 h
    · have := (hR d).2 h1 h2
      rw [hσm, hq, Nat.card_congr (hE m)] at this
      exact this
  choose hfinH δ hδ hR using key
  -- the finiteness of the periodic points
  have hfinN : ∀ m, 0 < m → {y : ClosedPoint C | (⇑σ)^[m] y = y}.Finite := fun m hm =>
    finite_setOf_iterate_closedPointPerm g p f hf Ψ hΨ hm
  have hfinNC : ∀ m, 0 < m →
      {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[m] x = x}.Finite := fun m hm =>
    ((hfinN m hm).image Subtype.val).subset fun x hx =>
      ⟨⟨x, hx.1⟩, by
        change ((⇑σ)^[m] ⟨x, hx.1⟩) = ⟨x, hx.1⟩
        exact Subtype.ext (by rw [iterate_closedPointPerm_val]; exact hx.2), rfl⟩
  refine ⟨hfinNC, hfinH, ?_⟩
  have hq2 : 2 ≤ p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt
  set δ' : ℕ → ℕ := fun m => if hm : 0 < m then δ m hm else 1
  have := exists_zeta_roots (p ^ f) hq2 (genus g)
    (fun m => Nat.card {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[m] x = x}) δ'
    (fun m => Nat.card {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ P^[m] c = c})
    (fun m d => invariantCount (σ ^ m) d)
    (fun m hm => by simp only [δ', dite_eq_left hm]; exact hδ m hm)
    (fun m hm => by
      have := hfinH m hm
      have : Nonempty {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ P^[m] c = c} :=
        ⟨⟨0, map_zero _, Function.iterate_fixed (map_zero P) m⟩⟩
      exact Nat.card_pos)
    (fun m _ => invariantCount_zero)
    (fun m hm d => by simp only [δ', dite_eq_left hm]; exact hR m hm d)
    (fun m hm k hk => by
      have hpow : ∀ j, (⇑(σ ^ m))^[j] = (⇑σ)^[m * j] := fun j => by
        simp only [Equiv.Perm.coe_pow, ← Function.iterate_mul]
      rw [coeff_logDerivative_invariantCount
        (fun j hj => by simpa only [hpow] using hfinN (m * j) (Nat.mul_pos hm hj)) hk,
        hpow]
      exact congrArg _ (natCard_setOf_iterate_closedPointPerm Ψ (m * k)))
  exact this

include hf in
/-- **The reciprocal roots of the zeta function, for a twisted Frobenius.** The setting of
`Stacks.EtaleCohomology.WeilTraceInput`: `φ` an endomorphism of `C` over `Ω` and `Ψ` an
automorphism of the scheme `C` with `Ψ ≫ φ = F ^ f`, `F` the absolute Frobenius, `f ≥ 1`. Then the
conclusion of `Stacks.Zeta.exists_zeta_roots_of_isCurve` holds for `Ψ` and `q = p ^ f`. -/
theorem exists_zeta_roots_of_twistedFrobenius
    (halg : letI := ZMod.algebra Ω p; Algebra.IsAlgebraic (ZMod p) Ω) (φ : C ⟶ C)
    (w : φ ≫ g = g) (hC : Stacks.Frobenius.IsInCharacteristic C p) (Ψ : C ≅ C)
    (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow C p hC f) :
    (∀ m, 0 < m → {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[m] x = x}.Finite) ∧
    (∀ m, 0 < m → Finite {c : Stacks.Picard.ofScheme C //
      Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c = 0 ∧
      (Stacks.Picard.schemePullbackClassHom Ψ.hom)^[m] c = c}) ∧
    ∃ (r : ℕ) (α : Fin r → AlgebraicClosure ℚ), r ≤ 2 * genus g ∧ (∀ i, IsIntegral ℤ (α i)) ∧
      ∀ m, 0 < m →
        (Nat.card {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[m] x = x} :
            AlgebraicClosure ℚ) =
          1 + ((p ^ f : ℕ) : AlgebraicClosure ℚ) ^ m - ∑ i, α i ^ m ∧
        (Nat.card {c : Stacks.Picard.ofScheme C //
            Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c = 0 ∧
            (Stacks.Picard.schemePullbackClassHom Ψ.hom)^[m] c = c} : AlgebraicClosure ℚ) =
          ∏ i, (1 - α i ^ m) ∧
        ((p ^ f : ℕ) : AlgebraicClosure ℚ) ^ (m * (2 * genus g - r)) *
            ∏ i, (((p ^ f : ℕ) : AlgebraicClosure ℚ) ^ m - α i ^ m) =
          ((p ^ f : ℕ) : AlgebraicClosure ℚ) ^ (m * genus g) *
            (Nat.card {c : Stacks.Picard.ofScheme C //
              Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c = 0 ∧
              (Stacks.Picard.schemePullbackClassHom Ψ.hom)^[m] c = c} : AlgebraicClosure ℚ) :=
  exists_zeta_roots_of_isCurve p g f hf Ψ
    (hom_comp_eq_of_hom_comp_eq_absoluteFrobeniusPow p g φ w hC f Ψ hΨ) halg

end Stacks.Zeta

end
