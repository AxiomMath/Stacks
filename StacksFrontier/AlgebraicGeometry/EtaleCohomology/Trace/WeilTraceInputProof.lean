module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceInput
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.CurveZetaRoots
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusKernelCount
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusEigenvalues
public import StacksFrontier.AlgebraicGeometry.Curves.TwistedFrobeniusDegree
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionCharpolyRat
public import StacksFrontier.AlgebraicGeometry.Picard.WeilPairingCharpoly
public import StacksFrontier.AlgebraicGeometry.Picard.WeilPairingTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilPairingCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilPairingFrobenius
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ConnectedComponentSelfMap

/-!
# Proof of Weil's trace formula for a twisted Frobenius of a curve

This file proves `Stacks.EtaleCohomology.WeilTraceInput`, the form of Weil's theorem
([Stacks, Tag 03U1]) consumed by Step 9 of the proof of [Stacks, Tag 03V3]: for a smooth proper
curve `C` over an algebraically closed field `Ω` algebraic over `𝔽_p`, an endomorphism `φ` of
`C` over `Ω` and an automorphism `Ψ` of the scheme `C` with `Ψ ≫ φ = F^f` (`F` the absolute
Frobenius, `q = p^f`), and a prime `ℓ ≠ p`,

`#{c ∈ C(Ω) : φ c = c} = 1 - Tr(φ^* | Pic(C)[ℓⁿ]) + deg φ` in `ℤ/ℓⁿ`.

The proof goes through the zeta function of `Ψ` rather than through intersection numbers:

* the `Ω`-points fixed by `φ` are the closed points fixed by `Ψ`, since `φ = F^f ≫ Ψ⁻¹` and `F`
  is the identity on points, and their number is `N₁ = 1 + q - ∑ αᵢ` for the reciprocal roots
  `αᵢ` of the zeta function (`Stacks.Zeta.exists_zeta_roots_of_twistedFrobenius`);
* `deg φ = q` (`AlgebraicGeometry.degreeOver_eq_pow_of_comp_eq_absoluteFrobeniusPow`);
* the Frobenius of the jacobian gives a monic `χ ∈ ℚ[X]` of degree `2γ` computing the kernel
  counts of polynomials in `Ψ^*` on `Pic⁰(C)`
  (`Stacks.Zeta.exists_normForm_natCard_ker_twistedFrobenius`),
  which is the `ℓ`-adic characteristic polynomial of `Ψ^*` on the `Pic⁰(C)[ℓ^N] = Pic(C)[ℓ^N]`
  (`Stacks.Picard.exists_charpoly_levelMatrix_eq_of_normForm`);
* the Weil pairing (`Stacks.Picard.exists_weilPairing_of_twist`), for which `Ψ^*` is a similitude
  of factor `q` and `Ψ^* φ^* = φ^* Ψ^* = q`, makes `χ` symmetric
  (`Stacks.Picard.charpoly_coeff_zero_mul_coeff_eq_of_pairing`) and gives
  `Tr(φ^*) = Tr(Ψ^*)` (`Stacks.Picard.trace_eq_of_pairing`);
* the roots of `χ` are then the `αᵢ` (`Stacks.Zeta.nextCoeff_eq_neg_sum_of_zeta`), so
  `Tr(Ψ^* | Pic[ℓⁿ]) = ∑ αᵢ = 1 + q - N₁`.

## Main results

* `Stacks.EtaleCohomology.weilTraceInput`.
* `Stacks.EtaleCohomology.natCard_fixedSections_eq_natCard_fixedClosedPoints`: over an
  algebraically closed field, the rational points fixed by an endomorphism are its fixed closed
  points.

The statement of Tag 03U1 itself (any endomorphism `φ ≠ id` of a curve, `V(φ)` an intersection
number with multiplicities and `Tr_J(φ^*)` the trace on the jacobian) is not registered here:
this file covers only twisted Frobenius endomorphisms, whose fixed points are counted without
multiplicity, and the trace on `Pic[ℓⁿ]`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace Stacks.EtaleCohomology

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [LocallyOfFiniteType g]

/-- **The `Ω`-points of `C` fixed by an endomorphism `φ` over `Ω` are its fixed closed points.** -/
theorem natCard_fixedSections_eq_natCard_fixedClosedPoints (φ : C ⟶ C) (w : φ ≫ g = g) :
    Nat.card (fixedSections g φ) = Nat.card {x : C | IsClosed ({x} : Set C) ∧ φ.base x = x} := by
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1.base (IsLocalRing.closedPoint Ω),
        (pointEquivClosedPoint g ⟨y.1, y.2.1⟩).2, by
          show (y.1 ≫ φ).base (IsLocalRing.closedPoint Ω) = _
          rw [y.2.2]⟩
      invFun := fun x => ⟨pointOfClosedPoint g x.1 x.2.1, pointOfClosedPoint_comp g x.1 x.2.1,
        ext_of_apply_closedPoint_eq g (by rw [Category.assoc, w, pointOfClosedPoint_comp])
          (pointOfClosedPoint_comp g x.1 x.2.1) (by
            have h := pointOfClosedPoint_apply g x.1 x.2.1 (IsLocalRing.closedPoint Ω)
            exact (congrArg φ.base h).trans (x.2.2.trans h.symm))⟩
      left_inv := fun y => Subtype.ext (ext_of_apply_closedPoint_eq g
        (pointOfClosedPoint_comp _ _ _) y.2.1 (pointOfClosedPoint_apply _ _ _ _))
      right_inv := fun x => Subtype.ext (pointOfClosedPoint_apply g _ _ _) }

/-- If `φ ≫ Ψ = F^f` for an automorphism `Ψ` of `C` and `F` the absolute Frobenius, the
`Ω`-points of `C` fixed by `φ` are the closed points fixed by `Ψ`. -/
theorem natCard_fixedSections_eq_natCard_fixedClosedPoints_of_comp_eq_absoluteFrobeniusPow
    (φ : C ⟶ C) (w : φ ≫ g = g) (p : ℕ) [Fact p.Prime]
    (hC : Stacks.Frobenius.IsInCharacteristic C p) (f : ℕ) (Ψ : C ≅ C)
    (hφΨ : φ ≫ Ψ.hom = absoluteFrobeniusPow C p hC f) :
    Nat.card (fixedSections g φ) =
      Nat.card {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[1] x = x} := by
  rw [natCard_fixedSections_eq_natCard_fixedClosedPoints g φ w]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => and_congr_right fun _ => ?_)
  have hφx : φ.base x = Ψ.inv.base x := by
    rw [show φ = absoluteFrobeniusPow C p hC f ≫ Ψ.inv by
        rw [← hφΨ, Category.assoc, Iso.hom_inv_id, Category.comp_id],
      Scheme.Hom.comp_base, TopCat.comp_app, AlgebraicGeometry.absoluteFrobeniusPow_base_apply]
  rw [hφx, Function.iterate_one]
  exact ⟨fun h => (congrArg Ψ.hom.base h.symm).trans (Scheme.inv_hom_apply Ψ x),
    fun h => (congrArg Ψ.inv.base h.symm).trans (Scheme.hom_inv_apply Ψ x)⟩

/-- For a homomorphism `d : A →+ ℤ` and `m ≠ 0`, the `m`-torsion of `ker d` is the `m`-torsion
of `A`: torsion elements have degree `0`. -/
def torsionByKerAddEquiv {A : Type*} [AddCommGroup A] (d : A →+ ℤ) {m : ℤ} (hm : m ≠ 0) :
    Submodule.torsionBy ℤ d.ker m ≃+ Submodule.torsionBy ℤ A m where
  toFun x := ⟨x.1.1, (Submodule.mem_torsionBy_iff _ _).mpr
    (congrArg Subtype.val ((Submodule.mem_torsionBy_iff _ _).mp x.2))⟩
  invFun y := ⟨⟨y.1, by
      have h : m • d y.1 = 0 := by
        rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp y.2, map_zero]
      rw [AddMonoidHom.mem_ker]
      exact (smul_eq_zero.mp h).resolve_left hm⟩,
    (Submodule.mem_torsionBy_iff _ _).mpr (Subtype.ext ((Submodule.mem_torsionBy_iff _ _).mp y.2))⟩
  left_inv x := rfl
  right_inv y := rfl
  map_add' a b := rfl

/-- The kernel of `1 - u ^ m`, for `u` the restriction to `ker d` of an endomorphism `P` of `A`,
is the set of elements of `ker d` fixed by `P ^ m`. -/
theorem natCard_ker_one_sub_pow_eq {A : Type*} [AddCommGroup A] (d : A →+ ℤ) (P : A →+ A)
    (u : d.ker →+ d.ker) (hu : ∀ c, (u c : A) = P c) (m : ℕ) :
    Nat.card (aeval (Stacks.Picard.asEnd u) ((1 : ℤ[X]) - Polynomial.X ^ m)).ker =
      Nat.card {c : A // d c = 0 ∧ P^[m] c = c} := by
  have hit : ∀ (k : ℕ) (x : d.ker), ((u^[k] x : d.ker) : A) = P^[k] x :=
    fun k => Function.Semiconj.iterate_right hu k
  have hev : ∀ x : d.ker,
      aeval (Stacks.Picard.asEnd u) ((1 : ℤ[X]) - Polynomial.X ^ m) x = x - u^[m] x := by
    intro x
    rw [map_sub, map_one, map_pow, aeval_X]
    show x - ((Stacks.Picard.asEnd u) ^ m) x = _
    rw [AddMonoid.End.coe_pow]
    rfl
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, by
        have h : aeval (Stacks.Picard.asEnd u) ((1 : ℤ[X]) - Polynomial.X ^ m) x.1 = 0 := x.2
        rw [hev, sub_eq_zero] at h
        rw [← hit]
        exact congrArg Subtype.val h.symm⟩
      invFun := fun c => ⟨⟨c.1, c.2.1⟩, by
        show aeval (Stacks.Picard.asEnd u) ((1 : ℤ[X]) - Polynomial.X ^ m) ⟨c.1, c.2.1⟩ = 0
        rw [hev, sub_eq_zero]
        exact Subtype.ext ((hit m _).trans c.2.2).symm⟩
      left_inv := fun x => rfl
      right_inv := fun c => rfl }

/-- For a prime `p` and `m > 0`, `p` does not divide the constant coefficient of `1 - X ^ m`. -/
theorem not_dvd_coeff_zero_one_sub_X_pow {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 0 < m) :
    ¬ (p : ℤ) ∣ ((1 : ℤ[X]) - Polynomial.X ^ m).coeff 0 := by
  intro hdvd
  rw [coeff_sub, coeff_one_zero, coeff_X_pow, ite_eq_right hm.ne, sub_zero] at hdvd
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using hdvd))

/-- A monic `χ ∈ ℚ[X]` of even degree with `0 ≤ normForm χ X` has `0 ≤ χ(0)`. -/
theorem coeff_zero_nonneg_of_normForm_X_nonneg {χ : ℚ[X]} (hmon : χ.Monic) {γ : ℕ}
    (hχdeg : χ.natDegree = 2 * γ) (hnf : 0 ≤ Stacks.Polynomial.normForm χ Polynomial.X) :
    0 ≤ χ.coeff 0 := by
  have e := Stacks.Zeta.normForm_eq_prod_roots (K := AlgebraicClosure ℚ) hmon Polynomial.X
  simp only [Polynomial.map_X, eval_X, Multiset.map_id'] at e
  have hc := (IsAlgClosed.splits (χ.map (algebraMap ℚ (AlgebraicClosure ℚ)))
    ).coeff_zero_eq_prod_roots_of_monic (hmon.map _)
  rw [natDegree_map, hχdeg, pow_mul, neg_one_sq, one_pow, one_mul, coeff_map, ← e] at hc
  rwa [(algebraMap ℚ (AlgebraicClosure ℚ)).injective hc]

/-- If `F ∈ ℤ_ℓ[X]` and `χ ∈ ℚ[X]` have the same image in `ℚ_ℓ[X]`, and the reductions of `F`
mod `ℓ ^ N` satisfy `F(0) F_j = q ^ (d - j) F_{d - j}` for all `N > 0`, then so does `χ`. -/
theorem coeff_zero_mul_coeff_eq_of_toZModPow {ℓ : ℕ} [Fact ℓ.Prime] {F : ℤ_[ℓ][X]} {χ : ℚ[X]}
    (hFχ : F.map PadicInt.Coe.ringHom = χ.map (algebraMap ℚ ℚ_[ℓ])) (q d : ℕ)
    (h : ∀ N : ℕ, 0 < N → ∀ j ≤ d,
      (F.map (PadicInt.toZModPow N)).coeff 0 * (F.map (PadicInt.toZModPow N)).coeff j =
        (q : ZMod (ℓ ^ N)) ^ (d - j) * (F.map (PadicInt.toZModPow N)).coeff (d - j))
    (j : ℕ) (hj : j ≤ d) :
    χ.coeff 0 * χ.coeff j = (q : ℚ) ^ (d - j) * χ.coeff (d - j) := by
  have hcoe : ∀ k, PadicInt.Coe.ringHom (F.coeff k) = algebraMap ℚ ℚ_[ℓ] (χ.coeff k) := fun k => by
    simpa only [coeff_map] using congrArg (fun P => Polynomial.coeff P k) hFχ
  have hF : F.coeff 0 * F.coeff j = (q : ℤ_[ℓ]) ^ (d - j) * F.coeff (d - j) := by
    refine PadicInt.ext_of_toZModPow.mp fun N => ?_
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have : Subsingleton (ZMod (ℓ ^ 0)) := by
        rw [pow_zero]
        infer_instance
      exact Subsingleton.elim _ _
    · simpa only [coeff_map, map_mul, map_pow, map_natCast] using h N hN j hj
  have := congrArg PadicInt.Coe.ringHom hF
  rw [map_mul, map_mul, map_pow, map_natCast, hcoe, hcoe, hcoe] at this
  apply (algebraMap ℚ ℚ_[ℓ]).injective
  rwa [map_mul, map_mul, map_pow, map_natCast]

/-- If `a ≫ b = F^f`, then `a^* ∘ b^*` acts on the `m`-torsion of `Pic(S)` as `p ^ f`. -/
theorem torsionByRestrict_schemePullbackClassHom_comp_eq_smul {S : Scheme.{u}} (p : ℕ)
    [Fact p.Prime] (hS : Stacks.Frobenius.IsInCharacteristic S p) (f : ℕ) (m : ℤ)
    {a b : S ⟶ S} (hab : a ≫ b = absoluteFrobeniusPow S p hS f)
    (x : Submodule.torsionBy ℤ (Stacks.Picard.ofScheme S) m) :
    Stacks.Picard.torsionByRestrict (A := Stacks.Picard.ofScheme S)
        (Stacks.Picard.schemePullbackClassHom a) m
      (Stacks.Picard.torsionByRestrict (A := Stacks.Picard.ofScheme S)
        (Stacks.Picard.schemePullbackClassHom b) m x) =
      (p ^ f) • x := by
  apply Subtype.ext
  show Stacks.Picard.schemePullbackClass a (Stacks.Picard.schemePullbackClass b x.1) = _
  rw [Stacks.Picard.schemePullbackClass_comp, hab,
    Stacks.Picard.schemePullbackClass_absoluteFrobeniusPow_eq_zsmul, Submodule.coe_smul_of_tower,
    ← natCast_zsmul, Nat.cast_pow]

/-- For distinct primes `p ≠ ℓ`, `p ^ f` is a unit in `ℤ/ℓ^N`. -/
theorem isUnit_natCast_pow_of_prime_ne {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (h : p ≠ ℓ)
    (f N : ℕ) : IsUnit ((p ^ f : ℕ) : ZMod (ℓ ^ N)) := by
  rw [Nat.cast_pow]
  refine (ZMod.isUnit_prime_of_not_dvd hp fun hd => h ?_).pow f
  exact (Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hd)

/-- If `F ∈ ℤ_ℓ[X]` and a monic `χ ∈ ℚ[X]` have the same image in `ℚ_ℓ[X]`, then `F` is monic. -/
theorem monic_of_map_coe_eq_map {ℓ : ℕ} [Fact ℓ.Prime] {F : ℤ_[ℓ][X]} {χ : ℚ[X]}
    (hFχ : F.map PadicInt.Coe.ringHom = χ.map (algebraMap ℚ ℚ_[ℓ])) (hmon : χ.Monic) :
    F.Monic := by
  have hinj : Function.Injective (PadicInt.Coe.ringHom (p := ℓ)) := Subtype.coe_injective
  have h1 := leadingCoeff_map_of_injective hinj F
  rw [hFχ, (hmon.map _).leadingCoeff] at h1
  exact hinj (by rw [← h1, map_one])

/-- Let `σ` be a similitude of unit factor `c` for a nondegenerate pairing on a `ℤ/N`-module with
basis `b`, and `τ` with `σ τ = τ σ = c`. If `P` is the characteristic polynomial of the matrix of
`σ`, then `P(0) P_j = c ^ (d - j) P_{d - j}` and `Tr τ = -P.nextCoeff`. -/
theorem charpoly_symm_and_trace_eq_of_pairing {N : ℕ} [NeZero N] [Nontrivial (ZMod N)]
    {G : Type*} [AddCommGroup G] [Module (ZMod N) G] {d : ℕ} (b : Module.Basis (Fin d) (ZMod N) G)
    (σ τ : G →ₗ[ZMod N] G) (c : ZMod N) (hc : IsUnit c) (e : G →+ G →+ ZMod N)
    (he : ∀ a, (∀ b, e a b = 0) → a = 0) (hσ : ∀ a b, e (σ a) (σ b) = c * e a b)
    (hστ : ∀ a, σ (τ a) = c • a) (hτσ : ∀ a, τ (σ a) = c • a) {P : (ZMod N)[X]}
    (hP : (LinearMap.toMatrix b b σ).charpoly = P) :
    (∀ j ≤ d, P.coeff 0 * P.coeff j = c ^ (d - j) * P.coeff (d - j)) ∧
      LinearMap.trace (ZMod N) G τ = -P.nextCoeff := by
  have : Module.Free (ZMod N) G := Module.Free.of_basis b
  have : Module.Finite (ZMod N) G := Module.Finite.of_basis b
  have hrank : Module.finrank (ZMod N) G = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hP
  refine ⟨fun j hj => ?_, ?_⟩
  · have := Stacks.Picard.charpoly_coeff_zero_mul_coeff_eq_of_pairing σ τ c hc e he hσ hστ hτσ j
      (by rwa [hrank])
    rwa [hrank, ← LinearMap.charpoly_toMatrix σ b] at this
  · rw [← Stacks.Picard.trace_eq_of_pairing σ τ c hc e he hσ hστ,
      LinearMap.trace_eq_matrix_trace (ZMod N) b, Matrix.trace_eq_neg_charpoly_nextCoeff]

/-- **Weil's trace formula for a twisted Frobenius of a curve, in `Pic[ℓⁿ]` form**, proved.
For `C` a smooth proper curve of genus `γ` over an algebraically closed field `Ω` algebraic over
`𝔽_p`, `φ` an endomorphism of `C` over `Ω` and `Ψ` an automorphism of the scheme `C` with
`Ψ ≫ φ = F^f`, `q = p^f`, and `ℓ ≠ p`:
`#{c ∈ C(Ω) : φ c = c} = 1 - Tr(φ^* | Pic(C)[ℓⁿ]) + deg φ` in `ℤ/ℓⁿ`.

The zeta function of `Ψ` (`Stacks.Zeta.exists_zeta_roots_of_twistedFrobenius`) gives
`N₁ = 1 + q - ∑ αᵢ`; the Frobenius `F_J` of the jacobian
(`Stacks.Zeta.exists_normForm_natCard_ker_twistedFrobenius`) has a characteristic polynomial
`χ ∈ ℚ[X]` of degree `2γ` computing kernel counts, which is the `ℓ`-adic characteristic polynomial
of `Ψ^*` on the `Pic⁰[ℓ^N]` (`Stacks.Picard.exists_charpoly_levelMatrix_eq_of_normForm`); the
Weil pairing (`Stacks.Picard.exists_weilPairing_of_twist`) makes `χ` symmetric under
`b ↦ q / b` (`Stacks.Picard.charpoly_coeff_zero_mul_coeff_eq_of_pairing`), so that the
reciprocal roots of the zeta function are the roots of `χ`
(`Stacks.Zeta.nextCoeff_eq_neg_sum_of_zeta`) and `Tr(Ψ^*) = ∑ αᵢ`; the pairing also gives
`Tr(φ^*) = Tr(Ψ^*)` (`Stacks.Picard.trace_eq_of_pairing`, `Ψ^* φ^* = q`), and `deg φ = q`
(`AlgebraicGeometry.degreeOver_eq_pow_of_comp_eq_absoluteFrobeniusPow`). The `Ω`-points fixed
by `φ` are the closed points fixed by `Ψ`, as `φ = F^f ≫ Ψ⁻¹` and `F` is the identity on
points. -/
theorem weilTraceInput : WeilTraceInput := by
  intro Ω _ _ p _ _ halg C g _ _ _ φ w hnc f hf hC Ψ hΨ ℓ n _ hℓ hn
  classical
  have hℓp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓp.ne_zero⟩
  have hpp : p.Prime := Fact.out
  have hpℓ : p ≠ ℓ := fun h => hℓ (h ▸ CharP.cast_eq_zero Ω p)
  have hdim : topologicalKrullDim C ≤ 1 := Stacks.Zeta.topologicalKrullDim_le_one g
  have hΨs := Stacks.Zeta.hom_comp_eq_of_hom_comp_eq_absoluteFrobeniusPow p g φ w hC f Ψ hΨ
  have hφΨ : φ ≫ Ψ.hom = absoluteFrobeniusPow C p hC f := by
    rw [← cancel_epi Ψ.hom, ← Category.assoc, hΨ,
      AlgebraicGeometry.absoluteFrobeniusPow_naturality Ψ.hom p hC hC f]
  -- the fixed points
  have hfix :=
    natCard_fixedSections_eq_natCard_fixedClosedPoints_of_comp_eq_absoluteFrobeniusPow g φ w p hC f
      Ψ hφΨ
  -- the degree of `φ`
  have hdegφ := AlgebraicGeometry.degreeOver_eq_pow_of_comp_eq_absoluteFrobeniusPow p g hC φ w hnc
    f hf Ψ hΨ
  -- the zeta function
  obtain ⟨-, hfinH, r, α, hr, hαint, hzeta⟩ :=
    Stacks.Zeta.exists_zeta_roots_of_twistedFrobenius p g f hf halg φ w hC Ψ hΨ
  set q : ℕ := p ^ f
  have hq1 : 1 < q := Nat.one_lt_pow hf.ne' hpp.one_lt
  set γ := genus g
  set deg := Stacks.Picard.picardDegree g hdim
  set Pσ := Stacks.Picard.schemePullbackClassHom Ψ.hom
  set Pφ := Stacks.Picard.schemePullbackClassHom φ
  -- `Ψ^*` on `Pic⁰`
  have hdegΨ : ∀ L, deg (Pσ L) = deg L :=
    Stacks.Picard.picardDegree_schemePullbackClassHom_of_twist g hdim Ψ.hom
      (iterateFrobeniusEquiv Ω p f) hΨs
  let u : deg.ker →+ deg.ker := (Pσ.comp deg.ker.subtype).codRestrict deg.ker fun c => by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hdegΨ]
    exact c.2
  obtain ⟨χ, hmon, hχdeg, hnf, hker, htors⟩ :=
    Stacks.Zeta.exists_normForm_natCard_ker_twistedFrobenius p g hdim f hf Ψ.hom hΨs u
      (fun c => rfl)
  let instP : ∀ N : ℕ, Module (ZMod (ℓ ^ N)) (Submodule.torsionBy ℤ deg.ker ((ℓ : ℤ) ^ N)) :=
    fun N => AddCommGroup.zmodModule fun x => by
      ext1
      simp [← natCast_zsmul]
  obtain ⟨F, hFχ, hFlev⟩ := Stacks.Picard.exists_charpoly_levelMatrix_eq_of_normForm u p hpp hpℓ
    (fun N => htors ℓ N hℓp hℓ) χ hmon hχdeg hker
  -- `Pic⁰(C)[ℓ^N] ≅ Pic(C)[ℓ^N]`, and `Ψ^*`, `φ^*` there
  let eN : ∀ N : ℕ, Submodule.torsionBy ℤ deg.ker ((ℓ : ℤ) ^ N) ≃ₗ[ZMod (ℓ ^ N)]
      Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ N) := fun N =>
    Stacks.Picard.zmodLinearEquiv (ℓ ^ N) (torsionByKerAddEquiv deg
      (pow_ne_zero N (by exact_mod_cast hℓp.ne_zero)))
  let tN : (C ⟶ C) → ∀ N : ℕ, Module.End (ZMod (ℓ ^ N))
      (Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ N)) :=
    fun a N => (Stacks.Picard.torsionByRestrict (A := Stacks.Picard.ofScheme C)
      (Stacks.Picard.schemePullbackClassHom a)
      ((ℓ : ℤ) ^ N)).toZModLinearMap (ℓ ^ N)
  let σN := tN Ψ.hom
  let τN := tN φ
  have hconj : ∀ N, (eN N).conj (Stacks.Picard.levelMap u N) = σN N := fun N =>
    LinearMap.ext fun x => Subtype.ext rfl
  have hcomp : ∀ (N : ℕ) (a b : C ⟶ C), a ≫ b = absoluteFrobeniusPow C p hC f →
      ∀ x, tN a N (tN b N x) = (q : ZMod (ℓ ^ N)) • x := fun N a b hab x => by
    rw [Nat.cast_smul_eq_nsmul]
    exact torsionByRestrict_schemePullbackClassHom_comp_eq_smul p hC f _ hab x
  -- the Weil pairing
  have hweil : ∀ N : ℕ, ∃ e : Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ N) →+
      Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ N) →+ ZMod (ℓ ^ N),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b, e (σN N a) (σN N b) = (q : ZMod (ℓ ^ N)) * e a b := by
    intro N
    obtain ⟨e, he, heσ⟩ := Stacks.Picard.exists_weilPairing_of_twist g (isUnit_iff_ne_zero.mpr hℓ)
      Ψ.hom (iterateFrobenius Ω p f) q hΨs (fun x => rfl) 1
      (fun L => by simpa only [one_mul] using hdegΨ L) N
    refine ⟨e, he, fun a b => ?_⟩
    show e (Stacks.Picard.torsionByRestrict Pσ _ a) (Stacks.Picard.torsionByRestrict Pσ _ b) = _
    rw [heσ, zsmul_eq_mul]
    push_cast
    ring
  -- the facts at level `ℓ^N`
  have hlevel : ∀ N : ℕ, 0 < N →
      (∀ j ≤ 2 * γ,
        (F.map (PadicInt.toZModPow N)).coeff 0 * (F.map (PadicInt.toZModPow N)).coeff j =
        (q : ZMod (ℓ ^ N)) ^ (2 * γ - j) * (F.map (PadicInt.toZModPow N)).coeff (2 * γ - j)) ∧
      picardTorsionTrace C Pφ ℓ N = -(F.map (PadicInt.toZModPow N)).nextCoeff := by
    intro N hN
    have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN.ne' hℓp.one_lt⟩
    obtain ⟨E⟩ := htors ℓ N hℓp hℓ
    let b := (Stacks.Picard.levelBasis N E).map (eN N)
    have hmat : LinearMap.toMatrix b b (σN N) = Stacks.Picard.levelMatrix u N E := by
      ext i j
      rw [Stacks.Picard.levelMatrix, ← hconj, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
      simp only [b, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    obtain ⟨e, he, heσ⟩ := hweil N
    exact charpoly_symm_and_trace_eq_of_pairing b (σN N) (τN N) (q : ZMod (ℓ ^ N))
      (isUnit_natCast_pow_of_prime_ne hpp hℓp hpℓ f N) e he heσ (hcomp N _ _ hΨ) (hcomp N _ _ hφΨ)
      (by rw [hmat, hFlev N E])
  -- `F` is symmetric, hence so is `χ`
  -- the zeta function and the roots of `χ`
  set h : ℕ → ℕ := fun m => Nat.card {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ Pσ^[m] c = c}
  have hnorm : ∀ m, 0 < m → (h m : ℚ) = Stacks.Polynomial.normForm χ (1 - Polynomial.X ^ m) := by
    intro m hm
    show ((Nat.card {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ Pσ^[m] c = c} : ℕ) : ℚ) = _
    rw [← natCard_ker_one_sub_pow_eq deg Pσ u (fun c => rfl) m]
    exact hker _ (not_dvd_coeff_zero_one_sub_X_pow hpp hm)
  have hh0 : ∀ m, 0 < m → h m ≠ 0 := by
    intro m hm
    have := hfinH m hm
    have : Nonempty {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ Pσ^[m] c = c} :=
      ⟨⟨0, map_zero _, Function.iterate_fixed (map_zero Pσ) m⟩⟩
    exact Nat.card_pos.ne'
  have hnext := Stacks.Zeta.nextCoeff_eq_neg_sum_of_zeta χ hmon γ hχdeg q hq1
    (coeff_zero_mul_coeff_eq_of_toZModPow hFχ q (2 * γ) fun N hN => (hlevel N hN).1)
    (coeff_zero_nonneg_of_normForm_X_nonneg hmon hχdeg hnf) r α hr hαint h
    (fun m hm => (hzeta m hm).2.1) hh0 (fun m hm => (hzeta m hm).2.2) hnorm
  set N₁ := Nat.card {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[1] x = x}
  have h1 := (hzeta 1 one_pos).1
  simp only [pow_one] at h1
  have hχnext : χ.nextCoeff = (((N₁ : ℤ) - 1 - q : ℤ) : ℚ) := by
    apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    rw [hnext]
    push_cast
    linear_combination -h1
  have hinj : Function.Injective (PadicInt.Coe.ringHom (p := ℓ)) := Subtype.coe_injective
  have hFnext : F.nextCoeff = (((N₁ : ℤ) - 1 - q : ℤ) : ℤ_[ℓ]) := by
    apply hinj
    rw [← nextCoeff_map hinj, hFχ, nextCoeff_map (algebraMap ℚ ℚ_[ℓ]).injective, hχnext,
      map_intCast, map_intCast]
  -- the conclusion
  have : Fact (1 < ℓ ^ n) := ⟨Nat.one_lt_pow (by omega) hℓp.one_lt⟩
  rw [hfix, hdegφ, (hlevel n (by omega)).2,
    nextCoeff_map_eq_of_isUnit_leadingCoeff _
      (by simp [(monic_of_map_coe_eq_map hFχ hmon).leadingCoeff]),
    hFnext, map_intCast]
  push_cast
  ring

end Stacks.EtaleCohomology
