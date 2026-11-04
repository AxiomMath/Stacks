module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TwistNegOneTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityInput

/-!
# The Tate twist as an operation on all ℓ-adic sheaves, and its trace property

`Stacks.EtaleCohomology.LAdicSheaf.twistNegOne` is defined for a lisse ℓ-adic sheaf on a scheme
over a field in which `ℓ` is invertible. Extending it by the identity elsewhere gives an operation
`Stacks.EtaleCohomology.LAdicSheaf.twistNegOneOp` on all ℓ-adic sheaves on all Noetherian schemes
of a big étale site. It satisfies `Stacks.EtaleCohomology.LAdicTwistInput`
(`Stacks.EtaleCohomology.LAdicSheaf.lAdicTwistInput_twistNegOneOp`): over a finite field of
characteristic `p ≠ ℓ`, the twist of a lisse sheaf is lisse and multiplies the Frobenius traces at
a closed point `x` by `#κ(x)^m`
(`Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_twistNegOne_pow`).

## Main definitions

* `Stacks.EtaleCohomology.IsInvertibleOverField`: `ℓ` is invertible on `X` through a structure
  map to the spectrum of a field.
* `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneOp`: `F(-1)` for `F` lisse on a scheme over a
  field in which `ℓ` is invertible, and `F` otherwise.
* `Stacks.EtaleCohomology.LAdicSheaf.padicTowerTwistNegOneOpIso`: the tower of levels of the
  total twist of a lisse sheaf is `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.lAdicTwistInput_twistNegOneOp`: the total twist satisfies
  `Stacks.EtaleCohomology.LAdicTwistInput`.
* `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTower_eq`: the twisted tower does not depend on
  the structure map to a field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ℓ` is invertible on `X` through a structure map to the spectrum of a field. -/
def IsInvertibleOverField (X : Scheme.{u}) (ℓ : ℕ) : Prop :=
  ∃ (k : Type u) (_ : Field k) (_ : X ⟶ Spec (.of k)), (ℓ : k) ≠ 0

open Classical in
/-- **The Tate twist as a total operation**: `F(-1)` when `F` is lisse on a scheme over a field in
which `ℓ` is invertible, and `F` otherwise. -/
def LAdicSheaf.twistNegOneOp (X : B.Scheme) [IsNoetherian X.1] (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.{u, u + 1} B X ℓ :=
  if h : IsInvertibleOverField X.1 ℓ ∧ F.IsLisse then
    letI : Field h.1.choose := h.1.choose_spec.choose
    haveI : NeZero (ℓ : h.1.choose) := ⟨h.1.choose_spec.choose_spec.choose_spec⟩
    LAdicSheaf.twistNegOne h.1.choose_spec.choose_spec.choose h.2
  else F

/-- **The Tate twist satisfies the trace property `LAdicTwistInput`**: over a finite field of
characteristic `p ≠ ℓ` the twist of a lisse sheaf is lisse, with Frobenius traces at a closed
point `x` multiplied by `#κ(x)^m`. -/
theorem LAdicSheaf.lAdicTwistInput_twistNegOneOp :
    LAdicTwistInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ) := by
  intro k _ _ p n _ _ hcard hℓp X _ fX _ F hF
  have hk : IsInvertibleOverField X.1 ℓ := ⟨k, inferInstance, fX, fun h0 => hℓp
    ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1
      ((CharP.cast_eq_zero_iff k p ℓ).1 h0)).symm⟩
  have h : IsInvertibleOverField X.1 ℓ ∧ F.IsLisse := ⟨hk, hF⟩
  let : Field h.1.choose := h.1.choose_spec.choose
  have : NeZero (ℓ : h.1.choose) := ⟨h.1.choose_spec.choose_spec.choose_spec⟩
  have key : ∀ T : LAdicSheaf.{u, u + 1} B X ℓ,
      T = LAdicSheaf.twistNegOne h.1.choose_spec.choose_spec.choose hF →
      T.IsLisse ∧ ∀ (x : closedPoints X.1) (m : ℕ),
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ T x.1
            (finite_residueField fX x.1 x.2) ^ m) =
          (Nat.card (X.1.residueField x.1) : ℚ_[ℓ]) ^ m *
            LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1
              (finite_residueField fX x.1 x.2) ^ m) := by
    rintro T rfl
    refine ⟨LAdicSheaf.isLisse_twistNegOne _ hF, fun x m => ?_⟩
    have : Finite (X.1.residueField x.1) := finite_residueField fX x.1 x.2
    exact LAdicSheaf.trace_rationalStalkFrobenius_twistNegOne_pow _ hF x.1 _ m
  exact key _ (dite_eq_left h)

variable {B ℓ} in
/-- The twisted tower does not depend on the structure map to a field. -/
theorem LAdicSheaf.twistNegOneTower_eq {X : B.Scheme} [IsNoetherian X.1] {k k' : Type u} [Field k]
    [Field k'] (fX : X.1 ⟶ Spec (.of k)) (fX' : X.1 ⟶ Spec (.of k')) [NeZero (ℓ : k)]
    [NeZero (ℓ : k')] (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.twistNegOneTower fX F = LAdicSheaf.twistNegOneTower fX' F :=
  rfl

variable {B ℓ} in
/-- **The tower of levels of the total twist of a lisse sheaf on a scheme over a field in which `ℓ`
is invertible is `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)`.** -/
def LAdicSheaf.padicTowerTwistNegOneOpIso {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k]
    (fX : X.1 ⟶ Spec (.of k)) [NeZero (ℓ : k)] {F : LAdicSheaf.{u, u + 1} B X ℓ} (hF : F.IsLisse) :
    LAdicSheaf.padicTower B X ℓ (LAdicSheaf.twistNegOneOp B ℓ X F) ≅
      LAdicSheaf.twistNegOneTower fX F :=
  have h : IsInvertibleOverField X.1 ℓ ∧ F.IsLisse := ⟨⟨k, inferInstance, fX, NeZero.ne _⟩, hF⟩
  letI : Field h.1.choose := h.1.choose_spec.choose
  haveI : NeZero (ℓ : h.1.choose) := ⟨h.1.choose_spec.choose_spec.choose_spec⟩
  eqToIso (congrArg (LAdicSheaf.padicTower B X ℓ) (dite_eq_left h)) ≪≫
    LAdicSheaf.padicTowerTwistNegOneIso h.1.choose_spec.choose_spec.choose hF ≪≫
    eqToIso (LAdicSheaf.twistNegOneTower_eq _ fX F)

end Stacks.EtaleCohomology

end
