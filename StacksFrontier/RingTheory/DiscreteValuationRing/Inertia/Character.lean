module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.RingTheory.DiscreteValuationRing.Galois
public import StacksFrontier.RingTheory.Invariant.Primes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Wild and tame inertia for a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `K`, let `L / K` be a finite Galois
extension, let `B` be the integral closure of `A` in `L`, and let `P` be a maximal ideal of `B`.
The *inertia character* is the canonical homomorphism from the inertia group at `P` to the group
of `e`-th roots of unity in the residue field `B / P`, where `e` is the ramification index; its
kernel is the *wild inertia group* `P`, and the quotient of inertia by it is the *tame inertia
group* `I_t`. The inertia character is equivariant for conjugation by the decomposition group,
and raising it to the residue-characteristic-primary part of `e` gives the canonical character
identifying `I_t` with the roots of unity of order the prime-to-`p` part of `e`.

The subring of `B` fixed by the inertia group is the integral closure of `A` in the corresponding
fixed field, and its localization at the prime below `P` is étale over `A`. More completely, the
fixed fields and invariant rings of the wild inertia, inertia and decomposition groups form a
tower whose field extensions, primes, local rings, ramification indices and residue fields have
the standard Galois-theoretic description. In a tower `M / L / K` of finite Galois extensions,
restriction surjects the decomposition, inertia and wild inertia groups at a maximal ideal of the
integral closure in `M` onto the corresponding groups at its contraction, compatibly with the
actions on residue fields and with the canonical inertia characters.

## Main definitions

* `IsDiscreteValuationRing.inertiaCharacter`: the canonical character from inertia to the roots
  of unity of order the ramification index in the residue field.
* `IsDiscreteValuationRing.wildInertiaGroup`: the wild inertia group, the kernel of that
  character.
* `IsDiscreteValuationRing.tameInertiaGroup` and `IsDiscreteValuationRing.tameInertiaMap`: the
  tame inertia group, namely inertia modulo wild inertia, and the quotient map.
* `IsDiscreteValuationRing.tameInertiaEquivRootsOfUnity`: the induced isomorphism from tame
  inertia to the roots of unity.
* `IsDiscreteValuationRing.wildRamificationFactor` and
  `IsDiscreteValuationRing.tameRamificationIndex`: the residue-characteristic-primary part of the
  ramification index and its prime-to-residue-characteristic part.
* `IsDiscreteValuationRing.canonicalInertiaCharacter`: the inertia character raised to the wild
  factor.

## Main results

* `IsDiscreteValuationRing.wildInertiaGroup_eq_ker_inertiaCharacter` and
  `IsDiscreteValuationRing.tameInertiaEquivRootsOfUnity_apply_mk`: wild inertia is the kernel of
  the inertia character, and the induced isomorphism is the one it determines.
* `IsDiscreteValuationRing.inertiaCharacter_conj`: equivariance of the inertia character under
  the decomposition group.
* `IsDiscreteValuationRing.inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization`: the
  inertia-invariant ring is an integral closure, and its localization below `P` is étale.
* `IsDiscreteValuationRing.decomposition_inertia_wildInertia_tower`: the complete decomposition,
  inertia and wild inertia tower at `P`.
* `IsDiscreteValuationRing.surjective_restrictions_commute_with_residue_and_inertiaCharacter`:
  the three surjections and the two canonical commutative squares in a tower.
* `IsDiscreteValuationRing.canonicalInertiaCharacter_spec`: the canonical description of the
  character induced on tame inertia, its equivariance and its naturality square in a tower.

## Implementation notes

Tag 09EE supplies the wild subgroup and the canonical character existentially; that data is
packaged once, together with the intrinsic uniformizer-ratio property
`IsDiscreteValuationRing.IsInertiaCharacter` which makes the character canonical, before the
terminology of the wild and tame groups is introduced. The action on roots of unity used for
equivariance is the restriction of the ring automorphism of the residue field induced by an
element of the decomposition group.

The invariant rings are Mathlib's `FixedPoints.subalgebra` and the fixed fields are
`IntermediateField.fixedField`; the canonical embedding of an invariant ring into its fixed field
equips the former with the algebra structure used by `IsIntegralClosure`. Contractions are
`Ideal.under`, so the prime `P.under B'` is the intersection `B' ∩ P`. Ramification indices are
stated on the invariant rings, which is the invariant-ring form of the indices of the
corresponding localized discrete valuation rings. The order `|I_t|` is represented by
`Nat.ordCompl` of the ramification index, and the theorem identifies that number with the
cardinality of tame inertia. Vertical maps in the tower squares are given as uniquely
characterized maps: the characterizing equations express restriction of residue automorphisms and
the `e' / e`-power formula, which records their canonical nature without choosing presentations
of the residue fields.

## References

* [The Stacks Project, Tag 09EH](https://stacks.math.columbia.edu/tag/09EH)
* [The Stacks Project, Tag 0BU4](https://stacks.math.columbia.edu/tag/0BU4)
* [The Stacks Project, Tag 0BU5](https://stacks.math.columbia.edu/tag/0BU5)
* [The Stacks Project, Tag 0BU6](https://stacks.math.columbia.edu/tag/0BU6)
* [The Stacks Project, Tag 0BU7](https://stacks.math.columbia.edu/tag/0BU7)
* [The Stacks Project, Tag 0BU8](https://stacks.math.columbia.edu/tag/0BU8)
-/

@[expose] public section

open scoped Pointwise

namespace IsDiscreteValuationRing

section InertiaCharacter

variable
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]

/-- The action of `Gal(L/K)` on the integral closure of `A` in `L` by ring automorphisms. -/
noncomputable local instance : MulSemiringAction Gal(L/K) (integralClosure A L) :=
  IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)

/-- The uniformizer-ratio property intrinsically characterizing the inertia character. -/
def IsInertiaCharacter
    (θ : P.inertia Gal(L/K) →*
      rootsOfUnity (P.ramificationIdx A) (integralClosure A L ⧸ P)) : Prop :=
  ∀ (σ : P.inertia Gal(L/K)) (x a : integralClosure A L), x ∈ P → x ∉ P ^ 2 →
    Ideal.Quotient.mk P a = (θ σ).1.1 → (σ : Gal(L/K)) • x - a * x ∈ P ^ 2

/-- A normal subgroup `wild` of the inertia group at `P` together with a surjective character
`character` from inertia onto the `e`-th roots of unity of the residue field, `e` the ramification
index, whose kernel is `wild`, and which is the unique homomorphism satisfying
`IsInertiaCharacter`. -/
structure InertiaCharacterData where
  /-- The wild inertia subgroup. -/
  wild : Subgroup (P.inertia Gal(L/K))
  /-- The wild inertia subgroup is normal. -/
  wild_normal : wild.Normal
  /-- The inertia character. -/
  character : P.inertia Gal(L/K) →*
    rootsOfUnity (P.ramificationIdx A) (integralClosure A L ⧸ P)
  /-- The sequence `wild → inertia → roots of unity` is exact. -/
  exact : Function.MulExact wild.subtype character
  surjective : Function.Surjective character
  characterizes : IsInertiaCharacter A K L P character
  character_unique : ∀ θ, IsInertiaCharacter A K L P θ → θ = character

/-- Inertia-character data exists for every maximal ideal `P`. -/
theorem inertiaCharacterData_nonempty : Nonempty (InertiaCharacterData A K L P) := by
  classical
  let B := integralClosure A L
  let D := MulAction.stabilizer Gal(L/K) P
  let I := P.inertia Gal(L/K)
  let inclusion : I →* D := I.subtype.codRestrict D
    (fun σ ↦ Ideal.inertia_le_stabilizer (M := Gal(L/K)) P σ.property)
  obtain ⟨W, hW, -, -, -, -, -, -, θ, -, hexact, hsurj, -, -, hcharacter, hunique⟩ :=
    exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity A K L P
  exact ⟨⟨W, hW, θ, hexact, hsurj, hcharacter, hunique⟩⟩

/-- A choice of inertia-character data at `P`. -/
noncomputable def inertiaCharacterData : InertiaCharacterData A K L P :=
  Classical.choice (inertiaCharacterData_nonempty A K L P)

/-- **Stacks Project, Tag 0BU4.** The canonical character from inertia to the roots of unity of
order the ramification index in the residue field. -/
@[stacks 0BU4]
noncomputable def inertiaCharacter := (inertiaCharacterData A K L P).character

/-- **Stacks Project, Tag 0BU4.** The wild inertia group at `P`. -/
@[stacks 0BU4, sga "1 XIII 2.0" "partial"]
noncomputable def wildInertiaGroup := (inertiaCharacterData A K L P).wild

/-- The wild inertia group is a normal subgroup of the inertia group. -/
instance wildInertiaGroup_normal : (wildInertiaGroup A K L P).Normal :=
  (inertiaCharacterData A K L P).wild_normal

/-- **Stacks Project, Tag 0BU4.** The tame inertia group, namely inertia modulo wild inertia. -/
@[stacks 0BU4, sga "7 I 0.3"]
abbrev tameInertiaGroup := P.inertia Gal(L/K) ⧸ wildInertiaGroup A K L P

/-- **Stacks Project, Tag 0BU4.** The quotient map from inertia to tame inertia. -/
@[stacks 0BU4]
noncomputable def tameInertiaMap : P.inertia Gal(L/K) →* tameInertiaGroup A K L P :=
  QuotientGroup.mk' (wildInertiaGroup A K L P)

/-- Wild inertia is the kernel of the canonical inertia character. -/
@[sga "1 XIII 2.0" "partial"]
theorem wildInertiaGroup_eq_ker_inertiaCharacter :
    wildInertiaGroup A K L P = MonoidHom.ker (inertiaCharacter A K L P) := by
  simpa [wildInertiaGroup, inertiaCharacter] using
    (inertiaCharacterData A K L P).exact.monoidHom_ker_eq.symm

/-- **Stacks Project, Tag 0BU4.** The canonical isomorphism from tame inertia to the roots of
unity induced by the inertia character. -/
@[stacks 0BU4, sga "7 I 0.3" "finite Galois case"]
noncomputable def tameInertiaEquivRootsOfUnity :
    tameInertiaGroup A K L P ≃*
      rootsOfUnity (P.ramificationIdx A) (integralClosure A L ⧸ P) :=
  (QuotientGroup.quotientMulEquivOfEq
      (wildInertiaGroup_eq_ker_inertiaCharacter A K L P)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (inertiaCharacter A K L P)
      (inertiaCharacterData A K L P).surjective)

/-- The canonical inertia character satisfies its intrinsic uniformizer-ratio property. -/
theorem inertiaCharacter_characterizes :
    IsInertiaCharacter A K L P (inertiaCharacter A K L P) :=
  (inertiaCharacterData A K L P).characterizes

/-- The uniformizer-ratio property uniquely determines the canonical inertia character. -/
theorem inertiaCharacter_eq
    (θ : P.inertia Gal(L/K) →*
      rootsOfUnity (P.ramificationIdx A) (integralClosure A L ⧸ P))
    (hθ : IsInertiaCharacter A K L P θ) : θ = inertiaCharacter A K L P :=
  (inertiaCharacterData A K L P).character_unique θ hθ

/-- The canonical isomorphism on tame inertia is induced by the inertia character. -/
@[sga "7 I 0.3" "partial"]
theorem tameInertiaEquivRootsOfUnity_apply_mk (σ : P.inertia Gal(L/K)) :
    tameInertiaEquivRootsOfUnity A K L P (tameInertiaMap A K L P σ) =
      inertiaCharacter A K L P σ := by
  rfl

end InertiaCharacter

/-- **Stacks Tag 0BU5.** The inertia character is equivariant for conjugation by the
decomposition group: conjugating an inertia element by a decomposition element has character
equal to the image of the original character under the induced residue-field automorphism. -/
@[stacks 0BU5, sga "7 I 0.3" "finite Galois case"]
theorem inertiaCharacter_conj
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    let D := MulAction.stabilizer Gal(L/K) P
    let I := P.inertia Gal(L/K)
    let e := P.ramificationIdx A
    let conjugate : D → I → I := fun τ σ ↦
      ⟨(τ : Gal(L/K)) * (σ : Gal(L/K)) * (τ : Gal(L/K))⁻¹, by
        rw [Ideal.mem_inertia]
        intro x
        have hσ := (Ideal.mem_inertia.mp σ.property) ((τ : Gal(L/K))⁻¹ • x)
        have hτ := Ideal.smul_mem_pointwise_smul (τ : Gal(L/K)) _ P hσ
        rw [τ.property] at hτ
        simpa only [mul_smul, smul_sub, smul_inv_smul] using hτ⟩
    ∀ (θ : I →* rootsOfUnity e (B ⧸ P)),
      (∀ (σ : I) (x a : B), x ∈ P → x ∉ P ^ 2 →
        Ideal.Quotient.mk P a = (θ σ).1.1 →
        (σ : Gal(L/K)) • x - a * x ∈ P ^ 2) →
      ∀ (τ : D) (σ : I),
        θ (conjugate τ σ) =
          (Ideal.quotientEquiv P P
            ((MulSemiringAction.toRingEquiv Gal(L/K) B) (τ : Gal(L/K)))
            τ.property.symm).toMulEquiv.restrictRootsOfUnity e (θ σ) := by
  intro B D I e conjugate θ hθ τ σ
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let Q := Ideal.quotientEquiv P P
    ((MulSemiringAction.toRingEquiv Gal(L/K) (integralClosure A L)) (τ : Gal(L/K)))
    τ.property.symm
  let E := Q.toMulEquiv.restrictRootsOfUnity (P.ramificationIdx A)
  let c : P.inertia Gal(L/K) →* P.inertia Gal(L/K) :=
    { toFun := conjugate τ
      map_one' := Subtype.ext (by simp [conjugate])
      map_mul' := fun ρ υ ↦ Subtype.ext (by simp [conjugate, mul_assoc]) }
  let θ' : P.inertia Gal(L/K) →* rootsOfUnity (P.ramificationIdx A)
      (integralClosure A L ⧸ P) := E.symm.toMonoidHom.comp (θ.comp c)
  have hθ' : ∀ (ρ : P.inertia Gal(L/K)) (x a : integralClosure A L),
      x ∈ P → x ∉ P ^ 2 → Ideal.Quotient.mk P a = (θ' ρ).1.1 →
      (ρ : Gal(L/K)) • x - a * x ∈ P ^ 2 := by
    intro ρ x a hx hx2 ha
    have hp2inv : ((τ : Gal(L/K))⁻¹) • (P ^ 2) = P ^ 2 := by
      rw [inv_smul_eq_iff, Ideal.pointwise_smul_def, Ideal.map_pow,
        ← Ideal.pointwise_smul_def, τ.property]
    have hy : (τ : Gal(L/K)) • x ∈ P := by
      have := Ideal.smul_mem_pointwise_smul (τ : Gal(L/K)) x P hx
      rwa [τ.property] at this
    have hy2 : (τ : Gal(L/K)) • x ∉ P ^ 2 := by
      intro h
      have h' := Ideal.smul_mem_pointwise_smul
        ((τ : Gal(L/K))⁻¹) ((τ : Gal(L/K)) • x) (P ^ 2) h
      rw [hp2inv] at h'
      exact hx2 (by simpa only [inv_smul_smul] using h')
    have ha' : Ideal.Quotient.mk P ((τ : Gal(L/K)) • a) = (θ (c ρ)).1.1 := by
      calc
        Ideal.Quotient.mk P ((τ : Gal(L/K)) • a) = Q (Ideal.Quotient.mk P a) := by
          symm
          exact Ideal.quotientEquiv_mk P P _ _ a
        _ = Q ((θ' ρ).1.1) := congrArg Q ha
        _ = (θ (c ρ)).1.1 := by
          change Q (Q.symm ((θ (c ρ)).1.1)) = (θ (c ρ)).1.1
          exact Q.apply_symm_apply _
    have h := hθ (c ρ) ((τ : Gal(L/K)) • x) ((τ : Gal(L/K)) • a) hy hy2 ha'
    have h' := Ideal.smul_mem_pointwise_smul ((τ : Gal(L/K))⁻¹)
      ((c ρ : Gal(L/K)) • ((τ : Gal(L/K)) • x) -
        ((τ : Gal(L/K)) • a) * ((τ : Gal(L/K)) • x)) (P ^ 2) h
    rw [hp2inv] at h'
    change ((τ : Gal(L/K))⁻¹) •
      (((τ : Gal(L/K)) * (ρ : Gal(L/K)) * (τ : Gal(L/K))⁻¹) •
        ((τ : Gal(L/K)) • x) -
        ((τ : Gal(L/K)) • a) * ((τ : Gal(L/K)) • x)) ∈ P ^ 2 at h'
    simpa only [smul_sub, smul_mul', mul_smul, inv_smul_smul] using h'
  obtain ⟨W, hW, -, -, -, -, -, -, θ₀, -, -, -, -, -, hθ₀, huniq⟩ :=
    exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity A K L P
  have heq : θ' = θ := (huniq θ' hθ').trans (huniq θ hθ).symm
  have happ := DFunLike.congr_fun heq σ
  change E.symm (θ (c σ)) = θ σ at happ
  change θ (c σ) = E (θ σ)
  calc
    θ (c σ) = E (E.symm (θ (c σ))) := (E.apply_symm_apply _).symm
    _ = E (θ σ) := congrArg E happ

end IsDiscreteValuationRing
