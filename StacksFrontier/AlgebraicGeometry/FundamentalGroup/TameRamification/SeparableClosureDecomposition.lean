module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.SeparableClosureInertia
public import StacksFrontier.RingTheory.Invariant.Primes
import all StacksFrontier.RingTheory.Invariant.Primes

/-!
# The decomposition exact sequence at a separable closure

Let `A` be a discrete valuation ring with fraction field `K`, let `L` be a separable closure
of `K` and let `B` be the integral closure of `A` in `L`.  At a maximal ideal `P` of `B` the
residue field `B ⧸ P` is an algebraic closure of the residue field `A ⧸ (P.under A)`, and the
decomposition group at `P` acts on the separable closure of `A ⧸ (P.under A)` inside it.  That
action is surjective and its kernel is the inertia group.

## Main results

* `Stacks.FundamentalGroup.isAlgClosure_quotient_integralClosure`: the residue field at `P` is
  an algebraic closure of the residue field of `A`.
* `Stacks.FundamentalGroup.exists_residueSeparableClosureHom`: the exact sequence
  `1 → I → D → Gal(κ^sep/κ) → 1`.

## Implementation notes

The residue field of `A` is the quotient by `P.under A`, which is the maximal ideal of `A`, and
`κ^sep` is `separableClosure` taken inside the residue field at `P`; that this really is a
separable closure of `κ` is part of the statement.  The map `D → Gal(κ^sep/κ)` is the
restriction to `κ^sep` of Mathlib's residue action `Ideal.Quotient.stabilizerHom`, and the
characterization by that restriction is recorded, so the map is pinned down rather than merely
asserted to exist.  Exactness at `D` is the equality of the image in `Gal(L/K)` of the kernel
with the inertia group, together with the inclusion of the inertia group in the decomposition
group.  Surjectivity comes from the profinite surjectivity of the residue action together with
the surjectivity of restriction to a normal subextension; injectivity of the restriction uses
that `κ̄` is purely inseparable over `κ^sep`.  `IsAlgClosure` takes the torsion-freeness of
`κ̄` over `κ` as an instance argument; it holds because `κ` is a field, and is recorded as
`isTorsionFree_quotient_under` and used here as a local instance.

## References

* [Stacks Project, Tag 0BUB](https://stacks.math.columbia.edu/tag/0BUB)
-/

@[expose] public noncomputable section

open scoped Pointwise

universe u v w

namespace Stacks.FundamentalGroup

/-- An automorphism of an algebraic normal extension `E / F` is determined by its restriction to
the separable closure of `F` in `E`, since `E` is purely inseparable over that closure. -/
private lemma restrictNormalHom_separableClosure_injective
    (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]
    [Normal F E] :
    Function.Injective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (separableClosure F E)) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix : ∀ x ∈ separableClosure F E, σ x = x :=
    (AlgEquiv.restrictNormal_eq_one_iff (separableClosure F E) σ).mp hσ
  have h : ({ σ.toRingEquiv.toRingHom with commutes' := fun y ↦ hfix (y : E) y.2 } :
      E →ₐ[separableClosure F E] E) = AlgHom.id (separableClosure F E) E :=
    Subsingleton.elim _ _
  exact AlgEquiv.ext fun x ↦
    congrArg (fun g : E →ₐ[separableClosure F E] E ↦ g x) h

/-- The Galois action on the integral closure of `A` in `L` commutes with the action of `A`. -/
private lemma smulCommClass_gal_integralClosure
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    SMulCommClass Gal(L/K) A (integralClosure A L) :=
  letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  ⟨fun σ a b ↦ by
    simp only [Algebra.smul_def, smul_mul']
    congr 1
    exact (galRestrict A K L (integralClosure A L) σ).commutes a⟩

/-- The decomposition group at a maximal ideal of the integral closure of a discrete valuation
ring in a separable closure of its fraction field surjects onto the automorphism group of the
residue extension. -/
private lemma stabilizerHom_surjective
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI : SMulCommClass Gal(L/K) A (integralClosure A L) :=
      smulCommClass_gal_integralClosure A K L
    Function.Surjective (Ideal.Quotient.stabilizerHom P (P.under A) Gal(L/K)) := by
  have : IsSepClosed L := IsSepClosure.sep_closed K
  have hAlgKL : Algebra.IsAlgebraic K L := IsSepClosure.separable.isAlgebraic
  have : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr hAlgKL
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_algebraic fun x hx ↦ by
      apply IsFractionRing.injective A K
      apply (algebraMap K L).injective
      simpa only [map_zero, ← IsScalarTower.algebraMap_apply A K L] using hx
  let _ := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let _ : TopologicalSpace (integralClosure A L) := ⊥
  have : DiscreteTopology (integralClosure A L) := ⟨rfl⟩
  have : ContinuousSMul Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.continuousSMul A K L (integralClosure A L)
  have : Algebra.IsInvariant A (integralClosure A L) Gal(L/K) :=
    IsIntegralClosure.isInvariant A K L (integralClosure A L)
  have : SMulCommClass Gal(L/K) A (integralClosure A L) :=
    smulCommClass_gal_integralClosure A K L
  exact Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Gal(L/K)) (P.under A) P

attribute [local instance] Ideal.Quotient.field

/-- The residue field at a maximal ideal `P` of an integral extension is torsion-free over the
residue field of the base: both quotients are fields. -/
public theorem isTorsionFree_quotient_under {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (P : Ideal B) [P.IsMaximal] :
    Module.IsTorsionFree (A ⧸ P.under A) (B ⧸ P) :=
  DivisionSemiring.to_moduleIsTorsionFree

attribute [local instance] isTorsionFree_quotient_under

/-- **Stacks 0BUB**, first assertion.  The residue field of the integral closure of a discrete
valuation ring in a separable closure of its fraction field is an algebraic closure of the
residue field of the discrete valuation ring. -/
@[stacks 0BUB "the residue field is an algebraic closure of the residue field of `A`"]
public theorem isAlgClosure_quotient_integralClosure
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    IsAlgClosure (A ⧸ P.under A) (integralClosure A L ⧸ P) where
  isAlgClosed := isAlgClosed_quotient_integralClosure A K L P
  isAlgebraic := Algebra.IsIntegral.isAlgebraic

/-- **Stacks 0BUB**, the first exact sequence.  Write `κ = A ⧸ (P.under A)` for the residue
field of `A` and `κ̄` for the residue field at `P`, an algebraic closure of `κ`, and let
`κ^sep ⊆ κ̄` be the separable closure of `κ`.  The decomposition group `D` at `P` maps to
`Gal(κ^sep/κ)` by restricting the residue action, the inertia group `I` is contained in `D`,
the map is surjective, and the image in `Gal(L/K)` of its kernel is exactly `I`: the sequence
`1 → I → D → Gal(κ^sep/κ) → 1` is exact. -/
@[stacks 0BUB "the exact sequence `1 → I → D → Gal(κ^sep/κ) → 1`"]
public theorem exists_residueSeparableClosureHom
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI : SMulCommClass Gal(L/K) A (integralClosure A L) :=
      ⟨fun σ a b ↦ by
        simp only [Algebra.smul_def, smul_mul']
        congr 1
        exact (galRestrict A K L (integralClosure A L) σ).commutes a⟩
    let κsep := separableClosure (A ⧸ P.under A) (integralClosure A L ⧸ P)
    IsSepClosure (A ⧸ P.under A) κsep ∧
    P.inertia Gal(L/K) ≤ MulAction.stabilizer Gal(L/K) P ∧
    ∃ θ : MulAction.stabilizer Gal(L/K) P →* (κsep ≃ₐ[A ⧸ P.under A] κsep),
      (∀ (σ : MulAction.stabilizer Gal(L/K) P) (x : κsep),
        (θ σ x : integralClosure A L ⧸ P) =
          Ideal.Quotient.stabilizerHom P (P.under A) Gal(L/K) σ (x : integralClosure A L ⧸ P)) ∧
      Function.Surjective θ ∧
      θ.ker.map (MulAction.stabilizer Gal(L/K) P).subtype = P.inertia Gal(L/K) := by
  have halg : IsAlgClosure (A ⧸ P.under A) (integralClosure A L ⧸ P) :=
    isAlgClosure_quotient_integralClosure A K L P
  have hclosed : IsAlgClosed (integralClosure A L ⧸ P) := halg.isAlgClosed
  have : Algebra.IsAlgebraic (A ⧸ P.under A) (integralClosure A L ⧸ P) := halg.isAlgebraic
  have : Normal (A ⧸ P.under A) (integralClosure A L ⧸ P) := IsAlgClosure.normal _ _
  have : IsSepClosed (integralClosure A L ⧸ P) := inferInstance
  let _ := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let _ : SMulCommClass Gal(L/K) A (integralClosure A L) :=
    smulCommClass_gal_integralClosure A K L
  refine ⟨inferInstance, Ideal.inertia_le_stabilizer P,
    (AlgEquiv.restrictNormalHom
        (separableClosure (A ⧸ P.under A) (integralClosure A L ⧸ P))).comp
      (Ideal.Quotient.stabilizerHom P (P.under A) Gal(L/K)), ?_, ?_, ?_⟩
  · intro σ x
    exact AlgEquiv.restrictNormalHom_apply _ _ x
  · exact (AlgEquiv.restrictNormalHom_surjective (F := A ⧸ P.under A)
      (K₁ := separableClosure (A ⧸ P.under A) (integralClosure A L ⧸ P))
      (E := integralClosure A L ⧸ P)).comp (stabilizerHom_surjective A K L P)
  · rw [MonoidHom.ker_comp_of_injective
      (Ideal.Quotient.stabilizerHom P (P.under A) Gal(L/K))
      (AlgEquiv.restrictNormalHom
        (separableClosure (A ⧸ P.under A) (integralClosure A L ⧸ P)))
      (restrictNormalHom_separableClosure_injective (A ⧸ P.under A) (integralClosure A L ⧸ P))]
    exact Ideal.Quotient.map_ker_stabilizer_subtype P (P.under A) Gal(L/K)

end Stacks.FundamentalGroup
