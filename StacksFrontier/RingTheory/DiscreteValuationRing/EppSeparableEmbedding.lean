module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppBaseChangeEmbedding

/-!
# The Hensel-embedded base change at an arbitrary separable residue extension

Condition **(†)** of `EppConditionalDescent` — that the separable algebraic closure of `κ_A`
inside `κ_B` be `κ_A` itself — reduces to one missing datum: an `A`-algebra map `A₁ → B`, whose
residue-field shadow is a compatibility hypothesis on the residue fields.  The reason it is
missing is structural: `A₁` is built as `A[X] ⧸ (P)`, an *abstract* monogenic algebra
over `A`, and nothing in that construction maps it into `B`.

This file supplies the map.  `EppBaseChangeEmbedding` already does exactly this for the **perfect
core** target, via Hensel's lemma; but both of its theorems
(`exists_isWeaklyUnramified_algebraMap_fieldRange_eq_perfectCore` and
`exists_isWeaklyUnramified_nonempty_algHom`) are specialised to that target, carrying
`EppCondition` and `PerfectField (ResidueField A)` hypotheses that the separable case neither
needs nor can supply.  So the embedding is restated here at an arbitrary finite separable
intermediate field.

## Why the separable case is easier, not harder

For the perfect core the simplicity of the root has to be argued; here it is automatic.  A
primitive element `α` of `E / κ_A` has separable minimal polynomial `q` precisely because `E` is
separable over `κ_A`, and a root of a separable polynomial is simple —
`Polynomial.Separable.aeval_derivative_ne_zero`.  That is the whole extra input.  So the Hensel
lift of `AdjoinRoot.exists_algHom_residue_root_eq_of_henselian` applies directly,
and `B` henselian is the only real hypothesis (available for complete `B` through
`henselianLocalRing_of_isAdicComplete_maximalIdeal`).

Note that `α` lives in `E ⊆ κ_B` on the nose, so no search for a root upstairs is needed: `α`
*is* the root, and `minpoly.algebraMap_eq` identifies its minimal polynomial computed in `E` with
the one computed in `κ_B`.

## Main results

* `Stacks.EppTheorem.exists_isWeaklyUnramified_nonempty_algHom_of_isSeparable`: for any
  intermediate field `E` of `κ_B / κ_A` finite and separable over `κ_A`, and `B` henselian, a
  finite weakly unramified extension `A₁ / A` of discrete valuation rings **together with** an
  `A`-algebra map `A₁ → B`.
* `Stacks.EppTheorem.exists_isWeaklyUnramified_nonempty_algHom_separableClosure`: the instance at
  `E = separableClosure κ_A κ_B`, which is the embedding the (†) arrangement was missing.

## References

* [Epp, *Elimination of wild ramification*][epp1973]
* `StacksFrontier.RingTheory.DiscreteValuationRing.EppConditionalDescent` — why (†) is the condition
-/

@[expose] public section

open IsLocalRing Polynomial

namespace Stacks.EppTheorem

universe u v

/-- **The Hensel-embedded base change at a finite separable residue extension.**

Let `A → B` be a local homomorphism of discrete valuation rings with `B` henselian, and let `E`
be an intermediate field of `κ_B / κ_A` which is finite and separable over `κ_A`.  Then there is
a discrete valuation ring `A₁`, finite over `A`, weakly unramified over `A`, admitting an
`A`-algebra map `A₁ → B`.

The construction is the monogenic one: a primitive element `α` of `E / κ_A`, its minimal
polynomial `q`, a monic lift `P ∈ A[X]` of `q`, and `A₁ = A[X] ⧸ (P)`.  What makes the *embedding*
available is that `α` already lies in `κ_B` and is a **simple** root of `q` there — simple because
`q` is separable, by `Polynomial.Separable.aeval_derivative_ne_zero` — so Hensel's lemma over the
henselian `B` lifts it to an `A`-algebra map. -/
theorem exists_isWeaklyUnramified_nonempty_algHom_of_isSeparable {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [Algebra.IsSeparable (ResidueField A) E] [FiniteDimensional (ResidueField A) E] :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧ Nonempty (A₁ →ₐ[A] B) := by
  -- A primitive element of `E / κ_A`, and its minimal polynomial.
  obtain ⟨α, -⟩ := Field.exists_primitive_element (ResidueField A) E
  have hint : IsIntegral (ResidueField A) α := IsIntegral.of_finite (ResidueField A) α
  have hqmonic : (minpoly (ResidueField A) α).Monic := minpoly.monic hint
  have hqirr : Irreducible (minpoly (ResidueField A) α) := minpoly.irreducible hint
  have hqsep : (minpoly (ResidueField A) α).Separable :=
    Algebra.IsSeparable.isSeparable (ResidueField A) α
  have hqdeg : 0 < (minpoly (ResidueField A) α).natDegree := minpoly.natDegree_pos hint
  -- Lift the minimal polynomial to a monic polynomial over `A`.
  obtain ⟨P, hP, hPmap⟩ := exists_monic_lift_map_residue_eq A hqmonic
  have hirr : Irreducible (P.map (residue A)) := hPmap ▸ hqirr
  have hd : 0 < P.natDegree := by
    rwa [← hP.natDegree_map (residue A), hPmap]
  -- `α`, read inside `κ_B`, is a root of the reduction of `P`, and a simple one.
  have hminpoly : minpoly (ResidueField A) ((α : ResidueField B)) = minpoly (ResidueField A) α :=
    minpoly.algebraMap_eq (algebraMap E (ResidueField B)).injective α
  have hrootq : aeval ((α : ResidueField B)) (minpoly (ResidueField A) α) = 0 := by
    have h := minpoly.aeval (ResidueField A) ((α : ResidueField B))
    rwa [hminpoly] at h
  have hroot : aeval ((α : ResidueField B)) (P.map (residue A)) = 0 := by
    rw [hPmap]; exact hrootq
  have hsimple : aeval ((α : ResidueField B)) (derivative (P.map (residue A))) ≠ 0 := by
    rw [hPmap]; exact hqsep.aeval_derivative_ne_zero hrootq
  -- The monogenic algebra, and the Hensel lift of `α`.
  have hlocal := AdjoinRoot.isLocalRing_of_irreducible_map_residue hP hirr
  have hdom := AdjoinRoot.isDomain_of_irreducible_map_residue hP hirr
  have hlh := AdjoinRoot.isLocalHom_of_monic_of_degree_pos (g := P) hP
    (Polynomial.natDegree_pos_iff_degree_pos.mp hd)
  have hdvr := AdjoinRoot.isDiscreteValuationRing hP hirr hd
  have hmf : Module.Finite A (AdjoinRoot P) := hP.finite_adjoinRoot
  have hfs := AdjoinRoot.faithfulSMul_of_monic_of_degree_pos hP
    (Polynomial.natDegree_pos_iff_degree_pos.mp hd)
  have hext : IsDiscreteValuationRing.IsExtension A (AdjoinRoot P) :=
    { toFaithfulSMul := hfs, toIsLocalHom := hlh }
  obtain ⟨φ, -⟩ :=
    AdjoinRoot.exists_algHom_residue_root_eq_of_henselian (A := A) (B := B) hP hroot hsimple
  exact ⟨AdjoinRoot P, inferInstance, hdom, hdvr, inferInstance, hmf, hext,
    AdjoinRoot.ramificationIdx_eq_one hP hirr hd, ⟨φ⟩⟩

/-- **The embedding the (†) arrangement was missing.**

Instantiating `exists_isWeaklyUnramified_nonempty_algHom_of_isSeparable` at
`E = separableClosure κ_A κ_B`: when that closure is finite over `κ_A` and `B` is henselian, the
finite weakly unramified base change realising it comes equipped with an `A`-algebra map into `B`.

This is what makes condition (†) of `EppConditionalDescent` genuinely arrangeable rather than
merely stated: the algebra map supplies the residue-field compatibility such a step takes as a
hypothesis. -/
theorem exists_isWeaklyUnramified_nonempty_algHom_separableClosure {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [FiniteDimensional (ResidueField A)
      (separableClosure (ResidueField A) (ResidueField B))] :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧ Nonempty (A₁ →ₐ[A] B) :=
  exists_isWeaklyUnramified_nonempty_algHom_of_isSeparable
    (separableClosure (ResidueField A) (ResidueField B))

end Stacks.EppTheorem
