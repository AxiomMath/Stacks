module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootDividedPowers
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincare

/-!
# The decomposition of the one-forms of the purely inseparable extension

Let `(B, I, γ)` be a divided power ring which is an `A`-algebra, let `p ≠ 0` and let `λ ∈ B`.
The ring of the proof of Tag 07N1,

`B' = B[z]⟨ξ⟩/(ξ - (z^p - λ)) = B⟨ξ⟩[z]/(z^p - ξ - λ)`,

carries the divided powers `γ'` on `J' = I B' + (ξ)` built in
`StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootDividedPowers`.  This file
computes its module of divided power differentials over `A`:

`Ω¹_{B'/A,γ'} = (B' ⊗_B Ω¹_{B/A,γ}) ⊕ B' · dz`,

which is assumption (07Q1) of Section 60.25 for the extension `B → B'`.  Together with the
identity `d(ξ^[n+1]) = ξ^[n] dξ`, already proved for these modules, this discharges the last two
hypotheses of `Crystalline.exists_homotopyInverse_pthRootExtension`, so the conclusion of
Tag 07N1 for the uncompleted extension becomes a theorem with no inputs about `Ω¹_{B'/A,γ'}`.

The decomposition is obtained by writing down both maps explicitly.  Backwards, the
comparison `ψ : Ω¹_{B/A,γ} → Ω¹_{B'/A,γ'}` of one-forms is induced by the divided power
derivation `b ↦ d(algebraMap b)` of `B`, which is a divided power derivation because
`B → B'` is a divided power morphism, being the composite of the three divided power morphisms
`B → B⟨ξ⟩ → B⟨ξ⟩[z] → B'`; the backward map is `ψ` on the base change summand and multiplication
by `dz` on the free summand.  Forwards, the divided power polynomial formula for `B⟨ξ⟩` and the
polynomial formula for `B⟨ξ⟩[z]` give an `A`-derivation of `B⟨ξ⟩[z]` into
`(B' ⊗_B Ω¹_{B/A,γ}) ⊕ B'` sending `db` to `(1 ⊗ db, 0)`, `dξ` to `(-(1 ⊗ dλ), p z^{p-1})` and
`dz` to `(0, 1)`.  Differentiating `z^p - ξ - λ` gives zero, so the derivation kills the relation
ideal and descends to `B'`; it obeys the divided power chain rule for `γ'` because the
presentation is a divided power morphism, so it factors through `Ω¹_{B'/A,γ'}`.

That the two maps are mutually inverse is checked on generators.  One composite is the identity
because the right-hand side is generated over `B'` by the forms `1 ⊗ db` and by `dz`.  For the
other, the set of `f ∈ B'` on which the round trip agrees with `d f` is a `B`-submodule closed
under multiplication, contains the image of `B` and `z`, hence `ξ = z^p - λ`, hence every `ξ^[n]`
by the divided power chain rule, hence every `ξ^[n] z^i`; and those are the free `B`-basis of
`B'`.

## Main definitions

* `Crystalline.PthRootExtension.primeFormsComparison` — the comparison `ψ` of one-forms along
  `B → B'`, semilinear over `B → B'`.
* `Crystalline.PthRootExtension.primeFormsTarget` — the right-hand side
  `(B' ⊗_B Ω¹_{B/A,γ}) ⊕ B'` of the decomposition.
* `Crystalline.PthRootExtension.primeFormsBackward` and
  `Crystalline.PthRootExtension.primeFormsForward` — the two maps of the decomposition.
* `Crystalline.PthRootExtension.primeExtensionDerivation` — the divided power differential of
  `B'` read through the decomposition, as an `A`-derivation of `B'`.
* `Crystalline.PthRootExtension.primeFormsEquiv` — the decomposition itself.
* `Crystalline.PthRootExtension.primeFormsAgreement` — the elements of `B'` on which the round
  trip agrees with the universal differential.
* `Crystalline.PthRootExtension.baseFormsProjection` and
  `Crystalline.PthRootExtension.primeFormsProjection` — the two projections of Tag 07HZ onto the
  divided power one-forms.

## Main results

* `Crystalline.PthRootExtension.isDPMorphism_algebraMap_primeDividedPowers` — the structure map
  `B → B'` is a divided power morphism `γ → γ'`.
* `Crystalline.PthRootExtension.primeFormsComparison_dividedPowerDifferential` — the comparison
  of one-forms is compatible with the two universal differentials.
* `Crystalline.PthRootExtension.primePolyDerivation_primePoly` — the derivation of `B⟨ξ⟩[z]`
  attached to the decomposition annihilates the relation `z^p - ξ - λ`.
* `Crystalline.PthRootExtension.primeExtensionDerivation_dpow` — the descended derivation obeys
  the divided power chain rule for `γ'`.
* `Crystalline.PthRootExtension.pthRootDzDecomposition` — **assumption (07Q1) for the extension
  of Tag 07N1**, the decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz`.
* `Crystalline.exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials` — the
  conclusion of Tag 07N1 for the uncompleted extension and the modules of divided power
  differentials, with no hypotheses about those modules; the completed statement of the tag is
  `Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension`.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Section 60.25, Tag 07Q1](https://stacks.math.columbia.edu/tag/07Q1)
* [Stacks Project, Lemma 60.25.2, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Lemma 60.6.6, Tag 07HS](https://stacks.math.columbia.edu/tag/07HS)
* [Stacks Project, Lemma 60.6.9, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
-/

@[expose] public section

noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u w

namespace Crystalline.PthRootExtension

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)]
  (p : ℕ) (lam : (B : Type u))

/-- **The structure map of the extension is a divided power morphism.**  The map
`B → B' = B⟨ξ⟩[z]/(z^p - ξ - λ)` is the composite of the coefficient map `B → B⟨ξ⟩`, the
polynomial inclusion `B⟨ξ⟩ → B⟨ξ⟩[z]` and the presentation `B⟨ξ⟩[z] → B'`, each of which is a
divided power morphism. -/
public theorem isDPMorphism_algebraMap_primeDividedPowers (hp : p ≠ 0) :
    DividedPowers.IsDPMorphism B.dividedPowers (primeDividedPowers B p lam hp)
      (algebraMap (B : Type u) (primeRing B p lam)) := by
  have hcomp := DividedPowers.IsDPMorphism.comp (primeDividedPowers B p lam hp)
    (isDPMorphism_relationQuotientMk B p lam hp)
    (DividedPowers.IsDPMorphism.comp (zPolyDPRing B).dividedPowers
      (isDPMorphism_C_polynomialDividedPowerRing (xiDPRing B))
      (setIndexedDividedPowerPolynomialCoefficient_isDPMorphism B Unit))
  have h : (relationQuotientMk B p lam).comp
      ((Polynomial.C : XiAlg B →+* Polynomial (XiAlg B)).comp
        (algebraMap (B : Type u) (XiAlg B))) =
      algebraMap (B : Type u) (primeRing B p lam) := rfl
  rwa [h] at hcomp

/-- The divided power differential of `B'` over `A`, as an `A`-derivation of `B'`. -/
public def primeDerivation (hp : p ≠ 0) :
    Derivation A (primeRing B p lam)
      (dividedPowerDifferentials (A := A) (primeDividedPowers B p lam hp)) :=
  Derivation.llcomp
    (dividedPowerDifferentialRelations (A := A) (primeDividedPowers B p lam hp)).mkQ
    (KaehlerDifferential.D A (primeRing B p lam))

/-- The derivation is the universal divided power differential of `B'`. -/
public theorem primeDerivation_apply (hp : p ≠ 0) (x : primeRing B p lam) :
    primeDerivation A B p lam hp x =
      dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp) x := rfl

/-- The divided power differential of `B'` restricted along `B → B'`, as an `A`-derivation
of `B`. -/
public def primeBaseDerivation (hp : p ≠ 0) :
    Derivation A (B : Type u)
      (dividedPowerDifferentials (A := A) (primeDividedPowers B p lam hp)) :=
  Derivation.compAlgebraMap (B : Type u) (primeDerivation A B p lam hp)

/-- The restricted derivation is `b ↦ d(algebraMap b)`. -/
public theorem primeBaseDerivation_apply (hp : p ≠ 0) (b : (B : Type u)) :
    primeBaseDerivation A B p lam hp b =
      dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp)
        (algebraMap (B : Type u) (primeRing B p lam) b) := rfl

/-- The comparison of one-forms, as a `B`-linear map into the divided power differentials of the
extension read as a `B`-module. -/
public def primeFormsComparisonLinear (hp : p ≠ 0) :
    dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) (primeDividedPowers B p lam hp) :=
  (dividedPowerDifferentialRelations (A := A) B.dividedPowers).liftQ
    (primeBaseDerivation A B p lam hp).liftKaehlerDifferential (by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨x, n⟩, rfl⟩
      have hx : (x : (B : Type u)) ∈ B.ideal := x.2
      have hmem : algebraMap (B : Type u) (primeRing B p lam) (x : (B : Type u)) ∈
          primeIdeal B p lam :=
        (isDPMorphism_algebraMap_primeDividedPowers B p lam hp).ideal_comp
          (Ideal.mem_map_of_mem _ hx)
      have hdp : ∀ k : ℕ, algebraMap (B : Type u) (primeRing B p lam)
            (B.dividedPowers.dpow k (x : (B : Type u))) =
          (primeDividedPowers B p lam hp).dpow k
            (algebraMap (B : Type u) (primeRing B p lam) (x : (B : Type u))) := fun k =>
        (isDPMorphism_algebraMap_primeDividedPowers B p lam hp).map_dpow hx
      change (primeBaseDerivation A B p lam hp).liftKaehlerDifferential
          (KaehlerDifferential.D A (B : Type u)
            (B.dividedPowers.dpow (n + 1) (x : (B : Type u))) -
            B.dividedPowers.dpow n (x : (B : Type u)) •
              KaehlerDifferential.D A (B : Type u) (x : (B : Type u))) = 0
      rw [map_sub, map_smul, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D, primeBaseDerivation_apply,
        primeBaseDerivation_apply, hdp (n + 1),
        dividedPowerDifferential_dpow (A := A) (hJ := primeDividedPowers B p lam hp)
          ⟨_, hmem⟩ n, ← hdp n, IsScalarTower.algebraMap_smul, sub_self])

/-- The comparison of one-forms sends the universal differential of `b` to the universal
differential of the image of `b`. -/
public theorem primeFormsComparisonLinear_dividedPowerDifferential (hp : p ≠ 0)
    (b : (B : Type u)) :
    primeFormsComparisonLinear A B p lam hp
        (dividedPowerDifferential (A := A) B.dividedPowers b) =
      dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp)
        (algebraMap (B : Type u) (primeRing B p lam) b) := by
  change (primeBaseDerivation A B p lam hp).liftKaehlerDifferential
    (KaehlerDifferential.D A (B : Type u) b) = _
  rw [Derivation.liftKaehlerDifferential_comp_D, primeBaseDerivation_apply]

/-- **The comparison `ψ : Ω¹_{B/A,γ} → Ω¹_{B'/A,γ'}` of one-forms** along the structure map of
the extension `B → B' = B⟨ξ⟩[z]/(z^p - ξ - λ)`, semilinear over `B → B'`.  It is the map
induced by the divided power derivation `b ↦ d(algebraMap b)` of `B`, which is a divided power
derivation because `B → B'` is a divided power morphism. -/
public def primeFormsComparison (hp : p ≠ 0) :
    dividedPowerDifferentials (A := A) B.dividedPowers
      →ₛₗ[algebraMap (B : Type u) (primeRing B p lam)]
        dividedPowerDifferentials (A := A) (primeDividedPowers B p lam hp) where
  toFun := primeFormsComparisonLinear A B p lam hp
  map_add' := (primeFormsComparisonLinear A B p lam hp).map_add
  map_smul' b om := by
    rw [(primeFormsComparisonLinear A B p lam hp).map_smul, IsScalarTower.algebraMap_smul]

/-- The comparison of one-forms is compatible with the two universal differentials. -/
public theorem primeFormsComparison_dividedPowerDifferential (hp : p ≠ 0) (b : (B : Type u)) :
    primeFormsComparison A B p lam hp
        (dividedPowerDifferential (A := A) B.dividedPowers b) =
      dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp)
        (algebraMap (B : Type u) (primeRing B p lam) b) :=
  primeFormsComparisonLinear_dividedPowerDifferential A B p lam hp b


section Decomposition

/-- `B⟨ξ⟩[z]` acts on the extension through the presentation `B⟨ξ⟩[z] → B'`. -/
local instance instAlgebraPolynomialPrimeRing :
    Algebra (Polynomial (XiAlg B)) (primeRing B p lam) :=
  inferInstanceAs (Algebra (Polynomial (XiAlg B))
    (Polynomial (XiAlg B) ⧸ relationIdeal B p lam))

/-- The action of `B⟨ξ⟩[z]` on the extension extends the action of `B⟨ξ⟩`. -/
local instance instTowerXiPolynomialPrimeRing :
    IsScalarTower (XiAlg B) (Polynomial (XiAlg B)) (primeRing B p lam) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The action of `B⟨ξ⟩[z]` on the extension extends the action of the base ring. -/
local instance instTowerBasePolynomialPrimeRing :
    IsScalarTower A (Polynomial (XiAlg B)) (primeRing B p lam) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The right-hand side `(B' ⊗_B Ω¹_{B/A,γ}) ⊕ B'` of the decomposition (07Q1) of the one-forms
of the extension. -/
public abbrev primeFormsTarget : Type u :=
  (primeRing B p lam ⊗[(B : Type u)] dividedPowerDifferentials (A := A) B.dividedPowers) ×
    primeRing B p lam

variable (hp : p ≠ 0)

/-- **The map `(B' ⊗_B Ω¹_{B/A,γ}) ⊕ B' → Ω¹_{B'/A,γ'}` of the decomposition (07Q1)**: the
comparison `ψ` on the base change summand and multiplication by `dz` on the free summand. -/
public def primeFormsBackward :
    primeFormsTarget A B p lam →ₗ[primeRing B p lam]
      dividedPowerDifferentials (A := A) (primeDividedPowers B p lam hp) :=
  LinearMap.coprod
    (TensorProduct.AlgebraTensorModule.lift
      (LinearMap.smulRight
        (LinearMap.id : primeRing B p lam →ₗ[primeRing B p lam] primeRing B p lam)
        (primeFormsComparisonLinear A B p lam hp)))
    (LinearMap.smulRight
      (LinearMap.id : primeRing B p lam →ₗ[primeRing B p lam] primeRing B p lam)
      (dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp) (zElt B p lam)))

/-- On the base change summand the map of the decomposition is `b' ⊗ ω ↦ b' ψ(ω)`. -/
public theorem primeFormsBackward_tmul (b' : primeRing B p lam)
    (om : dividedPowerDifferentials (A := A) B.dividedPowers) :
    primeFormsBackward A B p lam hp (b' ⊗ₜ[(B : Type u)] om, 0) =
      b' • primeFormsComparisonLinear A B p lam hp om := by
  simp [primeFormsBackward]

/-- On the free summand the map of the decomposition is `c ↦ c dz`. -/
public theorem primeFormsBackward_free (b' : primeRing B p lam) :
    primeFormsBackward A B p lam hp (0, b') =
      b' • dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp)
        (zElt B p lam) := by
  simp [primeFormsBackward]

/-- The inclusion `ω ↦ (1 ⊗ ω, 0)` of the one-forms of `B` into the right-hand side of the
decomposition. -/
public def primeFormsUnitInclusion :
    dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      primeFormsTarget A B p lam :=
  (LinearMap.inl (B : Type u) _ _).comp
    (TensorProduct.mk (B : Type u) (primeRing B p lam)
      (dividedPowerDifferentials (A := A) B.dividedPowers) 1)

/-- The inclusion of one-forms has the expected value. -/
public theorem primeFormsUnitInclusion_apply
    (om : dividedPowerDifferentials (A := A) B.dividedPowers) :
    primeFormsUnitInclusion A B p lam om =
      ((1 : primeRing B p lam) ⊗ₜ[(B : Type u)] om, 0) := rfl

/-- **`dξ` read through the decomposition.**  The relation `ξ = z^p - λ` gives
`dξ = p z^{p-1} dz - dλ`, so the coordinates of `dξ` are `-(1 ⊗ dλ)` and `p z^{p-1}`. -/
public def primeFormsDXi : primeFormsTarget A B p lam :=
  (-((1 : primeRing B p lam) ⊗ₜ[(B : Type u)]
      dividedPowerDifferential (A := A) B.dividedPowers lam),
    ((p : ℕ) : primeRing B p lam) * zElt B p lam ^ (p - 1))


/-- **The one-forms of `B⟨ξ⟩` read through the decomposition (07Q1).**  The divided power
polynomial decomposition of `Ω¹_{B⟨ξ⟩/A,δ}` sends the base change summand to the base change
summand and `dξ` to its coordinates `(-(1 ⊗ dλ), p z^{p-1})`. -/
public def primeFormsXiMap :
    dividedPowerDifferentials (A := A) (xiDPRing B).dividedPowers →ₗ[XiAlg B]
      primeFormsTarget A B p lam :=
  (LinearMap.coprod
      (TensorProduct.AlgebraTensorModule.lift
        (LinearMap.smulRight (LinearMap.id : XiAlg B →ₗ[XiAlg B] XiAlg B)
          (primeFormsUnitInclusion A B p lam)))
      (LinearMap.smulRight (LinearMap.id : XiAlg B →ₗ[XiAlg B] XiAlg B)
        (primeFormsDXi A B p lam))).comp
    (oneVariableDifferentialsEquiv A B).toLinearMap

/-- The differential of a coefficient is carried to the base change summand. -/
public theorem primeFormsXiMap_coefficient (b : (B : Type u)) :
    primeFormsXiMap A B p lam
        (dividedPowerDifferential (A := A) (xiDPRing B).dividedPowers
          (algebraMap (B : Type u) (XiAlg B) b)) =
      ((1 : primeRing B p lam) ⊗ₜ[(B : Type u)]
        dividedPowerDifferential (A := A) B.dividedPowers b, 0) := by
  change (LinearMap.coprod _ _) (oneVariableDifferentialsEquiv A B
    (dividedPowerDifferential (A := A) (oneVariableDividedPowers B)
      (algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B) b))) = _
  rw [oneVariableDifferentialsEquiv_coefficient A B b]
  simp [primeFormsUnitInclusion_apply]

/-- The differential of `ξ` is carried to the coordinates of `dξ`. -/
public theorem primeFormsXiMap_xi :
    primeFormsXiMap A B p lam
        (dividedPowerDifferential (A := A) (xiDPRing B).dividedPowers (xi B)) =
      primeFormsDXi A B p lam := by
  change (LinearMap.coprod _ _) (oneVariableDifferentialsEquiv A B
    (dividedPowerDifferential (A := A) (oneVariableDividedPowers B)
      (oneVariableVariable B))) = _
  rw [oneVariableDifferentialsEquiv_variable A B]
  simp

/-- The polynomial decomposition (07HS) of the one-forms of `B⟨ξ⟩[z]` over `B⟨ξ⟩`. -/
public abbrev primePolyFormsData :=
  dividedPowerDifferentialsPolynomialEquiv (A := A) (xiDPRing B)
    (zPolyDPRing B).dividedPowers (isDPMorphism_C_polynomialDividedPowerRing (xiDPRing B))

/-- **The one-forms of `B⟨ξ⟩[z]` read through the decomposition (07Q1).**  The polynomial
decomposition of `Ω¹_{B⟨ξ⟩[z]/A,δ'}` sends the base change summand through
`Crystalline.PthRootExtension.primeFormsXiMap` and `dz` to the generator of the free summand. -/
public def primeFormsPolyMap :
    dividedPowerDifferentials (A := A) (zPolyDPRing B).dividedPowers
      →ₗ[Polynomial (XiAlg B)] primeFormsTarget A B p lam :=
  (LinearMap.coprod
      (TensorProduct.AlgebraTensorModule.lift
        (LinearMap.smulRight
          (LinearMap.id : Polynomial (XiAlg B) →ₗ[Polynomial (XiAlg B)] Polynomial (XiAlg B))
          (primeFormsXiMap A B p lam)))
      (LinearMap.smulRight
        (LinearMap.id : Polynomial (XiAlg B) →ₗ[Polynomial (XiAlg B)] Polynomial (XiAlg B))
        ((0, 1) : primeFormsTarget A B p lam))).comp
    (primePolyFormsData A B).1.toLinearMap

/-- The differential of a constant polynomial is read through `primeFormsXiMap`. -/
public theorem primeFormsPolyMap_C (b : XiAlg B) :
    primeFormsPolyMap A B p lam
        (dividedPowerDifferential (A := A) (zPolyDPRing B).dividedPowers (Polynomial.C b)) =
      primeFormsXiMap A B p lam
        (dividedPowerDifferential (A := A) (xiDPRing B).dividedPowers b) := by
  change (LinearMap.coprod _ _) ((primePolyFormsData A B).1 _) = _
  rw [(primePolyFormsData A B).2.1 b]
  simp

/-- The differential of `z` is the generator of the free summand. -/
public theorem primeFormsPolyMap_X :
    primeFormsPolyMap A B p lam
        (dividedPowerDifferential (A := A) (zPolyDPRing B).dividedPowers Polynomial.X) =
      (0, 1) := by
  change (LinearMap.coprod _ _) ((primePolyFormsData A B).1 _) = _
  rw [(primePolyFormsData A B).2.2]
  simp


/-- The divided power differential of `B⟨ξ⟩[z]` read through the decomposition (07Q1), as an
`A`-derivation of `B⟨ξ⟩[z]` with values in `(B' ⊗_B Ω¹_{B/A,γ}) ⊕ B'`. -/
public def primePolyDerivation :
    Derivation A (Polynomial (XiAlg B)) (primeFormsTarget A B p lam) :=
  Derivation.llcomp
    ((primeFormsPolyMap A B p lam).comp
      (dividedPowerDifferentialRelations (A := A) (zPolyDPRing B).dividedPowers).mkQ)
    (KaehlerDifferential.D A (Polynomial (XiAlg B)))

/-- The derivation is the universal divided power differential read through the decomposition. -/
public theorem primePolyDerivation_apply (x : Polynomial (XiAlg B)) :
    primePolyDerivation A B p lam x =
      primeFormsPolyMap A B p lam
        (dividedPowerDifferential (A := A) (zPolyDPRing B).dividedPowers x) := rfl

/-- The derivation sends the differential of a coefficient of `B` to `(1 ⊗ db, 0)`. -/
public theorem primePolyDerivation_C_coefficient (b : (B : Type u)) :
    primePolyDerivation A B p lam
        (Polynomial.C (algebraMap (B : Type u) (XiAlg B) b)) =
      ((1 : primeRing B p lam) ⊗ₜ[(B : Type u)]
        dividedPowerDifferential (A := A) B.dividedPowers b, 0) := by
  rw [primePolyDerivation_apply, primeFormsPolyMap_C, primeFormsXiMap_coefficient]

/-- The derivation sends `ξ` to the coordinates of `dξ`. -/
public theorem primePolyDerivation_C_xi :
    primePolyDerivation A B p lam (Polynomial.C (xi B)) = primeFormsDXi A B p lam := by
  rw [primePolyDerivation_apply, primeFormsPolyMap_C, primeFormsXiMap_xi]

/-- The derivation sends `z` to the generator of the free summand. -/
public theorem primePolyDerivation_X :
    primePolyDerivation A B p lam Polynomial.X = (0, 1) := by
  rw [primePolyDerivation_apply, primeFormsPolyMap_X]

/-- The derivation sends `z^p` to `p z^{p-1} dz`. -/
public theorem primePolyDerivation_X_pow :
    primePolyDerivation A B p lam (Polynomial.X ^ p) =
      (0, ((p : ℕ) : primeRing B p lam) * zElt B p lam ^ (p - 1)) := by
  have h1 : (Polynomial.X ^ (p - 1) : Polynomial (XiAlg B)) •
      ((0, 1) : primeFormsTarget A B p lam) = (0, zElt B p lam ^ (p - 1)) := by
    refine Prod.ext (smul_zero _) ?_
    change (Polynomial.X ^ (p - 1) : Polynomial (XiAlg B)) • (1 : primeRing B p lam) =
      zElt B p lam ^ (p - 1)
    rw [Algebra.smul_def, mul_one, map_pow]
    rfl
  rw [Derivation.leibniz_pow, primePolyDerivation_X, h1]
  refine Prod.ext (smul_zero _) ?_
  change (p : ℕ) • zElt B p lam ^ (p - 1) = _
  rw [nsmul_eq_mul]

/-- **The derivation annihilates the relation `z^p - ξ - λ`.**  The three contributions
`p z^{p-1} dz`, `dξ = p z^{p-1} dz - dλ` and `dλ` cancel, which is exactly the relation
`ξ = z^p - λ` differentiated. -/
public theorem primePolyDerivation_primePoly :
    primePolyDerivation A B p lam (primePoly B p lam) = 0 := by
  change primePolyDerivation A B p lam (Polynomial.X ^ p - Polynomial.C (xi B) -
    Polynomial.C (algebraMap (B : Type u) (XiAlg B) lam)) = 0
  rw [map_sub, map_sub, primePolyDerivation_X_pow, primePolyDerivation_C_xi,
    primePolyDerivation_C_coefficient, primeFormsDXi]
  refine Prod.ext ?_ ?_
  · change (0 : primeRing B p lam ⊗[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers) -
        (-((1 : primeRing B p lam) ⊗ₜ[(B : Type u)]
          dividedPowerDifferential (A := A) B.dividedPowers lam)) -
        ((1 : primeRing B p lam) ⊗ₜ[(B : Type u)]
          dividedPowerDifferential (A := A) B.dividedPowers lam) = 0
    abel
  · change ((p : ℕ) : primeRing B p lam) * zElt B p lam ^ (p - 1) -
        ((p : ℕ) : primeRing B p lam) * zElt B p lam ^ (p - 1) - 0 = 0
    ring

/-- The presentation sends the relation to zero. -/
public theorem relationQuotientMk_primePoly :
    relationQuotientMk B p lam (primePoly B p lam) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- **The derivation annihilates the relation ideal**, hence descends to the extension: a
multiple `h (z^p - ξ - λ)` has differential `h d(z^p - ξ - λ) + (z^p - ξ - λ) dh`, and both
terms vanish, the first because the relation is annihilated and the second because the relation
acts as zero on `(B' ⊗_B Ω¹_{B/A,γ}) ⊕ B'`. -/
public theorem primePolyDerivation_eq_zero_of_mem (k : Polynomial (XiAlg B))
    (hk : k ∈ relationIdeal B p lam) : primePolyDerivation A B p lam k = 0 := by
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hk
  rw [Derivation.leibniz, primePolyDerivation_primePoly, smul_zero, zero_add,
    ← IsScalarTower.algebraMap_smul (primeRing B p lam) (primePoly B p lam),
    show algebraMap (Polynomial (XiAlg B)) (primeRing B p lam) (primePoly B p lam) = 0 from
      relationQuotientMk_primePoly B p lam, zero_smul]


/-- The scalar action of `B⟨ξ⟩[z]` on the right-hand side of the decomposition factors through
the presentation. -/
public theorem relationQuotientMk_smul_formsTarget (c : Polynomial (XiAlg B))
    (t : primeFormsTarget A B p lam) : relationQuotientMk B p lam c • t = c • t :=
  IsScalarTower.algebraMap_smul (primeRing B p lam) c t

/-- The presentation of the extension is surjective. -/
public theorem relationQuotientMk_surjective :
    Function.Surjective (relationQuotientMk B p lam) :=
  Ideal.Quotient.mk_surjective

/-- The additive descent to the extension of the derivation of `B⟨ξ⟩[z]`, which exists because
that derivation annihilates the relation ideal. -/
public def primeExtensionDerivationAddHom :
    primeRing B p lam →+ primeFormsTarget A B p lam :=
  QuotientAddGroup.lift (relationIdeal B p lam).toAddSubgroup
    (primePolyDerivation A B p lam).toAddMonoidHom fun k hk =>
      AddMonoidHom.mem_ker.mpr (primePolyDerivation_eq_zero_of_mem A B p lam k hk)

/-- The additive descent agrees with the derivation of `B⟨ξ⟩[z]` on classes. -/
public theorem primeExtensionDerivationAddHom_mk (x : Polynomial (XiAlg B)) :
    primeExtensionDerivationAddHom A B p lam (relationQuotientMk B p lam x) =
      primePolyDerivation A B p lam x := rfl

/-- The additive descent obeys the Leibniz rule, the Leibniz rule of the derivation of
`B⟨ξ⟩[z]` passing to classes. -/
public theorem primeExtensionDerivationAddHom_leibniz (y y' : primeRing B p lam) :
    primeExtensionDerivationAddHom A B p lam (y * y') =
      y • primeExtensionDerivationAddHom A B p lam y' +
        y' • primeExtensionDerivationAddHom A B p lam y := by
  obtain ⟨x, rfl⟩ := relationQuotientMk_surjective B p lam y
  obtain ⟨x', rfl⟩ := relationQuotientMk_surjective B p lam y'
  rw [← map_mul, primeExtensionDerivationAddHom_mk, primeExtensionDerivationAddHom_mk,
    primeExtensionDerivationAddHom_mk, Derivation.leibniz,
    relationQuotientMk_smul_formsTarget, relationQuotientMk_smul_formsTarget]

/-- The additive descent annihilates the image of the base ring. -/
public theorem primeExtensionDerivationAddHom_algebraMap (a : A) :
    primeExtensionDerivationAddHom A B p lam (algebraMap A (primeRing B p lam) a) = 0 := by
  rw [IsScalarTower.algebraMap_apply A (Polynomial (XiAlg B)) (primeRing B p lam) a,
    show algebraMap (Polynomial (XiAlg B)) (primeRing B p lam) = relationQuotientMk B p lam from
      rfl, primeExtensionDerivationAddHom_mk, Derivation.map_algebraMap]

/-- **The divided power differential of `B'` read through the decomposition (07Q1)**, as an
`A`-derivation of `B'`: the derivation of `B⟨ξ⟩[z]` descends because it annihilates the relation
ideal. -/
public def primeExtensionDerivation :
    Derivation A (primeRing B p lam) (primeFormsTarget A B p lam) where
  toLinearMap :=
    { toFun := primeExtensionDerivationAddHom A B p lam
      map_add' := map_add _
      map_smul' := fun a y => by
        rw [RingHom.id_apply]
        change primeExtensionDerivationAddHom A B p lam (a • y) = _
        rw [Algebra.smul_def, primeExtensionDerivationAddHom_leibniz,
          primeExtensionDerivationAddHom_algebraMap, smul_zero, add_zero,
          IsScalarTower.algebraMap_smul] }
  map_one_eq_zero' := by
    change primeExtensionDerivationAddHom A B p lam 1 = 0
    rw [show (1 : primeRing B p lam) = relationQuotientMk B p lam 1 from (map_one _).symm,
      primeExtensionDerivationAddHom_mk, Derivation.map_one_eq_zero]
  leibniz' := primeExtensionDerivationAddHom_leibniz A B p lam

/-- The descended derivation agrees with the derivation of `B⟨ξ⟩[z]` on classes. -/
public theorem primeExtensionDerivation_mk (x : Polynomial (XiAlg B)) :
    primeExtensionDerivation A B p lam (relationQuotientMk B p lam x) =
      primePolyDerivation A B p lam x := rfl

/-- **The descended derivation obeys the divided power chain rule for `γ'`** on a class.  This is
the chain rule for `δ'` on `B⟨ξ⟩[z]` transported along the presentation, which is a divided power
morphism. -/
public theorem primeExtensionDerivation_dpow_mk (n : ℕ) (x : Polynomial (XiAlg B))
    (hx : x ∈ (zPolyDPRing B).ideal) :
    primeExtensionDerivation A B p lam
        ((primeDividedPowers B p lam hp).dpow (n + 1) (relationQuotientMk B p lam x)) =
      (primeDividedPowers B p lam hp).dpow n (relationQuotientMk B p lam x) •
        primeExtensionDerivation A B p lam (relationQuotientMk B p lam x) := by
  rw [(isDPMorphism_relationQuotientMk B p lam hp).dpow_comp (n := n + 1) x hx,
    (isDPMorphism_relationQuotientMk B p lam hp).dpow_comp (n := n) x hx,
    primeExtensionDerivation_mk, primeExtensionDerivation_mk, primePolyDerivation_apply,
    primePolyDerivation_apply,
    dividedPowerDifferential_dpow (A := A) (hJ := (zPolyDPRing B).dividedPowers) ⟨x, hx⟩ n,
    map_smul, relationQuotientMk_smul_formsTarget]

/-- **The descended derivation obeys the divided power chain rule for `γ'`.**  This is what makes
it factor through the divided power differentials of `B'`. -/
public theorem primeExtensionDerivation_dpow (n : ℕ) (y : primeRing B p lam)
    (hy : y ∈ primeIdeal B p lam) :
    primeExtensionDerivation A B p lam ((primeDividedPowers B p lam hp).dpow (n + 1) y) =
      (primeDividedPowers B p lam hp).dpow n y • primeExtensionDerivation A B p lam y := by
  obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective (relationQuotientMk B p lam)
    Ideal.Quotient.mk_surjective).mp hy
  exact primeExtensionDerivation_dpow_mk A B p lam hp n x hx

/-- **The map `Ω¹_{B'/A,γ'} → (B' ⊗_B Ω¹_{B/A,γ}) ⊕ B'` of the decomposition (07Q1)**, the
inverse of `Crystalline.PthRootExtension.primeFormsBackward`. -/
public def primeFormsForward :
    dividedPowerDifferentials (A := A) (primeDividedPowers B p lam hp) →ₗ[primeRing B p lam]
      primeFormsTarget A B p lam :=
  (dividedPowerDifferentialRelations (A := A) (primeDividedPowers B p lam hp)).liftQ
    (primeExtensionDerivation A B p lam).liftKaehlerDifferential (by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨y, n⟩, rfl⟩
      change (primeExtensionDerivation A B p lam).liftKaehlerDifferential
          (KaehlerDifferential.D A (primeRing B p lam)
            ((primeDividedPowers B p lam hp).dpow (n + 1) (y : primeRing B p lam)) -
            (primeDividedPowers B p lam hp).dpow n (y : primeRing B p lam) •
              KaehlerDifferential.D A (primeRing B p lam) (y : primeRing B p lam)) = 0
      rw [map_sub, map_smul, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D,
        primeExtensionDerivation_dpow A B p lam hp n (y : primeRing B p lam) y.2, sub_self])

/-- The forward map sends the universal differential to the descended derivation. -/
public theorem primeFormsForward_dividedPowerDifferential (x : primeRing B p lam) :
    primeFormsForward A B p lam hp
        (dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp) x) =
      primeExtensionDerivation A B p lam x := by
  change (primeExtensionDerivation A B p lam).liftKaehlerDifferential
    (KaehlerDifferential.D A (primeRing B p lam) x) = _
  exact Derivation.liftKaehlerDifferential_comp_D _ x


/-- The descended derivation on the image of `B` is the base change of the differential of `B`:
the coordinates of `d(algebraMap b)` are `1 ⊗ db` and `0`. -/
public theorem primeExtensionDerivation_algebraMap (b : (B : Type u)) :
    primeExtensionDerivation A B p lam (algebraMap (B : Type u) (primeRing B p lam) b) =
      ((1 : primeRing B p lam) ⊗ₜ[(B : Type u)]
        dividedPowerDifferential (A := A) B.dividedPowers b, 0) := by
  rw [show algebraMap (B : Type u) (primeRing B p lam) b =
      relationQuotientMk B p lam (Polynomial.C (algebraMap (B : Type u) (XiAlg B) b)) from rfl,
    primeExtensionDerivation_mk, primePolyDerivation_C_coefficient]

/-- The descended derivation sends `z` to the generator of the free summand. -/
public theorem primeExtensionDerivation_zElt :
    primeExtensionDerivation A B p lam (zElt B p lam) = (0, 1) := by
  rw [show zElt B p lam = relationQuotientMk B p lam Polynomial.X from rfl,
    primeExtensionDerivation_mk, primePolyDerivation_X]

/-- A scalar multiple of the generator of the free summand. -/
public theorem primeFormsTarget_smul_free (c : primeRing B p lam) :
    c • ((0, 1) : primeFormsTarget A B p lam) = (0, c) := by
  refine Prod.ext (smul_zero _) ?_
  change c • (1 : primeRing B p lam) = c
  rw [smul_eq_mul, mul_one]

/-- **The decomposition maps compose to the identity on `(B' ⊗_B Ω¹_{B/A,γ}) ⊕ B'`.**  The right
hand side is generated over `B'` by the forms `1 ⊗ db` and by `dz`, and on those the composite is
the identity because `ψ(db) = d(algebraMap b)` and the descended derivation has the stated
values. -/
public theorem primeFormsForward_comp_primeFormsBackward :
    (primeFormsForward A B p lam hp).comp (primeFormsBackward A B p lam hp) = LinearMap.id := by
  have hpsi : ((primeFormsForward A B p lam hp).restrictScalars (B : Type u)).comp
      (primeFormsComparisonLinear A B p lam hp) = primeFormsUnitInclusion A B p lam :=
    LinearMap.ext_on_range (dividedPowerDifferentials_span (A := A) B.dividedPowers) fun b => by
      change primeFormsForward A B p lam hp (primeFormsComparisonLinear A B p lam hp
        (dividedPowerDifferential (A := A) B.dividedPowers b)) = _
      rw [primeFormsComparisonLinear_dividedPowerDifferential,
        primeFormsForward_dividedPowerDifferential, primeExtensionDerivation_algebraMap,
        primeFormsUnitInclusion_apply]
  have hpsi' : ∀ om : dividedPowerDifferentials (A := A) B.dividedPowers,
      primeFormsForward A B p lam hp (primeFormsComparisonLinear A B p lam hp om) =
        ((1 : primeRing B p lam) ⊗ₜ[(B : Type u)] om, 0) := fun om => by
    have h := LinearMap.congr_fun hpsi om
    rwa [primeFormsUnitInclusion_apply] at h
  have hinl : ∀ t : primeRing B p lam ⊗[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers,
      primeFormsForward A B p lam hp (primeFormsBackward A B p lam hp (t, 0)) = (t, 0) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul b' om =>
      rw [show ((b' ⊗ₜ[(B : Type u)] om), (0 : primeRing B p lam)) =
          b' • (((1 : primeRing B p lam) ⊗ₜ[(B : Type u)] om), (0 : primeRing B p lam)) from
        Prod.ext (by
            change b' ⊗ₜ[(B : Type u)] om = b' • ((1 : primeRing B p lam) ⊗ₜ[(B : Type u)] om)
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
          (smul_zero _).symm, map_smul, map_smul, primeFormsBackward_tmul, map_smul, hpsi',
        one_smul]
    | add x y hx hy =>
      rw [show ((x + y), (0 : primeRing B p lam)) =
          (x, (0 : primeRing B p lam)) + (y, (0 : primeRing B p lam)) from
        Prod.ext rfl (add_zero 0).symm, map_add, map_add, hx, hy]
  refine LinearMap.ext fun t => ?_
  obtain ⟨t1, t2⟩ := t
  rw [LinearMap.comp_apply, LinearMap.id_apply,
    show ((t1, t2) : primeFormsTarget A B p lam) =
        (t1, (0 : primeRing B p lam)) + ((0 : primeRing B p lam ⊗[(B : Type u)]
          dividedPowerDifferentials (A := A) B.dividedPowers), t2) from
      Prod.ext (add_zero t1).symm (zero_add t2).symm,
    map_add, map_add, hinl, primeFormsBackward_free, map_smul,
    primeFormsForward_dividedPowerDifferential, primeExtensionDerivation_zElt,
    primeFormsTarget_smul_free]

/-- The round trip `ω ↦ ψ(d(·))` of the decomposition, as an `A`-derivation of `B'` into its
divided power one-forms. -/
public def primeFormsRoundTrip :
    Derivation A (primeRing B p lam)
      (dividedPowerDifferentials (A := A) (primeDividedPowers B p lam hp)) :=
  Derivation.llcomp (primeFormsBackward A B p lam hp) (primeExtensionDerivation A B p lam)

/-- The round trip derivation is the composite of the descended derivation with the map of the
decomposition. -/
public theorem primeFormsRoundTrip_apply (f : primeRing B p lam) :
    primeFormsRoundTrip A B p lam hp f =
      primeFormsBackward A B p lam hp (primeExtensionDerivation A B p lam f) := rfl

/-- The round trip agrees with the universal differential on the image of `B`. -/
public theorem primeFormsRoundTrip_algebraMap (b : (B : Type u)) :
    primeFormsRoundTrip A B p lam hp (algebraMap (B : Type u) (primeRing B p lam) b) =
      primeDerivation A B p lam hp (algebraMap (B : Type u) (primeRing B p lam) b) := by
  rw [primeFormsRoundTrip_apply, primeExtensionDerivation_algebraMap, primeFormsBackward_tmul,
    one_smul, primeFormsComparisonLinear_dividedPowerDifferential, primeDerivation_apply]

/-- The elements of the extension on which the round trip agrees with the universal
differential.  It is a `B`-submodule because both maps are derivations which agree on the image
of `B`. -/
public def primeFormsAgreement : Submodule (B : Type u) (primeRing B p lam) where
  carrier := {f | primeFormsRoundTrip A B p lam hp f = primeDerivation A B p lam hp f}
  zero_mem' := show primeFormsRoundTrip A B p lam hp 0 = _ by rw [map_zero, map_zero]
  add_mem' := by
    intro f g hf hg
    have hf' : primeFormsRoundTrip A B p lam hp f = primeDerivation A B p lam hp f := hf
    have hg' : primeFormsRoundTrip A B p lam hp g = primeDerivation A B p lam hp g := hg
    change primeFormsRoundTrip A B p lam hp (f + g) = _
    rw [map_add, map_add, hf', hg']
  smul_mem' := by
    intro c f hf
    have hf' : primeFormsRoundTrip A B p lam hp f = primeDerivation A B p lam hp f := hf
    change primeFormsRoundTrip A B p lam hp (c • f) = _
    rw [Algebra.smul_def, Derivation.leibniz, Derivation.leibniz, hf',
      primeFormsRoundTrip_algebraMap]

/-- Membership in the agreement submodule is the agreement of the two derivations. -/
public theorem mem_primeFormsAgreement_iff (f : primeRing B p lam) :
    f ∈ primeFormsAgreement A B p lam hp ↔
      primeFormsRoundTrip A B p lam hp f = primeDerivation A B p lam hp f := Iff.rfl

/-- The agreement submodule is closed under multiplication, both maps obeying the Leibniz
rule. -/
public theorem mul_mem_primeFormsAgreement {f g : primeRing B p lam}
    (hf : f ∈ primeFormsAgreement A B p lam hp) (hg : g ∈ primeFormsAgreement A B p lam hp) :
    f * g ∈ primeFormsAgreement A B p lam hp := by
  rw [mem_primeFormsAgreement_iff] at hf hg ⊢
  rw [Derivation.leibniz, Derivation.leibniz, hf, hg]

/-- The image of `B` lies in the agreement submodule. -/
public theorem algebraMap_mem_primeFormsAgreement (b : (B : Type u)) :
    algebraMap (B : Type u) (primeRing B p lam) b ∈ primeFormsAgreement A B p lam hp :=
  primeFormsRoundTrip_algebraMap A B p lam hp b

/-- `1` lies in the agreement submodule, being the image of `1 ∈ B`. -/
private theorem one_mem_primeFormsAgreement :
    (1 : primeRing B p lam) ∈ primeFormsAgreement A B p lam hp :=
  map_one (algebraMap (B : Type u) (primeRing B p lam)) ▸
    algebraMap_mem_primeFormsAgreement A B p lam hp 1

/-- `z` lies in the agreement submodule, both maps sending it to `dz`. -/
public theorem zElt_mem_primeFormsAgreement :
    zElt B p lam ∈ primeFormsAgreement A B p lam hp := by
  rw [mem_primeFormsAgreement_iff, primeFormsRoundTrip_apply, primeExtensionDerivation_zElt,
    primeFormsBackward_free, one_smul, primeDerivation_apply]

/-- Every power of `z` lies in the agreement submodule. -/
public theorem zElt_pow_mem_primeFormsAgreement (i : ℕ) :
    zElt B p lam ^ i ∈ primeFormsAgreement A B p lam hp := by
  induction i with
  | zero =>
    rw [pow_zero]
    exact one_mem_primeFormsAgreement A B p lam hp
  | succ k ih =>
    rw [pow_succ]
    exact mul_mem_primeFormsAgreement A B p lam hp ih (zElt_mem_primeFormsAgreement A B p lam hp)

/-- `ξ` lies in the agreement submodule, being `z^p - λ`. -/
public theorem xiElt_one_zero_mem_primeFormsAgreement :
    xiElt B p lam 1 0 ∈ primeFormsAgreement A B p lam hp := by
  rw [xiElt_one_zero_eq]
  exact sub_mem (zElt_pow_mem_primeFormsAgreement A B p lam hp p)
    (algebraMap_mem_primeFormsAgreement A B p lam hp lam)

/-- **Every divided power monomial `ξ^[n]` lies in the agreement submodule.**  Both maps satisfy
`d(ξ^[n+1]) = ξ^[n] dξ`, the round trip because the descended derivation does and the map of the
decomposition is `B'`-linear, so the identity at `ξ` propagates to all of its divided
powers. -/
public theorem xiElt_zero_mem_primeFormsAgreement (n : ℕ) :
    xiElt B p lam n 0 ∈ primeFormsAgreement A B p lam hp := by
  cases n with
  | zero =>
    rw [xiElt_zero_zero]
    exact one_mem_primeFormsAgreement A B p lam hp
  | succ n =>
    have hmem := xiElt_one_zero_mem B p lam hp
    have hdpd := dividedPowerDifferential_dpow (A := A) (hJ := primeDividedPowers B p lam hp)
      ⟨xiElt B p lam 1 0, hmem⟩ n
    have hxi := xiElt_one_zero_mem_primeFormsAgreement A B p lam hp
    rw [mem_primeFormsAgreement_iff] at hxi ⊢
    rw [← primeDividedPowers_dpow_xiElt B p lam hp (n + 1), primeFormsRoundTrip_apply,
      primeExtensionDerivation_dpow A B p lam hp n (xiElt B p lam 1 0) hmem, map_smul,
      ← primeFormsRoundTrip_apply, hxi, primeDerivation_apply, primeDerivation_apply, hdpd]

/-- Every basis element `ξ^[n] z^i` lies in the agreement submodule. -/
public theorem xiElt_mem_primeFormsAgreement (n i : ℕ) :
    xiElt B p lam n i ∈ primeFormsAgreement A B p lam hp := by
  rw [xiElt_eq_mul n i]
  exact mul_mem_primeFormsAgreement A B p lam hp
    (xiElt_zero_mem_primeFormsAgreement A B p lam hp n)
    (zElt_pow_mem_primeFormsAgreement A B p lam hp i)

/-- **The agreement submodule is everything**, since the elements `ξ^[n] z^i` with `i < p` form a
`B`-basis of the extension. -/
public theorem primeFormsAgreement_eq_top [Nontrivial (XiAlg B)] :
    primeFormsAgreement A B p lam hp = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← (basisZXi B p lam hp).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨n, i⟩, rfl⟩
  rw [basisZXi_eq_xiElt]
  exact xiElt_mem_primeFormsAgreement A B p lam hp n (i : ℕ)

/-- **The decomposition maps compose to the identity on `Ω¹_{B'/A,γ'}`.**  The universal
differentials span the one-forms of `B'`, and the round trip agrees with the universal
differential everywhere. -/
public theorem primeFormsBackward_comp_primeFormsForward [Nontrivial (XiAlg B)] :
    (primeFormsBackward A B p lam hp).comp (primeFormsForward A B p lam hp) = LinearMap.id := by
  have key : ∀ f : primeRing B p lam,
      primeFormsBackward A B p lam hp (primeExtensionDerivation A B p lam f) =
        dividedPowerDifferential (A := A) (primeDividedPowers B p lam hp) f := by
    intro f
    have hf : f ∈ primeFormsAgreement A B p lam hp := by
      rw [primeFormsAgreement_eq_top]
      exact Submodule.mem_top
    rw [mem_primeFormsAgreement_iff, primeFormsRoundTrip_apply, primeDerivation_apply] at hf
    exact hf
  refine LinearMap.ext_on_range
    (dividedPowerDifferentials_span (A := A) (primeDividedPowers B p lam hp)) fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply, primeFormsForward_dividedPowerDifferential, key]


/-- **The decomposition (07Q1) for the extension of Tag 07N1**: the divided power one-forms of
`B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))` are the base change of those of `B` together with a free rank one
piece spanned by `dz`. -/
public def primeFormsEquiv [Nontrivial (XiAlg B)] :
    primeFormsTarget A B p lam ≃ₗ[primeRing B p lam]
      dividedPowerDifferentials (A := A) (primeDividedPowers B p lam hp) :=
  LinearEquiv.ofLinearMap (primeFormsBackward A B p lam hp) (primeFormsForward A B p lam hp)
    (primeFormsBackward_comp_primeFormsForward A B p lam hp)
    (primeFormsForward_comp_primeFormsBackward A B p lam hp)

/-- **Assumption (07Q1) of Section 60.25 for the extension of Tag 07N1.**  The one-forms of
`B'` decompose as `Ω' = (B' ⊗_B Ω) ⊕ B' dz`, with the base change summand the image of the
comparison `ψ` and the free summand generated by `dz`. -/
public def pthRootDzDecomposition [Nontrivial (XiAlg B)] :
    DzDecomposition
      (dividedPowerDifferentialRelations (A := A) (primeDividedPowers B p lam hp)).mkQ
      (primeFormsComparison A B p lam hp)
      (zElt B p lam) where
  equiv := primeFormsEquiv A B p lam hp
  equiv_tmul b' om := by
    change primeFormsBackward A B p lam hp (b' ⊗ₜ[(B : Type u)] om, 0) = _
    rw [primeFormsBackward_tmul]
    rfl
  equiv_dz b' := by
    change primeFormsBackward A B p lam hp (0, b') = _
    rw [primeFormsBackward_free]
    rfl

end Decomposition


/-! ### The projections and the generation hypotheses of the two de Rham complexes -/

section Unconditional

/-- `Ω¹_{B/A,γ}`, the divided power one-forms of the base of the extension. -/
public abbrev baseForms : Type u := dividedPowerDifferentials (A := A) B.dividedPowers

/-- `Ω¹_{B'/A,γ'}`, the divided power one-forms of the extension. -/
public abbrev primeForms (hp : p ≠ 0) : Type u :=
  dividedPowerDifferentials (A := A) (primeDividedPowers B p lam hp)

/-- The projection `π : Ω_{B/A} → Ω¹_{B/A,γ}` onto the divided power one-forms of the base. -/
public abbrev baseFormsProjection : Ω[(B : Type u)⁄A] →ₗ[(B : Type u)] baseForms A B :=
  (dividedPowerDifferentialRelations (A := A) B.dividedPowers).mkQ

/-- The projection `π' : Ω_{B'/A} → Ω¹_{B'/A,γ'}` onto the divided power one-forms of the
extension. -/
public abbrev primeFormsProjection (hp : p ≠ 0) :
    Ω[primeRing B p lam⁄A] →ₗ[primeRing B p lam] primeForms A B p lam hp :=
  (dividedPowerDifferentialRelations (A := A) (primeDividedPowers B p lam hp)).mkQ

/-- The projection onto the divided power one-forms of the base satisfies the generation
hypothesis of Tag 07HY, so the de Rham differential of `B` descends to it. -/
public theorem baseFormsGenerationHypothesis (S : SourceDeRham A (B : Type u)) :
    S.GenerationHypothesis (baseFormsProjection A B) :=
  dividedPowerDifferentials_generationHypothesis B S

/-- The projection onto the divided power one-forms of the extension satisfies the generation
hypothesis of Tag 07HY, so the de Rham differential of `B'` descends to it. -/
public theorem primeFormsGenerationHypothesis (hp : p ≠ 0)
    (S' : SourceDeRham A (primeRing B p lam)) :
    S'.GenerationHypothesis (primeFormsProjection A B p lam hp) :=
  dividedPowerDifferentials_generationHypothesis (primeDPRing B p lam hp) S'

end Unconditional

end Crystalline.PthRootExtension

namespace Crystalline

open PthRootExtension

/-- **Tag 07N1 for the extension `B → B[z]⟨ξ⟩/(ξ - (z^p - λ))`, with nothing assumed about its
one-forms.**  For a pair `(M, ∇)` over `B` with `∇` integrable, the canonical map of de Rham
complexes (07PY)

`c_M^• : M ⊗_B Ω^•_{B/A,γ} ⟶ M ⊗_B Ω^•_{B'/A,γ'}`

admits a map `e_M^•` in the opposite direction such that both `c_M^• ∘ e_M^•` and
`e_M^• ∘ c_M^•` are homotopic to multiplication by `p`.

This is `Crystalline.exists_homotopyInverse_pthRootExtension` specialised to the modules of
divided power differentials, where its two remaining hypotheses become theorems: the
decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz` of (07Q1) is
`Crystalline.PthRootExtension.pthRootDzDecomposition`, built from the divided powers `γ'` of
`J' = I B' + (ξ)` and the divided power polynomial and polynomial formulas for one-forms, and
the identity `d(ξ^[n+1]) = ξ^[n] dξ` is
`Crystalline.PthRootExtension.isDpowDifferential_dividedPowerDifferentials`, which holds because
`ξ` lies in `J'` and `γ'_n(ξ) = ξ^[n]`.

This is the uncompleted ingredient of [Stacks, Tag 07N1].  The tag itself, for the `p`-adically
completed rings and forms, is
`Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension` in
`StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedTheorem`, which
applies the present statement at every level `pⁿ` and assembles the results. -/
public theorem exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials
    {A : Type u} {M : Type w} [CommRing A]
    (B : DividedPowerRing.{u}) (p : ℕ) (lam : (B : Type u)) (hp : p ≠ 0)
    [Algebra A (B : Type u)]
    [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)]
    [AddCommGroup M] [Module (B : Type u) M]
    (S : SourceDeRham A (B : Type u))
    (S' : SourceDeRham A (primeRing B p lam))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M)
    (hintegrable : Connection.IsIntegrable S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
      (baseFormsGenerationHypothesis A B S) nabla)
    (c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))) →ₗ[A]
        RestrictScalars A (primeRing B p lam)
          ((primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[primeRing B p lam]
              (⋀[primeRing B p lam]^q (primeForms A B p lam hp))))
    (hc_wedge : ∀ (q : ℕ) (m : M) (omega : Fin q → (baseForms A B)),
      c q (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam hp) ∘ omega))
    (hc_comm : ∀ (q : ℕ) (x : M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))),
      c (q + 1)
          ((extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
            (baseFormsGenerationHypothesis A B S) nabla).toLinearMap q x) =
        (extendedConnection S' (primeFormsProjection A B p lam hp) (Submodule.mkQ_surjective _)
          (primeFormsGenerationHypothesis A B p lam hp S')
          (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
            (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap q (c q x)) :
    ∃ e : ∀ q : ℕ,
      RestrictScalars A (primeRing B p lam)
          ((primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[primeRing B p lam]
              (⋀[primeRing B p lam]^q (primeForms A B p lam hp))) →ₗ[A]
        RestrictScalars A (B : Type u) (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))),
      (∀ (q : ℕ) (x : RestrictScalars A (primeRing B p lam)
          ((primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[primeRing B p lam]
              (⋀[primeRing B p lam]^q (primeForms A B p lam hp)))),
          e (q + 1)
              ((extendedConnection S' (primeFormsProjection A B p lam hp)
                (Submodule.mkQ_surjective _) (primeFormsGenerationHypothesis A B p lam hp S')
                (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
                  (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap
                q x) =
            (extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
              (baseFormsGenerationHypothesis A B S) nabla).toLinearMap
              q (e q x)) ∧
        (∃ h : ∀ q : ℕ,
            RestrictScalars A (primeRing B p lam)
                ((primeRing B p lam ⊗[(B : Type u)] M)
                  ⊗[primeRing B p lam]
                    (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp))) →ₗ[A]
              RestrictScalars A (primeRing B p lam)
                ((primeRing B p lam ⊗[(B : Type u)] M)
                  ⊗[primeRing B p lam]
                    (⋀[primeRing B p lam]^q (primeForms A B p lam hp))),
          (∀ x : RestrictScalars A (primeRing B p lam)
              ((primeRing B p lam ⊗[(B : Type u)] M)
                ⊗[primeRing B p lam]
                  (⋀[primeRing B p lam]^0 (primeForms A B p lam hp))),
              h 0 ((extendedConnection S' (primeFormsProjection A B p lam hp)
                (Submodule.mkQ_surjective _) (primeFormsGenerationHypothesis A B p lam hp S')
                (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
                  (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap
                0 x) =
                RestrictScalars.lsmul A (primeRing B p lam)
                    ((primeRing B p lam ⊗[(B : Type u)] M)
                      ⊗[primeRing B p lam]
                        (⋀[primeRing B p lam]^0 (primeForms A B p lam hp)))
                    (algebraMap (B : Type u) (primeRing B p lam)
                      ((p : ℕ) : (B : Type u))) x -
                  c 0 (e 0 x)) ∧
            ∀ (q : ℕ)
                (x : RestrictScalars A (primeRing B p lam)
                  ((primeRing B p lam ⊗[(B : Type u)] M)
                    ⊗[primeRing B p lam]
                      (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp)))),
              (show RestrictScalars A (primeRing B p lam)
                  ((primeRing B p lam ⊗[(B : Type u)] M)
                    ⊗[primeRing B p lam]
                      (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp))) from
                (extendedConnection S' (primeFormsProjection A B p lam hp)
                  (Submodule.mkQ_surjective _)
                  (primeFormsGenerationHypothesis A B p lam hp S')
                  (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
                    (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap
                    q (h q x)) +
                  h (q + 1)
                    ((extendedConnection S' (primeFormsProjection A B p lam hp)
                      (Submodule.mkQ_surjective _) (primeFormsGenerationHypothesis A B p lam hp S')
                      (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
                        (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap
                      (q + 1) x) =
                RestrictScalars.lsmul A (primeRing B p lam)
                    ((primeRing B p lam ⊗[(B : Type u)] M)
                      ⊗[primeRing B p lam]
                        (⋀[primeRing B p lam]^(q + 1) (primeForms A B p lam hp)))
                    (algebraMap (B : Type u) (primeRing B p lam)
                      ((p : ℕ) : (B : Type u))) x -
                  c (q + 1) (e (q + 1) x)) ∧
        (∃ k : ∀ q : ℕ,
            RestrictScalars A (B : Type u)
                (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) (baseForms A B))) →ₗ[A]
              RestrictScalars A (B : Type u)
                (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))),
          (∀ x : RestrictScalars A (B : Type u)
              (M ⊗[(B : Type u)] (⋀[(B : Type u)]^0 (baseForms A B))),
              k 0 ((extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
                (baseFormsGenerationHypothesis A B S) nabla).toLinearMap
                0 x) =
                RestrictScalars.lsmul A (B : Type u)
                  (M ⊗[(B : Type u)] (⋀[(B : Type u)]^0 (baseForms A B)))
                  ((p : ℕ) : (B : Type u)) x - e 0 (c 0 x)) ∧
            ∀ (q : ℕ) (x : RestrictScalars A (B : Type u)
                (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) (baseForms A B)))),
              (extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
                (baseFormsGenerationHypothesis A B S) nabla).toLinearMap
                  q (k q x) +
                k (q + 1)
                  ((extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
                    (baseFormsGenerationHypothesis A B S) nabla).toLinearMap
                    (q + 1) x) =
                RestrictScalars.lsmul A (B : Type u)
                    (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) (baseForms A B)))
                    ((p : ℕ) : (B : Type u)) x -
                  e (q + 1) (c (q + 1) x)) :=
  exists_homotopyInverse_pthRootExtension B p lam S S'
    (baseFormsProjection A B) (primeFormsProjection A B p lam hp)
    (Submodule.mkQ_surjective _) (baseFormsGenerationHypothesis A B S)
    (Submodule.mkQ_surjective _) (primeFormsGenerationHypothesis A B p lam hp S')
    (primeFormsComparison A B p lam hp)
    (primeFormsComparison_dividedPowerDifferential A B p lam hp)
    nabla hintegrable c hc_wedge hc_comm (pthRootDzDecomposition A B p lam hp) hp
    (isDpowDifferential_dividedPowerDifferentials B p lam hp)

end Crystalline

end

end
