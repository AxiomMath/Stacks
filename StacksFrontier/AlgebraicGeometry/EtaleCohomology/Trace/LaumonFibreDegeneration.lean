module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsWeightsOfInjection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Laumon's degeneration at the origin

Let `σ` be a representation of `π₁(𝔸¹_k, x̄)` with coefficients in a finite extension `E` of `ℚ_ℓ`,
`ι'`-pure of weight `β`, and suppose that the two-parameter Fourier family
`H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a xⁿ + c x))` is `ι'`-pure of weight `β + 1` off a curve `D = 0` of the
`(a, c)`-plane (`Stacks.EtaleCohomology.LaumonFibrePure`). Restricting the family to a curve of
the plane through the origin which is not contained in `D = 0`, the sheaf `G = R¹pr₂!` of the
restricted family is lisse on a punctured neighbourhood `V` of the origin, where it is given by a
representation `τ` of `π₁(V, η̄)`, `ι'`-pure of weight `β + 1` because its stalks are the fibres of
the family. Its stalk at the origin is `H¹_c(𝔸¹_k̄, ℱ_σ)`, and the specialization map embeds it,
Frobenius-equivariantly, into the invariants of the inertia group `I_0` of `V` at the origin. By
Weil II 1.8.4 (`Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput`) the geometric Frobenius on
`τ^{I_0}` has weights `≤ β + 1`, hence so does the Frobenius on `H¹_c(𝔸¹_k̄, ℱ_σ)`
(Laumon; Kedlaya, *Fourier transforms and p-adic Weil II*, §6.4).

`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput` states the existence of `V`, `τ` (pure of
weight `β + 1`), the local data of Weil II 1.8.4 at the origin, and the specialization injection;
`Stacks.EtaleCohomology.laumonFibreDegenerationInput_of_family` deduces
`Stacks.EtaleCohomology.LaumonFibreDegenerationInput` from it and Weil II 1.8.4.

## Main definitions

* `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`.

## Main results

* `Stacks.EtaleCohomology.exists_addChar_ne_one_of_isPrimitiveRoot`: a nontrivial additive
  character of a finite field of characteristic `p` with values in a field containing a primitive
  `p`-th root of unity.
* `Stacks.EtaleCohomology.laumonFibreDegenerationInput_of_family`.
* `Stacks.EtaleCohomology.laumonFibreDegenerationInput_of_family_of_injection`: the same with
  Weil II 1.8.4 replaced by its inputs
  (`Stacks.EtaleCohomology.curveLocalInvariantsWeightInput_of_injection`).

## References

* G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987).
* K. Kedlaya, *Fourier transforms and p-adic Weil II*, Compositio Math. 142 (2006), §6.4.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open scoped Pointwise

universe u

namespace Stacks.EtaleCohomology

/-- **A nontrivial additive character from a primitive `p`-th root of unity**: if `E` contains a
primitive `p`-th root of unity `ζ` and `k` is a finite field of characteristic `p`, then
`a ↦ ζ ^ Tr_{k/𝔽_p}(a)` is a nontrivial additive character of `k` with values in `E`. -/
@[sga "7 XXII 4.0" "more general"]
public theorem exists_addChar_ne_one_of_isPrimitiveRoot (k : Type*) [Field k] [Finite k]
    {E : Type*} [CommRing E] (p : ℕ) [Fact p.Prime] [CharP k p] {ζ : E}
    (hζ : IsPrimitiveRoot ζ p) : ∃ ψ : AddChar k E, ψ ≠ 1 := by
  obtain rfl := ringChar.eq k p
  let : Algebra (ZMod (ringChar k)) k := ZMod.algebra _ _
  let ψ := (AddChar.zmodChar (ringChar k) hζ.pow_eq_one).compAddMonoidHom
    (Algebra.trace (ZMod (ringChar k)) k).toAddMonoidHom
  refine ⟨ψ, AddChar.ne_one_iff.2 ?_⟩
  obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate k one_ne_zero
  rw [one_mul] at ha
  refine ⟨a, fun h => ha ?_⟩
  change ζ ^ (Algebra.trace (ZMod (ringChar k)) k a).val = 1 at h
  rw [hζ.pow_eq_one_iff_dvd] at h
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt _)

/-- **The degeneration of the Fourier family at the origin** (Laumon; Kedlaya, *Fourier transforms
and p-adic Weil II*, §6.4). Let `σ` be as in `Stacks.EtaleCohomology.LaumonFibreDegenerationInput`,
`ι'`-pure of weight `β`, `ψ` a nontrivial additive character, `n₀` prime to `p` and `D ≠ 0` such
that the Fourier family `H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a x^{n₀} + c x))` is `ι'`-pure of weight `β + 1` off
`D = 0` (`Stacks.EtaleCohomology.LaumonFibrePure`). Then there are

* an open `V` of a curve `W ⊆ 𝔸¹_{k'}` over a finite extension `k'` of `k` and a closed point
  `y ∈ W ∖ V` (the origin of a curve through the origin of the `(a, c)`-plane not contained in
  `D = 0`, with `V` inside the lisse locus of `G = R¹pr₂!` of the restricted family),
* the data of Weil II 1.8.4 at `y` (`Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput`):
  a discrete valuation ring `A ≅ 𝒪_{W,y}`, a separable closure `L` of the function field of `V`,
  a place `P` of `L` over `A` and an arithmetic Frobenius `Fr` at `P`,
* a representation `τ` of `π₁(V, η̄)` with coefficients in `E` (the representation of `G|_V`),
  `ι'`-pure of weight `β + 1`, and
* `d_y > 0` with `#κ(y) = q ^ {d_y}` and an injective `E`-linear map from
  `H¹_c(𝔸¹_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` (the stalk of `G` at `y`) to the `τ(I_y)`-invariants (the
  specialization map) carrying `(π^*) ^ {d_y}` to the geometric Frobenius `τ(φ Fr⁻¹)`.

The existence is stated in continuation-passing form (`∀ C, (∀ data, facts → C) → C`), so that the
data can carry their instances. -/
public def LaumonDegenerationFamilyInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f
          j kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ (ψ : AddChar k E), ψ ≠ 1 → ∀ (n₀ : ℕ), ¬ p ∣ n₀ →
    ∀ (D : MvPolynomial (Fin 2) k), D ≠ 0 → LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n₀ D →
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    haveI := (restrictScalarsRepCoefficientSheaf B U x b σ
      hσ).rationalCohomologyModule_isScalarTower f j kbar 1 E
        (algebraMap_conjIntegralSubring_algebraMap _ _)
    ∀ C : Prop, (∀ (V : B.Scheme)
      [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
      [IsNoetherian V.1] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
      (k' : Type u) [Field k'] [Fintype k'] (fV : V.1 ⟶ Spec (.of k'))
      [LocallyOfFiniteType fV] [QuasiCompact fV] [IsSeparated fV] [SmoothOfRelativeDimension 1 fV]
      (_ : CompactificationOf (Over.mk fV)) (kbar' : Type u) [Field kbar'] [Algebra k' kbar']
      [IsAlgClosure k' kbar']
      [ConnectedSpace ↥(Limits.pullback fV (Spec.map (CommRingCat.ofHom (algebraMap k' kbar'))))]
      (n' : ℕ) [CharP k' p] (_ : Fintype.card k' = p ^ n')
      -- the curve `W ⊇ V` and the origin `y`
      (W : B.Scheme) (fW : W.1 ⟶ Spec (.of k')) [LocallyOfFiniteType fW] [QuasiCompact fW]
      [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
      (eW : W.1 ⟶ Spec (.of (Polynomial k'))) [IsOpenImmersion eW]
      (_ : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))) = fW)
      (jW : V.1 ⟶ W.1) [IsOpenImmersion jW]
      (_ : jW ≫ fW = fV) (y : W.1) (_ : IsClosed ({y} : Set W.1)) (_ : y ∉ Set.range jW.base)
      (hy : jW.base (genericPoint V.1) ⤳ y)
      -- the local field at `y`
      (L Ω : Type u) [Field L] [Field Ω]
      [Algebra (V.1.residueField (genericPoint V.1)) L]
      [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
      [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
      [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
      [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
      (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [Algebra A (V.1.residueField (genericPoint V.1))]
      [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
      [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
      [Finite (IsLocalRing.ResidueField A)]
      (eA : A ≃+* W.1.presheaf.stalk y)
      (_ : ∀ a : A, algebraMap A (V.1.residueField (genericPoint V.1)) a =
        (curveLocalRingToFunctionField jW hy).hom (eA a))
      (P : Ideal (integralClosure A L)) [P.IsMaximal]
      (Fr : Gal(L / V.1.residueField (genericPoint V.1)))
      (hFrD :
        letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
          (integralClosure A L)
        Fr ∈ MulAction.stabilizer Gal(L / V.1.residueField (genericPoint V.1)) P)
      (_ :
        letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
          (integralClosure A L)
        ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
      -- the representation of `G|_V`, pure of weight `β + 1`
      {r : ℕ} (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
        (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
          →* GL (Fin r) E)
      (_ : Continuous (restrictScalarsRep b τ)),
      (∀ (z : closedPoints V.1) (c : ℂ),
          ((τ (geometricFrobeniusFamily fV ((algebraicClosureGeometricPoint
            (V.1.residueField (genericPoint V.1)) Ω).map
              (V.1.fromSpecResidueField (genericPoint V.1))) z)).val.charpoly.map ι').IsRoot c →
          ‖c‖ = ((p ^ n' : ℕ) : ℝ) ^ (((residueDegree fV z.1 : ℤ) * ((β + 1 : ℤ) : ℝ) : ℝ) / 2)) →
      -- the specialization injection
      ∀ dy : ℕ, 0 < dy → Nat.card (IsLocalRing.ResidueField A) = (p ^ n) ^ dy →
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∀ J : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1 →ₗ[E]
          Representation.invariants ((matrixRepresentation τ).comp
            (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype),
        Function.Injective J →
        J ∘ₗ (((restrictScalarsRepCoefficientSheaf B U x b σ
            hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard) ^ dy) =
          ((Matrix.toLin' ((τ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹) :
            GL (Fin r) E) : Matrix (Fin r) (Fin r) E)).restrict
          (toLin'_mem_invariants_of_mem_normalizer τ
            (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
            (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
              (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD))) ∘ₗ J → C) → C

/-- **`Stacks.EtaleCohomology.LaumonFibreDegenerationInput` from the degeneration of the Fourier
family and Weil II 1.8.4.** Choose a nontrivial additive character `ψ` (from `ζ_p ∈ E`), an
exponent `n₀ > N` prime to `p` and the curve `D` of the purity hypothesis; the degeneration
(`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`) gives a representation `τ` pure of weight
`β + 1` near the origin and the specialization injection of `H¹_c(𝔸¹_k̄, ℱ_σ)` into the inertia
invariants, which have weights `≤ β + 1` by Weil II 1.8.4
(`Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput`). -/
public theorem laumonFibreDegenerationInput_of_family (h9 : CurveLocalInvariantsWeightInput.{u})
    (hfam : LaumonDegenerationFamilyInput.{u}) : LaumonFibreDegenerationInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hζ ι' β hV hpure h7
  let := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
  have := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule_isScalarTower
    f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f
      j kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) := hV
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one_of_isPrimitiveRoot k p hζ
  obtain ⟨N, hN⟩ := h7 ψ hψ
  have hp1 : ¬ p ∣ N * p + 1 := fun h =>
    (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (dvd_mul_left p N)).1 h))
  obtain ⟨D, hD, hfib⟩ := hN (N * p + 1)
    (Nat.lt_succ_of_le (Nat.le_mul_of_pos_right N (Fact.out : p.Prime).pos)) hp1
  refine hfam B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ ι' β hpure ψ hψ (N * p + 1) hp1 D hD
    hfib _ ?_
  intro V _ _ _ _ _ k' _ _ fV _ _ _ _ jV kbar' _ _ _ _ n' _ hcard' W fW _ _ _ _ eW _ heW jW _ hjW
    y hyc hyV hy L Ω _ _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ _ eA hA P _ Fr hFrD hFr r τ hτ hpτ dy hdy
    hcardA J hJ hJT
  have hloc := h9 B V ℓ k' fV jV kbar' p n' hcard' hℓp W fW eW heW jW hjW y hyc hyV hy L Ω A eA
    hA P Fr hFrD hFr E b τ hτ ι' (β + 1) hpτ
  rw [hcardA] at hloc
  refine IsCharpolyNormMixedOfWeightLE.of_pow hdy.ne' (hloc.of_injective (fun v => ?_) hJ)
  exact LinearMap.congr_fun hJT v

/-- **`Stacks.EtaleCohomology.LaumonFibreDegenerationInput` from the degeneration of the Fourier
family and the inputs of Weil II 1.8.4**: the `E`-linear trace formula on curves
(`Stacks.EtaleCohomology.CurveLinearTraceFormulaInput`), the `E`-linear identification of `H²_c`
with the twisted coinvariants (`Stacks.EtaleCohomology.CurveLinearCoinvariantsInput`) and the
injection of the local invariants into `H¹_c`
(`Stacks.EtaleCohomology.CurveLocalInvariantsInjectionInput`), through
`Stacks.EtaleCohomology.curveLocalInvariantsWeightInput_of_injection`. -/
public theorem laumonFibreDegenerationInput_of_family_of_injection
    (hD8 : CurveLinearTraceFormulaInput.{u}) (hC : CurveLinearCoinvariantsInput.{u})
    (hinj : CurveLocalInvariantsInjectionInput.{u}) (hfam : LaumonDegenerationFamilyInput.{u}) :
    LaumonFibreDegenerationInput.{u} :=
  laumonFibreDegenerationInput_of_family (curveLocalInvariantsWeightInput_of_injection hD8 hC hinj)
    hfam

end Stacks.EtaleCohomology

end
