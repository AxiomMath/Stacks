module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyStalkPurity

/-!
# `E`-linear proper base change at a stalk, as an isomorphism

Let `g : U ⟶ W` be separated of finite type with a compactification, `w` a closed point of `W` with
finite residue field and `Y` the fibre of `g` over `w`. For an ℓ-adic sheaf `F` on `U` with
coefficients in a `ℤ_ℓ`-algebra `O` and `E = O[1/ℓ]`, proper base change at the stalk ([Tags 0F7L,
0F7I](https://stacks.math.columbia.edu/tag/0F7L)) identifies `Hʳ_c(Y_{κ̄}, F|_Y ⊗ ℚ_ℓ)` with the
rational stalk `ℚ_ℓ ⊗ (Rʳ g_! F)_w̄`, `E`-linearly and carrying the Frobenius of `κ(w)` to the
geometric Frobenius at `w`
(`Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearIsoInput`). Equality of the
`E`-linear characteristic polynomials follows by conjugation
(`Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearInput_of_iso`), which is input (b)
of the purity step of Laumon's degeneration
(`Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearInput`); the isomorphism itself is
what the specialization step at the origin needs
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearIsoInput`.

## Main results

* `Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearInput_of_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- **`E`-linear proper base change at the stalks of `Rʳ g_!`, as an isomorphism** (Tags 0F7L,
0F7I, with coefficients): for `g : U ⟶ W` separated of finite type with a compactification and a
closed point `w` of `W` (of finite type over a finite field `k`), there are a fibre
`Y = U ×_W Spec κ(w)` of `g` over `w` in the big étale site and a compactification of `Y` over
`κ(w)` such that for every ℓ-adic sheaf `F` with coefficients in a `ℤ_ℓ`-algebra `O` and
`E = O[1/ℓ]`, if the rational stalk of `Rʳ g_! F` at `w̄` is finite-dimensional, there is an
`E`-linear isomorphism `Hʳ_c(Y_{κ̄}, F|_Y ⊗ ℚ_ℓ) ≃ ℚ_ℓ ⊗ (Rʳ g_! F)_w̄` carrying the Frobenius of
`κ(w)` to the geometric Frobenius at `w` (the `E`-structures coming from the actions of `O`). The
existence is stated in continuation-passing form; the data are those of
`Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearInput`. -/
public def CoefficientHigherDirectImageStalkLinearIsoInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] (U W : B.Scheme) [IsNoetherian U.1] [IsNoetherian W.1]
    (g : U ⟶ W) [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
    (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] (w : closedPoints W.1)
    [Fintype (W.1.residueField w.1)] (kbar : Type u) [Field kbar]
    [Algebra (W.1.residueField w.1) kbar] [IsAlgClosure (W.1.residueField w.1) kbar] (p n : ℕ)
    [Fact p.Prime] [CharP (W.1.residueField w.1) p]
    (hcard : Fintype.card (W.1.residueField w.1) = p ^ n) (C : Prop),
    (∀ (Y : B.Scheme) [IsNoetherian Y.1] (i : Y ⟶ U) (fY : Y.1 ⟶ Spec (.of (W.1.residueField w.1)))
      [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY],
      IsPullback (B.inclusion.map i) fY (B.inclusion.map g) (W.1.fromSpecResidueField w.1) →
      ∀ jY : CompactificationOf (Over.mk fY),
      (∀ {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B U ℓ O)
        (r : ℕ) (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra O E]
        [IsLocalization (Submonoid.powers (ℓ : O)) E]
        (_hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
        [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B W ℓ
          (F.higherDirectImageShriek B ℓ g jg r).toLAdicSheaf (geometricPointAt W.1 w.1))],
        letI := (F.higherDirectImageShriek B ℓ g jg r).rationalStalkModule
          (geometricPointAt W.1 w.1) E
        letI := (LAdicSheaf.CoefficientSheaf.inverseImage i F).rationalCohomologyModule fY jY
          kbar r E
        ∃ Θ : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
            (LAdicSheaf.CoefficientSheaf.inverseImage i F).toLAdicSheaf r ≃ₗ[E]
            LAdicSheaf.rationalStalkLeft B W ℓ (F.higherDirectImageShriek B ℓ g jg r).toLAdicSheaf
              (geometricPointAt W.1 w.1),
          Θ.toLinearMap ∘ₗ (LAdicSheaf.CoefficientSheaf.inverseImage i
              F).rationalGeometricCompactlySupportedFrobenius fY jY kbar r E p n hcard =
            (F.higherDirectImageShriek B ℓ g jg r).rationalStalkFrobenius E w.1
              (finite_residueField fW w.1 w.2) ∘ₗ Θ.toLinearMap) →
      C) → C

/-- **Conjugate endomorphisms have the same characteristic polynomial**: if `e : M ≃ N` carries
`φ` to `ψ`, then `φ` and `ψ` have the same characteristic polynomial. -/
theorem charpoly_eq_of_linearEquiv_comp {K M N : Type*} [Field K] [AddCommGroup M]
    [AddCommGroup N] [Module K M] [Module K N] [Module.Finite K M] [Module.Finite K N]
    (e : M ≃ₗ[K] N) (φ : M →ₗ[K] M) (ψ : N →ₗ[K] N)
    (h : e.toLinearMap ∘ₗ φ = ψ ∘ₗ e.toLinearMap) : φ.charpoly = ψ.charpoly := by
  rw [← e.charpoly_conj φ]
  congr 1
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  have h' := LinearMap.congr_fun h (e.symm v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h'
  exact h'

/-- **The isomorphism form of `E`-linear proper base change at a stalk gives the characteristic
polynomial form** (input (b) of `Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep`):
`Hʳ_c(Y_{κ̄}, F|_Y ⊗ ℚ_ℓ)` is finite dimensional, being isomorphic to the rational stalk, and the
two Frobenius endomorphisms are conjugate. -/
public theorem coefficientHigherDirectImageStalkLinearInput_of_iso
    (h : CoefficientHigherDirectImageStalkLinearIsoInput.{u}) :
    CoefficientHigherDirectImageStalkLinearInput.{u} := by
  intro B ℓ _ _ _ _ k _ _ U W _ _ g _ _ _ jg fW _ w _ kbar _ _ _ p n _ _ hcard C hC
  refine h B ℓ k U W g jg fW w kbar p n hcard C ?_
  intro Y _ i fY _ _ _ hpb jY hY
  refine hC Y i fY hpb jY ?_
  intro O _ _ F r E _ _ _ _ hOE _
  obtain ⟨Θ, hΘ⟩ := hY F r E hOE
  let := (F.higherDirectImageShriek B ℓ g jg r).rationalStalkModule (geometricPointAt W.1 w.1) E
  have := (F.higherDirectImageShriek B ℓ g jg r).rationalStalkModule_isScalarTower
    (geometricPointAt W.1 w.1) E hOE
  let := (LAdicSheaf.CoefficientSheaf.inverseImage i F).rationalCohomologyModule fY jY kbar r E
  have := (LAdicSheaf.CoefficientSheaf.inverseImage i F).rationalCohomologyModule_isScalarTower
    fY jY kbar r E hOE
  have hY' : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
        (LAdicSheaf.CoefficientSheaf.inverseImage i F).toLAdicSheaf r) :=
    LinearEquiv.finiteDimensional (Θ.restrictScalars ℚ_[ℓ]).symm
  refine ⟨hY', ?_⟩
  have : Module.Finite E (LAdicSheaf.rationalStalkLeft B W ℓ
      (F.higherDirectImageShriek B ℓ g jg r).toLAdicSheaf (geometricPointAt W.1 w.1)) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  have : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ
      fY jY kbar (LAdicSheaf.CoefficientSheaf.inverseImage i F).toLAdicSheaf r) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  exact (charpoly_eq_of_linearEquiv_comp Θ _ _ hΘ).symm

end Stacks.EtaleCohomology

end
