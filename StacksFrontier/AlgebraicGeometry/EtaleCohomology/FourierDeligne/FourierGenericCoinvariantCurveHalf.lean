module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTopCompactSupportNoConstantQuotient
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantFibreSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CurveOpenConstantExt
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety

/-!
# The curve half of the generic coinvariant vanishing

On a nonempty open `C` of `X ≅ 𝔸¹_Ω`, `Ω` algebraically closed, the top compactly supported
cohomology `H²_c(C, N)` of a locally constant sheaf `N` with finite values over a finite ring `Λ`
whose characteristic is invertible in `Ω` vanishes as soon as `N` has no constant simple quotient
(`Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_affineLineOpen`): `C` is an open
of the smooth proper curve `ℙ¹_Ω` through the first chart, and
`Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_of_hasNoConstantSimpleQuotient`
applies. This is `Stacks.EtaleCohomology.AffineLineOpenTopCohomologyVanishingInput` under the
hypothesis that the characteristic of `Λ` is invertible in `Ω`; without it the statement would
involve the `p`-torsion of `H²_c` in characteristic `p`, which the applications never need.

For the generic coinvariant vanishing (L2) of the Fourier transform the coefficient ring has
`#k` invertible, so its characteristic is invertible in every field over `k`
(`Stacks.EtaleCohomology.isUnit_ringChar_cast_of_isUnit_card`), and (L2) follows from the
Artin–Schreier half alone
(`Stacks.EtaleCohomology.fourierGenericCoinvariantVanishingInput_of_twist`), in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_affineLineOpen`.
* `Stacks.EtaleCohomology.isUnit_ringChar_cast_of_isUnit_card`.
* `Stacks.EtaleCohomology.fourierFibreCoinvariantVanishingInput_of_twist`.
* `Stacks.EtaleCohomology.fourierGenericCoinvariantVanishingInput_of_twist`.

## Implementation notes

`Rf_!` lives in the standard model `HasDerivedCategory.standard`, and so do the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard

/-- **`H²_c` of a locally constant sheaf without constant simple quotient on an open of `𝔸¹_Ω`
vanishes.** For `Ω` algebraically closed, `C` a nonempty open of `X ≅ 𝔸¹_Ω`, `Λ` a finite
commutative ring whose characteristic is invertible in `Ω`, and `N` a locally constant sheaf of
`Λ`-modules with finite values on `C_étale` with no nonzero morphism to the constant sheaf on a
simple `Λ`-module, `H²_c(C, N) = 0` for every compactification of `C ⟶ Spec Ω`. -/
theorem isZero_homology_two_derivedLowerShriek_affineLineOpen (Ω : Type u) [Field Ω]
    [IsAlgClosed Ω] (Λ : Type) [CommRing Λ] [Finite Λ] (hΛ : IsUnit ((ringChar Λ : ℕ) : Ω))
    {X C : Scheme.{u}} (f : X ⟶ Spec (.of Ω))
    (hX : ∃ e : X ≅ AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)),
      e.hom ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)) ↘ Spec (.of Ω)) = f)
    (ι : C ⟶ X) [IsOpenImmersion ι] [Nonempty C] (N : EtaleModules.{u, 0} Λ C)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ C.smallEtaleTopology
      (fun E => Module.Finite Λ E) N)
    (hNQ : HasNoConstantSimpleQuotient Λ N) (jc : CompactificationOf (Over.mk (ι ≫ f))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} (ι ≫ f) jc Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N))) := by
  obtain ⟨e, he⟩ := hX
  have := isCurve_projectiveSpaceOver_one Ω
  let j₀ : AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)) ⟶
      projectiveSpaceOver 1 (Spec (.of Ω)) :=
    ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of Ω))
  have : IsOpenImmersion j₀ := ProjectiveSpace.isOpenImmersion_fromAffineSpace 1 0 (Spec (.of Ω))
  have hj₀ : j₀ ≫ (projectiveSpaceOver 1 (Spec (.of Ω)) ↘ Spec (.of Ω)) =
      AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)) ↘ Spec (.of Ω) :=
    ProjectiveSpace.fromAffineSpace_over 1 0 (Spec (.of Ω))
  exact isZero_homology_two_derivedLowerShriek_of_hasNoConstantSimpleQuotient Ω Λ hΛ
    (projectiveSpaceOver 1 (Spec (.of Ω)) ↘ Spec (.of Ω)) (ι ≫ e.hom ≫ j₀) (ι ≫ f)
    (by rw [Category.assoc, Category.assoc, hj₀, he]) N hN hNQ jc

/-- **The characteristic of a finite ring in which `#k` is a unit is invertible in every field over
`k`**: it is prime to the characteristic `p` of `k`, `#k` being a power of `p`. -/
theorem isUnit_ringChar_cast_of_isUnit_card (k : Type*) [Field k] [Fintype k] (Λ : Type*)
    [CommRing Λ] [Finite Λ] {Ω : Type*} [Field Ω] (φ : k →+* Ω)
    (hq : IsUnit (Fintype.card k : Λ)) : IsUnit ((ringChar Λ : ℕ) : Ω) := by
  obtain ⟨p, hpk⟩ := CharP.exists k
  obtain ⟨r, hp, hcard⟩ := FiniteField.card k p
  have : CharP Ω p := charP_of_injective_ringHom φ.injective p
  have hpΛ : IsUnit (p : Λ) :=
    (isUnit_pow_iff r.ne_zero).1 (by rwa [← Nat.cast_pow, ← hcard])
  have hndvd : ¬ p ∣ ringChar Λ := by
    rintro ⟨m, hm⟩
    have hn0 : ringChar Λ ≠ 0 := CharP.char_ne_zero_of_finite Λ (ringChar Λ)
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp_all
    have hmΛ : ((m : ℕ) : Λ) = 0 := by
      have h := ringChar.Nat.cast_ringChar (R := Λ)
      rw [hm, Nat.cast_mul] at h
      exact hpΛ.mul_right_eq_zero.1 h
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (ringChar.dvd hmΛ)
    rw [hm] at hle
    nlinarith [hp.two_le, Nat.pos_of_ne_zero hm0]
  exact Ne.isUnit (fun h => hndvd ((CharP.cast_eq_zero_iff Ω p _).1 h))

local notation "𝔸f" => affineLineStructureMap

/-- **The fibre input from the Artin–Schreier half alone**: on the open `U` of the
Artin–Schreier half, the fibre `X_s` of `pr₂` is a copy of `𝔸¹_Ω`, its open `C_s` over `V` is
nonempty, `t⁻¹ M ⊗ L_ψ(x s)` is locally constant with finite values, and the characteristic of
`Λ` is invertible in `Ω`, `#k` being a unit in `Λ`; so
`Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_affineLineOpen` applies. -/
theorem fourierFibreCoinvariantVanishingInput_of_twist
    (hT : FourierTwistNoConstantQuotientInput.{u}) :
    FourierFibreCoinvariantVanishingInput.{u} := by
  intro k _ _ Λ _ _ ψ B p₀ hψ hq V jV _ _ M hM
  obtain ⟨U, jU, hU, hUne, hNQ⟩ := hT k Λ ψ B p₀ hψ hq jV M hM
  refine ⟨U, jU, hU, hUne, fun y jc => ?_⟩
  let pr₁ := pullback.fst (𝔸f k) (𝔸f k)
  let pr₂ := pullback.snd (𝔸f k) (𝔸f k)
  let s := (GeometricPoint.ofPoint U y).hom ≫ jU
  let Ω := (GeometricPoint.ofPoint U y).residueField
  let f' := pullback.snd pr₂ s
  let u' := pullback.fst pr₂ s
  let w := u' ≫ pr₁
  let ι := pullback.fst w jV
  let t := pullback.snd w jV
  -- `C_s` is nonempty: the fibre maps onto the `x`-line
  have hsq : IsPullback w f' (𝔸f k) (s ≫ 𝔸f k) :=
    (IsPullback.of_hasPullback pr₂ s).paste_horiz (IsPullback.of_hasPullback (𝔸f k) (𝔸f k))
  have : Surjective (s ≫ 𝔸f k) := ⟨fun _ => ⟨(default : Spec (.of Ω)), Subsingleton.elim _ _⟩⟩
  have hw : Surjective w := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip inferInstance
  have : Nonempty ↥(pullback w jV : Scheme.{u}) := by
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨z, hz⟩ := hw.surj (jV v)
    obtain ⟨c, -⟩ : z ∈ Set.range ι.base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨v, hz.symm⟩
    exact ⟨c⟩
  -- the twisted sheaf is locally constant with finite values
  have hN := isLocallyConstantWith_tensor Λ _ _ (isLocallyConstantWith_inverseImage Λ _ t hM)
    (isLocallyFreeEtaleModule_inverseImage Λ (ι ≫ u')
      (isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀))
  -- the characteristic of `Λ` is invertible in `Ω`
  have hΛ : IsUnit ((ringChar Λ : ℕ) : Ω) :=
    isUnit_ringChar_cast_of_isUnit_card k Λ
      ((Scheme.Spec.preimage s).unop.hom.comp Polynomial.C) hq
  refine isZero_homology_two_derivedLowerShriek_affineLineOpen Ω Λ hΛ f'
    (nonempty_affineLineFibre_iso k s) ι _ ?_ (hNQ y) jc
  refine isLocallyConstantWith_of_imp Λ ?_ hN
  rintro E ⟨E₁, E₂, h₁, h₂, rfl⟩
  have := h₁
  have := h₂.2
  exact inferInstanceAs (Module.Finite Λ (TensorProduct Λ E₁ E₂))

/-- **(L2) from the Artin–Schreier half**:
`Stacks.EtaleCohomology.FourierGenericCoinvariantVanishingInput` follows from the generic
absence of constant simple quotients of the twisted sheaves `t⁻¹ M ⊗ L_ψ(x s)`, the curve half
being `Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_affineLineOpen`. -/
theorem fourierGenericCoinvariantVanishingInput_of_twist
    (hT : FourierTwistNoConstantQuotientInput.{u}) :
    FourierGenericCoinvariantVanishingInput.{u} :=
  fourierGenericCoinvariantVanishingInput_of_fibre
    (fourierFibreCoinvariantVanishingInput_of_twist hT)

end Stacks.EtaleCohomology

end
