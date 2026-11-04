module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonContragredientInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierFamilyConjugateWildProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLisseLocalTheory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonLineBasicOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteCompactSupportCohomology

/-!
# Equal absolute values of the Fourier family in the totally wild range

The first half of Laumon's purity of the two-parameter Fourier family
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, Theorem 6.4), `Stacks.EtaleCohomology.LaumonFourierEquinormStableInput`, off the line
`a = 0`, from:

* Laumon's local theory away from `a = 0`: for `n` large prime to `p` and `a ≠ 0` the Fourier
  family is lisse over every open of the `t`-line
  (`Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput`), applied to `(σ, ψ)` AND to the dual
  `(σ^∨, ψ⁻¹)`, whose hypotheses are checked in
  `Stacks.EtaleCohomology.forall_eq_bot_or_eq_top_contragredient`,
  `Stacks.EtaleCohomology.laumonStablyAbsIrr_contragredient` and
  `Stacks.EtaleCohomology.norm_eq_rpow_of_isRoot_contragredient` (weight `-β`);
* the absolute irreducibility of the Fourier transform (L6,
  `Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput`);
* the identification of the fibres over the rational points
  (`Stacks.EtaleCohomology.LaumonFourierFamilyFibreInput`) and over all closed points
  (`Stacks.EtaleCohomology.LaumonFourierFamilyFieldExtensionInput`), the latter giving the real
  partner (`Stacks.EtaleCohomology.laumonFourierFamilyConjugateWildInput_of_inputs`).

The curve is `D = a`: at a fibre over `(k', a, c)` with `a ≠ 0`, the open `V'` is the whole
`t`-line (`Stacks.EtaleCohomology.laumonLineBasicOpen_elim` for `P = 1`), over which both the
family of `σ` and that of `σ^∨` are lisse, and the argument of
`Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_inputs` (Weil II 1.5.1 on `V'` for the
representation `τ` of the family, read at the rational point over `t = c`) applies with the real
partner of the totally wild range.

## Main results

* `Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_inputs'`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- **Equal absolute values of the Fourier family for `σ` which stays absolutely irreducible**
(Laumon; Kedlaya, *Fourier transforms and p-adic Weil II*, Theorem 6.4, first half;
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), off the curve `a = 0`, from Laumon's local
theory away from `a = 0` (`Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput`, used for `σ`
and for `σ^∨`), the absolute irreducibility of the Fourier transform (L6,
`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput`) and the identification of the fibres
(`Stacks.EtaleCohomology.LaumonFourierFamilyFibreInput`,
`Stacks.EtaleCohomology.LaumonFourierFamilyFieldExtensionInput`). The real partner is
`Stacks.EtaleCohomology.laumonFourierFamilyConjugateWildInput_of_inputs`, `E`-linear proper base
change at the stalks is `Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearInput`. -/
public theorem laumonFourierEquinormStableInput_of_inputs'
    (hL6 : LaumonFourierLineAbsIrrInput.{u}) (hlis : LaumonFourierLineLisseAwayInput.{u})
    (hfib : LaumonFourierFamilyFibreInput.{u}) (hext : LaumonFourierFamilyFieldExtensionInput.{u}) :
    LaumonFourierEquinormStableInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hst hζ ι' β _ hpure ψ hψ
  -- the hypotheses on `σ` hold for `σ^∨`, with weight `-β`
  have hσd := continuous_restrictScalarsRep_contragredient b hσ
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
      U ℓ f j kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b (contragredient σ))
        hσd) 1) :=
    (LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ k kbar p n hcard hℓp U f j _ 1).1
  have hpured : ∀ (y : closedPoints U.1) (z : ℂ),
      (((contragredient σ) (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
      ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * ((-β : ℤ) : ℝ) : ℝ) / 2) := by
    intro y z hz
    rw [norm_eq_rpow_of_isRoot_contragredient σ ι' (geometricFrobeniusFamily f x y)
      ((p ^ n : ℕ) : ℝ) ((residueDegree f y.1 : ℤ) * β : ℝ) (Nat.cast_nonneg _) (hpure y) z hz]
    congr 1
    push_cast
    ring
  obtain ⟨N₁, hN₁⟩ := hlis B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hst hζ ι' β hpure
    ψ hψ
  obtain ⟨N₂, hN₂⟩ := hlis B U ℓ k f e he j kbar p n hcard hℓp x E b (contragredient σ) hσd K
    (forall_eq_bot_or_eq_top_contragredient σ K hirr) (laumonStablyAbsIrr_contragredient hst) hζ
    ι' (-β) hpured ψ⁻¹ (inv_ne_one.2 hψ)
  obtain ⟨N₃, hN₃⟩ := laumonFourierFamilyConjugateWildInput_of_inputs hext B U ℓ k f e he j kbar p n
    hcard hℓp x E b σ hσ K hirr hst hζ ι' β hpure ψ hψ
  refine ⟨max N₁ (max N₂ N₃), fun n₀ hn₀ hpn₀ => ?_⟩
  refine ⟨MvPolynomial.X 0, MvPolynomial.X_ne_zero 0, ?_⟩
  intro k' _ _ _ hX' _ _ x' hx' a c hac p₀ hτ₀ _ _ _ j' kbar' _ _ _ p' n' _ _ hcard' hV'
  have ha : a ≠ 0 := by
    simpa only [MvPolynomial.map_X, MvPolynomial.eval_X, Matrix.cons_val_zero] using hac
  have hpp : p = p' := CharP.eq k'
    (charP_of_injective_algebraMap (algebraMap k k').injective p) ‹CharP k' p'›
  subst hpp
  classical
  -- a point `z̄` of the `(x, t)`-plane over `x̄'` and the pullback `σ₁` of `σ` to `𝔸¹_{k'}`
  have hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))) :=
    (schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).2 (Polynomial.cardinalMk_le_max.trans_lt
      (max_lt ((schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).1 hX') B.aleph0_lt_cutoff))
  let zz : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))) :=
    x'.map (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X : Polynomial k'))))
  have hzz : zz.map (laumonFamilyPr₁ k') = x' := by
    simp only [zz]
    rw [← GeometricPoint.map_comp, laumonFourier_specMap_evalRingHom_X_comp_pr₁]
    cases x'
    simp only [GeometricPoint.map, Category.comp_id]
  have hz : (zz.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x := by
    rwa [hzz]
  obtain ⟨pz⟩ := Stacks.ArtinSchreier.nonempty_finiteEtaleFiber_cover k'
    (laumonFourierKernel k' n₀ a) zz
  have hσ₁ := continuous_restrictScalarsRep_comp_etaleFundamentalGroupMap
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
    (zz.map (laumonFamilyPr₁ k')) hz b σ hσ
  have hσ₂ := continuous_restrictScalarsRep_comp_etaleFundamentalGroupMap
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
    (zz.map (laumonFamilyPr₁ k')) hz b (contragredient σ) hσd
  -- the whole `t`-line `V'`, over which both families are lisse
  refine laumonLineBasicOpen_elim k' B hS hX' (P := 1) one_ne_zero _ ?_
  intro V' U' _ _ _ _ _ jV' jU g' _ _ _ jg' fV _ _ _ _ jfV hjV' hrange hfV hpb hconn
  have hlisse := hN₁ n₀ (by omega) hpn₀ k' a ha hS hX' zz hz pz hσ₁ V' U' jV' jU g' jg' hjV' hpb
  have hlis₂ := hN₂ n₀ (by omega) hpn₀ k' a ha hS hX' zz hz pz hσ₂ V' U' jV' jU g' jg' hjV' hpb
  -- the rational point `v` of `V'` over `t = c`
  obtain ⟨v, hvcl, hbij, hvX⟩ := exists_laumonPoint_of_eval_ne_zero jV' hjV' 1 hrange c
    (by simp)
  let xV : GeometricPoint V'.1 := geometricPointAt V'.1 v
  -- the representation `τ` of the lisse family `G_V`
  obtain ⟨r, ρ, hρ, φ, ψ₀, N', hφψ, hψφ, mτ, τ, P, Q, hτc, hPQ, hQP, hα, hτ⟩ :=
    exists_restrictScalarsRep_of_isLisse B V' xV _ E
      (algebraMap_conjIntegralSubring_algebraMap _ _) b hlisse
  -- `τ` is absolutely irreducible (L6)
  obtain ⟨p₁⟩ := Stacks.ArtinSchreier.nonempty_finiteEtaleFiber_cover k'
    (Polynomial.C a * Polynomial.X ^ n₀) (zz.map (laumonFamilyPr₁ k'))
  have hirr₁ : ∀ (K' : Type) [Field K'] [IsAlgClosed K'] [Algebra E K']
      (W : Submodule K' (Fin m → K')),
      (∀ g, ∀ w ∈ W, (characterTwist (σ.comp (hz ▸ (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
          (zz.map (laumonFamilyPr₁ k'))).toMonoidHom))
        (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
          (Polynomial.C a * Polynomial.X ^ n₀)
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) (zz.map (laumonFamilyPr₁ k'))
          p₁) g).val.map (algebraMap E K') *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun K' _ _ _ => (forall_eq_bot_or_eq_top_characterTwist_iff _ _ K').2
      (hst k' (zz.map (laumonFamilyPr₁ k')) hz K')
  have hτirr := hL6 B ℓ k' p E b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom)
    (Stacks.FourierDeligne.traceChar_ne_one ψ k' hψ) hζ n₀ a hS hX' zz pz _ hσ₁ p₁ hirr₁ V' U'
    jV' jU g' jg' hjV' hpb xV ρ hρ φ ψ₀ N' hφψ hψφ τ P Q hPQ hα hτ hQP
  -- a real partner (the dual family twisted by an unramified character), and Weil II 1.5.1
  obtain ⟨r', τ', hτ', hreal⟩ := hN₃ n₀ (by omega) hpn₀ k' a ha hS hX' zz hz pz hσ₁ hσ₂ V' U' jV' jU
    g' jg' fV hjV' hfV hpb hlis₂ xV ρ hρ φ ψ₀ N' hφψ hψφ τ P Q hPQ hα hτ hQP
  have := hconn (AlgebraicClosure k')
  obtain ⟨β', -, hβ'⟩ := exists_norm_eq_pow_of_isIotaRealizable_curve B V' ℓ fV jfV
    (AlgebraicClosure k') p n' hcard' hℓp xV E b τ hτc τ' hτ' ι' hreal hτirr
  refine ⟨β' ^ residueDegree fV v, fun z hz' => ?_⟩
  -- the fibre characteristic polynomial is that of `τ(F_v)`
  let vc : closedPoints V'.1 := ⟨v, hvcl⟩
  have : Finite (V'.1.residueField v) := finite_residueField fV v hvcl
  let : Fintype (V'.1.residueField v) := Fintype.ofFinite _
  have : CharP (V'.1.residueField v) p := charP_of_injective_ringHom hbij.injective p
  have hcardv : Fintype.card (V'.1.residueField v) = p ^ (n' * residueDegree fV v) := by
    rw [← Nat.card_eq_fintype_card, natCard_residueField_eq_pow_residueDegree fV v, hcard',
      pow_mul]
  have hcharτ := charpoly_rationalStalkFrobenius_eq_restrictScalarsRep_family B V' xV _ ρ hρ φ ψ₀ N'
    hφψ hψφ E (algebraMap_conjIntegralSubring_algebraMap _ _) b fV τ P Q hPQ hα hτ hQP vc
  have := finite_rationalStalkLeft_of_isogeny B V' xV _ ρ hρ φ ψ₀ N' hφψ hψφ
    (geometricPointAt V'.1 v)
  refine coefficientHigherDirectImageStalkLinearInput B ℓ k' U' V' g' jg' fV vc
    (AlgebraicClosure (V'.1.residueField v)) p (n' * residueDegree fV v) hcardv _ ?_
  intro Y _ i fY _ _ _ hpbY jY hY
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  obtain ⟨_, heqb⟩ := hY (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (laumonFourierFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom)
      n₀ a zz pz _ hσ₁)) 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have heqc := hfib B U ℓ k e x E b σ ψ n₀ k' a hS hX' zz hz pz hσ₁ V' U' jV' jU g' hjV' hpb v
    Y i fY hpbY jY (AlgebraicClosure (V'.1.residueField v)) p (n' * residueDegree fV v) hcardv c
    hbij hvX hX' x' hx' p₀ hτ₀ j' kbar' p n' hcard'
  rw [← hcharτ.symm.trans (heqb.trans heqc)] at hz'
  exact hβ' vc z hz'

end Stacks.EtaleCohomology

end
