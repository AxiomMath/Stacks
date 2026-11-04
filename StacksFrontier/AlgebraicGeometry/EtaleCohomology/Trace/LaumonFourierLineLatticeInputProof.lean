module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssemblyLeavesGeneric
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLatticeModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LatticeModelSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModelConjugate

/-!
# The lattice comparison of Laumon's Fourier family

This file proves `Stacks.EtaleCohomology.LaumonFourierLineLatticeInput`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): there are finitely many constructible
sheaves `Q_o` killed by `ℓ` on the model `Spec k[a][x][t]` such that, for every finite extension
`k'` of `k` and every `a₀ ∈ k'`, the level zero of the flat model of the Fourier family at
`(k', a₀)` lies in the closure under extensions and summands of the pullbacks of the `Q_o` along
`a ↦ a₀`.

The model representation is `ρ₀ = Res_b(pr₁^*σ ⊗ ψ(-χ_{a xⁿ + x t}))` on `π₁(Spec k[a][x][t], w̄)`,
`ρₘ` its integral model, and the `Q_o` are the sheaves of the simple subquotients of `L / ℓ L`,
`L` the lattice of `ρₘ` (`Stacks.EtaleCohomology.latticeModelSheaf`). At `(k', a₀)`, with
`φ = φ_t ∘ (a ↦ a₀)_* : π₁(𝔸²_{k'}, z̄) → π₁(model, w̄)`:

* the family representation `Res_b(pr₁^*σ₁ ⊗ ψ'(-χ_{a₀ xⁿ + x t}))`, `ψ' = ψ ∘ Tr`, is conjugate
  to `ρ₀ ∘ φ` (the routes to `U` are inner conjugate,
  `Stacks.EtaleCohomology.exists_conj_laumonModelPr₁`, and the characters agree,
  `Stacks.EtaleCohomology.artinSchreierCharacter_laumonModel`), hence so are the integral models;
* with `π = pr₁_*` on the model, `π' = pr₁_*` on the plane over `k'` (surjective) and
  `ι = γ (π₁(𝔸¹_{k'}) → π₁(U)) γ⁻¹` (normal image), `π ∘ φ = ι ∘ π'`; on the kernel `N` of the
  Artin–Schreier character of the model `ρₘ` only depends on `π`; and `[π₁(𝔸²_{k'}) : φ⁻¹ N]`
  divides `#k = pⁿ`, prime to `ℓ`;
* so the constituents of `ℤ_ℓ^r / ℓ` under the family are summands of the restrictions of the
  simple subquotients of `L / ℓ L`
  (`Stacks.EtaleCohomology.hasConstituentsIn_latticeModule_restrict`: Clifford and
  Brauer–Nesbitt), and the closure statement follows
  (`Stacks.EtaleCohomology.isExtensionSummandClosure_representationLAdicSheaf_levelZero`).

## Main results

* `Stacks.EtaleCohomology.laumonFourierLineLatticeInput`.
* `Stacks.EtaleCohomology.laumonFourierLineLisseFibreInput`: the generic lisse locus of the family.
* `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves''`:
  `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves'` with the lattice comparison
  discharged.

## Implementation notes

The cohomology groups in the statement of
`Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves''` are those of
`Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves'`, defined in the standard model
`HasDerivedCategory.standard` of the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

/-- **The lattice comparison of Laumon's Fourier family**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). -/
theorem laumonFourierLineLatticeInput : LaumonFourierLineLatticeInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ hef j kbar _ _ _ _ p q _ _ hcard hℓp x E _ _ _
    d b m σ hσ K _ _ _ hirr hstab hζ ι' β hV hpure ψ hψ n hS₀
  classical
  -- the model
  let R := Polynomial (Polynomial (Polynomial k))
  let Xm := Stacks.ArtinSchreier.specObject R B hS₀
  let pUm : Spec (.of R) ⟶ U.1 := laumonModelPr₁ k ≫ inv e
  let wm : GeometricPoint (Spec (.of R)) := (x.map e).map
    (Spec.map (CommRingCat.ofHom ((mapRingHom (evalRingHom (0 : k))).comp
      (evalRingHom (0 : Polynomial (Polynomial k))))))
  obtain ⟨t₀⟩ := nonempty_finiteEtaleFiberFunctorIso (x := x) (x' := wm.map pUm)
  let π := (etaleFundamentalGroupBasePointHom t₀).comp (etaleFundamentalGroupMap pUm wm)
  obtain ⟨pm⟩ := nonempty_finiteEtaleFiberFunctor_cover k (laumonModelKernel k n) wm
  let χm := artinSchreierCharacter k R (laumonModelKernel k n) ψ wm pm
  let ρ₀ := characterTwist (σ.comp π.toMonoidHom) χm
  have hρ₀ : Continuous (restrictScalarsRep b ρ₀) :=
    continuous_restrictScalarsRep_characterTwist_artinSchreierCharacter k R _ b ψ wm pm _
      (hσ.comp π.continuous)
  have := compactSpace_etaleFundamentalGroup (Spec (.of R)) wm
  let ρm := integralModel (restrictScalarsRep b ρ₀) hρ₀
  have hρm : Continuous ρm := continuous_integralModel _ hρ₀
  refine ⟨LatticeModelIndex ρm, Fintype.ofFinite _, latticeModelSheaf B Xm wm ρm hρm,
    fun o => isBigSiteConstructibleEtaleModule_latticeModelSheaf B Xm wm ρm hρm o,
    fun o => nsmul_id_latticeModelSheaf_eq_zero B Xm wm ρm hρm o, ?_⟩
  intro k' _ _ _ a hS z hz pz hσ₁
  -- the family at `(k', a₀)`
  let fm := laumonParamPlaneHom k k' B a hS hS₀
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (x := wm) (x' := z.map fm.hom)
  let φ := (etaleFundamentalGroupBasePointHom t).comp (etaleFundamentalGroupMap fm.hom z)
  let ψ' := ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom
  let ι₀ := hz ▸ (etaleFundamentalGroupMap
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
      (z.map (laumonFamilyPr₁ k'))).toMonoidHom
  let σ₁ := σ.comp ι₀
  let ρfam := laumonFourierFamilyRep k' ψ' n a z pz σ₁
  have hρfam : Continuous (restrictScalarsRep b ρfam) :=
    continuous_restrictScalarsRep_laumonFourierFamilyRep k' b ψ' n a z pz σ₁ hσ₁
  have := compactSpace_etaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z
  let ρf := integralModel (restrictScalarsRep b ρfam) hρfam
  have hρf : Continuous ρf := continuous_integralModel _ hρfam
  -- the two routes to `U`, and the characters
  obtain ⟨γ, hγ⟩ := exists_conj_laumonModelPr₁ k k' a e z hz wm t₀ t
  have hσc : ∀ g, (σ.comp π.toMonoidHom) (φ g) =
      σ γ * (σ₁.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom) g *
        (σ γ)⁻¹ := fun g => by
    show σ (π (φ g)) = _
    rw [show π (φ g) = _ from hγ g, map_mul, map_mul, map_inv]
    rfl
  have hχ : ∀ g, χm (φ g) = artinSchreierCharacter k' (Polynomial (Polynomial k'))
      (laumonFourierKernel k' n a) ψ' z pz g := fun g =>
    (artinSchreierCharacter_laumonModel k k' a n ψ z pz wm pm t g).symm
  have hconj : ∀ g, ρ₀ (φ g) = σ γ * ρfam g * (σ γ)⁻¹ :=
    characterTwist_comp_eq_conj _ _ _ _ φ.toMonoidHom (σ γ) hσc hχ
  obtain ⟨Q, hQ⟩ := exists_conj_integralModel_comp (restrictScalarsRep b ρ₀) hρ₀
    (restrictScalarsRep b ρfam) hρfam φ.toMonoidHom _
    (restrictScalarsRep_comp_eq_conj b ρ₀ ρfam φ.toMonoidHom (σ γ) hconj)
  -- the kernel of the model character
  let N := ((torsorCover k R (laumonModelKernel k n)).character wm pm).ker
  have : N.Normal := MonoidHom.normal_ker _
  have hN : ∀ g ∈ N, ρ₀ g = σ (π g) := fun g hg => by
    have h1 : χm g = 1 := by
      show ψ.toMonoidHom.toHomUnits
        (((torsorCover k R (laumonModelKernel k n)).character wm pm)⁻¹ g) = 1
      rw [MonoidHom.inv_apply, MonoidHom.mem_ker.1 hg, inv_one, map_one]
    show σ (π g) * Units.map (Matrix.scalar (Fin m) : E →+* Matrix (Fin m) (Fin m) E).toMonoidHom
      (χm g) = σ (π g)
    rw [h1, map_one, mul_one]
  have hfac : ∀ n₁ ∈ N, ∀ n₂ ∈ N, π.toMonoidHom n₁ = π.toMonoidHom n₂ → ρm n₁ = ρm n₂ := by
    intro n₁ h₁ n₂ h₂ he
    refine integralModel_eq_of_eq _ hρ₀ ?_
    show Units.map (restrictScalarsMonoidHom b m) (ρ₀ n₁) =
      Units.map (restrictScalarsMonoidHom b m) (ρ₀ n₂)
    rw [hN n₁ h₁, hN n₂ h₂]
    exact congrArg (fun g => Units.map (restrictScalarsMonoidHom b m) (σ g)) he
  -- the normal image
  let ι := (MulAut.conj γ).toMonoidHom.comp ι₀
  have : ι₀.range.Normal :=
    normal_range_laumonLineFieldExtension k k' f e hef (z.map (laumonFamilyPr₁ k')) hz
  have : ι.range.Normal := by
    rw [MonoidHom.range_comp]
    exact Subgroup.Normal.map inferInstance _ (MulAut.conj γ).surjective
  have hcomm : ∀ g, π.toMonoidHom (φ.toMonoidHom g) =
      ι ((etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom g) := fun g => hγ g
  -- the index
  have hp : p.Prime := Fact.out
  have hdvd : (N.comap φ.toMonoidHom).index ∣ p ^ q := by
    rw [MonoidHom.comap_ker, Subgroup.index_ker, ← hcard, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have : (N.comap φ.toMonoidHom).FiniteIndex := ⟨by rw [hi]; exact pow_ne_zero _ hp.ne_zero⟩
  have hidx : ((N.comap φ.toMonoidHom).index : ZMod ℓ) ≠ 0 := by
    rw [hi, Nat.cast_pow]
    refine pow_ne_zero _ fun h0 => hℓp ?_
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact (Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h0
  -- Clifford and Brauer–Nesbitt
  have hcon := hasConstituentsIn_latticeModule_restrict ρm ρf φ.toMonoidHom Q hQ π.toMonoidHom
    (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom
    (surjective_etaleFundamentalGroupMap_laumonFamilyPr₁ k' z) ι hcomm N hfac hidx (0 + 1)
  exact isExtensionSummandClosure_representationLAdicSheaf_levelZero B fm z t ρm hρm ρf hρf hcon

/-- **The Fourier family is lisse generically on the `(a, t)`-plane and on the special lines**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), from the lattice comparison. -/
theorem laumonFourierLineLisseFibreInput : LaumonFourierLineLisseFibreInput.{u} :=
  laumonFourierLineLisseFibreInput_of_lattice laumonFourierLineLatticeInput

section WeightBound

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) from the leaf inputs, with the lattice
comparison proved.**
Let `k` be a finite field with `q = p ^ m` elements, `k̄` an algebraic closure, `ℓ ≠ p` a prime,
`X` connected and separated of finite type over `k` with a compactification `j`, and
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` continuous, satisfying the conclusions of Deligne's conjecture along
every embedding `ι : ℚ_ℓ → ℂ`. Then for every `i` the eigenvalues of `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` (finite dimensional) are algebraic numbers of absolute value `q ^ (w / 2)`
along `ι` with `w ∈ ℤ`, `w ≤ i`; and if `X` is smooth and proper over `k`, then `w = i`.

This is `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves'` with its input
`Stacks.EtaleCohomology.LaumonFourierLineLatticeInput` discharged by
`Stacks.EtaleCohomology.laumonFourierLineLatticeInput`. -/
theorem LAdicSheaf.weightBound_of_leaves''
    -- L7
    (hL6 : LaumonFourierLineAbsIrrInput.{u})
    -- L8
    (hH2 : LaumonFamilyFlatLevelZeroVanishingInput'.{u})
    -- relative purity
    (hcls : Purity.PurityClassMapStalkIsoInput.{u})
    -- Poincaré duality
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K], ProperCurveRelativeDualityInput ℓ K)
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ)
    (hD : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) :
    (∀ (i : ℤ) (ι : ℚ_[ℓ] →+* ℂ),
      haveI : FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
          (LAdicSheaf.representationSheaf B X x ρ hρ) i) :=
        LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q
          hcard hℓ X f j _ i
      IsCharpolyMixedOfWeightLE (p ^ q) ι i
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom) ∧
    (IsProper f → Smooth f → ∀ (i : ℤ) (ι : ℚ_[ℓ] →+* ℂ),
      haveI : FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
          (LAdicSheaf.representationSheaf B X x ρ hρ) i) :=
        LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q
          hcard hℓ X f j _ i
      IsCharpolyPureOfWeight (p ^ q) ι i
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom) :=
  LAdicSheaf.weightBound_of_leaves' B ℓ hL6 laumonFourierLineLatticeInput hH2 hcls he kbar p q
    hcard hℓ X f j x ρ hρ hD

end WeightBound

end Stacks.EtaleCohomology

end
