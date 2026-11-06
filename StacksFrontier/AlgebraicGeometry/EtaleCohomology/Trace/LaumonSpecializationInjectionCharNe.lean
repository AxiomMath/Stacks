module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonSpecializationInjectionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyNoPunctualSectionsCharNe

/-!
# The specialization injection of Laumon's degeneration from (H2) for `ℓ ≠ char k'`

The specialization injections
`Stacks.EtaleCohomology.exists_laumonSpecializationInjection_of_isogeny` and
`Stacks.EtaleCohomology.exists_laumonSpecializationInjection_of_baseChange` of Laumon's
degeneration argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) consume the
no-punctual-sections input (H2) only at their own prime `ℓ` and the finite field `k'` of
characteristic `p`, where `ℓ ≠ p` is a hypothesis. The versions here consume
`Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput'`, which asks for (H2) only for
`ℓ ≠ char k'`, and discharge that condition from `ℓ ≠ p` and `CharP k' p`.

## Main results

* `Stacks.EtaleCohomology.exists_laumonSpecializationInjection_of_isogeny'`.
* `Stacks.EtaleCohomology.exists_laumonSpecializationInjection_of_baseChange'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.SmallEtale.LAdicSheaf
open Stacks.Frobenius
open scoped Pointwise Matrix

universe u

namespace Stacks.EtaleCohomology

set_option maxHeartbeats 1000000 in
/-- **The specialization injection at the origin of Laumon's degeneration, along an isogeny, for
`ℓ ≠ char k'`** (piece P5 of `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). In the setting of
`Stacks.EtaleCohomology.exists_laumonSpecializationInjection`, let `χ : G|_V → F_V` be an
`O`-compatible morphism with `χ' : F_V → G|_V` such that `χ ≫ χ' = ℓᵃ` (e.g. the base change
morphism `G|_V → R¹pr₂'!(K|_{U'})`, inverse up to the isogeny of torsion-free models). Then there
is an injective `E`-linear map `J : H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ) → τ^{I_y}` carrying `(π_U^*) ^ {d_y}` to
`τ(φ Fr⁻¹)`. The inputs are the fibre over the origin (F0, BC) and the absence of punctual
sections (H2); the `E`-linear proper base change at the stalk is
`Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearIsoInput`. -/
public theorem exists_laumonSpecializationInjection_of_isogeny'
    (hF0 : LaumonOriginFibreCohomologyInput.{u})
    (hH2 : LaumonFamilyNoPunctualSectionsInput'.{u})
    (B : BigEtaleSite.{u}) (ℓ : ℕ)
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
    (k : Type u) [Field k] [Fintype k] (U : B.Scheme) [ConnectedSpace U.1] [IsNoetherian U.1]
    (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)
    (hℓp : ℓ ≠ p) (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ))
    (ψ : AddChar k E) (n₀ : ℕ) (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (c : k')
    (hψ : ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom ≠ 1)
    (hh : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    -- the open `V` of the `t`-line
    (V : B.Scheme) [IsNoetherian V.1] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (fV : V.1 ⟶ Spec (.of k'))
    [LocallyOfFiniteType fV] [QuasiCompact fV] [IsSeparated fV] [SmoothOfRelativeDimension 1 fV]
    (jV : CompactificationOf (Over.mk fV)) (kbar' : Type u) [Field kbar'] [Algebra k' kbar']
    [IsAlgClosure k' kbar']
    [ConnectedSpace ↥(Limits.pullback fV (Spec.map (CommRingCat.ofHom (algebraMap k' kbar'))))]
    (n' : ℕ) [CharP k' p] (hcard' : Fintype.card k' = p ^ n')
    (fW : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 ⟶ Spec (.of k'))
    [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (eW : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 ⟶ Spec (.of (Polynomial k')))
    [IsOpenImmersion eW]
    (heW : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))) = fW)
    (jW : V.1 ⟶ (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) [IsOpenImmersion jW]
    (hjW : jW ≫ fW = fV)
    -- the origin `y`
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1)
    (hy0 : y.asIdeal = Ideal.span {Polynomial.X}) (hyc : IsClosed ({y} : Set _))
    (hyV : y ∉ Set.range jW.base) (hy : jW.base (genericPoint V.1) ⤳ y) (dy : ℕ)
    (hcardy : Nat.card ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) =
      (p ^ n) ^ dy)
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
    (eA : A ≃+* (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.presheaf.stalk y)
    (hA : ∀ a : A, algebraMap A (V.1.residueField (genericPoint V.1)) a =
      (curveLocalRingToFunctionField jW hy).hom (eA a))
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (Fr : Gal(L / V.1.residueField (genericPoint V.1)))
    (hFrD :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L / V.1.residueField (genericPoint V.1)) P)
    (hFr :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    -- the sheaf `F_V` with a split `O`-compatible morphism `χ : G|_V → F_V`
    (FV : LAdicSheaf.CoefficientSheaf B V ℓ _)
    (χ : ((laumonFamilyHigherDirectImage k' B hS hL b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jg).inverseImage
        (ObjectProperty.homMk jW :
          V ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)).toLAdicSheaf ⟶
      FV.toLAdicSheaf)
    (hχ : ∀ o, (((laumonFamilyHigherDirectImage k' B hS hL b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jg).inverseImage
        (ObjectProperty.homMk jW :
          V ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)).act o).asHom ≫
          χ = χ ≫ (FV.act o).asHom)
    (χ' : FV.toLAdicSheaf ⟶ ((laumonFamilyHigherDirectImage k' B hS hL b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jg).inverseImage
        (ObjectProperty.homMk jW :
          V ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)).toLAdicSheaf)
    (a : ℕ) (hχχ' : χ ≫ χ' = (ℓ ^ a) • 𝟙 _)
    -- the representation of `F_V` (the data of `exists_restrictScalarsRep_of_isLisse`)
    (r : ℕ) (ρ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : FV.toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V _ ρ hρ)
    (ψ₀ : LAdicSheaf.representationSheaf B V _ ρ hρ ⟶ FV.toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (mτ : ℕ) (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin mτ) E)
    (Pm : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Qm : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ])
    (hPQ : Pm * Qm = 1)
    (hα : ∀ e' : E, Qm * isogenyCoefficientAlgHom B V _ FV ρ hρ φ ψ₀ N E hφψ hψφ
      (algebraMap_conjIntegralSubring_algebraMap _ _) e' * Pm =
        restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e'))
    (hτ : ∀ g, Qm * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (haveI := compactSpace_etaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
          (V.1.residueField (genericPoint V.1)) Ω).map
            (V.1.fromSpecResidueField (genericPoint V.1)))
         integralModel ρ hρ g)).val * Pm = (restrictScalarsRep b τ g).val) :
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    ∃ J : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1 →ₗ[E]
        Representation.invariants ((matrixRepresentation τ).comp
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype),
      Function.Injective J ∧
      J ∘ₗ (((restrictScalarsRepCoefficientSheaf
          B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
          f j kbar 1 E p n hcard) ^ dy) =
        ((Matrix.toLin' ((τ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹) :
          GL (Fin mτ) E) : Matrix (Fin mτ) (Fin mτ) E)).restrict
        (toLin'_mem_invariants_of_mem_normalizer τ
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
          (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
            (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD))) ∘ₗ J := by
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial k'))))
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  let W := Stacks.ArtinSchreier.specObject (Polynomial k') B hL
  let ψ' := ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom
  let G := laumonFamilyHigherDirectImage k' B hS hL b ψ' n₀ c z p₀ _ hσ₁ jg
  have hOE := algebraMap_conjIntegralSubring_algebraMap (ℓ := ℓ)
    (representationSheafConj B (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
      z (restrictScalarsRep b (laumonFamilyRep k' ψ' n₀ c z p₀ _))
      (continuous_restrictScalarsRep_laumonFamilyRep k' b ψ' n₀ c z p₀ _ hσ₁))
    (restrictScalarsScalarAlgHom b m)
  have hyf : Finite (W.1.residueField y) := finite_residueField fW y hyc
  -- (H2) no punctual sections, up to the isogeny `χ ≫ χ' = ℓ ^ a`
  let := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
  have : Nonempty V.1 := (inferInstance : IrreducibleSpace V.1).toNonempty
  obtain ⟨M, hM⟩ := hH2 B ℓ k' (ringChar.eq k' p ▸ hℓp.symm) hS hL b ψ' hψ n₀ c hh
    z p₀ _ hσ₁ jg V jW y hyV
  -- the specialization map
  obtain ⟨sp, hsp, hspF⟩ := curveSpecializationMapInput.{u} B V ℓ k' fV jV kbar' p n' hcard' hℓp
    W fW eW heW jW hjW y hyc hyV hy L Ω A eA hA P Fr hFrD hFr hyf G E hOE b FV χ hχ r ρ hρ φ ψ₀
    N hφψ hψφ mτ τ Pm Qm hPQ hα hτ (M + a) (fun n w h => by
      rw [pow_add ℓ M a, mul_smul]
      exact hM n _
        (levelUnitStalkMap_pow_smul_eq_zero_of_levelAdjunctStalkMap_eq_zero _ _ _ χ χ' a hχχ'
          n w h))
  -- the rational stalk is finite dimensional, as it embeds into `E ^ mτ`
  let := G.rationalStalkModule (geometricPointAt W.1 y) E
  have := G.rationalStalkModule_isScalarTower (geometricPointAt W.1 y) E hOE
  have : Module.Finite E (LAdicSheaf.rationalStalkLeft B W ℓ G.toLAdicSheaf
      (geometricPointAt W.1 y)) := Module.Finite.of_injective sp hsp
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B W ℓ G.toLAdicSheaf
      (geometricPointAt W.1 y)) := Module.Finite.trans E _
  -- the residue field at `y` and its embedding into `k̄`
  let : Fintype (W.1.residueField y) := Fintype.ofFinite _
  have : CharP (W.1.residueField y) p :=
    charP_of_injective_ringHom ((laumonPointRingHom (𝟙 W) y).comp Polynomial.C).injective p
  have hcardY : Fintype.card (W.1.residueField y) = p ^ (n * dy) := by
    rw [← Nat.card_eq_fintype_card, hcardy, pow_mul]
  let : Algebra k (W.1.residueField y) := laumonPointAlgebra (𝟙 W) y k
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  let ι : W.1.residueField y →ₐ[k] kbar := IsAlgClosed.lift
  let : Algebra (W.1.residueField y) kbar := ι.toRingHom.toAlgebra
  have : IsScalarTower k (W.1.residueField y) kbar :=
    IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  have : IsAlgClosure (W.1.residueField y) kbar :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := k) _⟩
  have hι : ∀ a : k, algebraMap (W.1.residueField y) kbar
      (laumonPointRingHom (𝟙 W) y (algebraMap k (Polynomial k') a)) = algebraMap k kbar a :=
    ι.commutes
  -- (Θ) proper base change at the stalk
  refine coefficientHigherDirectImageStalkLinearIsoInput B ℓ k'
    (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) W
    (laumonFamilyProjection k' B hS hL) jg fW ⟨y, hyc⟩ kbar p (n * dy) hcardY _ ?_
  intro Y _ i fY _ _ _ hpb jY hY
  obtain ⟨Θ, hΘF⟩ := hY (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ _ hσ₁) 1 E hOE
  let := ((laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ _ hσ₁).higherDirectImageShriek B ℓ
    (laumonFamilyProjection k' B hS hL) jg 1).rationalStalkModule (geometricPointAt W.1 y) E
  let := (LAdicSheaf.CoefficientSheaf.inverseImage i
    (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ _ hσ₁)).rationalCohomologyModule fY jY kbar 1 E
  -- (F0, BC) the fibre over the origin
  obtain ⟨eY, heY⟩ := hF0 B ℓ k U f e he j kbar p n hcard x E b σ hσ ψ n₀ k' c hS hL z hz p₀
    hσ₁ y hy0 dy hcardY hι Y i fY hpb jY
  let eS := eY.symm.trans Θ
  have hS' : eS.toLinearMap ∘ₗ
    ((restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
        f j kbar 1 E p n hcard) ^ dy =
      G.rationalStalkFrobenius E y hyf ∘ₗ eS.toLinearMap := by
    refine LinearMap.ext fun v => ?_
    have h1 := heY (eY.symm v)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact (congrArg Θ (eY.symm_apply_eq.2 h1.symm)).trans (LinearMap.congr_fun hΘF (eY.symm v))
  exact ⟨sp ∘ₗ eS.toLinearMap,
    injective_comp_linearEquiv_and_comp_pow sp hsp _ _ hspF _ dy eS hS'⟩

/-- **The specialization injection at the origin of Laumon's degeneration, through base change,
for `ℓ ≠ char k'`** (piece P5 of `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the specialization injection of
`Stacks.EtaleCohomology.exists_laumonSpecializationInjection_of_isogeny` for
`F_V = R¹g'_!(K|_{U'})` (`Stacks.EtaleCohomology.laumonFamilyRestrictedHigherDirectImage`), `U'`
the inverse image of `V` under `pr₂`, through the base change morphisms
`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom`. There is
an injective `E`-linear map `J : H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ) → τ^{I_y}` carrying `(π_U^*) ^ {d_y}` to
`τ(φ Fr⁻¹)`; the inputs are the fibre over the origin (F0, BC) and the absence of punctual
sections (H2). -/
public theorem exists_laumonSpecializationInjection_of_baseChange' (B : BigEtaleSite.{u}) (ℓ : ℕ)
    (hF0 : LaumonOriginFibreCohomologyInput.{u})
    (hH2 : LaumonFamilyNoPunctualSectionsInput'.{u})
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
    (k : Type u) [Field k] [Fintype k] (U : B.Scheme) [ConnectedSpace U.1] [IsNoetherian U.1]
    (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)
    (hℓp : ℓ ≠ p) (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ))
    (ψ : AddChar k E) (n₀ : ℕ) (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (c : k')
    (hψ : ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom ≠ 1)
    (hh : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    -- the open `V` of the `t`-line
    (V : B.Scheme) [IsNoetherian V.1] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (fV : V.1 ⟶ Spec (.of k'))
    [LocallyOfFiniteType fV] [QuasiCompact fV] [IsSeparated fV] [SmoothOfRelativeDimension 1 fV]
    (jV : CompactificationOf (Over.mk fV)) (kbar' : Type u) [Field kbar'] [Algebra k' kbar']
    [IsAlgClosure k' kbar']
    [ConnectedSpace ↥(Limits.pullback fV (Spec.map (CommRingCat.ofHom (algebraMap k' kbar'))))]
    (n' : ℕ) [CharP k' p] (hcard' : Fintype.card k' = p ^ n')
    (fW : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 ⟶ Spec (.of k'))
    [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (eW : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 ⟶ Spec (.of (Polynomial k')))
    [IsOpenImmersion eW]
    (heW : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))) = fW)
    (jW : V.1 ⟶ (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) [IsOpenImmersion jW]
    (hjW : jW ≫ fW = fV)
    -- the restriction `g' : U' ⟶ V` of `pr₂` to `U' = pr₂⁻¹(V)`, with a compactification
    (U' : B.Scheme) [IsNoetherian U'.1]
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V)
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
    (hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL))
      (B.inclusion.map (ObjectProperty.homMk jW : V ⟶ Stacks.ArtinSchreier.specObject
        (Polynomial k') B hL)))
    -- the origin `y`
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1)
    (hy0 : y.asIdeal = Ideal.span {Polynomial.X}) (hyc : IsClosed ({y} : Set _))
    (hyV : y ∉ Set.range jW.base) (hy : jW.base (genericPoint V.1) ⤳ y) (dy : ℕ)
    (hcardy : Nat.card ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) =
      (p ^ n) ^ dy)
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
    (eA : A ≃+* (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.presheaf.stalk y)
    (hA : ∀ a : A, algebraMap A (V.1.residueField (genericPoint V.1)) a =
      (curveLocalRingToFunctionField jW hy).hom (eA a))
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (Fr : Gal(L / V.1.residueField (genericPoint V.1)))
    (hFrD :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L / V.1.residueField (genericPoint V.1)) P)
    (hFr :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    -- the representation of `F_V` (the data of `exists_restrictScalarsRep_of_isLisse`)
    (r : ℕ) (ρ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g'
          jg').toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V _ ρ hρ)
    (ψ₀ : LAdicSheaf.representationSheaf B V _ ρ hρ ⟶
      (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g'
          jg').toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (mτ : ℕ) (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin mτ) E)
    (Pm : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Qm : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ])
    (hPQ : Pm * Qm = 1)
    (hα : ∀ e' : E, Qm * isogenyCoefficientAlgHom B V _
        (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g' jg')
        ρ hρ φ ψ₀ N E hφψ hψφ
      (algebraMap_conjIntegralSubring_algebraMap _ _) e' * Pm =
        restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e'))
    (hτ : ∀ g, Qm * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (haveI := compactSpace_etaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
          (V.1.residueField (genericPoint V.1)) Ω).map
            (V.1.fromSpecResidueField (genericPoint V.1)))
         integralModel ρ hρ g)).val * Pm = (restrictScalarsRep b τ g).val) :
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    ∃ J : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1 →ₗ[E]
        Representation.invariants ((matrixRepresentation τ).comp
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype),
      Function.Injective J ∧
      J ∘ₗ (((restrictScalarsRepCoefficientSheaf
          B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
          f j kbar 1 E p n hcard) ^ dy) =
        ((Matrix.toLin' ((τ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹) :
          GL (Fin mτ) E) : Matrix (Fin mτ) (Fin mτ) E)).restrict
        (toLin'_mem_invariants_of_mem_normalizer τ
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
          (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
            (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD))) ∘ₗ J :=
  exists_laumonSpecializationInjection_of_isogeny' hF0 hH2 B ℓ k U f e he j kbar p n hcard
    hℓp x E b σ hσ ψ n₀ k' c hψ hh hS hL z hz p₀ hσ₁ jg V fV jV kbar' n' hcard' fW eW heW jW hjW
    y hy0 hyc hyV hy dy hcardy L Ω A eA hA P Fr hFrD hFr
    (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
      (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g' jg')
    (LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom B ℓ
      (laumonFamilyProjection k' B hS hL) jg g' jg' jU _ hpb
      (laumonFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c
        z p₀ _ hσ₁) 1)
    (LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom_act B ℓ
      (laumonFamilyProjection k' B hS hL) jg g' jg' jU _ hpb
      (laumonFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c
        z p₀ _ hσ₁) 1)
    (LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeInv B ℓ
      (laumonFamilyProjection k' B hS hL) jg g' jg' jU _ hpb
      (laumonFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c
        z p₀ _ hσ₁) 1) _
    (LAdicSheaf.CoefficientSheaf.higherDirectImageShriekBaseChangeHom_comp_inv B ℓ
      (laumonFamilyProjection k' B hS hL) jg g' jg' jU _ hpb
      (laumonFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c
        z p₀ _ hσ₁) 1)
    r ρ hρ φ ψ₀ N hφψ hψφ mτ τ Pm Qm hPQ hα hτ

end Stacks.EtaleCohomology

end
