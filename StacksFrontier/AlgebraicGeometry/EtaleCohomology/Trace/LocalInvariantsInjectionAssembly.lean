module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsInjectionInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkConnectingMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsTowerLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineLineOpenCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafCompactificationIsoNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StrongMixInertiaCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTowerLevelTorsion

/-!
# The local invariants inject into `H¹_c` (Weil II 1.8), from its three geometric inputs

Let `V ⊆ W ⊆ 𝔸¹_k` be opens of the affine line over a finite field, `y ∈ W ∖ V` a closed point
and `τ : π₁(V, x̄) → GL_m(E)` with `Res_b τ` continuous. Compactify `W` (Nagata), let `Z` be the
reduced complement of `V` in `W` and `ℱₙ` the levels of `ℱ_{Res_b τ}`. The stalk of `j_* ℱₙ` at
`ȳ` embeds into `H⁰_c(W_k̄, i_* i⁻¹ j_* ℱₙ)`, whose connecting map to `H¹_c(V_k̄, ℱₙ)` is
injective because `H⁰_c(W_k̄, j_* ℱₙ) = 0` (`W` is an affine curve); changing the
compactification of `V` to the given one, these maps are compatible in `n`, with the
endomorphisms of `ℱ` and with the Frobenius. The stalks are the reductions of the inertia
invariants of the integral model of `Res_b τ`, so the inertia invariants of `τ`, through the
`b`-coordinates and the conjugation to the integral model, map injectively, `E`-linearly and
Frobenius-equivariantly into `H¹_c(V_k̄, ℱ_{Res_b τ} ⊗ ℚ_ℓ)`. This is
`Stacks.EtaleCohomology.CurveLocalInvariantsInjectionInput` from
`Stacks.EtaleCohomology.AffineCurveDirectImageCompactSupportZeroInput`,
`Stacks.EtaleCohomology.ClosedPartStalkCompactSupportInput` and
`Stacks.EtaleCohomology.CurvePointInertiaStalkInput`, a step of Weil II 1.8.4
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.

## Main results

* `Stacks.EtaleCohomology.curveLocalInvariantsInjectionInput_of_inputs`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open scoped Pointwise Matrix

universe u

namespace Stacks.EtaleCohomology

/-! ### Coordinates conjugated to the integral model -/

section Coordinates

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {d m : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) (P : GL (Fin (m * d)) ℚ_[ℓ])

/-- **`x ↦ P⁻¹ (b-coordinates of x)`**, from `E^m` to `ℚ_ℓ^{m d}`. -/
public def conjRestrictScalarsCoords : (Fin m → E) →ₗ[ℚ_[ℓ]] (Fin (m * d) → ℚ_[ℓ]) where
  toFun x := (P⁻¹ : GL (Fin (m * d)) ℚ_[ℓ]).val *ᵥ restrictScalarsCoords b x
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext p
    simp only [restrictScalarsCoords, Pi.add_apply, map_add, Finsupp.add_apply]
  map_smul' c x := by
    rw [RingHom.id_apply, ← Matrix.mulVec_smul]
    congr 1
    funext p
    simp only [restrictScalarsCoords, Pi.smul_apply, map_smul, Finsupp.smul_apply]

/-- `conjRestrictScalarsCoords b P x` is `P⁻¹` applied to the `b`-coordinates of `x`. -/
public theorem conjRestrictScalarsCoords_apply (x : Fin m → E) :
    conjRestrictScalarsCoords b P x =
      (P⁻¹ : GL (Fin (m * d)) ℚ_[ℓ]).val *ᵥ restrictScalarsCoords b x :=
  rfl

/-- The conjugated coordinates `x ↦ P⁻¹ (b-coordinates of x)` are injective. -/
public theorem injective_conjRestrictScalarsCoords :
    Function.Injective (conjRestrictScalarsCoords b P) := by
  intro x y h
  refine restrictScalarsCoords_injective b ?_
  simpa only [conjRestrictScalarsCoords_apply, Matrix.mulVec_mulVec, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.one_mulVec] using congrArg (P.val *ᵥ ·) h

/-- **The conjugated coordinates intertwine `M` with `P⁻¹ Res_b(M) P`.** -/
public theorem conjRestrictScalarsCoords_mulVec (M : Matrix (Fin m) (Fin m) E)
    (A : Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ])
    (h : (P⁻¹ : GL (Fin (m * d)) ℚ_[ℓ]).val * restrictScalarsMatrix b M * P.val = A)
    (x : Fin m → E) :
    conjRestrictScalarsCoords b P (M *ᵥ x) = A *ᵥ conjRestrictScalarsCoords b P x := by
  rw [conjRestrictScalarsCoords_apply, conjRestrictScalarsCoords_apply,
    ← restrictScalarsMatrix_mulVec_restrictScalarsCoords, ← h, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc _ P.val, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

/-- A scalar matrix acts by scalar multiplication. -/
public theorem scalar_mulVec_eq_smul (e : E) (x : Fin m → E) :
    Matrix.scalar (Fin m) e *ᵥ x = e • x := by
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

end Coordinates

/-- Two squares pasted; stated on variables. -/
private theorem square_paste {C : Type*} [Category* C] {a b c a' b' c' : C} (x : a ⟶ a')
    (s : a ⟶ b) (t : b ⟶ c) (s' : a' ⟶ b') (t' : b' ⟶ c') (y : b ⟶ b') (z : c ⟶ c')
    (h₁ : x ≫ s' = s ≫ y) (h₂ : y ≫ t' = t ≫ z) : x ≫ (s' ≫ t') = (s ≫ t) ≫ z := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

set_option maxHeartbeats 800000 in
-- one long proof assembling the three inputs over many local instances and derived categories
/-- **The local invariants inject into `H¹_c`** (Weil II 1.8, `H⁰_loc ⊆ H¹_c`), from
`H⁰_c(W_k̄, j_* G) = 0` on an affine curve, the embedding of the stalk at a closed point of the
complement into `H⁰_c(W_k̄, i_* i⁻¹ -)`, and the identification of the stalks of `j_*` of the
levels of `ℱ_{ρ₀}` with the reductions of the inertia invariants. -/
public theorem curveLocalInvariantsInjectionInput_of_inputs
    (h2 : AffineCurveDirectImageCompactSupportZeroInput.{u})
    (h3 : ClosedPartStalkCompactSupportInput.{u})
    (h46 : CurvePointInertiaStalkInput.{u}) : CurveLocalInvariantsInjectionInput.{u} := by
  intro B V ℓ _ _ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p q _ _ hcard hℓp W fW _ _ _ _ eW _
    heW jW _ hjW y hyc hyV hy L Ω _ _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ _ eA hA P _ Fr hFrD hFr E _ _ _
    d b m τ hτ
  subst hjW
  classical
  -- the geometry of `V ⊆ W ⊆ 𝔸¹_k`
  have : Nonempty V.1 := ⟨genericPoint V.1⟩
  have : Nonempty W.1 := ⟨y⟩
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : IrreducibleSpace W.1 := irreducibleSpace_of_isOpenImmersion_affineLine eW
  have : IsCurve k fW := isCurve_of_isOpenImmersion_affineLine fW eW
  have : Smooth fW := SmoothOfRelativeDimension.smooth 1 fW
  have : IsAffine W.1 := isAffine_of_isOpenImmersion_affineLine fW eW heW
  have hdimW : topologicalKrullDim W.1 ≤ 1 :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 fW).le
  have : IsFinite (closedComplementι jW ≫ fW) :=
    isFinite_closedComplementι_comp_of_irreducibleSpace fW jW hdimW
  have hij := range_eq_compl_range_closedComplementι jW
  have hyZ := mem_range_closedComplementι jW hyV
  let eR := IsLocalRing.ResidueField.mapEquiv eA
  have : Finite (W.1.residueField y) := Finite.of_equiv _ eR.toEquiv
  obtain ⟨jWb⟩ : Nonempty (CompactificationOf (Over.mk fW)) := IsCofiltered.nonempty
  obtain ⟨dy, hdy, hcardy, s, hs, hsF⟩ :=
    h3 fW jWb kbar p q hcard (closedComplementι jW) y hyZ ℤ_[ℓ]
  have hcardA : Nat.card (IsLocalRing.ResidueField A) = (p ^ q) ^ dy :=
    (Nat.card_congr eR.toEquiv).trans hcardy
  -- the integral model and the levels
  let x : GeometricPoint V.1 := (algebraicClosureGeometricPoint
    (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1))
  have := compactSpace_etaleFundamentalGroup V.1 x
  let ρ₀ := integralModel (restrictScalarsRep b τ) hτ
  have hρ₀ : Continuous ρ₀ := continuous_integralModel (restrictScalarsRep b τ) hτ
  obtain ⟨ε, hεi, hεs, hεt, hεM, hεF, hεI⟩ := h46 B V ℓ k (jW ≫ fW) kbar p hℓp W fW eW
    heW jW rfl y hyc hyV hy L Ω A eA hA P Fr hFr (m * d) ρ₀ hρ₀
  let F := restrictScalarsRepCoefficientSheaf B V x b τ hτ
  let ℱ := F.toLAdicSheaf
  let Seq := (SmallEtale.sheafEquiv B V.1 V.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor
  let G : ℕ → EtaleModules.{u, 0} ℤ_[ℓ] V.1 := fun N => Seq.obj (LAdicSheaf.padicLevel B V ℓ ℱ N)
  let fib : Sheaf W.1.smallEtaleTopology (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤ ModuleCat.{u + 1} ℤ_[ℓ] :=
    (Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt W.1 y).hom).sheafFiber
  let DW := etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jW
  let S : ℕ → ModuleCat.{u + 1} ℤ_[ℓ] := fun N => fib.obj (DW.obj (G N))
  let C := LAdicSheaf.geometricCompactlySupportedCohomologySystem B V ℓ (jW ≫ fW) j kbar ℱ 1
  let lW := jWb.restrictOpen jW
  have hpos : ∀ N : ℕ, 0 < ℓ ^ (N + 1) := fun N => pow_pos (Fact.out : ℓ.Prime).pos _
  have hkill : ∀ N : ℕ, ℓ ^ (N + 1) • 𝟙 (G N) = 0 := fun N =>
    LAdicSheaf.pow_nsmul_id_padicTower_obj B ℓ ℱ N
  let cI : ∀ N : ℕ, (compactSupportSheafCohomology ℤ_[ℓ] (jW ≫ fW) lW kbar 1).obj (G N) ≅
      (compactSupportSheafCohomology ℤ_[ℓ] (jW ≫ fW) j kbar 1).obj (G N) := fun N =>
    compactSupportSheafCohomologyCompactificationIso ℤ_[ℓ] (jW ≫ fW) kbar lW j (G N) _ (hpos N)
      (hkill N) 1
  let SC : ∀ N : ℕ, S N ⟶ (compactSupportSheafCohomology ℤ_[ℓ] (jW ≫ fW) lW kbar 1).obj (G N) :=
    fun N => stalkConnecting ℤ_[ℓ] fW jWb kbar p q hcard jW (closedComplementι jW) hij y s (G N)
  let Ψ : ∀ N : ℕ, S N ⟶ C.obj (op N) := fun N => SC N ≫ (cI N).hom
  let t : ∀ N : ℕ, S (N + 1) ⟶ S N := fun N =>
    fib.map (DW.map (Seq.map (LAdicSheaf.padicTransition B V ℓ ℱ N)))
  -- `H⁰_c(W_k̄, j_* ℱₙ) = 0`, from the levels with `ℤ/ℓⁿ⁺¹`-coefficients
  have hzero : ∀ N : ℕ, IsZero ((compactSupportSheafCohomology ℤ_[ℓ] fW jWb kbar 0).obj
      (DW.obj (G N))) := by
    intro N
    have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    let ρ := PadicInt.toZModPow (p := ℓ) (N + 1)
    let M := (SmallEtale.sheafEquiv B V.1 V.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (N + 1))))).functor.obj
      (ℱ.level N)
    have hM : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (N + 1)))
        V.1.smallEtaleTopology M :=
      (isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B V (ZMod (ℓ ^ (N + 1)))
        (ℱ.level N)).2 (isFiniteTypeLocallyConstant_representationLevelSheaf B V x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V x) ρ₀ hρ₀ (N + 1))
    have h := h2 fW jWb kbar jW (ZMod (ℓ ^ (N + 1))) M hM
    let e₁ : DW.obj (G N) ≅ (etaleModuleRestrictScalars ρ W.1).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (N + 1))) jW).obj M) :=
      DW.mapIso ((sheafEquivRestrictScalarsIso B V.1 V.2 ρ).app (ℱ.level N)).symm
    let K := (sheafSingleComplex (ZMod (ℓ ^ (N + 1)))).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (N + 1))) jW).obj M)
    let e₂ : (sheafSingleComplex ℤ_[ℓ]).obj ((etaleModuleRestrictScalars ρ W.1).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (N + 1))) jW).obj M)) ≅
        (etaleModuleRestrictScalars ρ W.1).mapCochainComplexPlus.obj K :=
      ObjectProperty.isoMk _ ((HomologicalComplex.singleMapHomologicalComplex
        (etaleModuleRestrictScalars ρ W.1) (ComplexShape.up ℤ) 0).app _).symm
    refine IsZero.of_iso ?_ ((compactSupportSheafCohomology ℤ_[ℓ] fW jWb kbar 0).mapIso e₁)
    refine IsZero.of_iso ((ModuleCat.restrictScalars.{u + 1} ρ).map_isZero h) ?_
    exact (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) 0).mapIso
        ((compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jWb kbar).mapIso e₂) ≪≫
      (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ fW jWb kbar K 0).symm
  -- the levels `Ψₙ : (j_* ℱₙ)_ȳ ⟶ H¹_c(V_k̄, ℱₙ)`
  have hΨi : ∀ N, Function.Injective (Ψ N).hom := by
    intro N
    change Function.Injective (SC N ≫ (cI N).hom).hom
    rw [ModuleCat.hom_comp, LinearMap.coe_comp]
    exact ((ModuleCat.mono_iff_injective (cI N).hom).1 inferInstance).comp
      (injective_stalkConnecting ℤ_[ℓ] fW jWb kbar p q hcard jW (closedComplementι jW) hij y s
        (G N) (hs _) (hzero N))
  have hnat : ∀ {N N' : ℕ} (g : G N ⟶ G N'), fib.map (DW.map g) ≫ Ψ N' =
      Ψ N ≫ (compactSupportSheafCohomology ℤ_[ℓ] (jW ≫ fW) j kbar 1).map g := fun {N N'} g =>
    square_paste _ _ _ _ _ _ _
      (stalkConnecting_naturality ℤ_[ℓ] fW jWb kbar p q hcard jW (closedComplementι jW) hij y s g)
      (compactSupportSheafCohomologyCompactificationIso_hom_naturality ℤ_[ℓ] (jW ≫ fW) kbar lW j g
        _ (hpos N) (hkill N) _ (hpos N') (hkill N') 1)
  have hΨ : ∀ N, t N ≫ Ψ N = Ψ (N + 1) ≫ C.map (homOfLE (N.le_add_right 1)).op := fun N => by
    rw [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ]
    exact hnat _
  -- the integral inertia invariants into the limit
  let Inr := Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P
  let ρq : EtaleFundamentalGroup V.1 x → Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ] := fun g =>
    (ρ₀ g).val.map (algebraMap ℤ_[ℓ] ℚ_[ℓ])
  let Irat : Submodule ℚ_[ℓ] (Fin (m * d) → ℚ_[ℓ]) :=
    { carrier := {z | ∀ σ ∈ Inr, ρq σ *ᵥ z = z}
      add_mem' := fun {a b} ha hb σ hσ => by
        change ρq σ *ᵥ (a + b) = a + b
        rw [Matrix.mulVec_add, ha σ hσ, hb σ hσ]
      zero_mem' := fun σ _ => Matrix.mulVec_zero _
      smul_mem' := fun c z hz σ hσ => by
        change ρq σ *ᵥ (c • z) = c • z
        rw [Matrix.mulVec_smul, hz σ hσ] }
  have hI : ∀ v ∈ integralSubmodule Irat, ∀ N,
      (fun i => PadicInt.toZModPow (N + 1) (v i)) ∈ Set.range (ε N) := fun v hv =>
    hεI v fun σ hσ => funext fun i => PadicInt.ext <|
      (RingHom.map_mulVec (algebraMap ℤ_[ℓ] ℚ_[ℓ]) (ρ₀ σ).val v i).trans (congrFun (hv σ hσ) i)
  let Jint := towerLimitLift ε hεi hεs (integralSubmodule Irat) hI t hεt C Ψ hΨ
  have hJint : Function.Injective Jint :=
    injective_towerLimitLift ε hεi hεs (integralSubmodule Irat) hI t hεt C Ψ hΨ hΨi
  let H := LAdicSheaf.geometricCompactlySupportedCohomology B V ℓ (jW ≫ fW) j kbar ℱ 1
  let Jrat := rationalLift H Jint
  -- the inertia invariants of `τ` to the rational inertia invariants of the integral model
  let Pc := representationSheafConj B V x (restrictScalarsRep b τ) hτ
  have hconj : ∀ g, (Pc⁻¹ : GL (Fin (m * d)) ℚ_[ℓ]).val * restrictScalarsMatrix b (τ g).val *
      Pc.val = ρq g := by
    intro g
    have h := congrArg Units.val (map_integralModel (restrictScalarsRep b τ) hτ g)
    simp only [Units.val_mul, restrictScalarsRep_val] at h
    exact h.symm
  let inv := Representation.invariants ((matrixRepresentation τ).comp Inr.subtype)
  have hΦ : ∀ z : inv, conjRestrictScalarsCoords b Pc (z : Fin m → E) ∈ Irat := by
    intro z σ hσ
    rw [← conjRestrictScalarsCoords_mulVec b Pc _ _ (hconj σ)]
    congr 1
    exact (Representation.mem_invariants _ _).1 z.2 ⟨σ, hσ⟩
  let Φ : inv →ₗ[ℚ_[ℓ]] Irat := LinearMap.codRestrict Irat
    ((conjRestrictScalarsCoords b Pc).comp (inv.subtype.restrictScalars ℚ_[ℓ])) hΦ
  have hΦi : Function.Injective Φ := fun z z' h =>
    Subtype.ext (injective_conjRestrictScalarsCoords b Pc (congrArg Subtype.val h))
  let Jl : inv →ₗ[ℚ_[ℓ]] LAdicSheaf.rationalGeometricCompactlySupportedCohomology B V ℓ (jW ≫ fW) j
      kbar ℱ 1 := Jrat ∘ₗ Φ
  -- `E`-linearity, from the action of the integral part `O` of `E`
  let O := conjIntegralSubring Pc (restrictScalarsScalarAlgHom b m)
  have hO : ∀ (o : O) (z : inv), Jl (algebraMap O E o • z) =
      F.rationalIntegralRingHom (jW ≫ fW) j kbar 1 o (Jl z) := by
    intro o z
    let Mo := conjIntegralLift Pc (restrictScalarsScalarAlgHom b m) o
    have hΦo : ((Φ (algebraMap O E o • z) : Irat) : Fin (m * d) → ℚ_[ℓ]) =
        Mo.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) *ᵥ ((Φ z : Irat) : Fin (m * d) → ℚ_[ℓ]) := by
      change conjRestrictScalarsCoords b Pc ((algebraMap O E o) • (z : Fin m → E)) = _
      rw [← scalar_mulVec_eq_smul]
      exact conjRestrictScalarsCoords_mulVec b Pc _ _
        (mapMatrix_conjIntegralLift Pc (restrictScalarsScalarAlgHom b m) o).symm _
    have hz : Mo.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) *ᵥ ((Φ z : Irat) : Fin (m * d) → ℚ_[ℓ]) ∈ Irat :=
      hΦo ▸ (Φ (algebraMap O E o • z)).2
    have hM : ∀ g, Mo * (ρ₀ g).val = (ρ₀ g).val * Mo := fun g =>
      conjIntegralLift_mul_integralModel B V x (restrictScalarsRep b τ) hτ
        (restrictScalarsScalarAlgHom b m) (restrictScalarsScalarAlgHom_commute b τ) o g
    change Jrat (Φ (algebraMap O E o • z)) = _
    rw [show Φ (algebraMap O E o • z) = ⟨_, hz⟩ from Subtype.ext hΦo]
    refine (rationalLift_mulVec H Jint Mo
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap (jW ≫ fW) j kbar (F.act o).asHom 1)
      (fun v hv => ?_) (Φ z) hz).trans ?_
    swap
    · rfl
    exact towerLimitLift_mulVec ε hεi hεs _ hI t hεt C Ψ hΨ Mo
      (fun N => fib.map (DW.map (Seq.map (LAdicSheaf.padicLevelMap (F.act o).asHom N))))
      (fun N w => hεM Mo hM N w)
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap (jW ≫ fW) j kbar
        (F.act o).asHom 1).hom
      (fun N => ((geometricCompactSupportPadicCohomology B V ℓ (jW ≫ fW) j kbar 1).map
        (LAdicSheaf.padicLevelMap (F.act o).asHom N)).hom)
      (fun N y' => congrArg (fun φ => φ.hom y')
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap_π (jW ≫ fW) j kbar
          (F.act o).asHom 1 N))
      (fun N w => congrArg (fun φ => φ.hom w)
        (hnat (Seq.map (LAdicSheaf.padicLevelMap (F.act o).asHom N)))) v hv
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have hE : ∀ (e : E) (z : inv), Jl (e • z) = F.rationalRingHom (jW ≫ fW) j kbar 1 E e (Jl z) := by
    intro e z
    obtain ⟨⟨o, ⟨_, k', rfl⟩⟩, he⟩ := IsLocalization.surj (Submonoid.powers (ℓ : O)) e
    have hN : algebraMap O E ((ℓ : O) ^ k') = ((ℓ ^ k' : ℕ) : E) := by
      rw [map_pow, map_natCast, Nat.cast_pow]
    have hR : F.rationalRingHom (jW ≫ fW) j kbar 1 E (algebraMap O E ((ℓ : O) ^ k')) =
        ((ℓ ^ k' : ℕ) : Module.End ℚ_[ℓ] _) := by
      rw [hN, map_natCast]
    apply smul_right_injective _ (show ((ℓ ^ k' : ℕ) : ℚ_[ℓ]) ≠ 0 from
      Nat.cast_ne_zero.2 (pow_ne_zero _ hℓ0))
    simp only [Nat.cast_smul_eq_nsmul]
    calc (ℓ ^ k') • Jl (e • z) = Jl (((ℓ ^ k' : ℕ) : E) • e • z) := by
          rw [Nat.cast_smul_eq_nsmul, map_nsmul]
      _ = Jl (algebraMap O E o • z) := by
          rw [smul_smul, mul_comm, ← hN, he]
      _ = F.rationalIntegralRingHom (jW ≫ fW) j kbar 1 o (Jl z) := hO o z
      _ = F.rationalRingHom (jW ≫ fW) j kbar 1 E (algebraMap O E o) (Jl z) := by
          rw [F.rationalRingHom_algebraMap_apply]
      _ = F.rationalRingHom (jW ≫ fW) j kbar 1 E e
            (F.rationalRingHom (jW ≫ fW) j kbar 1 E (algebraMap O E ((ℓ : O) ^ k')) (Jl z)) := by
          rw [← he, map_mul, Module.End.mul_apply]
      _ = (ℓ ^ k') • F.rationalRingHom (jW ≫ fW) j kbar 1 E e (Jl z) := by
          rw [hR, Module.End.natCast_apply, map_nsmul]
  -- the Frobenius
  let g₀ := (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹
  let Frob := LAdicSheaf.geometricCompactlySupportedFrobenius B V ℓ (jW ≫ fW) j kbar p q hcard ℱ 1
  let frobN : ∀ N : ℕ, C.obj (op N) ⟶ C.obj (op N) := fun N =>
    (compactSupportSheafFrobenius ℤ_[ℓ] (jW ≫ fW) j kbar p q hcard 1).app (G N)
  have hπ : ∀ N (y' : (limit C : ModuleCat.{u + 1} ℤ_[ℓ])),
      (limit.π C (op N)).hom ((Frob.hom ^ dy) y') =
        ((frobN N).hom ^ dy) ((limit.π C (op N)).hom y') := by
    intro N y'
    have h1 : (frobN N).hom ∘ₗ (limit.π C (op N)).hom = (limit.π C (op N)).hom ∘ₗ Frob.hom :=
      (congrArg ModuleCat.Hom.hom (LAdicSheaf.geometricCompactlySupportedFrobenius_π B V ℓ
        (jW ≫ fW) j kbar p q hcard ℱ 1 N)).symm
    exact (LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h1 dy) y').symm
  have hac : ∀ N (w : S N), (Ψ N).hom ((Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ])
      W.1 y (DW.obj (G N))).hom w) = ((frobN N).hom ^ dy) ((Ψ N).hom w) := by
    intro N w
    have h1 := stalkConnecting_frobenius ℤ_[ℓ] fW jWb kbar p q hcard jW (closedComplementι jW) hij y
      s (G N) dy (hsF _)
    have h2 : ((compactSupportSheafFrobenius ℤ_[ℓ] (jW ≫ fW) j kbar p q hcard 1).app (G N)).hom ∘ₗ
        (cI N).hom.hom = (cI N).hom.hom ∘ₗ
          ((compactSupportSheafFrobenius ℤ_[ℓ] (jW ≫ fW) lW kbar p q hcard 1).app (G N)).hom :=
      (congrArg ModuleCat.Hom.hom (compactSupportSheafCohomologyCompactificationIso_hom_frobenius
        ℤ_[ℓ] (jW ≫ fW) kbar lW j p q hcard (G N) _ (hpos N) (hkill N) 1)).symm
    have h3 := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h2 dy)
      ((SC N).hom w)
    change (cI N).hom.hom ((SC N).hom _) = _
    exact (congrArg (cI N).hom.hom (LinearMap.congr_fun h1 w)).trans h3.symm
  have hFrob : ∀ (z : Irat) (hz : ρq g₀ *ᵥ (z : Fin (m * d) → ℚ_[ℓ]) ∈ Irat),
      Jrat ⟨_, hz⟩ = ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (ModuleCat.ofHom (Frob.hom ^ dy))).hom (Jrat z) := fun z hz =>
    rationalLift_mulVec H Jint (ρ₀ g₀).val (ModuleCat.ofHom (Frob.hom ^ dy))
      (fun v hv => towerLimitLift_mulVec ε hεi hεs _ hI t hεt C Ψ hΨ (ρ₀ g₀).val
        (fun N => Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) W.1 y (DW.obj (G N)))
        (fun N w => hεF N w) (Frob.hom ^ dy) (fun N => (frobN N).hom ^ dy) hπ hac v hv) z hz
  -- the `E`-linear injection
  let := F.rationalCohomologyModule (jW ≫ fW) j kbar 1 E
  let J : inv →ₗ[E] LAdicSheaf.rationalGeometricCompactlySupportedCohomology B V ℓ (jW ≫ fW) j
      kbar ℱ 1 :=
    { toFun := Jl
      map_add' := Jl.map_add
      map_smul' := hE }
  refine ⟨dy, hdy, hcardA, J, (injective_rationalLift H Jint hJint).comp hΦi, ?_⟩
  refine LinearMap.ext fun z => ?_
  have hΦT : ((Φ ((Matrix.toLin' ((τ g₀ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)).restrict
      (toLin'_mem_invariants_of_mem_normalizer τ Inr
        (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
          (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD)) z) : Irat) :
        Fin (m * d) → ℚ_[ℓ]) = ρq g₀ *ᵥ ((Φ z : Irat) : Fin (m * d) → ℚ_[ℓ]) := by
    change conjRestrictScalarsCoords b Pc ((τ g₀ : GL (Fin m) E).val *ᵥ (z : Fin m → E)) = _
    exact conjRestrictScalarsCoords_mulVec b Pc _ _ (hconj g₀) _
  have hz : ρq g₀ *ᵥ ((Φ z : Irat) : Fin (m * d) → ℚ_[ℓ]) ∈ Irat := hΦT ▸ (Φ _).2
  change Jrat (Φ _) = _
  rw [show Φ _ = ⟨_, hz⟩ from Subtype.ext hΦT, hFrob (Φ z) hz, LinearMap.comp_apply,
    Module.End.pow_apply]
  change extendScalarsEndRingHom H (Frob.hom ^ dy) (Jrat (Φ z)) = _
  rw [map_pow, Module.End.pow_apply]
  rfl

end Stacks.EtaleCohomology
