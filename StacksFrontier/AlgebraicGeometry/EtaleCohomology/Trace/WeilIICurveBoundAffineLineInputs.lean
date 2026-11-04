module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveDegreeOneWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveEasyDegreeWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBoundAffineLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectCurveFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTraceFormulaOfCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveFiniteLevelCohomology

/-!
# The weight bound of Weil II on open subschemes of the affine line, from its inputs

`Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine` follows from four statements proved
elsewhere in the project (or by sibling developments), stated here as propositions with the exact
shapes consumed:

* `Stacks.EtaleCohomology.CurveTraceFormulaInput`: the Grothendieck–Lefschetz trace formula
  (Tag 03V2) for `ℱ_τ` on a smooth curve, `τ` any continuous `ℚ_ℓ`-representation;
* `Stacks.EtaleCohomology.CurveCoinvariantsInput`: `H²_c(U_k̄, ℱ_τ ⊗ ℚ_ℓ)` is the geometric
  coinvariants of `τ`, with `π_U^*` acting as `q` times a Frobenius lift (Tag 03VN);
* `Stacks.EtaleCohomology.CurveFiniteLevelInput`: the finite levels `Hⁱ_c(U_k̄, ℱ_{τ,n})` are
  finite (Tag 0GKR after base change to `k̄`);
* `Stacks.EtaleCohomology.LaumonOpenAffineLineInput`: Laumon's theorem (Weil II 3.2.3 for pure
  lisse sheaves on opens of the affine line, by the Fourier transform), for the restriction of
  scalars of a representation with coefficients in a finite extension `E` of `ℚ_ℓ` which is pure of
  an integer weight `≤ w` along every embedding of `E`.

Degrees `i ≠ 1` use `H⁰_c = 0` on an affine curve and the coinvariants in degree two; degree one is
`Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_one_of_isIotaRealizable`.

## Main results

* `Stacks.EtaleCohomology.weilIICurveBoundOpenAffineLine_of_inputs`.
* `Stacks.EtaleCohomology.curveFiniteLevelInput`: the finiteness input holds (Tag 0GKR over `k̄`).
* `Stacks.EtaleCohomology.weilIICurveBoundOpenAffineLine_of_traceFormula_of_coinvariants_of_laumon`
  gives the bound from the three remaining inputs.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- **The trace formula for `ℱ_τ` on a smooth curve** (Tag 03V2 for lisse sheaves on curves):
`∑_{deg y ∣ N} deg y · tr τ(F_y)^{N / deg y} = ∑_{i < 3} (-1)^i tr (π_U^*)^N` on
`Hⁱ_c(U_k̄, ℱ_τ ⊗ ℚ_ℓ)`. -/
public def CurveTraceFormulaInput : Prop :=
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
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    {m : ℕ} (τ : EtaleFundamentalGroup U.1 x →* GL (Fin m) ℚ_[ℓ]) (hτ : Continuous τ) (N : ℕ),
    0 < N →
    ∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : ℚ_[ℓ]) *
        (((τ (geometricFrobeniusFamily f x y)).val) ^ (N / residueDegree f y.1)).trace =
      ∑ i ∈ Finset.range 3, (-1 : ℚ_[ℓ]) ^ i * LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
            (LAdicSheaf.representationSheaf B U x τ hτ) (i : ℤ))
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B U x τ hτ) (i : ℤ)).hom ^ N)

/-- **`H²_c` of `ℱ_τ` on a smooth geometrically connected curve is the geometric coinvariants,
twisted by `(-1)`** (Tag 03VN): for every lift `φ` of the inverse of the Frobenius of `k`, there is
an isomorphism with the coinvariants of `τ` under `π₁(U_k̄)` carrying `π_U^*` to `q · φ`. -/
public def CurveCoinvariantsInput : Prop :=
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
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    {m : ℕ} (τ : EtaleFundamentalGroup U.1 x →* GL (Fin m) ℚ_[ℓ]) (hτ : Continuous τ)
    (φ : EtaleFundamentalGroup U.1 x),
    etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hcard (x.map f))⁻¹ →
    ∃ e : (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x τ hτ) 2) ≃ₗ[ℚ_[ℓ]]
        Representation.Coinvariants ((matrixRepresentation τ).comp
          (etaleFundamentalGroupMap f x).toMonoidHom.ker.subtype),
      ∀ v, e ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B U x τ hτ) 2).hom v) =
        ((p ^ n : ℕ) : ℚ_[ℓ]) • coinvariantsFrobenius (etaleFundamentalGroupMap f x).toMonoidHom.ker
          τ φ (e v)

/-- **The finite levels of `Hⁱ_c(U_k̄, ℱ_τ)` on a smooth curve are finite** (Tag 0GKR over
`k̄`). -/
public def CurveFiniteLevelInput : Prop :=
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
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    {m : ℕ} (τ : EtaleFundamentalGroup U.1 x →* GL (Fin m) ℚ_[ℓ]) (hτ : Continuous τ) (i : ℤ)
    (N : ℕ), Finite ((geometricCompactSupportPadicCohomology B U ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B U ℓ (LAdicSheaf.representationSheaf B U x τ hτ) N))

/-- **Laumon's theorem on opens of the affine line** (Weil II 3.2.3 for pure lisse sheaves, by the
`ℓ`-adic Fourier transform), for the restriction of scalars `Res_b σ` of a representation
`σ : π₁(U, x̄) → GL_m(E)` with `E` finite over `ℚ_ℓ`: if along every embedding `ι' : E → ℂ` over
`ι` the representation `σ` is pure of some integer weight `≤ w`, then the characteristic roots of
`π_U^*` on `H¹_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` have weights `≤ w + 1`. -/
public def LaumonOpenAffineLineInput : Prop :=
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
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ ι' : E →+* ℂ, (∀ c, ι' (algebraMap ℚ_[ℓ] E c) = ι c) → ∃ β : ℤ, β ≤ w ∧
      ∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    IsCharpolyNormMixedOfWeightLE (p ^ n) ι (w + 1)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1).hom

open LAdicSheaf in
/-- **The weight bound of Weil II on affine opens of the affine line, from its inputs**: the trace
formula, the coinvariants in degree two, the finiteness of the finite levels and Laumon's theorem
give `Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine`. -/
public theorem weilIICurveBoundOpenAffineLine_of_inputs (hT : CurveTraceFormulaInput.{u})
    (hC : CurveCoinvariantsInput.{u}) (hF : CurveFiniteLevelInput.{u})
    (hL : LaumonOpenAffineLineInput.{u}) : WeilIICurveBoundOpenAffineLine.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ he j kbar _ _ _ _ p n _ _ hcard hℓp x r ρ hρ ι w
    hmix hreal i _ z hz
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : Nonempty U.1 := ConnectedSpace.toNonempty
  have hdim : topologicalKrullDim U.1 ≤ 1 :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le
  have hFD : ∀ {N : ℕ} (τ : EtaleFundamentalGroup U.1 x →* GL (Fin N) ℚ_[ℓ]) (hτ : Continuous τ)
      (i' : ℤ), FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x τ hτ) i') :=
    fun τ hτ i' =>
      LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le_one
        B U ℓ f j kbar p n hcard hdim _ i'
  obtain ⟨φ, hφ⟩ := exists_etaleFundamentalGroupMap_eq_finiteFieldFrobenius_inv p n hcard f x kbar
  have htf : ∀ (ι₁ : ℚ_[ℓ] →+* ℂ) (m : ℕ) (τ : EtaleFundamentalGroup U.1 x →* GL (Fin m) ℚ_[ℓ]),
      Continuous τ → SatisfiesFrobeniusTraceFormula ((p ^ n : ℕ) : ℝ) ι₁
        (etaleFundamentalGroupMap f x).toMonoidHom.ker φ
        (fun y : closedPoints U.1 => geometricFrobeniusFamily f x y)
        (fun y => residueDegree f y.1) τ := by
    intro ι₁ m τ hτ
    obtain ⟨e₂, he₂⟩ := hC B U ℓ k f j kbar p n hcard hℓp x τ hτ φ hφ
    have : ∀ i' : ℕ, FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x τ hτ) (i' : ℤ)) :=
      fun i' => hFD τ hτ i'
    exact satisfiesFrobeniusTraceFormula_of_trace_eq (etaleFundamentalGroupMap f x).toMonoidHom.ker
      (p ^ n) (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)) ι₁ φ
      (fun y : closedPoints U.1 => geometricFrobeniusFamily f x y) (fun y => residueDegree f y.1) τ
      (fun i' : ℕ => ↥(LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x τ hτ) (i' : ℤ)))
      (fun i' => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B U x τ hτ) (i' : ℤ)).hom)
      (subsingleton_rationalGeometricCompactlySupportedCohomology_zero_representationSheaf
        B U ℓ f j kbar x τ hτ) e₂ he₂ (fun N hN => hT B U ℓ k f j kbar p n hcard hℓp x τ hτ N hN)
  by_cases hi : i = 1
  · subst hi
    obtain ⟨w', hw', hn⟩ := isCharpolyNormMixedOfWeightLE_one_of_isIotaRealizable B U ℓ f j kbar p n
      hcard hℓp x φ hφ htf (fun τ hτ => hFD τ hτ 1)
      (fun τ hτ N => hF B U ℓ k f j kbar p n hcard hℓp x τ hτ 1 N)
      (fun E _ _ _ _ b _ σ hσ ι' w'' _ hP => hL B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ ι'
        w'' hP) ρ hρ ι w hmix hreal z hz
    exact ⟨w', hw', hn⟩
  · obtain ⟨e₂, he₂⟩ := hC B U ℓ k f j kbar p n hcard hℓp x ρ hρ φ hφ
    have := hFD ρ hρ 2
    exact exists_weight_le_of_isRoot_rationalGeometricCompactlySupportedFrobenius_of_ne_one B U ℓ f
      j kbar p n hcard x ρ hρ ι hmix φ hφ
      (subsingleton_rationalGeometricCompactlySupportedCohomology_zero_representationSheaf
        B U ℓ f j kbar x ρ hρ) e₂ he₂ i hi hz

open LAdicSheaf in
/-- **The finite levels of `Hⁱ_c(U_k̄, ℱ_τ)` on a smooth curve are finite**: Tag 0GKR over
`k̄`. -/
public theorem curveFiniteLevelInput : CurveFiniteLevelInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p n _ _ hcard hℓp x m τ hτ i N
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Nonempty U.1 := ConnectedSpace.toNonempty
  exact finite_geometricCompactSupportPadicCohomology_padicLevel_of_topologicalKrullDim_le_one
    B U ℓ f j kbar (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le _ i N

/-- **The weight bound of Weil II on affine opens of the affine line** from the trace formula, the
coinvariants in degree two and Laumon's theorem. -/
public theorem weilIICurveBoundOpenAffineLine_of_traceFormula_of_coinvariants_of_laumon
    (hT : CurveTraceFormulaInput.{u}) (hC : CurveCoinvariantsInput.{u})
    (hL : LaumonOpenAffineLineInput.{u}) : WeilIICurveBoundOpenAffineLine.{u} :=
  weilIICurveBoundOpenAffineLine_of_inputs hT hC curveFiniteLevelInput hL

end Stacks.EtaleCohomology

end
