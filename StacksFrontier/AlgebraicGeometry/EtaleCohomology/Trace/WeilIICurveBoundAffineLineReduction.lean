module

public import StacksFrontier.AlgebraicGeometry.Curves.AffineLineShiftFiniteEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionOneGoodOpen

/-!
# The weight bound of Weil II on opens of the affine line, from the affine line

Deligne's proof of the curve case of the weight bound (Weil II 3.2.3; Kedlaya, *Fourier
transforms and p-adic Weil II*, §6) treats the affine line `𝔸¹_k` itself by the Fourier transform
(Laumon) and passes to its opens along finite étale maps: an open `U = D(g)` of `𝔸¹_k`, `g` monic,
is finite étale over `𝔸¹_k` by `y ↦ x + g(x)^{-p}`
(`Stacks.GenericFiniteEtale.exists_finite_etale_affineLine`), and the weight bound passes from a
smooth curve to its finite étale covers (`π_*` preserves lisseness, pointwise mixedness and
realizability, and `Hⁱ_c(U_k̄, F) = Hⁱ_c((𝔸¹)_k̄, π_* F)`,
`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_finite_etale`). No case of the weight
bound on `U` enters: only the bound on `𝔸¹_k`.

## Main definitions

* `Stacks.EtaleCohomology.WeilIICurveBoundAffineLine`: the curve case on `𝔸¹_k` itself.

## Main results

* `Stacks.EtaleCohomology.weilIICurveBoundOpenAffineLine_of_affineLine`: from `𝔸¹_k` to its opens.
* `Stacks.EtaleCohomology.weilIICurveBoundAffineLine_of_inputs`: the curve case on `𝔸¹_k` from the
  trace formula, the coinvariants, the finite levels and Laumon's theorem on `𝔸¹_k`.
* `Stacks.EtaleCohomology.weilIICurveBoundOpenAffineLine_of_laumonAffineLine`: the curve case on
  opens of `𝔸¹_k` with Laumon's theorem only on `𝔸¹_k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- **The weight bound of Weil II on the affine line**: the statement of
`Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine` for the curves `U` over `k` with an
isomorphism `e : U ⟶ 𝔸¹_k = Spec k[T]` over `k`. -/
public def WeilIICurveBoundAffineLine : Prop :=
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
    (x : GeometricPoint U.1) {r : ℕ} (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ) (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ),
    IsPointwiseMixedOfWeightLE f x (p ^ n) ι w ρ → IsIotaRealizable f x ι ρ →
    ∀ (i : ℤ) [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x ρ hρ) i)] (z : ℂ),
      ((ModuleCat.Hom.hom (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar
        p n hcard (LAdicSheaf.representationSheaf B U x ρ hρ) i)).charpoly.map ι).IsRoot z →
      ∃ w' : ℤ, w' ≤ w + i ∧ ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ ((w' : ℝ) / 2)

/-- **The weight bound of Weil II on opens of the affine line, from the affine line.**  An open
`U` of `𝔸¹_k` is finite étale over `𝔸¹_k`
(`Stacks.GenericFiniteEtale.exists_finite_etale_affineLine`);
the weight bound on `𝔸¹_k` for lisse sheaves
(`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_forall_representationSheaf`) passes to
`U` along `π` (`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_finite_etale`: the
direct image `π_*` of a lisse, pointwise mixed, realizable sheaf is again such, with the same
`Hⁱ_c`), and is then read for `ℱ_ρ`, which is lisse, pointwise mixed and realizable when `ρ` is. -/
public theorem weilIICurveBoundOpenAffineLine_of_affineLine
    (h : WeilIICurveBoundAffineLine.{u}) : WeilIICurveBoundOpenAffineLine.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ he j kbar _ _ _ _ p n _ _ hcard hℓp x r ρ hρ ι w
    hmix hreal i _ z hz
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : Nonempty U.1 := ConnectedSpace.toNonempty
  -- the affine line, an object of `B`
  have hk : (Spec (.of k)).size < B.cutoff := by
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff)
  have hVB : B.Contains (Spec (.of (Polynomial k))) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k
      (Polynomial k) hk
  let V : B.Scheme := B.obj (Spec (.of (Polynomial k))) hVB
  let fV : V.1 ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))
  have : IsNoetherian V.1 := inferInstanceAs (IsNoetherian (Spec (.of (Polynomial k))))
  have : ConnectedSpace V.1 := inferInstanceAs (ConnectedSpace (PrimeSpectrum (Polynomial k)))
  have : IsAffine V.1 := inferInstanceAs (IsAffine (Spec (.of (Polynomial k))))
  have : SmoothOfRelativeDimension 1 fV :=
    Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_polynomial k
  have : Smooth fV := SmoothOfRelativeDimension.smooth 1 fV
  have : IsCurve k fV := Stacks.GenericFiniteEtale.isCurve_specMap_polynomial k
  have : ConnectedSpace ↥(pullback fV (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) :=
    Stacks.GenericFiniteEtale.connectedSpace_pullback_specMap_polynomial k kbar
  obtain ⟨v⟩ : Nonempty V.1 := inferInstanceAs (Nonempty (PrimeSpectrum _))
  -- the weight bound on the affine line
  have hV : LAdicSheaf.SatisfiesWeightBound B ℓ kbar p n hcard ι V fV :=
    LAdicSheaf.satisfiesWeightBound_of_forall_representationSheaf V fV (Stacks.Etale.ofPoint v)
      fun jV _ ρ' hρ' w' hm hr i' _ => h B V ℓ k fV (𝟙 _) (Category.id_comp _) jV kbar p n hcard
        hℓp (Stacks.Etale.ofPoint v) ρ' hρ' ι w' hm hr i'
  -- the finite étale map `U ⟶ 𝔸¹_k`
  obtain ⟨π, hπf, hπe, hπk⟩ := Stacks.GenericFiniteEtale.exists_finite_etale_affineLine p e
  let πB : U ⟶ V := ObjectProperty.homMk π
  have : IsFinite (B.inclusion.map πB) := hπf
  have : Etale (B.inclusion.map πB) := hπe
  have hπk' : B.inclusion.map πB ≫ fV = f := hπk.trans he
  have : LocallyOfFiniteType (B.inclusion.map πB ≫ fV) := by rw [hπk']; infer_instance
  have : QuasiCompact (B.inclusion.map πB ≫ fV) := by rw [hπk']; infer_instance
  have : IsSeparated (B.inclusion.map πB ≫ fV) := by rw [hπk']; infer_instance
  obtain ⟨jV, -⟩ := hasCompactification_of_isNoetherian fV
  exact (LAdicSheaf.satisfiesWeightBound_of_finite_etale fV πB jV
    (LAdicSheaf.hasFiniteCompactSupportCohomology_of_topologicalKrullDim_le_one B ℓ kbar p n hcard
      U _ (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le) hV).congr hπk'
    j (LAdicSheaf.representationSheaf B U x ρ hρ) w
    (LAdicSheaf.representationSheaf_isLisse B U x ρ hρ)
    ((LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_iff B U ℓ f x ρ hρ _ _ _).2 hmix)
    (LAdicSheaf.isIotaRealizable_representationSheaf B U ℓ f x ρ hρ hreal) i z hz

/-- **The weight bound of Weil II on the affine line, from its inputs**: the trace formula, the
coinvariants in degree two, the finiteness of the finite levels and Laumon's theorem on `𝔸¹_k`
(`Stacks.EtaleCohomology.LaumonAffineLineInput`) give
`Stacks.EtaleCohomology.WeilIICurveBoundAffineLine`; the argument is that of
`Stacks.EtaleCohomology.weilIICurveBoundOpenAffineLine_of_inputs` with `U = 𝔸¹_k`. -/
public theorem weilIICurveBoundAffineLine_of_inputs (hT : CurveTraceFormulaInput.{u})
    (hC : CurveCoinvariantsInput.{u}) (hF : CurveFiniteLevelInput.{u})
    (hL : LaumonAffineLineInput.{u}) : WeilIICurveBoundAffineLine.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x r ρ hρ ι w
    hmix hreal i _ z hz
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : Nonempty U.1 := ConnectedSpace.toNonempty
  have hdim : topologicalKrullDim U.1 ≤ 1 :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le
  have hFD : ∀ {N : ℕ} (τ : EtaleFundamentalGroup U.1 x →* GL (Fin N) ℚ_[ℓ]) (hτ : Continuous τ)
      (i' : ℤ), FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x τ hτ) i') := fun τ hτ i' =>
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
          (LAdicSheaf.representationSheaf B U x τ hτ) (i' : ℤ)) := fun i' => hFD τ hτ i'
    exact satisfiesFrobeniusTraceFormula_of_trace_eq (etaleFundamentalGroupMap f x).toMonoidHom.ker
      (p ^ n) (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)) ι₁ φ
      (fun y : closedPoints U.1 => geometricFrobeniusFamily f x y) (fun y => residueDegree f y.1) τ
      (fun i' : ℕ => ↥(LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x τ hτ) (i' : ℤ)))
      (fun i' => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B U x τ hτ) (i' : ℤ)).hom) (
      LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_representationSheaf
        B U ℓ f j kbar x τ hτ) e₂ he₂ (fun N hN => hT B U ℓ k f j kbar p n hcard hℓp x τ hτ N hN)
  rcases eq_or_ne i 1 with rfl | hi
  · exact isCharpolyNormMixedOfWeightLE_one_of_isIotaRealizable B U ℓ f j kbar p n
      hcard hℓp x φ hφ htf (fun τ hτ => hFD τ hτ 1)
      (fun τ hτ N => hF B U ℓ k f j kbar p n hcard hℓp x τ hτ 1 N)
      (fun E _ _ _ _ b _ σ hσ ι' w'' _ hP =>
        hL B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ ι' w'' hP) ρ hρ ι w hmix hreal z hz
  · obtain ⟨e₂, he₂⟩ := hC B U ℓ k f j kbar p n hcard hℓp x ρ hρ φ hφ
    have := hFD ρ hρ 2
    exact exists_weight_le_of_isRoot_rationalGeometricCompactlySupportedFrobenius_of_ne_one B U ℓ f
      j kbar p n hcard x ρ hρ ι hmix φ hφ (
      LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_representationSheaf
        B U ℓ f j kbar x ρ hρ) e₂ he₂ i hi hz

/-- **The weight bound of Weil II on opens of the affine line, with Laumon's theorem only on
`𝔸¹_k`**: the curve case on `𝔸¹_k` from the trace formula, the coinvariants and Laumon's theorem
on `𝔸¹_k`, then on its opens along finite étale maps. -/
public theorem weilIICurveBoundOpenAffineLine_of_laumonAffineLine
    (hT : CurveTraceFormulaInput.{u}) (hC : CurveCoinvariantsInput.{u})
    (hL : LaumonAffineLineInput.{u}) : WeilIICurveBoundOpenAffineLine.{u} :=
  weilIICurveBoundOpenAffineLine_of_affineLine
    (weilIICurveBoundAffineLine_of_inputs hT hC curveFiniteLevelInput hL)

end Stacks.EtaleCohomology

end
