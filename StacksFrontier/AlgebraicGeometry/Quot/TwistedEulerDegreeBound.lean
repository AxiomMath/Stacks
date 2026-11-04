module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPolynomialLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionChartBounds
public import StacksFrontier.Topology.LocallyConstant.PolynomialFamilyLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.RepresentedFibreComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyBounded
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineNoetherianEtaleCovering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degrees of the Hilbert polynomials of a family of coherent sheaves are locally bounded

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `L` an invertible
`𝒪_X`-module and `(T, 𝓕)` an object of `Coh_{X/B}`.  For every point `t ∈ T` the twisted Euler
characteristic `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is a numerical polynomial (Stacks 0DN4). Its
degree is bounded near every point of `T`: there are a neighbourhood `V` of a given point and an
integer `d` such that for every `t ∈ V` the polynomial has degree at most `d`. Consequently, if
each `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant, the condition
`P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` for all `n ∈ ℤ` is open and closed (Stacks 0DNF).

## Main results

* `CoherentObject.exists_twistedEuler_eq_eulerCharacteristic_and_dimension_le`:
  the twisted Euler characteristic at `t` is that of a coherent module twisted by an invertible
  module on a proper algebraic space `Z` over `κ(t)`, of dimension at most that of any surjective
  étale chart of `X_t`.
* `CoherentObject.isPolynomialOfDegreeLE_twistedEuler_of_chart`: the twisted Euler
  characteristic at `t` is a polynomial of degree at most the dimension of any surjective étale
  chart of `X_t`.
* `CoherentObject.exists_mem_nhds_isPolynomialOfDegreeLE_twistedEuler`:
  **the degrees are locally bounded on `T`.**
* `CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial_of_forall_isLocallyConstant`:
  consequently `Coh^{P, L}_{X/B} ⊆ Coh_{X/B}` is cut out by an open and closed condition as soon
  as each `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 0CZI](https://stacks.math.columbia.edu/tag/0CZI)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

/-- The polynomial in one variable obtained from a multivariate polynomial by sending every
variable to `X` has degree at most the total degree. -/
theorem MvPolynomial.natDegree_aeval_X_le {R σ : Type*} [CommRing R] (P : MvPolynomial σ R) :
    (MvPolynomial.aeval (fun _ : σ => (Polynomial.X : Polynomial R)) P).natDegree ≤
      P.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [show (algebraMap R (Polynomial R) (MvPolynomial.coeff d P)).natDegree = 0 from
    Polynomial.natDegree_C _, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => Polynomial.natDegree_pow_le_of_le _
    Polynomial.natDegree_X_le).trans ?_
  simp only [mul_one]
  exact (MvPolynomial.le_totalDegree hd).trans_eq' rfl

namespace AlgebraicGeometry.Space.CoherentObject

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **The twisted Euler characteristic at a point lives on a proper space of bounded
dimension.**  For an object `(T, 𝓕)` of `Coh_{X/B}` and `t ∈ T`, there are a proper algebraic
space `Z` over `Spec κ(t)`, a coherent `𝒢` and an invertible `ℒ` on `Z` with
`χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = χ(Z, 𝒢 ⊗ ℒ^{⊗ n})` for every `n`, and `Z` has dimension at most the
dimension of the scheme of every étale chart of `X_t` surjective on points. -/
theorem exists_twistedEuler_eq_eulerCharacteristic_and_dimension_le
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) :
    ∃ (Z : AlgebraicSpaces B (Spec (.of (A.testScheme.residueField t)))
        (B.residueField_spec_contains A.T.left.left.property t))
      (hf : IsProper B _ _ (toYonedaId B _ _ Z.1))
      (G ℒ : Modules.{u, u} B _ _ Z.1 Z.2)
      (_ : IsCoherent B _ _ Z.1 Z.2 G)
      (hℒ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B _ _ Z.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B _ _ Z.1 Z.2).O)).property
        ℒ)
      (hcoh : ∀ n : Fin 1 → ℤ, IsCoherent B _ _ Z.1 Z.2
        (@twistedModuleUlift.{u, u} B _ _ Z.1 Z.2 1 G (fun _ => ℒ) (fun _ => hℒ) n)),
      (∀ n : ℤ, twistedEuler L A t n =
        @eulerCharacteristic.{u, u} (A.testScheme.residueField t) _ B _ Z.1 Z.2
          (toYonedaId B _ _ Z.1) hf
          (@twistedModuleUlift.{u, u} B _ _ Z.1 Z.2 1 G (fun _ => ℒ) (fun _ => hℒ) (fun _ => n))
          (hcoh _)) ∧
      ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ (A.fibreSpace t).1),
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf a →
        Function.Surjective (pointsMap B S hS (yoneda.obj U) a) →
        dimension B _ _ Z.1 Z.2 ≤ topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨Zc, G, hG, hGft, hZp, ⟨e⟩⟩ := A.exists_closedSubspace_fibreModule t
  let Zsp := closedSubspaceToSpace B S hS (A.fibreSpace t) Zc
  let i := closedSubspaceInclusion B S hS (A.fibreSpace t) Zc
  let φZ := i.hom ≫ A.fibreProjection t
  let Φ := (smallerBaseModulesEquivalence.{u, u} B _ S _ hS (A.pointSchemeHom' t) Zsp φZ).functor
  have hf := A.isProper_closedSubspaceOverPoint t Zc hZp
  have hLt := isInvertible_modulePullback B S hS (baseChangeProjection D.f (A.pointTest t)) L
  have hLZ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Zsp.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Zsp.1 Zsp.2).O)).property
      (closedSubspaceTwist L A t Zc) :=
    isInvertible_modulePullback B S hS i _
  have hL' := isInvertible_smallerBaseModules B _ S _ hS (A.pointSchemeHom' t) Zsp φZ
    (closedSubspaceTwist L A t Zc)
  have hnoeth : Fact (HasEtaleLocalProperty B _ _ (A.closedSubspaceOverPoint t Zc).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper (A.testScheme.residueField t) B _
      (A.closedSubspaceOverPoint t Zc).1 (A.closedSubspaceOverPoint t Zc).2 _ hf⟩
  have hGcoh := @isCoherent_smallerBaseModules B _ S _ hS (A.pointSchemeHom' t) Zsp φZ hnoeth G hG
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite G hGft)
  refine ⟨A.closedSubspaceOverPoint t Zc, hf, Φ.obj G, Φ.obj (closedSubspaceTwist L A t Zc),
    hGcoh, hL', fun n => @isCoherent_twistedModuleUlift.{u, u} B _ _ _ _ hnoeth 1 _ _
      (fun _ => hL') n hGcoh, fun n => ?_, fun U a ha hs => ?_⟩
  swap
  · exact (dimension_spaceOverSmallerBase_le B S hS _ _ (A.pointSchemeHom' t) Zsp φZ).trans
      (dimension_le_topologicalKrullDim_of_isClosedImmersion B S hS (A.fibreSpace t).2 Zsp.2
        Zc.1.ι Zc.2.2 U a ha hs)
  rw [A.twistedEuler_eq_finsum_closedSubspaceOverPoint L t Zc G hG e n,
    eulerCharacteristic_eq_finsum]
  refine finsum_congr fun q => ?_
  congr 2
  refine (cohomologyOverBaseIso.{u, u} _ B _ _ _
    (uliftForPresentationMapIso.{u, u} B _ _ _ _ ?_) q).toLinearEquiv.finrank_eq
  let eL : (modulePullback B S hS i).obj (fibreTwist L A t n) ≅
      invertibleTensorPower B S hS Zsp.1 Zsp.2 (closedSubspaceTwist L A t Zc) n :=
    (modulePullback B S hS i).mapIso
        (modulePullbackInvertibleTensorPowerIso B S hS (baseChangeProjection D.f (A.pointTest t))
          L n) ≪≫
      modulePullbackInvertibleTensorPowerIso B S hS i _ n
  exact smallerBaseModulesTensorIso B _ S _ hS (A.pointSchemeHom' t) Zsp φZ G _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B _ _ (A.closedSubspaceOverPoint t Zc).1
        (A.closedSubspaceOverPoint t Zc).2).O).obj (Φ.obj G)).mapIso
      (Φ.mapIso eL ≪≫ smallerBaseModulesTensorPowerIso B _ S _ hS (A.pointSchemeHom' t) Zsp φZ
        (closedSubspaceTwist L A t Zc) n)

/-- **The degree of the twisted Euler characteristic at a point is at most the dimension of a
surjective étale chart of the fibre.**  If `U ⟶ X_t` is an étale chart surjective on points and
the scheme `U` has dimension at most `d`, then `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is a rational
polynomial of degree at most `d` (Stacks 0DN4). -/
theorem isPolynomialOfDegreeLE_twistedEuler_of_chart (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ (A.fibreSpace t).1)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hs : Function.Surjective (pointsMap B S hS (yoneda.obj U) a)) {d : ℕ}
    (hd : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) ≤ d) :
    IsPolynomialOfDegreeLE (twistedEuler L A t) d := by
  obtain ⟨Z, hf, G, ℒ, hG, hℒ, _, he, hdim⟩ :=
    A.exists_twistedEuler_eq_eulerCharacteristic_and_dimension_le L t
  have hid : IsClosedImmersion B _ _ (𝟙 Z.1) := by
    have h : ∀ c : BigFppfOver B _ (B.residueField_spec_contains A.T.left.left.property t),
        _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B _ _).map (𝟙 c)) := by
      intro c
      rw [(BigFppfOver.toScheme B _ _).map_id c]
      infer_instance
    have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B _ (B.residueField_spec_contains A.T.left.left.property t))) :=
      MorphismProperty.RespectsIso.inverseImage _ _
    exact MorphismProperty.relative.of_exists fun c g =>
      ⟨c, g, 𝟙 c, by simpa using IsPullback.of_id_snd, h c⟩
  obtain ⟨P, hP, hdeg⟩ := @isTwistedEulerNumericalPolynomial_of_isCoherent.{u, u} _ _ B _ Z 1 _ hf
    G hG (fun _ => ℒ) (fun _ => hℒ) Z (𝟙 Z) hid G hG
    ((modulePushforwardIdIso B _ _ Z).app G).symm
  have hPd : P = 0 ∨ P.totalDegree ≤ d :=
    hdeg.imp id fun h ↦ by exact_mod_cast h.trans ((hdim U a ha hs).trans hd)
  refine ⟨MvPolynomial.aeval (fun _ => Polynomial.X) P, ?_, fun m => ?_⟩
  · rcases hPd with h | h
    · simp [h]
    · exact (MvPolynomial.natDegree_aeval_X_le P).trans h
  · rw [he m, ← hP (fun _ => m), ← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply,
      MvPolynomial.comp_aeval]
    simp

section LocalBound

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  preservesLimitsOfShape_walkingCospan_toScheme

/-- **The degrees are locally bounded over an affine test scheme.**  If the test scheme `T` of
an object of `Coh_{X/B}` is affine, then near every point of `T` the twisted Euler
characteristics `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` are polynomials of bounded degree. -/
theorem exists_mem_nhds_isPolynomialOfDegreeLE_twistedEuler_of_isAffine
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (hT : IsAffine A.testScheme) (t₀ : A.testScheme) :
    ∃ V ∈ 𝓝 t₀, ∃ d : ℕ, ∀ t ∈ V, IsPolynomialOfDegreeLE (twistedEuler L A t) d := by
  obtain ⟨U, hUaff, hUs⟩ :=
    exists_isAffine_isSurjective_chart_baseChangeSpace B S hS D.f D.finitePresentation.2.1 A.T hT
  let a : yoneda.obj U.obj.left ⟶ (D.space A.T).1 := U.obj.hom
  have ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := U.property
  let α : U.obj.left ⟶ A.T.left := Yoneda.fullyFaithful.preimage (a ≫ (D.projection A.T).hom)
  have hα : yoneda.map α = a ≫ (D.projection A.T).hom := Functor.FullyFaithful.map_preimage _ _
  have hlfp : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map α) :=
    locallyOfFinitePresentation_map_of_isLocallyOfFinitePresentation B S hS
      (isLocallyOfFinitePresentation_projection D A.T) (φ := ObjectProperty.homMk a)
      ((isEtale_iff_presheaf_of_yoneda B S hS a).2 ha)
      (ObjectProperty.hom_ext _ hα.symm)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left) := hUaff
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map α) :=
    quasiCompact_of_compactSpace _
  obtain ⟨V, hV, d, hd⟩ :=
    exists_mem_nhds_topologicalKrullDim_fiber_le ((BigFppfOver.toScheme B S hS).map α) t₀
  refine ⟨V, hV, d, fun t ht => ?_⟩
  let pS := A.pointSchemeHom t
  have Hfib := AlgebraicSpaces.isPullback_hom B S hS
    (isPullback_baseChangeMap D.f (A.pointTestHom t))
  have hw : (yoneda.map (pullback.fst α pS) ≫ a) ≫ (D.projection A.T).hom =
      yoneda.map (pullback.snd α pS) ≫ ((schemeSpaceFunctor B S hS).map pS).hom := by
    have h₁ : yoneda.map (pullback.fst α pS ≫ α) = yoneda.map (pullback.snd α pS ≫ pS) := by
      rw [pullback.condition]
    rw [Functor.map_comp, Functor.map_comp, hα] at h₁
    rw [Category.assoc]
    exact h₁
  let c := Hfib.lift _ _ hw
  have hc₁ : c ≫ (D.relativeMap (A.pointTestHom t)).hom = yoneda.map (pullback.fst α pS) ≫ a :=
    Hfib.lift_fst _ _ hw
  have hc₂ : c ≫ (D.projection (A.pointTest t)).hom = yoneda.map (pullback.snd α pS) :=
    Hfib.lift_snd _ _ hw
  have Hout : IsPullback (yoneda.map (pullback.fst α pS))
      (c ≫ (D.projection (A.pointTest t)).hom) (a ≫ (D.projection A.T).hom)
      ((schemeSpaceFunctor B S hS).map pS).hom := by
    rw [hc₂, ← hα]
    exact (IsPullback.of_hasPullback α pS).map yoneda
  have sq : IsPullback (yoneda.map (pullback.fst α pS)) c a
      (D.relativeMap (A.pointTestHom t)).hom :=
    IsPullback.of_bot Hout hc₁.symm Hfib
  have hcet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq ha
  have hcs : Function.Surjective (pointsMap B S hS (yoneda.obj (pullback α pS)) c) :=
    isSurjective_baseChange_of_isPullback (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _) (A.fibreSpace t).2 (D.space A.T).2 sq
      (show Function.Surjective (pointsMap B S hS _ a) from hUs)
  refine A.isPolynomialOfDegreeLE_twistedEuler_of_chart L t _ c hcet hcs ?_
  have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst α pS))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd α pS))
      ((BigFppfOver.toScheme B S hS).map α)
      (A.testScheme.fromSpecResidueField t) :=
    (IsPullback.of_hasPullback α pS).map (BigFppfOver.toScheme B S hS)
  let e := hsq.isoIsPullback _ _ (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map α)
    (A.testScheme.fromSpecResidueField t))
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph]
  exact hd t ht

/-- **The degrees of the Hilbert polynomials are locally bounded.**  For an object `(T, 𝓕)` of
`Coh_{X/B}` and an invertible `𝒪_X`-module `L`, every point of `T` has a neighbourhood `V` and an
integer `d` such that for every `t ∈ V` the function `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is a rational
polynomial of degree at most `d`. -/
@[ega "III 2.5.3" "(i), special case"]
theorem exists_mem_nhds_isPolynomialOfDegreeLE_twistedEuler
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t₀ : A.testScheme) :
    ∃ V ∈ 𝓝 t₀, ∃ d : ℕ, ∀ t ∈ V, IsPolynomialOfDegreeLE (twistedEuler L A t) d := by
  obtain ⟨W, hW, ht₀W, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top t₀)
  let W' : ((BigFppfOver.toScheme B S hS).obj A.T.left).affineOpens := ⟨W, hW⟩
  let j := affineOpenSpecSiteHom B S hS A.T.left W'
  let T' : SchemesOver D.Y := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map j ≫ A.T.hom)
  let h : T' ⟶ A.T := CostructuredArrow.homMk j rfl
  let A' := CoherentSituation.pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS)
    A h
  let m := CoherentSituation.pullbackHom' (modulePullbackStabilityOfFinitePresentation B S hS) A h
  have hm : ∀ s : A'.testScheme, m.baseScheme s = hW.fromSpec s := fun s => by
    show (BigFppfOver.toScheme B S hS).map j s = hW.fromSpec s
    rw [map_affineOpenSpecSiteHom]
  have hA' : IsAffine A'.testScheme :=
    inferInstanceAs (IsAffine (Spec Γ((BigFppfOver.toScheme B S hS).obj A.T.left, W)))
  obtain ⟨s₀, hs₀⟩ : t₀ ∈ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  obtain ⟨V, hV, d, hd⟩ := A'.exists_mem_nhds_isPolynomialOfDegreeLE_twistedEuler_of_isAffine L
    hA' s₀
  refine ⟨hW.fromSpec '' V, ?_, d, ?_⟩
  · rw [← hs₀]
    exact hW.fromSpec.isOpenEmbedding.isOpenMap.image_mem_nhds hV
  · rintro _ ⟨s, hs, rfl⟩
    have he : twistedEuler L A (hW.fromSpec s) = twistedEuler L A' s := by
      funext n
      rw [← hm s]
      exact (CoherentHom.twistedEuler_eq L m s n).symm
    exact he ▸ hd s hs

end LocalBound

end AlgebraicGeometry.Space.CoherentObject

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **`Coh^{P, L}_{X/B}` is cut out by an open and closed condition once the twisted Euler
characteristics are locally constant.**  If for every object `(T, 𝓕)` of `Coh_{X/B}` and every
`n` the function `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant on `T`, then for every `P` the
condition of having Hilbert polynomial `P` with respect to `L` is open and closed. -/
theorem isOpenAndClosedCondition_hasHilbertPolynomial_of_forall_isLocallyConstant
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (hlc : ∀ (A : CoherentObject D) (n : ℤ),
      IsLocallyConstant fun t : A.testScheme => CoherentObject.twistedEuler L A t n)
    (P : ℤ → ℤ) :
    IsOpenAndClosedCondition D (CoherentObject.HasHilbertPolynomial L P) :=
  isOpenAndClosedCondition_hasHilbertPolynomial_of_isLocallyConstant L hlc
    (fun A t => A.exists_mem_nhds_isPolynomialOfDegreeLE_twistedEuler L t) P

end AlgebraicGeometry.Space.CoherentSituation

end
