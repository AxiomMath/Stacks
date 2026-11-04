module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFibreSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedSectionsShiftedHom
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.Statements
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDualTowerData
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackSingleDelta

/-!
# The Ext groups of an object of `Coh_{X/B}` over a Noetherian affine base

Let `x = (T, g, ℱ)` be an object of `Coh_{X/Y}` (Stacks 08KB) whose test scheme `T = Spec R` is
affine with `R` Noetherian, and let `f : X_T ⟶ T` be the base change. Part (B) of Stacks 08JR,
applied to `E = ℱ[0]` and the one-term complex `𝒢^• = ℱ`, gives a pseudo-coherent object `L` of
`D(𝒪_T)` with `Ext^i_{𝒪_T}(L, 𝒢) ≅ Ext^i_{X_T}(ℱ, ℱ ⊗ f^*𝒢)` for quasi-coherent `𝒢`. Reading
`L` in `D(R)` through the derived sections (the affine case of Stacks 08H0) this becomes

`Ext^i_R(RΓ(L), N) ≅ Ext^i_{X_T}(ℱ, ℱ ⊗ f^*Ñ)`,

natural in the `R`-module `N` and compatible with the classes of short exact sequences, with
`RΓ(L)` pseudo-coherent. This is the input of the first proof of Stacks 08WA to which perfect
duality is then applied.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.exists_isPseudoCoherentFrom_extEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] pointTopology

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- The module of an object of `Coh_{X/Y}` placed in degree zero, as a one-term complex. -/
abbrev singleComplex (x : CoherentObject D) :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (D.space x.T))) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj x.F

/-- The test scheme of an object of `Coh_{X/Y}`, as the algebraic space it represents. -/
abbrev baseSpace (x : CoherentObject D) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj x.T.left, isAlgebraicSpace_yoneda B S hS x.T.left⟩

/-- The projection `X_T ⟶ T` of an object of `Coh_{X/Y}`, with its target written as the
represented algebraic space `AlgebraicGeometry.Space.CoherentSituation.baseSpace`. -/
abbrev baseProjection (x : CoherentObject D) : D.space x.T ⟶ D.baseSpace x :=
  D.projection x.T

/-- The ring of global functions of the test scheme of an object of `Coh_{X/Y}`. -/
abbrev baseRing (x : CoherentObject D) : CommRingCat.{u} :=
  Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)

/-- The base change of an object of `Coh_{X/Y}` over a Noetherian affine test scheme is
étale-locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_space (x : CoherentObject D)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)] :
    HasEtaleLocalProperty B S hS (D.space x.T).1
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) := by
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj x.T.left) :=
    isLocallyNoetherian_of_affine_cover
      (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj x.T.left)⟩)
      (by simp) fun _ ↦ inferInstance
  exact hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_schemeSpace x.T.left
    (D.projection x.T) x.properSupport.choose

/-- The module of an object of `Coh_{X/Y}` over a Noetherian affine test scheme is coherent. -/
theorem isCoherent_F_of_isNoetherianRing (x : CoherentObject D)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)] :
    IsCoherent B S hS (D.space x.T).1 (D.space x.T).2 x.F := by
  have : Fact (HasEtaleLocalProperty B S hS (D.space x.T).1
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V)) :=
    ⟨D.hasEtaleLocalProperty_isLocallyNoetherian_space x⟩
  exact (isCoherent_iff_isFinitePresentationOnSite B S hS _ _ x.F).2 x.finitePresentation

/-- The one-term complex of an object of `Coh_{X/Y}` over a Noetherian affine test scheme
satisfies the hypotheses of Stacks 08JR on `𝒢^•`. -/
theorem flatProperSupportComplex_singleComplex (x : CoherentObject D)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)] :
    FlatProperSupportComplex B S hS (D.baseProjection x) x.properSupport.choose
      (D.singleComplex x) := by
  have hz : ∀ q : ℤ, q ≠ 0 → IsZero ((D.singleComplex x).X q) := fun q hq =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hq
  let e₀ : (D.singleComplex x).X 0 ≅ x.F := HomologicalComplex.singleObjXSelf _ 0 x.F
  obtain ⟨hU, hprop⟩ := x.properSupport.choose_spec
  refine ⟨⟨0, 0, fun q hq => hz q (by omega)⟩, fun q => ?_, fun q => ?_,
    ⟨D.support x.T x.F, hU, hprop, fun q => ?_⟩⟩
  · by_cases hq : q = 0
    · subst hq
      exact isCoherent_of_iso B S hS _ e₀.symm (D.isCoherent_F_of_isNoetherianRing x)
    · exact isCoherent_of_isZero B S hS (D.space x.T) (hz q hq)
  · by_cases hq : q = 0
    · subst hq
      exact IsFlatOver.of_iso B S hS _ e₀.symm x.flat
    · exact isFlatOver_of_isZero B S hS (D.baseProjection x) (hz q hq)
  · by_cases hq : q = 0
    · subst hq
      exact (supportOfSheaf_eq_of_iso B S hS (D.space x.T) e₀).le
    · rw [(supportOfSheaf_eq_empty_iff_isZero B S hS (D.space x.T) _).2 (hz q hq)]
      exact Set.empty_subset _

/-- The module of an object of `Coh_{X/Y}` placed in degree zero of the derived category of its
base change. -/
abbrev singleObject (x : CoherentObject D) :
    DerivedCategory (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2) :=
  (DerivedCategory.singleFunctor _ 0).obj x.F

/-- The module of an object of `Coh_{X/Y}` over a Noetherian affine test scheme, in degree zero,
has coherent cohomology sheaves. -/
theorem isCoherent_homology_singleObject (x : CoherentObject D)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)] (q : ℤ) :
    IsCoherent B S hS (D.space x.T).1 (D.space x.T).2
      ((DerivedCategory.homologyFunctor _ q).obj (D.singleObject x)) := by
  by_cases hq : q = 0
  · subst hq
    exact isCoherent_of_iso B S hS _
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app x.F).symm
      (D.isCoherent_F_of_isNoetherianRing x)
  · rcases lt_or_gt_of_ne hq with h | h
    · exact isCoherent_of_isZero B S hS (D.space x.T)
        (DerivedCategory.isZero_of_isGE (D.singleObject x) 0 q h)
    · exact isCoherent_of_isZero B S hS (D.space x.T)
        (DerivedCategory.isZero_of_isLE (D.singleObject x) 0 q h)

/-- **The Ext groups of an object of `Coh_{X/Y}` over a Noetherian affine base.** For an object
`x = (T, g, ℱ)` with `T = Spec R` affine and `R` Noetherian there is a `(-3)`-pseudo-coherent
`L` in `D(R)` with additive bijections `Ext^i_R(L, N) ≃+ Ext^i_{X_T}(ℱ, ℱ ⊗ f^*Ñ)`, natural in
the `R`-module `N` and carrying composition with the class of a short exact sequence of
`R`-modules to composition with the boundary of the associated sequence
`0 → ℱ ⊗ f^*Ñ₁ → ℱ ⊗ f^*Ñ₂ → ℱ ⊗ f^*Ñ₃ → 0`. This is part (B) of Stacks 08JR at `E = ℱ[0]`,
`𝒢^• = ℱ`, read in `D(R)`. -/
theorem exists_isPseudoCoherentFrom_extEquiv (x : CoherentObject D)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)] :
    ∃ (L : DerivedCategory (ModuleCat.{u} (D.baseRing x))),
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom L (-3) ∧
      ∃ Ξ : ∀ (N : ModuleCat.{u} (D.baseRing x)) (i : ℤ),
          ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i ≃+
            ShiftedHom (D.singleObject x) (tensorPullbackComplexDerived (D.baseProjection x)
              (D.singleComplex x)
              ((HomologicalComplex.single (SheafOfModules.{u}
                (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
                ((representedAffineAssociated B S hS x.T.left).obj N))) i,
        (∀ {N N' : ModuleCat.{u} (D.baseRing x)}
          (g : N ⟶ N') (i : ℤ) (e : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i),
          Ξ N' i (e.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
              ((DerivedCategory.singleFunctor _ 0).map g)) (zero_add i)) =
            Ξ N i e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
              (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
                (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
                ((representedAffineAssociated B S hS x.T.left).map g))))⟦i⟧') ∧
        (∀ {Sq : ShortComplex (ModuleCat.{u} (D.baseRing x))}
          (hSq : Sq.ShortExact) (i : ℤ)
          (e : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj Sq.X₃) i),
          Ξ Sq.X₁ (i + 1) (e.comp hSq.singleδ (add_comm 1 i)) =
            (Ξ Sq.X₃ i e).comp (tensorPullbackSingleDelta B S hS (D.baseProjection x)
              x.properSupport.choose (D.singleComplex x)
              (D.flatProperSupportComplex_singleComplex x)
              (representedAffineShortComplex B S hS x.T.left Sq)
              (representedAffineShortComplex_shortExact B S hS x.T.left hSq))
              (add_comm 1 i)) := by
  have hEb : DerivedCategoryB.IsBoundedAbove (D.singleObject x) :=
    ⟨0, fun n hn => DerivedCategory.isZero_of_isLE (D.singleObject x) 0 n hn⟩
  -- case analysis on this existential runs out of heartbeats re-checking its body, so the
  -- components are extracted with `choose`
  have h08 := exists_isPseudoCoherent_extAddEquiv_tensorPullbackComplex B S hS
    B.contains_terminal (D.baseProjection x) x.properSupport.choose
    (D.isQuasiSeparated_projection x.T)
    (isNoetherian_yoneda_of_isAffine B S hS (T := x.T.left) B.contains_terminal)
    (D.singleObject x) (D.isCoherent_homology_singleObject x) hEb (D.singleComplex x)
    (D.flatProperSupportComplex_singleComplex x)
  have hL : (smallEtaleRingedSite B S hS (yoneda.obj x.T.left)
      (isAlgebraicSpace_yoneda B S hS x.T.left)).IsPseudoCoherent h08.choose :=
    h08.choose_spec.choose
  have hQ : QcohDerived B S hS ⟨yoneda.obj x.T.left, isAlgebraicSpace_yoneda B S hS x.T.left⟩
      h08.choose :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS _ _ _ hL
  obtain ⟨Ξ, h₁, h₂⟩ := exists_representedAffineShiftedHomEquiv_trans B S hS x.T.left h08.choose hQ
    (fun F i => ShiftedHom (D.singleObject x) (tensorPullbackComplexDerived (D.baseProjection x)
      (D.singleComplex x) ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj F)) i)
    h08.choose_spec.choose_spec.choose
    (fun q i y => y ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
      (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
          q)))⟦i⟧')
    (fun T hT i y => y.comp (tensorPullbackSingleDelta B S hS (D.baseProjection x)
      x.properSupport.choose (D.singleComplex x) (D.flatProperSupportComplex_singleComplex x)
      T hT) (add_comm 1 i))
    h08.choose_spec.choose_spec.choose_spec.1 h08.choose_spec.choose_spec.choose_spec.2
  exact ⟨_, isPseudoCoherentFrom_representedAffineDerivedSections B S hS x.T.left _ hL (-3),
    Ξ, h₁, h₂⟩

end CoherentSituation

end AlgebraicGeometry.Space

end
