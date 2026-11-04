module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.CategoryTheory.Shift.ShiftedHomConj
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsFiniteOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.PseudoCoherentIffCoherentHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.Homology.PseudoCoherent.Coherent

/-!
# Ext groups out of a quasi-coherent object on an affine algebraic space

Let `U` be an object of the big fppf site whose underlying scheme is affine, `R = Γ(U, 𝒪_U)`,
`M ↦ M^~` the associated-module functor to `𝒪`-modules on the small étale site of `yoneda.obj U`
and `RΓ : D(𝒪) ⥤ D(R)` the derived sections. For `L ∈ D_QCoh(𝒪)` and an `R`-module `N` there are
canonical isomorphisms

`Hom_{D(R)}(RΓ(L), N[i]) ≅ Hom_{D(𝒪)}(L, N^~[i])`,

natural in `N` and carrying composition with the class of a short exact sequence of `R`-modules
to composition with the class of the associated short exact sequence of `𝒪`-modules. They are
induced by the fully faithful functor `Φ : D(R) ⥤ D(𝒪)` and the counit `Φ(RΓ(L)) ≅ L`.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineShiftedHomEquiv`: the isomorphism.

## Main results

* `AlgebraicGeometry.Space.representedAffineShiftedHomEquiv_comp_mk₀`: naturality in `N`.
* `AlgebraicGeometry.Space.representedAffineShiftedHomEquiv_comp_singleδ`: compatibility with
  the classes of short exact sequences.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_representedAffineDerivedSections`: over a
  Noetherian ring `R`, the derived sections of a pseudo-coherent object are pseudo-coherent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

variable (L : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
  (isAlgebraicSpace_yoneda B S hS U)))
  (hL : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ L)

/-- The counit `Φ(RΓ(L)) ≅ L`, for `L` in `D_QCoh`. -/
def representedAffineCounitIso :
    (representedAffineDerivedAssociated B S hS U).obj
        ((representedAffineDerivedSections B S hS U).obj L) ≅ L :=
  haveI := isIso_representedAffineDerivedAdjunction_counit_app B S hS U L hL
  asIso ((representedAffineDerivedAdjunction B S hS U).counit.app L)

/-- The comparison `Φ(N[0]) ≅ N^~[0]` of the derived associated module with the associated
module placed in degree zero. -/
abbrev representedAffineSingleIso (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineDerivedAssociated B S hS U).obj
        ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((representedAffineAssociated B S hS U).obj N) :=
  ((representedAffineAssociated B S hS U).mapDerivedCategorySingleFunctor 0).app N

include hL

/-- **`Hom_{D(R)}(RΓ(L), N[i]) ≃+ Hom_{D(𝒪)}(L, N^~[i])`** for `L ∈ D_QCoh(𝒪)`. -/
def representedAffineShiftedHomEquiv
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (i : ℤ) :
    ShiftedHom ((representedAffineDerivedSections B S hS U).obj L)
        ((DerivedCategory.singleFunctor _ 0).obj N) i ≃+
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj
        ((representedAffineAssociated B S hS U).obj N)) i :=
  ShiftedHom.conjMapAddEquiv (representedAffineDerivedAssociated B S hS U)
    (representedAffineDerivedAssociatedFullyFaithful B S hS U)
    (representedAffineCounitIso B S hS U L hL) (representedAffineSingleIso B S hS U N) i

/-- The isomorphism sends `f` to `Φ(f)` conjugated by the counit and by `Φ(N[0]) ≅ N^~[0]`. -/
theorem representedAffineShiftedHomEquiv_apply
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (i : ℤ)
    (f : ShiftedHom ((representedAffineDerivedSections B S hS U).obj L)
        ((DerivedCategory.singleFunctor _ 0).obj N) i) :
    representedAffineShiftedHomEquiv B S hS U L hL N i f =
      (representedAffineCounitIso B S hS U L hL).inv ≫
        f.map (representedAffineDerivedAssociated B S hS U) ≫
          (representedAffineSingleIso B S hS U N).hom⟦i⟧' :=
  rfl

/-- **Naturality in the module.** The isomorphism commutes with composition with the image of a
morphism `N ⟶ N'` of `R`-modules. -/
theorem representedAffineShiftedHomEquiv_comp_mk₀
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') (i : ℤ)
    (f : ShiftedHom ((representedAffineDerivedSections B S hS U).obj L)
        ((DerivedCategory.singleFunctor _ 0).obj N) i) :
    representedAffineShiftedHomEquiv B S hS U L hL N' i
        (f.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ((DerivedCategory.singleFunctor _ 0).map g))
          (zero_add i)) =
      (representedAffineShiftedHomEquiv B S hS U L hL N i f).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl ((DerivedCategory.singleFunctor _ 0).map
          ((representedAffineAssociated B S hS U).map g))) (zero_add i) :=
  ShiftedHom.conjMapAddEquiv_comp_mk₀ _ _ _ _ _ _ _
    (((representedAffineAssociated B S hS U).mapDerivedCategorySingleFunctor 0).hom.naturality g)
    i f

omit L hL in
/-- The associated modules of a short complex of `R`-modules compose to zero. -/
theorem representedAffineAssociated_map_comp_map_eq_zero
    (Sq : ShortComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    (representedAffineAssociated B S hS U).map Sq.f ≫
      (representedAffineAssociated B S hS U).map Sq.g = 0 := by
  rw [← Functor.map_comp, Sq.zero, Functor.map_zero]

omit L hL in
/-- The short complex of associated modules of a short complex of `R`-modules. -/
def representedAffineShortComplex
    (Sq : ShortComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    ShortComplex (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :=
  ShortComplex.mk _ _ (representedAffineAssociated_map_comp_map_eq_zero B S hS U Sq)

omit L hL in
/-- The associated modules of a short exact sequence of `R`-modules form a short exact
sequence. -/
theorem representedAffineShortComplex_shortExact
    {Sq : ShortComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))}
    (hSq : Sq.ShortExact) : (representedAffineShortComplex B S hS U Sq).ShortExact :=
  hSq.map_of_exact (representedAffineAssociated B S hS U)

/-- **Compatibility with the classes of short exact sequences.** -/
theorem representedAffineShiftedHomEquiv_comp_singleδ
    {Sq : ShortComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))}
    (hSq : Sq.ShortExact) (i j : ℤ) (hij : 1 + i = j)
    (f : ShiftedHom ((representedAffineDerivedSections B S hS U).obj L)
        ((DerivedCategory.singleFunctor _ 0).obj Sq.X₃) i) :
    representedAffineShiftedHomEquiv B S hS U L hL Sq.X₁ j (f.comp hSq.singleδ hij) =
      (representedAffineShiftedHomEquiv B S hS U L hL Sq.X₃ i f).comp
        (representedAffineShortComplex_shortExact B S hS U hSq).singleδ hij := by
  rw [representedAffineShiftedHomEquiv_apply, representedAffineShiftedHomEquiv_apply]
  exact ShiftedHom.conj_map_comp (representedAffineDerivedAssociated B S hS U)
    (representedAffineCounitIso B S hS U L hL) (representedAffineSingleIso B S hS U Sq.X₃)
    (representedAffineSingleIso B S hS U Sq.X₁) f hSq.singleδ _
    (hSq.mapShiftedHom_singleδ (representedAffineAssociated B S hS U)) hij

omit hL in
/-- **The derived sections of a pseudo-coherent object over a Noetherian affine are
pseudo-coherent.** If `U` has affine underlying scheme with Noetherian ring of global functions
`R` and `L` is a pseudo-coherent object of `D(𝒪_{yoneda.obj U})`, then `RΓ(L)` is
`m`-pseudo-coherent in `D(R)` for every `m`: its cohomology `Γ(U, Hⁱ(L))` is finite over `R`,
the `Hⁱ(L)` being coherent (Stacks 08IK), and vanishes in large degrees (Stacks 066E). -/
theorem isPseudoCoherentFrom_representedAffineDerivedSections
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    (hpc : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherent L) (m : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((representedAffineDerivedSections B S hS U).obj L) m := by
  have hZ := B.contains_terminal
  have hX := isNoetherian_yoneda_of_isAffine B S hS (T := U) hZ
  have hQ : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ L :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS _ _ L hpc
  obtain ⟨⟨b, hb⟩, hcoh⟩ := (isPseudoCoherent_iff_isCoherent_homology hZ
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ hX ⟨L, hQ⟩).1 hpc
  refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    ((representedAffineDerivedSections B S hS U).obj L) m
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).1.2 ⟨⟨b, fun i hi => ?_⟩, fun i _ => ?_⟩
  · exact ((representedAffineSections B S hS U).map_isZero (hb i hi)).of_iso
      (representedAffineDerivedSectionsHomologyIso B S hS U L hQ i)
  · let N := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) i).obj L
    have hTa : IsAffineChart B S hS (yoneda.obj U) (idEtaleChart B S hS U) :=
      (inferInstance : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    have hNT := moduleFinite_sections_of_isCoherent B S hS _ _ N (hcoh i)
      (V := idEtaleChart B S hS U) hTa
    have := moduleFinite_representedAffineSections B S hS U N (hQ i) _
      (isTerminalIdEtaleChart B S hS U) hTa hNT
    exact Module.Finite.equiv
      (representedAffineDerivedSectionsHomologyIso B S hS U L hQ i).toLinearEquiv.symm

omit hL in
/-- **Reading Ext groups out of a quasi-coherent object in `D(R)`, composed with a further
identification.** Let `L ∈ D_QCoh(𝒪)` on the affine `U` and let `Φ` identify the groups
`Ext^i(L, 𝒢)` for quasi-coherent `𝒢` with groups `W 𝒢 i`, compatibly with given maps along
morphisms of modules and with given boundary maps of short exact sequences. Then
`Ext^i_R(RΓ(L), N) ≃+ W Ñ i`, naturally in the `R`-module `N` and compatibly with the boundary
maps of short exact sequences of `R`-modules. -/
theorem exists_representedAffineShiftedHomEquiv_trans
    (hQ : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ L)
    (W : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) → ℤ → Type*)
    [∀ F i, AddCommGroup (W F i)]
    (Φ : ∀ (F : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
      (_ : F.IsQuasicoherentOnSite) (i : ℤ),
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj F) i ≃+ W F i)
    (Wmap : ∀ {F F' : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)}
      (_ : F ⟶ F') (i : ℤ), W F i → W F' i)
    (Wδ : ∀ (T : ShortComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))) (_ : T.ShortExact) (i : ℤ), W T.X₃ i → W T.X₁ (i + 1))
    (hnat : ∀ {F F' : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)}
      (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ)
      (e : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj F) i),
      Φ F' hF' i (e ≫ ((DerivedCategory.singleFunctor _ 0).map q)⟦i⟧') = Wmap q i (Φ F hF i e))
    (hδ : ∀ (T : ShortComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))) (hT : T.ShortExact)
      (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite)
      (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
      (e : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj T.X₃) i),
      Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) = Wδ T hT i (Φ T.X₃ h₃ i e)) :
    ∃ Ξ : ∀ (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (i : ℤ),
        ShiftedHom ((representedAffineDerivedSections B S hS U).obj L)
          ((DerivedCategory.singleFunctor _ 0).obj N) i ≃+
          W ((representedAffineAssociated B S hS U).obj N) i,
      (∀ {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') (i : ℤ)
        (e : ShiftedHom ((representedAffineDerivedSections B S hS U).obj L)
          ((DerivedCategory.singleFunctor _ 0).obj N) i),
        Ξ N' i (e.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
            ((DerivedCategory.singleFunctor _ 0).map g)) (zero_add i)) =
          Wmap ((representedAffineAssociated B S hS U).map g) i (Ξ N i e)) ∧
      (∀ {Sq : ShortComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))}
        (hSq : Sq.ShortExact) (i : ℤ)
        (e : ShiftedHom ((representedAffineDerivedSections B S hS U).obj L)
          ((DerivedCategory.singleFunctor _ 0).obj Sq.X₃) i),
        Ξ Sq.X₁ (i + 1) (e.comp hSq.singleδ (add_comm 1 i)) =
          Wδ (representedAffineShortComplex B S hS U Sq)
            (representedAffineShortComplex_shortExact B S hS U hSq) i (Ξ Sq.X₃ i e)) := by
  refine ⟨fun N i => (representedAffineShiftedHomEquiv B S hS U L hQ N i).trans
    (Φ ((representedAffineAssociated B S hS U).obj N)
      (isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U N) i), ?_, ?_⟩
  · intro N N' g i e
    simp only [AddEquiv.trans_apply]
    rw [representedAffineShiftedHomEquiv_comp_mk₀, ShiftedHom.comp_mk₀]
    exact hnat _ _ _ i _
  · intro Sq hSq i e
    simp only [AddEquiv.trans_apply]
    rw [representedAffineShiftedHomEquiv_comp_singleδ B S hS U L hQ hSq i (i + 1) (add_comm 1 i)]
    have h := isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U
    exact hδ _ (representedAffineShortComplex_shortExact B S hS U hSq) (h _) (h _) (h _) i _

end AlgebraicGeometry.Space

end
