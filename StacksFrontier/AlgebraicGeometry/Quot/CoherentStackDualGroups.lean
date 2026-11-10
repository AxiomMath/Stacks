module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDualComplex
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituationOfGroups
public import StacksFrontier.Deformation.Artin.Obstruction.PseudoCoherentDualComplex

/-!
# The perfect complex of an object of `Coh_{X/B}` over a Noetherian affine base

Let `x = (T, g, ℱ)` be an object of `Coh_{X/Y}` (Stacks 08KB) whose test scheme `T` is affine
with Noetherian ring of global functions, identified with a ring `A` by `e`. This file produces,
as in the first proof of Stacks 08WA, a perfect object `K` of `D(A)` together with
identifications

`Hⁿ(K ⊗ᴸ_A M) ≅ Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃)`,  `n = 1, 2`,

natural in the `A`-module `M` and compatible with the connecting maps. Part (B) of Stacks 08JR
gives the right-hand side as `Ext^n` out of a pseudo-coherent object of `D(A)`
(`AlgebraicGeometry.Space.CoherentSituation.exists_isPseudoCoherentFrom_extEquiv`), and perfect
duality turns that into the cohomology of `K ⊗ᴸ -`
(`Deformation.Artin.exists_perfect_shiftedHomEquiv_of_isPseudoCoherentFrom_of_ringEquiv`).

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.extGroup`: `Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃)`, with its
  functoriality `extGroupMap` and the connecting maps `extGroupDelta`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.exists_perfect_derivedCohomology_addEquiv_extGroup`.
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
section Chart

variable {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}

/-- **The ring of an object of `Coh_{X/Y}` over a chart.** For an object `x` whose test scheme is
`Spec A` (as the object `Deformation.Artin.algebraOver` of the site), the identification of `A`
with the ring of global functions of the test scheme. -/
def chartRingEquiv (x : CoherentObject D)
    (hx : x.T.left = Deformation.Artin.algebraOver A B S hS toS hA) : A ≃+* D.baseRing x :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).symm ≪≫
    Scheme.Γ.mapIso
      (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hx)).op).commRingCatIsoToRingEquiv

/-- The test scheme of an object of `Coh_{X/Y}` over a chart is affine. -/
theorem isAffine_of_chart (x : CoherentObject D)
    (hx : x.T.left = Deformation.Artin.algebraOver A B S hS toS hA) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left) := by
  rw [hx]
  exact inferInstanceAs (IsAffine (Spec (.of A)))

/-- The ring of global functions of the test scheme of an object of `Coh_{X/Y}` over a chart with
Noetherian ring is Noetherian. -/
theorem isNoetherianRing_of_chart [IsNoetherianRing A] (x : CoherentObject D)
    (hx : x.T.left = Deformation.Artin.algebraOver A B S hS toS hA) :
    IsNoetherianRing (D.baseRing x) :=
  isNoetherianRing_of_ringEquiv A (D.chartRingEquiv x hx)

end Chart

variable (x : CoherentObject D) [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
variable {A : Type u} [CommRing A] (e : A ≃+* D.baseRing x)

/-- An `A`-module, read as a module over the ring of global functions of the test scheme. -/
abbrev baseModule (M : ModuleCat.{u} A) : ModuleCat.{u} (D.baseRing x) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.obj M

/-- **`Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃)`** for an `A`-module `M`.

This is a type synonym of the group of shifted morphisms in `D(𝒪_{X_T})`, with its additive
structure recorded as a named instance, so that the additive structures met in later
constructions are syntactically one and the same and need never be compared by unfolding the
derived category. -/
def extGroup (M : ModuleCat.{u} A) (n : ℤ) : Type (u + 1) :=
  ShiftedHom (D.singleObject x) (tensorPullbackComplexDerived (D.baseProjection x)
    (D.singleComplex x) ((HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
        ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e M)))) n

/-- The additive structure of `Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃)`, that of the shifted morphisms. -/
instance (M : ModuleCat.{u} A) (n : ℤ) : AddCommGroup (D.extGroup x e M n) :=
  inferInstanceAs (AddCommGroup (ShiftedHom (D.singleObject x)
    (tensorPullbackComplexDerived (D.baseProjection x)
    (D.singleComplex x) ((HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
        ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e M)))) n))

/-- An element of `Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃)` as a shifted morphism. -/
def extGroupEquiv (M : ModuleCat.{u} A) (n : ℤ) :
    D.extGroup x e M n ≃+ ShiftedHom (D.singleObject x)
      (tensorPullbackComplexDerived (D.baseProjection x)
      (D.singleComplex x) ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
          ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e M)))) n :=
  AddEquiv.refl _

/-- The map of `Ext` groups induced by a map of `A`-modules. -/
def extGroupMap {M N : ModuleCat.{u} A} (g : M ⟶ N) (n : ℤ) :
    D.extGroup x e M n →+ D.extGroup x e N n where
  toFun y := (D.extGroupEquiv x e N n).symm (D.extGroupEquiv x e M n y ≫
    (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
    (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
        ((representedAffineAssociated B S hS x.T.left).map
          ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map g)))))⟦n⟧')
  map_zero' := by simp only [map_zero, Limits.zero_comp]
  map_add' _ _ := by simp only [map_add, Preadditive.add_comp]

/-- The map of `Ext` groups induced by a map `g` of `A`-modules is composition with the map
induced by `g` on the coefficients. -/
theorem extGroupMap_apply {M N : ModuleCat.{u} A} (g : M ⟶ N) (n : ℤ) (y : D.extGroup x e M n) :
    D.extGroupMap x e g n y = (D.extGroupEquiv x e N n).symm (D.extGroupEquiv x e M n y ≫
      (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
        (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
            ((representedAffineAssociated B S hS x.T.left).map
              ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map g)))))⟦n⟧') :=
  rfl

/-- The connecting map of `Ext` groups of a short exact sequence of `A`-modules. -/
def extGroupDelta [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)]
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) :
    D.extGroup x e Sq.X₃ 1 → D.extGroup x e Sq.X₁ 2 := fun y =>
  (D.extGroupEquiv x e Sq.X₁ 2).symm ((D.extGroupEquiv x e Sq.X₃ 1 y).comp
    (tensorPullbackSingleDelta B S hS (D.baseProjection x) x.properSupport.choose
    (D.singleComplex x) (D.flatProperSupportComplex_singleComplex x)
    (representedAffineShortComplex B S hS x.T.left
      (ShortComplex.mk (X₁ := D.baseModule x e Sq.X₁) (X₂ := D.baseModule x e Sq.X₂)
        (X₃ := D.baseModule x e Sq.X₃)
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map Sq.f)
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map Sq.g)
        (Deformation.Artin.ringEquivShortComplex e Sq).zero))
    (representedAffineShortComplex_shortExact B S hS x.T.left
      (Deformation.Artin.ringEquivShortComplex_shortExact e hSq)))
    (add_comm 1 1))

section DataLemmas

variable [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)]

/-- Naturality of the composite identification, in a fixed degree. -/
theorem extGroup_trans_natural
    (L : DerivedCategory (ModuleCat.{u} (D.baseRing x)))
    (Ξ : ∀ (N : ModuleCat.{u} (D.baseRing x)) (i : ℤ),
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i ≃+
        ShiftedHom (D.singleObject x) (tensorPullbackComplexDerived (D.baseProjection x)
          (D.singleComplex x)
          ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
            ((representedAffineAssociated B S hS x.T.left).obj N))) i)
    (hΞnat : ∀ {N N' : ModuleCat.{u} (D.baseRing x)}
      (g : N ⟶ N') (i : ℤ) (y : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i),
      Ξ N' i (y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((DerivedCategory.singleFunctor _ 0).map g)) (zero_add i)) =
        Ξ N i y ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
          (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
            ((representedAffineAssociated B S hS x.T.left).map g))))⟦i⟧')
    (_hΞδ : ∀ {Sq : ShortComplex (ModuleCat.{u} (D.baseRing x))}
      (hSq : Sq.ShortExact) (i : ℤ)
      (y : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj Sq.X₃) i),
      Ξ Sq.X₁ (i + 1) (y.comp hSq.singleδ (add_comm 1 i)) =
        (Ξ Sq.X₃ i y).comp (tensorPullbackSingleDelta B S hS (D.baseProjection x)
          x.properSupport.choose (D.singleComplex x)
          (D.flatProperSupportComplex_singleComplex x)
          (representedAffineShortComplex B S hS x.T.left Sq)
          (representedAffineShortComplex_shortExact B S hS x.T.left hSq)) (add_comm 1 i))
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (Ψ' : ∀ M : ModuleCat.{u} A, ((Deformation.Artin.derivedCohomology A K n).obj M : Type u) ≃+
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj (D.baseModule x e M)) n)
    (h' : ∀ {M N : ModuleCat.{u} A} (g : M ⟶ N)
      (c : (Deformation.Artin.derivedCohomology A K n).obj M),
      Ψ' N ((Deformation.Artin.derivedCohomology A K n).map g c) =
        (Ψ' M c).comp (ShiftedHom.mk₀ (0 : ℤ) rfl ((DerivedCategory.singleFunctor _ 0).map
          ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map g))) (zero_add n))
    {M N : ModuleCat.{u} A} (g : M ⟶ N) (c : (Deformation.Artin.derivedCohomology A K n).obj M) :
    (((Ψ' N).trans (Ξ (D.baseModule x e N) n)).trans (D.extGroupEquiv x e N n).symm)
        ((Deformation.Artin.derivedCohomology A K n).map g c) =
      D.extGroupMap x e g n
        ((((Ψ' M).trans (Ξ (D.baseModule x e M) n)).trans (D.extGroupEquiv x e M n).symm) c) := by
  simp only [AddEquiv.trans_apply, extGroupMap_apply, AddEquiv.apply_symm_apply]
  exact congrArg (D.extGroupEquiv x e N n).symm
    ((congrArg (Ξ (D.baseModule x e N) n) (h' g c)).trans (hΞnat _ n _))

end DataLemmas

/-- The perfect complex of an object of `Coh_{X/Y}`, from given data of the conclusion of
`AlgebraicGeometry.Space.CoherentSituation.exists_isPseudoCoherentFrom_extEquiv`. -/
theorem exists_perfect_derivedCohomology_addEquiv_extGroup_of_data
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)]
    (L : DerivedCategory (ModuleCat.{u} (D.baseRing x)))
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom L (-3))
    (Ξ : ∀ (N : ModuleCat.{u} (D.baseRing x)) (i : ℤ),
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i ≃+
        ShiftedHom (D.singleObject x) (tensorPullbackComplexDerived (D.baseProjection x)
          (D.singleComplex x)
          ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
            ((representedAffineAssociated B S hS x.T.left).obj N))) i)
    (hΞnat : ∀ {N N' : ModuleCat.{u} (D.baseRing x)}
      (g : N ⟶ N') (i : ℤ) (y : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i),
      Ξ N' i (y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((DerivedCategory.singleFunctor _ 0).map g)) (zero_add i)) =
        Ξ N i y ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
          (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
            ((representedAffineAssociated B S hS x.T.left).map g))))⟦i⟧')
    (hΞδ : ∀ {Sq : ShortComplex (ModuleCat.{u} (D.baseRing x))}
      (hSq : Sq.ShortExact) (i : ℤ)
      (y : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj Sq.X₃) i),
      Ξ Sq.X₁ (i + 1) (y.comp hSq.singleδ (add_comm 1 i)) =
        (Ξ Sq.X₃ i y).comp (tensorPullbackSingleDelta B S hS (D.baseProjection x)
          x.properSupport.choose (D.singleComplex x)
          (D.flatProperSupportComplex_singleComplex x)
          (representedAffineShortComplex B S hS x.T.left Sq)
          (representedAffineShortComplex_shortExact B S hS x.T.left hSq)) (add_comm 1 i)) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A)), StacksDraft.Perfect.IsPerfect K ∧
      ∃ (Ψ₁ : ∀ M : ModuleCat.{u} A,
          ((Deformation.Artin.derivedCohomology A K 1).obj M : Type u) ≃+ D.extGroup x e M 1)
        (Ψ₂ : ∀ M : ModuleCat.{u} A,
          ((Deformation.Artin.derivedCohomology A K 2).obj M : Type u) ≃+ D.extGroup x e M 2),
        (∀ {M N : ModuleCat.{u} A} (g : M ⟶ N)
          (c : (Deformation.Artin.derivedCohomology A K 1).obj M),
          Ψ₁ N ((Deformation.Artin.derivedCohomology A K 1).map g c) =
            D.extGroupMap x e g 1 (Ψ₁ M c)) ∧
        (∀ {M N : ModuleCat.{u} A} (g : M ⟶ N)
          (c : (Deformation.Artin.derivedCohomology A K 2).obj M),
          Ψ₂ N ((Deformation.Artin.derivedCohomology A K 2).map g c) =
            D.extGroupMap x e g 2 (Ψ₂ M c)) ∧
        (∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
          (c : (Deformation.Artin.derivedCohomology A K 1).obj Sq.X₃),
          Ψ₂ Sq.X₁ (Deformation.Artin.boundaryMap A K hSq c) =
            D.extGroupDelta x e hSq (Ψ₁ Sq.X₃ c)) := by
  obtain ⟨K, hK, Ψ₁', Ψ₂', h₁, h₂, hδ⟩ :=
    Deformation.Artin.exists_perfect_shiftedHomEquiv_of_isPseudoCoherentFrom_of_ringEquiv e L hL
  refine ⟨K, hK, fun M => ((Ψ₁' M).trans (Ξ (D.baseModule x e M) 1)).trans
      (D.extGroupEquiv x e M 1).symm,
    fun M => ((Ψ₂' M).trans (Ξ (D.baseModule x e M) 2)).trans (D.extGroupEquiv x e M 2).symm,
    ?_, ?_, ?_⟩
  · exact fun g c => D.extGroup_trans_natural x e L Ξ hΞnat hΞδ K 1 Ψ₁' h₁ g c
  · exact fun g c => D.extGroup_trans_natural x e L Ξ hΞnat hΞδ K 2 Ψ₂' h₂ g c
  · intro Sq hSq c
    simp only [AddEquiv.trans_apply]
    refine congrArg (D.extGroupEquiv x e Sq.X₁ 2).symm ?_
    change _ = (D.extGroupEquiv x e Sq.X₃ 1 ((D.extGroupEquiv x e Sq.X₃ 1).symm _)).comp _ _
    rw [AddEquiv.apply_symm_apply]
    exact (congrArg (Ξ (D.baseModule x e Sq.X₁) 2) (hδ hSq c)).trans
      (hΞδ (Sq := (ShortComplex.mk (X₁ := D.baseModule x e Sq.X₁) (X₂ := D.baseModule x e Sq.X₂)
        (X₃ := D.baseModule x e Sq.X₃)
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map Sq.f)
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map Sq.g)
        (Deformation.Artin.ringEquivShortComplex e Sq).zero))
        (Deformation.Artin.ringEquivShortComplex_shortExact e hSq) 1 _)

/-- **The perfect complex of an object of `Coh_{X/Y}` over a Noetherian affine base.** There
are a perfect `K` in `D(A)` and additive bijections `Hⁿ(K ⊗ᴸ M) ≃+ Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃)` for
`n = 1, 2`, natural in the `A`-module `M` and carrying the connecting map of a short exact
sequence of `A`-modules to the connecting map of `Ext` groups. -/
theorem exists_perfect_derivedCohomology_addEquiv_extGroup
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)] :
    ∃ (K : DerivedCategory (ModuleCat.{u} A)), StacksDraft.Perfect.IsPerfect K ∧
      ∃ (Ψ₁ : ∀ M : ModuleCat.{u} A,
          ((Deformation.Artin.derivedCohomology A K 1).obj M : Type u) ≃+ D.extGroup x e M 1)
        (Ψ₂ : ∀ M : ModuleCat.{u} A,
          ((Deformation.Artin.derivedCohomology A K 2).obj M : Type u) ≃+ D.extGroup x e M 2),
        (∀ {M N : ModuleCat.{u} A} (g : M ⟶ N)
          (c : (Deformation.Artin.derivedCohomology A K 1).obj M),
          Ψ₁ N ((Deformation.Artin.derivedCohomology A K 1).map g c) =
            D.extGroupMap x e g 1 (Ψ₁ M c)) ∧
        (∀ {M N : ModuleCat.{u} A} (g : M ⟶ N)
          (c : (Deformation.Artin.derivedCohomology A K 2).obj M),
          Ψ₂ N ((Deformation.Artin.derivedCohomology A K 2).map g c) =
            D.extGroupMap x e g 2 (Ψ₂ M c)) ∧
        (∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
          (c : (Deformation.Artin.derivedCohomology A K 1).obj Sq.X₃),
          Ψ₂ Sq.X₁ (Deformation.Artin.boundaryMap A K hSq c) =
            D.extGroupDelta x e hSq (Ψ₁ Sq.X₃ c)) := by
  -- the components are extracted with `choose`: case analysis on this existential re-checks a
  -- body that is expensive to elaborate
  have hX := D.exists_isPseudoCoherentFrom_extEquiv x
  exact D.exists_perfect_derivedCohomology_addEquiv_extGroup_of_data x e hX.choose
    hX.choose_spec.1 hX.choose_spec.2.choose hX.choose_spec.2.choose_spec.1
    hX.choose_spec.2.choose_spec.2

end CoherentSituation

end AlgebraicGeometry.Space

end
