module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RelativeFrobeniusArrowSites07N5
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekCounitPullbackIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseQuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusFactorization07N5
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusTwistArrows

/-!
# Arrow 2 of the proof of [Stacks, Tag 07N5] on cohomology is the map of [Stacks, Tag 07QA]

The second arrow of the proof of [Stacks, Tag 07N5],

`F_{X/S₀}^* : RΓ(Cris(X^{(1)}/S), E^{(1)}) ⟶ RΓ(Cris(X/S), (F_X)^*_cris E)`,

is built in `SmallSite/FrobeniusTwistArrows.lean` as the derived comparison on the big
crystalline site, with module coefficients, of change of divided power base along the relative
Frobenius `F_{X/S₀} : X ⟶ X^{(1)}`.  The map whose kernel and cokernel [Stacks, Tag 07QB] bounds
is the pullback of [Stacks, Tag 07QA] on the small crystalline site with abelian coefficients,
`...SmallSite.crisModuleCohomologyMap`.  This file identifies the two on cohomology, so that the
bound of [Stacks, Tag 07QB] transfers to arrow 2.

## The argument

`...SmallSite.derivedChangeBaseBigGlobalSectionsMap_comp_isoTarget` is the instance of the
abstract comparison `Stacks.LerayPullbackComparison.derivedSquareMap_comp_targetIso` of
`Algebra/Homology/DerivedCategory/LerayPullbackComparison.lean`: the derived comparison of the
square on the big site, read through the restriction to the small site and the forgetful functor
to abelian groups, is the pullback on derived crystalline sections followed by the comparison
`f_cris^{-1} ⟶ f_cris^*` and the counit `i_!i^{-1}N ⟶ N`.  The underived input is
`...SmallSite.changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian`.  The counit is
invertible at the crystal `E^{(1)}`, by
`...SmallSite.isIso_crisModulePullback_map_moduleLowerShriekAdjunction_counit`.  Taking
cohomology, kernels and cokernels are compared elementwise (`AnnihilatedKerCoker`).

## Main results

* `annihilatedKerCoker_derivedChangeBaseBigGlobalSectionsMap` — for a general morphism of global
  crystalline situations.
* `relativeFrobeniusArrow07N6_annihilation_of_crisModuleCohomologyMap` — **arrow 2 inherits the
  bound of [Stacks, Tag 07QB]**: if in every degree a power of `p` annihilates the kernel and the
  cokernel of the map of [Stacks, Tag 07QA] for `F_{X/S₀}` at `E^{(1)}`, then in every degree a
  power of `p` annihilates the kernel and the cokernel of the cohomology of arrow 2.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u w w' wB wA wS

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Forgetting the action of the base ring preserves finite colimits; instance search does not
find this at the universes of the chapter, Mathlib stating the preservation of all colimits at a
module universe of the form `max w w'`. -/
local instance preservesFiniteColimits_forgetBaseAction (S : GlobalCrystallineSituation.{u}) :
    PreservesFiniteColimits (forgetBaseAction S) :=
  ⟨fun _ _ _ => inferInstance⟩

section Generic

variable {S S' : GlobalCrystallineSituation.{u}} (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{wB} (BigModuleSheaf S)] [HasDerivedCategory.{wB} (BigModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
  [HasDerivedCategory.{wS} (ModuleSheaf S)] [HasDerivedCategory.{wS} (ModuleSheaf S')]

/-- The abelian inverse image `f_cris^{-1}` is additive, being a left adjoint. -/
local instance additive_crisInverseImage : (crisInverseImage S S' fS fX hf).Additive :=
  (crisDirectImageAdjunction S S' fS fX hf).left_adjoint_additive

variable (S) in
omit [HasDerivedCategory.{wB} (BigModuleSheaf S)] in
/-- **`i^{-1}` carries an injective sheaf of modules on `CRIS(X/S)` to an abelian sheaf on
`Cris(X/S)` acyclic for global sections**: it is acyclic for the module-valued global sections,
`...SmallSite.rightAcyclic_moduleRestrictι_obj`, and the module-valued and abelian cohomology
agree, [Stacks, Tag 03FD]. -/
theorem rightAcyclic_bigRestrictToAbelian (I : BigModuleSheaf S) (hI : Injective I) :
    (globalSections S).rightAcyclic ((bigRestrictToAbelian S).obj I) :=
  (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat (globalSections S) _).2 fun n hn =>
    (isZero_moduleCohomology_iff S _ n).1
      ((Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat (baseModuleGlobalSections S) _).1
        (rightAcyclic_moduleRestrictι_obj S I hI) n hn)

/-- **`RΓ(CRIS(X/S), N)`, the `A`-action forgotten, is `RΓ(Cris(X/S), i^{-1}N)` of abelian
sheaves.** -/
def isoSource (N : BigModuleSheaf S') :
    (forgetBaseAction S').mapDerivedCategoryPlus.obj ((derivedBigModuleGlobalSections S').obj N) ≅
      (derivedGlobalSections S').obj ((bigRestrictToAbelian S').obj N) :=
  (Stacks.LerayPullbackComparison.splitIso (bigBaseModuleGlobalSections S')
        (forgetBaseAction S')).symm.app _ ≪≫
    (Stacks.LerayPullbackComparison.restrictionIso
      (bigBaseModuleGlobalSections S' ⋙ forgetBaseAction S')
      (bigRestrictToAbelian S') (globalSections S') (rightAcyclic_bigRestrictToAbelian S')
      (bigSectionsIsoAbelian S')).app _ ≪≫
    (globalSections S').rightDerivedFunctorPlus.mapIso
      ((bigRestrictToAbelian S').mapDerivedCategoryPlusObjSingleIso N)

/-- `bigSectionsIsoAbelian` after a restriction of scalars along
`...SmallSite.baseChangeRingHom`. -/
def bigSectionsIsoAbelianRestrictScalars :
    bigBaseModuleGlobalSections S ⋙ ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom fS) ⋙
        forgetBaseAction S' ≅ bigRestrictToAbelian S ⋙ globalSections S :=
  Functor.isoWhiskerLeft _ (restrictScalarsForgetIso fS) ≪≫ bigSectionsIsoAbelian S

/-- **`res_* RΓ(CRIS(X/S), M)`, the action forgotten, is `RΓ(Cris(X/S), i^{-1}M)` of abelian
sheaves**, for `M` the pullback of a sheaf of modules on `CRIS(X'/S')`. -/
def isoTarget (N : BigModuleSheaf S') :
    (forgetBaseAction S').mapDerivedCategoryPlus.obj
        ((ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom fS)).mapDerivedCategoryPlus.obj
          ((derivedBigModuleGlobalSections S).obj
            ((changeBaseBigModulePullback S S' fS fX hf).obj N))) ≅
      (derivedGlobalSections S).obj
        ((bigRestrictToAbelian S).obj ((changeBaseBigModulePullback S S' fS fX hf).obj N)) :=
  (Stacks.LerayPullbackComparison.targetIso
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom fS))
      (forgetBaseAction S') (rightAcyclic_bigRestrictToAbelian S)
      (bigSectionsIsoAbelianRestrictScalars fS)).app _ ≪≫
    (globalSections S).rightDerivedFunctorPlus.mapIso
      ((bigRestrictToAbelian S).mapDerivedCategoryPlusObjSingleIso
        ((changeBaseBigModulePullback S S' fS fX hf).obj N))

omit [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}] in
/-- Bookkeeping for `derivedChangeBaseBigGlobalSectionsMap_comp_isoTarget`, in arbitrary
categories. -/
private lemma finishGeneric {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (G : 𝒦 ⥤ 𝒦')
    {X₀ X₁ X₂ X₃ : 𝒦'} {Y Z W : 𝒦} (L : X₀ ⟶ G.obj W) (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (c : X₂ ⟶ X₃) (d : X₃ ⟶ G.obj Y) (x : Y ⟶ Z) (y : Z ⟶ W)
    (h : L = a ≫ b ≫ c ≫ d ≫ G.map (x ≫ y)) :
    L = (a ≫ b ≫ c) ≫ (d ≫ G.map x) ≫ G.map y := by
  rw [h, G.map_comp]
  simp only [Category.assoc]

/-- **The derived comparison along a change of divided power base is the pullback of
[Stacks, Tag 07QA]**: read through `isoSource` and `isoTarget`, it is
`...SmallSite.derivedModulePullbackMap` followed by the counit of `i_! ⊣ i^{-1}`. -/
theorem derivedChangeBaseBigGlobalSectionsMap_comp_isoTarget (N : BigModuleSheaf S') :
    (forgetBaseAction S').mapDerivedCategoryPlus.map
        (derivedChangeBaseBigGlobalSectionsMap fS fX hf N) ≫ (isoTarget fS fX hf N).hom =
      (isoSource N).hom ≫ derivedModulePullbackMap S S' fS fX hf ((moduleRestrictι S').obj N) ≫
        (derivedGlobalSections S).map
          ((toAbelianSheaf S).map (lowerShriekCounitPullback fS fX hf N)) := by
  have h := Stacks.LerayPullbackComparison.derivedSquareMap_comp_targetIso
    (crisDirectImageAdjunction S S' fS fX hf) (crisGlobalSectionsIso S S' fS fX hf)
    (rightAcyclic_bigRestrictToAbelian S') (rightAcyclic_bigRestrictToAbelian S)
    (changeBaseBigBaseGlobalSectionsTrans fS fX hf) (bigSectionsIsoAbelian S')
    (bigSectionsIsoAbelianRestrictScalars fS) (crisComparisonTrans fS fX hf)
    (changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian fS fX hf) N
  rw [derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap]
  exact finishGeneric (derivedGlobalSections S) _ _ _ _ _ _ _ h

end Generic

/-! ### Kernels and cokernels annihilated by an integer, elementwise -/

section Elementwise

/-- **The kernel and the cokernel of a map of abelian groups are annihilated by `m`**, read on
elements: `φ x = 0` forces `m • x = 0`, and `m` times any element of the target is in the image. -/
def AnnihilatedKerCoker {A B : AddCommGrpCat.{u + 1}} (φ : A ⟶ B) (m : ℤ) : Prop :=
  (∀ x : A, φ x = 0 → m • x = 0) ∧ ∀ y : B, ∃ x : A, m • y = φ x

/-- The annihilation of the kernel and of the cokernel by `m`, read on elements. -/
theorem annihilatedKerCoker_of_smul_id {A B : AddCommGrpCat.{u + 1}} (φ : A ⟶ B) (m : ℤ)
    (hk : m • 𝟙 (kernel φ) = 0) (hc : m • 𝟙 (cokernel φ) = 0) : AnnihilatedKerCoker φ m := by
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have hS := ShortComplex.exact_of_f_is_kernel (ShortComplex.mk (kernel.ι φ) φ
      (kernel.condition φ)) (kernelIsKernel φ)
    obtain ⟨z, rfl⟩ := (ShortComplex.ab_exact_iff _).1 hS x hx
    have h := ConcreteCategory.congr_hom (congrArg (· ≫ kernel.ι φ) hk) z
    simpa using h
  · have hS := ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk φ (cokernel.π φ)
      (cokernel.condition φ)) (cokernelIsCokernel φ)
    have h := ConcreteCategory.congr_hom (congrArg (cokernel.π φ ≫ ·) hc) y
    simp only [Preadditive.comp_zsmul, Category.comp_id, comp_zero] at h
    obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).1 hS (m • y) (by simpa using h)
    exact ⟨x, hx.symm⟩

/-- **The annihilation transfers along a commutative square of isomorphisms.** -/
theorem AnnihilatedKerCoker.of_comm {A B A' B' : AddCommGrpCat.{u + 1}} {φ : A ⟶ B}
    {ψ : A' ⟶ B'} {m : ℤ} (h : AnnihilatedKerCoker ψ m) (i₁ : A ≅ A') (i₂ : B ≅ B')
    (hw : φ ≫ i₂.hom = i₁.hom ≫ ψ) : AnnihilatedKerCoker φ m := by
  have hw' : ∀ x, i₂.hom (φ x) = ψ (i₁.hom x) := fun x => ConcreteCategory.congr_hom hw x
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have h0 : ψ (i₁.hom x) = 0 := by rw [← hw', hx, map_zero]
    have h1 := h.1 _ h0
    have h2 : i₁.hom (m • x) = 0 := by rw [map_zsmul, h1]
    have h3 := congrArg i₁.inv h2
    simpa using h3
  · obtain ⟨x, hx⟩ := h.2 (i₂.hom y)
    refine ⟨i₁.inv x, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso i₂.hom).1
    rw [map_zsmul, hx, hw']
    simp

/-- **Back to modules**: if the kernel and the cokernel of the underlying map of abelian groups of
a map of `R`-modules are annihilated by `m`, so are those of the map of modules. -/
theorem smul_id_kernel_cokernel_of_annihilatedKerCoker {R : Type*} [Ring R]
    {M N : ModuleCat.{u + 1} R} (φ : M ⟶ N) (m : ℕ)
    (h : AnnihilatedKerCoker ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map φ)
      (m : ℤ)) :
    m • 𝟙 (kernel φ) = 0 ∧ m • 𝟙 (cokernel φ) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [← cancel_mono (kernel.ι φ)]
    ext z
    have hz : φ (kernel.ι φ z) = 0 := by simp
    have := h.1 (kernel.ι φ z) hz
    simpa [Preadditive.nsmul_comp, natCast_zsmul] using this
  · rw [← cancel_epi (cokernel.π φ)]
    ext y
    obtain ⟨x, hx⟩ := h.2 y
    have hc : cokernel.π φ (φ x) = 0 := by simp
    have hx' : (m • y : N) = φ x := by simpa [natCast_zsmul] using hx
    simp [← map_nsmul, hx', hc]

end Elementwise

/-! ### The comparison on cohomology, for a general morphism of situations -/

section GenericCohomology

variable {S S' : GlobalCrystallineSituation.{u}} (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{wB} (BigModuleSheaf S)] [HasDerivedCategory.{wB} (BigModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
  [HasDerivedCategory.{wS} (ModuleSheaf S)] [HasDerivedCategory.{wS} (ModuleSheaf S')]

omit [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}] in
/-- The annihilation transfers along an isomorphism of functors to abelian groups. -/
private lemma annihilatedKerCoker_of_natIso {𝒦 : Type*} [Category* 𝒦]
    {F F' : 𝒦 ⥤ AddCommGrpCat.{u + 1}} (e : F ≅ F') {X Y : 𝒦} (f : X ⟶ Y) {m : ℤ}
    (h : AnnihilatedKerCoker (F.map f) m) : AnnihilatedKerCoker (F'.map f) m :=
  h.of_comm (e.app X).symm (e.app Y).symm (by simp)

omit [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}] in
/-- A functor carries an identity `a ≫ b = c ≫ d ≫ f` with `f` invertible to one of the form
of `AnnihilatedKerCoker.of_comm`. -/
private lemma map_comm_of_eq {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (G : 𝒦 ⥤ 𝒦')
    {X Y Z W V : 𝒦} (a : X ⟶ Y) (b : Y ⟶ V) (c : X ⟶ Z) (d : Z ⟶ W) (f : W ≅ V)
    (h : a ≫ b = c ≫ d ≫ f.hom) :
    G.map a ≫ G.map b ≫ G.map f.inv = G.map c ≫ G.map d := by
  rw [← G.map_comp, ← G.map_comp, ← Category.assoc, h, Category.assoc, Category.assoc,
    f.hom_inv_id, Category.comp_id, G.map_comp]

omit [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})] in
/-- **The kernel and the cokernel of the cohomology of the derived comparison along a change of
divided power base are annihilated by `m` as soon as those of the map of [Stacks, Tag 07QA]
are**, for a sheaf of modules `N` at which `lowerShriekCounitPullback` is invertible. -/
theorem annihilatedKerCoker_derivedChangeBaseBigGlobalSectionsMap (N : BigModuleSheaf S')
    (i : ℕ) (m : ℤ) (hκ : IsIso (lowerShriekCounitPullback fS fX hf N))
    (h : AnnihilatedKerCoker (crisModuleCohomologyMap S S' fS fX hf
      ((moduleRestrictι S').obj N) i) m) :
    AnnihilatedKerCoker ((forgetBaseAction S').map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)) (i : ℤ)).map
        (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap fS fX hf N)))) m := by
  -- step D: the map of [Stacks, Tag 07QA] is the cohomology of `derivedModulePullbackMap`
  have hD : AnnihilatedKerCoker ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1}
      (i : ℤ)).map (derivedModulePullbackMap S S' fS fX hf ((moduleRestrictι S').obj N))) m := by
    refine h.of_comm (homologyDerivedGlobalSectionsIsoObj S' _ i)
      (homologyDerivedGlobalSectionsIsoObj S _ i) ?_
    rw [crisModuleCohomologyMap_eq_derivedModulePullbackMap, Iso.hom_inv_id_assoc]
  -- step C: the derived identification
  have hC : AnnihilatedKerCoker ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1}
      (i : ℤ)).map ((forgetBaseAction S').mapDerivedCategoryPlus.map
        (derivedChangeBaseBigGlobalSectionsMap fS fX hf N))) m := by
    refine hD.of_comm ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).mapIso
      (isoSource N))
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).mapIso
        (isoTarget fS fX hf N) ≪≫
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).mapIso
          ((derivedGlobalSections S).mapIso
            (asIso ((toAbelianSheaf S).map (lowerShriekCounitPullback fS fX hf N))))).symm) ?_
    exact map_comm_of_eq _ _ _ _ _ _
      (derivedChangeBaseBigGlobalSectionsMap_comp_isoTarget fS fX hf N)
  -- step B: forgetting the action commutes with cohomology
  let e := (forgetBaseAction S').mapDerivedCategoryHomologyIso (i : ℤ)
  let e := (forgetBaseAction S').mapDerivedCategoryHomologyIso (i : ℤ)
  exact annihilatedKerCoker_of_natIso (Functor.isoWhiskerLeft DerivedCategory.Plus.ι e) _ hC

end GenericCohomology

/-! ### Arrow 2 of the proof of [Stacks, Tag 07N5] -/

section Twist

variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
  [HasDerivedCategory.{w} (Sheaf (smallTopology T.global) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (smallTopology (T.global.frobeniusTwistSituation T.prime_mem)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology T.global) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (opensTopology (T.global.frobeniusTwistSituation T.prime_mem)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- The two constructions of `X^{(1)}/S` agree, so the derived category of abelian sheaves on its
small crystalline site is the one assumed. -/
local instance arrowTwo_hasDerivedCategory_twistSmall :
    HasDerivedCategory.{w}
      (Sheaf (smallTopology T.frobeniusTwistSituation) AddCommGrpCat.{u + 1}) :=
  inferInstanceAs (HasDerivedCategory.{w}
    (Sheaf (smallTopology (T.global.frobeniusTwistSituation T.prime_mem)) AddCommGrpCat.{u + 1}))

/-- The two constructions of `X^{(1)}/S` agree, so the derived category of abelian sheaves on its
Zariski site is the one assumed. -/
local instance arrowTwo_hasDerivedCategory_twistOpens :
    HasDerivedCategory.{w'}
      (Sheaf (opensTopology T.frobeniusTwistSituation) AddCommGrpCat.{u + 1}) :=
  inferInstanceAs (HasDerivedCategory.{w'}
    (Sheaf (opensTopology (T.global.frobeniusTwistSituation T.prime_mem)) AddCommGrpCat.{u + 1}))

omit [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}] in
/-- A functor carries `a ≫ b ≫ c.hom` followed by `c.inv` to `a ≫ b`, in arbitrary
categories. -/
private lemma map_comp_comp_hom_inv {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (G : 𝒦 ⥤ 𝒦')
    {X Y Z W : 𝒦} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ≅ W) :
    G.map (a ≫ b ≫ c.hom) ≫ G.map c.inv = G.map a ≫ G.map b := by
  rw [← G.map_comp, Category.assoc, Category.assoc, c.hom_inv_id, Category.comp_id, G.map_comp]

omit [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}] in
/-- **The annihilation is unchanged by composing with isomorphisms on either side**, after a
functor to abelian groups. -/
theorem annihilatedKerCoker_map_comp_of_isIso {𝒦 : Type*} [Category* 𝒦]
    (G : 𝒦 ⥤ AddCommGrpCat.{u + 1}) {X Y Z W : 𝒦} (a : X ⟶ Y) (ha : IsIso a) (b : Y ⟶ Z)
    (c : Z ⟶ W) (hc : IsIso c) {m : ℤ} (h : AnnihilatedKerCoker (G.map b) m) :
    AnnihilatedKerCoker (G.map (a ≫ b ≫ c)) m :=
  have := ha
  have := hc
  h.of_comm (G.mapIso (asIso a)) (G.mapIso (asIso c)).symm
    (by simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, asIso_hom, asIso_inv,
      ← Functor.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id])

omit [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
  [HasDerivedCategory.{w} (Sheaf (smallTopology T.global) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (smallTopology (T.global.frobeniusTwistSituation T.prime_mem)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology T.global) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (opensTopology (T.global.frobeniusTwistSituation T.prime_mem)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}] in
/-- The counit of `i_! ⊣ i^{-1}` pulled back along the relative Frobenius is invertible at the
base change `E^{(1)}` of an `F`-crystal, `E^{(1)}` being quasi-coherent on the big site. -/
theorem isIso_lowerShriekCounitPullback_sigmaModulePullback (E : Crystalline.FCrystal T) :
    IsIso (lowerShriekCounitPullback (S := T.global) (S' := T.frobeniusTwistSituation)
      (𝟙 T.global.S) T.relativeFrobeniusToTwist
      T.toClosedFiber_comp_closedFiberMap_id
      ((bigModuleULift T.frobeniusTwistSituation).obj (T.sigmaModulePullback.obj E.crystal))) := by
  have hqc : (T.sigmaModulePullback.obj E.crystal).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_changeBaseModulePullback (S := T.frobeniusTwistSituation)
      (S' := T.global) T.specSigma T.twistProjection
      T.twistToClosedFiber_comp_closedFiberMap_specSigma E.crystal
      E.isFiniteLocallyFreeQuasicoherentCrystal.isQuasicoherentOnSite
  have := isIso_crisModulePullback_map_moduleLowerShriekAdjunction_counit (S := T.global)
    (S' := T.frobeniusTwistSituation) (𝟙 T.global.S)
    T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id _ hqc
  have h₁ : IsIso ((crisModulePullback.{u + 1} (S := T.global) (S' := T.frobeniusTwistSituation)
      (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id).map
        ((moduleLowerShriek T.frobeniusTwistSituation).map
          ((crisRestrictModulesIsoModuleRestrictι T.frobeniusTwistSituation).inv.app
            ((bigModuleULift T.frobeniusTwistSituation).obj
              (T.sigmaModulePullback.obj E.crystal)))))
    := Functor.map_isIso _ _
  unfold lowerShriekCounitPullback
  rw [Functor.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₁ this)
    ((crisRestrictModulesIsoModuleRestrictι T.global).app _).isIso_hom

omit [HasDerivedCategory.{w'} (Sheaf (opensTopology T.global) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (opensTopology (T.global.frobeniusTwistSituation T.prime_mem)) AddCommGrpCat.{u + 1})] in
/-- **Arrow 2 in a nonnegative degree `i`**: the kernel and the cokernel of the map of abelian
groups underlying `H^i` of `...SmallSite.relativeFrobeniusArrow07N6` are annihilated by `m` as soon
as those of the map of [Stacks, Tag 07QA] for the relative Frobenius at `E^{(1)}` are. -/
theorem annihilatedKerCoker_homology_relativeFrobeniusArrow07N6 (E : Crystalline.FCrystal T)
    (i : ℕ) (m : ℤ)
    (h : AnnihilatedKerCoker (crisModuleCohomologyMap T.global T.frobeniusTwistSituation
        (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id
        ((moduleRestrictι T.frobeniusTwistSituation).obj
          ((bigModuleULift T.frobeniusTwistSituation).obj (T.sigmaModulePullback.obj E.crystal)))
        i) m) :
    AnnihilatedKerCoker ((forget₂ (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤))
        AddCommGrpCat.{u + 1}).map ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) (i : ℤ)).map
            (relativeFrobeniusArrow07N6 T E))) m := by
  have hB := annihilatedKerCoker_derivedChangeBaseBigGlobalSectionsMap (S := T.global)
    (S' := T.frobeniusTwistSituation) (𝟙 T.global.S) T.relativeFrobeniusToTwist
    T.toClosedFiber_comp_closedFiberMap_id
    ((bigModuleULift T.frobeniusTwistSituation).obj (T.sigmaModulePullback.obj E.crystal)) i _
    (isIso_lowerShriekCounitPullback_sigmaModulePullback T E) h
  have hB' : AnnihilatedKerCoker ((DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) (i : ℤ) ⋙
        forget₂ (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) AddCommGrpCat.{u + 1}).map
      (derivedChangeBaseBigGlobalSectionsMap (S := T.global)
        (S' := T.frobeniusTwistSituation) (𝟙 T.global.S) T.relativeFrobeniusToTwist
        T.toClosedFiber_comp_closedFiberMap_id
        ((bigModuleULift T.frobeniusTwistSituation).obj
          (T.sigmaModulePullback.obj E.crystal)))) m :=
    hB
  unfold relativeFrobeniusArrow07N6 derivedRelativeFrobeniusRestrictGlobalSectionsMap
  refine annihilatedKerCoker_map_comp_of_isIso (DerivedCategory.Plus.ι ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) (i : ℤ) ⋙
      forget₂ (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
    _ (Iso.isIso_inv _) _ _ ?_ hB'
  exact IsIso.comp_isIso' (Iso.isIso_hom ((restrictScalarsIdDerivedPlusIso T.global).app _))
    (IsIso.comp_isIso' (Iso.isIso_hom ((derivedBigModuleGlobalSections T.global).mapIso
      ((frobeniusBigModulePullbackIso T).app _)))
      (Iso.isIso_hom (derivedRestrictModuleGlobalSectionsULiftIso T.global _)))

omit [HasDerivedCategory.{w'} (Sheaf (opensTopology T.global) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (opensTopology (T.global.frobeniusTwistSituation T.prime_mem)) AddCommGrpCat.{u + 1})] in
/-- **Arrow 2 of the proof of [Stacks, Tag 07N5] inherits the bound of [Stacks, Tag 07QB].**  If
in every degree some power of `p` annihilates the kernel and the cokernel of the map of
[Stacks, Tag 07QA] for the relative Frobenius `F_{X/S₀} : X ⟶ X^{(1)}` at the restriction of
`E^{(1)}` to `Cris(X^{(1)}/S)`,

`F_{X/S₀}^* : H^i(Cris(X^{(1)}/S), E^{(1)}) ⟶ H^i(Cris(X/S), F_{X/S₀, cris}^* E^{(1)})`,

then in every degree some power of `p` annihilates the kernel and the cokernel of the map arrow 2,
`...SmallSite.relativeFrobeniusArrow07N6`, induces on cohomology.

The two maps are identified on cohomology by
`annihilatedKerCoker_derivedChangeBaseBigGlobalSectionsMap`: the derived comparison on the big
site of arrow 2 and the pullback of [Stacks, Tag 07QA] on the small site agree after the unit of
the right derived functor (`rightDerived_ext`), and the target of the latter is identified with
that of the former by the counit of `i_! ⊣ i^{-1}`, invertible at the crystal `E^{(1)}`
(`isIso_lowerShriekCounitPullback_sigmaModulePullback`).  In negative degrees both cohomology
groups of arrow 2 vanish. -/
theorem relativeFrobeniusArrow07N6_annihilation_of_crisModuleCohomologyMap
    (E : Crystalline.FCrystal T)
    (h : ∀ n : ℕ, ∃ k : ℕ,
      ((T.global.p : ℤ) ^ k) • 𝟙 (kernel (crisModuleCohomologyMap T.global
        (T.global.frobeniusTwistSituation T.prime_mem) (𝟙 T.global.S)
        (T.global.relativeFrobeniusToTwist T.prime_mem)
        (T.global.toClosedFiber_comp_closedFiberMap_id T.prime_mem)
        ((moduleULift _).obj (restrictSheafOfModules (T.sigmaModulePullback.obj E.crystal)))
          n)) = 0 ∧
      ((T.global.p : ℤ) ^ k) • 𝟙 (cokernel (crisModuleCohomologyMap T.global
        (T.global.frobeniusTwistSituation T.prime_mem) (𝟙 T.global.S)
        (T.global.relativeFrobeniusToTwist T.prime_mem)
        (T.global.toClosedFiber_comp_closedFiberMap_id T.prime_mem)
        ((moduleULift _).obj (restrictSheafOfModules (T.sigmaModulePullback.obj E.crystal)))
          n)) = 0)
    (n : ℤ) : ∃ k : ℕ,
      (T.global.p ^ k) • 𝟙 (kernel ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) n).map
            (relativeFrobeniusArrow07N6 T E))) = 0 ∧
      (T.global.p ^ k) • 𝟙 (cokernel ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) n).map
            (relativeFrobeniusArrow07N6 T E))) = 0 := by
  refine (lt_or_ge n 0).elim (fun hn => ⟨0, ?_, ?_⟩) (fun hn => ?_)
  · have hs : IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) n).obj
          (DerivedCategory.Plus.ι.obj (twistDerivedGlobalSectionsPlus T E.crystal))) :=
      isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg
        (S := T.frobeniusTwistSituation)
        (restrictSheafOfModules (T.sigmaModulePullback.obj E.crystal))
        n hn
    exact (IsZero.of_mono (kernel.ι _) hs).eq_of_src _ _
  · have ht : IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) n).obj
          (frobeniusPullbackDerivedGlobalSections T E)) :=
      isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg (S := T.global)
        ((crisRestrictModules.{u} T.global).obj (T.frobeniusModulePullback.obj E.crystal)) n hn
    exact (IsZero.of_epi (cokernel.π _) ht).eq_of_src _ _
  · refine (h n.toNat).elim fun k hkc => ?_
    have hk := hkc.1
    have hc := hkc.2
    refine ⟨k, smul_id_kernel_cokernel_of_annihilatedKerCoker _ _ ?_⟩
    have hE : AnnihilatedKerCoker (crisModuleCohomologyMap T.global T.frobeniusTwistSituation
        (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id
        ((moduleRestrictι T.frobeniusTwistSituation).obj
          ((bigModuleULift T.frobeniusTwistSituation).obj (T.sigmaModulePullback.obj E.crystal)))
        n.toNat) ((T.global.p ^ k : ℕ) : ℤ) := by
      rw [Nat.cast_pow]
      exact annihilatedKerCoker_of_smul_id _ _ hk hc
    have hI := annihilatedKerCoker_homology_relativeFrobeniusArrow07N6 T E n.toNat _ hE
    let e := eqToIso (congrArg (DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤))) (Int.toNat_of_nonneg hn).symm)
    exact annihilatedKerCoker_of_natIso (Functor.isoWhiskerRight e.symm (forget₂ _ _)) _ hI

end Twist

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
