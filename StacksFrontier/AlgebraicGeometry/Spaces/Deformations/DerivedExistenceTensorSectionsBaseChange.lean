module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceTensorSectionsLimit

/-!
# Stacks 0DIM: `RΓ(Xₙ, Kₙ ⊗^L E|_{Xₙ}) = RΓ(X, K ⊗^L E) ⊗^L_A Aₙ`

In Situation [Stacks, Tag 0DIK] let `K = DQ_X(R lim Kₙ)` (Stacks 0DIL) and `E` perfect on `X`,
`M = RΓ(X, K ⊗^L E)`. The canonical map `cₙ : M ⊗^L_A Aₙ ⟶ RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)` (the base change
map of `RΓ`, then Stacks 07A4 and `Lpₙ^*E ⊗^L τₙ`, with `τₙ : Lpₙ^* K ⟶ Kₙ` the adjoint of the
projection) is an isomorphism, and `M` is pseudo-coherent.

## Main definitions

* `SeparatedDerivedExistenceSystem.stageTensorSectionsBaseChange`: the canonical map `cₙ`.

## Main results

* `SeparatedDerivedExistenceSystem.isIso_stageTensorSectionsBaseChange`: `cₙ` is an isomorphism for
  `E`
  perfect.
* `SeparatedDerivedExistenceSystem.isIso_stageSections_map_tensor_coheratorLimitPullbackMap`:
  `RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L τₙ)` is invertible for `E` perfect.
* `SeparatedDerivedExistenceSystem.isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange`:
  [Stacks, Tag 0DIM].

## References

* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace StacksDraft.DerivedInverseLimit

attribute [local instance] HasDerivedCategory.standard

/-- **The base change comparison of 0CQF is natural in its source.** -/
theorem derivedBaseChangeComparison_comp {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {X X' : DerivedCategory (ModuleCat.{u} R)}
    {Y : DerivedCategory (ModuleCat.{u} S)} (a : X' ⟶ X)
    (g : X ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj Y) :
    derivedBaseChangeComparison.{u, u, u} f (a ≫ g) =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f).functor.map a ≫ derivedBaseChangeComparison.{u, u, u} f g := by
  rw [derivedBaseChangeComparison_eq_adjunction_homEquiv_symm,
    derivedBaseChangeComparison_eq_adjunction_homEquiv_symm,
    Adjunction.homEquiv_naturality_left_symm]

/-- `IsIso` of a base change comparison is insensitive to rewriting `p ≫ q ≫ r` as `b`. -/
theorem isIso_derivedBaseChangeComparison_of_comp_eq {R : Type u} {S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) {X₀ X₁ X₂ Z : DerivedCategory (ModuleCat.{u} R)}
    {Y : DerivedCategory (ModuleCat.{u} S)} (p : X₀ ⟶ X₁) (q : X₁ ⟶ X₂) (r : X₂ ⟶ Z)
    (b : X₀ ⟶ Z) (g : Z ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj Y)
    (h : p ≫ q ≫ r = b)
    (hi : IsIso (derivedBaseChangeComparison.{u, u, u} f ((p ≫ q) ≫ r ≫ g))) :
    IsIso (derivedBaseChangeComparison.{u, u, u} f (b ≫ g)) := by
  subst h
  simpa only [Category.assoc] using hi

/-- **A map out of a base change whose transpose is `a ≫ b ≫ g`, with `a` invertible and the base
change comparison of `b ≫ g` invertible, is invertible.** -/
theorem isIso_of_homEquiv_eq_comp {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {X X' Z : DerivedCategory (ModuleCat.{u} R)}
    {Y : DerivedCategory (ModuleCat.{u} S)}
    (c : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      f).functor.obj X ⟶ Y) (a : X ⟶ X') (b : X' ⟶ Z)
    (g : Z ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj Y)
    (hc : (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction f).homEquiv _ _ c =
      a ≫ b ≫ g) (ha : IsIso a)
    (hg : IsIso (derivedBaseChangeComparison.{u, u, u} f (b ≫ g))) : IsIso c := by
  have e : c = derivedBaseChangeComparison.{u, u, u} f (a ≫ b ≫ g) := by
    rw [derivedBaseChangeComparison_eq_adjunction_homEquiv_symm, ← hc]
    exact (Equiv.symm_apply_apply _ _).symm
  rw [e, derivedBaseChangeComparison_comp]
  exact IsIso.comp_isIso' inferInstance hg

end StacksDraft.DerivedInverseLimit

namespace Stacks.CategoryTheory.TowerStep

universe w₁ w₂ w₃ w₄ t₁ t₂ t₃ t₄

section OneSquare

variable {𝒳 : Type t₁} {𝒳' : Type t₂} {𝒜 : Type t₃} {𝒜' : Type t₄}
  [Category.{w₁} 𝒳] [Category.{w₂} 𝒳'] [Category.{w₃} 𝒜] [Category.{w₄} 𝒜']
  {Lf : 𝒜 ⥤ 𝒳} {Γ : 𝒳 ⥤ 𝒜} {Lf' : 𝒜' ⥤ 𝒳'} {Γ' : 𝒳' ⥤ 𝒜'} {Lg : 𝒜 ⥤ 𝒜'} {Lh : 𝒳 ⥤ 𝒳'}

/-- **The canonical map of one square at a tensor product**, `Lg Γ(E ⊗ K) ⟶ Γ'(Lh E ⊗ K')`:
the base change map of the square `e` followed by `Γ'` of `μ` and `Lh E ⊗ φ`. -/
def baseChangeTensorRight (adjf : Lf ⊣ Γ) (adjf' : Lf' ⊣ Γ') (e : Lg ⋙ Lf' ≅ Lf ⋙ Lh)
    (T : 𝒳 ⥤ 𝒳 ⥤ 𝒳) (T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳')
    (μ : Functor.uncurry.obj T ⋙ Lh ⟶ Lh.prod Lh ⋙ Functor.uncurry.obj T') (E : 𝒳)
    {K : 𝒳} {K' : 𝒳'} (φ : Lh.obj K ⟶ K') :
    Lg.obj (Γ.obj ((T.obj E).obj K)) ⟶ Γ'.obj ((T'.obj (Lh.obj E)).obj K') :=
  BaseChange.map adjf adjf' e (Iso.refl _) ((T.obj E).obj K) ≫
    Γ'.map (μ.app (E, K) ≫ (T'.obj (Lh.obj E)).map φ)

/-- **The transpose of `baseChangeTensorRight`** is `Γ(E ⊗ z)` followed by `towerSectionsHom`,
for `φ` with adjoint `z ≫ β⁻¹`. -/
theorem homEquiv_baseChangeTensorRight {r : 𝒜' ⥤ 𝒜} {Rh : 𝒳' ⥤ 𝒳} (adjf : Lf ⊣ Γ)
    (adjf' : Lf' ⊣ Γ') (ag : Lg ⊣ r) (ah : Lh ⊣ Rh) (e : Lg ⋙ Lf' ≅ Lf ⋙ Lh)
    (T : 𝒳 ⥤ 𝒳 ⥤ 𝒳) (T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳')
    (μ : Functor.uncurry.obj T ⋙ Lh ⟶ Lh.prod Lh ⋙ Functor.uncurry.obj T') (E : 𝒳)
    {K : 𝒳} {K' : 𝒳'} (φ : Lh.obj K ⟶ K')
    (pf : T.flip.obj (Rh.obj K') ⟶ Lh ⋙ T'.flip.obj K' ⋙ Rh)
    (hpf : pf.app E = ProjectionFormula.adjunctionTensorMapSnd ah (Functor.uncurry.obj T)
      (Functor.uncurry.obj T') μ E K')
    {P₀ : 𝒳' ⥤ 𝒳} (β : Rh ≅ P₀) (z : K ⟶ P₀.obj K')
    (hφ : ah.homEquiv _ _ φ = z ≫ β.inv.app K') :
    ag.homEquiv _ _ (baseChangeTensorRight adjf adjf' e T T' μ E φ) =
      Γ.map ((T.obj E).map z) ≫ towerSectionsHom Γ Γ' r T T' Lh Rh K' pf
        (conjugateEquiv (adjf.comp ah) (ag.comp adjf') e.hom) β E := by
  have hT := BaseChange.homEquiv_map_comp_tensor_curried adjf adjf' ag ah e T T' μ E K
    (𝟙 (Lh.obj E)) K' φ
  rw [hφ, ← hpf] at hT
  have h1 : ∀ Y : 𝒳', (T'.map (𝟙 (Lh.obj E))).app Y = 𝟙 _ := fun Y ↦ by
    rw [CategoryTheory.Functor.map_id]
    rfl
  have h2 : Rh.map ((T'.map (𝟙 (Lh.obj E))).app K') = 𝟙 _ := by
    rw [h1 K']
    exact Rh.map_id _
  unfold baseChangeTensorRight towerSectionsHom sectionsHom
  rw [← Category.id_comp ((T'.obj (Lh.obj E)).map φ), ← h1 (Lh.obj K), hT, h2]
  dsimp only [Functor.comp_obj, Functor.flip_obj_obj, Functor.uncurry_obj_obj]
  simp only [Category.comp_id, Functor.map_comp, Category.assoc]

/-- If `baseChangeTensorRight`, its base change map and `μ` are invertible, so is
`Γ'(Lh E ⊗ φ)`. -/
theorem isIso_map_of_isIso_baseChangeTensorRight (adjf : Lf ⊣ Γ) (adjf' : Lf' ⊣ Γ')
    (e : Lg ⋙ Lf' ≅ Lf ⋙ Lh) (T : 𝒳 ⥤ 𝒳 ⥤ 𝒳) (T' : 𝒳' ⥤ 𝒳' ⥤ 𝒳')
    (μ : Functor.uncurry.obj T ⋙ Lh ⟶ Lh.prod Lh ⋙ Functor.uncurry.obj T') (E : 𝒳)
    {K : 𝒳} {K' : 𝒳'} (φ : Lh.obj K ⟶ K')
    (h : IsIso (baseChangeTensorRight adjf adjf' e T T' μ E φ))
    (hbc : IsIso (BaseChange.map adjf adjf' e (Iso.refl _) ((T.obj E).obj K)))
    (hμ : IsIso μ) : IsIso (Γ'.map ((T'.obj (Lh.obj E)).map φ)) := by
  unfold baseChangeTensorRight at h
  have h₁ : IsIso (Γ'.map (μ.app (E, K) ≫ (T'.obj (Lh.obj E)).map φ)) :=
    IsIso.of_isIso_comp_left (BaseChange.map adjf adjf' e (Iso.refl _) ((T.obj E).obj K)) _
  rw [Functor.map_comp] at h₁
  exact IsIso.of_isIso_comp_left (Γ'.map (μ.app (E, K))) _

end OneSquare

end Stacks.CategoryTheory.TowerStep

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **The shift structure of `Ψ = RΓ(X, E ⊗^L -)`**, composed from those of `E ⊗^L -`, `Rf_*`
and `RΓ(Spec A, -)`. -/
abbrev limitTensorSectionsCommShift
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left) :
    (D.limitTensorSections E).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ ((smallEtaleDerivedTensor D.B (limitBase D.system)
      D.containsLimitBase D.X.left).obj E) D.limitSectionsFunctor ℤ _ _ _ _
    ((smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
      D.X.left).commShift_right E)
    (@Functor.CommShift.comp _ _ _ _ _ _ (derivedModulePushforward D.B (limitBase D.system)
        D.containsLimitBase D.X.hom) (representedAffineDerivedSections D.B (limitBase D.system)
        D.containsLimitBase (limitBaseObject D.system D.B D.containsLimitBase)) ℤ _ _ _ _
      (inferInstance : (derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
        D.X.hom).CommShift ℤ)
      (inferInstance : (representedAffineDerivedSections D.B (limitBase D.system)
        D.containsLimitBase (limitBaseObject D.system D.B D.containsLimitBase)).CommShift ℤ))

/-- **`Ψ = RΓ(X, E ⊗^L -)` is triangulated.** -/
theorem limitTensorSections_isTriangulated
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left) :
    letI := D.limitTensorSectionsCommShift E
    (D.limitTensorSections E).IsTriangulated := by
  let hT : ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).obj
      E).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
      D.X.left).commShift_right E
  have hTtri : ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
      D.X.left).obj E).IsTriangulated :=
    (smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
      D.X.left).exact_right E
  let hRf : (derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
      D.X.hom).CommShift ℤ := inferInstance
  let hRΓ : (representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).CommShift ℤ := inferInstance
  let h₁ : D.limitSectionsFunctor.CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ (derivedModulePushforward D.B (limitBase D.system)
        D.containsLimitBase D.X.hom) (representedAffineDerivedSections D.B (limitBase D.system)
        D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)) ℤ _ _ _ _ hRf hRΓ
  have : D.limitSectionsFunctor.IsTriangulated := ⟨fun Tr hTr ↦
    Pretriangulated.isomorphic_distinguished _
    ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).map_distinguished _
          ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          D.X.hom).map_distinguished Tr hTr)) _
      ((@Functor.mapTriangleCompIso _ _ _ _ _ _ _ _ _ (derivedModulePushforward D.B (limitBase
          D.system) D.containsLimitBase D.X.hom) hRf (representedAffineDerivedSections D.B
          (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)) hRΓ).app Tr)⟩
  let h₂ : (D.limitTensorSections E).CommShift ℤ := D.limitTensorSectionsCommShift E
  exact ⟨fun Tr hTr ↦ Pretriangulated.isomorphic_distinguished _
    (D.limitSectionsFunctor.map_distinguished _ (hTtri.map_distinguished Tr hTr)) _
      ((@Functor.mapTriangleCompIso _ _ _ _ _ _ _ _ _ ((smallEtaleDerivedTensor D.B (limitBase
          D.system) D.containsLimitBase D.X.left).obj E) hT D.limitSectionsFunctor h₁).app Tr)⟩


section Coherator

variable (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).FullSubcategory)
  (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)

/-- **The adjoint of `τₙ : Lpₙ^* K ⟶ Kₙ` along `Lpₙ^* ⊣ Rpₙ,*`** is the projection
`K ⟶ Rpₙ,* Kₙ`, read through `Rpₙ,* ≅ Rjₙ,*`. -/
theorem smallEtaleDerivedModuleAdjunction_homEquiv_coheratorLimitPullbackMap (n : ℕ) :
    (smallEtaleDerivedModuleAdjunction D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).homEquiv _ _
        (D.coheratorLimitPullbackMap DQ adj n) =
      D.coheratorLimitProjection DQ adj n ≫
        (D.stageToposDerivedPushforwardIso n).inv.app (D.K n) := by
  change (D.stageToposDerivedAdjunction n).homEquiv _ _
    (((D.stageAdjunction n).homEquiv _ _).symm (D.coheratorLimitProjection DQ adj n)) = _
  unfold stageAdjunction
  exact (congrArg ((D.stageToposDerivedAdjunction n).homEquiv _ _)
    (Adjunction.homEquiv_ofNatIsoRight_symm_apply (D.stageToposDerivedAdjunction n)
      (D.stageToposDerivedPushforwardIso n) (D.coheratorLimitProjection DQ adj n))).trans
    (Equiv.apply_symm_apply _ _)

/-- **The canonical map `cₙ : M ⊗^L_A Aₙ ⟶ RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)` of Stacks 0DIM**, with
`M = RΓ(X, E ⊗^L K)` and `K = DQ_X(R lim Kₙ)`: the base change map of `RΓ` along
`Spec Aₙ ⟶ Spec A`, then `RΓ(Xₙ, -)` of Stacks 07A4 and of `Lpₙ^*E ⊗^L τₙ`. -/
def stageTensorSectionsBaseChange (E : smallEtaleToposDerivedCategory D.X.left) (n : ℕ) :=
  Stacks.CategoryTheory.TowerStep.baseChangeTensorRight
    (Γ := affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase D.X.hom)
    (Γ' := affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
    (Lh := smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
    (affineBaseDerivedSectionsAdjunction D.B (limitBase D.system) D.containsLimitBase D.X.hom)
    (affineBaseDerivedSectionsAdjunction D.B (limitBase D.system) D.containsLimitBase
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
    (affineBaseDerivedSectionsSquareIso D.B (limitBase D.system) D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip.w)
    (smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
      (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
    (smallEtaleDerivedPullbackTensorIso
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).hom E
    (D.coheratorLimitPullbackMap DQ adj n)

/-- **The transpose of `cₙ`** is `RΓ(X, E ⊗^L -)` of the projection `K ⟶ Rjₙ,* Kₙ`, followed by
`RΓ(X, E ⊗^L Rpₙ,* Kₙ) ≅ res Mₙ`. -/
theorem homEquiv_stageTensorSectionsBaseChange (E : smallEtaleToposDerivedCategory D.X.left)
    (n : ℕ) :
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
        (representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
          (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom).homEquiv
        _ _ (D.stageTensorSectionsBaseChange DQ adj E n) =
      (affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase D.X.hom).map
          (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).obj
            E).map (D.coheratorLimitProjection DQ adj n)) ≫
        D.towerTensorSectionsHom E n :=
  Stacks.CategoryTheory.TowerStep.homEquiv_baseChangeTensorRight _ _ _ _ _ _ _ _ _ _
    (smallEtaleProjectionFormulaSndNatTrans
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) (D.K n)) rfl
    (D.stageToposDerivedPushforwardIso n) (D.coheratorLimitProjection DQ adj n)
    (D.smallEtaleDerivedModuleAdjunction_homEquiv_coheratorLimitPullbackMap DQ adj n)

/-- **`cₙ` is an isomorphism** for `E` perfect ([Stacks, Tag 0DIM], second half). -/
theorem isIso_stageTensorSectionsBaseChange (hpc : D.StageSectionsPseudoCoherent)
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E) (n : ℕ) :
    IsIso (D.stageTensorSectionsBaseChange DQ adj E n) := by
  let := D.limitTensorSectionsCommShift E
  have := D.limitTensorSections_isTriangulated E
  have _ : PreservesLimitsOfSize.{0, 0} (D.limitTensorSections E) :=
    (D.limitTensorSectionsAdjunction E hE).rightAdjoint_preservesLimits
  let h : HasProduct fun n : ℕ ↦ (D.limitTensorSections E).obj (D.spaceTower.obj ⟨n⟩) :=
    ⟨⟨_, isLimitOfHasProductOfPreservesLimit (D.limitTensorSections E)
      (fun n : ℕ ↦ D.spaceTower.obj ⟨n⟩)⟩⟩
  obtain ⟨δ, hT⟩ := Stacks.Injectives.isDerivedLimit_map_of_preservesProduct
    (D.limitTensorSections E) D.spaceTower D.derivedLimit D.derivedLimitToProduct
    D.exists_distTriang_derivedLimitToProduct
  have hq := qcohDerived_of_isPerfect _ _ _ _ _ hE
  have hc := (D.isPseudoCoherent_and_isIso_of_distTriang E hpc hE
    (fun n ↦ (D.limitTensorSections E).obj (D.spaceTower.obj ⟨n⟩))
    (fun n ↦ (D.limitTensorSections E).map (D.spaceTower.map (homOfLE (Nat.le_succ n)).op))
    (fun n ↦ D.towerTensorSectionsHom E n) (he' := fun n ↦ D.isIso_towerTensorSectionsHom E hq n)
    (fun n ↦ D.limitTensorSections_map_towerTensorSectionsHom E n)
    ((D.limitTensorSections E).obj D.derivedLimit) _ δ hT).2 n
  have e₁ : (D.limitTensorSections E).map D.derivedLimitToProduct ≫
      piComparison (D.limitTensorSections E) (fun n : ℕ ↦ D.spaceTower.obj ⟨n⟩) ≫
        Pi.π (fun n : ℕ ↦ (D.limitTensorSections E).obj (D.spaceTower.obj ⟨n⟩)) n =
      (D.limitTensorSections E).map (D.derivedLimitProjection n) := by
    rw [piComparison_comp_π, ← Functor.map_comp]
    rfl
  have hg := StacksDraft.DerivedInverseLimit.isIso_derivedBaseChangeComparison_of_comp_eq _ _ _ _
    _ (D.towerTensorSectionsHom E n) e₁ hc
  exact StacksDraft.DerivedInverseLimit.isIso_of_homEquiv_eq_comp _ _
    ((D.limitTensorSections E).map (adj.counit.app D.derivedLimit))
    ((D.limitTensorSections E).map (D.derivedLimitProjection n)) (D.towerTensorSectionsHom E n)
    ((D.homEquiv_stageTensorSectionsBaseChange DQ adj E n).trans
      (Functor.map_comp_assoc (D.limitTensorSections E) _ _ _))
    (Adjunction.isIso_map_counit_app_of_forall adj (D.limitTensorSectionsAdjunction E hE)
      (D.qcohDerived_limitTensorSections_leftAdjoint_obj E hE) D.derivedLimit) hg

/-- **`RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L τₙ)` is invertible** for `E` perfect: `cₙ` is, and so is its
first factor, the base change map of `RΓ` along `Spec Aₙ ⟶ Spec A` (`X` is flat over `A`, so
`X` and `Spec Aₙ` are Tor independent over `Spec A`). -/
theorem isIso_stageSections_map_tensor_coheratorLimitPullbackMap
    (hpc : D.StageSectionsPseudoCoherent) (n : ℕ)
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E) :
    IsIso ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
        (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) ⋙
      representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
        (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
      (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
        ((D.stageDerivedPullback n).obj E)).map (D.coheratorLimitPullbackMap DQ adj n))) := by
  have hq := qcohDerived_of_isPerfect _ _ _ _ _ hE
  exact Stacks.CategoryTheory.TowerStep.isIso_map_of_isIso_baseChangeTensorRight
    _ _ _ _ _ _ _ _
    (D.isIso_stageTensorSectionsBaseChange DQ adj hpc E hE n)
    (isIso_affineBaseDerivedSectionsBaseChangeMap D.B (limitBase D.system) D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip
      D.finitePresentation.2.1 D.finitePresentation.2.2
      (torIndependent_of_isFlat_left _ _ D.flat) _
      (qcohDerived_smallEtaleDerivedTensor _ _ _ hq (DQ.obj D.derivedLimit).property))
    (Iso.isIso_hom _)

end Coherator

/-- **[Stacks, Tag 0DIM], for `X` only separated over `A`, given the pseudo-coherence of the
`Mₙ`.** In the situation of `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem` let `K =
DQ_X(R lim Kₙ)` be the object of
[Stacks, Tag 0DIL] and `E` a perfect object of `D(𝒪_X)`. Then `M = RΓ(X, E ⊗^L K)` is a
pseudo-coherent object of `D(A)`, and for every `n` the canonical map
`cₙ : M ⊗^L_A Aₙ ⟶ RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)` (the base change map of `RΓ`, then Stacks 07A4 and
`Lpₙ^*E ⊗^L τₙ`, with `τₙ : Lpₙ^*K ⟶ Kₙ` adjoint to the projection) is an isomorphism in
`D(Aₙ)`. Here `K` is `D.quasicoherentLimit`, with `R lim Kₙ = D.derivedLimit` and `DQ_X` the
right adjoint `D.coherator` of the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`. -/
theorem isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange
    (hpc : D.StageSectionsPseudoCoherent)
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((D.limitTensorSections E).obj ((spaceQuasicoherentProp D.B (limitBase D.system)
          D.containsLimitBase D.X.left).ι.obj D.quasicoherentLimit)) ∧
      ∀ n : ℕ, IsIso (D.stageTensorSectionsBaseChange D.coherator D.coheratorAdjunction E n) := by
  obtain ⟨h, hK⟩ := D.isDerivedLimit_quasicoherentLimit
  exact ⟨D.isPseudoCoherent_limitTensorSections_of_isDerivedLimit hpc h _ hK E hE,
    fun n ↦ D.isIso_stageTensorSectionsBaseChange D.coherator D.coheratorAdjunction hpc E hE n⟩

end SeparatedDerivedExistenceSystem

namespace DerivedExistenceSystem

/-- **[Stacks, Tag 0DIM].** In Situation 0DIK let `K = DQ_X(R lim Kₙ)` be the object of
[Stacks, Tag 0DIL] and `E` a perfect object of `D(𝒪_X)`. Then `M = RΓ(X, E ⊗^L K)` is a
pseudo-coherent object of `D(A)`, and for every `n` the canonical map
`cₙ : M ⊗^L_A Aₙ ⟶ RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)` (the base change map of `RΓ`, then Stacks 07A4 and
`Lpₙ^*E ⊗^L τₙ`, with `τₙ : Lpₙ^*K ⟶ Kₙ` adjoint to the projection) is an isomorphism in
`D(Aₙ)`. Here `K` is `D.quasicoherentLimit`, with `R lim Kₙ = D.derivedLimit` and `DQ_X` the
right adjoint `D.coherator` of the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`. -/
@[stacks 0DIM "the full statement: for every perfect E, M = RΓ(X, E ⊗^L K) is pseudo-coherent \
and the canonical map M ⊗^L_A Aₙ ⟶ RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ) is an isomorphism in D(Aₙ) for every n. \
D is Situation 0DIK (DerivedExistenceSystem), whose fields are only the situation's data and \
hypotheses: the rings Aₙ with surjective transitions with locally nilpotent kernels, the fppf \
site containing Spec A and every Spec Aₙ, X proper, flat and of finite presentation over A, the \
pseudo-coherent Kₙ, and the comparison isomorphisms Liₙ^* Kₙ₊₁ ≅ Kₙ; no result is a field. \
K = DQ_X(R lim Kₙ) is the object of 0DIL, built from the coherator (the right adjoint of \
D_QCoh(𝒪_X) ⥤ D(𝒪_X)) and a derived limit, both constructed and not assumed"]
theorem isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange (D : DerivedExistenceSystem.{u})
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((D.toSeparated.limitTensorSections E).obj ((spaceQuasicoherentProp D.B (limitBase D.system)
          D.containsLimitBase D.X.left).ι.obj D.toSeparated.quasicoherentLimit)) ∧
      ∀ n : ℕ, IsIso (D.toSeparated.stageTensorSectionsBaseChange D.toSeparated.coherator
        D.toSeparated.coheratorAdjunction E n) :=
  D.toSeparated.isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange
    D.stageSectionsPseudoCoherent E hE

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
