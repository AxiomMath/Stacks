module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.GeneratingSubspaceAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleTrivial
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# A section of a power of `𝓛` generating at a closed point

Let `X` be a Noetherian algebraic space and `𝓛` an invertible `𝒪_X`-module such that every
coherent `𝓕` has some `n ≥ 1` with `H¹(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0`.  For every closed point `x` of
`|X|` there are `d ≥ 1` and a global section `s` of `𝓛^{⊗ d}` generating `𝓛^{⊗ d}` at `x`
(`AlgebraicGeometry.Space.exists_mem_sectionGeneratingLocus_of_isClosed`).  This is the second
paragraph of the proof of Stacks 0D2W.

By Stacks 0AHB the point is represented by a closed immersion `i : Spec k ⟶ X`.  Let `𝓘` be the
kernel of the unit `η : 𝒪_X ⟶ i_* i^* 𝒪_X`, which is an epimorphism (Stacks 04CJ), and choose
`d ≥ 1` with `H¹(X, 𝓘 ⊗ 𝓛^{⊗ d}) = 0`.  Tensoring by `𝓛^{⊗ d}` is exact, so the long exact
sequence makes `Γ(𝓛^{⊗ d}) ⟶ Γ((i_* i^* 𝒪_X) ⊗ 𝓛^{⊗ d})` surjective.  The target has a global
section generating it everywhere: the invertible module `i^* 𝓛^{⊗ -d}` on `Spec k` is trivial,
so the unit `𝓛^{⊗ -d} ⟶ i_* i^* 𝓛^{⊗ -d} ≅ i_* i^* 𝒪_X` is an epimorphism, and twisting it by
`𝓛^{⊗ d}` gives an epimorphism `𝒪_X ⟶ (i_* i^* 𝒪_X) ⊗ 𝓛^{⊗ d}`.  A lift `s` of that section
pulls back to a generator of `i^* 𝓛^{⊗ d}`, the pullback of `η ⊗ 𝓛^{⊗ d}` being invertible;
since the generating locus of a section of a quasi-coherent module of finite type pulls back
along any morphism (Stacks 07TZ), `x` lies in the generating locus of `s`.

## Main results

* `AlgebraicGeometry.Space.isIso_modulePullback_map_tensorMap`: the pullback of `f ⊗ 𝓜` is
  invertible once that of `f` is.
* `AlgebraicGeometry.Space.sectionGeneratingLocus_modulePullback_of_isFiniteTypeOnSite`: the
  generating locus of a section of a quasi-coherent module of finite type pulls back along any
  morphism.
* `AlgebraicGeometry.Space.exists_mem_sectionGeneratingLocus_of_isClosed`: a section of a power
  of `𝓛` generating at a given closed point.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
* [Stacks Project, Tag 0AHB](https://stacks.math.columbia.edu/tag/0AHB)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The pullback of `f ⊗ 𝓜` is invertible once that of `f` is**, for an arbitrary morphism of
algebraic spaces: the inverse image commutes with tensor products naturally in both variables
(Stacks 03EL). -/
theorem isIso_modulePullback_map_tensorMap {X Z : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (M : Modules.{u, u} B S hS X.1 X.2) (f : F ⟶ F')
    (hf : IsIso ((modulePullback B S hS i).map f)) :
    IsIso ((modulePullback B S hS i).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
        f).app M)) := by
  have hp : IsIso (X := ((modulePullback B S hS i).obj F, (modulePullback B S hS i).obj M))
      (Y := ((modulePullback B S hS i).obj F', (modulePullback B S hS i).obj M))
      ((modulePullback B S hS i).map f, (modulePullback B S hS i).map (𝟙 M)) := by
    rw [isIso_prod_iff]
    exact ⟨hf, (congrArg IsIso ((modulePullback B S hS i).map_id M)).mpr (IsIso.id _)⟩
  have key : (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O)).map
        ((f, 𝟙 M) : (F, M) ⟶ (F', M)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
        f).app M := by
    rw [Functor.uncurry_obj_map]
    dsimp only
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  refine (congrArg (fun g => IsIso ((modulePullback B S hS i).map g)) key).mp ?_
  exact (NatIso.isIso_map_iff (Stacks.SheafOfModules.pullbackTensorIso
    (smallEtaleRingedToposModulesHom B S hS i)) (X := (F, M)) (Y := (F', M)) (f, 𝟙 M)).2
      (by rw [Functor.comp_map]; exact @Functor.map_isIso _ _ _ _ _ _ _ _ hp)

section Pullback

/-- The pullback of a section `s`, viewed as a map out of the unit, is `s` pulled back, precomposed
with the unit iso. -/
private theorem unitHomEquiv_symm_modulePullbackSections {X Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2) (s : M.sections) :
    ((modulePullback B S hS g).obj M).unitHomEquiv.symm (modulePullbackSections B S hS g M s) =
      (modulePullbackUnitIso B S hS g).inv ≫
        (modulePullback B S hS g).map (M.unitHomEquiv.symm s) :=
  Equiv.symm_apply_apply _ _

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] smallEtaleModulesAbelian

/-- **The generating locus of a section of a quasi-coherent module of finite type pulls back
along any morphism**: for `g : Y ⟶ X`, the generating locus of `g^* s` is the preimage of that of
`s`.  The pullback carries the cokernel of `𝒪_X ⟶ 𝓜` to that of `𝒪_Y ⟶ g^* 𝓜`, and the support
of a quasi-coherent module of finite type pulls back (Stacks 07TZ). -/
theorem sectionGeneratingLocus_modulePullback_of_isFiniteTypeOnSite {X Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hMft : SheafOfModules.IsFiniteTypeOnSite M) (s : M.sections) :
    sectionGeneratingLocus B S hS ((modulePullback B S hS g).obj M)
        (modulePullbackSections B S hS g M s) =
      pointsMap B S hS Y.1 g.hom ⁻¹' sectionGeneratingLocus B S hS M s := by
  set φ := M.unitHomEquiv.symm s with hφ
  have := isClosedUnderCokernels_quasicoherentSheaves B S hS X.1 X.2
  have hadd : (modulePullback B S hS g).Additive :=
    (modulePullbackAdjunction B S hS g).left_adjoint_additive
  have hpres : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS g) :=
    (modulePullbackAdjunction B S hS g).leftAdjoint_preservesColimits
  have hepi : Epi (modulePullbackUnitIso B S hS g).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  let I : cokernel (C := Modules.{u, u} B S hS Y.1 Y.2)
      (((modulePullback B S hS g).obj M).unitHomEquiv.symm
        (modulePullbackSections B S hS g M s)) ≅
      (modulePullback B S hS g).obj (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ) :=
    cokernelIsoOfEq (C := Modules.{u, u} B S hS Y.1 Y.2)
        (unitHomEquiv_symm_modulePullbackSections g M s) ≪≫
      @cokernelEpiComp (Modules.{u, u} B S hS Y.1 Y.2) _ _ _ _ _ _ _ hepi _ ≪≫
      (PreservesCokernel.iso (modulePullback B S hS g) φ).symm
  have hCq : (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).IsQuasicoherentOnSite :=
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_cokernel φ
      (SheafOfModules.isQuasicoherentOnSite_unit _) hM
  have hCft : SheafOfModules.IsFiniteTypeOnSite
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ) :=
    isFiniteTypeOnSite_of_epi B S hS X.1 X.2 (cokernel.π φ) hMft
  ext y
  rw [Set.mem_preimage, mem_sectionGeneratingLocus_iff, mem_sectionGeneratingLocus_iff,
    supportOfSheaf_eq_of_iso B S hS Y I,
    supportOfSheaf_modulePullback_eq B S hS g _ hCq hCft, Set.mem_preimage]

end Pullback

section ClosedPoint

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard pointTopology

/-- **Stacks 0D2W, second paragraph of the proof: a section of a power of `𝓛` generating at a
closed point.**  See the module docstring. -/
theorem exists_mem_sectionGeneratingLocus_of_isClosed (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (h : have := enoughInjectives_modules B S hS X.1 X.2
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
        ∃ n : ℕ, 1 ≤ n ∧ IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj
            (twistStep B S hS X.1 X.2 L n F)))
    (x : points B S hS X.1) (hx : IsClosed ({x} : Set (points B S hS X.1))) :
    ∃ d : ℕ, 0 < d ∧ ∃ s : (invertibleTensorPower B S hS X.1 X.2 L d).sections,
      x ∈ sectionGeneratingLocus B S hS (invertibleTensorPower B S hS X.1 X.2 L d) s := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS X.1 X.2
  have hXN : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  -- the closed point as a closed immersion of the spectrum of a field
  obtain ⟨p, hpx, hi⟩ := exists_fieldValuedPoint_isClosedImmersion B S hS X.2
    (isDecentSpace_of_isNoetherian B S hS hZ X.2 hN) x hx
  let Z : AlgebraicSpaces B S hS := ⟨yoneda.obj p.siteObject, isAlgebraicSpace_yoneda B S hS _⟩
  let i : Z ⟶ X := ObjectProperty.homMk (fieldMorphism B S hS X.1 p)
  have hi' : IsClosedImmersion B S hS i.hom := hi
  let adj := modulePullbackAdjunction B S hS i
  have hη : ∀ M, Epi (adj.unit.app M) := fun M =>
    epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS i hi'
      (fun N hN => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi' N hN) M
  let O := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let η₀ := adj.unit.app O
  -- the ideal of the point is coherent
  have hO : IsCoherent B S hS X.1 X.2 O :=
    have := isCoherentOnSite_of_isInvertible O
      (@Stacks.SheafOfModules.isInvertible_unit _ _
        (smallEtaleRingedSite B S hS X.1 X.2).J (structurePresheaf B S hS X.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        _ _)
    isCoherent_of_isCoherentOnSite B S hS X.1 X.2 O
  have hQ : IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS i).obj
      ((modulePullback B S hS i).obj O)) :=
    isCoherent_of_iso B S hS X.2 ((modulePushforward B S hS i).mapIso
      (modulePullbackUnitIso B S hS i).symm)
      (isCoherent_structureSheafPushforward B S hS hN.2.2 i hi')
  have hI : IsCoherent B S hS X.1 X.2 (kernel η₀) := isCoherent_kernel B S hS X.1 X.2 hO hQ η₀
  obtain ⟨d, hd, hvan⟩ := h _ hI
  -- tensoring by `𝓛^{⊗ d}`
  let M := invertibleTensorPower B S hS X.1 X.2 L d
  have hpow : ∀ n : ℤ, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      (invertibleTensorPower B S hS X.1 X.2 L n) := fun n =>
    @Stacks.SheafOfModules.Invertible.tensorPower_isInvertible.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ L hL n
  have hMinv := hpow d
  have hMinv' : AlgebraicGeometry.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ M hMinv
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS X.1 X.2).O).flip.obj
    M
  have hT : T.IsEquivalence :=
    @Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible _ _
      (smallEtaleRingedSite B S hS X.1 X.2).J (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ M hMinv'
  -- `Γ(𝓛^{⊗ d}) ⟶ Γ((i_* i^* 𝒪_X) ⊗ 𝓛^{⊗ d})` is surjective
  have hSE : (ShortComplex.mk (kernel.ι η₀) η₀ (kernel.condition η₀)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel η₀)
      mono_f := inferInstance
      epi_g := hη O }
  have hvan' : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj (T.obj (kernel η₀))) :=
    hvan
  have hsurj : Function.Surjective (SheafOfModules.sectionsMap (T.map η₀)) :=
    @surjective_sectionsMap_map_of_isZero_rightDerived_one B S hS X T hT
      (ShortComplex.mk (kernel.ι η₀) η₀ (kernel.condition η₀)) hSE hvan'
  -- the module `𝓝 = 𝒪_X ⊗ 𝓛^{⊗ -d}` and its pullback to the point, which is trivial
  let N := twistStep B S hS X.1 X.2 L (-(d : ℤ)) O
  have hNinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property N :=
    @Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _
      (smallEtaleRingedSite B S hS X.1 X.2).J (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ _ _
      (@Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor.{u, u + 1, u}
        (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
        (structurePresheaf B S hS X.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        _ _ _).symm (hpow _)
  have hiN : IsInvertibleModule Z ((modulePullback B S hS i).obj N) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (isInvertible_modulePullback_obj B S hS i N
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ N hNinv))
  have hsub : Subsingleton (chartScheme (idEtaleChart B S hS p.siteObject)) := by
    change Subsingleton (PrimeSpectrum p.carrier)
    infer_instance
  let t : chartScheme (idEtaleChart B S hS p.siteObject) :=
    pointsEquivScheme B S hS p.siteObject
      ((p.tautologicalPoint B S hS X.1).class B S hS (yoneda.obj p.siteObject))
  obtain ⟨eN⟩ := nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top B S hS p.siteObject
    (R := CommRingCat.of p.carrier) rfl t
    (fun W hW => eq_top_iff.2 fun y _ => (Subsingleton.elim t y) ▸ hW) Z.2 _ hiN
  -- the epimorphism `θ : 𝓝 ⟶ i_* i^* 𝒪_X`
  let g : (modulePullback B S hS i).obj N ≅ (modulePullback B S hS i).obj O :=
    eN ≪≫ (modulePullbackUnitIso B S hS i).symm
  let θ : N ⟶ (modulePushforward B S hS i).obj ((modulePullback B S hS i).obj O) :=
    adj.unit.app N ≫ (modulePushforward B S hS i).map g.hom
  have hθ : Epi θ := @epi_comp _ _ _ _ _ _ (hη N) _
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom ((modulePushforward B S hS i).mapIso g)))
  -- the twist of `𝓝` by `𝓛^{⊗ d}` is `𝒪_X`, so `θ` twists to a generator
  let e₀ : O ≅ T.obj N :=
    (twistStepAddIso X L d (-(d : ℤ)) O ≪≫
      eqToIso (congrArg (fun n : ℤ => twistStep B S hS X.1 X.2 L n O)
        (by simp : -(d : ℤ) + ((d : ℕ) : ℤ) = 0)) ≪≫
      @Stacks.SheafOfModules.Invertible.tensorProductRightUnitor.{u, u + 1, u}
        (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
        (structurePresheaf B S hS X.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        _ _ O).symm
  let τ : O ⟶ T.obj ((modulePushforward B S hS i).obj ((modulePullback B S hS i).obj O)) :=
    e₀.hom ≫ T.map θ
  have := hθ
  have hTepi : Epi (T.map θ) := @Functor.map_epi _ _ _ _ T _ _ _ θ hθ
  -- a lift of `τ`
  obtain ⟨σ, hσ⟩ := hsurj ((T.obj _).unitHomEquiv τ)
  let σ' : O ⟶ T.obj O := (T.obj O).unitHomEquiv.symm σ
  have hσ' : σ' ≫ T.map η₀ = τ :=
    (SheafOfModules.unitHomEquiv_symm_comp σ (T.map η₀)).trans
      ((congrArg (T.obj _).unitHomEquiv.symm hσ).trans (Equiv.symm_apply_apply _ _))
  -- the section of `𝓛^{⊗ d}`
  let lam := @Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor.{u, u + 1, u}
    (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
    (structurePresheaf B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property _ _ M
  let s : M.sections := M.unitHomEquiv (σ' ≫ lam.hom)
  refine ⟨d, hd, s, ?_⟩
  -- pull back to the point
  have hMq : M.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertibleModule X M hMinv
  have hMft : SheafOfModules.IsFiniteTypeOnSite M :=
    have := isCoherentOnSite_of_isInvertible M hMinv
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS X M
  have hgl := sectionGeneratingLocus_modulePullback_of_isFiniteTypeOnSite i M hMq hMft s
  have hz : pointsMap B S hS Z.1 i.hom
      ((p.tautologicalPoint B S hS X.1).class B S hS (yoneda.obj p.siteObject)) = x :=
    (pointsMap_fieldMorphism_tautologicalPoint B S hS X.1 p).trans hpx
  rw [← hz, ← Set.mem_preimage, ← hgl, mem_sectionGeneratingLocus_iff]
  -- the pulled back section generates
  have : Abelian (Modules.{u, u} B S hS Z.1 Z.2) := smallEtaleModulesAbelian (X := Z)
  have hpres : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS i) :=
    adj.leftAdjoint_preservesColimits
  have hs : M.unitHomEquiv.symm s = σ' ≫ lam.hom := Equiv.symm_apply_apply _ _
  have hiso := isIso_modulePullback_map_tensorMap i M η₀
    (isIso_modulePullback_map_modulePullbackAdjunction_unit B S hS i hi' O)
  have hτ0 : Epi τ := @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom e₀)) _ hTepi
  have hτ : Epi ((modulePullback B S hS i).map τ) :=
    @Functor.map_epi _ _ _ _ (modulePullback B S hS i) _ _ _ τ hτ0
  have : IsIso ((modulePullback B S hS i).map (T.map η₀)) := hiso
  have hσepi : Epi ((modulePullback B S hS i).map σ') := by
    have e1 : (modulePullback B S hS i).map σ' =
        (modulePullback B S hS i).map τ ≫ inv ((modulePullback B S hS i).map (T.map η₀)) := by
      rw [IsIso.eq_comp_inv]
      exact ((modulePullback B S hS i).map_comp σ' (T.map η₀)).symm.trans
        (congrArg (fun f => (modulePullback B S hS i).map f) hσ')
    rw [e1]
    exact epi_comp _ _
  have hep : Epi (((modulePullback B S hS i).obj M).unitHomEquiv.symm
      (modulePullbackSections B S hS i M s)) := by
    rw [unitHomEquiv_symm_modulePullbackSections, hs]
    refine @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _ ?_
    exact (congrArg Epi ((modulePullback B S hS i).map_comp σ' lam.hom)).mpr
      (@epi_comp _ _ _ _ _ _ hσepi _
        (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom ((modulePullback B S hS i).mapIso lam))))
  have hz0 := isZero_cokernel_of_epi (((modulePullback B S hS i).obj M).unitHomEquiv.symm
      (modulePullbackSections B S hS i M s))
  rw [(supportOfSheaf_eq_empty_iff_isZero B S hS Z _).2 hz0]
  exact Set.notMem_empty _

end ClosedPoint

end AlgebraicGeometry.Space

end
