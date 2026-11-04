module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightTExactCohomologyClass
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriekLargeSections
public import StacksFrontier.CategoryTheory.Sites.Modules.DerivedCountableCoproducts

/-!
# Stacks 07B9 (2)(a) and (2)(c) at module universe `u + 1`, over their module-level inputs

Let `𝒳` be an algebraic stack, `g^*` restriction of modules to the flat-fppf site at module
universe `u + 1` (`AlgebraicGeometry.Stack.FlatFppf.moduleInverseImage`) and `Lg_!` its derived
left adjoint (`AlgebraicGeometry.Stack.FlatFppf.derivedModuleLowerShriekSucc`, **Stacks 07AS**
(4) at that universe). This is the universe-`u + 1` reading of the dévissage that proves
**Stacks 07B9** (2)(a) and (2)(c) — the universe where the derived direct image of
**Stacks 07BC** lives, and hence where **Stacks 07BE** is stated — for a class `𝒜` of modules
(the faithful `LQCoh^fbc` of **Stacks 0762**), over the three module-level facts the source uses:

* `ha`: `g^*` carries `𝒜` into the quasi-coherent modules of the flat-fppf site
  (**Stacks 07B1** (2)(b));
* `hcolim`: `𝒜` is closed under colimits of sequences (**Stacks 0771** (5));
* `h0`: `Lg_!` carries a quasi-coherent module in degree `0` into `D_𝒜` (**Stacks 07B3** (2)).

together with `𝒜` being a weak Serre subcategory (**Stacks 0771** (2)).

## Main results

* `derivedCategoryB_moduleInverseImage_mapDerivedCategory`: (2)(a).
* `derivedCategoryB_derivedModuleLowerShriekSucc_of_single`: (2)(c).
* `derivedCategoryB_derivedModuleLowerShriekSucc_moduleInverseImage`: (2)(a) followed by (2)(c),
  `Lg_! g^* K ∈ D_𝒜` for `K ∈ D_𝒜`, the input of **Stacks 07BA**.

## References

* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w t t'

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  Stacks.hasSheafCompose_forget₂_commRingCat preservesCoveringPullbacks_inclusion_topology
  essentiallySmall_obj_largeSections essentiallySmall_flatFppf_largeSections
  hasSheafify_topology_largeSections wEqualsLocallyBijective_topology_largeSections
  hasSheafify_fppfTopology_largeSections wEqualsLocallyBijective_fppfTopology_largeSections
  hasPointwiseRightKanExtension_inclusion_ringCat_largeSections
  hasPointwiseRightKanExtension_inclusion_addCommGrpCat_largeSections

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The quasi-coherent modules on the flat-fppf site of an algebraic stack at module universe
`u + 1`. -/
abbrev flatQuasicoherentModulesSucc :
    ObjectProperty (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) :=
  fun M => M.IsQuasicoherentOnSite

/-- Quasi-coherence on the flat-fppf site is invariant under isomorphism. -/
theorem isClosedUnderIsomorphisms_flatQuasicoherentModulesSucc :
    (flatQuasicoherentModulesSucc B S hS 𝒳).IsClosedUnderIsomorphisms where
  of_iso e h := SheafOfModules.IsQuasicoherentOnSite.of_iso e h

variable [HasDerivedCategory.{t} (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{t'} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]

/-- `Lg_!` at module universe `u + 1` commutes with the shift, being left adjoint to the
shift-compatible `g^*`. -/
instance commShift_derivedModuleLowerShriekSucc :
    (derivedModuleLowerShriekSucc B S hS 𝒳).CommShift ℤ :=
  (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳).leftAdjointCommShift ℤ

/-- The adjunction `Lg_! ⊣ g^*` at module universe `u + 1` is compatible with the shifts. -/
instance commShift_derivedModuleLowerShriekSuccAdjunction :
    (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳).CommShift ℤ :=
  (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳).commShift_of_rightAdjoint ℤ

/-- **`Lg_!` at module universe `u + 1` is a triangulated functor**, being left adjoint to the
triangulated functor `g^*`. -/
instance isTriangulated_derivedModuleLowerShriekSucc :
    (derivedModuleLowerShriekSucc B S hS 𝒳).IsTriangulated :=
  Adjunction.isTriangulated_leftAdjoint (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳)

variable (𝒜 : ObjectProperty (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))

/-- **Stacks 07B9** (2)(a) at module universe `u + 1`: if `g^*` carries `𝒜` into the
quasi-coherent modules (Stacks 07B1 (2)(b)), then it carries `D_𝒜` into `D_QCoh` of the
flat-fppf site, `g^*` being exact. -/
theorem derivedCategoryB_moduleInverseImage_mapDerivedCategory
    (ha : ∀ F, 𝒜 F → (flatQuasicoherentModulesSucc B S hS 𝒳) ((moduleInverseImage B S hS 𝒳).obj F))
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB 𝒜 K) :
    DerivedCategoryB.derivedCategoryB (flatQuasicoherentModulesSucc B S hS 𝒳)
      ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K) := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((moduleInverseImage B S hS 𝒳).mapDerivedCategoryHomologyIso n).app K).symm
    (ha _ (hK n))

/-- **Stacks 07B9** (2)(c) at module universe `u + 1`, over Stacks 07B3 (2): if `Lg_!` carries
every quasi-coherent module of the flat-fppf site, put in degree `0`, into `D_𝒜`, then it carries
all of `D_QCoh` of the flat-fppf site into `D_𝒜`, for a weak Serre class `𝒜` closed under
colimits of sequences. -/
theorem derivedCategoryB_derivedModuleLowerShriekSucc_of_single [𝒜.IsWeakSerreClass]
    (hcolim : ∀ F : ℕ ⥤ SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳),
      (∀ n, 𝒜 (F.obj n)) → 𝒜 (colimit F))
    (h0 : ∀ M : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳),
      M.IsQuasicoherentOnSite → DerivedCategoryB.derivedCategoryB 𝒜
        ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)))
    (H : DerivedCategory (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)))
    (hH : DerivedCategoryB.derivedCategoryB (flatQuasicoherentModulesSucc B S hS 𝒳) H) :
    DerivedCategoryB.derivedCategoryB 𝒜 ((derivedModuleLowerShriekSucc B S hS 𝒳).obj H) := by
  have := isClosedUnderIsomorphisms_flatQuasicoherentModulesSucc.{u, w} B S hS 𝒳
  have hA : IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)
  have hB : IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)
  have := AB5OfSize_shrink.{0, 0, u + 1, u + 1}
    (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  have := AB5OfSize_shrink.{0, 0, u + 1, u + 1}
    (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  have : PreservesColimitsOfShape (Discrete ℕ) (derivedModuleLowerShriekSucc B S hS 𝒳) :=
    have := (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳).leftAdjoint_preservesColimits
    inferInstance
  exact DerivedCategory.derivedCategoryB_obj_of_isLE_obj (derivedModuleLowerShriekSucc B S hS 𝒳)
    (WeakSerre.isWeakSerre_of_isWeakSerreClass _)
    (hasExactCountableDirectSums_of_isGrothendieckAbelian _)
    (hasExactCountableDirectSums_of_isGrothendieckAbelian _)
    (fun X n _ => DerivedCategory.isLE_obj_of_adjunction (moduleInverseImage B S hS 𝒳)
      (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳) X n)
    hcolim
    (fun M hM q => DerivedCategory.derivedCategoryB_obj_singleFunctor
      (derivedModuleLowerShriekSucc B S hS 𝒳) (flatQuasicoherentModulesSucc B S hS 𝒳) 𝒜
      (WeakSerre.isWeakSerre_of_isWeakSerreClass 𝒜).isClosedUnderIsomorphisms h0 M hM q)
    H hH

/-- **Stacks 07B9** (2)(a) followed by (2)(c) at module universe `u + 1`: for `K` in `D_𝒜`, the
parasitic-free part `Lg_! g^* K` of Stacks 07BA lies in `D_𝒜` again, over the module-level inputs
Stacks 07B1 (2)(b), 0771 (5), 07B3 (2) and the weak Serre property 0771 (2). -/
theorem derivedCategoryB_derivedModuleLowerShriekSucc_moduleInverseImage [𝒜.IsWeakSerreClass]
    (ha : ∀ F, 𝒜 F → (flatQuasicoherentModulesSucc B S hS 𝒳) ((moduleInverseImage B S hS 𝒳).obj F))
    (hcolim : ∀ F : ℕ ⥤ SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳),
      (∀ n, 𝒜 (F.obj n)) → 𝒜 (colimit F))
    (h0 : ∀ M : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳),
      M.IsQuasicoherentOnSite → DerivedCategoryB.derivedCategoryB 𝒜
        ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)))
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB 𝒜 K) :
    DerivedCategoryB.derivedCategoryB 𝒜 ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
      ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K)) :=
  derivedCategoryB_derivedModuleLowerShriekSucc_of_single B S hS 𝒳 𝒜 hcolim h0 _
    (derivedCategoryB_moduleInverseImage_mapDerivedCategory B S hS 𝒳 𝒜 ha K hK)

end AlgebraicGeometry.Stack.FlatFppf
