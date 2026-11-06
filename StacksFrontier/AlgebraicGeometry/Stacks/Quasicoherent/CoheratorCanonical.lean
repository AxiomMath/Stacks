module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentKernelImageCokernel
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.CoreflectiveKernelImage
public import StacksFrontier.CategoryTheory.Monoidal.CoreflectionStrongMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorLqcohSheafFbc
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreFppf

/-!
# Stacks 0GQL, 0GQM and 0779 at the canonical coherator

This file states **Stacks 0GQL** (2) corrected and (3), **Stacks 0GQM** (ii)–(iv) and
**Stacks 0779** at the canonical coherator of an algebraic stack,
`AlgebraicGeometry.Stack.AlgebraicStacks.coherator` with its adjunction
`AlgebraicGeometry.Stack.AlgebraicStacks.coheratorAdjunction` (**Stacks 0778**). The results of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatFppf` and
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorLqcohSheafFbc` hold for an
arbitrary right adjoint of the inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)`; here they are instantiated at
the canonical one, together with the properties of `LQCoh^fbc(𝒪_𝒳)` they combine with
(**Stacks 0771** (2), (6) and `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`).

## Main results

* `isZero_coherator_obj_iff_isParasitic` and
  `isParasitic_kernel_and_cokernel_coheratorAdjunction_counit`: **Stacks 0779** (1) and (2);
  `preservesFiniteLimits_and_preservesFiniteColimits_lqcohSheafFbc_ι_comp_coherator`,
  `preservesLimitsOfSize_lqcohSheafFbc_ι_comp_coherator` and
  `preservesColimitsOfShape_lqcohSheafFbc_ι_comp_coherator`: **Stacks 0779** (3), `Q` is exact
  and commutes with all limits and colimits on `LQCoh^fbc(𝒪_𝒳)`. All are in the namespace
  `AlgebraicGeometry.Stack.AlgebraicStacks`.
* `isMonoidal_lqcohSheafFbc`, `lqcohSheafFbcInclusionBraided`,
  `quasicoherentToLqcohSheafFbcBraided`, `coheratorBraided`, `isIso_coheratorTensorComparison` and
  `coheratorTensorIso`: **Stacks 0GQM** (ii)–(iv), for the monoidal structure of Tag 01CA on
  `Mod(𝒪_𝒳)` and the structures it induces. That the coherator inverts a map of `LQCoh^fbc(𝒪_𝒳)`
  with parasitic kernel and cokernel is seen on the flat-fppf site
  (`AlgebraicGeometry.Stack.isIso_map_of_isIso_modulePullback_map`), with no use of the weak Serre
  property of `LQCoh^fbc(𝒪_𝒳)`.
* `lqcohSheafFbc_kernel_quasicoherentInclusion` and `isLimitKernelForkCoherator`: **Stacks 0GQL**
  part (3), the kernel `Ker(i φ)` computed in `Mod(𝒪_𝒳)` lies in `LQCoh^fbc(𝒪_𝒳)` and `Q` of it
  is the kernel of `φ` in `QCoh(𝒪_𝒳)`.
* `lqcohSheafFbc_image_quasicoherentInclusion` and `coheratorImageIsImage`: **Stacks 0GQL**
  part (2), corrected: the image computed in `Mod(𝒪_𝒳)` lies in `LQCoh^fbc(𝒪_𝒳)` and `Q` of it is
  the image of `φ` in `QCoh(𝒪_𝒳)`. The part as stated, that this image is quasi-coherent, is
  false (`AlgebraicGeometry.Stack.ImageCounterexample.not_forall_isQuasicoherentOnSite_image`).

## References

* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0GQL, part (3), the kernel in `QCoh(𝒪_𝒳)`.** For a map `φ : 𝓕 ⟶ 𝓖` of
quasi-coherent modules on an algebraic stack, `Q(Ker(i φ))`, the coherator of the kernel computed
in `Mod(𝒪_𝒳)`, with its map to `𝓕`, is the kernel of `φ` in `QCoh(𝒪_𝒳)`. -/
@[stacks 0GQL "part (3), the second half: Q(Ker φ), with its map to 𝓕, is the kernel of φ in \
  QCoh(𝒪_𝒳), for the coherator Q of Stacks 0778"]
def isLimitKernelForkCoherator {F G : quasicoherentModules B S hS 𝒳} (φ : F ⟶ G) :
    IsLimit (KernelFork.ofι (Abelian.coreflectorKernelι (coheratorAdjunction B S hS 𝒳) φ)
      (Abelian.coreflectorKernelι_comp (coheratorAdjunction B S hS 𝒳) φ)) :=
  Abelian.isLimitCoreflectorKernelFork (coheratorAdjunction B S hS 𝒳) φ

section Stacks0779

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- **Stacks 0779** (1). An object of `LQCoh^fbc(𝒪_𝒳)` is killed by the coherator
`Q : Mod(𝒪_𝒳) → QCoh(𝒪_𝒳)` of **Stacks 0778** exactly when it is parasitic: the kernel of `Q` on
`LQCoh^fbc(𝒪_𝒳)` is exactly the collection of its parasitic objects. -/
@[stacks 0779 "part (1): the kernel of Q on LQCoh^fbc(𝒪_𝒳) is exactly its parasitic objects"]
theorem isZero_coherator_obj_iff_isParasitic (F : Stack.fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    IsZero ((coherator B S hS 𝒳).obj F) ↔ IsParasitic B S hS 𝒳 .fppf F.val :=
  isZero_obj_iff_isParasitic_of_lqcohSheafFbc B E h S hS 𝒳 (coheratorAdjunction B S hS 𝒳) F hF

/-- **Stacks 0779** (2). For `𝓕` in `LQCoh^fbc(𝒪_𝒳)` both the kernel and the cokernel of the
adjunction map `Q(𝓕) ⟶ 𝓕` are parasitic. -/
@[stacks 0779 "part (2): the kernel and the cokernel of the adjunction map Q(F) → F are \
  parasitic, for F in LQCoh^fbc(𝒪_𝒳)"]
theorem isParasitic_kernel_and_cokernel_coheratorAdjunction_counit
    (F : Stack.fppfModules B S hS 𝒳) (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    IsParasitic B S hS 𝒳 .fppf (kernel ((coheratorAdjunction B S hS 𝒳).counit.app F)).val ∧
      IsParasitic B S hS 𝒳 .fppf
        (cokernel ((coheratorAdjunction B S hS 𝒳).counit.app F)).val :=
  isParasitic_kernel_and_cokernel_counit_of_lqcohSheafFbc B E h S hS 𝒳
    (coheratorAdjunction B S hS 𝒳) F hF

/-- `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`, as an inequality of object properties. -/
theorem isQuasicoherentOnSite_le_lqcohSheafFbc :
    SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf) ≤ lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 :=
  fun M hM => lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳 ⟨M, hM⟩

/-- The coherator restricted to `LQCoh^fbc(𝒪_𝒳)` is right adjoint to the inclusion
`QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳)`. -/
def lqcohSheafFbcCoheratorAdjunction :
    ObjectProperty.ιOfLE (isQuasicoherentOnSite_le_lqcohSheafFbc B S hS 𝒳 E h) ⊣
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳 :=
  (coheratorAdjunction B S hS 𝒳).restrictFullyFaithful (Functor.FullyFaithful.id _)
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).fullyFaithfulι
    ((quasicoherentInclusion B S hS 𝒳).leftUnitor ≪≫
      (ObjectProperty.ιOfLECompιIso (isQuasicoherentOnSite_le_lqcohSheafFbc B S hS 𝒳 E h)).symm)
    (Functor.rightUnitor _).symm

/-- The counit of `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSheafFbcCoheratorAdjunction` is
the counit of the coherator. -/
theorem ι_map_lqcohSheafFbcCoheratorAdjunction_counit_app
    (F : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory) :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι.map
        ((lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).counit.app F) =
      (coheratorAdjunction B S hS 𝒳).counit.app F.obj := by
  have := (coheratorAdjunction B S hS 𝒳).map_restrictFullyFaithful_counit_app
    (Functor.FullyFaithful.id _) (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).fullyFaithfulι
    ((quasicoherentInclusion B S hS 𝒳).leftUnitor ≪≫
      (ObjectProperty.ιOfLECompιIso (isQuasicoherentOnSite_le_lqcohSheafFbc B S hS 𝒳 E h)).symm)
    ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳).rightUnitor.symm F
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app] at this
  exact this.trans (Category.id_comp _)

/-- **Stacks 0779** (3), limits: the coherator `Q : LQCoh^fbc(𝒪_𝒳) → QCoh(𝒪_𝒳)` commutes with all
limits, being right adjoint to the inclusion `QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳)`. -/
@[stacks 0779 "part (3): Q on LQCoh^fbc(𝒪_𝒳) commutes with all limits"]
theorem preservesLimitsOfSize_lqcohSheafFbc_ι_comp_coherator :
    PreservesLimitsOfSize.{u, u}
      ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳) :=
  (lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).rightAdjoint_preservesLimits

/-- **Stacks 0779** (3), colimits: the coherator `Q : LQCoh^fbc(𝒪_𝒳) → QCoh(𝒪_𝒳)` commutes with
all colimits of `u`-small shapes, which are computed in `Mod(𝒪_𝒳)`. -/
@[stacks 0779 "part (3): Q on LQCoh^fbc(𝒪_𝒳) commutes with all colimits"]
theorem preservesColimitsOfShape_lqcohSheafFbc_ι_comp_coherator (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J
      ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳) :=
  preservesColimitsOfShape_lqcohSheafFbc_ι_comp B E h S hS 𝒳 (coheratorAdjunction B S hS 𝒳) J

/-- **Stacks 0779** (3), exactness: the coherator `Q : LQCoh^fbc(𝒪_𝒳) → QCoh(𝒪_𝒳)` is exact, it
preserves finite limits and finite colimits. -/
@[stacks 0779 "part (3): Q is exact on LQCoh^fbc(𝒪_𝒳)"]
theorem preservesFiniteLimits_and_preservesFiniteColimits_lqcohSheafFbc_ι_comp_coherator :
    PreservesFiniteLimits
        ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳) ∧
      PreservesFiniteColimits
        ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳) :=
  ⟨@PreservesLimitsOfSize.preservesFiniteLimits _ _ _ _ _
      (preservesLimitsOfSize_lqcohSheafFbc_ι_comp_coherator B S hS 𝒳 E h),
    preservesFiniteColimits_lqcohSheafFbc_ι_comp B E h S hS 𝒳 (coheratorAdjunction B S hS 𝒳)⟩

include E h in
/-- The consumer form (I2) of **Stacks 0779** (2) at the canonical coherator: for a
quasi-compact and quasi-separated 1-morphism `f : 𝒴' ⟶ 𝒳`, a quasi-coherent module `𝓕` on `𝒴'`
and `q ≥ 0`, the kernel and the cokernel of `Q(Rᵠf_*𝓕) ⟶ Rᵠf_*𝓕` are parasitic. -/
theorem isParasitic_kernel_and_cokernel_coheratorAdjunction_counit_higherDirectImage
    {𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒴' ⟶ 𝒳)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : quasicoherentModules B S hS 𝒴') (q : ℕ) :
    IsParasitic B S hS 𝒳 .fppf (kernel ((coheratorAdjunction B S hS 𝒳).counit.app
        ((fppfModulesHigherDirectImage B S hS f q).obj F.obj))).val ∧
      IsParasitic B S hS 𝒳 .fppf (cokernel ((coheratorAdjunction B S hS 𝒳).counit.app
        ((fppfModulesHigherDirectImage B S hS f q).obj F.obj))).val :=
  isParasitic_kernel_and_cokernel_counit_higherDirectImage B E h S hS 𝒳
    (coheratorAdjunction B S hS 𝒳) f hqc hqs F q

end Stacks0779

/-! ### Stacks 0GQM -/

section Stacks0GQM

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat
  fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- **Stacks 0GQM, (ii).** `LQCoh^fbc(𝒪_𝒳)` is closed under the tensor product of `𝒪_𝒳`-modules
(**Stacks 0771** (6)) and contains `𝒪_𝒳`: it is a monoidal subcategory of `Mod(𝒪_𝒳)`. -/
@[stacks 0GQM "(ii): LQCoh^fbc(𝒪_𝒳) is closed under the tensor product, a monoidal subcategory \
  of Mod(𝒪_𝒳)"]
theorem isMonoidal_lqcohSheafFbc :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsMonoidal where
  prop_tensor F G hF hG := lqcohSheafFbcFppfModules_sheafTensor B E h S hS 𝒳 F G hF hG
  prop_unit :=
    have hinc : ∀ M, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
        ((quasicoherentInclusion B S hS 𝒳).obj M) :=
      lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳
    hinc ⟨_, SheafOfModules.isQuasicoherentOnSite_unit
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)⟩

/-- **Stacks 0GQM, (iii), the inclusion `LQCoh^fbc(𝒪_𝒳) → Mod(𝒪_𝒳)`**: a functor of symmetric
monoidal categories, for the tensor product of `𝒪_𝒳`-modules and the structure it induces on
`LQCoh^fbc(𝒪_𝒳)`. -/
@[stacks 0GQM "(iii): the inclusion LQCoh^fbc(𝒪_𝒳) → Mod(𝒪_𝒳) is a functor of symmetric \
  monoidal categories", instance_reducible]
def lqcohSheafFbcInclusionBraided :
    letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι.Braided :=
  letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
  inferInstance

/-- **Stacks 0GQM, (iii), the inclusion `QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳)`**: a functor of symmetric
monoidal categories, for the structures both inherit from `Mod(𝒪_𝒳)`. -/
@[stacks 0GQM "(iii): the inclusion QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) is a functor of symmetric \
  monoidal categories", instance_reducible]
def quasicoherentToLqcohSheafFbcBraided :
    letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
    (ObjectProperty.ιOfLE (isQuasicoherentOnSite_le_lqcohSheafFbc B S hS 𝒳 E h)).Braided :=
  letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
  inferInstance

/-- The coherator inverts the tensor product of two counits at objects of `LQCoh^fbc(𝒪_𝒳)`: that
tensor product has parasitic kernel and cokernel (**Stacks 0779** (2)), so it becomes an
isomorphism on the flat-fppf site, between modules whose restriction there is quasi-coherent. -/
theorem isIso_coherator_map_tensorHom_counit
    (F G : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory) :
    letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
    IsIso (((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳).map
      ((lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).counit.app F ⊗ₘ
        (lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).counit.app G)) := by
  let := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
  let L := lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
  have hι : L.ι.map ((lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).counit.app F ⊗ₘ
      (lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).counit.app G) =
      (coheratorAdjunction B S hS 𝒳).counit.app F.obj ⊗ₘ
        (coheratorAdjunction B S hS 𝒳).counit.app G.obj := by
    rw [Functor.Monoidal.map_tensor, ι_map_lqcohSheafFbcCoheratorAdjunction_counit_app,
      ι_map_lqcohSheafFbcCoheratorAdjunction_counit_app]
    simp
  have hrqc : ∀ M, L M →
      ((FlatFppf.modulePullback B S hS 𝒳).obj M).IsQuasicoherentOnSite := fun M hM =>
    FlatFppf.isQuasicoherentOnSite_modulePullback_of_isCartesianAlongFlatAffine B S hS 𝒳 M
      (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS M hM)
  have hF := isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒳 E h F.obj
    F.property
  have hG := isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒳 E h G.obj
    G.property
  have hk : IsIso ((FlatFppf.modulePullback B S hS 𝒳).map
      (@MonoidalCategoryStruct.tensorHom (Stack.fppfModules B S hS 𝒳) _
        (fppfModulesMonoidal B S hS 𝒳).toMonoidalCategoryStruct _ _ _ _
        ((coheratorAdjunction B S hS 𝒳).counit.app F.obj)
        ((coheratorAdjunction B S hS 𝒳).counit.app G.obj))) :=
    FlatFppf.isIso_modulePullback_map_of_bijective B S hS 𝒳 _
      (isIso_app_of_isParasitic_kernel_cokernel B S hS _
        (isParasitic_kernel_tensorHom B S hS 𝒳 _ _ hF.1 hF.2 hG.1 hG.2)
        (isParasitic_cokernel_tensorHom B S hS 𝒳 _ _ hF.1 hF.2 hG.1 hG.2))
  show IsIso ((coherator B S hS 𝒳).map (L.ι.map _))
  rw [hι]
  exact isIso_map_of_isIso_modulePullback_map B S hS 𝒳 (coheratorAdjunction B S hS 𝒳) _
    (hrqc _ (lqcohSheafFbcFppfModules_sheafTensor B E h S hS 𝒳 _ _
      (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳 _)
      (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳 _)))
    (hrqc _ (lqcohSheafFbcFppfModules_sheafTensor B E h S hS 𝒳 _ _ F.property G.property)) hk

/-- **Stacks 0GQM, (iv).** The coherator `Q : LQCoh^fbc(𝒪_𝒳) → QCoh(𝒪_𝒳)` is a functor of
symmetric monoidal categories. Its comparison `Q(𝓕) ⊗ Q(𝓖) → Q(𝓕 ⊗ 𝓖)` is the adjoint transpose
of the tensor product `Q(𝓕) ⊗ Q(𝓖) → 𝓕 ⊗ 𝓖` of the two counits, the south-west arrow of the
triangle of the source, and it is invertible because `Q` inverts that tensor product of counits
(`AlgebraicGeometry.Stack.AlgebraicStacks.isIso_coherator_map_tensorHom_counit`). -/
@[stacks 0GQM "(iv): the coherator Q : LQCoh^fbc(𝒪_𝒳) → QCoh(𝒪_𝒳) is a functor of symmetric \
  monoidal categories", instance_reducible]
def coheratorBraided :
    letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
    ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳).Braided :=
  letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
  (lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).rightAdjointBraided
    (isIso_coherator_map_tensorHom_counit B S hS 𝒳 E h)

/-- **Stacks 0GQM, (iv), the tensor comparison.** For `𝓕, 𝓖` in `LQCoh^fbc(𝒪_𝒳)` the canonical
map `Q(𝓕) ⊗ Q(𝓖) → Q(𝓕 ⊗ 𝓖)`, the adjoint transpose of the tensor product of the two counits,
is an isomorphism. -/
@[stacks 0GQM "(iv): the canonical map Q(F) ⊗ Q(G) → Q(F ⊗ G) is an isomorphism"]
theorem isIso_coheratorTensorComparison
    (F G : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory) :
    letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
    letI := (lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).rightAdjointLaxMonoidal
    IsIso (Functor.LaxMonoidal.μ
      ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳) F G) :=
  let := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
  (lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).isIso_rightAdjointLaxMonoidal_μ F G
    (isIso_coherator_map_tensorHom_counit B S hS 𝒳 E h F G)

/-- **Stacks 0GQM, (iv), the isomorphism `Q(𝓕) ⊗ Q(𝓖) ≅ Q(𝓕 ⊗ 𝓖)`** of the symmetric monoidal
functor `AlgebraicGeometry.Stack.AlgebraicStacks.coheratorBraided`; its forward map is the
canonical comparison (`AlgebraicGeometry.Stack.AlgebraicStacks.coheratorTensorIso_hom`). -/
@[stacks 0GQM "(iv): the isomorphism Q(F) ⊗ Q(G) ≅ Q(F ⊗ G)"]
def coheratorTensorIso
    (F G : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory) :
    letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
    (coherator B S hS 𝒳).obj F.obj ⊗ (coherator B S hS 𝒳).obj G.obj ≅
      (coherator B S hS 𝒳).obj (F ⊗ G).obj :=
  letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
  letI := coheratorBraided B S hS 𝒳 E h
  Functor.Monoidal.μIso
    ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳) F G

/-- The forward map of `AlgebraicGeometry.Stack.AlgebraicStacks.coheratorTensorIso` is the
canonical comparison of the adjunction. -/
theorem coheratorTensorIso_hom
    (F G : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory) :
    letI := isMonoidal_lqcohSheafFbc B S hS 𝒳 E h
    letI := (lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).rightAdjointLaxMonoidal
    (coheratorTensorIso B S hS 𝒳 E h F G).hom =
      Functor.LaxMonoidal.μ
        ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳) F G :=
  rfl

end Stacks0GQM

/-! ### Stacks 0GQL, parts (2) and (3) -/

section Stacks0GQL

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

set_option synthInstance.maxHeartbeats 200000 in
/-- **Stacks 0GQL, part (3), the kernel in `Mod(𝒪_𝒳)`.** For a map `φ : 𝓕 ⟶ 𝓖` of quasi-coherent
modules on an algebraic stack, the kernel of `φ` computed in `Mod(𝒪_𝒳)` lies in
`LQCoh^fbc(𝒪_𝒳)`, `LQCoh^fbc(𝒪_𝒳)` being a weak Serre subcategory containing `QCoh(𝒪_𝒳)`
(**Stacks 0771** (2)). Its coherator is the kernel of `φ` in `QCoh(𝒪_𝒳)`
(`AlgebraicGeometry.Stack.AlgebraicStacks.isLimitKernelForkCoherator`). -/
@[stacks 0GQL "part (3), the first half: the kernel computed in Mod(𝒪_𝒳) of a map of \
  quasi-coherent modules lies in LQCoh^fbc(𝒪_𝒳)"]
theorem lqcohSheafFbc_kernel_quasicoherentInclusion {F G : quasicoherentModules B S hS 𝒳}
    (φ : F ⟶ G) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
      (kernel ((quasicoherentInclusion B S hS 𝒳).map φ)) :=
  Abelian.prop_kernel_map _ (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳) φ

/-- **Stacks 0GQL, part (2), corrected, the image in `Mod(𝒪_𝒳)`.** For a map `φ : 𝓕 ⟶ 𝓖` of
quasi-coherent modules on an algebraic stack, the image of `φ` computed in `Mod(𝒪_𝒳)` lies in
`LQCoh^fbc(𝒪_𝒳)`: it is the kernel of `𝓖 ⟶ Coker(φ)`. It need not be quasi-coherent: part (2)
as printed is refuted by
`AlgebraicGeometry.Stack.ImageCounterexample.not_forall_isQuasicoherentOnSite_image`. -/
@[stacks 0GQL "part (2), corrected, the first half: the image computed in Mod(𝒪_𝒳) of a map of \
  quasi-coherent modules lies in LQCoh^fbc(𝒪_𝒳); it need not be quasi-coherent"]
theorem lqcohSheafFbc_image_quasicoherentInclusion {F G : quasicoherentModules B S hS 𝒳}
    (φ : F ⟶ G) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
      (Abelian.image ((quasicoherentInclusion B S hS 𝒳).map φ)) :=
  Abelian.prop_image_map _ (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳) φ

/-- **Stacks 0GQL, part (2), corrected, the image in `QCoh(𝒪_𝒳)`.** For a map `φ : 𝓕 ⟶ 𝓖` of
quasi-coherent modules on an algebraic stack, `Q(Im φ)`, the coherator of the image computed in
`Mod(𝒪_𝒳)`, is the image of `φ` in `QCoh(𝒪_𝒳)`: the epimorphism `𝓕 ⟶ Im φ` lies in
`LQCoh^fbc(𝒪_𝒳)`, where `Q` is right exact (**Stacks 0779** (3)), and `Q` keeps
`Im φ ⟶ 𝓖` a monomorphism. Part (2) as printed, with `Im φ` itself quasi-coherent, is refuted by
`AlgebraicGeometry.Stack.ImageCounterexample.not_forall_isQuasicoherentOnSite_image`. -/
@[stacks 0GQL "part (2), corrected, the second half: Q(Im φ) is the image of φ in QCoh(𝒪_𝒳), \
  for the coherator Q of Stacks 0778"]
def coheratorImageIsImage {F G : quasicoherentModules B S hS 𝒳} (φ : F ⟶ G) :
    IsImage (Abelian.coreflectorImageMonoFactorisation (coheratorAdjunction B S hS 𝒳) φ) :=
  haveI := (preservesFiniteLimits_and_preservesFiniteColimits_lqcohSheafFbc_ι_comp_coherator
    B S hS 𝒳 E h).2
  Abelian.coreflectorImageIsImage (coheratorAdjunction B S hS 𝒳)
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳)
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳) φ

end Stacks0GQL

end AlgebraicGeometry.Stack.AlgebraicStacks

end
