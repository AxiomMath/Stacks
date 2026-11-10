module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.SmallModelModuleAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.FullyFaithfulModuleLowerShriekUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedAdjunctionTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOverASquareOfSites

/-!
# The derived lower shriek of modules whose sections lie above the structure sheaf

Let `f : C ⥤ D` be a continuous and cocontinuous functor of essentially small sites satisfying
the covering-pullback condition of Stacks 00WV, and let `O_D` be a sheaf of commutative rings on
`D` with sections in `Type r`. The derived lower shriek `totalLeftDerivedLowerShriek` is formed
for modules whose sections lie in the universe of the rings. This file gives it for modules with
sections in the larger universe `max r w`, over the same rings: the restriction functor is
`Stacks.SheafOfModules.inverseImage`, whose module and ring universes are independent.

The construction raises the structure sheaf to `max r w` (`liftedStructureSheaf`), applies the
single-universe theory there, and transports the result back along the equivalences of module
categories given by the ring isomorphisms `ULift R ≃+* R`
(`Stacks.UniverseLift.RingTransport.sheafEquivalence`), which are the identity on underlying
sheaves of abelian groups (`Stacks.DerivedAdjunctionTransport`).

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.ULift.liftedStructureSheaf`: `O_D` with its section rings
  raised to `max r w`.
* `Stacks.Cohomology.DerivedLowerShriek.ULift.derivedLowerShriek`: `Lg_!` on modules with
  sections in `max r w`.
* `Stacks.Cohomology.DerivedLowerShriek.ULift.derivedLowerShriekAdjunction`: `Lg_! ⊣ g^*`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.ULift.isIso_derivedLowerShriekAdjunction_unit`:
  `g^* Lg_! = id` for a fully faithful `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w r t t' v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek.ULift

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
  [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K CommRingCat.{r})
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max r w} RingCat.{max r w})]

/-- The structure sheaf with its section rings raised to the universe `max r w`. -/
abbrev liftedStructureSheaf : Sheaf K CommRingCat.{max r w} :=
  ⟨O.obj ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{r, w},
    Stacks.UniverseLift.isSheaf_comp_commRingCatULift _ O.property⟩

/-- The ring isomorphisms `ULift O_D(V) ≃+* O_D(V)`, as a ring transport along the identity of
`D`. -/
def targetRingTransport :
    Stacks.UniverseLift.RingTransport (CategoryTheory.Equivalence.refl (C := D))
      (Stacks.SheafOfModules.Tensor.ringSheaf O).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)).obj where
  iso _ := ULift.ringEquiv
  naturality _ _ := rfl

/-- The ring isomorphisms `ULift O_C(U) ≃+* O_C(U)` for `O_C = g^{-1} O_D`, as a ring transport
along the identity of `C`. -/
def sourceRingTransport :
    Stacks.UniverseLift.RingTransport (CategoryTheory.Equivalence.refl (C := C))
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj
      (inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))).obj where
  iso _ := ULift.ringEquiv
  naturality _ _ := rfl

/-- The functor of the identity equivalence of `D` is continuous for `K`. -/
instance : (CategoryTheory.Equivalence.refl (C := D)).functor.IsContinuous K K :=
  inferInstanceAs ((𝟭 D).IsContinuous K K)

/-- The inverse of the identity equivalence of `D` is continuous for `K`. -/
instance : (CategoryTheory.Equivalence.refl (C := D)).inverse.IsContinuous K K :=
  inferInstanceAs ((𝟭 D).IsContinuous K K)

/-- The functor of the identity equivalence of `C` is continuous for `J`. -/
instance : (CategoryTheory.Equivalence.refl (C := C)).functor.IsContinuous J J :=
  inferInstanceAs ((𝟭 C).IsContinuous J J)

/-- The inverse of the identity equivalence of `C` is continuous for `J`. -/
instance : (CategoryTheory.Equivalence.refl (C := C)).inverse.IsContinuous J J :=
  inferInstanceAs ((𝟭 C).IsContinuous J J)

/-- The inverse of the reversed (`symm`) identity equivalence of `D` is continuous for `K`. -/
instance : (CategoryTheory.Equivalence.refl (C := D)).symm.inverse.IsContinuous K K :=
  inferInstanceAs ((𝟭 D).IsContinuous K K)

/-- The functor of the reversed (`symm`) identity equivalence of `D` is continuous for `K`. -/
instance : (CategoryTheory.Equivalence.refl (C := D)).symm.functor.IsContinuous K K :=
  inferInstanceAs ((𝟭 D).IsContinuous K K)

/-- The inverse of the reversed (`symm`) identity equivalence of `C` is continuous for `J`. -/
instance : (CategoryTheory.Equivalence.refl (C := C)).symm.inverse.IsContinuous J J :=
  inferInstanceAs ((𝟭 C).IsContinuous J J)

/-- The functor of the reversed (`symm`) identity equivalence of `C` is continuous for `J`. -/
instance : (CategoryTheory.Equivalence.refl (C := C)).symm.functor.IsContinuous J J :=
  inferInstanceAs ((𝟭 C).IsContinuous J J)

/-- Sheaves of `O_D`-modules with sections in `max r w` are sheaves of modules over the raised
structure sheaf. -/
abbrev targetModulesEquivalence :
    SheafOfModules.{max r w} (Stacks.SheafOfModules.Tensor.ringSheaf O) ≌
      SheafOfModules.{max r w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)) :=
  (targetRingTransport.{w} K O).sheafEquivalence

/-- Sheaves of `O_C`-modules with sections in `max r w` are sheaves of modules over the raised
inverse image of the structure sheaf. -/
abbrev sourceModulesEquivalence :
    SheafOfModules.{max r w} (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≌
      SheafOfModules.{max r w} (inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))) :=
  (sourceRingTransport.{w} J K f O).sheafEquivalence

/-- **Restriction commutes with raising the ring universe**, on the nose: both composites send a
sheaf of modules to its restriction along `f`, with scalars read through `ULift`. -/
def inverseImageCompIso :
    Stacks.SheafOfModules.inverseImage.{max r w} J K f (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        (sourceModulesEquivalence.{w} J K f O).functor ≅
      (targetModulesEquivalence.{w} K O).functor ⋙
        restrictionModules J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)) :=
  Iso.refl _

section Derived

variable [EssentiallySmall.{max r w} C] [EssentiallySmall.{max r w} D]
  [Stacks.Sites.PreservesCoveringPullbacks J f]
  [HasWeakSheafify J AddCommGrpCat.{max r w}] [J.WEqualsLocallyBijective AddCommGrpCat.{max r w}]
  [HasSheafify J AddCommGrpCat.{max r w}]
  [HasWeakSheafify K AddCommGrpCat.{max r w}] [K.WEqualsLocallyBijective AddCommGrpCat.{max r w}]
  [HasSheafify K AddCommGrpCat.{max r w}]

attribute [local instance] Stacks.essentiallySmall_over

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **The lower shriek of `Stacks.SheafOfModules` is the transport of the lower shriek over the
raised structure sheaf**: both are left adjoint to `g^*`, read on either side of the transport. -/
def lowerShriekCompIso
    [UnivLE.{r, max r w}] [UnivLE.{v₁, max r w}] [UnivLE.{v₂, max r w}] [UnivLE.{u₁, max r w}] :
    (sourceModulesEquivalence.{w} J K f O).functor ⋙
        lowerShriekModules J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)) ⋙
        (targetModulesEquivalence.{w} K O).inverse ≅
      Stacks.SheafOfModules.lowerShriek.{max r w} J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  ((((sourceModulesEquivalence.{w} J K f O).toAdjunction.comp
      (adjunctionModules J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)))).comp
      (targetModulesEquivalence.{w} K O).symm.toAdjunction).ofNatIsoRight
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (inverseImageCompIso.{w} J K f O).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (sourceModulesEquivalence.{w} J K f O).unitIso.symm ≪≫
      Functor.rightUnitor _)).leftAdjointUniq
    (Stacks.SheafOfModules.lowerShriekAdjunction.{max r w} J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- Sheaves of modules over the raised structure sheaf form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_liftedModules :
    IsGrothendieckAbelian.{max r w} (SheafOfModules.{max r w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- The equivalence of module categories over the two structure sheaves is additive. -/
instance targetModulesEquivalence_functor_additive :
    (targetModulesEquivalence.{w} K O).functor.Additive :=
  Stacks.UniverseLift.RingTransport.sheafFunctor_additive _

/-- The inverse of the equivalence of module categories over the two structure sheaves is
additive. -/
instance targetModulesEquivalence_inverse_additive :
    (targetModulesEquivalence.{w} K O).inverse.Additive :=
  Stacks.UniverseLift.RingTransport.sheafFunctor_additive _

/-- The equivalence of module categories over the two inverse-image rings is additive. -/
instance sourceModulesEquivalence_functor_additive :
    (sourceModulesEquivalence.{w} J K f O).functor.Additive :=
  Stacks.UniverseLift.RingTransport.sheafFunctor_additive _

/-- The inverse of the equivalence of module categories over the two inverse-image rings is
additive. -/
instance sourceModulesEquivalence_inverse_additive :
    (sourceModulesEquivalence.{w} J K f O).inverse.Additive :=
  Stacks.UniverseLift.RingTransport.sheafFunctor_additive _

variable [HasDerivedCategory.{t} (SheafOfModules.{max r w}
    (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)))]
  [HasDerivedCategory.{t'} (SheafOfModules.{max r w} (Stacks.SheafOfModules.Tensor.ringSheaf O))]

/-- **The derived lower shriek `Lg_! : D(O_C) ⥤ D(O_D)` on modules with sections in `max r w`**,
for any models of the two derived categories, read from the derived lower shriek over the raised
structure sheaf (formed there at the standard models, which do not appear in the result). -/
abbrev derivedLowerShriek :
    DerivedCategory (SheafOfModules.{max r w}
        (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O))) ⥤
      DerivedCategory (SheafOfModules.{max r w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max r w} (inverseImageRing J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))))
  letI := HasDerivedCategory.standard (SheafOfModules.{max r w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)))
  haveI := hasPointwiseLeftDerivedLowerShriek_of_essentiallySmall J K f _
    (SmallModel.lowerShriekModules_acyclic_of_essentiallySmall J K f
      (liftedStructureSheaf.{w} K O))
  Stacks.DerivedAdjunctionTransport.leftAdjoint (sourceModulesEquivalence.{w} J K f O)
    (targetModulesEquivalence.{w} K O) (totalLeftDerivedLowerShriek J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)))

/-- **`Lg_! ⊣ g^*`** for modules with sections in `max r w`, `g^*` being
`Stacks.SheafOfModules.inverseImage` applied degreewise. -/
def derivedLowerShriekAdjunction :
    derivedLowerShriek.{w} J K f O ⊣
      (Stacks.SheafOfModules.inverseImage.{max r w} J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapDerivedCategory :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max r w} (inverseImageRing J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))))
  letI := HasDerivedCategory.standard (SheafOfModules.{max r w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)))
  haveI := hasPointwiseLeftDerivedLowerShriek_of_essentiallySmall J K f _
    (SmallModel.lowerShriekModules_acyclic_of_essentiallySmall J K f
      (liftedStructureSheaf.{w} K O))
  Stacks.DerivedAdjunctionTransport.adjunction (sourceModulesEquivalence.{w} J K f O)
    (targetModulesEquivalence.{w} K O) _ _ (inverseImageCompIso.{w} J K f O)
    (totalLeftDerivedLowerShriekAdjunction J K f _
      (SmallModel.lowerShriekModules_acyclic_of_essentiallySmall J K f
        (liftedStructureSheaf.{w} K O)))

omit [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max r w} RingCat.{max r w})] in
/-- **`g^* Lg_! = id`** for modules with sections in `max r w`, for a fully faithful functor of
sites: the unit of `Lg_! ⊣ g^*` is invertible. It is the transport of the unit over the raised
structure sheaf, which is invertible by `isIso_totalLeftDerivedLowerShriekAdjunction_unit` and
the underived `g^* g_! = id` of `isIso_adjunctionModules_unit`. -/
theorem isIso_derivedLowerShriekAdjunction_unit [f.Full] [f.Faithful]
    [∀ F : Cᵒᵖ ⥤ RingCat.{max r w}, f.op.HasPointwiseRightKanExtension F]
    [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max r w}, f.op.HasPointwiseRightKanExtension F] :
    IsIso (derivedLowerShriekAdjunction.{w} J K f O).unit :=
  let := HasDerivedCategory.standard (SheafOfModules.{max r w} (inverseImageRing J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))))
  let := HasDerivedCategory.standard (SheafOfModules.{max r w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)))
  have hac := SmallModel.lowerShriekModules_acyclic_of_essentiallySmall J K f
    (liftedStructureSheaf.{w} K O)
  have := hasPointwiseLeftDerivedLowerShriek_of_essentiallySmall J K f _ hac
  Stacks.DerivedAdjunctionTransport.isIso_adjunction_unit _ _ _ _ _ _
    (isIso_totalLeftDerivedLowerShriekAdjunction_unit J K f _ hac
      (isIso_adjunctionModules_unit J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))))

/-- **`Lg_!` is computed degreewise**, at module universe `max r w` (Stacks 0794): for a
complex `L` of `O_C`-modules bounded above by `0` whose terms are carried by the transport to
direct sums of the `j_{U!} O_U` over the raised structure sheaf, `Lg_!(L)` is `g_!(L)` applied
degreewise, `g_!` being `Stacks.SheafOfModules.lowerShriek`. -/
def derivedLowerShriekObjQIso
    [UnivLE.{r, max r w}] [UnivLE.{v₁, max r w}] [UnivLE.{v₂, max r w}] [UnivLE.{u₁, max r w}]
    (L : CochainComplex (SheafOfModules.{max r w}
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O))) ℤ)
    (hL0 : CochainComplex.IsStrictlyLE L 0)
    (hL : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)))
      ((sourceModulesEquivalence.{w} J K f O).functor.obj (L.X n))) :
    (derivedLowerShriek.{w} J K f O).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (((Stacks.SheafOfModules.lowerShriek.{max r w} J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max r w} (inverseImageRing J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))))
  letI := HasDerivedCategory.standard (SheafOfModules.{max r w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O)))
  haveI := hasPointwiseLeftDerivedLowerShriek_of_essentiallySmall J K f _
    (SmallModel.lowerShriekModules_acyclic_of_essentiallySmall J K f
      (liftedStructureSheaf.{w} K O))
  let E₁ := (sourceModulesEquivalence.{w} J K f O).functor
  let E₂ := (targetModulesEquivalence.{w} K O).inverse
  let L₁ := (E₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have := hL0
  have hL₁ : CochainComplex.IsStrictlyLE L₁ 0 := inferInstance
  have := isIso_totalLeftDerivedLowerShriekCounit_app J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))
    (SmallModel.lowerShriekModules_acyclic_of_essentiallySmall J K f
      (liftedStructureSheaf.{w} K O)) L₁ hL₁ hL
  E₂.mapDerivedCategory.mapIso
      ((totalLeftDerivedLowerShriek J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))).mapIso
          (E₁.mapDerivedCategoryFactors.app L ≪≫
            ((DerivedCategory.quotientCompQhIso _).app L₁).symm) ≪≫
        asIso ((totalLeftDerivedLowerShriekCounit J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L₁)) ≪≫
        (DerivedCategory.quotientCompQhIso _).app _) ≪≫
    E₂.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (lowerShriekCompIso.{w} J K f O) (ComplexShape.up ℤ)).app L)

end Derived

end Stacks.Cohomology.DerivedLowerShriek.ULift

end
