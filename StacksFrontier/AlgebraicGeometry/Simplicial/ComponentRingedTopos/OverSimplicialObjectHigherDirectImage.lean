module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.Algebra.Homology.DerivedCategory.IsZeroRightDerivedOfSingleComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringSimplicialObjectModuleCohomologicalDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.OverSimplicialObjectModuleDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.UnboundedBaseChangeForACocontinuousSquare
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectComparison
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Higher direct images of abelian sheaves along a hypercovering, in the model `n ↦ C/U_n`

Let `C` be a site with fibre products and `a : U ⟶ X` a hypercovering of `X` in `C`. For every
abelian sheaf `M` on `C/X` the higher direct images of `a⁻¹M` along the augmentation
`(C/U)_total ⟶ C/X` vanish: `Rⁿa_*(a⁻¹M) = 0` for `n > 0`. This is the abelian content of
Stacks 0D8L and 0DAC, here in Mathlib's `ℕ`-indexed right derived functors and in the model
`n ↦ C/U_n` of the total site.

It is read off Stacks 0D8L in the semi-representable model (the comparison of the degreewise and
the derived direct image is invertible at `a⁻¹M`), and carried across the morphism of simplicial
sites between the two models, whose total functor induces an equivalence of the categories of
abelian sheaves: the direct image in one model is the direct image in the other after that
equivalence, and an equivalence is exact and preserves injectives, so the right derived functors
agree (`Stacks.RightDerivedComp.objIsoOfAcyclicImage`).

## Main results

* `isZero_rightDerived_abelianTotalPushforwardOver_obj_overSimplicialObjectHigherDirectImage`
  (in `CategoryTheory.SimplicialSemiRepresentable`): the semi-representable model.
* `isZero_rightDerived_of_isZero_rightDerived_overSimplicialObjectHigherDirectImage`
  (in `CategoryTheory.CocontinuousSimplicialSite.Morphism`): transport of the vanishing between
  total sites.
* `isZero_rightDerived_augmentationFunctor_obj_overSimplicialObjectHigherDirectImage`
  (in `CategoryTheory.SimplicialOver`): the model `n ↦ C/U_n`.

## References

* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0DAC](https://stacks.math.columbia.edu/tag/0DAC)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard additive_abelianTotalPushforwardOver
  additive_abelianTotalInverseImageOver preservesFiniteColimits_abelianTotalInverseImageOver
  hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver
  hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **Stacks 0D8L in `ℕ`-indexed form**, in the semi-representable model: for a hypercovering
`K` of `X` and an abelian sheaf `M` on `C/X`, `Rⁿa_*(a⁻¹M) = 0` for `n > 0`. The comparison of
the degreewise and the derived direct image is invertible at `a⁻¹(M[0])`. -/
theorem isZero_rightDerived_abelianTotalPushforwardOver_obj_overSimplicialObjectHigherDirectImage
    (hK : IsHypercovering P K)
    (M : AbelianSheavesOver P.toGrothendieck X) (n : ℕ) (hn : 0 < n) :
    IsZero (((abelianTotalPushforwardOver P.toGrothendieck X K).rightDerived n).obj
      ((abelianTotalInverseImageOver P.toGrothendieck X K).obj M)) := by
  refine
    Functor.isZero_rightDerived_obj_of_isIso_app_singleFunctor_isZeroRightDerivedOfSingleComparison
      _ (derivedAbelianTotalPushforwardOver P.toGrothendieck X K)
      (derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X K)
      (fun L => ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion _).app L, inferInstance,
        inferInstance⟩) _ ?_ n hn
  exact (NatTrans.isIso_app_iff_of_iso _
    ((Functor.mapHomotopyCategorySingleFunctor
      (abelianTotalInverseImageOver P.toGrothendieck X K) 0).app M)).mp
    (isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage_of_isHypercovering P K hK _)

end CategoryTheory.SimplicialSemiRepresentable

namespace CategoryTheory.CocontinuousSimplicialSite.Morphism

variable {C C' : CocontinuousSimplicialSite.{u}} (h : Morphism C C')
  [∀ n, (h.hom.app n).toFunctor.IsEquivalence]
  (hc : ∀ n, (h.hom.app n).toFunctor.IsContinuous (topologyOfCoverings (C.coverage n))
    (topologyOfCoverings (C'.coverage n)))

include hc in
/-- **Transport of the vanishing of higher direct images between total sites.** Let `F₁` and
`F₂` be continuous and cocontinuous functors from the total sites of `C` and of `C'` to a site
`D`, with `h_total ⋙ F₂ ≅ F₁`. If `Rⁿ(F₁)_*(F₁⁻¹M) = 0`, then `Rⁿ(F₂)_*(F₂⁻¹M) = 0`: restriction
along `h_total` is an equivalence of the categories of abelian sheaves which identifies the two
direct images. -/
theorem isZero_rightDerived_of_isZero_rightDerived_overSimplicialObjectHigherDirectImage
    {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D)
    (F₁ : Grothendieck C.underlying ⥤ D) (F₂ : Grothendieck C'.underlying ⥤ D)
    [i₁ : F₁.IsContinuous (SimplicialCoverings.totalTopology C.underlying C.coverage) K]
    [i₂ : F₂.IsContinuous (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K]
    [i₃ : F₁.IsCocontinuous (SimplicialCoverings.totalTopology C.underlying C.coverage) K]
    [i₄ : F₂.IsCocontinuous (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K]
    (e : h.totalFunctor ⋙ F₂ ≅ F₁) (M : Sheaf K AddCommGrpCat.{u}) (n : ℕ)
    (hM : IsZero (((F₁.sheafPushforwardCocontinuous AddCommGrpCat.{u}
        (SimplicialCoverings.totalTopology C.underlying C.coverage) K).rightDerived n).obj
      ((F₁.sheafPushforwardContinuous AddCommGrpCat.{u}
        (SimplicialCoverings.totalTopology C.underlying C.coverage) K).obj M))) :
    IsZero (((F₂.sheafPushforwardCocontinuous AddCommGrpCat.{u}
        (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K).rightDerived n).obj
      ((F₂.sheafPushforwardContinuous AddCommGrpCat.{u}
        (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K).obj M)) := by
  have := totalFunctor_isContinuous_totalSiteEquivalence h hc
  have := isDenseSubsite_totalFunctor_totalSiteEquivalence h hc
  have : h.totalFunctor.IsCocontinuous
      (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    totalFunctor_isCocontinuous h
  let R := h.totalFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
    (SimplicialCoverings.totalTopology C.underlying C.coverage)
    (SimplicialCoverings.totalTopology C'.underlying C'.coverage)
  let E := R.asEquivalence
  let iso : F₂.sheafPushforwardContinuous AddCommGrpCat.{u}
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K ⋙ R ≅
      F₁.sheafPushforwardContinuous AddCommGrpCat.{u}
        (SimplicialCoverings.totalTopology C.underlying C.coverage) K :=
    Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{u} _ _ K
  let P₁ := F₁.sheafPushforwardCocontinuous AddCommGrpCat.{u}
    (SimplicialCoverings.totalTopology C.underlying C.coverage) K
  let P₂ := F₂.sheafPushforwardCocontinuous AddCommGrpCat.{u}
    (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K
  let ε : P₁ ≅ E.inverse ⋙ P₂ :=
    Adjunction.rightAdjointUniq
      (F₁.sheafAdjunctionCocontinuous AddCommGrpCat.{u}
        (SimplicialCoverings.totalTopology C.underlying C.coverage) K)
      (((F₂.sheafAdjunctionCocontinuous AddCommGrpCat.{u}
        (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K).comp
          E.toAdjunction).ofNatIsoLeft iso)
  have : P₁.Additive := additive_sheafPushforwardCocontinuous_ab _ _ F₁
  have : P₂.Additive := additive_sheafPushforwardCocontinuous_ab _ _ F₂
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : P₂.IsRightAdjoint := (F₂.sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K).isRightAdjoint
  let N := (F₂.sheafPushforwardContinuous AddCommGrpCat.{u}
    (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K).obj M
  have h₁ : IsZero (((E.inverse ⋙ P₂).rightDerived n).obj (R.obj N)) :=
    hM.of_iso (((E.inverse ⋙ P₂).rightDerived n).mapIso (iso.app M) ≪≫
      ((Functor.rightDerivedIsoOfIso ε n).app _).symm)
  exact h₁.of_iso ((P₂.rightDerived n).mapIso (E.unitIso.app N) ≪≫
    (Stacks.RightDerivedComp.objIsoOfAcyclicImage E.inverse P₂
      (fun m hm => Functor.isZero_rightDerived_of_exact E.inverse _ m hm)
      (fun Z _ => Stacks.RightDerivedComp.acyclic_of_injective P₂ (E.inverse.obj Z)) n).symm)

end CategoryTheory.CocontinuousSimplicialSite.Morphism

namespace CategoryTheory.SimplicialOver

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C)
  {U : SimplicialObject C} {X : C} {a : U ⟶ (SimplicialObject.const C).obj X}

/-- **Stacks 0D8L / 0DAC on abelian sheaves, in the model `n ↦ C/U_n`.** Let `a : U ⟶ X` be a
hypercovering of `X` in `C`, the topology `J` of `C` being generated by `P`. For every abelian
sheaf `M` on `C/X`, the higher direct images of its restriction along `V/U_n ↦ V/X` vanish:
`Rⁿa_*(a⁻¹M) = 0` for `n > 0`. -/
theorem isZero_rightDerived_augmentationFunctor_obj_overSimplicialObjectHigherDirectImage
    {J : GrothendieckTopology C}
    (hJ : P.toGrothendieck = J) (h : IsHypercoveringAugmentation P U a)
    (M : Sheaf (J.over X) AddCommGrpCat.{u}) (n : ℕ) (hn : 0 < n) :
    IsZero ((((augmentationFunctor U a).sheafPushforwardCocontinuous AddCommGrpCat.{u}
        (totalTopology J U) (J.over X)).rightDerived n).obj
      (((augmentationFunctor U a).sheafPushforwardContinuous AddCommGrpCat.{u}
        (totalTopology J U) (J.over X)).obj M)) := by
  open SimplicialSemiRepresentable in
  subst hJ
  exact (semiRepresentableMorphismOverSimplicialObjectComparison a P.toGrothendieck
    ).isZero_rightDerived_of_isZero_rightDerived_overSimplicialObjectHigherDirectImage
    (semiRepresentableMorphism_isContinuous_overSimplicialObjectComparison a _)
    (P.toGrothendieck.over X)
    (SimplicialSemiRepresentable.totalForget (associatedSimplicialObject.{u} U a))
    (augmentationFunctor U a)
    (i₁ := SimplicialSemiRepresentable.totalForget_isContinuous _ _)
    (i₂ := augmentationFunctor_isContinuous_overSimplicialObjectComparison P.toGrothendieck a)
    (i₃ := SimplicialSemiRepresentable.totalForget_isCocontinuous _ _)
    (i₄ := augmentationFunctor_isCocontinuous P.toGrothendieck U a)
    (semiRepresentableAugmentationIsoOverSimplicialObjectComparison a _) M n
    (isZero_rightDerived_abelianTotalPushforwardOver_obj_overSimplicialObjectHigherDirectImage P
      (associatedSimplicialObject.{u} U a) (h.isHypercovering P U a) M n hn)

end CategoryTheory.SimplicialOver

namespace CategoryTheory.SimplicialOver

open AlgebraicGeometry

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {U : SimplicialObject C} {X : C}
  {a : U ⟶ (SimplicialObject.const C).obj X} {J : GrothendieckTopology C}

/-- For a cocontinuous functor `w` of sites, the underlying abelian sheaf of an injective sheaf
of modules is acyclic for the direct image along `w` (Stacks 0D6J): its single complex is
K-injective, and there the comparison of the degreewise and the derived direct image of abelian
sheaves is invertible. -/
theorem isZero_rightDerived_sheafPushforwardCocontinuous_toSheaf_of_injective
    {C₁ : Type u} [SmallCategory C₁] {D : Type u} [SmallCategory D]
    (J₁ : GrothendieckTopology C₁) (K : GrothendieckTopology D) (w : C₁ ⥤ D)
    [w.IsCocontinuous J₁ K] (O : Sheaf J₁ RingCat.{u}) (Z : SheafOfModules.{u} O)
    (hZ : Injective Z) (n : ℕ) (hn : 0 < n) :
    haveI := additive_sheafPushforwardCocontinuous_ab J₁ K w
    IsZero (((w.sheafPushforwardCocontinuous AddCommGrpCat.{u} J₁ K).rightDerived n).obj
      ((SheafOfModules.toSheaf O).obj Z)) := by
  let := HasDerivedCategory.standard (Sheaf J₁ AddCommGrpCat.{u})
  let := HasDerivedCategory.standard (Sheaf K AddCommGrpCat.{u})
  have := additive_sheafPushforwardCocontinuous_ab J₁ K w
  let I : CochainComplex (SheafOfModules.{u} O) ℤ :=
    (HomologicalComplex.single (SheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj Z
  have : ∀ m : ℤ, Injective (I.X m) := fun m => by
    by_cases hm : m = 0
    · subst hm
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).symm
        inferInstance
    · exact Injective.of_iso (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Z m
        hm).isoZero.symm inferInstance
  have : CochainComplex.IsKInjective I := CochainComplex.isKInjective_of_injective I 0
  have hI :=
    Stacks.Cohomology.CocontinuousForgetModule.abelianPushforwardUnit_isIso_at_underlying_kInjective
      J₁ K w O I
  refine
    Functor.isZero_rightDerived_obj_of_isIso_app_singleFunctor_isZeroRightDerivedOfSingleComparison
      _ (Stacks.Cohomology.CocontinuousForgetModule.derivedAbelianPushforward J₁ K w)
      (Stacks.Cohomology.CocontinuousForgetModule.derivedAbelianPushforwardUnit J₁ K w)
      (fun L => ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion _).app L, inferInstance,
        inferInstance⟩) _ ?_ n hn
  refine (NatTrans.isIso_app_iff_of_iso _ ?_).mp hI
  exact (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (SheafOfModules.toSheaf O)
        (ComplexShape.up ℤ) 0).app Z) ≪≫
    ((HomotopyCategory.singleFunctorPostcompQuotientIso (Sheaf J₁ AddCommGrpCat.{u}) 0).app
      ((SheafOfModules.toSheaf O).obj Z)).symm

variable (P : Pretopology C) (hJ : P.toGrothendieck = J) (h : IsHypercoveringAugmentation P U a)

include hJ h in
/-- **Stacks 0DAC in `ℕ`-indexed form, in the model `n ↦ C/U_n`.** Let `a : U ⟶ X` be a
hypercovering of `X` in `C` and `f : (Sh((C/U)_total), O) ⟶ (Sh(C/X), O_X)` a morphism of ringed
topoi whose inverse image is restriction along `V/U_n ↦ V/X` and whose structure map is the
identification `O = f⁻¹O_X`. Then for every `O_X`-module `E`, `Rⁿf_*(f^*E) = 0` for `n > 0`.

The direct image of modules is, on underlying abelian sheaves, the direct image along
`V/U_n ↦ V/X`, which carries the underlying abelian sheaves of injective modules to acyclic
objects (Stacks 0D6J); the underlying abelian sheaf of `f^*E` is the restriction of that of `E`;
so the vanishing is the abelian one,
`isZero_rightDerived_augmentationFunctor_obj_overSimplicialObjectHigherDirectImage`. -/
theorem isZero_rightDerived_pushforwardModules_pullbackModules_overSimplicialObjectHigherDirectImage
    {O : Sheaf (totalTopology J U) CommRingCat.{u}}
    {OX : Sheaf (J.over X) CommRingCat.{u}}
    (f : RingedToposHom { C := Grothendieck (slices U), J := totalTopology J U, O := O }
      { C := Over X, J := J.over X, O := OX })
    [hf : IsIso f.fSharpInverseImage]
    (e : f.toToposHom.inverseImage ≅ (augmentationFunctor U a).sheafPushforwardContinuous (Type u)
      (totalTopology J U) (J.over X))
    (E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OX)) (n : ℕ) (hn : 0 < n) :
    haveI := RingedToposHom.pushforwardModules_additive f
    IsZero (((RingedToposHom.pushforwardModules f).rightDerived n).obj
      (f.toModulesHom.pullbackModules.obj E)) := by
  have := RingedToposHom.pushforwardModules_additive f
  let R₁ := Stacks.SheafOfModules.Tensor.ringSheaf O
  let R₂ := Stacks.SheafOfModules.Tensor.ringSheaf OX
  let W := SheafOfModules.toSheaf.{u} R₁
  let W' := SheafOfModules.toSheaf.{u} R₂
  let F₂ := augmentationFunctor U a
  let T := F₂.sheafPushforwardCocontinuous AddCommGrpCat.{u} (totalTopology J U) (J.over X)
  let fP := Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u, u, u} f.toModulesHom
  let fA := Stacks.Topos.AbelianPushforward.abelianPushforward (totalTopology J U) f.toToposHom
  let adjA := Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward
    (totalTopology J U) f.toToposHom
  let adjT := F₂.sheafAdjunctionCocontinuous AddCommGrpCat.{u} (totalTopology J U) (J.over X)
  have : T.Additive := additive_sheafPushforwardCocontinuous_ab _ _ F₂
  have : T.IsRightAdjoint := adjT.isRightAdjoint
  have : f.toModulesHom.pullbackModules.Additive := RingedToposHom.pullbackModules_additive f
  have : fP.Additive :=
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      f.toModulesHom).right_adjoint_additive
  have : HasZeroObject (Sheaf (J.over X) AddCommGrpCat.{u}) := hasZeroObject_of_hasTerminal_object
  have : HasZeroObject (Sheaf (totalTopology J U) AddCommGrpCat.{u}) :=
    hasZeroObject_of_hasTerminal_object
  have : (Sites.abelianInverseImage (J := totalTopology J U) f.toToposHom).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have : (Sites.abelianInverseImage (J := totalTopology J U) f.toToposHom).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : fA.Additive := adjA.right_adjoint_additive
  have : HasBinaryBiproducts (SheafOfModules.{u} R₁) := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasBinaryBiproducts (SheafOfModules.{u} R₂) := HasBinaryBiproducts.of_hasBinaryProducts
  have : (F₂.sheafPushforwardContinuous (Type u) (totalTopology J U) (J.over X)).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F₂ (Type u)
      (totalTopology J U) (J.over X)).isRightAdjoint
  let eAb : Sites.abelianInverseImage (J := totalTopology J U) f.toToposHom ≅
      F₂.sheafPushforwardContinuous AddCommGrpCat.{u} (totalTopology J U) (J.over X) :=
    Sites.abelianInverseImageIsoSheafPushforwardContinuous F₂ (totalTopology J U) (J.over X)
      f.toToposHom e
  have : (F₂.sheafPushforwardContinuous AddCommGrpCat.{u} (totalTopology J U)
      (J.over X)).Additive := Functor.additive_of_iso eAb
  let ePush : fA ≅ T := Adjunction.rightAdjointUniq adjA (adjT.ofNatIsoLeft eAb.symm)
  let ePM : fP ⋙ W' ≅ W ⋙ T :=
    Stacks.Cohomology.abelianSheafNatIsoOfUnderlying (J.over X) (fP ⋙ W') (W ⋙ fA)
      (Iso.refl _) ≪≫ Functor.isoWhiskerLeft W ePush
  let ePB : f.toModulesHom.pullbackModules ⋙ W ≅
      W' ⋙ F₂.sheafPushforwardContinuous AddCommGrpCat.{u} (totalTopology J U) (J.over X) :=
    Stacks.Cohomology.abelianSheafNatIsoOfUnderlying (totalTopology J U)
      (f.toModulesHom.pullbackModules ⋙ W)
      (W' ⋙ Sites.abelianInverseImage (J := totalTopology J U) f.toToposHom)
      (RingedToposHom.pullbackUnderlyingIsoOfIsIso f) ≪≫ Functor.isoWhiskerLeft W' eAb
  have hab : IsZero ((T.rightDerived n).obj (W.obj (f.toModulesHom.pullbackModules.obj E))) :=
    (isZero_rightDerived_augmentationFunctor_obj_overSimplicialObjectHigherDirectImage P hJ h
      (W'.obj E) n hn).of_iso ((T.rightDerived n).mapIso (ePB.app E))
  have : W.PreservesHomology := Functor.preservesHomologyOfExact W
  have : W'.PreservesHomology := Functor.preservesHomologyOfExact W'
  have hcomp : IsZero (((fP ⋙ W').rightDerived n).obj (f.toModulesHom.pullbackModules.obj E)) :=
    hab.of_iso ((Functor.rightDerivedIsoOfIso ePM n).app _ ≪≫
      Stacks.RightDerivedComp.objIsoOfAcyclicImage W T
        (fun m hm => Functor.isZero_rightDerived_of_exact W _ m hm)
        (fun Z hZ m hm =>
          isZero_rightDerived_sheafPushforwardCocontinuous_toSheaf_of_injective
            (totalTopology J U) (J.over X) F₂ R₁ Z hZ m hm)
        n)
  obtain ⟨i⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology fP W' n
    (f.toModulesHom.pullbackModules.obj E)
  have hW : IsZero (W'.obj ((fP.rightDerived n).obj (f.toModulesHom.pullbackModules.obj E))) :=
    hcomp.of_iso i
  have hfP : IsZero ((fP.rightDerived n).obj (f.toModulesHom.pullbackModules.obj E)) := by
    rw [IsZero.iff_id_eq_zero]
    exact W'.map_injective (by rw [W'.map_id, W'.map_zero]; exact hW.eq_of_src _ _)
  exact hfP.of_iso ((Functor.rightDerivedIsoOfIso f.toModulesPushforwardIso n).app _).symm

end CategoryTheory.SimplicialOver

end
