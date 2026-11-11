module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroStalk
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction

import StacksCore.Tactic.StacksAttribute

/-!
# The derived lower shriek of a compactification

Let `j : X ⟶ X̄` be an open immersion in a big étale site and let `f̄ : X̄ ⟶ Y` be finite, so
that `f = j ≫ f̄` is quasi-finite and separated. The derived lower shriek is
`Rf_! = R f̄_* ∘ j_!`. Since `f̄` is finite, `f̄_*` is exact and `R f̄_* = f̄_*`, and since
`f̄_* ∘ j_! = f_!`, the functor `Rf_!` is the functor induced on unbounded derived categories by
the direct image with compact support `f_!`.

## Main definitions

* `Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso`: an exact functor isomorphic to a
  composite of exact functors induces the composite of the induced functors on unbounded derived
  categories.
* `AlgebraicGeometry.SmallEtale.etalePushforward`: direct image of abelian sheaves on the small
  étale sites.
* `AlgebraicGeometry.SmallEtale.properSupportToPushforward`: the inclusion `f_! ⟶ f_*` of the
  proper-support direct image, as a natural transformation.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriekIso`: for a compactification `f = j ≫ f̄`,
  `R f̄_* ∘ j_!` agrees with the functor induced on unbounded derived categories by `f_!`.

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportIsoPushforward`: for proper `f`, `f_! ≅ f_*`.
* `AlgebraicGeometry.SmallEtale.fShriekFunctorIsoProperSupport`: the sheafified finite-support
  direct image and the proper-support subsheaf of the direct image agree as functors.
* `AlgebraicGeometry.SmallEtale.fShriekFunctorIsoCompactification`: `f_! = f̄_* ∘ j_!` for
  `f = j ≫ f̄` with `j` an open immersion and `f̄` proper and locally quasi-finite.
* `AlgebraicGeometry.SmallEtale.etalePushforward_exact_of_isFinite`: direct image along a
  finite morphism is exact.
* `AlgebraicGeometry.SmallEtale.etalePushforward_isRightDerivedFunctor_of_isFinite`: for finite
  `f̄` the functor induced by `f̄_*` on derived categories is a total right derived functor of
  `f̄_*`.

## References

* [Stacks Project, Tag 0GKM](https://stacks.math.columbia.edu/tag/0GKM)
* [Stacks Project, Tag 0F52](https://stacks.math.columbia.edu/tag/0F52)
* [Stacks Project, Tag 0F6N](https://stacks.math.columbia.edu/tag/0F6N)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ v₂ v₃ u₁ u₂ u₃ u v

namespace Stacks.DerivedFunctor

section Localization

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w} C₃]

/-- An exact functor identified with a composite of two exact functors induces on unbounded
derived categories the composite of the induced functors. -/
public def mapDerivedCategoryCompIsoOfIso (H : C₁ ⥤ C₃) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : H ≅ F ⋙ G) :
    H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex e.symm (ComplexShape.up ℤ)) DerivedCategory.Q⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    H.mapDerivedCategory (F.mapDerivedCategory ⋙ G.mapDerivedCategory) (Iso.refl _)

end Localization

end Stacks.DerivedFunctor

namespace AlgebraicGeometry

/-! ### Exactness properties of extension by zero -/

section ExtensionByZero

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- Extension by zero of abelian étale sheaves preserves finite limits. -/
@[stacks 03S5 "left exactness of j_! in a big étale site"]
public instance abelianExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (abelianExtensionByZero B X hX U) :=
  ((exactFunctor_iff _).mp (abelianExtensionByZero_exact B X hX U)).1

/-- Extension by zero of abelian étale sheaves preserves finite colimits. -/
@[stacks 03S5 "right exactness of j_! in a big étale site"]
public instance abelianExtensionByZero_preservesFiniteColimits :
    PreservesFiniteColimits (abelianExtensionByZero B X hX U) :=
  ((exactFunctor_iff _).mp (abelianExtensionByZero_exact B X hX U)).2

/-- Extension by zero of abelian étale sheaves is additive. -/
public instance abelianExtensionByZero_additive :
    (abelianExtensionByZero B X hX U).Additive :=
  Functor.additive_of_preserves_binary_products _

end ExtensionByZero

namespace SmallEtale

section Composites

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} {a : X ⟶ Y} {b : Y ⟶ Z}

/-- The image in schemes of a composite of morphisms locally of finite type in a big étale site
is locally of finite type. -/
public instance locallyOfFiniteType_inclusion_map_comp
    [LocallyOfFiniteType (B.inclusion.map a)] [LocallyOfFiniteType (B.inclusion.map b)] :
    LocallyOfFiniteType (B.inclusion.map (a ≫ b)) := by
  change LocallyOfFiniteType (B.inclusion.map a ≫ B.inclusion.map b)
  infer_instance

/-- The image in schemes of a composite of locally quasi-finite morphisms in a big étale site is
locally quasi-finite. -/
@[ega "II 6.2.4" "(ii)"]
public instance locallyQuasiFinite_inclusion_map_comp
    [LocallyQuasiFinite (B.inclusion.map a)] [LocallyQuasiFinite (B.inclusion.map b)] :
    LocallyQuasiFinite (B.inclusion.map (a ≫ b)) := by
  change LocallyQuasiFinite (B.inclusion.map a ≫ B.inclusion.map b)
  infer_instance

/-- The image in schemes of a composite of separated morphisms in a big étale site is
separated. -/
public instance isSeparated_inclusion_map_comp
    [IsSeparated (B.inclusion.map a)] [IsSeparated (B.inclusion.map b)] :
    IsSeparated (B.inclusion.map (a ≫ b)) := by
  change IsSeparated (B.inclusion.map a ≫ B.inclusion.map b)
  infer_instance

end Composites

/-! ### Direct image and the proper-support subsheaf -/

section Pushforward

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (g : X ⟶ Y)

/-- Direct image `g_*` of abelian sheaves for the small étale topologies: restriction of
sections along base change. -/
public abbrev etalePushforward :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v} :=
  (smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

/-- Direct image of abelian étale sheaves is additive. -/
public instance etalePushforward_additive : (etalePushforward.{u, v} B g).Additive where
  map_add := by intros; rfl

variable [LocallyOfFiniteType (B.inclusion.map g)]

/-- The inclusion of the proper-support direct image `g_!` into the ordinary direct image
`g_*`, as a natural transformation of functors on abelian étale sheaves. -/
public def properSupportToPushforward :
    properSupportFunctor.{u, v} B g ⟶ etalePushforward.{u, v} B g where
  app F := (fShriekSubsheaf B g F).val.arrow
  naturality F H φ := (fShriekMap B g F H φ).property

/-- For a proper morphism the proper-support direct image is the ordinary
direct image, naturally in the abelian étale sheaf. -/
@[stacks 0F51 "natural isomorphism f_! ≅ f_* for proper f"]
public def properSupportIsoPushforward [IsProper (B.inclusion.map g)] :
    properSupportFunctor.{u, v} B g ≅ etalePushforward.{u, v} B g :=
  have : ∀ F, IsIso ((properSupportToPushforward.{u, v} B g).app F) := fun F =>
    fShriekSubsheaf_arrow_isIso B g F
  have : IsIso (properSupportToPushforward.{u, v} B g) := NatIso.isIso_of_isIso_app _
  asIso (properSupportToPushforward.{u, v} B g)

/-- The two models of the direct image with compact support agree: the
sheafification of the finite-support direct image presheaf is the proper-support subsheaf of
the ordinary direct image. -/
@[stacks 0F6N "functor comparison of the two models of f_!"]
public def fShriekFunctorIsoProperSupport [IsSeparated (B.inclusion.map g)]
    [LocallyQuasiFinite (B.inclusion.map g)] :
    fShriekFunctor.{u, v} B g ≅ properSupportFunctor.{u, max (u + 1) v} B g :=
  let J := SmallEtale.topology B Y.obj Y.property
  let L := presheafToSheaf J AddCommGrpCat.{max (u + 1) v}
  let R := sheafToPresheaf J AddCommGrpCat.{max (u + 1) v}
  have : IsIso (sheafificationAdjunction J AddCommGrpCat.{max (u + 1) v}).counit :=
    NatIso.isIso_of_isIso_app _
  Functor.isoWhiskerRight (finiteSupportPushforwardIso.{u, max (u + 1) v} B g).val L ≪≫
    Functor.associator _ R L ≪≫
    Functor.isoWhiskerLeft (properSupportFunctor.{u, max (u + 1) v} B g)
      (asIso (sheafificationAdjunction J AddCommGrpCat.{max (u + 1) v}).counit) ≪≫
    (properSupportFunctor.{u, max (u + 1) v} B g).rightUnitor

end Pushforward

/-! ### `f_! = f̄_* ∘ j_!` through a compactification -/

section Compactification

variable (B : BigEtaleSite.{u}) {Xbar Y : B.Scheme} (fbar : Xbar ⟶ Y)
  [IsProper (B.inclusion.map fbar)] (U : SmallEtale B Xbar.obj Xbar.property)
  [IsOpenImmersion (B.inclusion.map U.obj.hom)]

/-- The canonical comparison `f_! ⟶ f̄_! ∘ j_!` of proper-support direct
images through a compactification `j : X ⟶ X̄` of `X` over `Y`, as a natural isomorphism of
functors on abelian étale sheaves. -/
@[stacks 0F52 "natural isomorphism of proper-support functors"]
public def compactificationProperSupportIso
    [LocallyOfFiniteType (B.inclusion.map U.obj.hom)] :
    properSupportFunctor.{u, u + 1} B (U.obj.hom ≫ fbar) ≅
      abelianExtensionByZero B Xbar.obj Xbar.property U ⋙
        properSupportFunctor.{u, u + 1} B fbar :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ _ (compactificationFShriekMap_isIso B fbar U F))
    (fun {F H} φ => compactificationFShriekMap_naturality B fbar U F H φ
      ((properSupportFunctor.{u, u + 1} B (U.obj.hom ≫ fbar)).map φ)
      ((properSupportFunctor.{u, u + 1} B fbar).map
        ((abelianExtensionByZero B Xbar.obj Xbar.property U).map φ))
      (fShriekMap B (U.obj.hom ≫ fbar) F H φ).property
      (fShriekMap B fbar _ _
        ((abelianExtensionByZero B Xbar.obj Xbar.property U).map φ)).property)

/-- `f_! = f̄_* ∘ j_!`: the direct image with compact support along
`f = j ≫ f̄`, for `j : X ⟶ X̄` an open immersion and `f̄ : X̄ ⟶ Y` proper, is extension by zero
along `j` followed by the ordinary direct image along `f̄`. -/
@[stacks 0F52 "f_! = f̄_* ∘ j_!"]
public def fShriekFunctorIsoCompactification
    [LocallyQuasiFinite (B.inclusion.map fbar)] :
    fShriekFunctor.{u, u} B (U.obj.hom ≫ fbar) ≅
      abelianExtensionByZero B Xbar.obj Xbar.property U ⋙
        etalePushforward.{u, u + 1} B fbar :=
  fShriekFunctorIsoProperSupport.{u, u} B (U.obj.hom ≫ fbar) ≪≫
    compactificationProperSupportIso.{u} B fbar U ≪≫
    Functor.isoWhiskerLeft (abelianExtensionByZero B Xbar.obj Xbar.property U)
      (properSupportIsoPushforward.{u, u + 1} B fbar)

end Compactification

/-! ### Direct image along a finite morphism is exact -/

section Finite

variable (B : BigEtaleSite.{u}) {Xbar Y : B.Scheme} (fbar : Xbar ⟶ Y)
  [IsFinite (B.inclusion.map fbar)]

/-- Direct image of abelian étale sheaves along a finite morphism is exact. -/
@[stacks 03QP "exactness of direct image along a finite morphism"]
public theorem etalePushforward_exact_of_isFinite :
    exactFunctor _ _ (etalePushforward.{u, u + 1} B fbar) :=
  let e : fShriekFunctor.{u, u} B fbar ≅ etalePushforward.{u, u + 1} B fbar :=
    fShriekFunctorIsoProperSupport.{u, u} B fbar ≪≫ properSupportIsoPushforward.{u, u + 1} B fbar
  have ⟨_, _⟩ := fShriekFunctor_exact.{u, u} B fbar
  (exactFunctor_iff _).2
    ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e⟩

/-- Direct image along a finite morphism preserves finite limits. -/
public instance etalePushforward_preservesFiniteLimits_of_isFinite :
    PreservesFiniteLimits (etalePushforward.{u, u + 1} B fbar) :=
  ((exactFunctor_iff _).mp (etalePushforward_exact_of_isFinite.{u} B fbar)).1

/-- Direct image along a finite morphism preserves finite colimits. -/
public instance etalePushforward_preservesFiniteColimits_of_isFinite :
    PreservesFiniteColimits (etalePushforward.{u, u + 1} B fbar) :=
  ((exactFunctor_iff _).mp (etalePushforward_exact_of_isFinite.{u} B fbar)).2

end Finite

/-! ### The derived lower shriek of a compactification -/

section Derived

variable (B : BigEtaleSite.{u}) {Xbar Y : B.Scheme} (fbar : Xbar ⟶ Y)
  [IsFinite (B.inclusion.map fbar)] (U : SmallEtale B Xbar.obj Xbar.property)
  [IsOpenImmersion (B.inclusion.map U.obj.hom)]
  [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B U.obj.left)]
  [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B Xbar)]
  [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B Y)]

/-- `R f̄_* = f̄_*`: for a finite morphism `f̄` the functor induced on unbounded derived
categories by the direct image `f̄_*` is a total right derived functor of `f̄_*`. This is the
step `R f̄_* = f̄_*` of the proof of Stacks 0GKM. -/
public theorem etalePushforward_isRightDerivedFunctor_of_isFinite :
    (etalePushforward.{u, u + 1} B fbar).mapDerivedCategory.IsRightDerivedFunctor
      (etalePushforward.{u, u + 1} B fbar).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (AbelianSheaf.{u, u} B Xbar) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact _

/-- For an open immersion `j : X ⟶ X̄` in a big étale site and a finite `f̄ : X̄ ⟶ Y`, so that
`f = j ≫ f̄` is quasi-finite and separated, the derived lower shriek `Rf_! = R f̄_* ∘ j_!` agrees
with the functor induced on unbounded derived categories of abelian étale sheaves by the direct
image with compact support `f_!`. -/
public def derivedLowerShriekIso :
    (fShriekFunctor.{u, u} B (U.obj.hom ≫ fbar)).mapDerivedCategory ≅
      (abelianExtensionByZero B Xbar.obj Xbar.property U).mapDerivedCategory ⋙
        (etalePushforward.{u, u + 1} B fbar).mapDerivedCategory :=
  have hf := (exactFunctor_iff _).mp (fShriekFunctor_exact.{u, u} B (U.obj.hom ≫ fbar))
  have := hf.1
  have := hf.2
  Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
    (fShriekFunctorIsoCompactification.{u} B fbar U)

end Derived

end SmallEtale

end AlgebraicGeometry

end
