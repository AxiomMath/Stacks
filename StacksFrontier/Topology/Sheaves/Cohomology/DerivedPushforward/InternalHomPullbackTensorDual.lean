module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomComparisonTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackTensorIsoAssociator
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkTransportClauses
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLawGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.TensorDualToSheafHomTranspose
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeComparisonMaps

/-!
# The canonical map of Tag 08I3 on `K ⊗^L R𝓗om(E, 𝒪)`

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `E, K ∈ D(𝒪_Y)`.  There is a
canonical map `K ⊗^L R𝓗om(E, 𝒪_Y) ⟶ R𝓗om(E, K)`, the transpose of

`(K ⊗^L R𝓗om(E, 𝒪_Y)) ⊗^L E ⟶ K ⊗^L (R𝓗om(E, 𝒪_Y) ⊗^L E) ⟶ K ⊗^L 𝒪_Y ⟶ K`.

This file proves that the derived pullback of it, followed by the canonical map of Tag 08I3, is
the comparison of Tag 079U followed by the canonical map of Tag 08I3 on the dual and by the map of
the same kind on `X` for `Lh^*E` and `Lh^*K`.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.tensorDualToSheafHom`: the map
  `K ⊗^L R𝓗om(E, 𝒪) ⟶ R𝓗om(E, K)`.
* `Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackDualMap`: the canonical map
  `Lh^*R𝓗om(E, 𝒪_Y) ⟶ R𝓗om(Lh^*E, 𝒪_X)`.

## Main results

* `map_tensorDualToSheafHom_comp_derivedPullbackSheafHomMap`: the derived pullback of
  `K ⊗^L R𝓗om(E, 𝒪) ⟶ R𝓗om(E, K)`, followed by the canonical map of Tag 08I3, is the comparison
  of Tag 079U followed by the map of the same kind on `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback

open Stacks.Cohomology.DerivedProjectionFormula (singleUnit derivedPullbackUnitIso)

universe u

section Pinned

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Sheaf TopCat.Presheaf.IsSheaf

-- `Tensor.ringSheaf` is opened at `instance_reducible`, the transparency at which the congruence
-- `convert` builds compares the instance arguments of a coercion, as in
-- `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackModels`.
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable (Z : AlgebraicGeometry.RingedSpace.{u, u})

/-- The bijection of Tag 08DI at the spelling of the derived pullback is the one of the ringed
space, as a family. -/
theorem tensorHomEquiv_eq_family :
    tensorHomEquiv Z = fun A B C =>
      (Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf A B C).toEquiv := rfl

/-- The bijection of Tag 08DI at the spelling of the derived pullback is the one of the ringed
site of the space, as a family. -/
theorem tensorHomEquiv_eq_curry :
    tensorHomEquiv Z = fun A B C =>
      (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).toEquiv := rfl

/-- The bijection of Tag 08DI is natural in its source variable. -/
theorem tensorHomEquiv_naturalLeft :
    Transpose.TensorHomEquivNaturalLeft (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
      (internalHomTensorUncurried Z) (tensorHomEquiv Z) := by
  rw [tensorHomEquiv_eq_family]
  intro A A' B C φ ψ
  exact Stacks.SheafOfModules.derivedSheafHomTensorEquiv_toEquiv_naturality_source Z.sheaf
    A A' B C φ ψ

/-- The bijection of Tag 08DI is natural in its target variable, in the argument order of the
transpose construction. -/
theorem tensorHomEquiv_naturality_target
    (A B C C' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    (f : A ⟶ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).obj C) (g : C ⟶ C') :
    tensorHomEquiv Z A B C' (f ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj
      (op B)).map g) = tensorHomEquiv Z A B C f ≫ g := by
  revert A B C C' f g
  rw [tensorHomEquiv_eq_curry]
  intro A B C C' f g
  convert derivedCurryHomEquiv_naturality_target_ringedSpace_toEquiv Z A B g f using 1

/-- The evaluation of Tag 08DI is the counit. -/
theorem evaluation_tensorHomEquiv
    (B M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    Transpose.evaluation (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
        (internalHomTensorUncurried Z) (tensorHomEquiv Z) B M =
      Stacks.SheafOfModules.derivedSheafHomCounit Z.sheaf B M := by
  unfold Transpose.evaluation
  revert B M
  rw [tensorHomEquiv_eq_family]
  intro B M
  exact Stacks.SheafOfModules.derivedSheafHomTensorEquiv_toEquiv_id Z.sheaf B M

/-- **The canonical map `K ⊗^L R𝓗om(E, 𝒪_Z) ⟶ R𝓗om(E, K)` of Tag 08I1**, with its source written
at the derived tensor product of the internal hom. -/
abbrev canonicalTensorDualMap
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (internalHomTensorUncurried Z).obj
        (K, ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj (singleUnit Z)) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj K :=
  Stacks.SheafOfModules.derivedTensorDualToSheafHom Z.sheaf E K

/-- The contraction against the application morphism of Stacks 08J8 is the contraction against
the evaluation of the bijection of Tag 08DI. -/
theorem contraction_derivedSheafHomCounit_eq_evaluation
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (internalHomTensorUncurried Z).map
        (𝟙 ((internalHomTensorUncurried Z).obj
          (K, ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj (singleUnit Z))) ×ₘ
          𝟙 E) ≫
        (Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf K
            (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj (singleUnit Z)) E ≫
          (internalHomTensorUncurried Z).map
            (𝟙 K ×ₘ Stacks.SheafOfModules.derivedSheafHomCounit Z.sheaf E (singleUnit Z)) ≫
          Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf K) =
      Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf K
          (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj (singleUnit Z)) E ≫
        (internalHomTensorUncurried Z).map (𝟙 K ×ₘ
          Transpose.evaluation (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
            (internalHomTensorUncurried Z) (tensorHomEquiv Z) E (singleUnit Z)) ≫
          Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf K :=
  (congrArg (· ≫ _) ((internalHomTensorUncurried Z).map_id _)).trans
    ((Category.id_comp _).trans (congrArg (fun x =>
      Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf K
        (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj (singleUnit Z)) E ≫
      (internalHomTensorUncurried Z).map (𝟙 K ×ₘ x) ≫
        Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf K)
      (evaluation_tensorHomEquiv Z E (singleUnit Z)).symm))

/-- The map `K ⊗^L R𝓗om(E, 𝒪_Z) ⟶ R𝓗om(E, K)` built from the transpose of the contraction
against the evaluation, with the right unit constraint of Tag 0FPT, is the canonical map of
Tag 08I1. -/
theorem dualTensorMap_derivedRightUnitorHom_eq_canonicalTensorDualMap
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    Transpose.dualTensorMap (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
        (internalHomTensorUncurried Z) (tensorHomEquiv Z)
        (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C) (singleUnit Z)
        (fun W => Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf W) E K =
      canonicalTensorDualMap Z E K := by
  refine (Transpose.dualTensorMap_eq_of_transpose (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
    (internalHomTensorUncurried Z) (tensorHomEquiv Z)
    (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C) (singleUnit Z)
    (fun W => Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf W) E K
    (canonicalTensorDualMap Z E K)
    (Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf K
      (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj (singleUnit Z)) E ≫
      (internalHomTensorUncurried Z).map (𝟙 K ×ₘ
        Stacks.SheafOfModules.derivedSheafHomCounit Z.sheaf E (singleUnit Z)) ≫
        Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf K) ?_ (𝟙 _) ?_).trans
    (Category.id_comp _)
  · intro A c
    have p1 : c ≫ canonicalTensorDualMap Z E K =
        CategoryStruct.comp (Y := ((Stacks.SheafOfModules.derivedTensor Z.sheaf).obj K).obj
          (Stacks.SheafOfModules.derivedDual Z.sheaf E)) c
          (Stacks.SheafOfModules.derivedTensorDualToSheafHom Z.sheaf E K) := rfl
    have e1a : tensorHomEquiv Z A E K =
        (Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf A E K).toEquiv := rfl
    have f1 : ⇑(tensorHomEquiv Z A E K) =
        ⇑(Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf A E K) :=
      (congrArg DFunLike.coe e1a).trans
        (AddEquiv.coe_toEquiv (Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf A E K))
    have e2 :=
      Stacks.SheafOfModules.derivedSheafHomTensorEquiv_toEquiv_comp_derivedTensorDualToSheafHom
        Z.sheaf E K A c
    have p4 : (internalHomTensorUncurried Z).map (c ×ₘ 𝟙 E) =
        (Functor.uncurry.obj (Stacks.SheafOfModules.derivedTensor Z.sheaf)).map
          (Prod.mkHom (X₂ := ((Stacks.SheafOfModules.derivedTensor Z.sheaf).obj K).obj
          (Stacks.SheafOfModules.derivedDual Z.sheaf E)) c (𝟙 E)) := rfl
    have p5 : Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf K
          (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj (singleUnit Z)) E =
        Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf K
          (Stacks.SheafOfModules.derivedDual Z.sheaf E) E := rfl
    have p6 : (internalHomTensorUncurried Z).map
          (𝟙 K ×ₘ Stacks.SheafOfModules.derivedSheafHomCounit Z.sheaf E (singleUnit Z)) ≫
            Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf K =
        (Functor.uncurry.obj (Stacks.SheafOfModules.derivedTensor Z.sheaf)).map
          (𝟙 K ×ₘ Stacks.SheafOfModules.derivedSheafHomCounit Z.sheaf E
            (AlgebraicGeometry.RingedSite.derivedStructureSheaf
              (Stacks.SheafOfModules.ringedSite Z.sheaf))) ≫
            Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf K := rfl
    have q3 := (congrFun (AddEquiv.coe_toEquiv
      (Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf A E K))
        (CategoryStruct.comp (Y := ((Stacks.SheafOfModules.derivedTensor Z.sheaf).obj K).obj
          (Stacks.SheafOfModules.derivedDual Z.sheaf E)) c
          (Stacks.SheafOfModules.derivedTensorDualToSheafHom Z.sheaf E K))).symm
    exact (congrArg (tensorHomEquiv Z A E K) p1).trans ((congrFun f1 _).trans
      (q3.trans (e2.trans
        (congrArg₂ (· ≫ ·) p4.symm (congrArg₂ (· ≫ ·) p5.symm p6.symm)))))
  exact contraction_derivedSheafHomCounit_eq_evaluation Z E K

/-- **The transpose of the contraction against the evaluation is the canonical map of Tag 08I1**,
followed by `R𝓗om(E, -)` of the comparison of the two right unit constraints. -/
theorem dualTensorMap_eq_canonicalTensorDualMap
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    Transpose.dualTensorMap (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
        (internalHomTensorUncurried Z) (tensorHomEquiv Z)
        (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C) (singleUnit Z)
        (fun W => (rightUnitorAtUnit Z W).hom) E K =
      canonicalTensorDualMap Z E K ≫
        ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).map
          (Stacks.SheafOfModules.derivedRightUnitorInv Z.sheaf K ≫
            (rightUnitorAtUnit Z K).hom) := by
  refine (Transpose.dualTensorMap_eq_dualTensorMap_comp
    (Stacks.SheafOfModules.derivedSheafHom Z.sheaf) (internalHomTensorUncurried Z)
    (tensorHomEquiv Z)
    (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C) (singleUnit Z)
    (fun W => (rightUnitorAtUnit Z W).hom) ?_
    (fun W => Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf W) E K
    (Stacks.SheafOfModules.derivedRightUnitorInv Z.sheaf K)
    (Stacks.SheafOfModules.derivedRightUnitorHom_inv Z.sheaf K)).trans ?_
  · intro A B C C' f g
    convert tensorHomEquiv_naturality_target Z A B C C' f g using 1
  congr 1
  exact dualTensorMap_derivedRightUnitorHom_eq_canonicalTensorDualMap Z E K

/-- **Stacks 08DQ for the map `K ⊗^L R𝓗om(E, 𝒪_Z) ⟶ R𝓗om(E, K)`**: for `E` perfect it is an
isomorphism. -/
theorem isIso_dualTensorMap_of_isPerfect
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z) E) :
    IsIso (Transpose.dualTensorMap (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
        (internalHomTensorUncurried Z) (tensorHomEquiv Z)
        (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C) (singleUnit Z)
        (fun W => (rightUnitorAtUnit Z W).hom) E K) := by
  rw [dualTensorMap_eq_canonicalTensorDualMap]
  have h1 : IsIso (canonicalTensorDualMap Z E K) :=
    Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfectSpace Z E K hE
  have h2 : IsIso (Stacks.SheafOfModules.derivedRightUnitorInv Z.sheaf K ≫
      (rightUnitorAtUnit Z K).hom) :=
    IsIso.comp_isIso' ⟨⟨Stacks.SheafOfModules.derivedRightUnitorHom Z.sheaf K,
      Stacks.SheafOfModules.derivedRightUnitorInv_hom Z.sheaf K,
      Stacks.SheafOfModules.derivedRightUnitorHom_inv Z.sheaf K⟩⟩ (Iso.isIso_hom _)
  exact IsIso.comp_isIso' h1 (Functor.map_isIso _ _)

end Pinned


attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedPullbackTensor in
attribute [local instance] abelianModulesSheafTensor

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Sheaf TopCat.Presheaf.IsSheaf

attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable (Z : AlgebraicGeometry.RingedSpace.{u, u})

/-- **The map `K ⊗^L R𝓗om(E, 𝒪_Z) ⟶ R𝓗om(E, K)`** on a ringed space: the transpose of the
associativity constraint of Tag 0FPT, the evaluation and the right unit constraint. -/
abbrev tensorDualToSheafHom
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (internalHomTensorUncurried Z).obj
        (K, ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj (singleUnit Z)) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj K :=
  Transpose.dualTensorMap (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
    (internalHomTensorUncurried Z) (tensorHomEquiv Z)
    (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C) (singleUnit Z)
    (fun W => (rightUnitorAtUnit Z W).hom) E K

/-- Naturality of a family of morphisms of a bifunctor in its second variable, from the curried
form to the uncurried one. -/
private theorem uncurry_nat_second {C : Type*} [Category C] (F : C ⥤ C ⥤ C)
    (a : ∀ A B D : C, (F.obj ((F.obj A).obj B)).obj D ⟶ (F.obj A).obj ((F.obj B).obj D))
    (h : ∀ (A : C) {B B' : C} (g : B ⟶ B') (D : C),
      (F.map ((F.obj A).map g)).app D ≫ a A B' D = a A B D ≫ (F.obj A).map ((F.map g).app D))
    (A : C) {B B' : C} (g : B ⟶ B') (D : C) :
    (Functor.uncurry.obj F).map ((Functor.uncurry.obj F).map (𝟙 A ×ₘ g) ×ₘ 𝟙 D) ≫ a A B' D =
      a A B D ≫ (Functor.uncurry.obj F).map (𝟙 A ×ₘ (Functor.uncurry.obj F).map (g ×ₘ 𝟙 D)) := by
  simpa [Functor.uncurry] using h A g D

/-- Naturality of a family of morphisms of a bifunctor in its first variable, from the curried
form to the uncurried one. -/
private theorem uncurry_nat_first {C : Type*} [Category C] (F : C ⥤ C ⥤ C)
    (a : ∀ A B D : C, (F.obj ((F.obj A).obj B)).obj D ⟶ (F.obj A).obj ((F.obj B).obj D))
    (h : ∀ {A A' : C} (f : A ⟶ A') (B D : C),
      (F.map ((F.map f).app B)).app D ≫ a A' B D = a A B D ≫ (F.map f).app ((F.obj B).obj D))
    {A A' : C} (f : A ⟶ A') (B D : C) :
    (Functor.uncurry.obj F).map ((Functor.uncurry.obj F).map (f ×ₘ 𝟙 B) ×ₘ 𝟙 D) ≫ a A' B D =
      a A B D ≫ (Functor.uncurry.obj F).map (f ×ₘ 𝟙 ((Functor.uncurry.obj F).obj (B, D))) := by
  simpa [Functor.uncurry] using h f B D

/-- The associativity constraint of Tag 0FPT is natural in its second variable, uncurried. -/
theorem derivedAssociatorHom_naturality_second_uncurried
    (A : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    {B B' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (g : B ⟶ B')
    (C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (internalHomTensorUncurried Z).map ((internalHomTensorUncurried Z).map (𝟙 A ×ₘ g) ×ₘ 𝟙 C) ≫
        Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B' C =
      Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C ≫
        (internalHomTensorUncurried Z).map (𝟙 A ×ₘ (internalHomTensorUncurried Z).map (g ×ₘ 𝟙 C)) :=
  uncurry_nat_second _ _ (fun A _ _ g C =>
    Stacks.SheafOfModules.derivedAssociatorHom_naturality_second Z.sheaf A g C) A g C

/-- The associativity constraint of Tag 0FPT is natural in its first variable, uncurried. -/
theorem derivedAssociatorHom_naturality_first_uncurried
    {A A' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (f : A ⟶ A')
    (B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (internalHomTensorUncurried Z).map ((internalHomTensorUncurried Z).map (f ×ₘ 𝟙 B) ×ₘ 𝟙 C) ≫
        Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A' B C =
      Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C ≫
        (internalHomTensorUncurried Z).map
          (f ×ₘ 𝟙 ((internalHomTensorUncurried Z).obj (B, C))) :=
  uncurry_nat_first _ _ (fun f B C =>
    Stacks.SheafOfModules.derivedAssociatorHom_naturality_first Z.sheaf f B C) f B C


/-- **The map `K ⊗^L R𝓗om(E, 𝒪_Z) ⟶ R𝓗om(E, K)` is natural in `K`.** -/
theorem tensorDualToSheafHom_naturality
    (E : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    {K K' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (f : K ⟶ K') :
    tensorDualToSheafHom Z E K ≫
        ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).map f =
      (internalHomTensorUncurried Z).map (f ×ₘ 𝟙 _) ≫ tensorDualToSheafHom Z E K' := by
  refine Transpose.dualTensorMap_naturality (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
    (internalHomTensorUncurried Z) (tensorHomEquiv Z)
    (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C) (singleUnit Z)
    (fun W => (rightUnitorAtUnit Z W).hom) (tensorHomEquiv_naturalLeft Z) ?_
    (fun f B C => derivedAssociatorHom_naturality_first_uncurried Z f B C)
    (fun f => rightUnitorAtUnit_naturality Z _ _ f) E f
  intro A B C C' f g
  convert tensorHomEquiv_naturality_target Z A B C C' f g using 1

/-- **Stacks 08DQ for `K ⊗^L R𝓗om(E, 𝒪_Z) ⟶ R𝓗om(E, K)`**: for `E` perfect it is an
isomorphism. -/
theorem isIso_tensorDualToSheafHom
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z) E) :
    IsIso (tensorDualToSheafHom Z E K) :=
  isIso_dualTensorMap_of_isPerfect Z E K hE

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (h : X ⟶ Y)

/-- **The canonical map `Lh^*R𝓗om(E, 𝒪_Y) ⟶ R𝓗om(Lh^*E, 𝒪_X)`**: the canonical map of Tag 08I3
followed by the unit comparison `Lh^*𝒪_Y ≅ 𝒪_X`. -/
abbrev derivedPullbackDualMap
    (E : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (derivedPullbackFunctor h).obj
        (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj (singleUnit Y)) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op ((derivedPullbackFunctor h).obj E))).obj (singleUnit X) :=
  Transpose.dualComparison (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Y)
    (internalHomTensorUncurried X) (tensorHomEquiv Y) (tensorHomEquiv X) (pullbackTensorIso h)
    (singleUnit Y) (singleUnit X) (derivedPullbackUnitIso h).hom E

/-- The unit coherence of the comparison of Tag 079U at the derived tensor product of the
internal hom, against `rightUnitorAtUnit` on both sides. -/
theorem pullbackTensorIso_rightUnitorAtUnit
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (pullbackTensorIso h).hom.app (W, singleUnit Y) ≫
        (internalHomTensorUncurried X).map
          (𝟙 ((derivedPullbackFunctor h).obj W) ×ₘ (derivedPullbackUnitIso h).hom) ≫
          (rightUnitorAtUnit X ((derivedPullbackFunctor h).obj W)).hom =
      (derivedPullbackFunctor h).map (rightUnitorAtUnit Y W).hom := by
  have hb := (tensorBridge X).inv.naturality
    (𝟙 ((derivedPullbackFunctor h).obj W) ×ₘ (derivedPullbackUnitIso h).hom)
  have hu : (rightUnitorAtPullbackUnit h ((derivedPullbackFunctor h).obj W)).hom =
      (internalHomTensorUncurried X).map
          (𝟙 ((derivedPullbackFunctor h).obj W) ×ₘ (derivedPullbackUnitIso h).hom) ≫
        (rightUnitorAtUnit X ((derivedPullbackFunctor h).obj W)).hom :=
    ((reassoc_of% hb) ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).hom.app
      ((derivedPullbackFunctor h).obj W))).symm
  rw [← hu]
  exact pullbackTensorIso_rightUnitor_coherence h W

/-- **The derived pullback of `K ⊗^L R𝓗om(E, 𝒪) ⟶ R𝓗om(E, K)`, followed by the canonical map of
Tag 08I3, is the comparison of Tag 079U followed by the map of the same kind on `X`.** -/
theorem map_tensorDualToSheafHom_comp_derivedPullbackSheafHomMap
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (derivedPullbackFunctor h).map (tensorDualToSheafHom Y E K) ≫
        derivedPullbackSheafHomMap h E K =
      (pullbackTensorIso h).hom.app
          (K, ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj (singleUnit Y)) ≫
        (internalHomTensorUncurried X).map
          (𝟙 ((derivedPullbackFunctor h).obj K) ×ₘ derivedPullbackDualMap h E) ≫
          tensorDualToSheafHom X ((derivedPullbackFunctor h).obj E)
            ((derivedPullbackFunctor h).obj K) := by
  refine Transpose.map_dualTensorMap_comp_homComparison (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf) (Stacks.SheafOfModules.derivedSheafHom X.sheaf)
    (internalHomTensorUncurried Y) (internalHomTensorUncurried X) (tensorHomEquiv Y)
    (tensorHomEquiv X) (pullbackTensorIso h)
    (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Y.sheaf A B C)
    (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom X.sheaf A B C)
    (singleUnit Y) (singleUnit X) (fun W => (rightUnitorAtUnit Y W).hom)
    (fun W => (rightUnitorAtUnit X W).hom) (derivedPullbackUnitIso h).hom
    (tensorHomEquiv_naturalLeft Y) (tensorHomEquiv_naturalLeft X)
    ?_
    (fun A {_ _} g C => derivedAssociatorHom_naturality_second_uncurried X A g C)
    (pullbackTensorIso_associator h) (pullbackTensorIso_rightUnitorAtUnit h) E K
  intro A B C C' f g
  convert tensorHomEquiv_naturality_target X A B C C' f g using 1


/-- A morphism in the first factor of a bifunctor commutes with one in the second. -/
private theorem bifunctor_interchange {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C × D ⥤ E) {A A' : C} {B B' : D} (f : A ⟶ A') (g : B ⟶ B') :
    F.map (𝟙 A ×ₘ g) ≫ F.map (f ×ₘ 𝟙 B') = F.map (f ×ₘ 𝟙 B) ≫ F.map (𝟙 A' ×ₘ g) := by
  rw [← F.map_comp, ← F.map_comp, prod_comp, prod_comp]
  simp

/-- The chase behind the base-change comparison on `K ⊗^L R𝓗om(E, 𝒪)`. -/
private theorem baseChange_chase {C : Type*} [Category C] {S A B B' M M₁ M' M₁' : C}
    (p : S ⟶ A) (cmp : A ⟶ B) (hφ : B ⟶ B') (m : S ⟶ M) (t₁ : M ⟶ M₁) (μ : M₁ ⟶ B)
    (s : M ⟶ M') (t₁' : M' ⟶ M₁') (μ' : M₁' ⟶ B') (s₁ : M₁ ⟶ M₁')
    (h1 : p ≫ cmp = m ≫ t₁ ≫ μ) (h2 : μ ≫ hφ = s₁ ≫ μ') (h3 : t₁ ≫ s₁ = s ≫ t₁') :
    p ≫ cmp ≫ hφ = (m ≫ s) ≫ t₁' ≫ μ' := by
  rw [← Category.assoc, h1]
  simp only [Category.assoc]
  rw [h2, reassoc_of% h3]

/-- **For `E` perfect, the canonical map `Lh^*R𝓗om(E, 𝒪_Y) ⟶ R𝓗om(Lh^*E, 𝒪_X)` is an
isomorphism**: the map of Tag 08I3 is one by Tag 0GM7 (1), and so is the unit comparison. -/
theorem isIso_derivedPullbackDualMap
    (E : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hE : AlgebraicGeometry.RingedSpace.IsPerfect (X := Y) E) :
    IsIso (derivedPullbackDualMap h E) :=
  IsIso.comp_isIso' (isIso_derivedPullbackSheafHomMap_of_isPerfect h E hE (singleUnit Y))
    (Iso.isIso_hom (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
      (op ((derivedPullbackFunctor h).obj E))).mapIso (derivedPullbackUnitIso h)))

/-- **The base-change comparison of a derived internal hom on `K ⊗^L R𝓗om(E, 𝒪)`.**  The derived
pullback of `K ⊗^L R𝓗om(E, 𝒪_Y) ⟶ R𝓗om(E, K)`, followed by the base-change comparison
`Lh^*R𝓗om(E, K) ⟶ R𝓗om(Lh^*E, K')` of `φ : Lh^*K ⟶ K'`, is the base-change comparison of the
derived tensor product followed by the dual comparison and the map
`K' ⊗^L R𝓗om(Lh^*E, 𝒪_X) ⟶ R𝓗om(Lh^*E, K')`. -/
theorem map_tensorDualToSheafHom_comp_baseChangeSheafHomComparison
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (K' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (φ : (derivedPullbackFunctor h).obj K ⟶ K') :
    (derivedPullbackFunctor h).map (tensorDualToSheafHom Y E K) ≫
        Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison h E K K' φ =
      ((pullbackTensorIso h).hom.app
          (K, ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj (singleUnit Y)) ≫
        (internalHomTensorUncurried X).map (φ ×ₘ 𝟙 _)) ≫
        (internalHomTensorUncurried X).map (𝟙 K' ×ₘ derivedPullbackDualMap h E) ≫
          tensorDualToSheafHom X ((derivedPullbackFunctor h).obj E) K' :=
  baseChange_chase _ _ _ _ _ _ _ _ _ _
    (map_tensorDualToSheafHom_comp_derivedPullbackSheafHomMap h E K)
    (tensorDualToSheafHom_naturality X ((derivedPullbackFunctor h).obj E) φ)
    (bifunctor_interchange (internalHomTensorUncurried X) φ (derivedPullbackDualMap h E))

end Stacks.Cohomology.DerivedInternalHomPullback

end
