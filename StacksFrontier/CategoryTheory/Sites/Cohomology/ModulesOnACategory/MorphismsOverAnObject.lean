module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalMorphismOfSites
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms over an object between derived modules on a category

Let `C` be a category viewed as a site with the chaotic topology, let `O : Cᵒᵖ ⥤ RingCat` be a
sheaf of rings on `C` and let `U` be an object of `C`. Restriction of modules along the forgetful
functor `C/U ⥤ C` is exact, so it descends to a functor `D(O) ⥤ D(O_U)` on derived categories,
where `O_U` denotes the restriction of `O` to the slice category. Taking derived sections over an
object `A` of `C/U` after this restriction is taking derived sections over the source of `A`; in
particular, since `id_U` is a terminal object of `C/U`, derived sections over `id_U` of a
restricted module are the derived sections over `U` of the original module.

The main result is that restriction to `C/U` is fully faithful on objects with cartesian derived
sections: if `K` has cartesian derived sections and `M` is arbitrary, then the morphisms
`K|_U ⟶ M|_U` in `D(O_U)` are exactly the morphisms `RΓ(U, K) ⟶ RΓ(U, M)` in `D(O(U))`.

## Main definitions

* `Stacks.ModulesOnACategory.MorphismsOverAnObject.derivedRestriction`: the restriction
  `D(O) ⥤ D(O_U)` of derived modules to the slice category over `U`.
* `Stacks.ModulesOnACategory.MorphismsOverAnObject.derivedSectionsCompIso`: derived sections over
  an object `A` of `C/U` after restriction are the derived sections over the source of `A`.
* `Stacks.ModulesOnACategory.MorphismsOverAnObject.derivedSectionsIso`: the case `A = id_U` of the
  previous isomorphism, with its target spelled as derived sections over `U`.

## Main results

* `Stacks.ModulesOnACategory.MorphismsOverAnObject.isQC_derivedRestriction`: the restriction to
  `C/U` of an object with cartesian derived sections again has cartesian derived sections.
* `Stacks.ModulesOnACategory.MorphismsOverAnObject.isQC_of_forall_isQC_derivedRestriction`: an
  object whose restriction to every slice `C/U` has cartesian derived sections has cartesian
  derived sections.
* `Stacks.ModulesOnACategory.MorphismsOverAnObject.homDerivedRestriction_bijective`: morphisms out
  of the restriction of an object with cartesian derived sections are the morphisms between the
  derived sections over `U`.

## Implementation notes

The cartesian condition in `isQC_derivedRestriction` is taken relative to an arbitrary derived
base-change datum, one for `O` and one for `O_U`; this is more general than the canonical datum,
which only exists under a commutativity hypothesis on the section rings.

## References

* [Stacks Project, Tag 0H0S](https://stacks.math.columbia.edu/tag/0H0S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.DerivedCategoryComparisons (mapDerivedCategoryCompIso
  mapDerivedCategoryCompIso_inv_app_Q)
open Stacks.Sites.OverModules (overRingPresheaf)
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)

universe w u v r

namespace Stacks.ModulesOnACategory.MorphismsOverAnObject

attribute [local instance] HasDerivedCategory.standard

section MapHomologicalComplex

variable {D₁ : Type*} [Category D₁] [Preadditive D₁] {D₂ : Type*} [Category D₂] [Preadditive D₂]
  {D₃ : Type*} [Category D₃] [Preadditive D₃]

/-- The functor induced on homological complexes by a composite is the composite of the induced
functors. -/
private theorem mapHomologicalComplex_comp (F : D₁ ⥤ D₂) (G : D₂ ⥤ D₃)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) =
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        G.mapHomologicalComplex (ComplexShape.up ℤ) :=
  rfl

end MapHomologicalComplex

section Slice

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r}) (U : C)

/-- Restriction of presheaves of modules along `Over.forget U` is a left adjoint, stated at the
module universe that the derived categories of modules on `C` and on `C/U` share. -/
theorem restrictionIsLeftAdjoint :
    (PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) O).IsLeftAdjoint :=
  Stacks.Sites.OverModules.restriction_isLeftAdjoint.{v, u, r, max r w} O U

/-- Restriction of presheaves of modules along `Over.forget U` is a right adjoint, stated at the
module universe that the derived categories of modules on `C` and on `C/U` share. -/
theorem restrictionIsRightAdjoint :
    (PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) O).IsRightAdjoint :=
  Stacks.Sites.OverModules.restriction_isRightAdjoint.{v, u, r, max r w} O U

attribute [local instance] restrictionIsLeftAdjoint restrictionIsRightAdjoint

/-- Derived restriction of modules to the slice category over `U`: the descent to derived
categories of the exact restriction of presheaves of modules along `Over.forget U`. -/
def derivedRestriction : DMod.{w} O ⥤ DMod.{w} (overRingPresheaf O U) :=
  (PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) O).mapDerivedCategory

/-- Derived sections over an object `A` of `C/U` of the restriction of a derived module are the
derived sections over the source of `A` of the original derived module. -/
def derivedSectionsCompIso (A : Over U) :
    derivedRestriction.{w} O U ⋙
        RGamma.{w} (overRingPresheaf O U) (Opposite.op A) ≅
      RGamma.{w} O (Opposite.op A.left) :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) O)
      (PresheafOfModules.evaluation.{max u v r w} (overRingPresheaf O U)
        (Opposite.op A))).symm

/-- The identity of `U` is a terminal object of `C/U`, and derived sections there of a restricted
derived module are the derived sections over `U` of the original derived module. -/
def derivedSectionsIso :
    derivedRestriction.{w} O U ⋙
        RGamma.{w} (overRingPresheaf O U) (Opposite.op (Over.mk (𝟙 U))) ≅
      RGamma.{w} O (Opposite.op U) :=
  derivedSectionsCompIso.{w} O U (Over.mk (𝟙 U))

/-- The comparison isomorphism of derived sections, evaluated at the image of a cochain
complex. -/
private theorem derivedSectionsCompIso_hom_app_Q (A : Over U)
    (P : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    (derivedSectionsCompIso.{w} O U A).hom.app (DerivedCategory.Q.obj P) =
      (RGamma.{w} (overRingPresheaf O U) (Opposite.op A)).map
          ((PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U)
            O).mapDerivedCategoryFactors.hom.app P) ≫
        (PresheafOfModules.evaluation.{max u v r w} (overRingPresheaf O U)
            (Opposite.op A)).mapDerivedCategoryFactors.hom.app
          (((PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U)
            O).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) O ⋙
          PresheafOfModules.evaluation.{max u v r w} (overRingPresheaf O U)
            (Opposite.op A)).mapDerivedCategoryFactors.inv.app P :=
  mapDerivedCategoryCompIso_inv_app_Q
    (PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) O)
    (PresheafOfModules.evaluation.{max u v r w} (overRingPresheaf O U) (Opposite.op A)) P

/-- The canonical derived restriction map on `C` along a morphism of `C/U`, evaluated at the image
of a cochain complex, with the derived sections written as sections of the restriction to
`C/U`. -/
private theorem restrictionMap_pushforward_Q_obj {A B : Over U}
    (f : Opposite.op B ⟶ Opposite.op A)
    (P : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    restrictionMap.{w} O ((Over.forget U).op.map f) (DerivedCategory.Q.obj P) =
      (PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) O ⋙
          PresheafOfModules.evaluation.{max u v r w} (overRingPresheaf O U)
            (Opposite.op B)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (PresheafOfModules.restriction O ((Over.forget U).op.map f))
              (ComplexShape.up ℤ)).app P) ≫
        ((ModuleCat.restrictScalars.{max u v r w}
              (O.map ((Over.forget U).op.map f)).hom).mapDerivedCategoryFactors.inv.app
            (((PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) O ⋙
              PresheafOfModules.evaluation.{max u v r w} (overRingPresheaf O U)
                (Opposite.op A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (DRestrict.{w} O ((Over.forget U).op.map f)).map
            ((PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) O ⋙
              PresheafOfModules.evaluation.{max u v r w} (overRingPresheaf O U)
                (Opposite.op A)).mapDerivedCategoryFactors.inv.app P)) :=
  restrictionMap_Q.{w} O ((Over.forget U).op.map f) P

/-- The canonical derived restriction maps are compatible with the comparison isomorphism of
derived sections, as natural transformations. -/
private theorem whiskerLeft_restrictionNatTrans {A B : Over U}
    (f : Opposite.op B ⟶ Opposite.op A) :
    Functor.whiskerLeft (derivedRestriction.{w} O U)
        (restrictionNatTrans.{w} (overRingPresheaf O U) f) ≫
      Functor.whiskerRight (derivedSectionsCompIso.{w} O U A).hom
        (DRestrict.{w} O ((Over.forget U).op.map f)) =
    (derivedSectionsCompIso.{w} O U B).hom ≫
      restrictionNatTrans.{w} O ((Over.forget U).op.map f) := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (PresheafOfModules.{max u v r w} O) (ComplexShape.up ℤ))
    fun P ↦ ?_
  have hn := (restrictionNatTrans.{w} (overRingPresheaf O U) f).naturality
    ((PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U)
      O).mapDerivedCategoryFactors.hom.app P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map] at hn ⊢
  rw [restrictionNatTrans_app, restrictionNatTrans_app] at hn
  simp only [Functor.comp_obj] at hn
  rw [restrictionMap_Q] at hn
  rw [restrictionNatTrans_app, restrictionNatTrans_app,
    derivedSectionsCompIso_hom_app_Q, derivedSectionsCompIso_hom_app_Q]
  exact comp_map_eq_comp_of_naturality hn (restrictionMap_pushforward_Q_obj.{w} O U f P)
    (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)

/-- The canonical derived restriction maps are compatible with the comparison isomorphism of
derived sections, on a single derived module. -/
private theorem restrictionMap_derivedRestriction {A B : Over U}
    (f : Opposite.op B ⟶ Opposite.op A) (K : DMod.{w} O) :
    restrictionMap.{w} (overRingPresheaf O U) f ((derivedRestriction.{w} O U).obj K) ≫
        (DRestrict.{w} O ((Over.forget U).op.map f)).map
          ((derivedSectionsCompIso.{w} O U A).hom.app K) =
      (derivedSectionsCompIso.{w} O U B).hom.app K ≫
        restrictionMap.{w} O ((Over.forget U).op.map f) K :=
  congr_app (whiskerLeft_restrictionNatTrans.{w} O U f) K

/-- **The cartesian comparison of a restricted module is the comparison of the module.** For a
morphism `f` of `C/U`, the comparison map of `K|_U` along `f` is the comparison map of `K` along
the underlying morphism of `C`, conjugated by the identifications of derived sections over the
two ends and the canonical isomorphism of the two derived base changes. -/
theorem comparison_derivedRestriction (bc : BaseChangeData.{w} O)
    (bc' : BaseChangeData.{w} (overRingPresheaf O U)) (K : DMod.{w} O)
    {A B : (Over U)ᵒᵖ} (f : B ⟶ A) :
    (bc'.baseChange f).map ((derivedSectionsCompIso.{w} O U B.unop).hom.app K) ≫
        (Adjunction.leftAdjointUniq (bc.baseChangeAdj ((Over.forget U).op.map f))
          (bc'.baseChangeAdj f)).inv.app _ ≫ comparison bc ((Over.forget U).op.map f) K ≫
        (derivedSectionsCompIso.{w} O U A.unop).inv.app K =
      comparison bc' f ((derivedRestriction.{w} O U).obj K) := by
  let adj₁ : bc'.baseChange f ⊣ DRestrict.{w} O ((Over.forget U).op.map f) :=
    bc'.baseChangeAdj f
  let α := Adjunction.leftAdjointUniq (bc.baseChangeAdj ((Over.forget U).op.map f)) adj₁
  have hα : ∀ X, adj₁.unit.app X ≫
      (DRestrict.{w} O ((Over.forget U).op.map f)).map (α.inv.app X) =
      (bc.baseChangeAdj ((Over.forget U).op.map f)).unit.app X := fun X ↦ by
    rw [Adjunction.leftAdjointUniq_inv_app]
    exact Adjunction.unit_leftAdjointUniq_hom_app adj₁
      (bc.baseChangeAdj ((Over.forget U).op.map f)) X
  apply (adj₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  calc (derivedSectionsCompIso.{w} O U B.unop).hom.app K ≫ adj₁.homEquiv _ _
        (α.inv.app _ ≫ comparison bc ((Over.forget U).op.map f) K ≫
          (derivedSectionsCompIso.{w} O U A.unop).inv.app K) =
      (derivedSectionsCompIso.{w} O U B.unop).hom.app K ≫
        ((adj₁.unit.app _ ≫
          (DRestrict.{w} O ((Over.forget U).op.map f)).map (α.inv.app _)) ≫
          (DRestrict.{w} O ((Over.forget U).op.map f)).map
            (comparison bc ((Over.forget U).op.map f) K) ≫
          (DRestrict.{w} O ((Over.forget U).op.map f)).map
            ((derivedSectionsCompIso.{w} O U A.unop).inv.app K)) := by
        simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    _ = (derivedSectionsCompIso.{w} O U B.unop).hom.app K ≫
        ((bc.baseChangeAdj ((Over.forget U).op.map f)).unit.app _ ≫
          (DRestrict.{w} O ((Over.forget U).op.map f)).map
            (comparison bc ((Over.forget U).op.map f) K) ≫
          (DRestrict.{w} O ((Over.forget U).op.map f)).map
            ((derivedSectionsCompIso.{w} O U A.unop).inv.app K)) := by
        rw [hα]
    _ = (derivedSectionsCompIso.{w} O U B.unop).hom.app K ≫
        (restrictionMap.{w} O ((Over.forget U).op.map f) K ≫
          (DRestrict.{w} O ((Over.forget U).op.map f)).map
            ((derivedSectionsCompIso.{w} O U A.unop).inv.app K)) := by
        have ht : (bc.baseChangeAdj ((Over.forget U).op.map f)).homEquiv _ _
            (comparison bc ((Over.forget U).op.map f) K) =
            restrictionMap.{w} O ((Over.forget U).op.map f) K :=
          Equiv.apply_symm_apply _ _
        have ht' := congrArg (fun g => (derivedSectionsCompIso.{w} O U B.unop).hom.app K ≫
          g ≫ (DRestrict.{w} O ((Over.forget U).op.map f)).map
            ((derivedSectionsCompIso.{w} O U A.unop).inv.app K)) ht
        simp only [Adjunction.homEquiv_unit, Category.assoc] at ht'
        exact ht'
    _ = restrictionMap.{w} (overRingPresheaf O U) f
          ((derivedRestriction.{w} O U).obj K) :=
        (Category.assoc _ _ _).symm.trans
          ((Iso.comp_inv_eq ((DRestrict.{w} O ((Over.forget U).op.map f)).mapIso
            ((derivedSectionsCompIso.{w} O U A.unop).app K))).mpr
            (restrictionMap_derivedRestriction.{w} O U f K).symm)
    _ = adj₁.homEquiv _ _
          (comparison bc' f ((derivedRestriction.{w} O U).obj K)) :=
        (Equiv.apply_symm_apply _ _).symm

/-- The restriction to `C/U` of a derived module with cartesian derived sections again has
cartesian derived sections. -/
theorem isQC_derivedRestriction (bc : BaseChangeData.{w} O)
    (bc' : BaseChangeData.{w} (overRingPresheaf O U)) (K : DMod.{w} O)
    (hK : IsQC.{w} bc K) :
    IsQC.{w} bc' ((derivedRestriction.{w} O U).obj K) := by
  intro A B f
  rw [← comparison_derivedRestriction.{w} O U bc bc' K f]
  have := hK ((Over.forget U).op.map f)
  infer_instance

/-- **Cartesian derived sections are local over the objects of `C`.** A derived module whose
restriction to every slice `C/U` has cartesian derived sections has cartesian derived sections:
the comparison map of `K` along an arrow `V ⟶ U` of `Cᵒᵖ` is, up to isomorphisms, the comparison
map of `K|_{U.unop}` along the corresponding arrow of the slice. -/
theorem isQC_of_forall_isQC_derivedRestriction (bc : BaseChangeData.{w} O)
    (bc' : ∀ U : C, BaseChangeData.{w} (overRingPresheaf O U)) (K : DMod.{w} O)
    (hK : ∀ U : C, IsQC.{w} (bc' U) ((derivedRestriction.{w} O U).obj K)) :
    IsQC.{w} bc K := by
  intro U V a
  let f : (Opposite.op (Over.mk (𝟙 V.unop)) : (Over V.unop)ᵒᵖ) ⟶ Opposite.op (Over.mk a.unop) :=
    (Over.homMk a.unop (by simp) : Over.mk a.unop ⟶ Over.mk (𝟙 V.unop)).op
  have h := comparison_derivedRestriction.{w} O V.unop bc (bc' V.unop) K f
  have hi : IsIso (comparison (bc' V.unop) f ((derivedRestriction.{w} O V.unop).obj K)) :=
    hK V.unop f
  rwa [← h, isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff] at hi

end Slice

section Bijective

universe u₁ v₁ u₂ v₂

variable {S : Type u₁} [Category.{v₁} S] {T : Type u₂} [Category.{v₂} T]

/-- If the counit of an adjunction `adj : L ⊣ R` is an isomorphism at `X`, then applying `R` and
conjugating by isomorphisms `α : R.obj X ≅ P` and `β : R.obj Y ≅ Q` is a bijection from the
morphisms `X ⟶ Y` onto the morphisms `P ⟶ Q`. -/
private theorem bijective_rightAdjoint_map_of_isIso_counit
    {L : S ⥤ T} {R : T ⥤ S} (adj : L ⊣ R) {X Y : T}
    (hX : IsIso (adj.counit.app X)) {P Q : S}
    (α : R.obj X ≅ P) (β : R.obj Y ≅ Q) :
    Function.Bijective (fun f : X ⟶ Y => α.inv ≫ R.map f ≫ β.hom) := by
  have hpre : Function.Bijective (fun f : X ⟶ Y => adj.counit.app X ≫ f) := by
    refine ⟨fun a b hab => (cancel_epi (adj.counit.app X)).mp hab,
      fun b => ⟨inv (adj.counit.app X) ≫ b, ?_⟩⟩
    simp
  have hfun : (fun f : X ⟶ Y => α.inv ≫ R.map f ≫ β.hom) =
      (Iso.homCongr α β) ∘ (adj.homEquiv (R.obj X) Y) ∘
        (fun f : X ⟶ Y => adj.counit.app X ≫ f) := by
    funext f
    show α.inv ≫ R.map f ≫ β.hom =
      α.inv ≫ adj.homEquiv (R.obj X) Y (adj.counit.app X ≫ f) ≫ β.hom
    rw [Adjunction.homEquiv_apply, Functor.map_comp]
    simp only [adj.right_triangle_components_assoc]
  rw [hfun]
  exact Function.Bijective.comp (Iso.homCongr α β).bijective
    (Function.Bijective.comp (adj.homEquiv _ _).bijective hpre)

end Bijective

section Main

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r}) (U : C)

attribute [local instance] restrictionIsLeftAdjoint restrictionIsRightAdjoint

/-- The section rings of the restriction of `O` to `C/U` are the section rings of `O`, so they are
commutative as soon as those of `O` are. -/
lemma comm_overRingPresheaf (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x)
    (A : (Over U)ᵒᵖ) (x y : (overRingPresheaf O U).obj A) : x * y = y * x :=
  hO ((Over.forget U).op.obj A) x y

/-- Let `K` be a derived module with cartesian derived sections and let `M` be an arbitrary derived
module. Applying derived sections over the terminal object `id_U` of `C/U` and conjugating by
`derivedSectionsIso` identifies the morphisms `K|_U ⟶ M|_U` in `D(O_U)` with the morphisms
`RΓ(U, K) ⟶ RΓ(U, M)` in `D(O(U))`. -/
@[stacks 0H0S]
theorem homDerivedRestriction_bijective
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x)
    (K M : DMod.{w} O)
    (hK : IsQC.{w} (baseChangeDataOfComm.{r, v, u, w} O hO) K) :
    Function.Bijective (fun f : (derivedRestriction.{w} O U).obj K ⟶
        (derivedRestriction.{w} O U).obj M =>
      ((derivedSectionsIso.{w} O U).app K).inv ≫
        (RGamma.{w} (overRingPresheaf O U)
          (Opposite.op (Over.mk (𝟙 U)))).map f ≫
        ((derivedSectionsIso.{w} O U).app M).hom) :=
  bijective_rightAdjoint_map_of_isIso_counit
    (morphismOfSites (overRingPresheaf O U) (comm_overRingPresheaf O U hO)
      (Over.mkIdTerminal (X := U))).adj
    (main_counit_isIso.{w}
      (baseChangeDataOfComm (overRingPresheaf O U) (comm_overRingPresheaf O U hO))
      (morphismOfSites (overRingPresheaf O U) (comm_overRingPresheaf O U hO)
        (Over.mkIdTerminal (X := U)))
      ((derivedRestriction.{w} O U).obj K)
      (isQC_derivedRestriction.{w} O U (baseChangeDataOfComm.{r, v, u, w} O hO)
        (baseChangeDataOfComm (overRingPresheaf O U) (comm_overRingPresheaf O U hO)) K hK))
    ((derivedSectionsIso.{w} O U).app K) ((derivedSectionsIso.{w} O U).app M)

end Main

end Stacks.ModulesOnACategory.MorphismsOverAnObject

end
