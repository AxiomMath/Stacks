module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ProperFinitenessStatement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# The underlying abelian sheaf of a constructible flat sheaf of modules over a finite ring

Let `Λ` be a finite ring. A constructible flat sheaf of `Λ`-modules on the small étale site of a
scheme is, on the strata of a constructible stratification of every affine open, locally constant
with finite projective values; a finite projective `Λ`-module is a finite set, so the underlying
abelian sheaf is constructible (Tag 03RW (2)). Since constructible flatness is stable under
inverse image (`Stacks.EtaleCohomology.IsConstructibleFlatEtaleModule.pullback`), so is this
conclusion.

## Main results

* `Stacks.ConstantSheaf.isFiniteLocallyConstant_forget₂_of_isFiniteProjectiveLocallyConstant`:
  over a finite ring, a sheaf of modules which is locally constant with finite projective values
  has finite locally constant underlying abelian sheaf.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_forget₂_of_isConstructibleFlatModuleSheaf`: the
  same for constructibility on the small étale site of Tag 021B.
* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_forget₂_etaleModuleInverseImage`: the
  underlying abelian sheaf of the inverse image of a constructible flat sheaf of `Λ`-modules
  along a morphism of a big étale site is constructible, on Mathlib's small étale site.

## Implementation notes

The coefficient universe is `max (u + 1) r`, that of `EtaleModules.{u, r}`. Inverse image along
base change of the site of Tag 021B commutes with forgetting the module structure by
`Stacks.EtaleCohomology.isIso_coefficientSheafPullbackTwoSquare`: the forgetful functor preserves
the left Kan extensions defining inverse image, base change being representably flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w r c v u

namespace Stacks.ConstantSheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type r) [Ring Λ]
  [UnivLE.{max c v, w}]

/-- **Over a finite ring, local constancy with finite projective values gives finite local
constancy of the underlying abelian sheaf.** A finite module over a finite ring is a finite set,
and the constant sheaf commutes with forgetting the module structure, which commutes with
sheafification. -/
theorem isFiniteLocallyConstant_forget₂_of_isFiniteProjectiveLocallyConstant [Finite Λ]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} Λ)]
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    (F : Sheaf J (ModuleCat.{w} Λ)) (hF : IsFiniteProjectiveLocallyConstant Λ J F) :
    IsFiniteLocallyConstant J
      ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F) := by
  refine ⟨fun U ↦ ?_⟩
  obtain ⟨I, V, f, hcover, hloc⟩ := hF U
  refine ⟨I, V, f, hcover, fun i ↦ ?_⟩
  obtain ⟨E, hfin, -, ⟨e⟩⟩ := hloc i
  have : (J.over (V i)).HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{w} Λ (J.over (V i))
  have : (J.over (V i)).PreservesSheafification
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
    Stacks.ModuleSheaf.preservesSheafification_forget₂.{w} Λ (J.over (V i))
  have : Finite E := Module.finite_of_finite Λ
  refine ⟨(forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).obj E, (inferInstance : Finite E), ⟨?_⟩⟩
  exact (constantCommuteCompose (J.over (V i))
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).symm.app E ≪≫
    (sheafCompose (J.over (V i)) (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).mapIso e ≪≫
    Iso.refl _

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- **Forgetting the module structure preserves the left Kan extensions defining inverse image
on the small étale sites of Tag 021B**: base change is representably flat, so the indexing
categories are filtered, and the forgetful functor preserves filtered colimits. -/
instance preservesLeftKanExtensions_forget₂_smallEtaleBaseChange_moduleCat {S T : B.Scheme}
    (f : T ⟶ S) :
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).PreservesLeftKanExtensions
      (smallEtaleBaseChange B f).op := by
  intro P
  have hfil : ∀ V : (SmallEtale B T.obj T.property)ᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange B f).op V) := fun V ↦
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange B f) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u, u + 1} _
  infer_instance

/-- **Inverse image along base change on the sites of Tag 021B commutes with forgetting the
module structure.** -/
def forget₂SheafPullbackIso {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) r} Λ)) :
    ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{max (u + 1) r}
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ)
          AddCommGrpCat.{max (u + 1) r})).obj F) ≅
      (sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).obj
        (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F) :=
  haveI := Stacks.ModuleSheaf.hasSheafCompose_forget₂.{max (u + 1) r} Λ
    (SmallEtale.topology B S.obj S.property)
  haveI := Stacks.ModuleSheaf.hasSheafCompose_forget₂.{max (u + 1) r} Λ
    (SmallEtale.topology B T.obj T.property)
  haveI := Stacks.ModuleSheaf.preservesSheafification_forget₂.{max (u + 1) r} Λ
    (SmallEtale.topology B T.obj T.property)
  asIso ((Stacks.EtaleCohomology.coefficientSheafPullbackTwoSquare (smallEtaleBaseChange B f)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).natTrans.app F)

/-- **Over a finite ring, the underlying abelian sheaf of a constructible flat sheaf of modules is
constructible**, on the small étale site of Tag 021B: the stratification which makes the sheaf of
modules locally constant with finite projective values makes the abelian sheaf finite locally
constant. -/
theorem isConstructibleAbelianSheaf_forget₂_of_isConstructibleFlatModuleSheaf [Finite Λ]
    (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    haveI := SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat.{u, r} B
    haveI := SmallEtale.hasWeakSheafify_over_addCommGrpCat.{u, r} B
    IsConstructibleAbelianSheaf B X
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).obj
        F) := by
  have := SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat.{u, r} B
  have := SmallEtale.hasWeakSheafify_over_addCommGrpCat.{u, r} B
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i ↦ ?_⟩
  have h :=
    Stacks.ConstantSheaf.isFiniteLocallyConstant_forget₂_of_isFiniteProjectiveLocallyConstant
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property) Λ _ (hs i)
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
    (forget₂SheafPullbackIso B Λ (s.inclusion i) F).symm (hF := h)

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- **The underlying abelian sheaf of the inverse image of a constructible flat sheaf of modules
over a finite ring is constructible.** For a morphism `f : Y ⟶ X` of a big étale site `B` and a
constructible flat sheaf `G` of `Λ`-modules on Mathlib's small étale site of `X`, the abelian
sheaf underlying `f⁻¹ G` is constructible on Mathlib's small étale site of `Y`, read through `B`
(`Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf`). -/
theorem isConstructibleEtaleAbelianSheaf_forget₂_etaleModuleInverseImage [Finite Λ]
    {X Y : B.Scheme} (f : Y ⟶ X) (G : EtaleModules.{u, r} Λ X.obj)
    (hG : IsConstructibleFlatEtaleModule B X Λ G) :
    IsConstructibleEtaleAbelianSheaf.{u, r} B Y.obj Y.property
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat)).obj
        ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map f)).obj G)) :=
  AlgebraicGeometry.isConstructibleAbelianSheaf_forget₂_of_isConstructibleFlatModuleSheaf B Λ Y
    _ (hG.pullback B Λ f)

end Stacks.EtaleCohomology

end
