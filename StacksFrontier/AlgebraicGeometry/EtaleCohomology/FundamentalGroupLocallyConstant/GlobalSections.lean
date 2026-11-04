module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Modules
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.GlobalSectionsInvariants

/-!
# Global sections under the dictionary of Stacks 0DV5 (3)

Let `X` be a connected scheme with a geometric point `x`, let `Λ` be a finite ring and let `ℱ`
be a finite type locally constant sheaf of `Λ`-modules on `X_étale`, corresponding under
Tag 0DV5 (3) to the finite `Λ`-module `M` with its continuous action of `π₁(X, x)`. Then the
global sections of `ℱ` are the invariants `M^{π₁(X, x)}`, naturally in `ℱ` and as `Λ`-modules.

## Main definitions

* `Stacks.GroupCohomology.finiteTypeContinuousModuleInvariants` — the invariants `M ↦ M^G` of
  a finite `Λ`-module with a continuous `G`-action, as a functor to `Λ`-modules. The ring `Λ`
  need not be commutative.
* `AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafSections` — global sections of a finite
  type locally constant sheaf of `Λ`-modules on `X_étale`.

## Main results

* `AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafSectionsIsoInvariants` — the natural
  isomorphism of `Λ`-modules `Γ(X, ℱ) ≅ M^{π₁(X, x)}`.

## Implementation notes

The dictionary of part (3) is that of part (2) read on scalar operations, and part (2) is that of
part (1) read on commutative group objects. The abelian group statement is
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianSectionsIsoInvariants`, at the equivalence of
part (1). Its components are `Λ`-linear because multiplication by `a ∈ Λ` is, on both sides, the
image of one endomorphism of the underlying abelian sheaf, and the isomorphism is natural in
endomorphisms.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf Stacks.GroupCohomology

universe u r u' w

namespace Stacks.GroupCohomology

variable (Λ : Type r) [Ring Λ] (G : Type u') [Group G] [TopologicalSpace G]

/-- The invariants of a finite `Λ`-module with a continuous action of `G`, as a submodule. -/
def finiteTypeContinuousModuleInvariantsSubmodule (M : FiniteTypeContinuousModule.{r, u', w} Λ G) :
    Submodule Λ M.obj.obj.obj.V where
  carrier := {x | ∀ g : G, ConcreteCategory.hom (M.obj.obj.obj.ρ g) x = x}
  zero_mem' := fun _ ↦ map_zero _
  add_mem' := fun ha hb g ↦ by rw [map_add, ha g, hb g]
  smul_mem' := fun a _ hx g ↦ by rw [map_smul, hx g]

/-- **The invariants `M^G` of a finite `Λ`-module with a continuous `G`-action**, as a functor
to `Λ`-modules. -/
def finiteTypeContinuousModuleInvariants :
    FiniteTypeContinuousModule.{r, u', w} Λ G ⥤ ModuleCat.{w} Λ where
  obj M := ModuleCat.of Λ (finiteTypeContinuousModuleInvariantsSubmodule Λ G M)
  map f := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨f.hom.hom.hom.hom x.1, fun g ↦
        (ConcreteCategory.congr_hom (f.hom.hom.hom.comm g) x.1).symm.trans
          (congrArg _ ((Submodule.mem_carrier _).2 x.2 g))⟩
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (map_smul _ _ _) }

/-- Membership in the invariants. -/
theorem mem_finiteTypeContinuousModuleInvariantsSubmodule
    {M : FiniteTypeContinuousModule.{r, u', w} Λ G} (x : M.obj.obj.obj.V) :
    x ∈ finiteTypeContinuousModuleInvariantsSubmodule Λ G M ↔
      ∀ g : G, ConcreteCategory.hom (M.obj.obj.obj.ρ g) x = x :=
  Iff.rfl

end Stacks.GroupCohomology

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type r) [Ring Λ] [Finite Λ]

/-- Global sections of a finite type locally constant sheaf of `Λ`-modules on `X_étale`: its
sections over the final object of the small étale site. -/
abbrev finiteTypeLocallyConstantModuleSheafSections :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F) ⥤
      ModuleCat.{u + 1} Λ :=
  ObjectProperty.ι _ ⋙ sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (op (SmallEtale.final B X.1 X.2))

/-- The abelian sheaf underlying a finite type locally constant sheaf of `Λ`-modules, as a finite
locally constant abelian sheaf. -/
abbrev finiteTypeLocallyConstantModuleSheafAbelian
    (F : ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F)) :
    (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory :=
  ((finiteLocallyConstantModuleSheafScalarActionEquivalence (SmallEtale.topology B X.1 X.2)
    Λ).functor.obj ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.obj F)).obj.obj
      (SingleObj.star Λ)

/-- The abelian group isomorphism `Γ(X, ℱ) ≅ M^{π₁(X, x)}` on the underlying abelian sheaf. -/
abbrev finiteTypeLocallyConstantModuleSheafAbelianIso
    (F : ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F)) :=
  (finiteLocallyConstantAbelianSectionsIsoInvariants (SmallEtale.topology B X.1 X.2)
    (SmallEtale.finalIsTerminal B X.1 X.2) (EtaleFundamentalGroup X.1 x)
    (finiteLocallyConstantSetsEquivalence' B X x)).app
      (finiteTypeLocallyConstantModuleSheafAbelian B X Λ F)

/-- The abelian isomorphism `finiteTypeLocallyConstantModuleSheafAbelianIso` is `Λ`-linear. -/
theorem finiteTypeLocallyConstantModuleSheafAbelianIso_hom_smul
    (F : ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F))
    (a : Λ) (y : (finiteTypeContinuousModuleInvariants Λ (EtaleFundamentalGroup X.1 x)).obj
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.obj F)) :
    (finiteTypeLocallyConstantModuleSheafAbelianIso B X x Λ F).hom (a • y) =
      a • (show (finiteTypeLocallyConstantModuleSheafSections B X Λ).obj F from
        (finiteTypeLocallyConstantModuleSheafAbelianIso B X x Λ F).hom y) := by
  have h := ConcreteCategory.congr_hom
    ((finiteLocallyConstantAbelianSectionsIsoInvariants (SmallEtale.topology B X.1 X.2)
      (SmallEtale.finalIsTerminal B X.1 X.2) (EtaleFundamentalGroup X.1 x)
      (finiteLocallyConstantSetsEquivalence' B X x)).hom.naturality
        ((((finiteLocallyConstantModuleSheafScalarActionEquivalence
          (SmallEtale.topology B X.1 X.2) Λ).functor.obj
            ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.obj F)).obj.map
            (show SingleObj.star Λ ⟶ SingleObj.star Λ from a)))) y
  exact h

/-- The `Λ`-linear isomorphism `M^{π₁(X, x)} ≃ Γ(X, ℱ)` at one sheaf. -/
def finiteTypeLocallyConstantModuleSheafSectionsLinearEquiv
    (F : ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F)) :
    (finiteTypeContinuousModuleInvariants Λ (EtaleFundamentalGroup X.1 x)).obj
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.obj F) ≃ₗ[Λ]
      (finiteTypeLocallyConstantModuleSheafSections B X Λ).obj F :=
  { (finiteTypeLocallyConstantModuleSheafAbelianIso B X x Λ F).addCommGroupIsoToAddEquiv with
    map_smul' := finiteTypeLocallyConstantModuleSheafAbelianIso_hom_smul B X x Λ F }

/-- **Global sections of a finite type locally constant sheaf of `Λ`-modules are the invariants
of the corresponding `π₁(X, x)`-module.** For a connected scheme `X` with a geometric point `x`
and a finite ring `Λ`, the global sections `Γ(X, ℱ)` of a finite type locally constant sheaf of
`Λ`-modules `ℱ` on `X_étale` are, as a `Λ`-module and naturally in `ℱ`, the invariants
`M^{π₁(X, x)}` of the finite `Λ`-module `M` with continuous `π₁(X, x)`-action that Tag 0DV5 (3)
attaches to `ℱ`. -/
def finiteTypeLocallyConstantModuleSheafSectionsIsoInvariants :
    (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor ⋙
        finiteTypeContinuousModuleInvariants Λ (EtaleFundamentalGroup X.1 x) ≅
      finiteTypeLocallyConstantModuleSheafSections B X Λ :=
  NatIso.ofComponents
    (fun F ↦ (finiteTypeLocallyConstantModuleSheafSectionsLinearEquiv B X x Λ F).toModuleIso)
    (fun {F F'} f ↦ by
      ext y
      have h := ConcreteCategory.congr_hom
        ((finiteLocallyConstantAbelianSectionsIsoInvariants (SmallEtale.topology B X.1 X.2)
          (SmallEtale.finalIsTerminal B X.1 X.2) (EtaleFundamentalGroup X.1 x)
          (finiteLocallyConstantSetsEquivalence' B X x)).hom.naturality
            (((finiteLocallyConstantModuleSheafScalarActionEquivalence
              (SmallEtale.topology B X.1 X.2) Λ).functor.map
                ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.map f)).hom.app
                  (SingleObj.star Λ))) y
      have hl : ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor ⋙
          finiteTypeContinuousModuleInvariants Λ (EtaleFundamentalGroup X.obj x)).map f y =
          ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence
            (SmallEtale.topology B X.1 X.2) (EtaleFundamentalGroup X.1 x)
            (finiteLocallyConstantSetsEquivalence' B X x)).functor ⋙
              ContinuousGAddCommGrp.finiteInvariants (EtaleFundamentalGroup X.1 x)).map
            (((finiteLocallyConstantModuleSheafScalarActionEquivalence
              (SmallEtale.topology B X.1 X.2) Λ).functor.map
                ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.map f)).hom.app
                  (SingleObj.star Λ)) y := rfl
      change (finiteTypeLocallyConstantModuleSheafAbelianIso B X x Λ F').hom
          (((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor ⋙
            finiteTypeContinuousModuleInvariants Λ (EtaleFundamentalGroup X.obj x)).map f y) =
        (finiteTypeLocallyConstantModuleSheafSections B X Λ).map f
          ((finiteTypeLocallyConstantModuleSheafAbelianIso B X x Λ F).hom y)
      rw [hl]
      exact h)

end AlgebraicGeometry
