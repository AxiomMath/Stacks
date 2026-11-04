module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModulesTerminalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelGlobalFunctions
public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedSiteModulesEquiv
public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedTopos

/-!
# The morphism `X ⟶ (pt, R)` and its inverse image `M ↦ 𝒪_X ⊗_R M`

Let `X` be an algebraic space and `φ : R →+* Γ(X, 𝒪_X)` a ring map, read on the model of the small
étale site (`AlgebraicGeometry.Space.modelGlobalFunctions`); for a morphism `f : X ⟶ Spec(R)` this
is `AlgebraicGeometry.Space.baseRingHomOfMap f`.  Through the identification
`AlgebraicGeometry.Space.spacesEtaleModelGlobalFunctionsEquiv` of global functions of the two
models, `φ` is a ring map into the sections of the structure sheaf of the spaces-étale model over
its terminal object, hence a morphism of ringed topoi
`(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` (`AlgebraicGeometry.toPointRingedTopos`).

Its direct image is sections over the terminal object read as `R`-modules; through the equivalence
`AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` with `𝒪_X`-modules these are the global
sections `AlgebraicGeometry.Space.baseRingGlobalSectionsModule`, because sections over a terminal
object are the compatible families on a dense subsite.  So its inverse image, being left adjoint
to the direct image, is the functor `M ↦ 𝒪_X ⊗_R M` of Stacks 0D3F
(`AlgebraicGeometry.Space.baseRingTensorModule`), which is left adjoint to the same functor.

This puts the morphism `X ⟶ Spec(R)` in the form in which the derived pullback and the projection
formula map of Stacks 0B56 apply, with `Rf_* = RΓ(X, -)` and `f^*M = 𝒪_X ⊗_R M`: that projection
formula is the case of Stacks 08IN used in the proof of Stacks 0D3F.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelToBaseRing`: the morphism of ringed topoi
  `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` given by `φ`.
* `AlgebraicGeometry.Space.pushforwardToBaseRingIso`: its direct image is
  `AlgebraicGeometry.Space.baseRingGlobalSectionsModule`.
* `AlgebraicGeometry.Space.pullbackToBaseRingIso`: its inverse image is
  `AlgebraicGeometry.Space.baseRingTensorModule`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.DenseSubsiteModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- The ring map `φ : R →+* Γ(X, 𝒪_X)`, read on the small étale model, as a ring map into the
sections of the structure sheaf of the spaces-étale model over its terminal object. -/
def spacesEtaleModelBaseRingHom :
    CommRingCat.of R ⟶ (spacesEtaleModelStructureSheaf B S hS X).obj.obj
      (op (spacesEtaleModelTerminal B S hS X)) :=
  CommRingCat.ofHom ((spacesEtaleModelGlobalFunctionsEquiv B S hS X).symm.toRingHom.comp φ)

/-- **The morphism of ringed topoi `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` given by a ring map
`φ : R →+* Γ(X, 𝒪_X)`**, presented on the spaces-étale model: its functor of sites picks out the
terminal object `X`, and its structure map is `φ`. -/
def spacesEtaleModelToBaseRing :
    RingedToposSiteHom (spacesEtaleModelRingedTopos B S hS X)
      (pointRingedTopos (CommRingCat.of R)) :=
  toPointRingedTopos (spacesEtaleModelRingedTopos B S hS X)
    (spacesEtaleModelBaseRingHom B S hS X φ)

/-- The restriction of `φ r`, read over the terminal object of the spaces-étale model, to an
object of the small étale model is the value there of `φ r`. -/
theorem spacesEtaleModelTerminal_map_baseRingHom (r : R)
    (V : (SmallModel.{u} (SmallEtale B S hS X.1))ᵒᵖ) :
    (spacesEtaleModelStructureSheaf B S hS X).obj.map
      ((isTerminal_spacesEtaleModelTerminal B S hS X).from
        ((spacesEtaleModelComparison B S hS X).obj V.unop)).op
        (spacesEtaleModelBaseRingHom B S hS X φ r) =
      (spacesEtaleModelStructureRestrictionIso B S hS X).inv.hom.app V ((φ r).val V) := by
  have h := congrFun (congrArg Subtype.val
    ((spacesEtaleModelGlobalFunctionsEquiv B S hS X).apply_symm_apply (φ r))) V
  rw [← h]
  exact (Iso.hom_inv_id_apply
    (((sheafToPresheaf _ _).mapIso
      (spacesEtaleModelStructureRestrictionIso B S hS X)).app V) _).symm

/-- The ring of sections of the structure sheaf of the punctual ringed topos of `R` is `R`. -/
def pointRingEquiv :
    R ≃+* Stacks.PointRingedSite.ptRing (CommRingCat.of R) :=
  RingEquiv.refl R

/-- `R`-modules are the modules over the sections of the punctual structure sheaf. -/
def pointModuleCatEquiv :
    ModuleCat.{u} (Stacks.PointRingedSite.ptRing (CommRingCat.of R)) ≌ ModuleCat.{u} R :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (pointRingEquiv (R := R))

/-- The sections over the terminal object of a sheaf of modules on the spaces-étale model, as an
`R`-module, identified with the global sections of its image on the small étale model. -/
def terminalSectionsLinearEquiv (M : (spacesEtaleModelRingedTopos B S hS X).Modules) :
    ((spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos ⋙
        Stacks.PointRingedSite.ev (CommRingCat.of R) ⋙
          (pointModuleCatEquiv (R := R)).functor).obj M ≃ₗ[R]
      (moduleRestriction (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)
          (spacesEtaleModelComparison B S hS X)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)) ⋙
        SheafOfModules.restrictScalars (spacesEtaleModelRingRestrictionIso B S hS X).inv ⋙
        Stacks.Cohomology.SiteModules.baseRingGlobalSectionsFunctor.{u, u, u, u} φ).obj M :=
  { terminalSectionsEquiv (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)
      (spacesEtaleModelComparison B S hS X)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))
      (isTerminal_spacesEtaleModelTerminal B S hS X) M with
    map_add' := fun x y => Subtype.ext (funext fun V => (M.val.map _).hom.map_add x y)
    map_smul' := fun r x => Subtype.ext (funext fun V => by
      refine (M.val.map_smul ((isTerminal_spacesEtaleModelTerminal B S hS X).from
        ((spacesEtaleModelComparison B S hS X).obj V.unop)).op
          (spacesEtaleModelBaseRingHom B S hS X φ r) x).trans ?_
      exact congrArg (fun a => a • M.val.map ((isTerminal_spacesEtaleModelTerminal B S hS X).from
        ((spacesEtaleModelComparison B S hS X).obj V.unop)).op x)
          (spacesEtaleModelTerminal_map_baseRingHom B S hS X φ r V)) }

/-- Sections over the terminal object, read as `R`-modules, are the global sections of the
restriction to the small étale model, naturally. -/
def terminalSectionsIso :
    (spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos ⋙
        Stacks.PointRingedSite.ev (CommRingCat.of R) ⋙ (pointModuleCatEquiv (R := R)).functor ≅
      moduleRestriction (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)
          (spacesEtaleModelComparison B S hS X)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)) ⋙
        SheafOfModules.restrictScalars (spacesEtaleModelRingRestrictionIso B S hS X).inv ⋙
        Stacks.Cohomology.SiteModules.baseRingGlobalSectionsFunctor.{u, u, u, u} φ :=
  NatIso.ofComponents (fun M => (terminalSectionsLinearEquiv B S hS X φ M).toModuleIso)
    (fun {M N} g => by
      ext x
      refine Subtype.ext (funext fun V => ?_)
      exact (ConcreteCategory.congr_hom (g.val.naturality ((isTerminal_spacesEtaleModelTerminal
        B S hS X).from ((spacesEtaleModelComparison B S hS X).obj V.unop)).op) x).symm)

/-- **The direct image along `X ⟶ (pt, R)` is global sections read as `R`-modules**: on the
spaces-étale model it is sections over the terminal object, and through the equivalence with
`𝒪_X`-modules this is `AlgebraicGeometry.Space.baseRingGlobalSectionsModule`. -/
def pushforwardToBaseRingIso :
    (spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos ⋙
        Stacks.PointRingedSite.ev (CommRingCat.of R) ⋙ (pointModuleCatEquiv (R := R)).functor ≅
      (spacesEtaleModelModulesEquiv B S hS X).functor ⋙ baseRingGlobalSectionsModule B S hS X φ :=
  terminalSectionsIso B S hS X φ ≪≫
    Functor.isoWhiskerLeft
      (moduleRestriction (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)
          (spacesEtaleModelComparison B S hS X)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)) ⋙
        SheafOfModules.restrictScalars (spacesEtaleModelRingRestrictionIso B S hS X).inv)
      (Functor.isoWhiskerRight (smallEtaleModelModulesEquiv B S hS X).counitIso.symm
        (Stacks.Cohomology.SiteModules.baseRingGlobalSectionsFunctor.{u, u, u, u} φ))

/-- The adjunction `f^* ⊣ f_*` of the morphism to `(pt, R)`, transported to `R`-modules and
`𝒪_X`-modules. -/
def toBaseRingAdjunction :
    (pointModuleCatEquiv (R := R)).inverse ⋙ (Stacks.PointRingedSite.modulesEquiv
        (CommRingCat.of R)).inverse ⋙ (spacesEtaleModelToBaseRing B S hS X φ).pullbackTopos ⋙
          (spacesEtaleModelModulesEquiv B S hS X).functor ⊣
      baseRingGlobalSectionsModule B S hS X φ :=
  ((pointModuleCatEquiv (R := R)).symm.toAdjunction.comp
    ((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of R)).symm.toAdjunction.comp
      ((spacesEtaleModelToBaseRing B S hS X φ).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelModulesEquiv B S hS X).toAdjunction))).ofNatIsoRight
    (Functor.isoWhiskerLeft (spacesEtaleModelModulesEquiv B S hS X).inverse
        (pushforwardToBaseRingIso B S hS X φ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (spacesEtaleModelModulesEquiv B S hS X).counitIso _ ≪≫
      Functor.leftUnitor _)

/-- **The inverse image along `X ⟶ (pt, R)` is `M ↦ 𝒪_X ⊗_R M`**: both are left adjoint to
global sections read as `R`-modules. -/
def pullbackToBaseRingIso :
    (pointModuleCatEquiv (R := R)).inverse ⋙ (Stacks.PointRingedSite.modulesEquiv
        (CommRingCat.of R)).inverse ⋙ (spacesEtaleModelToBaseRing B S hS X φ).pullbackTopos ⋙
          (spacesEtaleModelModulesEquiv B S hS X).functor ≅
      baseRingTensorModule B S hS X φ :=
  (toBaseRingAdjunction B S hS X φ).leftAdjointUniq (baseRingTensorModuleAdjunction B S hS X φ)

end AlgebraicGeometry.Space

end
