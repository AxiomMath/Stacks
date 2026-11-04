module

public import StacksFrontier.AlgebraicGeometry.BaseModuleOnScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinalSectionsTop
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceDerivedComparison

/-!
# The associated-module equivalence of an affine algebraic space and its adjunction to sections

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`e : X ≅ h_U` be an isomorphism with the algebraic space represented by an object `U` of the site
whose underlying scheme `T` is affine. Write `A₀ = Γ(T, 𝒪_T)` for its ring of global functions.

This file constructs, at the module universe `u` of the schemes:

* the *associated-module equivalence* `Mod(A₀) ≌ QCoh(𝒪_X)`, the affine case of Stacks 03DX (2) on
  the small étale site of an algebraic space;
* its *adjunction to global sections*, the affine case of Stacks 01BH (4) on that site: the
  associated-module functor, followed by the inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)`, is left adjoint to
  the functor sending an `𝒪_X`-module `𝓕` to the `A₀`-module `Γ(X, 𝓕)`.

## Main definitions

* `AlgebraicGeometry.Space.affineChartQuasicoherentEquivalence`: `QCoh(T_étale) ≌ QCoh(𝒪_X)`, the
  quasi-coherent restriction of `AlgebraicGeometry.Space.affineChartModuleEquivalence`.
* `AlgebraicGeometry.Space.affineChartAssociatedModuleEquivalence`: `Mod(A₀) ≌ QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.affineChartGlobalSections`: `Mod(𝒪_X) ⥤ Mod(A₀)`, global sections.
* `AlgebraicGeometry.Space.affineChartTerminalChart`: the étale chart of `X` at which
  `AlgebraicGeometry.Space.affineChartGlobalSections` evaluates.
* `AlgebraicGeometry.Space.affineChartAssociatedModuleAdjunction`: the adjunction between the
  associated-module functor and `AlgebraicGeometry.Space.affineChartGlobalSections`.
* `AlgebraicGeometry.Space.globalSectionsEquivSectionsAtTerminalChart`: the additive bijection
  between `Γ(X, 𝓕)` and the sections of `𝓕` over that chart.

## Main results

* `AlgebraicGeometry.Space.isTerminal_affineChartTerminalChart`: that chart is terminal.
* `AlgebraicGeometry.Space.affineChartGlobalSections_obj_carrier`: the underlying type of
  `affineChartGlobalSections` at `𝓕` is the type of sections of `𝓕` over that chart.
* `AlgebraicGeometry.Space.globalSectionsEquivSectionsAtTerminalChart_smul` and
  `AlgebraicGeometry.Space.globalSectionsEquivSectionsAtTerminalChart_naturality`: that bijection
  is compatible with the action of global functions and natural in `𝓕`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (e : F ≅ yoneda.obj U)

/-! ### The quasi-coherent modules on `X` and on the small étale site of the chart -/

/-- Quasi-coherence on the small étale site of the scheme underlying `U` is the inverse image of
quasi-coherence on the small étale site of `X` along
`AlgebraicGeometry.Space.affineChartModuleEquivalence`, as an equality of object properties. -/
theorem inverseImage_isQuasicoherentOnSite_affineChartModuleEquivalence :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O))).inverseImage
        (affineChartModuleEquivalence B S hS F hF U e).functor =
      SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedSchemeStructureSheaf B S hS U) := by
  funext M
  exact propext
    (isQuasicoherentOnSite_affineChartModuleEquivalence_functor_obj_iff B S hS F hF U e M)

/-- **`QCoh(T_étale, 𝒪) ≌ QCoh(𝒪_X)`.** The equivalence of module categories
`AlgebraicGeometry.Space.affineChartModuleEquivalence` restricts to the quasi-coherent modules. -/
def affineChartQuasicoherentEquivalence :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedSchemeStructureSheaf B S hS U)).FullSubcategory ≌
      QuasicoherentSheaves.{u, u} B S hS F hF :=
  (affineChartModuleEquivalence B S hS F hF U e).congrFullSubcategory
    (inverseImage_isQuasicoherentOnSite_affineChartModuleEquivalence B S hS F hF U e)

/-! ### The associated-module equivalence and the global sections -/

/-- **The associated-module equivalence `Mod(A₀) ≌ QCoh(𝒪_X)`** of an algebraic space `X`
isomorphic to the one represented by an object with affine underlying scheme `T`, where
`A₀ = Γ(T, 𝒪_T)`: the equivalence `Mod(A₀) ≌ QCoh(T_étale)` of the affine scheme `T`, followed by
`AlgebraicGeometry.Space.affineChartQuasicoherentEquivalence`. -/
def affineChartAssociatedModuleEquivalence :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ≌
      QuasicoherentSheaves.{u, u} B S hS F hF :=
  letI := hU
  (_root_.AlgebraicGeometry.affineQuasicoherentModulesEquiv
      ((BigFppfOver.toScheme B S hS).obj U)).trans
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).trans
      (affineChartQuasicoherentEquivalence B S hS F hF U e))

/-- **Global sections of an `𝒪_X`-module as a module over `A₀ = Γ(T, 𝒪_T)`.** The `𝒪_X`-module is
read on the small étale site of `T` along `AlgebraicGeometry.Space.affineChartModuleEquivalence`,
restricted to the Zariski site of `T` along `ε : T_étale ⟶ T_Zar`, and its global sections are
taken there. -/
def affineChartGlobalSections :
    Modules.{u, u} B S hS F hF ⥤
      ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  letI := hU
  (affineChartModuleEquivalence B S hS F hF U e).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    Stacks.AlgebraicGeometry.BaseModuleOnScheme.globalSectionsFunctor
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom

/-- **The affine case of Stacks 01BH (4) on the small étale site of an algebraic space**: the
associated-module functor `Mod(A₀) ⥤ QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is left adjoint to global sections. It
is the composite of the tilde–Gamma adjunction of the affine scheme `T`, the adjunction `ε^* ⊣ ε_*`
between the Zariski and the small étale site of `T`, and the equivalence of module categories
`AlgebraicGeometry.Space.affineChartModuleEquivalence`. -/
def affineChartAssociatedModuleAdjunction :
    (affineChartAssociatedModuleEquivalence B S hS F hF U hU e).functor ⋙
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O))).ι ⊣
      affineChartGlobalSections B S hS F hF U hU e :=
  letI := hU
  Adjunction.ofNatIsoLeft
    (((Stacks.AlgebraicGeometry.BaseModuleOnScheme.adjunction
        ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).comp
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction _ _ _)).comp
        (affineChartModuleEquivalence B S hS F hF U e).toAdjunction)
    (Functor.isoWhiskerRight
      (_root_.AlgebraicGeometry.affineQuasicoherentModulesEquivCompι
        ((BigFppfOver.toScheme B S hS).obj U)).symm
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
        (affineChartModuleEquivalence B S hS F hF U e).functor))

/-- Global sections through the chart are additive. -/
instance additive_affineChartGlobalSections :
    (affineChartGlobalSections B S hS F hF U hU e).Additive :=
  letI := hU
  inferInstanceAs
    (((affineChartModuleEquivalence B S hS F hF U e).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
      Stacks.AlgebraicGeometry.BaseModuleOnScheme.globalSectionsFunctor
        ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).Additive)

/-- The associated-module functor into all `𝒪_X`-modules is additive. -/
instance additive_affineChartAssociatedModuleEquivalence_functor_comp_ι :
    ((affineChartAssociatedModuleEquivalence B S hS F hF U hU e).functor ⋙
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).ι).Additive :=
  (affineChartAssociatedModuleAdjunction B S hS F hF U hU e).left_adjoint_additive

/-- The associated-module functor `Mod(A₀) ⥤ QCoh(𝒪_X)` is additive. -/
instance additive_affineChartAssociatedModuleEquivalence_functor :
    (affineChartAssociatedModuleEquivalence B S hS F hF U hU e).functor.Additive :=
  Functor.additive_of_comp_faithful _
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι

/-! ### The global sections are the global sections -/

/-- The étale chart of `X` at which `AlgebraicGeometry.Space.affineChartGlobalSections` evaluates:
the image, under the two equivalences of small étale sites
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and
`AlgebraicGeometry.Space.SmallEtale.congr`, of the object `⊤` of the small étale site of the scheme
`T`. -/
def affineChartTerminalChart : SmallEtale B S hS F :=
  (SmallEtale.congr B S hS e).inverse.obj
    ((representedSmallEtaleEquivalence B S hS U).inverse.obj
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤))

/-- The chart `AlgebraicGeometry.Space.affineChartTerminalChart` is terminal in the small étale
site of `X`. -/
def isTerminal_affineChartTerminalChart :
    IsTerminal (affineChartTerminalChart B S hS F U e) :=
  ((_root_.AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).isTerminalObj
    (representedSmallEtaleEquivalence B S hS U).inverse _).isTerminalObj
      (SmallEtale.congr B S hS e).inverse _

/-- Global sections of a module on a scheme over `Spec k`, read as a `k`-module, are its sections
over `⊤`. -/
theorem baseModuleGlobalSections_obj_carrier {k : CommRingCat.{u}} {X : Scheme.{u}}
    (π : X ⟶ Spec k) (G : X.Modules) :
    ((Stacks.AlgebraicGeometry.BaseModuleOnScheme.globalSectionsFunctor π).obj G).carrier =
      (G.presheaf.obj (op (⊤ : X.Opens)) : Type u) := rfl

/-- Reindexing along `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` is evaluation at
the image of the object. -/
theorem representedSmallEtaleModuleEquivalence_inverse_obj_presheaf_obj
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (V : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :
    (((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N).val.presheaf.obj
        (op V) : Type u) =
      (N.val.presheaf.obj (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj V))
        : Type u) := rfl

/-- Reindexing along `AlgebraicGeometry.Space.SmallEtale.congr` is evaluation at the image of the
object. -/
theorem smallEtaleCongrModuleEquivalence_inverse_obj_presheaf_obj
    (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS (yoneda.obj U)) :
    ((Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B S hS F)
          (SmallEtale.congr B S hS e)
          (representedStructureRingSheaf B S hS U)).inverse.obj M).val.presheaf.obj (op V) =
      M.val.presheaf.obj (op ((SmallEtale.congr B S hS e).inverse.obj V)) := rfl

/-- The underlying type of the `A₀`-module `AlgebraicGeometry.Space.affineChartGlobalSections`
assigns to an `𝒪_X`-module `𝓕` is the type of sections of `𝓕` over the étale chart
`AlgebraicGeometry.Space.affineChartTerminalChart`. -/
theorem affineChartGlobalSections_obj_carrier (M : Modules.{u, u} B S hS F hF) :
    ((affineChartGlobalSections B S hS F hF U hU e).obj M).carrier =
      (M.val.presheaf.obj (op (affineChartTerminalChart B S hS F U e)) : Type u) :=
  let := hU
  (baseModuleGlobalSections_obj_carrier _ _).trans
    ((congrArg (fun G : AddCommGrpCat.{u} => (G : Type u))
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule_obj_presheaf_obj
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
          ((affineChartModuleEquivalence B S hS F hF U e).inverse.obj M) ⊤)).trans
      ((representedSmallEtaleModuleEquivalence_inverse_obj_presheaf_obj B S hS U
          ((Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B S hS F)
            (SmallEtale.congr B S hS e)
            (representedStructureRingSheaf B S hS U)).inverse.obj M) _).trans
        (congrArg (fun G : AddCommGrpCat.{u} => (G : Type u))
          (smallEtaleCongrModuleEquivalence_inverse_obj_presheaf_obj B S hS F hF U e M _))))

/-- The additive bijection between `Γ(X, 𝓕)`, the compatible families of sections of `𝓕` on the
small étale site of `X`, and the sections of `𝓕` over the terminal chart
`AlgebraicGeometry.Space.affineChartTerminalChart`, given by evaluation. -/
def globalSectionsEquivSectionsAtTerminalChart (M : Modules.{u, u} B S hS F hF) :
    Stacks.Cohomology.SiteModules.GlobalSections
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) M ≃+
      (M.val.presheaf.obj (op (affineChartTerminalChart B S hS F U e)) : Type u) where
  toFun s := s.val (op (affineChartTerminalChart B S hS F U e))
  invFun x := (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
    (isTerminal_affineChartTerminalChart B S hS F U e)).symm x
  left_inv s :=
    (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
      (isTerminal_affineChartTerminalChart B S hS F U e)).left_inv s
  right_inv x :=
    (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
      (isTerminal_affineChartTerminalChart B S hS F U e)).right_inv x
  map_add' _ _ := rfl

/-- The bijection `Γ(X, 𝓕) ≃ 𝓕(V)` at a terminal chart `V` carries the action of a global function
of `X` to the action of its value at `V`. -/
theorem globalSectionsEquivSectionsAtTerminalChart_smul (M : Modules.{u, u} B S hS F hF)
    (a : Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    (s : Stacks.Cohomology.SiteModules.GlobalSections
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) M) :
    globalSectionsEquivSectionsAtTerminalChart B S hS F hF U e M (a • s) =
      Stacks.Cohomology.SiteModules.globalSectionEval
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          (op (affineChartTerminalChart B S hS F U e)) a •
        globalSectionsEquivSectionsAtTerminalChart B S hS F hF U e M s :=
  rfl

/-- The bijection `Γ(X, 𝓕) ≃ 𝓕(V)` at a terminal chart `V` is natural in `𝓕`. -/
theorem globalSectionsEquivSectionsAtTerminalChart_naturality
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (s : Stacks.Cohomology.SiteModules.GlobalSections
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) M) :
    globalSectionsEquivSectionsAtTerminalChart B S hS F hF U e N
        ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O))).map f s) =
      f.val.app (op (affineChartTerminalChart B S hS F U e))
        (globalSectionsEquivSectionsAtTerminalChart B S hS F hF U e M s) :=
  rfl

end AlgebraicGeometry.Space

end
