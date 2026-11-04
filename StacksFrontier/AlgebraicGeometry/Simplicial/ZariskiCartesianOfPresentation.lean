module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.QuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCartesianModule
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiQuasicoherentComponents
public import StacksFrontier.Topology.OpensMapFinal

/-!
# The transition of a cartesian module on the structure sheaf

Let `X` be a simplicial scheme and `φ : n ⟶ m` a map of simplicial degrees, so that
`X φ : X_n ⟶ X_m` is a morphism of schemes. Stacks 09WF attaches to `φ` a transition
`(X φ)^* F_m ⟶ F_n` for every sheaf of `𝒪_X`-modules `F` on the total Zariski site, and
Stacks 07TF (2) calls `F` cartesian when every transition is an isomorphism.

This file computes that transition on the structure sheaf `F = 𝒪_X`, where it is an
isomorphism, and runs the colimit mechanism of Stacks 0D7M on it: a natural transformation
between two colimit-preserving functors which is invertible on the structure sheaf is
invertible on every module built from the structure sheaf by coproducts and cokernels. The
conclusion is that a module with a *global* presentation on the total Zariski site is
cartesian — the global form of the forward implication of Stacks 0D7M.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.componentUnitHom`: the degree-`k` component of `𝒪_X` is
  the structure sheaf of `X_k`, read as a map of sheaves of modules out of the unit.
* `AlgebraicGeometry.SimplicialScheme.transitionUnitHom` and `transitionPullbackUnitHom`: the
  structure morphism of `X φ` and its mate `(X φ)^* 𝒪_{X_m} ⟶ 𝒪_{X_n}`.
* `AlgebraicGeometry.SimplicialScheme.componentModuleTransitionNatTrans`: the transition of
  Stacks 09WF as a natural transformation of functors on `Modules X`.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isIso_componentUnitHom` and
  `isIso_transitionPullbackUnitHom`: those two comparisons are isomorphisms.
* `AlgebraicGeometry.SimplicialScheme.componentModuleDirectTransition_app_unit`: **the direct
  transition of Stacks 09WF on the structure sheaf is the structure morphism of `X φ`**, under
  the identifications of the two components of `𝒪_X` with structure sheaves.
* `AlgebraicGeometry.SimplicialScheme.isIso_componentModuleTransition_unit`: **the transition
  of Stacks 09WF on the structure sheaf is an isomorphism.**
* `AlgebraicGeometry.SimplicialScheme.componentModule_preservesColimitsOfSize`: the component
  functor preserves colimits.
* `AlgebraicGeometry.SimplicialScheme.isCartesianModule_of_presentation`: **a sheaf of
  `𝒪_X`-modules with a global presentation on the total Zariski site is cartesian.**

## What is not proved

Stacks 0D7M is an equivalence and both of its directions are local: `F` is quasi-coherent when
every object of the total site has a covering on whose members `F` admits a presentation. The
step from `isCartesianModule_of_presentation` to the forward implication of 0D7M, and the
whole converse, need the transition and the component functor read on a *slice* of the total
Zariski site at an object `(n, W)`. Those are
`AlgebraicGeometry.SimplicialScheme.sliceComponentModuleTransition` and
`.sliceComponentModuleAt`, and with them both implications of Stacks 0D7M are proved, at
`AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_iff_isCartesianModule_and_components`.
Neither implication is proved *here*: this file supplies the global form, which is the input the
slice argument runs the colimit mechanism on.

## Implementation notes

The square on the structure sheaf is the module-level reading of
`transitionStructureHom_eq`, which is the same statement one level down, for sheaves of rings.
Both of its sides are morphisms out of `SheafOfModules.unit`, so they are determined by the
image of `1` in every degree, and on sections the two identifications of a component of `𝒪_X`
with a structure sheaf are identities; what is left is exactly the ring-level square. It is
transported rather than recomputed: `Sheaf.hom_ext_iff` and `NatTrans.congr_app` turn
`transitionStructureHom_eq` into an equality of ring maps on sections over a fixed open, and
`ConcreteCategory.congr_hom` evaluates that at `1`.

Rewriting inside these goals does not work and the reason is worth recording. The sites of the
simplicial degrees are the open-set sites of the schemes `X_k`, so the structure sheaf is
`(X.obj k).ringCatSheaf`, whose type is `TopCat.Sheaf RingCat (X.obj k)` — a `def` with its own
derived `Category` instance, not the `Sheaf (Opens.grothendieckTopology _) RingCat` that
`SheafOfModules.comp_val` speaks about. The two are definitionally equal but a rewrite by
`comp_val` produces a motive that is not type-correct at the transparency `rw` checks it at, so
the rewrite is refused; `simp` makes no progress at all for the same reason. Proof terms built
from `congrArg` and `ConcreteCategory.congr_hom`, whose defeq checks run at default
transparency, go through.

The transition itself is the mate of the direct transition. Since the two component
identifications are isomorphisms, the mate of the square's right-hand side is the mate of the
structure morphism of `X φ`, which is Mathlib's `SheafOfModules.pullbackObjUnitToUnit` — an
isomorphism because `TopologicalSpace.Opens.map (X φ).base` is a final functor, the opens of
`X_m` whose preimage contains a fixed open of `X_n` having a largest member.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial
open Stacks.Sheaves.RingedToposModules

universe u v₁ u₁ v₂ u₂ r

namespace AlgebraicGeometry.SimplicialScheme

variable (X : SimplicialObject Scheme.{u}) {n m : SimplexCategoryᵒᵖ}

/-- **The degree-`k` component of `𝒪_X` is the structure sheaf of `X_k`.** The identification
`componentStructureHom`, read as a morphism of sheaves of modules out of the unit object. -/
public noncomputable def componentUnitHom (k : SimplexCategoryᵒᵖ) :
    (SheafOfModules.unit (X.obj k).ringCatSheaf : (X.obj k).Modules) ⟶
      (componentModule X k).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)) :=
  SheafOfModules.unitToPushforwardObjUnit (componentStructureHom X k)

/-- An isomorphism of sheaves of rings induces an isomorphism on the canonical map out of the
unit object: on underlying presheaves of abelian groups the latter *is* the former.

This is `Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit` of
`StacksFrontier/Algebra/Homology/StrictlyPerfectApproximationLocal.lean`, restated because that
module reaches the simplicial-sites tree only through derived categories of ringed spaces; the
two belong in one place. Public rather than private, because the same fact is what makes the
counit of the slice adjunction of `ZariskiSlicePullback` invertible on the structure sheaf. -/
public theorem isIso_unitToPushforwardObjUnit' {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D} {Fun : C ⥤ D}
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}} [Functor.IsContinuous Fun J K]
    (φ : S ⟶ (Fun.sheafPushforwardContinuous RingCat.{r} J K).obj R) [IsIso φ] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit φ) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget.{r} S ⋙
    PresheafOfModules.toPresheaf S.obj), NatTrans.isIso_iff_isIso_app]
  intro W
  have h1 : IsIso (φ.hom.app W) := NatIso.isIso_app_of_isIso φ.hom W
  rw [← isIso_iff_of_reflects_iso _ (forget AddCommGrpCat.{r}), isIso_iff_bijective]
  have h2 : (forget AddCommGrpCat.{r}).map (((SheafOfModules.forget.{r} S ⋙
      PresheafOfModules.toPresheaf S.obj).map
      (SheafOfModules.unitToPushforwardObjUnit φ)).app W) =
      (forget RingCat.{r}).map (φ.hom.app W) := by
    ext x
    exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply φ x
  rw [h2]
  exact ConcreteCategory.bijective_of_isIso (φ.hom.app W)

/-- The comparison `componentUnitHom X k` is an isomorphism, because the structure map
`componentStructureHom X k` of the degree-`k` component is. -/
public instance isIso_componentUnitHom (k : SimplexCategoryᵒᵖ) :
    IsIso (componentUnitHom X k) := by
  change IsIso (SheafOfModules.unitToPushforwardObjUnit (componentStructureHom X k))
  exact @isIso_unitToPushforwardObjUnit' _ _ _ _ _ _ _ _ _ _
    (componentStructureHom X k) (isIso_componentStructureHom X k)

/-- **The structure morphism of `X φ`**, read as a morphism of sheaves of modules out of the
unit object, at the type the transitions of the total Zariski site are stated at. -/
public noncomputable def transitionUnitHom (φ : n ⟶ m) :
    (SheafOfModules.unit (X.obj m).ringCatSheaf : (X.obj m).Modules) ⟶
      (Scheme.Modules.pushforward (X.map φ)).obj
        (SheafOfModules.unit (X.obj n).ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit ((X.map φ).toRingCatSheafHom)

/-- **The comparison `(X φ)^* 𝒪_{X_m} ⟶ 𝒪_{X_n}`**: the mate of the structure morphism of
`X φ` under the adjunction `(X φ)^* ⊣ (X φ)_*` of sheaves of modules on schemes. -/
public noncomputable def transitionPullbackUnitHom (φ : n ⟶ m) :
    (Scheme.Modules.pullback (X.map φ)).obj (SheafOfModules.unit (X.obj m).ringCatSheaf) ⟶
      (SheafOfModules.unit (X.obj n).ringCatSheaf : (X.obj n).Modules) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ)).homEquiv _ _).symm
    (transitionUnitHom X φ)

/-- **The pullback of the structure sheaf is the structure sheaf.** The comparison
`(X φ)^* 𝒪_{X_m} ⟶ 𝒪_{X_n}` is an isomorphism, because `Opens.map (X φ)` is a final functor:
the opens of `X_m` whose preimage contains a fixed open of `X_n` have a largest member. -/
public instance isIso_transitionPullbackUnitHom (φ : n ⟶ m) :
    IsIso (transitionPullbackUnitHom X φ) := by
  have : (TopologicalSpace.Opens.map (X.map φ).base).Final :=
    Stacks.Topology.final_opensMap (X.map φ).base
  have : (SheafOfModules.pushforward.{u} ((X.map φ).toRingCatSheafHom)).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward (X.map φ)).IsRightAdjoint)
  change IsIso (SheafOfModules.pullbackObjUnitToUnit ((X.map φ).toRingCatSheafHom))
  exact SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal ((X.map φ).toRingCatSheafHom)

/-- **The direct transition of Stacks 09WF on the structure sheaf is the structure morphism of
`X φ`.** Under the identifications of the degree-`m` and degree-`n` components of `𝒪_X` with the
structure sheaves of `X_m` and `X_n`, the transition `(𝒪_X)_m ⟶ (X φ)_* (𝒪_X)_n` of Stacks 09WF
is `(X φ)^♯`. -/
public theorem componentModuleDirectTransition_app_unit (φ : n ⟶ m) :
    componentUnitHom X m ≫ (componentModuleDirectTransition X φ).app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)) =
      transitionUnitHom X φ ≫
        (Scheme.Modules.pushforward (X.map φ)).map (componentUnitHom X n) := by
  ext V
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (Sheaf.hom_ext_iff.mp (transitionStructureHom_eq X φ)) V) 1

/-- **The transition of Stacks 09WF on the structure sheaf is an isomorphism.** Under the
identifications of the two components of `𝒪_X` with the structure sheaves of `X_m` and `X_n`,
the transition `(X φ)^* (𝒪_X)_m ⟶ (𝒪_X)_n` is the comparison `(X φ)^* 𝒪_{X_m} ⟶ 𝒪_{X_n}`.

This is the one input that the colimit mechanism of Stacks 0D7M asks of the total Zariski
site: it is what makes the transition invertible on free modules, hence on every module with a
presentation. -/
public theorem isIso_componentModuleTransition_unit (φ : n ⟶ m) :
    IsIso (componentModuleTransition X φ
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O))) := by
  let em := @asIso _ _ _ _ (componentUnitHom X m) (isIso_componentUnitHom X m)
  let en := @asIso _ _ _ _ (componentUnitHom X n) (isIso_componentUnitHom X n)
  let ep := @asIso _ _ _ _ (transitionPullbackUnitHom X φ) (isIso_transitionPullbackUnitHom X φ)
  have hdir : (componentModuleDirectTransition X φ).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)) =
      em.inv ≫ (transitionUnitHom X φ ≫
          (Scheme.Modules.pushforward (X.map φ)).map (componentUnitHom X n)) :=
    (em.inv_hom_id_assoc _).symm.trans
      (congrArg (fun t => em.inv ≫ t) (componentModuleDirectTransition_app_unit X φ))
  have key : componentModuleTransition X φ
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)) =
      ((Scheme.Modules.pullback (X.map φ)).mapIso em).inv ≫ (ep ≪≫ en).hom :=
    (congrArg (fun t => ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ)).homEquiv
          ((componentModule X m).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)))
          ((componentModule X n).obj
            (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)))).symm t)
        hdir).trans
      ((Adjunction.homEquiv_naturality_left_symm _ em.inv _).trans
        (congrArg (fun t => (Scheme.Modules.pullback (X.map φ)).map em.inv ≫ t)
          (Adjunction.homEquiv_naturality_right_symm _ (transitionUnitHom X φ)
            (componentUnitHom X n))))
  rw [key]
  infer_instance

/-- **The transition of Stacks 09WF, as a natural transformation.** The mate of
`componentModuleDirectTransition` is natural in the module, because the direct transition is. -/
public noncomputable def componentModuleTransitionNatTrans (φ : n ⟶ m) :
    componentModule X m ⋙ Scheme.Modules.pullback (X.map φ) ⟶ componentModule X n where
  app F := componentModuleTransition X φ F
  naturality F G f :=
    ((Adjunction.homEquiv_naturality_left_symm
        (Scheme.Modules.pullbackPushforwardAdjunction (X.map φ))
        ((componentModule X m).map f)
        (componentModuleDirectTransition X φ |>.app G)).symm.trans
      (congrArg (fun t => ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ)).homEquiv
            ((componentModule X m).obj F)
            ((componentModule X n).obj G)).symm t)
        ((componentModuleDirectTransition X φ).naturality f))).trans
      (Adjunction.homEquiv_naturality_right_symm
        (Scheme.Modules.pullbackPushforwardAdjunction (X.map φ))
        ((componentModuleDirectTransition X φ).app F) ((componentModule X n).map f))

/-- The component of `componentModuleTransitionNatTrans X φ` at `F` is
`componentModuleTransition X φ F`. -/
@[simp] public theorem componentModuleTransitionNatTrans_app (φ : n ⟶ m) (F : Modules X) :
    (componentModuleTransitionNatTrans X φ).app F = componentModuleTransition X φ F := rfl

/-- **The component functor preserves colimits.** It is restriction along the inclusion of a
simplicial degree, which is continuous and cocontinuous by Stacks 09W0. -/
public noncomputable instance componentModule_preservesColimitsOfSize (k : SimplexCategoryᵒᵖ) :
    Limits.PreservesColimitsOfSize.{u, u} (componentModule X k) :=
  Stacks.SheafOfModules.pushforward_preservesColimits
    (J := Opens.grothendieckTopology ((zariskiSpace X).obj k)) (K := zariskiTopology X)
    (levelFunctor (zariskiSpace X) k) (componentStructureHom X k)

/-- **A module with a global presentation on the total Zariski site is cartesian.** The
transition of Stacks 09WF is a natural transformation between two functors that preserve
colimits — restriction to a simplicial degree followed by a pullback of sheaves of modules on
schemes — and it is invertible on the structure sheaf, so it is invertible on every module
exhibited as a cokernel of a map of coproducts of copies of the structure sheaf.

This is the global form of the forward implication of Stacks 0D7M. The source's statement is
local, and deducing it from this needs the transition to be read on a slice of the total site
at an object, which the development does not have for the total Zariski site. -/
public theorem isCartesianModule_of_presentation (F : Modules X) (P : F.Presentation) :
    IsCartesianModule X F := by
  intro n m φ
  have h1 : Limits.PreservesColimitsOfSize.{u, u}
      (componentModule X m ⋙ Scheme.Modules.pullback (X.map φ)) :=
    Limits.comp_preservesColimits _ _
  have h2 : Limits.PreservesFiniteColimits
      (componentModule X m ⋙ Scheme.Modules.pullback (X.map φ)) :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  have h3 : Limits.PreservesFiniteColimits (componentModule X n) :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  exact Stacks.SheafOfModules.isIso_app_of_presentation_of_unit
    (componentModuleTransitionNatTrans X φ) (isIso_componentModuleTransition_unit X φ) P

end AlgebraicGeometry.SimplicialScheme

end
