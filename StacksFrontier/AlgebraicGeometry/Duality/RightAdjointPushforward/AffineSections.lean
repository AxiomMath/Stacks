module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.Topology.Sheaves.Functors.Module.HomSheaf
public import StacksFrontier.Topology.Sheaves.Functors.Module.PushforwardSheaf

/-!
# Internal Hom for an affine morphism

Let `f : Y ⟶ X` be an affine morphism of schemes. Restriction of scalars from modules over
`f_* 𝒪_Y` to modules over `𝒪_X` has a right adjoint, namely the internal-Hom functor
`ℰom_{𝒪_X}(f_* 𝒪_Y, -)`. This file computes its sections on an affine open of `X`: they are
the module homomorphisms from the sections of `𝒪_Y` over the inverse image.

## Main definitions

* `CategoryTheory.ffAddEquiv` and `CategoryTheory.isoAddEquiv` are the additive refinements of
  the hom-set bijections induced by a fully faithful additive functor and by isomorphisms of
  source and target.
* `AlgebraicGeometry.moduleSpecSectionsIso` identifies the global sections of a restriction to
  `Spec Γ(X, V)` with the sections over the affine open `V`.
* `AlgebraicGeometry.coextSecToHom` identifies the coextension-of-scalars sections over `U`
  with morphisms over `U`.

## Main results

* `AlgebraicGeometry.sections_rightAdjoint_restrictionToStructureSheaf` computes the right
  adjoint on affine opens.

## Implementation notes

The adjunction part of the source is the general restriction-of-scalars result
`RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction`, whose chosen right adjoint is
`RingedSpaceModuleAdjunction.homSheaf`; the tag is attached to it rather than restated. The
section formula is an additive equivalence; the right-hand side is the group of `Γ(X,U)`-linear
maps from `Γ(Y,f⁻¹U)` to `Γ(U,F)`.

The computation transports the problem to `Spec Γ(X, U)` along `IsAffineOpen.isoSpec` and then
applies the `tilde`–global-sections adjunction there. The identification of global sections of
a restriction to `Spec Γ(X, U)` with sections on the affine open itself is
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictSectionsEquiv` composed with
`sectionsCongrSelf`.

## References

* [Stacks Project, Tag 0BUZ](https://stacks.math.columbia.edu/tag/0BUZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace CategoryTheory

/-- A fully faithful additive functor induces an additive equivalence on hom-groups. -/
public noncomputable def ffAddEquiv {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {F : C ⥤ D} (hF : F.FullyFaithful)
    [F.Additive] (X Y : C) : AddEquiv (X ⟶ Y) (F.obj X ⟶ F.obj Y) where
  toFun := hF.homEquiv
  invFun := hF.homEquiv.symm
  left_inv := hF.homEquiv.left_inv
  right_inv := hF.homEquiv.right_inv
  map_add' := by
    intro f g
    change F.map (f + g) = F.map f + F.map g
    simp

/-- Transporting hom-groups along isomorphisms of source and target is additive. -/
public noncomputable def isoAddEquiv {C : Type*} [Category C] [Preadditive C]
    {X Y X' Y' : C} (i : X ≅ X') (j : Y ≅ Y') : AddEquiv (X ⟶ Y) (X' ⟶ Y') where
  toFun := i.homCongr j
  invFun := (i.homCongr j).symm
  left_inv := (i.homCongr j).left_inv
  right_inv := (i.homCongr j).right_inv
  map_add' := by intro f g; simp [Iso.homCongr]

end CategoryTheory

namespace AlgebraicGeometry

add_to_stacks 0BUZ "the adjunction" RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction

/-- The module of global sections of the restriction of `F` to `Spec Γ(X, V)`, as an object of
`ModuleCat Γ(X, V)`, is the module of sections of `F` over the affine open `V`. -/
public noncomputable def moduleSpecSectionsIso {X : Scheme.{u}} (F : X.Modules)
    (V : X.affineOpens) [IsOpenImmersion V.2.fromSpec] :
    (AlgebraicGeometry.moduleSpecΓFunctor
      (R := CommRingCat.of Γ(X, V.1))).obj
        ((Scheme.Modules.restrictFunctor V.2.fromSpec).obj F) ≅
      ModuleCat.of Γ(X, V.1) Γ(F, V.1) := by
  have hTop : V.2.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V.1)).Opens) = V.1 :=
    (Scheme.Hom.image_top_eq_opensRange _).trans V.2.opensRange_fromSpec
  let e : Γ(F.restrict V.2.fromSpec, ⊤) ≃ₗ[Γ(X, V.1)] Γ(F, V.1) :=
    (restrictSectionsEquiv F V.2 ⊤).trans
      (sectionsCongrSelf F hTop (fromSpec_image_le V.2 ⊤))
  exact e.toModuleIso

/-- The explicit coextension-of-scalars sections over `U` are the morphisms, over `U`, from the
pushforward of the structure sheaf of `Y` to `F`. -/
public noncomputable def coextSecToHom
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) (U : X.Opens) :
    Stacks.PresheafOfModules.CoextendScalars.coextSec f.toRingCatSheafHom.hom F.val (op U) ≃+
      ((Scheme.Modules.restrictFunctor U.ι).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) ⟶
       (Scheme.Modules.restrictFunctor U.ι).obj F) := by
  let G := SheafOfModules.overFunctor X.ringCatSheaf U
  let E := Scheme.Modules.overEquiv U
  let M : X.Modules := (Scheme.Modules.pushforward f).obj
    (SheafOfModules.unit Y.ringCatSheaf)
  let S := G.obj M
  let T := G.obj F
  let hForget := SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over U)
  letI : E.functor.Additive := { map_add := by intro A B x y; ext; rfl }
  let h₁ : AddEquiv (Stacks.PresheafOfModules.CoextendScalars.coextSec f.toRingCatSheafHom.hom F.val
    (op U)) (S ⟶ T) := by
    change AddEquiv (S.val ⟶ T.val) (S ⟶ T)
    exact (ffAddEquiv hForget S T).symm
  let h₂ : AddEquiv (S ⟶ T) (E.functor.obj S ⟶ E.functor.obj T) :=
    ffAddEquiv E.fullyFaithfulFunctor S T
  let eS := (Scheme.Modules.overFunctorEquiv U).app M
  change E.functor.obj S ≅ (Scheme.Modules.restrictFunctor U.ι).obj M at eS
  let eT := (Scheme.Modules.overFunctorEquiv U).app F
  change E.functor.obj T ≅ (Scheme.Modules.restrictFunctor U.ι).obj F at eT
  exact h₁.trans (h₂.trans (isoAddEquiv eS eT))

/-- **Stacks Project, Tag 0BUZ (sections on an affine open).** If `f : Y ⟶ X` is
affine and `U ⊆ X` is affine, sections over `U` of the internal-Hom right adjoint
are the `Γ(X,U)`-linear maps from `Γ(Y,f⁻¹U)` to the sections of `F` over `U`. -/
@[stacks 0BUZ "sections on an affine open"]
public noncomputable def sections_rightAdjoint_restrictionToStructureSheaf
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] (F : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    (((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).obj F).val.obj
        (op U) : Type u) ≃+
      (ModuleCat.of Γ(X, U) Γ(Y, f ⁻¹ᵁ U) ⟶ ModuleCat.of Γ(X, U) Γ(F, U)) := by
  letI : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let R : CommRingCat := CommRingCat.of Γ(X, U)
  let S : X.Modules := (Scheme.Modules.pushforward f).obj
    (SheafOfModules.unit Y.ringCatSheaf)
  let M : (U : Scheme).Modules := (Scheme.Modules.restrictFunctor U.ι).obj S
  let N : (U : Scheme).Modules := (Scheme.Modules.restrictFunctor U.ι).obj F
  let e := hU.isoSpec
  let E : (U : Scheme).Modules ≌ (Spec R).Modules :=
    CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.inv)
      (Scheme.Modules.restrictFunctor e.hom)
      (((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
        Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
        Scheme.Modules.restrictFunctorId).symm)
      ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
        Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
        Scheme.Modules.restrictFunctorId)
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : E.functor.Additive :=
    { map_add := by
        intro A B g h
        ext V x
        rfl }
  let M' := E.functor.obj M
  let N' := E.functor.obj N
  letI : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y
  letI : S.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f _
  letI : M.IsQuasicoherent := inferInstance
  letI : M'.IsQuasicoherent := by
    dsimp [M', E]
    exact Scheme.Modules.isQuasicoherent_restrictFunctor e.inv M
  let hM : IsIso M'.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M'
  let eM : tilde ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj M') ≅ M' :=
    @asIso _ _ _ _ M'.fromTildeΓ hM
  let h₁ := coextSecToHom f F U
  let h₂ := ffAddEquiv E.fullyFaithfulFunctor M N
  let h₃ := isoAddEquiv eM.symm (Iso.refl N')
  let c := Scheme.Modules.restrictFunctorComp e.inv U.ι
  let hc : e.inv ≫ U.ι = hU.fromSpec := hU.isoSpec_inv_ι
  let d := Scheme.Modules.restrictFunctorCongr hc
  let isoM : M' ≅ (Scheme.Modules.restrictFunctor hU.fromSpec).obj S :=
    (c.app S).symm ≪≫ d.app S
  let isoN : N' ≅ (Scheme.Modules.restrictFunctor hU.fromSpec).obj F :=
    (c.app F).symm ≪≫ d.app F
  let V : X.affineOpens := ⟨U, hU⟩
  letI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  let isoMΓ : (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj M' ≅
      ModuleCat.of Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
    (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).mapIso isoM ≪≫
      moduleSpecSectionsIso S V
  let isoNΓ : (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj N' ≅
      ModuleCat.of Γ(X, U) Γ(F, U) :=
    (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).mapIso isoN ≪≫
      moduleSpecSectionsIso F V
  let h₄ : AddEquiv
      (tilde ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj M') ⟶ N')
      (ModuleCat.of Γ(X, U) Γ(Y, f ⁻¹ᵁ U) ⟶ ModuleCat.of Γ(X, U) Γ(F, U)) :=
    ((tilde.adjunction (R := R)).homAddEquiv
      ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj M') N').trans
        (isoAddEquiv isoMΓ isoNΓ)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end AlgebraicGeometry
