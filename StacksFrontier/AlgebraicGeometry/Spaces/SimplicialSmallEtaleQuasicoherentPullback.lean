module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherentOfHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppfUnit
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictScalars

/-!
# Pullback of quasi-coherent modules along the augmentation of a simplicial algebraic space

Let `X` be a simplicial algebraic space with an augmentation `a : X → Z`. The pullback
`a^* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` along the morphism of ringed topoi `a` of Stacks 0DE7 carries
quasi-coherent modules to quasi-coherent modules (Stacks 03DO). The morphism `a` is base change
along `a` followed by `ε : const(Z) → Z`, forgetting the degree. Pullback along `ε` is restriction
along a continuous and cocontinuous functor, up to restriction of scalars along isomorphisms of
structure sheaves. Pullback along base change is the pullback of a morphism of ringed sites,
every object of whose source receives a map from the image of the final object.

## Main results

In the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `isQuasicoherentOnSite_constRingedToposHom_pullbackModules_obj`: pullback along
  `ε : const(Z) → Z` preserves quasi-coherence.
* `isQuasicoherentOnSite_ringedToposHom_pullbackModules_obj`: pullback along base change by a
  morphism of simplicial algebraic spaces preserves quasi-coherence.
* `isQuasicoherentOnSite_augmentationRingedToposHom_pullbackModules_obj`: `a^*𝓕` is
  quasi-coherent for a quasi-coherent `𝒪_Z`-module `𝓕`.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Const

variable (Z : AlgebraicSpaces B S hS)

/-- The map of structure sheaves `ε^{-1}𝒪_Z → 𝒪_{const(Z)}` underlying `ε : const(Z) → Z` is an
isomorphism. -/
instance isIso_constRingedToposHom_fSharpInverseImage :
    IsIso (constRingedToposHom Z).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso
    (X := ringedTopos ((Functor.const _).obj Z)) (Y := spacesEtaleRingedTopos B S hS Z)
    (constToposHom Z) _

/-- **Pullback along `ε : const(Z) → Z` preserves quasi-coherence**: it is restriction along the
functor forgetting the degree, read through restrictions of scalars along isomorphisms. -/
theorem isQuasicoherentOnSite_constRingedToposHom_pullbackModules_obj
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology B S hS Z)) (SpacesEtale.structureSheaf B S hS Z)))
    [hF : F.IsQuasicoherentOnSite] :
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1} (constRingedToposHom Z).toModulesHom).obj F).IsQuasicoherentOnSite := by
  have hR : ((Stacks.Sheaves.ToposPullback.restrictionModules (topology ((Functor.const _).obj Z))
      (SpacesEtale.topology B S hS Z) (constForget Z)
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (SpacesEtale.topology B S hS Z))
        (SpacesEtale.structureSheaf B S hS Z))).obj F).IsQuasicoherentOnSite := by
    have : ∀ V : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj Z),
        (Over.post (X := V) (constForget Z)).IsContinuous
          ((topology ((Functor.const _).obj Z)).over V)
          ((SpacesEtale.topology B S hS Z).over ((constForget Z).obj V)) :=
      fun V ↦ Functor.isContinuous_overPost _ _ _ V
    exact Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv.{u + 1,
      u + 1, u + 1, u + 1, u + 1, u + 1} (constForget Z) (𝟙 _) (IsIso.id _) F hF
  have h1 := Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso
    (Stacks.Sheaves.ToposPullback.restrictionRingIso (topology ((Functor.const _).obj Z))
      (SpacesEtale.topology B S hS Z) (constForget Z)
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (SpacesEtale.topology B S hS Z))
        (SpacesEtale.structureSheaf B S hS Z))).hom _ hR
  have h2 := Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso
    (asIso (constRingedToposHom Z).toModulesHom.fSharpInverseImage).inv _ h1
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso ?_ h2
  exact
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso
        (constRingedToposHom Z).toModulesHom).app _).symm ≪≫
      (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp
        (constRingedToposHom Z).toModulesHom).mapIso
          ((Stacks.Sheaves.ToposPullback.restrictionModuleIso (topology ((Functor.const _).obj Z))
            (SpacesEtale.topology B S hS Z) (constForget Z)
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
              (J := (SpacesEtale.topology B S hS Z))
              (SpacesEtale.structureSheaf B S hS Z))).app F).symm

end Const

section BaseChange

variable {X Y : SimplicialObject (AlgebraicSpaces B S hS)} (h : X ⟶ Y)

/-- **Base change along a morphism of simplicial algebraic spaces as a morphism of ringed
sites**, `X_{spaces,étale} → Y_{spaces,étale}`; its ringed topos morphism is `ringedToposHom h`. -/
def ringedSiteHom : RingedSite.Hom (ringedSite X) (ringedSite Y) where
  u := pullbackFunctor h
  isMorphismOfSites := (pullbackFunctor_isMorphismOfSites h).toSmallIsMorphismOfSites
  fsharp := structureSheafSharp h

/-- The morphism of ringed topoi `ringedToposHom h` is the one induced by the morphism of ringed
sites `ringedSiteHom h`. -/
theorem ringedToposHom_eq_ringedSiteHom_ringedToposHom :
    ringedToposHom h = (ringedSiteHom h).ringedToposHom :=
  rfl

/-- Every object `W/X_n` maps to the base change of the final object of `Y_n`. -/
theorem nonempty_hom_pullbackFunctor_obj (A : SimplicialSpacesEtaleSite B S hS X) :
    ∃ T : SimplicialSpacesEtaleSite B S hS Y, Nonempty (A ⟶ (pullbackFunctor h).obj T) :=
  ⟨(degreeInclusion Y A.degree).obj (SpacesEtale.idObj B S hS (Y.obj (op A.degree))),
    ⟨(degreeInclusion X A.degree).map
      ((isTerminal_spacesBaseChange_idObj B S hS (h.app (op A.degree))).from A.obj ≫
        (spacesBaseChangeIso h A.degree).hom.app _)⟩⟩

/-- **Pullback along base change preserves quasi-coherence** (Stacks 03DO). -/
theorem isQuasicoherentOnSite_ringedToposHom_pullbackModules_obj
    (M : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (J := (ringedSite Y).J)
        (ringedSite Y).O))
    [hM : M.IsQuasicoherentOnSite] :
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1} (ringedToposHom h).toModulesHom).obj M).IsQuasicoherentOnSite := by
  rw [ringedToposHom_eq_ringedSiteHom_ringedToposHom]
  have hq := Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom
    (ringedSiteHom h) (nonempty_hom_pullbackFunctor_obj h) hM
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (ringedSiteHom h).ringedToposHom).ofNatIsoRight
        (ringedSiteHom h).pushforwardToposIso).leftAdjointUniq
      (ringedSiteHom h).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos).app M).symm hq

end BaseChange

variable {Z : AlgebraicSpaces B S hS} {X : SimplicialObject (AlgebraicSpaces B S hS)}

/-- **Pullback along the augmentation of a simplicial algebraic space preserves
quasi-coherence** (Stacks 03DO): for an augmentation `a : X → Z` and a quasi-coherent
`𝒪_Z`-module `𝓕`, the `𝒪_X`-module `a^*𝓕` is quasi-coherent. -/
theorem isQuasicoherentOnSite_augmentationRingedToposHom_pullbackModules_obj
    (a : X ⟶ (Functor.const _).obj Z)
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology B S hS Z)) (SpacesEtale.structureSheaf B S hS Z)))
    [F.IsQuasicoherentOnSite] :
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1}
      (augmentationRingedToposHom a).toModulesHom).obj F).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((RingedToposHom.pullbackModulesCompIso (ringedToposHom a) (constRingedToposHom Z)).app F).symm
    (isQuasicoherentOnSite_ringedToposHom_pullbackModules_obj a _
      (hM := isQuasicoherentOnSite_constRingedToposHom_pullbackModules_obj Z F))

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
