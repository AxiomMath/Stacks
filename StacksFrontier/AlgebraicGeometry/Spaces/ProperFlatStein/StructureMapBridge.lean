module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctionsEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGammaFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral

/-!
# `𝒪_{Y'} = f'_*𝒪_X` read on global functions

Let `f' : X ⟶ Y'` be a morphism of algebraic spaces whose structure map `𝒪_{Y'} ⟶ f'_*𝒪_X`
(Stacks 03G8) is an isomorphism.  Then for every étale chart `c : V ⟶ Y'` from an object of the
site and every cartesian square `P = X ×_{Y'} V`, pulling back regular functions along the
projection `P ⟶ V` is a bijection `Γ(V, 𝒪) ≅ Γ(P, 𝒪)`.  This is the form in which the proof of
Stacks 0E0D consumes the hypothesis that `X ⟶ Y'` is the first factor of the Stein
factorization.

## Main results

* `AlgebraicGeometry.Space.ProperFlatStein.bijective_pullbackToGlobalFunctions_comp_iso`:
  bijectivity of pulling back global functions is invariant under an isomorphism of the source
  over the target.
* `AlgebraicGeometry.Space.ProperFlatStein.bijective_pullbackToGlobalFunctions_of_isIso_fSharp`:
  the statement above.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0E0D](https://stacks.math.columbia.edu/tag/0E0D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.ProperFlatStein

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pulling back global functions along `e ≫ g` with `e` an isomorphism of algebraic spaces is
bijective exactly when pulling back along `g` is. -/
theorem bijective_pullbackToGlobalFunctions_comp_iso {P Q : AlgebraicSpaces B S hS}
    (e : P ≅ Q) {T : BigFppfOver B S hS} (g : Q ⟶ schemeSpace T) :
    Function.Bijective (pullbackToGlobalFunctions B S hS P T (e.hom ≫ g)) ↔
      Function.Bijective (pullbackToGlobalFunctions B S hS Q T g) := by
  have key : ∀ {R : AlgebraicSpaces B S hS} (k : R ⟶ schemeSpace T),
      pullbackToGlobalFunctions B S hS R T k = (globalFunctionsMap B S hS k).comp
        (reprGlobalFunctionsEquiv B S hS T).symm.toRingHom :=
    fun k => pullbackToGlobalFunctions_eq B S hS _ T k
  rw [key, key, globalFunctionsMap_comp]
  exact (bijective_globalFunctionsMap_of_isIso B S hS e).of_comp_iff'
    ⇑((globalFunctionsMap B S hS g).comp (reprGlobalFunctionsEquiv B S hS T).symm.toRingHom)

/-- **`𝒪_{Y'} = f'_*𝒪_X` on global functions, from bijectivity on sections.**  If the structure
map of `f' : X ⟶ Y'` is bijective on the sections over every étale chart, then for every étale
chart `c : V ⟶ Y'` and every cartesian square `P = X ×_{Y'} V`, the regular functions on `V`
are the global functions on `P`. -/
theorem bijective_pullbackToGlobalFunctions_of_bijective_fSharp_app
    {X Y' : AlgebraicSpaces B S hS} (f' : X ⟶ Y')
    (hA' : ∀ W : SmallEtale B S hS Y'.1,
      Function.Bijective ((smallEtaleRingedToposHom B S hS f').fSharp.hom.app (op W)).hom)
    (V : BigFppfOver B S hS) (c : yoneda.obj V ⟶ Y'.1)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (a : P ⟶ X.1) (b : P ⟶ yoneda.obj V) (sq : IsPullback a b f'.hom c) :
    Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ V
      (ObjectProperty.homMk b)) := by
  let Vs : SmallEtale B S hS Y'.1 := chartFromEtaleHom B S hS Y' V c hc
  let proj := chartBaseChangeProjection B S hS f' Vs
  have hcomp : ∀ r, directImageSectionsToGlobalFunctions B S hS f' Vs
      ((smallEtaleRingedToposHom B S hS f').fSharp.hom.app (op Vs) r) =
      pullbackToGlobalFunctions B S hS (chartBaseChangeSpace B S hS f' Vs) V
        (ObjectProperty.homMk proj.hom) r := by
    intro r
    refine Subtype.ext (funext fun c' => ?_)
    have h1 : ((smallEtaleRingedToposHom B S hS f').fSharp.hom.app (op Vs)).hom r =
        (pushforwardAlgebra B S hS (Over.mk f')).algebraMap (op Vs) r :=
      (congrArg (fun φ : (structureSheaf B S hS Y'.1 Y'.2).obj.obj (op Vs) →+*
          (pushforwardAlgebra B S hS (Over.mk f')).right.obj.obj (op Vs) => φ r)
        (pushforwardAlgebra_algebraMap B S hS (Over.mk f') (op Vs))).symm
    show (directImageSectionsToGlobalFunctions B S hS f' Vs
      (((smallEtaleRingedToposHom B S hS f').fSharp.hom.app (op Vs)).hom r)).val c' = _
    rw [h1, directImageSectionsToGlobalFunctions_algebraMap]
    rfl
  have hbij : Function.Bijective (pullbackToGlobalFunctions B S hS
      (chartBaseChangeSpace B S hS f' Vs) V (ObjectProperty.homMk proj.hom)) := by
    rw [show (pullbackToGlobalFunctions B S hS (chartBaseChangeSpace B S hS f' Vs) V
        (ObjectProperty.homMk proj.hom) : _ → _) =
        directImageSectionsToGlobalFunctions B S hS f' Vs ∘
          ((smallEtaleRingedToposHom B S hS f').fSharp.hom.app (op Vs)).hom from
      funext fun r => (hcomp r).symm]
    exact (bijective_directImageSectionsToGlobalFunctions B S hS f' Vs).comp (hA' Vs)
  have sqC := isPullback_chartBaseChangeProjection B S hS f' Vs
  let e : P ≅ (chartBaseChangeSpace B S hS f' Vs).obj := sq.flip.isoIsPullback _ _ sqC
  let eA : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ≅ chartBaseChangeSpace B S hS f' Vs :=
    (ObjectProperty.fullyFaithfulι _).preimageIso e
  have hfac : (ObjectProperty.homMk b : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace V) =
      eA.hom ≫ ObjectProperty.homMk proj.hom := by
    apply ObjectProperty.hom_ext
    exact (sq.flip.isoIsPullback_hom_fst _ _ sqC).symm
  rw [hfac]
  exact (bijective_pullbackToGlobalFunctions_comp_iso B S hS eA _).2 hbij

/-- **`𝒪_{Y'} = f'_*𝒪_X` on global functions.**  If the structure map of `f' : X ⟶ Y'` is an
isomorphism, then for every étale chart `c : V ⟶ Y'` and every cartesian square
`P = X ×_{Y'} V`, the regular functions on `V` are the global functions on `P`. -/
theorem bijective_pullbackToGlobalFunctions_of_isIso_fSharp {X Y' : AlgebraicSpaces B S hS}
    (f' : X ⟶ Y') (hiso : IsIso (smallEtaleRingedToposHom B S hS f').fSharp)
    (V : BigFppfOver B S hS) (c : yoneda.obj V ⟶ Y'.1)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (a : P ⟶ X.1) (b : P ⟶ yoneda.obj V) (sq : IsPullback a b f'.hom c) :
    Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ V
      (ObjectProperty.homMk b)) :=
  bijective_pullbackToGlobalFunctions_of_bijective_fSharp_app B S hS f'
    (fun _ => (ConcreteCategory.isIso_iff_bijective _).1 inferInstance) V c hc hP a b sq

/-- **The same, from the structure map of sheaves of rings.**  If the structure map
`f'♯ : 𝒪_{Y'} ⟶ f'_*𝒪_X` of Stacks 03G8, read as a morphism of sheaves of rings
(`AlgebraicGeometry.Space.structureSharp`), is an isomorphism, then for every étale chart
`c : V ⟶ Y'` and every cartesian square `P = X ×_{Y'} V`, the regular functions on `V` are the
global functions on `P`. -/
theorem bijective_pullbackToGlobalFunctions_of_isIso_structureSharp
    {X Y' : AlgebraicSpaces B S hS}
    (f' : X ⟶ Y') (hiso : IsIso (structureSharp B S hS f'))
    (V : BigFppfOver B S hS) (c : yoneda.obj V ⟶ Y'.1)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (a : P ⟶ X.1) (b : P ⟶ yoneda.obj V) (sq : IsPullback a b f'.hom c) :
    Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ V
      (ObjectProperty.homMk b)) := by
  refine bijective_pullbackToGlobalFunctions_of_bijective_fSharp_app B S hS f' (fun W => ?_)
    V c hc hP a b sq
  rw [show ⇑((smallEtaleRingedToposHom B S hS f').fSharp.hom.app (op W)).hom =
      ⇑((structureSharp B S hS f').hom.app (op W)).hom from
    funext fun r => fSharp_app_apply B S hS f' (op W) r]
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

end AlgebraicGeometry.Space.ProperFlatStein

end
