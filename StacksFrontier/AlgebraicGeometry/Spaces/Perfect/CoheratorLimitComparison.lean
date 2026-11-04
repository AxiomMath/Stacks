module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointProducts

/-!
# `DQ_X` inverts the canonical map of Stacks 0D3F

Let `f : X ⟶ T` be flat and of finite presentation over an affine `T`, `R = Γ(T, 𝒪_T)`, and let
`(M_n)` be an inverse system of `R`-modules with surjective transition maps. The headline of
[Stacks Project, Tag 0D3F] is that `𝒪_X ⊗_R lim M_n ⟶ lim 𝒪_X ⊗_R M_n` induces an isomorphism
after applying the derived coherator `DQ_X` (the right adjoint of `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`,
Stacks 0CR4). The lemma (in `AlgebraicGeometry`)
`Space.bijective_comp_single_limitComparison_baseRingTensorModule_of_isPerfect_derivedPushforward`
proves the source's rereading of it (bijectivity of composition on maps out of `D_QCoh(𝒪_X)`)
from perfectness of `RΓ(X, -)` (Stacks 0CTM). This file turns that rereading into the
invertibility of `DQ_X` applied to the map, and into the invertibility of `DQ_X` applied to any
map of modules identified with it, which is the form the body of the proof of
[Stacks Project, Tag 0D3X] uses (the `hDQ` input of 0D3Q).

## Main results

* `CategoryTheory.Adjunction.isIso_map_of_bijective_comp_obj`: for `ι ⊣ DQ`, `DQ.map g` is
  invertible once composition with `g` is bijective on morphisms out of every `ι.obj E`.
* `AlgebraicGeometry.Space.isIso_coherator_map_single_of_eq_limitComparison`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- **A right adjoint inverts a morphism on which composition is bijective from the left
adjoint's image.** For `ι ⊣ DQ` and `g : X ⟶ Y`, if composition with `g` is bijective on
morphisms `ι.obj E ⟶ X` for every `E`, then `DQ.map g` is an isomorphism: by the adjunction,
composition with `DQ.map g` on morphisms `E ⟶ DQ.obj X` is composition with `g`. -/
theorem isIso_map_of_bijective_comp_obj {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟]
    {ι : 𝒞 ⥤ 𝒟} {DQ : 𝒟 ⥤ 𝒞} (adj : ι ⊣ DQ) {X Y : 𝒟} (g : X ⟶ Y)
    (h : ∀ E : 𝒞, Function.Bijective (fun a : ι.obj E ⟶ X => a ≫ g)) : IsIso (DQ.map g) := by
  refine isIso_of_yoneda_map_bijective _ fun E => ?_
  have hcomp : (fun a' : E ⟶ DQ.obj X => a' ≫ DQ.map g) =
      (adj.homEquiv E Y) ∘ ((fun a : ι.obj E ⟶ X => a ≫ g) ∘ (adj.homEquiv E X).symm) := by
    funext a'
    exact (Equiv.symm_apply_eq _).1 (adj.homEquiv_naturality_right_symm a' g)
  rw [hcomp]
  exact (adj.homEquiv E Y).bijective.comp ((h E).comp (adj.homEquiv E X).symm.bijective)

end CategoryTheory.Adjunction

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- **`DQ_X` inverts every map of modules identified with the canonical map of Stacks 0D3F.**
Let `f : X ⟶ T` be flat and of finite presentation over an affine `T`, with `X` quasi-compact and
quasi-separated, let `(M_n)` be an inverse system of `Γ(T, 𝒪_T)`-modules with surjective
transition maps, and suppose `RΓ(X, -)`, read on the spaces-étale model, carries perfect objects to
perfect objects. If `φ : 𝒢 ⟶ 𝒩` is, up to isomorphisms `𝒢 ≅ 𝒪_X ⊗ lim M_n` and
`lim 𝒪_X ⊗ M_n ≅ 𝒩`, the canonical map `𝒪_X ⊗ lim M_n ⟶ lim 𝒪_X ⊗ M_n`, then `DQ_X` applied to
`φ` in degree zero is an isomorphism. -/
theorem isIso_coherator_map_single_of_eq_limitComparison (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXc : IsQuasiCompactSpace B S hS X.1) (hXs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ =>
      (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (Msys.obj ⟨n⟩)]
    [HasLimit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f))]
    (hpush : ∀ K, (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect K →
      (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj K))
    {G N : Modules.{u, u} B S hS X.1 X.2} (φ : G ⟶ N)
    (α : G ≅ (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (limit Msys))
    (β : limit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f)) ≅ N)
    (hφ : φ = α.hom ≫ limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f)) ≫
      β.hom) :
    letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
    IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)) := by
  let := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
  have : IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map
        (limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f))))) :=
    (Adjunction.ofIsLeftAdjoint (qcohDerivedProp B S hS X).ι).isIso_map_of_bijective_comp_obj _
      fun E =>
        bijective_comp_single_limitComparison_baseRingTensorModule_of_isPerfect_derivedPushforward
          hZ f hflat hfp hT Msys hsurj hpush E.obj E.property
  subst hφ
  simp only [Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Space

end
