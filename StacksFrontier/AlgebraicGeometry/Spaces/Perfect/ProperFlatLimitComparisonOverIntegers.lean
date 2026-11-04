module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectDescentOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickenedBasePushoutQcqs

/-!
# Stacks 0D3F: the limit comparison `𝒪_X ⊗_R lim M_n ⟶ lim 𝒪_X ⊗_R M_n` under `DQ_X`

Let `f : X ⟶ T` be proper, flat and of finite presentation with `T` affine and `R = Γ(T, 𝒪_T)`,
and let `(M_n)` be an inverse system of `R`-modules with surjective transition maps. The two
forms of the limit comparison in `AlgebraicGeometry.Space.ProperFlatLimitComparison` take the
descent of perfect objects along approximating systems as a hypothesis `hdescent`; it is
`AlgebraicGeometry.Space.perfectObjectsDescend_overIntegers`. This file records both forms
without it, and Stacks 0D3F itself: the canonical map induces an isomorphism from
`𝒪_X ⊗_R lim M_n` to `DQ_X(lim 𝒪_X ⊗_R M_n)`.

## Main results

* `bijective_comp_single_limitComparison_baseRingTensorModule_of_isProper_unconditional`:
  composition with `𝒪_X ⊗_R lim M_n ⟶ lim 𝒪_X ⊗_R M_n` in degree zero is bijective on maps out
  of every object of `D_QCoh(𝒪_X)`.
* `isIso_coherator_map_single_limitComparison_of_isProper_unconditional`: `DQ_X` inverts that
  map.
* `isIso_homEquiv_single_limitComparison_baseRingTensorModule_of_isProper`: the canonical map
  induces an isomorphism `𝒪_X ⊗_R lim M_n ⟶ DQ_X(lim 𝒪_X ⊗_R M_n)`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
-/

@[expose] public noncomputable section

-- The derived categories here are those of the standard model
-- `CategoryTheory.HasDerivedCategory.standard`, supplied by `letI` inside the statements and the
-- proofs rather than as a local instance.

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- **The canonical map of Stacks 0D3F, for `f` proper, flat and of finite presentation.** Let
`f : X ⟶ T` be proper, flat and of finite presentation over an affine `T` with `R = Γ(T, 𝒪_T)`,
and let `(M_n)` be an inverse system of `R`-modules with surjective transition maps. Composition
with the canonical map `𝒪_X ⊗_R lim M_n ⟶ lim 𝒪_X ⊗_R M_n`, placed in degree zero, is bijective
on maps out of every object of `D_QCoh(𝒪_X)`:
`AlgebraicGeometry.Space.bijective_comp_single_limitComparison_baseRingTensorModule_of_isProper`
with the descent of perfect objects
`AlgebraicGeometry.Space.perfectObjectsDescend_overIntegers`. -/
theorem bijective_comp_single_limitComparison_baseRingTensorModule_of_isProper_unconditional
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ =>
      (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (Msys.obj ⟨n⟩)]
    [HasLimit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f))] :
    letI : ∀ (C : Type (u + 1)) [Category.{u + 1} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
      fun C _ _ => HasDerivedCategory.standard C
    ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), qcohDerivedProp B S hS X E →
      Function.Bijective
        (fun a : E ⟶ (DerivedCategory.singleFunctor _ 0).obj
            ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (limit Msys)) =>
          a ≫ (DerivedCategory.singleFunctor _ 0).map
            (limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f)))) :=
  fun E hE => bijective_comp_single_limitComparison_baseRingTensorModule_of_isProper
    B.contains_terminal (perfectObjectsDescend_overIntegers B.contains_terminal) f hf hflat hfp hT
    Msys hsurj E hE

/-- **`DQ_X` inverts the canonical map of Stacks 0D3F, for `f` proper, flat and of finite
presentation.** Let `f : X ⟶ T` be proper, flat and of finite presentation over an affine `T`, and
let `(M_n)` be an inverse system of `Γ(T, 𝒪_T)`-modules with surjective transition maps. If
`φ : 𝒢 ⟶ 𝒩` is, up to isomorphisms `𝒢 ≅ 𝒪_X ⊗ lim M_n` and `lim 𝒪_X ⊗ M_n ≅ 𝒩`, the canonical
map `𝒪_X ⊗ lim M_n ⟶ lim 𝒪_X ⊗ M_n`, then `DQ_X` applied to `φ` in degree zero is an
isomorphism: `AlgebraicGeometry.Space.isIso_coherator_map_single_limitComparison_of_isProper` with
the descent of perfect objects `AlgebraicGeometry.Space.perfectObjectsDescend_overIntegers`. -/
theorem isIso_coherator_map_single_limitComparison_of_isProper_unconditional
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ =>
      (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (Msys.obj ⟨n⟩)]
    [HasLimit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f))]
    {G N : Modules.{u, u} B S hS X.1 X.2} (φ : G ⟶ N)
    (α : G ≅ (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (limit Msys))
    (β : limit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f)) ≅ N)
    (hφ : φ = α.hom ≫ limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f)) ≫
      β.hom) :
    letI : ∀ (C : Type (u + 1)) [Category.{u + 1} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
      fun C _ _ => HasDerivedCategory.standard C
    letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS B.contains_terminal X.1 X.2
      (qcqs_of_isFinitePresentation_schemeSpace B.contains_terminal f hT hfp).1
      (qcqs_of_isFinitePresentation_schemeSpace B.contains_terminal f hT hfp).2
    IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)) :=
  isIso_coherator_map_single_limitComparison_of_isProper B.contains_terminal
    (perfectObjectsDescend_overIntegers B.contains_terminal) f hf hflat hfp hT Msys hsurj φ α β hφ

/-- Let `f : X ⟶ T` be proper, flat and of finite presentation, with `T` affine and
`R = Γ(T, 𝒪_T)`, and let `(M_n)` be an inverse system of `R`-modules with surjective transition
maps. Then the canonical map `𝒪_X ⊗_R lim M_n ⟶ lim 𝒪_X ⊗_R M_n` induces an isomorphism from
the source, an object of `D_QCoh(𝒪_X)`, to `DQ_X` applied to the target: the morphism
`𝒪_X ⊗_R lim M_n ⟶ DQ_X(lim 𝒪_X ⊗_R M_n)` corresponding to it under the adjunction
`D_QCoh(𝒪_X) ⇄ D(𝒪_X)` of Stacks 0CR4 (both modules placed in degree zero) is an isomorphism.

The source's `Spec(R)` is the affine object `T` of the site with `R = Γ(T, 𝒪_T)`. -/
@[stacks 0D3F "`Spec(R)` is an affine object `T` of the site, with `R = Γ(T, 𝒪_T)`."]
theorem isIso_homEquiv_single_limitComparison_baseRingTensorModule_of_isProper
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op)) :
    letI : ∀ (C : Type (u + 1)) [Category.{u + 1} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
      fun C _ _ => HasDerivedCategory.standard C
    letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS B.contains_terminal X.1 X.2
      (qcqs_of_isFinitePresentation_schemeSpace B.contains_terminal f hT hfp).1
      (qcqs_of_isFinitePresentation_schemeSpace B.contains_terminal f hT hfp).2
    IsIso ((Adjunction.ofIsLeftAdjoint (qcohDerivedProp B S hS X).ι).homEquiv
      ⟨(DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (limit Msys)),
        qcohDerivedProp_singleFunctor_obj B S hS _
          (isQuasicoherentOnSite_baseRingTensorModule B S hS X _ _)⟩
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
        (limit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f))))
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map
        (limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f))))) :=
  let : ∀ (C : Type (u + 1)) [Category.{u + 1} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
    fun C _ _ => HasDerivedCategory.standard C
  let := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS B.contains_terminal X.1 X.2
    (qcqs_of_isFinitePresentation_schemeSpace B.contains_terminal f hT hfp).1
    (qcqs_of_isFinitePresentation_schemeSpace B.contains_terminal f hT hfp).2
  have := isIso_coherator_map_single_limitComparison_of_isProper_unconditional f hf hflat hfp hT
    Msys hsurj (limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f)))
    (Iso.refl _) (Iso.refl _) (by simp)
  by rw [Adjunction.homEquiv_unit]; infer_instance

end AlgebraicGeometry.Space

end
