module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Morphisms of quasi-coherent modules on an affine scheme are their maps on global sections

On an affine scheme `X` the global sections functor is fully faithful on quasi-coherent sheaves
of modules: a morphism `F ⟶ G` is determined by the `Γ(X, ⊤)`-linear map `Γ(F, ⊤) → Γ(G, ⊤)` it
induces, and every such linear map arises this way.  Mathlib has this for `X = Spec R` in the
form of the equivalence `AlgebraicGeometry.tildeEquiv`; what this file adds is the elementwise
reading of that equivalence and the passage from `Spec Γ(X, ⊤)` to an abstract affine scheme `X`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.moduleSpec_hom_ext` and
  `...moduleSpec_exists_hom`: faithfulness and fullness of `Γ(-, ⊤)` on quasi-coherent modules
  over `Spec R`, read on elements.
* `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top`: two morphisms of quasi-coherent
  sheaves of modules on an affine scheme which agree on global sections are equal.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq`: every `Γ(X, ⊤)`-linear map
  between the global sections of two quasi-coherent sheaves of modules on an affine scheme is
  the action on global sections of a morphism of sheaves of modules.

## Implementation notes

The `Spec R` case is `AlgebraicGeometry.tildeEquiv`, whose inverse is
`CategoryTheory.ObjectProperty.ι _ ⋙ AlgebraicGeometry.moduleSpecΓFunctor`; since an
equivalence's inverse is fully faithful, injectivity and surjectivity on morphisms are
`CategoryTheory.Functor.map_injective` and `CategoryTheory.Functor.map_surjective` for it.  Two
small facts make that usable elementwise: that the inverse's action on a morphism of the full
subcategory *is* `moduleSpecΓFunctor.map` (`rfl`), and that
`moduleSpecΓFunctor.obj A` is `ModuleCat.of R Γ(A, ⊤)` (also `rfl`).  The second has to be given
as a type ascription rather than left to unification: elaborating `ModuleCat.ofHom` against the
expected type `moduleSpecΓFunctor.obj A ⟶ moduleSpecΓFunctor.obj B` unfolds the object and then
looks for the module structure on the unfolded carrier, which instance search does not find.

The passage to an abstract affine scheme `X` goes through
`(AlgebraicGeometry.isAffineOpen_top X).fromSpec`, which is an isomorphism, so restriction along
it is an equivalence of module categories and in particular fully faithful.  The comparison of
global sections is `AlgebraicGeometry.affineSectionsLinearEquiv`, which already carries the
`Γ(X, ⊤)`-linearity — the content there being that the scalars are transported along
`AlgebraicGeometry.Scheme.ΓSpecIso`.  Its naturality in the module is proved here; it reduces to
`Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map` because
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl` and morphisms of
`TopologicalSpace.Opens X` between fixed opens are unique.

## References

* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### The spectrum of a ring -/

section Spec

variable {R : CommRingCat.{u}}

/-- The inverse of `AlgebraicGeometry.tildeEquiv` acts on morphisms by
`AlgebraicGeometry.moduleSpecΓFunctor`. -/
theorem tildeEquiv_inverse_map {A B : (Spec R).Modules}
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) (ψ : A ⟶ B) :
    (tildeEquiv (R := R)).inverse.map
        (ObjectProperty.homMk (X := (⟨A, hA⟩ :
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory))
          (Y := ⟨B, hB⟩) ψ) = moduleSpecΓFunctor.map ψ := rfl

/-- `AlgebraicGeometry.moduleSpecΓFunctor` acts on a morphism by its action on global
sections. -/
theorem moduleSpecΓFunctor_map_apply {A B : (Spec R).Modules} (ψ : A ⟶ B)
    (a : moduleSpecΓFunctor.obj A) : moduleSpecΓFunctor.map ψ a = ψ.app ⊤ a := rfl

/-- `AlgebraicGeometry.moduleSpecΓFunctor` sends a module to its global sections. -/
theorem moduleSpecΓFunctor_obj {A : (Spec R).Modules} :
    moduleSpecΓFunctor.obj A = ModuleCat.of R ↑Γ(A, ⊤) := rfl

/-- A quasi-coherent sheaf of modules on `Spec R`, as an object of the full subcategory. -/
private abbrev qcObj {A : (Spec R).Modules} (hA : A.IsQuasicoherent) :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory := ⟨A, hA⟩

/-- **Faithfulness of global sections on a spectrum.** Two morphisms of quasi-coherent sheaves
of modules on `Spec R` which agree on global sections are equal. -/
theorem moduleSpec_hom_ext {A B : (Spec R).Modules}
    [hA : A.IsQuasicoherent] [hB : B.IsQuasicoherent] {ψ ψ' : A ⟶ B}
    (h : ∀ a : Γ(A, ⊤), ψ.app ⊤ a = ψ'.app ⊤ a) : ψ = ψ' := by
  refine congrArg (fun k => k.hom) (Functor.map_injective (tildeEquiv (R := R)).inverse
    (a₁ := ObjectProperty.homMk (X := qcObj hA) (Y := qcObj hB) ψ)
    (a₂ := ObjectProperty.homMk (X := qcObj hA) (Y := qcObj hB) ψ')
    (by
      rw [tildeEquiv_inverse_map, tildeEquiv_inverse_map]
      exact ModuleCat.hom_ext (LinearMap.ext h)))

/-- **Fullness of global sections on a spectrum.** Every `R`-linear map between the global
sections of two quasi-coherent sheaves of modules on `Spec R` is the action on global sections
of a morphism of sheaves of modules. -/
theorem moduleSpec_exists_hom {A B : (Spec R).Modules}
    [hA : A.IsQuasicoherent] [hB : B.IsQuasicoherent] (v : ↑Γ(A, ⊤) →ₗ[R] ↑Γ(B, ⊤)) :
    ∃ ψ : A ⟶ B, ∀ a : Γ(A, ⊤), ψ.app ⊤ a = v a := by
  let v' : moduleSpecΓFunctor.obj A ⟶ moduleSpecΓFunctor.obj B :=
    (ModuleCat.ofHom v : ModuleCat.of R ↑Γ(A, ⊤) ⟶ ModuleCat.of R ↑Γ(B, ⊤))
  obtain ⟨ψ, hψ⟩ := Functor.map_surjective (tildeEquiv (R := R)).inverse
    (X := qcObj hA) (Y := qcObj hB) v'
  exact ⟨ψ.hom, fun a =>
    congrArg (fun k : moduleSpecΓFunctor.obj A ⟶ moduleSpecΓFunctor.obj B => k.hom a) hψ⟩

end Spec

/-! ### An arbitrary affine scheme -/

section Affine

variable {X : Scheme.{u}} [IsAffine X]

/-- For an affine scheme `X`, the canonical morphism `Spec Γ(X, ⊤) ⟶ X` is an isomorphism. -/
instance isIso_fromSpec_top : IsIso (isAffineOpen_top X).fromSpec := by
  have : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact inferInstanceAs (IsIso ((isAffineOpen_top X).isoSpec.inv ≫ (⊤ : X.Opens).ι))

/-- The image of `Spec Γ(X, ⊤)` under the canonical morphism to the affine scheme `X` is all
of `X`. -/
theorem image_top_fromSpec :
    (isAffineOpen_top X).fromSpec ''ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens) = ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, IsAffineOpen.opensRange_fromSpec]

/-- Restriction of sheaves of modules along an isomorphism of schemes is faithful. -/
noncomputable instance restrictFaithful {Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] :
    (Scheme.Modules.restrictFunctor f).Faithful := by
  have : IsOpenImmersion f := inferInstance
  exact Functor.Faithful.of_iso (F := Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback f).symm

/-- Restriction of sheaves of modules along an isomorphism of schemes is full. -/
noncomputable instance restrictFull {Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] :
    (Scheme.Modules.restrictFunctor f).Full := by
  have : IsOpenImmersion f := inferInstance
  exact Functor.Full.of_iso (F := Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback f).symm

omit [IsAffine X] in
/-- Naturality of `AlgebraicGeometry.affineSectionsIso` in the module. -/
theorem affineSectionsIso_naturality {F G : X.Modules} (χ : F ⟶ G) {U : X.Opens}
    (hU : IsAffineOpen U) (a : Γ(F.restrict hU.fromSpec, ⊤)) :
    (affineSectionsIso G hU).hom (((Scheme.Modules.restrictFunctor hU.fromSpec).map χ).app ⊤ a)
      = χ.app U ((affineSectionsIso F hU).hom a) := by
  have he : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have e1 : ∀ (M : X.Modules) (m : Γ(M.restrict hU.fromSpec, ⊤)),
      (affineSectionsIso M hU).hom m
        = M.presheaf.map (homOfLE he.ge).op (show Γ(M, hU.fromSpec ''ᵁ ⊤) from m) := by
    intro M m
    change M.presheaf.map _ ((M.restrictAppIso hU.fromSpec ⊤).hom m) = _
    rw [Scheme.Modules.restrictAppIso]
    congr 1
  rw [e1, e1]
  exact Hom_app_presheaf_map χ he.ge _

/-- **Faithfulness of global sections on an affine scheme.** Two morphisms of quasi-coherent
sheaves of modules on an affine scheme which agree on global sections are equal. -/
theorem hom_ext_of_app_top {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    {χ χ' : F ⟶ G} (h : ∀ a : Γ(F, ⊤), χ.app ⊤ a = χ'.app ⊤ a) : χ = χ' := by
  have hqF := Scheme.Modules.isQuasicoherent_restrictFunctor (isAffineOpen_top X).fromSpec F
  have hqG := Scheme.Modules.isQuasicoherent_restrictFunctor (isAffineOpen_top X).fromSpec G
  refine Functor.map_injective (Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec) ?_
  refine moduleSpec_hom_ext (hA := hqF) (hB := hqG) (fun a => ?_)
  refine (ConcreteCategory.bijective_of_isIso
    (affineSectionsIso G (isAffineOpen_top X)).hom).injective ?_
  rw [affineSectionsIso_naturality χ (isAffineOpen_top X) a,
    affineSectionsIso_naturality χ' (isAffineOpen_top X) a, h]

/-- **Fullness of global sections on an affine scheme.** Every `Γ(X, ⊤)`-linear map between the
global sections of two quasi-coherent sheaves of modules on an affine scheme is the action on
global sections of a morphism of sheaves of modules. -/
theorem exists_hom_app_top_eq {F G : X.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] (w : ↑Γ(F, ⊤) →ₗ[Γ(X, ⊤)] ↑Γ(G, ⊤)) :
    ∃ χ : F ⟶ G, ∀ a : Γ(F, ⊤), χ.app ⊤ a = w a := by
  have hqF := Scheme.Modules.isQuasicoherent_restrictFunctor (isAffineOpen_top X).fromSpec F
  have hqG := Scheme.Modules.isQuasicoherent_restrictFunctor (isAffineOpen_top X).fromSpec G
  set eF := affineSectionsLinearEquiv F (isAffineOpen_top X) with heF
  set eG := affineSectionsLinearEquiv G (isAffineOpen_top X) with heG
  obtain ⟨ψ, hψ⟩ := moduleSpec_exists_hom (hA := hqF) (hB := hqG)
    (eG.symm.toLinearMap ∘ₗ w ∘ₗ eF.toLinearMap)
  obtain ⟨χ, hχ⟩ := Functor.Full.map_surjective
    (F := Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec) ψ
  refine ⟨χ, fun a => ?_⟩
  have hnat := affineSectionsIso_naturality χ (isAffineOpen_top X) (eF.symm a)
  rw [hχ, hψ] at hnat
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hnat
  rw [← affineSectionsLinearEquiv_apply, ← affineSectionsLinearEquiv_apply, ← heF, ← heG,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hnat
  exact hnat.symm

end Affine

end Stacks.AlgebraicGeometry.ModuleLimits

end
