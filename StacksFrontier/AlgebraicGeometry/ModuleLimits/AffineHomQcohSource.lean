module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom

/-!
# Global sections is fully faithful out of a quasi-coherent module on a spectrum

Let `F` be a quasi-coherent sheaf of modules on `Spec R` and `G` an arbitrary sheaf of modules on
`Spec R`. For every `R`-linear map `v : Γ(F, ⊤) → Γ(G, ⊤)` there is exactly one `χ : F ⟶ G`
acting as `v` on global sections. The same holds for morphisms of restrictions along an open
immersion `Spec R ⟶ Y` out of a quasi-coherent sheaf of modules on `Y`.

## Main definitions

* `moduleSpecHomOfΓMap`: the morphism of sheaves of modules on `Spec R` out of a quasi-coherent
  one determined by a map of global sections.
* `restrictHomOfΓMap`: the morphism of restrictions along an open immersion `Spec R ⟶ Y`
  determined by a map of the sections over the image.

## Main results

* `moduleSpecΓFunctor_map_moduleSpecHomOfΓMap` and `moduleSpecHomOfΓMap_app_top`: the morphism
  `moduleSpecHomOfΓMap v` acts on global sections as `v`.
* `moduleSpec_hom_ext_of_isQuasicoherent_source` and
  `moduleSpec_hom_ext_app_top_of_isQuasicoherent_source`: two morphisms out of a quasi-coherent
  sheaf of modules on `Spec R` agreeing on global sections are equal.
* `existsUnique_hom_app_top_eq_of_isQuasicoherent_source`: every map of global sections out of a
  quasi-coherent sheaf of modules on `Spec R` is the action of exactly one morphism.
* `existsUnique_restrictHom_app_top_eq`, `restrictHomOfΓMap_app_top` and
  `restrict_hom_ext_app_top`: the same for morphisms of restrictions along an open immersion out
  of a spectrum, the source being quasi-coherent.

## References

* [Stacks Project, Tag 01I6](https://stacks.math.columbia.edu/tag/01I6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.AlgebraicGeometry.ModuleLimits

universe u

variable {R : CommRingCat.{u}} {F G : (Spec R).Modules}

/-- The counit of `AlgebraicGeometry.tilde.adjunction` at a quasi-coherent sheaf of modules on a
spectrum is invertible. -/
theorem isIso_tildeAdjunction_counit_app [F.IsQuasicoherent] :
    IsIso ((tilde.adjunction (R := R)).counit.app F) :=
  (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ F).mp inferInstance

/-- The morphism `F ⟶ G` of sheaves of modules on `Spec R`, for `F` quasi-coherent, acting on
global sections as the `R`-linear map `v : Γ(F, ⊤) ⟶ Γ(G, ⊤)`: the inverse of the counit of
`AlgebraicGeometry.tilde.adjunction` at `F` followed by the inverse adjoint transpose of `v`. -/
def moduleSpecHomOfΓMap [F.IsQuasicoherent]
    (v : moduleSpecΓFunctor.obj F ⟶ moduleSpecΓFunctor.obj G) : F ⟶ G :=
  haveI := isIso_tildeAdjunction_counit_app (F := F)
  inv ((tilde.adjunction (R := R)).counit.app F) ≫
    ((tilde.adjunction (R := R)).homEquiv (moduleSpecΓFunctor.obj F) G).symm v

/-- `Stacks.AlgebraicGeometry.ModuleLimits.moduleSpecHomOfΓMap v` acts on global sections as
`v`. -/
theorem moduleSpecΓFunctor_map_moduleSpecHomOfΓMap [F.IsQuasicoherent]
    (v : moduleSpecΓFunctor.obj F ⟶ moduleSpecΓFunctor.obj G) :
    moduleSpecΓFunctor.map (moduleSpecHomOfΓMap v) = v := by
  have := isIso_tildeAdjunction_counit_app (F := F)
  rw [moduleSpecHomOfΓMap, Functor.map_comp, Functor.map_inv,
    IsIso.inv_eq_of_inv_hom_id ((tilde.adjunction (R := R)).right_triangle_components F)]
  exact ((tilde.adjunction (R := R)).homEquiv_unit (moduleSpecΓFunctor.obj F) G
    (((tilde.adjunction (R := R)).homEquiv (moduleSpecΓFunctor.obj F) G).symm v)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- `Stacks.AlgebraicGeometry.ModuleLimits.moduleSpecHomOfΓMap v` acts on a global section as
`v` does. -/
theorem moduleSpecHomOfΓMap_app_top [F.IsQuasicoherent]
    (v : moduleSpecΓFunctor.obj F ⟶ moduleSpecΓFunctor.obj G) (a : Γ(F, ⊤)) :
    (moduleSpecHomOfΓMap v).app ⊤ a = v.hom a :=
  congrArg (fun k : moduleSpecΓFunctor.obj F ⟶ moduleSpecΓFunctor.obj G => k.hom a)
    (moduleSpecΓFunctor_map_moduleSpecHomOfΓMap v)

/-- Two morphisms out of a quasi-coherent sheaf of modules on `Spec R` with the same image under
`AlgebraicGeometry.moduleSpecΓFunctor` are equal. -/
theorem moduleSpec_hom_ext_of_isQuasicoherent_source [F.IsQuasicoherent] {χ χ' : F ⟶ G}
    (h : moduleSpecΓFunctor.map χ = moduleSpecΓFunctor.map χ') : χ = χ' := by
  have := isIso_tildeAdjunction_counit_app (F := F)
  refine (cancel_epi ((tilde.adjunction (R := R)).counit.app F)).mp ?_
  refine ((tilde.adjunction (R := R)).homEquiv (moduleSpecΓFunctor.obj F) G).injective ?_
  rw [(tilde.adjunction (R := R)).homEquiv_unit, (tilde.adjunction (R := R)).homEquiv_unit,
    Functor.map_comp, Functor.map_comp, h]

/-- Two morphisms out of a quasi-coherent sheaf of modules on `Spec R` agreeing on every global
section are equal. -/
theorem moduleSpec_hom_ext_app_top_of_isQuasicoherent_source [F.IsQuasicoherent] {χ χ' : F ⟶ G}
    (h : ∀ a : Γ(F, ⊤), χ.app ⊤ a = χ'.app ⊤ a) : χ = χ' :=
  moduleSpec_hom_ext_of_isQuasicoherent_source
    (ModuleCat.hom_ext (LinearMap.ext fun a => h a))

/-- Every `R`-linear map from `Γ(F, ⊤)` to `Γ(G, ⊤)`, with `F` quasi-coherent and `G` an arbitrary
sheaf of modules on `Spec R`, is the action on global sections of exactly one morphism
`F ⟶ G`. -/
theorem existsUnique_hom_app_top_eq_of_isQuasicoherent_source [F.IsQuasicoherent]
    (v : moduleSpecΓFunctor.obj F ⟶ moduleSpecΓFunctor.obj G) :
    ∃! χ : F ⟶ G, ∀ a : Γ(F, ⊤), χ.app ⊤ a = v.hom a :=
  ⟨moduleSpecHomOfΓMap v, moduleSpecHomOfΓMap_app_top v, fun _ hχ =>
    moduleSpec_hom_ext_app_top_of_isQuasicoherent_source fun a =>
      (hχ a).trans (moduleSpecHomOfΓMap_app_top v a).symm⟩

/-! ### Restriction along an open immersion out of a spectrum

For an open immersion `j : Spec R ⟶ Y` and a quasi-coherent sheaf of modules `M` on `Y`, morphisms
`M.restrict j ⟶ N.restrict j` correspond to `R`-linear maps between the sections of `M` and `N`
over the image `j ''ᵁ ⊤`. -/

section Restrict

variable {R : CommRingCat.{u}} {Y : Scheme.{u}} (j : Spec R ⟶ Y) [IsOpenImmersion j]
  {M N : Y.Modules}

/-- The morphism of restrictions `M.restrict j ⟶ N.restrict j` along an open immersion
`j : Spec R ⟶ Y`, for `M` quasi-coherent, acting on the sections over the image of `j` as `v`. -/
def restrictHomOfΓMap [M.IsQuasicoherent]
    (v : moduleSpecΓFunctor.obj (M.restrict j) ⟶ moduleSpecΓFunctor.obj (N.restrict j)) :
    M.restrict j ⟶ N.restrict j :=
  moduleSpecHomOfΓMap v

/-- `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfΓMap j v` acts on a section over the
image of `j` as `v` does. -/
theorem restrictHomOfΓMap_app_top [M.IsQuasicoherent]
    (v : moduleSpecΓFunctor.obj (M.restrict j) ⟶ moduleSpecΓFunctor.obj (N.restrict j))
    (a : Γ(M, j ''ᵁ ⊤)) :
    (restrictHomOfΓMap j v).app ⊤ a = v.hom a :=
  moduleSpecHomOfΓMap_app_top v a

/-- Two morphisms of restrictions along an open immersion out of a spectrum which agree on the
sections over the image are equal, the source being quasi-coherent. -/
theorem restrict_hom_ext_app_top [M.IsQuasicoherent] {φ φ' : M.restrict j ⟶ N.restrict j}
    (h : ∀ a : Γ(M, j ''ᵁ ⊤), φ.app ⊤ a = φ'.app ⊤ a) : φ = φ' :=
  moduleSpec_hom_ext_app_top_of_isQuasicoherent_source h

/-- For an open immersion `j : Spec R ⟶ Y` and `M` quasi-coherent, every `R`-linear map between
the sections of `M` and `N` over the image of `j` is the action on those sections of exactly one
morphism `M.restrict j ⟶ N.restrict j`. -/
theorem existsUnique_restrictHom_app_top_eq [M.IsQuasicoherent]
    (v : moduleSpecΓFunctor.obj (M.restrict j) ⟶ moduleSpecΓFunctor.obj (N.restrict j)) :
    ∃! φ : M.restrict j ⟶ N.restrict j, ∀ a : Γ(M, j ''ᵁ ⊤), φ.app ⊤ a = v.hom a :=
  existsUnique_hom_app_top_eq_of_isQuasicoherent_source v

end Restrict

end Stacks.AlgebraicGeometry.ModuleLimits

end
