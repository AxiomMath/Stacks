module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafHomAction

/-!
# The sections of the sheaf of homomorphisms over the whole space

The sections of `SheafHom_{𝒪_X}(M, N)` over an open `U` of a scheme `X` are the `𝒪_U`-linear maps
`M|_U ⟶ N|_U`, which is `Stacks.Thickenings.moduleHomSections`. Over `U = ⊤` they are the global
homomorphisms `M ⟶ N`: a section over `⊤` is a family of `Γ(X, W)`-linear maps
`Γ(M, W) ⟶ Γ(N, W)`, one for each open `W ≤ ⊤`, compatible with restriction, and since *every*
open of `X` satisfies `W ≤ ⊤` that family is exactly the datum of a map of sheaves of modules
`M ⟶ N`.

This file proves that, as an isomorphism of additive groups, and pins it down on sections in both
directions, so that it is not an arbitrary reparametrisation: the underlying family of maps on
sections over opens is unchanged in either direction.

## Main definitions

* `Stacks.Thickenings.moduleHomSectionsTopVal`: the map of presheaves of modules `M ⟶ N`
  underlying a section of `SheafHom_{𝒪_X}(M, N)` over `⊤`, read open by open through
  `Stacks.Thickenings.moduleHomSections.app`.
* `Stacks.Thickenings.moduleHomSectionsTopEquiv`: the resulting additive equivalence
  `Stacks.Thickenings.moduleHomSections M N ⊤ ≃+ (M ⟶ N)`.

## Main results

* `Stacks.Thickenings.moduleHomSectionsTopEquiv_app` and
  `Stacks.Thickenings.moduleHomSectionsTopEquiv_symm_app`: the equivalence and its inverse do not
  touch the family of maps on sections — the global homomorphism attached to a section over `⊤`
  acts on `Γ(M, W)` the way the section does, and conversely.

## Implementation notes

Nothing is transported along an equivalence of sites. The forward map is built by hand: its
component over an open `W` is the `Γ(X, W)`-linear map
`Stacks.Thickenings.moduleHomSections.app` of the section at the witness `W ≤ ⊤`, additive by
`Stacks.Thickenings.moduleHomSections.app_add`, linear by
`Stacks.Thickenings.moduleHomSections.app_smul`, and natural by
`Stacks.Thickenings.moduleHomSections.map_app`. The inverse is Mathlib's
`SheafOfModules.Hom.over`, the restriction functor on morphisms, and because the site of opens
contained in `⊤` has the same objects and the same morphisms as the site of all opens — the
structure map of an object of `Over ⊤` is a proof — the two round trips hold by definition.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Thickenings

section HomSectionsTop

variable {X : Scheme.{u}}

/-- **The map of presheaves of modules underlying a section of `SheafHom_{𝒪_X}(M, N)` over
`⊤`.** Its component over an open `W` is the map on sections
`Stacks.Thickenings.moduleHomSections.app` of the section at the witness `W ≤ ⊤`, which is
additive and `Γ(X, W)`-linear, and natural in `W`. -/
def moduleHomSectionsTopVal (M N : X.Modules) (θ : moduleHomSections M N ⊤) :
    M.val ⟶ N.val :=
  PresheafOfModules.Hom.mk
    (fun W => ModuleCat.ofHom (X := M.val.obj W) (Y := N.val.obj W)
      { toFun := fun s => moduleHomSections.app θ (W := W.unop) le_top s
        map_add' := fun s t => moduleHomSections.app_add θ (W := W.unop) le_top s t
        map_smul' := fun r s => moduleHomSections.app_smul θ (W := W.unop) le_top r s })
    (fun {W W'} f => by
      refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
      exact moduleHomSections.map_app θ (W := W.unop) (W' := W'.unop) le_top f.unop.le s)

/-- **The sections of `SheafHom_{𝒪_X}(M, N)` over the whole space are the global
homomorphisms.** A section over `⊤` is a family of `Γ(X, W)`-linear maps `Γ(M, W) ⟶ Γ(N, W)`
indexed by the opens `W ≤ ⊤` and compatible with restriction; every open of `X` satisfies
`W ≤ ⊤`, so that family is the datum of a map of sheaves of `𝒪_X`-modules `M ⟶ N`. The
identification is additive, and the inverse is the restriction functor on morphisms,
`SheafOfModules.Hom.over`. -/
def moduleHomSectionsTopEquiv (M N : X.Modules) :
    moduleHomSections M N ⊤ ≃+ (M ⟶ N) where
  toFun θ := SheafOfModules.Hom.mk (moduleHomSectionsTopVal M N θ)
  invFun f := SheafOfModules.Hom.over f ⊤
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **`Stacks.Thickenings.moduleHomSectionsTopEquiv` does not touch the maps on sections**: the
global homomorphism attached to a section of `SheafHom_{𝒪_X}(M, N)` over `⊤` acts on the sections
over an open `W` exactly as the section does. -/
theorem moduleHomSectionsTopEquiv_app {M N : X.Modules} (θ : moduleHomSections M N ⊤)
    {W : X.Opens} (hW : W ≤ ⊤) (s : Γ(M, W)) :
    Scheme.Modules.Hom.app (moduleHomSectionsTopEquiv M N θ) W s =
      moduleHomSections.app θ hW s :=
  rfl

/-- **The inverse of `Stacks.Thickenings.moduleHomSectionsTopEquiv` does not touch the maps on
sections** either: the section over `⊤` attached to a global homomorphism acts on the sections
over an open `W` exactly as the homomorphism does. -/
theorem moduleHomSectionsTopEquiv_symm_app {M N : X.Modules} (f : M ⟶ N) {W : X.Opens}
    (hW : W ≤ ⊤) (s : Γ(M, W)) :
    moduleHomSections.app ((moduleHomSectionsTopEquiv M N).symm f) hW s =
      Scheme.Modules.Hom.app f W s :=
  rfl

end HomSectionsTop

end Stacks.Thickenings

end
