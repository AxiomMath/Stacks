module

public import StacksFrontier.Topology.Sheaves.Modules.Skyscraper

/-!
# The stalk functor on sheaves of modules is left adjoint to the skyscraper functor

Let `X` be a topological space, `O` a sheaf of rings on `Opens X`, and `x : X`. Write
`i_x : ({x}, O_x) ⟶ (X, O)` for the inclusion of the point. This file proves that taking the
stalk at `x`, `AlgebraicGeometry.SheafOfModules.stalkFunctor`, is left adjoint to the
skyscraper functor `AlgebraicGeometry.SheafOfModules.skyscraperFunctor`, that is
`i_x^* ⊣ i_{x,*}` on sheaves of modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.stalkSkyscraperHomEquiv`: the bijection
  `Hom_{O_x}(M_x, N) ≃ Hom_O(M, i_{x,*} N)`.
* `AlgebraicGeometry.SheafOfModules.stalkSkyscraperAdjunction`:
  `stalkFunctor O x ⊣ skyscraperFunctor O x`.

## Implementation notes

The unit direction is the germ map: a linear map `g : M_x ⟶ N` is sent to the morphism whose
component at `U` takes `s : M(U)` to the function `h ↦ g (germ_U s)` on the proposition
`x ∈ U`. Semilinearity is germ-semilinearity of the scalar action
(`AlgebraicGeometry.SheafOfModules.germ_hom_smul`) together with the skyscraper module
structure acting through the same germ map.

The inverse direction uses no colimit descent. A morphism `φ : M ⟶ i_{x,*} N` is sent to
`stalkFunctor.map φ` followed by `AlgebraicGeometry.SheafOfModules.skyscraperStalkIsoObj`, the
already-available isomorphism `(i_{x,*} N)_x ≅ N`. Both round trips then reduce to the single lemma
`germ_skyscraperStalkIsoObj_hom`: the germ at `x` of a section `t` of `i_{x,*} N` over an open
containing `x`, transported along that isomorphism, is the value of `t`. Its proof is that
`PLift (x ∈ U)` is a subsingleton, so `t` *is* the constant function at that value, and
`AlgebraicGeometry.SheafOfModules.germ_skyscraper_const` then moves the germ to `⊤`.

Taking the inverse direction to be a colimit descent would require a cocone over
`(OpenNhds.inclusion x).op ⋙ M.val.presheaf` in `AddCommGrpCat` followed by a separate
germ-induction for linearity; routing through `stalkFunctor.map` avoids both.

## References

* [Stacks Project, Tag 009A](https://stacks.math.columbia.edu/tag/009A)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

attribute [local instance] skyscraperModule

section Key

variable (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))

/-- A section of the skyscraper sheaf over an open containing `x` is the constant function at
its value, because the type `PLift (x ∈ U)` it is a function on is a subsingleton. -/
theorem skyscraper_eq_const (U : Opens X) (hxU : x ∈ U)
    (t : (skyscraperVal O x N).obj (op U)) : t = (fun _ => t ⟨hxU⟩) :=
  funext fun _ => congrArg t (Subsingleton.elim _ _)

/-- The germ at `x` of a section of the skyscraper sheaf at `x`, read through the isomorphism
`(i_{x,*} N)_x ≅ N`, is the value of that section. -/
theorem germ_skyscraperStalkIsoObj_hom (U : Opens X) (hxU : x ∈ U)
    (t : (skyscraperVal O x N).obj (op U)) :
    (skyscraperStalkIsoObj O x N).hom.hom
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
          (skyscraperVal O x N).presheaf U x hxU).hom t) =
      t ⟨hxU⟩ := by
  have h1 : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
        (skyscraperVal O x N).presheaf U x hxU).hom t =
      (toSkyscraperStalk O x N).hom (t ⟨hxU⟩) :=
    (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
      (skyscraperVal O x N).presheaf U x hxU).hom
      (skyscraper_eq_const O x N U hxU t)).trans
      (germ_skyscraper_const O x N U hxU (t ⟨hxU⟩))
  exact h1 ▸ (skyscraperStalkEquiv O x N).symm_apply_apply (t ⟨hxU⟩)

end Key

section HomEquiv

variable {M₁ M₂ : _root_.SheafOfModules.{u} O}
  {N₁ N₂ : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)}

variable (M : _root_.SheafOfModules.{u} O)
  (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))

/-- The morphism of presheaves of abelian groups underlying the unit direction of the
stalk--skyscraper bijection: over `U` a section goes to the function sending a proof that
`x ∈ U` to the image under `g` of its germ at `x`. -/
def stalkSkyscraperUpAb (g : stalkObj O x M ⟶ N) :
    M.val.presheaf ⟶ (skyscraperVal O x N).presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun s h => g.hom ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
        M.val.presheaf U.unop x h.down).hom s)
      map_zero' := funext fun _ => (congrArg g.hom (map_zero _)).trans (map_zero g.hom)
      map_add' := fun a b => funext fun _ =>
        (congrArg g.hom (map_add _ a b)).trans (map_add g.hom _ _) }
  naturality {U V} i := by
    ext s
    exact funext fun h => congrArg g.hom
      (TopCat.Presheaf.germ_res_apply M.val.presheaf i.unop x h.down s)

/-- The unit direction of the stalk--skyscraper bijection: a linear map out of the stalk
`M_x` becomes a morphism `M ⟶ i_{x,*} N` of sheaves of modules by composing with the germ
maps. -/
def stalkSkyscraperUp (g : stalkObj O x M ⟶ N) : M ⟶ skyscraperObj O x N where
  val := PresheafOfModules.homMk (stalkSkyscraperUpAb O x M N g) (fun U r m => funext fun h =>
    ((congrArg g.hom (germ_hom_smul O x M.val U.unop h.down r m)).trans
      (map_smul g.hom _ _)).trans
      (skyscraperModule_smul_apply O x N U r
        (stalkSkyscraperUpAb O x M N g |>.app U |>.hom m) h).symm)

/-- The component of `stalkSkyscraperUp O x M N g` over `U` sends a section `s` and a proof that
`x ∈ U` to the image under `g` of the germ of `s` at `x`. -/
@[simp]
theorem stalkSkyscraperUp_val_app_apply (g : stalkObj O x M ⟶ N) (U : (Opens X)ᵒᵖ)
    (s : M.val.obj U) (h : PLift (x ∈ U.unop)) :
    (stalkSkyscraperUp O x M N g).val.app U s h =
      g.hom ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
        M.val.presheaf U.unop x h.down).hom s) :=
  rfl

/-- The counit direction of the stalk--skyscraper bijection: a morphism `φ : M ⟶ i_{x,*} N`
becomes a linear map `M_x ⟶ N` by taking stalks and using that the stalk at `x` of the
skyscraper at `x` is `N`. -/
def stalkSkyscraperDown (φ : M ⟶ skyscraperObj O x N) : stalkObj O x M ⟶ N :=
  (stalkFunctor O x).map φ ≫ (skyscraperStalkIsoObj O x N).hom

/-- The linear map `stalkSkyscraperDown O x M N φ` sends the germ at `x` of a section `s` over
`U ∋ x` to the value of the section `φ s` of the skyscraper sheaf. -/
theorem stalkSkyscraperDown_germ (φ : M ⟶ skyscraperObj O x N) (U : Opens X) (hxU : x ∈ U)
    (s : M.val.obj (op U)) :
    (stalkSkyscraperDown O x M N φ).hom
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
          M.val.presheaf U x hxU).hom s) =
      φ.val.app (op U) s ⟨hxU⟩ := by
  have hmap : ((stalkFunctor O x).map φ).hom
      ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
        M.val.presheaf U x hxU).hom s) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
        (skyscraperVal O x N).presheaf U x hxU).hom (φ.val.app (op U) s) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hxU
      ((PresheafOfModules.toPresheaf O.obj).map φ.val) s
  exact (congrArg (skyscraperStalkIsoObj O x N).hom.hom hmap).trans
    (germ_skyscraperStalkIsoObj_hom O x N U hxU (φ.val.app (op U) s))

/-- `stalkSkyscraperUp` is a left inverse of `stalkSkyscraperDown`. -/
theorem stalkSkyscraperUp_down (φ : M ⟶ skyscraperObj O x N) :
    stalkSkyscraperUp O x M N (stalkSkyscraperDown O x M N φ) = φ := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.Hom.ext ?_)
  ext U s
  exact funext fun h => stalkSkyscraperDown_germ O x M N φ U.unop h.down s

/-- `stalkSkyscraperDown` is a left inverse of `stalkSkyscraperUp`. -/
theorem stalkSkyscraperDown_up (g : stalkObj O x M ⟶ N) :
    stalkSkyscraperDown O x M N (stalkSkyscraperUp O x M N g) = g := by
  refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  obtain ⟨U, hxU, s, hs⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
  exact hs ▸ (stalkSkyscraperDown_germ O x M N (stalkSkyscraperUp O x M N g) U hxU s)

/-- **The stalk--skyscraper bijection for sheaves of modules.** A linear map from the stalk
`M_x` to an `O_x`-module `N` is the same thing as a morphism of sheaves of `O`-modules from `M`
to the skyscraper sheaf at `x` with value `N`. -/
def stalkSkyscraperHomEquiv : (stalkObj O x M ⟶ N) ≃ (M ⟶ skyscraperObj O x N) where
  toFun := stalkSkyscraperUp O x M N
  invFun := stalkSkyscraperDown O x M N
  left_inv := stalkSkyscraperDown_up O x M N
  right_inv := stalkSkyscraperUp_down O x M N

end HomEquiv

section Naturality

variable {M₁ M₂ : _root_.SheafOfModules.{u} O}
  {N N₁ N₂ : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)}

/-- `stalkSkyscraperUp` is natural in the module `N`: postcomposing with `k : N₁ ⟶ N₂`
corresponds to postcomposing with the skyscraper of `k`. -/
theorem stalkSkyscraperUp_naturality_right (M : _root_.SheafOfModules.{u} O)
    (g : stalkObj O x M ⟶ N₁) (k : N₁ ⟶ N₂) :
    stalkSkyscraperUp O x M N₂ (g ≫ k) =
      stalkSkyscraperUp O x M N₁ g ≫ (skyscraperFunctor O x).map k :=
  rfl

/-- `stalkSkyscraperDown` is natural in the sheaf `M`: precomposing with `ψ : M₁ ⟶ M₂`
corresponds to precomposing with the map of stalks induced by `ψ`. -/
theorem stalkSkyscraperDown_naturality_left (ψ : M₁ ⟶ M₂) (φ : M₂ ⟶ skyscraperObj O x N) :
    stalkSkyscraperDown O x M₁ N (ψ ≫ φ) =
      (stalkFunctor O x).map ψ ≫ stalkSkyscraperDown O x M₂ N φ :=
  (congrArg (fun k => k ≫ (skyscraperStalkIsoObj O x N).hom)
    ((stalkFunctor O x).map_comp ψ φ)).trans (Category.assoc _ _ _)

end Naturality

/-- **Taking the stalk at `x` is left adjoint to the skyscraper sheaf at `x`**, for sheaves of
modules: `i_x^* ⊣ i_{x,*}`. -/
def stalkSkyscraperAdjunction : stalkFunctor O x ⊣ skyscraperFunctor O x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N => stalkSkyscraperHomEquiv O x M N
      homEquiv_naturality_left_symm := fun ψ φ =>
        stalkSkyscraperDown_naturality_left O x ψ φ
      homEquiv_naturality_right := fun g k =>
        stalkSkyscraperUp_naturality_right O x _ g k }

/-- The stalk functor at `x` on sheaves of modules is a left adjoint. -/
instance stalkFunctor_isLeftAdjoint : (stalkFunctor O x).IsLeftAdjoint :=
  (stalkSkyscraperAdjunction O x).isLeftAdjoint

/-- The skyscraper functor at `x` on sheaves of modules is a right adjoint. -/
instance skyscraperFunctor_isRightAdjoint : (skyscraperFunctor O x).IsRightAdjoint :=
  (stalkSkyscraperAdjunction O x).isRightAdjoint

end AlgebraicGeometry.SheafOfModules

end
