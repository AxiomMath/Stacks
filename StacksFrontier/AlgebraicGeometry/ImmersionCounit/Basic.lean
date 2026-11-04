module

public import StacksFrontier.AlgebraicGeometry.SchemeModuleGlue.Chart
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Local

/-!
# The counit of the restriction--pushforward adjunction at an open immersion, on sections

For an open immersion `f : X ⟶ Y` of schemes the counit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is an isomorphism
`restrict (f_* M) f ≅ M`, and its component over an open `T` of `X` is the restriction map of `M`
along the equality of opens `f ⁻¹ᵁ (f ''ᵁ T) = T`. This file reads that isomorphism on sections.
A local isomorphism of `f_* M` with itself, defined over an open of `Y` containing the image of
`f`, is conjugated by it into an endomorphism of `M`; if that endomorphism is the identity, then
the local isomorphism is the identity on the sections over the image of every open of `X`.

## Main definitions

* `TopCat.Sheaf.LocalModuleEquiv.ofLE`: a local isomorphism read over a smaller open.
* `Stacks.AlgebraicGeometry.ImmersionCounit.counitIso`: the counit identification
  `restrict (f_* M) f ≅ M` at an open immersion.
* `Stacks.AlgebraicGeometry.ImmersionCounit.conjEndo`: the endomorphism of `M` obtained by
  conjugating a local isomorphism of `f_* M` with itself by the counit.

## Main results

* `Stacks.AlgebraicGeometry.ImmersionCounit.counitIso_hom_app` and `counitIso_inv_app`: both
  directions of the counit identification are restriction maps of `M` along an equality of opens.
* `Stacks.AlgebraicGeometry.ImmersionCounit.conjEndo_app`: the conjugated endomorphism on a
  section.
* `Stacks.AlgebraicGeometry.ImmersionCounit.app_image_eq_self_of_conjEndo_eq_id`: if the
  conjugated endomorphism is the identity then the local isomorphism is the identity on the
  sections over the image of every open of `X`.

## Implementation notes

The counit isomorphism itself is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`, whose components are given by
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_counit_app_app`.

Both components of the counit are stated against an arbitrary inclusion of the two equal opens:
morphisms between opens are unique, so any such inclusion gives the same restriction map.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TopCat.Sheaf.LocalModuleEquiv

/-- The restriction of a local isomorphism over `W₁` to a smaller open `W₀ ≤ W₁`. -/
public def ofLE {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} 𝒪} {W₀ W₁ : Opens X} (e : LocalModuleEquiv M N W₁)
    (h : W₀ ≤ W₁) : LocalModuleEquiv M N W₀ where
  app V hV := e.app V (hV.trans h)
  naturality hV hWV s := e.naturality (hV.trans h) hWV s

/-- The component of `e.ofLE h` over `V ≤ W₀` is the component of `e` over `V`. -/
@[simp]
public theorem ofLE_app {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} 𝒪} {W₀ W₁ : Opens X} (e : LocalModuleEquiv M N W₁)
    (h : W₀ ≤ W₁) (V : Opens X) (hV : V ≤ W₀) (s : M.obj (op V)) :
    (e.ofLE h).app V hV s = e.app V (hV.trans h) s :=
  rfl

end TopCat.Sheaf.LocalModuleEquiv

namespace Stacks.AlgebraicGeometry.ImmersionCounit

variable {X Y : Scheme.{u}}

/-! ### Reading an isomorphism of sheaves of modules on a section -/

/-- An isomorphism of sheaves of modules, followed by its inverse, is the identity on a
section. -/
public theorem iso_hom_inv_app {M N : X.Modules} (ι : M ≅ N) (T : X.Opens)
    (x : M.val.obj (op T)) : ι.inv.val.app (op T) (ι.hom.val.app (op T) x) = x :=
  congrArg (fun φ : M ⟶ M => φ.val.app (op T) x) ι.hom_inv_id

/-- The inverse of an isomorphism of sheaves of modules, followed by the isomorphism, is the
identity on a section. -/
public theorem iso_inv_hom_app {M N : X.Modules} (ι : M ≅ N) (T : X.Opens)
    (y : N.val.obj (op T)) : ι.hom.val.app (op T) (ι.inv.val.app (op T) y) = y :=
  congrArg (fun φ : N ⟶ N => φ.val.app (op T) y) ι.inv_hom_id

/-! ### The counit identification -/

/-- The counit of the restriction--pushforward adjunction at an open immersion, as an
isomorphism: the restriction along `f` of the direct image of `M` is `M`. -/
public def counitIso (f : X ⟶ Y) [IsOpenImmersion f] (M : X.Modules) :
    (Scheme.Modules.restrictFunctor f).obj ((Scheme.Modules.pushforward f).obj M) ≅ M :=
  asIso ((Scheme.Modules.restrictAdjunction f).counit.app M)

/-- On sections over `T`, the counit is the restriction map of `M` along the equality of opens
`f ⁻¹ᵁ (f ''ᵁ T) = T`. -/
public theorem counitIso_hom_app (f : X ⟶ Y) [IsOpenImmersion f] (M : X.Modules) (T : X.Opens)
    (i : (op (f ⁻¹ᵁ (f ''ᵁ T)) : (Opens X)ᵒᵖ) ⟶ op T)
    (x : ((Scheme.Modules.restrictFunctor f).obj
      ((Scheme.Modules.pushforward f).obj M)).val.obj (op T)) :
    (counitIso f M).hom.val.app (op T) x = M.val.map i x := by
  obtain rfl : i = (eqToHom (f.preimage_image_eq T).symm).op := Subsingleton.elim _ _
  rfl

/-- On sections over `T`, the inverse of the counit is the restriction map of `M` along the
equality of opens `T = f ⁻¹ᵁ (f ''ᵁ T)`. -/
public theorem counitIso_inv_app (f : X ⟶ Y) [IsOpenImmersion f] (M : X.Modules) (T : X.Opens)
    (j : (op T : (Opens X)ᵒᵖ) ⟶ op (f ⁻¹ᵁ (f ''ᵁ T))) (t : M.val.obj (op T)) :
    (counitIso f M).inv.val.app (op T) t = M.val.map j t := by
  refine Eq.trans (congrArg ((counitIso f M).inv.val.app (op T)) ?_)
    (iso_hom_inv_app (counitIso f M) T (M.val.map j t))
  exact ((counitIso_hom_app f M T (eqToHom (f.preimage_image_eq T).symm).op _).trans
    (PresheafOfModules.map_map_eq_self M.val j _ t)).symm

/-! ### Conjugating a local isomorphism of a direct image into an endomorphism -/

variable (f : X ⟶ Y) [IsOpenImmersion f] (M : X.Modules) {W₀ : Y.Opens}
  (e : TopCat.Sheaf.LocalModuleEquiv ((Scheme.Modules.pushforward f).obj M).val
    ((Scheme.Modules.pushforward f).obj M).val W₀)
  (hf : f ''ᵁ (⊤ : X.Opens) ≤ W₀)

/-- A local isomorphism of the direct image of `M` with itself, defined over an open of `Y`
containing the image of `f`, restricts along `f` to an automorphism of `restrict (f_* M) f`;
conjugating by the counit gives an endomorphism of `M`. -/
public def conjEndo : M ⟶ M :=
  (counitIso f M).inv ≫
    (TwistExistence.isoOfLocalEquiv (TwistExistence.restrictLocalEquiv f e hf)).hom ≫
      (counitIso f M).hom

/-- On a section over `T`, `conjEndo f M e hf` applies the inverse of the counit, then the
component of `e` over `f ''ᵁ T`, then the counit. -/
public theorem conjEndo_app (T : X.Opens) (t : M.val.obj (op T)) :
    (conjEndo f M e hf).val.app (op T) t =
      (counitIso f M).hom.val.app (op T)
        (e.app (f ''ᵁ T) ((f.image_mono le_top).trans hf)
          ((counitIso f M).inv.val.app (op T) t)) :=
  rfl

/-- If `conjEndo f M e hf` is the identity, then `e` is the identity on the sections over the image
of every open of `X`. -/
public theorem app_image_eq_self_of_conjEndo_eq_id (hid : conjEndo f M e hf = 𝟙 M) (T : X.Opens)
    (x : ((Scheme.Modules.pushforward f).obj M).val.obj (op (f ''ᵁ T))) :
    e.app (f ''ᵁ T) ((f.image_mono le_top).trans hf) x = x := by
  refine Function.LeftInverse.injective (iso_hom_inv_app (counitIso f M) T) ?_
  have h : (conjEndo f M e hf).val.app (op T) ((counitIso f M).hom.val.app (op T) x) =
      (counitIso f M).hom.val.app (op T) x :=
    congrArg (fun φ : M ⟶ M => φ.val.app (op T) ((counitIso f M).hom.val.app (op T) x)) hid
  exact (congrArg (fun z => (counitIso f M).hom.val.app (op T)
    (e.app (f ''ᵁ T) ((f.image_mono le_top).trans hf) z))
      (iso_hom_inv_app (counitIso f M) T x)).symm.trans h

end Stacks.AlgebraicGeometry.ImmersionCounit

end
