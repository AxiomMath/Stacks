module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials

/-!
# Ringed sites

A ringed site is a site equipped with a sheaf of commutative rings, its structure sheaf. A
morphism of ringed sites consists of a morphism of the underlying sites together with a
morphism from the target structure sheaf to the direct image of the source structure sheaf.
Such morphisms compose by applying the first direct-image functor to the second structure map
and then using the canonical comparison of the composite of two direct images with the direct
image of the composite.

The structure map is stored in its direct-image form `O_Y ⟶ f_* O_X`, and a morphism of sites
`X ⟶ Y` is represented by its continuous functor from the underlying category of `Y` to that of
`X`. The structure sheaf takes values in `CommRingCat`; for every site, the sheaf condition is
preserved by the forgetful functor `forget₂ CommRingCat RingCat`.

## Main definitions

* `AlgebraicGeometry.RingedSite`: a site together with its structure sheaf of commutative
  rings.
* `AlgebraicGeometry.RingedSite.Hom`: a morphism of ringed sites.
* `AlgebraicGeometry.RingedSite.Hom.fsharpPullback`: the structure map in inverse-image form.
* `AlgebraicGeometry.RingedSite.Hom.comp`: composition of morphisms of ringed sites.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.homEquiv_fsharpPullback` identifies the inverse-image
  structure map with the stored direct-image map under the canonical adjunction.
* `AlgebraicGeometry.RingedSite.Hom.comp_u` and
  `AlgebraicGeometry.RingedSite.Hom.comp_fsharp` record the two components of a composite.
* `AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`: every ringed site composes
  the sheaf condition with `forget₂ CommRingCat RingCat`.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- A ringed site is a category with a Grothendieck topology and a sheaf of commutative
rings. -/
@[stacks 03AD "part (1): ringed sites", sga "4 IV 11.1.1" "ringed site"]
structure RingedSite where
  /-- The underlying category. -/
  C : Type u
  /-- Morphisms in the underlying category. -/
  [category : Category.{v} C]
  /-- The Grothendieck topology on the underlying category. -/
  J : GrothendieckTopology C
  /-- The structure sheaf. -/
  O : Sheaf J CommRingCat.{w}

attribute [instance] RingedSite.category

namespace RingedSite

/-- A morphism of ringed sites. The functor `u : Y.C ⥤ X.C` represents the underlying morphism
of sites `X ⟶ Y`, and `fsharp` is its structure map in direct-image form. -/
@[stacks 03AD "part (2): morphisms of ringed sites", sga "4 IV 13.3"]
structure Hom (X Y : RingedSite.{u, u, w}) where
  /-- The functor, in the direction opposite to the represented morphism of sites. -/
  u : Y.C ⥤ X.C
  /-- The assertion that `u` defines a morphism of sites. -/
  isMorphismOfSites : u.IsMorphismOfSites Y.J X.J
  /-- The structure map `O_Y ⟶ f_* O_X`. -/
  fsharp :
    letI : u.IsContinuous Y.J X.J := isMorphismOfSites.isContinuous
    Y.O ⟶ (u.sheafPushforwardContinuous CommRingCat.{w} Y.J X.J).obj X.O

/-- The functor underlying a morphism of ringed sites is continuous. -/
instance Hom.isContinuous {X Y : RingedSite.{u, u, w}} (f : Hom X Y) :
    f.u.IsContinuous Y.J X.J := f.isMorphismOfSites.isContinuous

/-- The structure map of a morphism of ringed sites in inverse-image form
`f⁻¹ O_Y ⟶ O_X`. -/
noncomputable def Hom.fsharpPullback {X Y : RingedSite.{u, u, u}} (f : Hom X Y) :
    (f.u.sheafPullback CommRingCat.{u} Y.J X.J).obj Y.O ⟶ X.O :=
  ((f.u.sheafAdjunctionContinuous CommRingCat.{u} Y.J X.J).homEquiv Y.O X.O).symm f.fsharp

/-- Under the inverse-image/direct-image adjunction, `fsharpPullback` corresponds to the stored
direct-image structure map `fsharp`. -/
@[simp]
theorem Hom.homEquiv_fsharpPullback {X Y : RingedSite.{u, u, u}} (f : Hom X Y) :
    (f.u.sheafAdjunctionContinuous CommRingCat.{u} Y.J X.J).homEquiv Y.O X.O
      f.fsharpPullback = f.fsharp := by simp [Hom.fsharpPullback]

/-- Composition of morphisms of ringed sites. On structure sheaves this is
`O_Z ⟶ g_* O_Y ⟶ g_* f_* O_X ≅ (g ∘ f)_* O_X`. -/
@[stacks 03AD "part (3): composition of morphisms of ringed sites", implicit_reducible]
noncomputable def Hom.comp {X Y Z : RingedSite.{u, u, w}} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z := by
  let : g.u.IsContinuous Z.J Y.J := g.isMorphismOfSites.isContinuous
  let : f.u.IsContinuous Y.J X.J := f.isMorphismOfSites.isContinuous
  let h := g.isMorphismOfSites.comp f.isMorphismOfSites
  let : (g.u ⋙ f.u).IsContinuous Z.J X.J := h.isContinuous
  exact
    { u := g.u ⋙ f.u
      isMorphismOfSites := h
      fsharp := g.fsharp ≫
        (g.u.sheafPushforwardContinuous CommRingCat.{w} Z.J Y.J).map f.fsharp ≫
        (Functor.sheafPushforwardContinuousComp g.u f.u CommRingCat.{w}
          Z.J Y.J X.J).hom.app X.O }

/-- The functor underlying the composite `f.comp g` is `g.u ⋙ f.u`. -/
@[simp]
theorem Hom.comp_u {X Y Z : RingedSite.{u, u, w}} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).u = g.u ⋙ f.u := by simp [Hom.comp]

/-- The structure map of the composite `f.comp g` is `g.fsharp`, followed by the direct image
of `f.fsharp` under `g`, followed by the comparison of the composite of the two direct images
with the direct image of the composite. -/
@[simp]
theorem Hom.comp_fsharp {X Y Z : RingedSite.{u, u, w}} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).fsharp = g.fsharp ≫
      (g.u.sheafPushforwardContinuous CommRingCat.{w} Z.J Y.J).map f.fsharp ≫
      (Functor.sheafPushforwardContinuousComp g.u f.u CommRingCat.{w}
        Z.J Y.J X.J).hom.app X.O := by simp [Hom.comp]

end RingedSite

end AlgebraicGeometry

end

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t s u v w

namespace AlgebraicGeometry

namespace RingedSite

/-- On any site, the sheaf condition for `CommRingCat`-valued sheaves is preserved by
`forget₂ CommRingCat RingCat`. -/
theorem hasSheafCompose_forget₂_ringCat (X : RingedSite.{u, v, w}) :
    X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := by
  let : PreservesLimitsOfSize.{v, max u v} (forget₂ CommRingCat.{w} RingCat.{w}) :=
    preservesLimitsOfSize_forget₂_commRingCat_ringCat
  exact hasSheafCompose_of_preservesLimitsOfSize X.J

end RingedSite

end AlgebraicGeometry

end
