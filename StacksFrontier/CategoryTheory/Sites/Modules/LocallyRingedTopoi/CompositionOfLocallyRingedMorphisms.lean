module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of locally ringed morphisms of ringed topoi

A morphism of ringed topoi is *locally ringed* (Stacks 04HA) when its square of units subsheaves
is cartesian. This file proves Stacks 04IG: a composite of locally ringed morphisms is locally
ringed.

## Main results

* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_comp`: locality is preserved by composition.

## Implementation notes

The argument is the horizontal paste of two cartesian squares. Writing `f♯_set` for the
structure map on underlying sheaves of sets in inverse-image form, the units square of
`g ∘ f` has bottom edge `f♯_set (g ∘ f) = f⁻¹(g♯_set) ≫ f♯_set`
(`AlgebraicGeometry.RingedToposHom.fSharpSet_comp`), so it is the paste of the units square of
`f` with the image under `f⁻¹` of the units square of `g`. The image is again cartesian because
`f⁻¹` is left exact, which is part of the data of a morphism of topoi.

The three ringed topoi have independent site and section universes.

## References

* [Stacks Project, Tag 04IG](https://stacks.math.columbia.edu/tag/04IG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe v u w v' u' w' v'' u'' w''

namespace AlgebraicGeometry

namespace RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]

/-- In inverse-image form, the structure map of a composite of morphisms of ringed topoi is the
inverse image under `f⁻¹` of the structure map of `g`, followed by the structure map of `f`. -/
lemma fSharpSet_comp (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    fSharpSet (g.comp f) =
      f.toToposHom.inverseImage.map (fSharpSet g) ≫ fSharpSet f := by
  have h : fSharpSet (g.comp f) =
      ((g.toToposHom.adj.comp f.toToposHom.adj).homEquiv
        (Z.forgetRing.obj Z.O) (X.forgetRing.obj X.O)).symm
        (Z.forgetRing.map g.fSharp ≫
          g.toToposHom.pushforward.map (Y.forgetRing.map f.fSharp)) :=
    congrArg (fun m ↦ ((g.toToposHom.adj.comp f.toToposHom.adj).homEquiv
      (Z.forgetRing.obj Z.O) (X.forgetRing.obj X.O)).symm m) (comp_fSharp_forget g f)
  have hinner : (g.toToposHom.adj.homEquiv (Z.forgetRing.obj Z.O)
        (f.toToposHom.pushforward.obj (X.forgetRing.obj X.O))).symm
        (Z.forgetRing.map g.fSharp ≫
          g.toToposHom.pushforward.map (Y.forgetRing.map f.fSharp)) =
      fSharpSet g ≫ Y.forgetRing.map f.fSharp :=
    Adjunction.homEquiv_naturality_right_symm g.toToposHom.adj
      (Z.forgetRing.map g.fSharp) (Y.forgetRing.map f.fSharp)
  have houter : (f.toToposHom.adj.homEquiv
        (g.toToposHom.inverseImage.obj (Z.forgetRing.obj Z.O))
        (X.forgetRing.obj X.O)).symm (fSharpSet g ≫ Y.forgetRing.map f.fSharp) =
      f.toToposHom.inverseImage.map (fSharpSet g) ≫ fSharpSet f :=
    Adjunction.homEquiv_naturality_left_symm f.toToposHom.adj (fSharpSet g)
      (Y.forgetRing.map f.fSharp)
  rw [h, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  exact (congrArg (fun m ↦ (f.toToposHom.adj.homEquiv
    (g.toToposHom.inverseImage.obj (Z.forgetRing.obj Z.O))
    (X.forgetRing.obj X.O)).symm m) hinner).trans houter

/-- **Stacks 04IG.** A composite of locally ringed morphisms of ringed topoi is locally
ringed. -/
@[stacks 04IG]
theorem isLocallyRinged_comp (g : RingedToposHom Y Z) (f : RingedToposHom X Y)
    (hg : IsLocallyRinged g) (hf : IsLocallyRinged f) :
    IsLocallyRinged (g.comp f) := by
  obtain ⟨tg, htg⟩ := hg
  obtain ⟨tf, htf⟩ := hf
  refine ⟨f.toToposHom.inverseImage.map tg ≫ tf, ?_⟩
  have := f.toToposHom.preservesFiniteLimits
  rw [fSharpSet_comp g f]
  exact (CategoryTheory.Functor.map_isPullback f.toToposHom.inverseImage htg).paste_horiz htf

end RingedToposHom

end AlgebraicGeometry

end
