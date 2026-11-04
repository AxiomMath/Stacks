module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizationLift
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.CompositionOfLocallyRingedMorphisms
import StacksCore.Tactic.StacksAttribute

/-!
# Locally ringed morphisms of ringed topoi: 2-isomorphism invariance and right cancellation

Being a morphism of *locally* ringed topoi (Stacks 04HA: the square of units subsheaves is
cartesian) is a property of a morphism of ringed topoi, and this file proves the two closure
properties of it which are not formal consequences of the definition.

**2-isomorphism invariance.** A `AlgebraicGeometry.RingedToposHom.TwoIso` is an isomorphism of
the direct image functors compatible with the two structure maps, so it has nothing to say about
inverse images, in which the units square is written. What makes the units squares of two
2-isomorphic morphisms comparable is that an isomorphism of right adjoints induces one of the
left adjoints: the inverse images of `f` and `g` are both left adjoint to `f_*` once the
2-isomorphism is used to transport the adjunction of `g`, so they are canonically isomorphic,
and the compatibility of the 2-isomorphism with the two structure maps says exactly that this
isomorphism carries the one units square to the other.

**Right cancellation.** Stacks 04IG, `AlgebraicGeometry.RingedToposHom.isLocallyRinged_comp`,
says a composite of locally ringed morphisms is locally ringed, by pasting the units square of
`f` with the image under `f^{-1}` of that of `g`. Here the paste is read backwards: if the
composite `g ∘ f` is locally ringed and `f` is, then the *left* half of the paste is cartesian,
by `CategoryTheory.IsPullback.of_right'`, so the image under `f^{-1}` of the units square of `g`
is cartesian, and if `f^{-1}` is an equivalence that square descends to `g`. No nilpotency, no
conservative family of points and no locality of a stalk map is used: the cancellation is the
subobject sandwich `O_X^* ⊆ (f^♯)^{-1}(O^*) ⊆ ((g ∘ f)^♯)^{-1}(O^*)` read as a diagram.

The hypothesis that `f^{-1}` is an equivalence is needed in both of its halves. Fullness is
what produces the top edge of the descended square — a units square has at most one top edge,
the inclusion of units being monic, but *some* morphism on the site of `g`'s source has to be
exhibited — and reflection of limits is what makes the descended square cartesian.  It is an
explicit argument rather than an instance argument: the only witness in this development is a
theorem rather than an instance, and with it in instance position the failed search assigns the
universe parameters of the source ringed topos their defaults before the explicit arguments
have pinned them.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoIso.fSharpSet_eq`: the isomorphism of inverse images
  carries the inverse-image structure map of `g` to that of `f`, in the `fSharpSet` spelling the
  units square is written in.
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_twoIso`: **being locally ringed is
  invariant under 2-isomorphism.**
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_comp_of_isEquivalence`: **right
  cancellation** — if `g ∘ f` and `f` are locally ringed and the inverse image of `f` is an
  equivalence, then `g` is locally ringed.

## Implementation notes

The isomorphism of inverse images is not constructed here.  It is
`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIso` of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/LocalizationLift.lean:45`, the conjugate
of the 2-isomorphism across the two adjunctions, and it points `q⁻¹ ⟶ p⁻¹` for `s : TwoIso p q`.
The direction wanted here is `f⁻¹ ⟶ g⁻¹`, so every use below is at `s.symm`.

The right cancellation is stated with `f^{-1}` an equivalence rather than with the weaker
hypotheses it uses — full, faithful and reflecting pullbacks — because the only witness in
this development is an equivalence outright, and because `CategoryTheory.Functor.IsEquivalence`
is a class, so the two ingredients are found by instance search once it is in context rather
than threaded by hand.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04IG](https://stacks.math.columbia.edu/tag/04IG)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w' v'' u'' w''

section TwoIsoInvariance

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {f g : RingedToposHom X Y}

namespace TwoIso

/-- **The isomorphism of inverse images carries the structure map of `g` to that of `f`**, in the
`fSharpSet` spelling the units square is written in.  The isomorphism is
`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIso` of the *reversed* 2-isomorphism, that
being the one pointing `f⁻¹ ⟶ g⁻¹`, and the content is its compatibility with the structure maps,
`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIso_fSharpInverseImage`, transported along
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`, whose right-hand side is
`fSharpSet` by definition.  (The companion
`AlgebraicGeometry.RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpSet` is *not* usable
here: it is stated with both ringed topoi at one sheaf-value universe and with two further
`HasSheafCompose (forget CommRingCat)` instances, neither of which is assumed in this section.) -/
theorem fSharpSet_eq (s : TwoIso f g) :
    fSharpSet f = s.symm.inverseImageIso.hom.app (Y.forgetRing.obj Y.O) ≫ fSharpSet g := by
  have h (k : RingedToposHom X Y) :
      fSharpSet k = X.forgetRing.map k.fSharpInverseImage :=
    (fSharpInverseImage_forget_homEquiv k).symm
  rw [h f, h g]
  exact (inverseImageIso_fSharpInverseImage s.symm).symm

end TwoIso

/-- **Being a morphism of locally ringed topoi is invariant under 2-isomorphism.**  The
isomorphism of inverse images of `AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIso`
carries the units square of `g` to the units square of `f`, and an isomorphic square is
cartesian. -/
theorem isLocallyRinged_of_twoIso (s : TwoIso f g) (hg : g.IsLocallyRinged) :
    f.IsLocallyRinged := by
  obtain ⟨t, ht⟩ := hg
  refine ⟨s.symm.inverseImageIso.hom.app (RingedTopos.units Y) ≫ t, ?_⟩
  refine ht.of_iso' (s.symm.inverseImageIso.app (RingedTopos.units Y)) (Iso.refl _)
    (s.symm.inverseImageIso.app (Y.forgetRing.obj Y.O)) (Iso.refl _)
    (Category.comp_id _).symm ?_ ?_ ?_
  · exact (s.symm.inverseImageIso.hom.naturality (RingedTopos.unitsι Y)).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact s.fSharpSet_eq.symm.trans (Category.comp_id _).symm

end TwoIsoInvariance

section RightCancellation

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]

/-- **Right cancellation for locally ringed morphisms of ringed topoi.**  If `g ∘ f` and `f` are
morphisms of locally ringed topoi and the inverse image of `f` is an equivalence, then `g` is a
morphism of locally ringed topoi.

The units square of `g ∘ f` is the horizontal paste of the image under `f^{-1}` of the units
square of `g` with the units square of `f`
(`AlgebraicGeometry.RingedToposHom.fSharpSet_comp`), so the left half of the paste is cartesian
by `CategoryTheory.IsPullback.of_right'`; fullness of `f^{-1}` exhibits its top edge as the
image of a morphism on the site of the source of `g`, and `f^{-1}` reflects the square. -/
theorem isLocallyRinged_of_comp_of_isEquivalence (g : RingedToposHom Y Z)
    (f : RingedToposHom X Y) (hequiv : f.toToposHom.inverseImage.IsEquivalence)
    (hgf : (g.comp f).IsLocallyRinged) (hf : f.IsLocallyRinged) :
    g.IsLocallyRinged := by
  have := hequiv
  obtain ⟨t, ht⟩ := hgf
  obtain ⟨tf, htf⟩ := hf
  rw [fSharpSet_comp g f] at ht
  have hleft := IsPullback.of_right' ht htf
  refine ⟨f.toToposHom.inverseImage.preimage (htf.lift t
    ((g.comp f).toToposHom.inverseImage.map (RingedTopos.unitsι Z) ≫
      f.toToposHom.inverseImage.map (fSharpSet g))
    (ht.w.trans (Category.assoc _ _ _).symm)), ?_⟩
  refine IsPullback.of_map_of_faithful f.toToposHom.inverseImage ?_
  rw [f.toToposHom.inverseImage.map_preimage]
  exact hleft

end RightCancellation

end AlgebraicGeometry.RingedToposHom

end
