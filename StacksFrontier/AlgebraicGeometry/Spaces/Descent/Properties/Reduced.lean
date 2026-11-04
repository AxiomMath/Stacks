module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae

/-!
# Reducedness of algebraic spaces along flat and smooth morphisms

Reducedness of an algebraic space is the étale-local scheme property
`AlgebraicGeometry.IsReduced` in the sense of Stacks 03E6. It passes from the source of a flat
surjective morphism of algebraic spaces to its target, and from the target of a smooth
morphism to its source.

## Main results

* `AlgebraicGeometry.Space.isReduced_of_flat_of_surjective`: a flat surjective morphism with
  reduced source has reduced target.
* `AlgebraicGeometry.Space.isReduced_source_of_isSmooth`: a smooth morphism with reduced target
  has reduced source.

## References

* [Stacks Project, Tag 06MI](https://stacks.math.columbia.edu/tag/06MI)
* [Stacks Project, Tag 0GB3](https://stacks.math.columbia.edu/tag/0GB3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A flat surjective morphism of algebraic spaces over `S` whose source is reduced has reduced
target. -/
@[stacks 06MI, stacks 0GB3 "reducedness of the target under surjectivity"]
theorem isReduced_of_flat_of_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hflat : IsFlat B S hS f)
    (hsurj : IsSurjective B S hS f)
    (hred : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T)) :
    HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T) := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨V, b, hbS, hbE⟩ := hY.exists_atlas
  obtain ⟨U, a, h, haE, hcomm, -, hhsurj⟩ :=
    exists_etale_chart_square_over B S hS hX hY f V b hbE
  have : IsReduced (T.obj U) :=
    (exists_atlas_iff_forall_etale B S hS X (fun Z : Scheme.{u} => IsReduced Z) hX).mp
      hred U a haE
  have : Flat (T.map h) := hflat U V a b h haE hbE hcomm
  have : Surjective (T.map h) := hhsurj hsurj
  exact ⟨V, b, hbS, hbE, AlgebraicGeometry.isReduced_of_flat_of_surjective (T.map h)⟩

/-- A smooth morphism of algebraic spaces over `S` whose target is reduced has reduced source. -/
@[stacks 0GB3 "reducedness of the source", sga "1 II 3.1" "reduced, Y ⇒ X"]
theorem isReduced_source_of_isSmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsSmooth B S hS f)
    (hred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T)) :
    HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T) := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, V, a, b, h, haEtale, hbEtale, haSurj, _, hhSmooth⟩ :=
    ((isSmooth_tfae B S hS hX hY f).out 1 8).mp hf
  have : IsReduced (T.obj V) :=
    (exists_atlas_iff_forall_etale B S hS Y (fun Z : Scheme.{u} => IsReduced Z) hY).mp
      hred V b hbEtale
  have : Smooth (T.map h) := hhSmooth
  exact ⟨U, a, haSurj, haEtale, isReduced_of_smooth (T.map h)⟩

end AlgebraicGeometry.Space

end
