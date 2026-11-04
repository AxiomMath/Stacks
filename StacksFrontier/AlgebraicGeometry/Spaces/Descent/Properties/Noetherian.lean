module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# Descending a property of schemes along a flat surjection of finite presentation

A property of schemes which is local both for the étale precoverage and for the fppf
precoverage passes, as a property of algebraic spaces in the sense of Stacks 03E6, from the
source of a surjective, flat morphism locally of finite presentation to its target. Local
Noetherianity is such a property, so it descends along such a morphism.

## Main results

* `hasEtaleLocalProperty_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation`, in the
  namespace `AlgebraicGeometry.Space`, is the descent statement.
* `isLocallyNoetherian_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation`, in the
  same namespace, is its locally Noetherian case.

## Implementation notes

Étale locality turns both occurrences of `AlgebraicGeometry.Space.HasEtaleLocalProperty` into
every-chart conditions, by Stacks 03E8. Given an étale chart `b` of the target, lifting it to
an étale chart `a` of the source makes the morphism of schemes between the two charts
surjective, flat and locally of finite presentation, so it is a one-element fppf covering of
the chart of the target; fppf locality then transports the property from the chart of the
source to the chart of the target.

Both locality hypotheses are discharged for local Noetherianity of schemes by
`AlgebraicGeometry.isLocallyNoetherian_isLocal_fppf` (Stacks 034C) and
`AlgebraicGeometry.isLocallyNoetherian_isLocal_etale`, so the Noetherian case needs no
hypothesis beyond those of the general statement.

## References

* [Stacks Project, Tag 06MJ](https://stacks.math.columbia.edu/tag/06MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A property of schemes local for both the étale and the fppf precoverage passes from the
source of a surjective, flat morphism of algebraic spaces locally of finite presentation to
its target. -/
theorem hasEtaleLocalProperty_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] [P.IsLocal Scheme.fppfPrecoverage]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hflat : IsFlat B S hS f)
    (hsurj : IsSurjective B S hS f)
    (hP : HasEtaleLocalProperty B S hS X P) :
    HasEtaleLocalProperty B S hS Y P := by
  let T := BigFppfOver.toScheme B S hS
  refine (exists_atlas_iff_forall_etale B S hS Y P hY).mpr fun V b hb => ?_
  obtain ⟨U, a, h, haE, hcomm, -, hhsurj⟩ :=
    exists_etale_chart_square_over B S hS hX hY f V b hb
  have : Surjective (T.map h) := hhsurj hsurj
  have : Flat (T.map h) := hflat U V a b h haE hb hcomm
  have : LocallyOfFinitePresentation (T.map h) := hfp U V a b h haE hb hcomm
  exact P.of_presieve (Scheme.Hom.singleton_mem_fppfPrecoverage (T.map h)) fun _ _ ⟨⟩ =>
    (exists_atlas_iff_forall_etale B S hS X P hX).mp hP U a haE

/-- **Stacks 06MJ.** Local Noetherianity passes from the source of a surjective, flat
morphism of algebraic spaces over `S` locally of finite presentation to its target.

This is the case `P = AlgebraicGeometry.IsLocallyNoetherian` of
`hasEtaleLocalProperty_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation`, whose two
locality hypotheses hold for local Noetherianity of schemes. -/
@[stacks 06MJ]
theorem isLocallyNoetherian_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hflat : IsFlat B S hS f)
    (hsurj : IsSurjective B S hS f)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation B S hS
    (fun T : Scheme.{u} => IsLocallyNoetherian T) hX hY f hfp hflat hsurj hnoeth

end AlgebraicGeometry.Space

end
