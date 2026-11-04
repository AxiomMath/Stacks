module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

/-!
# Descending regularity along a flat surjection of algebraic spaces

Regularity of an algebraic space is the étale-local scheme property
`AlgebraicGeometry.IsRegular` in the sense of Stacks 03E6. It passes from the source of a flat
surjective morphism of algebraic spaces to its target, provided the target is already known to
be locally Noetherian.

## Main results

* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat` is the
  descent statement with local Noetherianity of the target assumed.
* `hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation`,
  in the same namespace, is the form in which local Noetherianity of the target is deduced
  rather than assumed, at the cost of assuming the morphism locally of finite presentation.

## Implementation notes

A regular scheme is a locally Noetherian scheme all of whose local rings are regular, which is
`AlgebraicGeometry.isRegular_tfae`. Local Noetherianity of the target is a hypothesis; what is
proved here is regularity of the local rings. Lifting an étale chart `b` of the target to an
étale chart `a` of the source makes the morphism of schemes between the two charts flat and
surjective, so every local ring of the chart of the target receives a flat local homomorphism
from a regular local ring of the chart of the source, and
`IsRegularLocalRing.of_flat_of_isLocalHom` applies.

Local finite presentation of the morphism is not needed for this implication: it is needed
only to obtain local Noetherianity of the target, which in the first statement is a
hypothesis and in the second is supplied by Stacks 06MJ,
`isLocallyNoetherian_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation`, applied to
the chart-level Noetherianity extracted from regularity of the source.

Étale locality of the two scheme properties involved, which turns the some-chart condition of
`AlgebraicGeometry.Space.HasEtaleLocalProperty` into an every-chart one by Stacks 03E8, comes
from `AlgebraicGeometry.isRegular_isLocal_etale` and
`AlgebraicGeometry.isLocallyNoetherian_isLocal_etale`; neither is a hypothesis.

## References

* [Stacks Project, Tag 06MK](https://stacks.math.columbia.edu/tag/06MK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Regularity passes from the source of a flat surjective morphism of algebraic spaces over
`S` to its target, provided the target is locally Noetherian. -/
theorem hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hflat : IsFlat B S hS f)
    (hsurj : IsSurjective B S hS f)
    (hYnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T)) :
    HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsRegular T) := by
  let T := BigFppfOver.toScheme B S hS
  have hXall :=
    (exists_atlas_iff_forall_etale B S hS X (fun Z : Scheme.{u} => IsRegular Z) hX).mp hreg
  have hYnoethAll :=
    (exists_atlas_iff_forall_etale B S hS Y
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z) hY).mp hYnoeth
  refine (exists_atlas_iff_forall_etale B S hS Y
    (fun Z : Scheme.{u} => IsRegular Z) hY).mpr ?_
  intro V b hb
  obtain ⟨U, a, h, haE, hcomm, -, hhsurj⟩ :=
    exists_etale_chart_square_over B S hS hX hY f V b hb
  have hhSurj : Surjective (T.map h) := hhsurj hsurj
  have hhFlat : Flat (T.map h) := hflat U V a b h haE hb hcomm
  have hVnoeth : IsLocallyNoetherian (T.obj V) := hYnoethAll V b hb
  refine ((isRegular_tfae (T.obj V)).out 1 2 rfl rfl).mpr ⟨hVnoeth, fun y => ?_⟩
  obtain ⟨x, hxy⟩ := hhSurj.surj y
  let R := (T.obj V).presheaf.stalk ((T.map h).base x)
  let Q := (T.obj U).presheaf.stalk x
  let _ : Algebra R Q := ((T.map h).stalkMap x).hom.toAlgebra
  let _ : Module.Flat R Q := RingHom.flat_algebraMap_iff.mpr (Flat.stalkMap (T.map h) x)
  let _ : IsLocalHom (algebraMap R Q) := (T.map h).toLRSHom.prop x
  let _ : IsRegularLocalRing Q :=
    (((isRegular_tfae (T.obj U)).out 1 2 rfl rfl).mp (hXall U a haE)).2 x
  exact hxy ▸ (IsRegularLocalRing.of_flat_of_isLocalHom Q : IsRegularLocalRing R)

/-- **Stacks 06MK.** Regularity passes from the source of a surjective, flat morphism of
algebraic spaces over `S` locally of finite presentation to its target.

A regular scheme is locally Noetherian, so a regular étale chart of the source witnesses local
Noetherianity of the source; Stacks 06MJ carries that to the target, and
`hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat` then applies. -/
@[stacks 06MK,
  stacks 06QN "the same statement in the descent chapter",
  sga "1 I 9.2" "converse (X reg ⇒ Y reg)"]
theorem hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hflat : IsFlat B S hS f)
    (hsurj : IsSurjective B S hS f)
    (hreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T)) :
    HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsRegular T) := by
  obtain ⟨A, a, haSurj, haEtale, haReg⟩ := hreg
  have hXnoeth : HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    ⟨A, a, haSurj, haEtale,
      (((isRegular_tfae ((BigFppfOver.toScheme B S hS).obj A)).out 1 2 rfl rfl).mp haReg).1⟩
  exact hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat B S hS hX hY f hflat hsurj
    (isLocallyNoetherian_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation B S hS
      hX hY f hfp hflat hsurj hXnoeth)
    ⟨A, a, haSurj, haEtale, haReg⟩

end AlgebraicGeometry.Space

end
