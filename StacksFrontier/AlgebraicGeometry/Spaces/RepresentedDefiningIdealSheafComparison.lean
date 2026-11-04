module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.SectionwiseKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# The ideal sheaf of a closed subspace on a chart, against the scheme-level ideal sheaf

Let `Z ⊆ X` be a closed subspace of an algebraic space over a scheme `S` contained in a big fppf
site `B`, and let `A` be an étale scheme chart of `X`.  Base changing the closed immersion
`Z ⟶ X` along `A ⟶ X` gives a closed immersion of schemes `Z ×_X A ⟶ A`, and that morphism has
a defining ideal sheaf on the **Zariski** site of `A` —
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom`, the sectionwise kernel of
pullback of regular functions.  On the other side, `AlgebraicGeometry.Space.definingIdealSheaf`
of Stacks 03MB is a sheaf of ideals of `𝒪_X` on the **small étale** site of `X`.  This file
identifies the two on sections: over an affine open `V` of the chart, the ideal the Zariski site
assigns to `V` is the ideal the small étale site assigns to the étale chart that `V` cuts out.

## Main results

* `AlgebraicGeometry.Space.definingIdealOfHom_obj_eq_openChartIdeal`: **the two ideals agree over
  every affine open of every étale chart.**
* `AlgebraicGeometry.Space.definingIdealOfHom_obj_selfChart_eq_openChartIdeal`: the same read at
  the identity chart of a representable algebraic space, where the base-changed closed immersion
  is the representing closed immersion of schemes.
* `AlgebraicGeometry.Space.isQuasicoherent_definingIdealOfHom`: the defining ideal sheaf of a
  closed immersion of schemes is quasi-coherent.

## Implementation notes

Both identifications are read through Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData`, which
is the only object the two levels have in common.  On the space side
`AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart` says that the `IdealSheafData`
assembled from the sections of `definingIdealSheaf` over the étale charts cut out by the affine
opens of `A` — `AlgebraicGeometry.Space.idealSheafDataOfChart` — is
`AlgebraicGeometry.Scheme.Hom.ker` of the base-changed closed immersion; on the scheme side
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom_obj_eq_ker` says that the
sectionwise kernel has the same component.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
-/


@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The defining ideal sheaf of a closed immersion of schemes is quasi-coherent.** -/
theorem isQuasicoherent_definingIdealOfHom {Z U : Scheme.{u}} (j : Z ⟶ U)
    [_root_.AlgebraicGeometry.IsClosedImmersion j] :
    SheafOfModules.IsQuasicoherent
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom j).toSheafOfModules :=
  CategoryTheory.ObjectProperty.prop_of_iso
    (SheafOfModules.isQuasicoherent
      (structureSheafRing U.toLocallyRingedSpace.toRingedSpace))
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso j).symm
    (Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf j)

/-- **The ideal the Zariski site of an étale chart assigns to an affine open is the ideal the
small étale site of the algebraic space assigns to the chart that open cuts out.**  For a closed
subspace `Z ⊆ X` and an étale scheme chart `A` of `X`, the sections over an affine open `V` of
`A` of the defining ideal sheaf of the base-changed closed immersion `Z ×_X A ⟶ A` are the
sections of `AlgebraicGeometry.Space.definingIdealSheaf` over the étale chart `V ⟶ X`, read
through `AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem definingIdealOfHom_obj_eq_openChartIdeal (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).affineOpens) :
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom))).obj (op V.1) =
      openChartIdeal B S hS X (definingIdealSheaf B S hS X Z) A V.1 := by
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)) :=
    Z.2.2.property A.1.hom _ _ (Z.2.2.rep.isPullback A.1.hom)
  exact (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom_obj_eq_ker _ V).trans
    (congrArg (fun J : (chartScheme A).IdealSheafData => J.ideal V)
      (ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z A))

/-- **The comparison at the identity chart of a representable algebraic space.**  For a closed
subspace `Z` of `yoneda.obj U`, the defining ideal sheaf of the representing closed immersion of
schemes — the base change of `Z ⟶ yoneda.obj U` along the identity chart — has over every affine
open of the representing scheme the sections that `AlgebraicGeometry.Space.definingIdealSheaf`
has over the étale chart that open cuts out. -/
theorem definingIdealOfHom_obj_selfChart_eq_openChartIdeal (U : BigFppfOver B S hS)
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (Z : ClosedSubspaces B S hS (yoneda.obj U))
    (V : (chartScheme (selfChart B S hS U)).affineOpens) :
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
        ((BigFppfOver.toScheme B S hS).map
          (Z.2.2.rep.snd (selfChart B S hS U).1.hom))).obj (op V.1) =
      openChartIdeal B S hS (⟨yoneda.obj U, hU⟩ : AlgebraicSpaces B S hS)
        (definingIdealSheaf B S hS (⟨yoneda.obj U, hU⟩ : AlgebraicSpaces B S hS) Z)
        (selfChart B S hS U) V.1 :=
  definingIdealOfHom_obj_eq_openChartIdeal B S hS
    (⟨yoneda.obj U, hU⟩ : AlgebraicSpaces B S hS) Z (selfChart B S hS U) V

end AlgebraicGeometry.Space

end
