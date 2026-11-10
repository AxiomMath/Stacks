module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullbackSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactKernelQuasicoherent
import all StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage

/-!
# Supplement to `ChartIdealSheafPreimage`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `kernelIdealSheaf_obj_eq_ker`
* `ker_rep_snd_eq_ofIdealTop_kernelIdealSheaf`
* `ker_rep_snd_eq_idealSheafDataOfChart_kernelIdealSheaf`
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sections of the kernel ideal sheaf of a representable morphism over an étale chart
are the kernel of pullback of regular functions along the canonical base change.**  This is
`AlgebraicGeometry.Space.ker_structureSharp_eq` read through
`AlgebraicGeometry.Space.chartPullbackRingHom_chartBaseChangeArrow`, and it is the general form
of `AlgebraicGeometry.Space.definingIdealAt_eq_ker`. -/
theorem kernelIdealSheaf_obj_eq_ker {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (U : SmallEtale B S hS X.1) :
    (kernelIdealSheaf B S hS i).obj (op U) =
      RingHom.ker (Scheme.Γ.map
        ((BigFppfOver.toScheme B S hS).map (hi.snd U.1.hom)).op).hom :=
  (ker_structureSharp_eq B S hS i hi U).trans
    (congrArg RingHom.ker (chartPullbackRingHom_chartBaseChangeArrow B S hS i hi U))

/-- **On an affine étale chart the ideal sheaf of the base change of a closed immersion is the
ideal sheaf of the ideal of sections of its kernel ideal sheaf there.**  The general form of
`AlgebraicGeometry.Space.ker_rep_snd_eq_ofIdealTop_definingIdealAt`. -/
theorem ker_rep_snd_eq_ofIdealTop_kernelIdealSheaf {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (U : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)] :
    ((BigFppfOver.toScheme B S hS).map (hi.rep.snd U.1.hom)).ker =
      Scheme.IdealSheafData.ofIdealTop ((kernelIdealSheaf B S hS i).obj (op U)) := by
  rw [Scheme.ker_of_isAffine, kernelIdealSheaf_obj_eq_ker B S hS i hi.rep U, Scheme.Γ_map_op]
  rfl

/-- **The sheaf of ideals that the kernel ideal sheaf of a closed immersion induces on an étale
chart is the ideal sheaf of the base change of that immersion to the chart.**

This is the general form of
`AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`, with the same proof: the two
ideal sheaves are compared over an affine open `V` of the chart scheme, where the right-hand
side is the ideal of sections of the kernel ideal sheaf over the étale chart `V` of `X`
transported along `AlgebraicGeometry.Scheme.Opens.topIso`, and the left-hand side restricts to
the ideal sheaf of the base change of `i` to `V`. -/
theorem ker_rep_snd_eq_idealSheafDataOfChart_kernelIdealSheaf {Z X : AlgebraicSpaces B S hS}
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) (A : SmallEtale B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.1.hom)).ker =
      idealSheafDataOfChart B S hS X (kernelIdealSheaf B S hS i)
        (isCartesianOnAffineCharts_kernelIdealSheaf B S hS i
          (isQuasiCompact_of_isClosedImmersion' B S hS hi)) A := by
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (openChart B S hS X.1 A V.1).1.left) := V.2
  have hTop : IsAffineOpen (⊤ : ((BigFppfOver.toScheme B S hS).obj
      (openChart B S hS X.1 A V.1).1.left).Opens) := isAffineOpen_top _
  have haff : ((BigFppfOver.toScheme B S hS).map
        (hi.rep.snd (openChart B S hS X.1 A V.1).1.hom)).ker =
      Scheme.IdealSheafData.ofIdealTop
        ((kernelIdealSheaf B S hS i).obj (op (openChart B S hS X.1 A V.1))) :=
    ker_rep_snd_eq_ofIdealTop_kernelIdealSheaf B S hS i hi (openChart B S hS X.1 A V.1)
  have hcomap : ((BigFppfOver.toScheme B S hS).map
        (hi.rep.snd (openChart B S hS X.1 A V.1).1.hom)).ker =
      (((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.1.hom)).ker).comap V.1.ι := by
    have h := schemeKer_snd_comp_of_isClosedImmersion B S hS i hi A.1.hom
      (openSubHom A.1.left V.1)
    have e : (BigFppfOver.toScheme B S hS).map (openSubHom A.1.left V.1) = V.1.ι :=
      toScheme_map_openSubHom B S hS _ V.1
    rw [e] at h
    exact h
  have hsec : (kernelIdealSheaf B S hS i).obj (op (openChart B S hS X.1 A V.1)) =
      Ideal.map (V.1.topIso.inv.hom)
        ((((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.1.hom)).ker).ideal V) := by
    refine (Stacks.Divisors.ideal_ofIdealTop_top hTop _).symm.trans ?_
    refine (congrArg (fun J => Scheme.IdealSheafData.ideal J ⟨⊤, hTop⟩)
      (haff.symm.trans hcomap)).trans ?_
    refine Eq.trans (Stacks.IdealSheaf.ideal_comap_appLE
      (((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.1.hom)).ker) V.1.ι V
      ⟨⊤, hTop⟩ V.1.ι_preimage_self.ge) ?_
    exact congrArg (fun φ => Ideal.map (CommRingCat.Hom.hom φ) _)
      (appLE_ι_top_eq_topIso_inv V.1)
  change (((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.1.hom)).ker).ideal V =
    Ideal.map (openChartTopRingHom B S hS X A V.1)
      ((kernelIdealSheaf B S hS i).obj (op (openChart B S hS X.1 A V.1)))
  rw [hsec]
  exact (map_topIso_hom_map_topIso_inv V.1 _).symm

variable {B S hS}

end Space

end AlgebraicGeometry

end
