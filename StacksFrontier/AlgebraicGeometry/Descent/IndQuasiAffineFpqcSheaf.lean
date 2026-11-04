module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcLocalFromDescentData
public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcLocalFromLegsResidue
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumLegsPreimage
public import StacksFrontier.AlgebraicGeometry.Descent.RestrictOpenDescended
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Algebraic spaces are fpqc sheaves, and affineness is fpqc local on the base

`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_legs_of_restrictOpen` and
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_legs_of_restrictOpen` reduce
[Stacks, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z) and
[Stacks, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL) to the three obligations `hlegs`,
`hrestrict` and `hglueing` of
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen`, quantified over every
surjective flat quasi-compact morphism of **affine** schemes. All three are now available:

* `hlegs` is `AlgebraicGeometry.DescentDatum.preimage_specMap_legs_subsetΓSpecImage`;
* `hrestrict` is `AlgebraicGeometry.DescentDatum.isEffective_restrictOpen_descentInvariants`;
* `hglueing` is `AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_restrictOpen`, which
  is [Stacks, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4).

So both conclusions hold outright, for an arbitrary base scheme `S`: the reduction asks for the
effectivity of ind-quasi-affine descent data only along morphisms of affine schemes, which is the
case of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) that
`AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom` proves.

## Main results

* `AlgebraicGeometry.Space.isLocalAtTarget_isAffineHom_fpqc`: **Stacks 041Z** — affineness of
  morphisms of algebraic spaces is fpqc local on the base.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc`: **Stacks 0APL** — an algebraic space is a
  sheaf for the fpqc topology.
* `AlgebraicGeometry.Space.isEffectiveAffineDescentAlongFpqc`: effective descent for affine
  morphisms along a finite fpqc covering of an affine object of the site, **with no hypothesis**.

## Implementation notes

*The named hypothesis is discharged here.*
`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc` of
`StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal` is carried as an undischarged
hypothesis in several places in this development.
`AlgebraicGeometry.Space.isEffectiveAffineDescentAlongFpqc_of_isSheaf_fpqc` of
`StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcChartDescent` reduces it to Stacks 0APL, whose
statement is exactly that file's hypothesis `hAPL`; and
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc` above *is* Stacks 0APL, at the same universe
and in the same spelling, so no transport is needed and the composition is immediate. It is
recorded here rather than in `AffineFpqcChartDescent` because this is the file where 0APL
becomes available: the import goes that way round.

No `@[stacks 0245]` attribute is attached. The source statement quantifies over an arbitrary
fpqc covering of a scheme and an arbitrary descent datum for it, whereas what is obtained here
is the one special shape its consumers in this development use — a *finite* covering of an
*affine* object of the site by affine objects, with the conclusion read as representability of a
base change by an affine object. That shape does not imply the tag.

*Why no affineness of the base appears.* The reduction
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_affine_indQuasiAffine`
quantifies its hypothesis over surjective flat quasi-compact morphisms of affine schemes only, so
the affine-base case of Stacks 0APK suffices; the restriction recorded in
`StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcEffective` does not propagate here.

## References

* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

namespace Space

/-- **Affineness of morphisms of algebraic spaces is fpqc local on the base**, which is
[Stacks, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z). -/
@[stacks 041Z]
theorem isLocalAtTarget_isAffineHom_fpqc (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, v} B S hS) := by
  refine isAffineHom_isLocalAtTarget_fpqc_of_legs_of_restrictOpen B S hS ?_ ?_ ?_
  · intro T T' g D _ _ _ _ _ _ E I _ U hU hE hEinv W hWinv hWE
    exact DescentDatum.preimage_specMap_legs_subsetΓSpecImage D E U hU hE hEinv W hWinv hWE
  · intro T T' g D _ _ _ _ _ _ E _ _ _ _ hRA hRC hAC _ I _ U hU hE h₁ h₂ W hWinv hWE W₀ hW₀
    exact DescentDatum.isEffective_restrictOpen_descentInvariants D E W hWinv hWE h₁ h₂ U hU hE
      hRC hRA hAC W₀ hW₀
  · intro T T' g D _ _ _ _ _ _ h
    exact DescentDatum.isEffective_of_forall_exists_restrictOpen D h

end Space

namespace IsAlgebraicSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}}
variable {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An algebraic space is a sheaf for the fpqc topology**, which is
[Stacks, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL). -/
@[stacks 0APL]
theorem isSheaf_fpqc (hF : IsAlgebraicSpace B S hS F) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F := by
  refine isSheaf_fpqc_of_legs_of_restrictOpen hF ?_ ?_ ?_
  · intro T T' g D _ _ _ _ _ _ E I _ U hU hE hEinv W hWinv hWE
    exact DescentDatum.preimage_specMap_legs_subsetΓSpecImage D E U hU hE hEinv W hWinv hWE
  · intro T T' g D _ _ _ _ _ _ E _ _ _ _ hRA hRC hAC _ I _ U hU hE h₁ h₂ W hWinv hWE W₀ hW₀
    exact DescentDatum.isEffective_restrictOpen_descentInvariants D E W hWinv hWE h₁ h₂ U hU hE
      hRC hRA hAC W₀ hW₀
  · intro T T' g D _ _ _ _ _ _ h
    exact DescentDatum.isEffective_of_forall_exists_restrictOpen D h

end IsAlgebraicSpace

namespace Space

/-- **Effective descent for affine morphisms along an fpqc covering of an affine object of the
site, with no hypothesis.**

`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc` is the named hypothesis that several
results of this development carry undischarged; this discharges it.
`AlgebraicGeometry.Space.isEffectiveAffineDescentAlongFpqc_of_isSheaf_fpqc` proves it from the
assumption that every algebraic space over `S` is a sheaf for the fpqc topology of the big fppf
site of `S`, and that assumption is the statement of Stacks 0APL, which
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc` proves outright.

The `@[stacks 0245]` attribute is **not** attached, and this is not Stacks 0245. That tag asserts
effectivity of an arbitrary descent datum for an arbitrary fpqc covering of a scheme whose
components are affine over their members; what is obtained here is the restricted shape its
consumers in this development use — a finite covering of an affine object of the site by affine
objects, with the conclusion read as representability of a base change by an affine object of the
site — which does not imply it. -/
@[ega "IV 2.7.1" "(xiii), special case"]
theorem isEffectiveAffineDescentAlongFpqc (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsEffectiveAffineDescentAlongFpqc B S hS :=
  isEffectiveAffineDescentAlongFpqc_of_isSheaf_fpqc B S hS
    fun hF => hF.isSheaf_fpqc

end Space

end AlgebraicGeometry

end
