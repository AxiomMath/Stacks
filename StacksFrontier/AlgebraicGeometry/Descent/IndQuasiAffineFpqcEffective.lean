module

public import StacksFrontier.AlgebraicGeometry.Descent.DescendingTypesOfMorphismsGeneralBase
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumLegsPreimage
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFamilyEffective
public import StacksFrontier.AlgebraicGeometry.Descent.RestrictOpenDescended
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Gabber's theorem: effective fpqc descent for ind-quasi-affine morphisms

Let `S` be a scheme, let `{X i ⟶ S}` be an fpqc covering family and let `D` be a descent datum
relative to that family, in the sense of Stacks 023W, each of whose component morphisms
`V i ⟶ X i` is ind-quasi-affine. Then `D` is effective in the sense of Stacks 02VU. This is
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK).

The three obligations of
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` are discharged:
`hlegs` by `AlgebraicGeometry.DescentDatum.preimage_specMap_legs_subsetΓSpecImage`, `hrestrict` by
`AlgebraicGeometry.DescentDatum.isEffective_restrictOpen_descentInvariants`, and `hglueing` —
[Stacks, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4) — by
`AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_restrictOpen`. That gives the
single-chart case, for a surjective flat morphism of affine schemes. The passage from there to an
arbitrary fpqc covering family of an arbitrary base is
`AlgebraicGeometry.DescentData.isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex`, the fpqc
case of [Stacks, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3) over an arbitrary base.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom`: every descent datum with
  ind-quasi-affine component relative to a surjective flat morphism of affine schemes is
  effective.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom_of_anyIndex`:
  **Stacks 0APK**, for an arbitrary base scheme and an arbitrary fpqc covering family of it.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom`: the same over
  an affine base, for a covering family indexed in the universe of the schemes.

## Implementation notes

*The base is not assumed affine.* The reduction of Stacks 02W3 consumed here is the general-base
one, `AlgebraicGeometry.DescentData.isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex` of
`StacksFrontier.AlgebraicGeometry.Descent.DescendingTypesOfMorphismsGeneralBase`, which glues the
schemes descended over the affine opens of the base along
[Stacks, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH). Its two hypotheses on the property
of the component morphisms are stability under base change, which is Stacks 0AP7 in the form of
the instance `AlgebraicGeometry.isIndQuasiAffineHom_isStableUnderBaseChange`, and closure under
finite disjoint unions, which is `AlgebraicGeometry.isIndQuasiAffineHom_sigmaMap`; its remaining
hypothesis is exactly the single-chart case proved here. So nothing beyond the affine-chart case
separates this file from the tag, and the affine-base statement is kept only because it is the
shape some consumers take.

*The index type of the covering family is in an arbitrary universe*, matching the source, whose
covering families are indexed by a set.

*Quasi-compactness is not a hypothesis.* The residue statement asks for `[QuasiCompact g]`, which
for a morphism between affine schemes is an instance, through
`AlgebraicGeometry.isAffineHom_of_isAffine`.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 0AP7](https://stacks.math.columbia.edu/tag/0AP7)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

namespace DescentDatum

/-- **The affine-chart case of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK).**
Every descent datum relative to a surjective flat morphism of affine schemes whose scheme over the
source is ind-quasi-affine is effective. -/
@[sga "1 VIII 7.9" "special case", sga "3 X 5.4" "special case"]
theorem isEffective_of_isIndQuasiAffineHom {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (g : T' ⟶ T) (hsurj : Surjective g) (hflat : Flat g) (D : DescentDatum g)
    (hiqa : IsIndQuasiAffineHom (D.obj ()).hom) :
    DescentData.IsEffective D := by
  refine isEffective_of_legs_of_restrictOpen_of_isAffine ?_ ?_ g hsurj hflat D hiqa
  · intro T T' g D _ _ _ _ _ _ E I _ U hU hE hEinv W hWinv hWE
    exact preimage_specMap_legs_subsetΓSpecImage D E U hU hE hEinv W hWinv hWE
  · intro T T' g D _ _ _ _ _ _ E _ _ _ _ hRA hRC hAC _ I _ U hU hE h₁ h₂ W hWinv hWE W₀ hW₀
    exact isEffective_restrictOpen_descentInvariants D E W hWinv hWE h₁ h₂ U hU hE hRC hRA hAC
      W₀ hW₀

end DescentDatum

namespace DescentData

/-- **[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), Gabber's theorem.** Let `S`
be a scheme, let `{X i ⟶ S}` be an fpqc covering family, indexed by a type in an arbitrary
universe, and let `D` be a descent datum relative to it each of whose component morphisms
`V i ⟶ X i` is ind-quasi-affine. Then `D` is effective: it is isomorphic to the canonical descent
datum of a scheme over `S`.

Ind-quasi-affineness is stable under base change, Stacks 0AP7, and closed under finite disjoint
unions, so the general-base fpqc reduction of Stacks 02W3,
`AlgebraicGeometry.DescentData.isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex`, reduces
the statement to the case of a surjective flat morphism of affine schemes, which is
`AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom`. -/
@[stacks 0APK,
  sga "1 VIII 7.9" "partial",
  sga "3 IX 2.3" "partial",
  sga "3 VIII 1.7.2" "more general",
  sga "3 X 5.4" "more general",
  sga "3 XI 4.2" "partial",
  sga "3 XXIV 3.11.2" "partial"]
theorem isFamilyEffective_of_forall_isIndQuasiAffineHom_of_anyIndex {ι : Type v} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f) (hP : ∀ i, IsIndQuasiAffineHom (D.obj i).hom) :
    D.IsFamilyEffective :=
  isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex (P := @IsIndQuasiAffineHom)
    (fun a ha ↦ isIndQuasiAffineHom_sigmaMap a ha)
    (fun a hsurj hflat E hPE ↦
      DescentDatum.isEffective_of_isIndQuasiAffineHom a hsurj hflat E hPE)
    f hf D hP

/-- **[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) over an affine base.** Let `S`
be an affine scheme, let `{X i ⟶ S}` be an fpqc covering family and let `D` be a descent datum
relative to it each of whose component morphisms is ind-quasi-affine. Then `D` is effective: it is
isomorphic to the canonical descent datum of a scheme over `S`.

This is the special case of
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom_of_anyIndex` kept
for the consumers taking this shape. -/
@[stacks 0APK "the case of an affine base",
  sga "1 VIII 7.9" "special case",
  sga "3 IX 2.3" "partial",
  sga "3 VIII 1.7.2" "(ii), special case",
  sga "3 X 5.4" "special case",
  sga "3 XXIV 3.11.2" "partial"]
theorem isFamilyEffective_of_forall_isIndQuasiAffineHom {ι : Type u} {S : Scheme.{u}} [IsAffine S]
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f) (hP : ∀ i, IsIndQuasiAffineHom (D.obj i).hom) :
    D.IsFamilyEffective :=
  isFamilyEffective_of_forall_isIndQuasiAffineHom_of_anyIndex f hf D hP

end DescentData

end AlgebraicGeometry

end

end
