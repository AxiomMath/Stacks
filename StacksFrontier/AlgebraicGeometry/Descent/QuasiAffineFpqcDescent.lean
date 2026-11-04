module

public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcEffective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Morphisms.SigmaMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.QuasiAffineAndImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending quasi-affine morphisms along an fpqc covering

**Stacks 0247.** Let `S` be a scheme, let `{X i ⟶ S}` be an fpqc covering family, indexed by a
type in an arbitrary universe, and let `D` be a descent datum relative to that family, in the
sense of Stacks 023W, each of whose component morphisms `V i ⟶ X i` is quasi-affine. Then `D` is
effective in the sense of Stacks 02VU: it is isomorphic to the canonical descent datum of a
scheme over `S`.

## Main results

* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isQuasiAffineHom`: **Stacks 0247**, for an
  arbitrary scheme `S`, an arbitrary fpqc covering family of it indexed by a type in an
  arbitrary universe, and an arbitrary descent datum relative to it with quasi-affine
  components.

## Implementation notes

The proof is the one of the source. Quasi-affineness is preserved under arbitrary base change,
Stacks 01SO (the instance `AlgebraicGeometry.isQuasiAffineHom_isStableUnderBaseChange`), and it
is Zariski local on the target (`AlgebraicGeometry.isQuasiAffineHom_isZariskiLocalAtTarget`, part
of Stacks 01SM), hence closed under finite disjoint unions
(`AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap`). So the general-base fpqc reduction of
Stacks 02W3, `AlgebraicGeometry.DescentData.isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex`,
applies, and it suffices to treat a covering given by a single surjective flat morphism of affine
schemes.

The source proves that affine-chart case from the affine hull: a quasi-affine `V ⟶ X = Spec A`
is a quasi-compact open immersion into `W = Spec Γ(V, ⊤)` (Stacks 01SM), flat base change
(Stacks 02KH) turns the gluing isomorphism of `V` into one of the affine scheme `W`, effective
descent for affine morphisms (Stacks 0245) descends `W` to an affine `U' ⟶ S` (Stacks 02L5), and
`V` is a quasi-compact open of `X ×_S U'` stable under the descent datum, hence the preimage of an
open `U ⊆ U'` (Stacks 02JY). This development already carries out that argument, in the greater
generality Gabber's theorem needs, as
`AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom`: there `V` is only
ind-quasi-affine and the single quasi-compact open `V ⊆ Spec Γ(V, ⊤)` is replaced by a filtered
family of them. A quasi-affine morphism is ind-quasi-affine
(`AlgebraicGeometry.isIndQuasiAffineHom_of_isQuasiAffineHom`, Stacks 0F1W), and at a quasi-affine
`V` that argument runs exactly the source's with the family a single member, so the affine-chart
case is taken from it rather than proved a second time. The source's proof of Stacks 0APK cites
02W3 and 0245, not 0247, so there is no circularity.

*Relation to the surjective-étale statement of the same tag.*
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom` of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent` proves effective descent of
quasi-affine morphisms along a surjective étale morphism of one big fppf site, for morphisms of
presheaves. The statement below is the tag itself, about descent data of schemes relative to an
arbitrary fpqc covering.

## References

* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 01SO](https://stacks.math.columbia.edu/tag/01SO)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02JY](https://stacks.math.columbia.edu/tag/02JY)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0F1W](https://stacks.math.columbia.edu/tag/0F1W)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

namespace DescentData

/-- **[Stacks, Tag 0247](https://stacks.math.columbia.edu/tag/0247).** Let `S` be a scheme, let
`{X i ⟶ S}` be an fpqc covering family, indexed by a type in an arbitrary universe, and let `D`
be a descent datum relative to it each of whose component morphisms `V i ⟶ X i` is quasi-affine.
Then `D` is effective: it is isomorphic to the canonical descent datum of a scheme over `S`.

Quasi-affineness is stable under arbitrary base change (Stacks 01SO) and, being Zariski local on
the target, closed under finite disjoint unions, so the general-base fpqc reduction of Stacks
02W3, `AlgebraicGeometry.DescentData.isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex`,
reduces the statement to a covering given by a single surjective flat morphism of affine schemes.
That case is the affine-hull argument of
`AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom`, applied to a quasi-affine,
hence ind-quasi-affine (Stacks 0F1W), morphism. -/
@[stacks 0247,
  sga "1 VIII 7.9" "partial",
  sga "3 IV 4.7" "partial",
  sga "3 IX 2.3" "Effectivity clause",
  sga "3 VIII 1.7.2" "more general",
  sga "3 X 5.4" "special case",
  sga "3 XXIV 3.11.2" "partial"]
theorem isFamilyEffective_of_isQuasiAffineHom {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f) (hD : ∀ i, IsQuasiAffineHom (D.obj i).hom) :
    D.IsFamilyEffective :=
  have := isQuasiAffineHom_isZariskiLocalAtTarget.{u}
  isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex (P := @IsQuasiAffineHom)
    (fun g hg ↦ IsZariskiLocalAtTarget.sigmaMap g hg)
    (fun a hsurj hflat E hE ↦
      DescentDatum.isEffective_of_isIndQuasiAffineHom a hsurj hflat E (have := hE; inferInstance))
    f hf D hD

end DescentData

end AlgebraicGeometry

end

end
