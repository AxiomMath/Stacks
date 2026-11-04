module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleLocal
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveComposition
import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition

/-!
# A jointly rig-surjective family composed with a rig-surjective morphism

Let `S` be a scheme contained in a big fppf site `B`, let `p : X ⟶ V` be a rig-surjective
morphism of formal algebraic spaces over `S` and let `{uⱼ : Uⱼ ⟶ X}` be a family of morphisms
which is jointly rig-surjective in the sense of
`AlgebraicGeometry.FormalSpace.IsJointlyRigSurjective`. Then the composed family
`{uⱼ ≫ p : Uⱼ ⟶ V}` is jointly rig-surjective.

## Main results

* `AlgebraicGeometry.FormalSpace.IsJointlyRigSurjective.comp_of_isRigSurjective`: the family
  form of the lifting mechanism of **Stacks 0AQR**.

## Implementation notes

This is the family analogue of `AlgebraicGeometry.FormalSpace.IsRigSurjective.comp`, this
library's Stacks 0AQR, and it is proved the same way: an adic point `Spf R ⟶ V` lifts through
`p` over an extension `R ⊂ R'` of complete discrete valuation rings, that lift is again adic, and
joint rig-surjectivity of the family carries it into one member `Uⱼ` over a further extension
`R' ⊂ R''`; the two extensions compose to the single extension the definition asks for.

Unlike Stacks 0AQR, no local finiteness of type is needed. Stacks 0AQR assumes it of both
factors only to conclude that the composite is locally of finite type; the lifting argument
itself does not use it, and the conclusion here is about lifting alone.

Adicness of the intermediate lift is the one step which is not bookkeeping: the definition of
rig-surjectivity produces a lift `Spf R' ⟶ X` but does not record that it is adic, whereas
feeding it to the second lifting step requires exactly that. It is
`isRepresentableByAlgebraicSpacesULift_of_comp_eq_formalSpectrumMap_comp`, which is why `hX` —
that the common target of the family is a formal algebraic space — appears: that is what
Stacks 0AQ0 asks of the source of `p` in order to cancel `p` off the representable composite
`Spf R' ⟶ Spf R ⟶ V`.

### Where this is used

This is the first geometric step of the source's proof of **Stacks 0GH6**, the descent of
rig-smoothness along a rig-surjective morphism. That proof fixes an affine étale chart square
over `g`, forms `X ×_Y V ⟶ V`, which is rig-surjective, takes an affine étale covering of
`X ×_Y V` as in Definition 0AIM, and then lifts an adic point of `V` out of a complete discrete
valuation ring into one member `Spf A` of that covering. The composite of those two liftings is
this lemma, applied to the covering of `X ×_Y V` and to `X ×_Y V ⟶ V`.

What that argument additionally needs, and this lemma does not supply, is joint
rig-surjectivity of the covering itself. That is the family form of **Stacks 0AQU**,
`FormalSpace.isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective`
in `StacksFrontier.AlgebraicGeometry.FormalSpace.JointlyRigSurjectiveEtalePoint`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQR](https://stacks.math.columbia.edu/tag/0AQR)
* [Stacks Project, Tag 0AQU](https://stacks.math.columbia.edu/tag/0AQU)
* [Stacks Project, Tag 0GH6](https://stacks.math.columbia.edu/tag/0GH6)
-/


@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u v

/-- A jointly rig-surjective family stays jointly rig-surjective after composition with a
rig-surjective morphism: an adic point of the final target lifts through the rig-surjective
morphism over an extension of complete discrete valuation rings, that lift is again adic, and so
lifts into one member of the family over a further extension; the two extensions compose to one.

This is the family analogue of Stacks 0AQR, and the first geometric step of the source's proof
of Stacks 0GH6 — there the family is an affine étale covering of `X ×_Y V` and the
rig-surjective morphism is `X ×_Y V ⟶ V`.

The hypothesis `hX` is what Stacks 0AQ0 asks in order to see that the intermediate lift is
adic; Stacks 0AQR assumes it of the same space, the common target of the family. -/
theorem IsJointlyRigSurjective.comp_of_isRigSurjective (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {J : Type v} {U : J → FppfSheaf B S hS} {X V : FppfSheaf B S hS}
    (u : ∀ j, U j ⟶ X) (p : X ⟶ V) (hX : IsFormalAlgebraicSpace B S hS X)
    (hu : IsJointlyRigSurjective B S hS U u) (hp : IsRigSurjective B S hS p) :
    IsJointlyRigSurjective B S hS U (fun j ↦ u j ≫ p) := by
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D q hq
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, x, he, hx⟩ := hp R hRadic hRcomplete hRweak D q hq
  let : CommRing R' := hR'ring
  let : IsDomain R' := hR'dom
  let : IsDiscreteValuationRing R' := hR'dvr
  let : Algebra R R' := hR'alg
  let : IsDiscreteValuationRing.IsExtension R R' := hR'ext
  let : TopologicalSpace R' := hR'top
  let : IsTopologicalRing R' := hR'topring
  let : IsLinearTopology R' R' := hR'lin
  have hR'weak : TopologicalRing.IsWeaklyAdmissible R' :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hR'adic hR'complete
  have hxrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS x.hom :=
    isRepresentableByAlgebraicSpacesULift_of_comp_eq_formalSpectrumMap_comp B S hS
      hRadic hR'adic hR'complete hRweak hR'weak p hX e he hq hx
  obtain ⟨R'', hR''ring, hR''dom, hR''dvr, hR''alg, hR''ext, hR''top, hR''topring, hR''lin,
    hR''adic, hR''complete, D'', e', j, y, he', hyrep, hy⟩ :=
    hu R' hR'adic hR'complete hR'weak D' x hxrep
  let : CommRing R'' := hR''ring
  let : IsDomain R'' := hR''dom
  let : IsDiscreteValuationRing R'' := hR''dvr
  let : Algebra R' R'' := hR''alg
  let : IsDiscreteValuationRing.IsExtension R' R'' := hR''ext
  let : TopologicalSpace R'' := hR''top
  let : IsTopologicalRing R'' := hR''topring
  let : IsLinearTopology R'' R'' := hR''lin
  let : Algebra R R'' := ((algebraMap R' R'').comp (algebraMap R R')).toAlgebra
  have halg : (algebraMap R R'' : R →+* R'') = (algebraMap R' R'').comp (algebraMap R R') :=
    RingHom.algebraMap_toAlgebra _
  have : IsScalarTower R R' R'' := IsScalarTower.of_algebraMap_eq' halg
  refine ⟨R'', inferInstance, inferInstance, inferInstance, inferInstance,
    IsDiscreteValuationRing.IsExtension.trans R R' R'', inferInstance, inferInstance,
    inferInstance, hR''adic, hR''complete, D'',
    ContinuousHom.comp hR'weak hRweak e' e, j, y, ?_, hyrep, ?_⟩
  · rw [ContinuousHom.comp_toRingHom, he', he, halg]
  · show y ≫ u j ≫ p = _
    rw [← Category.assoc, hy, Category.assoc, hx, ← Category.assoc,
      formalSpectrumMap_comp_eq hR'weak hRweak e' e]

end AlgebraicGeometry.FormalSpace

end
