module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.JointlyRigSurjectiveEtalePoint
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleLocal
import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition
import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Rig-surjectivity is étale local on the target, given a jointly rig-surjective cover

Let `f : X ⟶ Y` be a morphism of fppf sheaves over `S` which is locally of finite type and let
`{gᵢ : Yᵢ ⟶ Y}` be a family of representable étale morphisms which is jointly surjective on
points and jointly rig-surjective. Then `f` is rig-surjective exactly when each base change
`X ×_Y Yᵢ ⟶ Yᵢ` is.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_iff_forall_pullback_snd'`: the statement
  above, with joint rig-surjectivity of the given family as a hypothesis. Together with the
  joint rig-surjectivity of a jointly surjective family of representable étale morphisms of
  formal algebraic spaces it is **Stacks 0AQV**.
* `AlgebraicGeometry.FormalSpace.isRigSurjective_iff_forall_pullback_snd_of_isRepresentableEtale`:
  **Stacks 0AQV**, with joint rig-surjectivity of the cover proved
  (`isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective`, the family form of
  Stacks 0AQU).

## Implementation notes

The forward direction is Stacks 0AQS, applied to the members `gᵢ`, which are locally of finite
type by `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_isRepresentableEtale`. For the
converse an adic point of `Y` out of a complete discrete valuation ring is lifted to one `Yᵢ`
over an extension of complete discrete valuation rings, using joint rig-surjectivity, and then
lifted through the base change over a further extension; the two extensions compose to one.

## References

* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0AQU](https://stacks.math.columbia.edu/tag/0AQU)
* [Stacks Project, Tag 0AQV](https://stacks.math.columbia.edu/tag/0AQV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u v

/-- **Rig-surjectivity along a jointly rig-surjective étale cover.** Let `f : X ⟶ Y` be a
morphism of fppf sheaves over `S` which is locally of finite type and let `{gᵢ : Yᵢ ⟶ Y}` be a
family of representable étale morphisms which is jointly surjective on points and, granted
that, jointly rig-surjective (`hjoint`). Then `f` is rig-surjective exactly when each base change
`X ×_Y Yᵢ ⟶ Yᵢ` is rig-surjective.

The forward direction is Stacks 0AQS. For the converse an adic point of `Y` out of a complete
discrete valuation ring is lifted to one `Yᵢ` over an extension of complete discrete valuation
rings, using that the family is jointly rig-surjective, and then lifted through that base
change over a further extension; the projection to `X` makes the result a lift through `f`, and
the two extensions compose to one. -/
theorem isRigSurjective_iff_forall_pullback_snd' (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type v} {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (Yi : I → FppfSheaf B S hS) (g : ∀ i, Yi i ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hg : ∀ i, IsRepresentableEtale B S hS (g i))
    (hcover : IsJointlySurjective B S hS Yi g)
    (hjoint : (∀ i, IsRepresentableEtale B S hS (g i)) → IsJointlySurjective B S hS Yi g →
      IsJointlyRigSurjective B S hS Yi g) :
    IsRigSurjective B S hS f ↔ ∀ i, IsRigSurjective B S hS (pullback.snd f (g i)) := by
  refine ⟨fun hsf i => (IsRigSurjective.of_isPullback B S hS
    (IsPullback.of_hasPullback f (g i)).flip hf
    (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS (g i) (hg i)) hsf).2, ?_⟩
  intro hfi R _ _ _ _ _ _ hRadic hRcomplete hRweak D p hp
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, i, y, he, hyrep, hy⟩ :=
    hjoint hg hcover R hRadic hRcomplete hRweak D p hp
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
  obtain ⟨R'', hR''ring, hR''dom, hR''dvr, hR''alg, hR''ext, hR''top, hR''topring, hR''lin,
    hR''adic, hR''complete, D'', e', x, he', hx⟩ :=
    hfi i R' hR'adic hR'complete hR'weak D' y hyrep
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
  let : IsScalarTower R R' R'' := IsScalarTower.of_algebraMap_eq fun z => by rw [halg]; rfl
  refine ⟨R'', inferInstance, inferInstance, inferInstance, inferInstance,
    IsDiscreteValuationRing.IsExtension.trans R R' R'', inferInstance, inferInstance,
    inferInstance, hR''adic, hR''complete, D'',
    ContinuousHom.comp hR'weak hRweak e' e, x ≫ pullback.fst f (g i), ?_, ?_⟩
  · rw [ContinuousHom.comp_toRingHom, he', he, halg]
  · rw [Category.assoc, pullback.condition, reassoc_of% hx, hy, ← Category.assoc,
      formalSpectrumMap_comp_eq hR'weak hRweak e' e]

/-- **Stacks 0AQV.** Let `f : X ⟶ Y` be a morphism of fppf sheaves over `S` which is locally of
finite type and let `{gᵢ : Yᵢ ⟶ Y}` be a family of morphisms from formal algebraic spaces which
are representable by algebraic spaces and étale and which is jointly surjective on points (that
is, `∐ gᵢ` is surjective). Then `f` is rig-surjective if and only if each base change
`fᵢ : X ×_Y Yᵢ ⟶ Yᵢ` is rig-surjective.

This is `isRigSurjective_iff_forall_pullback_snd'` together with joint rig-surjectivity of the
family, which is the family form of Stacks 0AQU,
`isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective`: the source's proof
applies Stacks 0AQU to `∐ gᵢ`, and that form avoids the coproduct by catching each adic point in
one member of the family.

The source states this for locally Noetherian formal algebraic spaces `X`, `Y` and `Yᵢ`. The
proof uses that the `Yᵢ` are formal algebraic spaces and nothing more, so the locally Noetherian
hypotheses and the hypotheses on `X` and `Y` are omitted. -/
@[stacks 0AQV "for a morphism f : X ⟶ Y locally of finite type and a family of representable \
étale morphisms gᵢ : Yᵢ ⟶ Y from formal algebraic spaces with ∐ gᵢ surjective, f is \
rig-surjective if and only if every base change X ×_Y Yᵢ ⟶ Yᵢ is; the locally Noetherian \
hypotheses of the source are not needed"]
theorem isRigSurjective_iff_forall_pullback_snd_of_isRepresentableEtale (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {I : Type v} {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (Yi : I → FppfSheaf B S hS) (g : ∀ i, Yi i ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hYi : ∀ i, IsFormalAlgebraicSpace B S hS (Yi i))
    (hg : ∀ i, IsRepresentableEtale B S hS (g i))
    (hcover : IsJointlySurjective B S hS Yi g) :
    IsRigSurjective B S hS f ↔ ∀ i, IsRigSurjective B S hS (pullback.snd f (g i)) :=
  isRigSurjective_iff_forall_pullback_snd' B S hS f Yi g hf hg hcover fun hg' hcover' =>
    isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective B S hS Yi g hYi hg'
      hcover'

end AlgebraicGeometry.FormalSpace

end
