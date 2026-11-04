module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Defs

/-!
# Quasi-compact separated étale effectivity is Zariski-local on the base

Let `f : X ⟶ S` be a surjective integral morphism of schemes. Along such a morphism the étale
descent functor of [Stacks, Tag 0BTI](https://stacks.math.columbia.edu/tag/0BTI) is fully
faithful, and so is its base change along any morphism, an integral morphism being universally
closed and both properties being stable under base change. Feeding that into
[Stacks, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM) shows that effectivity of
quasi-compact separated étale descent data is Zariski-local on the base.

## Main results

* `fullyFaithful_etaleDescentFunctor_baseChange_of_isIntegralHom`: the étale descent functor of
  the base change of a surjective integral morphism is fully faithful.
* `qcSepEtaleEffective_of_isOpenCover`: **effectivity of quasi-compact separated étale descent
  data is Zariski-local on the base.**
* `essSurj_quasiCompactSeparatedEtaleDescentFunctor`: effectivity gives essential surjectivity of
  the functor of Tag 0BTI restricted to quasi-compact separated objects.
* `isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_qcSepEtaleEffective`: effectivity
  gives that this functor is an equivalence.

## Implementation notes

The witness produced by `AlgebraicGeometry.QcSepEtaleEffective` is a descended scheme, whose
projection is a base change of `f` and therefore surjective, quasi-compact and universally
closed. That is exactly what `AlgebraicGeometry.DescentDatum.Descended.quasiCompact_base_hom`
and `AlgebraicGeometry.DescentDatum.Descended.isSeparated_base_hom` need in order to land the
witness in the full subcategory of quasi-compact separated schemes étale over `S`, so no fpqc
descent of these two properties is used.

## References

* [Stacks Project, Tag 0BTI](https://stacks.math.columbia.edu/tag/0BTI)
* [Stacks Project, Tag 0BTL](https://stacks.math.columbia.edu/tag/0BTL)
* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe v u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {S X : Scheme.{u}}

/-- **The étale descent functor of the base change of a surjective integral morphism is fully
faithful.** -/
def fullyFaithful_etaleDescentFunctor_baseChange_of_isIntegralHom (f : X ⟶ S)
    [Surjective f] [IsIntegralHom f] {T : Scheme.{u}} (g : T ⟶ S) :
    (etaleDescentFunctor (pullback.snd f g)).FullyFaithful :=
  (etaleDescentFunctor_fullyFaithful_of_universallyClosed (pullback.snd f g)).some

/-- **Effectivity of quasi-compact separated étale descent data is Zariski-local on the
base.** -/
theorem qcSepEtaleEffective_of_isOpenCover (f : X ⟶ S) [Surjective f] [IsIntegralHom f]
    {ι : Type v} (U : ι → S.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, QcSepEtaleEffective (pullback.snd f (U i).ι)) :
    QcSepEtaleEffective f := by
  refine qcSepEtaleEffective_of_isEtaleEffective fun D hD hqc hsep ↦ ?_
  have := hD
  refine DescentDatum.isEtaleEffective_of_isOpenCover D U hU (fun i ↦ ?_)
    (fun i j ↦ fullyFaithful_etaleDescentFunctor_baseChange_of_isIntegralHom f (U i ⊓ U j).ι)
    (fun i j k ↦
      (fullyFaithful_etaleDescentFunctor_baseChange_of_isIntegralHom f
        (U i ⊓ U j ⊓ U k).ι).faithful)
  exact (h i).isEtaleEffective (D.baseDatum (U i))
    (D.quasiCompact_baseDatum_over_hom (U i) hqc) (D.isSeparated_baseDatum_over_hom (U i) hsep)

/-- **Effectivity gives essential surjectivity of the functor of Tag 0BTI restricted to
quasi-compact separated objects.** -/
theorem essSurj_quasiCompactSeparatedEtaleDescentFunctor (f : X ⟶ S) [Surjective f]
    [IsIntegralHom f] (h : QcSepEtaleEffective f) :
    (quasiCompactSeparatedEtaleDescentFunctor f).EssSurj := by
  refine ⟨fun Dq ↦ ?_⟩
  have hD : Etale (Dq.obj.obj.obj ()).hom := Dq.obj.property
  obtain ⟨Q, hQ⟩ := h Dq.obj.obj hD Dq.property.1 Dq.property.2
  have := hQ
  exact ⟨⟨Scheme.Etale.mk Q.base.hom,
    ⟨Q.quasiCompact_base_hom Dq.property.1, Q.isSeparated_base_hom Dq.property.2⟩⟩,
    ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _ Q.canonicalIso)⟩⟩

/-- **Effectivity makes the functor of Tag 0BTI, restricted to quasi-compact separated étale
objects, an equivalence** along a surjective integral morphism. -/
theorem isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_qcSepEtaleEffective
    (f : X ⟶ S) [Surjective f] [IsIntegralHom f] (h : QcSepEtaleEffective f) :
    (quasiCompactSeparatedEtaleDescentFunctor f).IsEquivalence :=
  have := essSurj_quasiCompactSeparatedEtaleDescentFunctor f h
  isEquivalence_quasiCompactSeparatedEtaleDescentFunctor f

end AlgebraicGeometry

end
