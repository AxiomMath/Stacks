module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalChartStalkOrigin
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AbsoluteApproximationFull
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkBaseChange

/-!
# The formal fibre of the standard nodal family, and its completed local ring

Stacks Tag 0GDX is applied to the standard nodal family
`Spec ℤ[u, v, a]/(uv - a) ⟶ Spec ℤ[a]` along a morphism `Spec A ⟶ Spec ℤ[a]` out of the spectrum
of the completed local ring `A` of the base, written in the factored shape
`Spec σ ≫ fromSpecStalk` that the tag's statement uses. Its hypotheses then ask for a point `y_σ`
of the fibre product `Y_σ = Y ×_{Spec ℤ[a]} Spec A` lying over the closed point, and for an
isomorphism of the completed local ring of `Y_σ` there with the completed local ring of the
source of the family.

This file supplies both. The fibre product is the spectrum of the nodal chart `A[u, v]/(uv - h)`
— that is `Stacks.NodalEtaleLocalStructure.isPullback_specMap_chartClassify` read along the
factorisation — the point is the origin of that chart over the closed point, and its completed
local ring is `A⟦u, v⟧/(uv - h)` by
`Stacks.NodalChart.exists_ringEquiv_adicCompletion_stalk_chartOriginPt`. Everything is produced
compatibly with the maps from the local ring of the base, which is what the tag's last hypothesis
asks and the only part of the argument that is not formal.

## Main results

* `Stacks.NodalEtaleLocalStructure.exists_point_ringEquiv_adicCompletion_pullback_standard` —
  **the point of the formal fibre of the standard family and its completed local ring**: a point
  of `Y ×_{Spec ℤ[a]} Spec A` over the closed point of `Spec A`, together with a ring
  isomorphism of its completed local ring with `A⟦u, v⟧/(uv - h)` compatible with the maps from
  the local ring of the base.

## Implementation notes

The compatibility is the composite of three steps, each matched on the image of the base ring:
the local ring of the fibre product at the point is the local ring of the chart at the origin
(the stalk map of an isomorphism of schemes), the latter completes to `A⟦u, v⟧/(uv - h)`, and
the structure map of the chart composed with `Spec A ⟶ S` is the map of local rings of the
morphism `Spec A ⟶ S` read through
`StacksDraft.ArtinApproximation.ofHom_stalkHomAt_of_eq_specMap_fromSpecStalk`.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 0CBX](https://stacks.math.columbia.edu/tag/0CBX)
* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Stacks.NodalChart
open StacksDraft.ArtinApproximation

universe u

namespace Stacks.NodalEtaleLocalStructure

/-- The map on local rings read out of a morphism at a point, with the trivial transport, is the
stalk map. -/
private theorem stalkHomAt_rfl {X Z : Scheme.{u}} {x : X} (m : X ⟶ Z) :
    m.stalkHomAt (rfl : m x = m x) = (m.stalkMap x).hom := by
  simp [Scheme.Hom.stalkHomAt]

/-- **The point of the formal fibre of the standard nodal family, and its completed local
ring.** Let `S` be a scheme with a point `s`, let `A` be a complete Noetherian local ring with a
local homomorphism `φ` from the local ring of `S` at `s`, and let `h` lie in the maximal ideal of
`A`. Form the morphism `Spec A ⟶ Spec ℤ[a]` classifying `h`, written in the factored shape that
Stacks Tag 0GDX uses, and let `Y_σ` be the fibre product of the standard nodal family along it.

Then `Y_σ` has a point lying over the closed point of `Spec A` whose completed local ring is
`A⟦u, v⟧/(uv - h)`, compatibly with the map of local rings of the morphism
`Y_σ ⟶ Spec A ⟶ S` on one side and `φ` on the other. -/
public theorem exists_point_ringEquiv_adicCompletion_pullback_standard
    {S : Scheme.{u}} {s : S} (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (h : A) (hh : h ∈ maximalIdeal A)
    (φ : S.presheaf.stalk s ⟶ CommRingCat.of A) [IsLocalHom φ.hom] :
    ∃ y : ↥(pullback (standardNodalFamily (ULift.{u} ℤ))
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
            (nodalParameterMap (intRingHom A) h)).hom) ≫
          (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
            ((nodalParameterMap (intRingHom A) h) (closedPoint A)))),
      pullback.snd (standardNodalFamily (ULift.{u} ℤ))
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
              (nodalParameterMap (intRingHom A) h)).hom) ≫
            (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
              ((nodalParameterMap (intRingHom A) h) (closedPoint A))) y = closedPoint A ∧
        ∃ hbase : (pullback.snd (standardNodalFamily (ULift.{u} ℤ))
              (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
                  (nodalParameterMap (intRingHom A) h)).hom) ≫
                (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
                  ((nodalParameterMap (intRingHom A) h) (closedPoint A))) ≫
              Spec.map φ ≫ S.fromSpecStalk s) y = s,
          ∃ Ψ : AdicCompletion (maximalIdeal ((pullback (standardNodalFamily (ULift.{u} ℤ))
                  (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
                      (nodalParameterMap (intRingHom A) h)).hom) ≫
                    (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
                      ((nodalParameterMap (intRingHom A) h) (closedPoint A)))).presheaf.stalk y))
                ((pullback (standardNodalFamily (ULift.{u} ℤ))
                  (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
                      (nodalParameterMap (intRingHom A) h)).hom) ≫
                    (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
                      ((nodalParameterMap (intRingHom A) h) (closedPoint A)))).presheaf.stalk y) ≃+*
              (MvPowerSeries (Fin 2) A ⧸ Ideal.span
                {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}),
            ∀ z : S.presheaf.stalk s,
              Ψ (algebraMap _ _ ((pullback.snd (standardNodalFamily (ULift.{u} ℤ))
                  (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
                      (nodalParameterMap (intRingHom A) h)).hom) ≫
                    (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
                      ((nodalParameterMap (intRingHom A) h) (closedPoint A))) ≫
                  Spec.map φ ≫ S.fromSpecStalk s).stalkHomAt hbase z)) =
                algebraMap A (MvPowerSeries (Fin 2) A ⧸ Ideal.span
                  {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) (φ.hom z) := by
  -- the morphism along which the fibre product is formed is the classifying map of `h`
  have hm : Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
        (nodalParameterMap (intRingHom A) h)).hom) ≫
      (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
        ((nodalParameterMap (intRingHom A) h) (closedPoint A)) =
      nodalParameterMap (intRingHom A) h :=
    specMap_stalkClosedPointTo_comp_fromSpecStalk_nodalParameterMap A h
  -- so the fibre product is the spectrum of the nodal chart
  have hsq : IsPullback
      (Spec.map (CommRingCat.ofHom (chartClassify (intRingHom A) h)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (nodalChartRing A h))))
      (standardNodalFamily (ULift.{u} ℤ))
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
          (nodalParameterMap (intRingHom A) h)).hom) ≫
        (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
          ((nodalParameterMap (intRingHom A) h) (closedPoint A))) := by
    rw [hm]
    exact isPullback_specMap_chartClassify (intRingHom A) h
  have hιsnd := hsq.isoIsPullback_hom_snd (Spec (.of (Stacks.Curves.nodalQuotient (ULift.{u} ℤ))))
    (Spec (.of A)) (IsPullback.of_hasPullback (standardNodalFamily (ULift.{u} ℤ))
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
          (nodalParameterMap (intRingHom A) h)).hom) ≫
        (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
          ((nodalParameterMap (intRingHom A) h) (closedPoint A))))
  set ι := hsq.isoIsPullback (Spec (.of (Stacks.Curves.nodalQuotient (ULift.{u} ℤ)))) (Spec (.of A))
    (IsPullback.of_hasPullback (standardNodalFamily (ULift.{u} ℤ))
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
          (nodalParameterMap (intRingHom A) h)).hom) ≫
        (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
          ((nodalParameterMap (intRingHom A) h) (closedPoint A)))) with hιdef
  -- the point is the origin of the chart over the closed point
  have hsnd : pullback.snd (standardNodalFamily (ULift.{u} ℤ))
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
          (nodalParameterMap (intRingHom A) h)).hom) ≫
        (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
          ((nodalParameterMap (intRingHom A) h) (closedPoint A)))
      (ι.hom (chartOriginPt A hh)) = closedPoint A :=
    (congrArg (fun q : Spec (.of (nodalChartRing A h)) ⟶ Spec (.of A) =>
        q (chartOriginPt A hh)) hιsnd).trans (specMap_algebraMap_chartOriginPt A hh)
  have hbase : (pullback.snd (standardNodalFamily (ULift.{u} ℤ))
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
            (nodalParameterMap (intRingHom A) h)).hom) ≫
          (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
            ((nodalParameterMap (intRingHom A) h) (closedPoint A))) ≫
        Spec.map φ ≫ S.fromSpecStalk s) (ι.hom (chartOriginPt A hh)) = s :=
    (congrArg (fun w : ↥(Spec (.of A)) => (Spec.map φ ≫ S.fromSpecStalk s) w) hsnd).trans
      (specMap_fromSpecStalk_closedPoint φ)
  -- the local rings at the two points agree, and so do their completions
  set Θs := (asIso (ι.hom.stalkMap (chartOriginPt A hh))).commRingCatIsoToRingEquiv with hΘsdef
  have hΘsapp : ∀ v, Θs v = (ι.hom.stalkHomAt
      (rfl : ι.hom (chartOriginPt A hh) = ι.hom (chartOriginPt A hh))) v := fun v => by
    rw [stalkHomAt_rfl]; rfl
  obtain ⟨EP, hEP⟩ := exists_ringEquiv_adicCompletion_stalk_chartOriginPt A h hh
  obtain ⟨Θc, hΘc⟩ :=
    Stacks.AdicCompletionFibreUniverse.exists_adicCompletion_ringEquiv_of_map_eq Θs
      (maximalIdeal ((pullback (standardNodalFamily (ULift.{u} ℤ))
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
            (nodalParameterMap (intRingHom A) h)).hom) ≫
          (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
            ((nodalParameterMap (intRingHom A) h) (closedPoint A)))).presheaf.stalk
        (ι.hom (chartOriginPt A hh))))
      (maximalIdeal ((Spec (.of (nodalChartRing A h))).presheaf.stalk (chartOriginPt A hh)))
      (IsLocalRing.map_ringEquiv_maximalIdeal Θs)
  refine ⟨ι.hom (chartOriginPt A hh), hsnd, hbase, Θc.trans EP, fun z => ?_⟩
  -- the structure map from the local ring of the base, computed through the chart
  have hβ : (Spec.map φ ≫ S.fromSpecStalk s) (closedPoint A) = s :=
    specMap_fromSpecStalk_closedPoint φ
  have hstalkβ : (Spec.map φ ≫ S.fromSpecStalk s).stalkHomAt hβ z =
      (stalkClosedPointIso (CommRingCat.of A)).inv.hom (φ.hom z) :=
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (ofHom_stalkHomAt_of_eq_specMap_fromSpecStalk φ (Spec.map φ ≫ S.fromSpecStalk s) rfl hβ)) z
  have hmorph : ι.hom ≫ (pullback.snd (standardNodalFamily (ULift.{u} ℤ))
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
            (nodalParameterMap (intRingHom A) h)).hom) ≫
          (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
            ((nodalParameterMap (intRingHom A) h) (closedPoint A))) ≫
        Spec.map φ ≫ S.fromSpecStalk s) =
      Spec.map (CommRingCat.ofHom (algebraMap A (nodalChartRing A h))) ≫
        Spec.map φ ≫ S.fromSpecStalk s := by
    rw [← Category.assoc, hιsnd]
  have hkey : Θs ((pullback.snd (standardNodalFamily (ULift.{u} ℤ))
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo
            (nodalParameterMap (intRingHom A) h)).hom) ≫
          (Spec (.of (Polynomial (ULift.{u} ℤ)))).fromSpecStalk
            ((nodalParameterMap (intRingHom A) h) (closedPoint A))) ≫
        Spec.map φ ≫ S.fromSpecStalk s).stalkHomAt hbase z) =
      ((Spec.map (CommRingCat.ofHom (algebraMap A (nodalChartRing A h)))).stalkHomAt
        (specMap_algebraMap_chartOriginPt A hh))
          ((stalkClosedPointIso (CommRingCat.of A)).inv.hom (φ.hom z)) := by
    rw [hΘsapp]
    have h1 : (ι.hom.stalkHomAt
          (rfl : ι.hom (chartOriginPt A hh) = ι.hom (chartOriginPt A hh)))
        ((pullback.snd (standardNodalFamily (ULift.{u} ℤ)) _ ≫
          Spec.map φ ≫ S.fromSpecStalk s).stalkHomAt hbase z) =
        (ι.hom ≫ (pullback.snd (standardNodalFamily (ULift.{u} ℤ)) _ ≫
          Spec.map φ ≫ S.fromSpecStalk s)).stalkHomAt hbase z :=
      (RingHom.congr_fun (Scheme.Hom.stalkHomAt_comp ι.hom
        (pullback.snd (standardNodalFamily (ULift.{u} ℤ)) _ ≫
          Spec.map φ ≫ S.fromSpecStalk s) rfl hbase) z).symm
    rw [h1, stalkHomAt_congr hmorph hbase
      (by rw [← hmorph]; exact hbase),
      Scheme.Hom.stalkHomAt_comp (Spec.map (CommRingCat.ofHom
        (algebraMap A (nodalChartRing A h)))) (Spec.map φ ≫ S.fromSpecStalk s)
        (specMap_algebraMap_chartOriginPt A hh) hβ]
    exact congrArg (fun w => ((Spec.map (CommRingCat.ofHom
      (algebraMap A (nodalChartRing A h)))).stalkHomAt
        (specMap_algebraMap_chartOriginPt A hh)) w) hstalkβ
  rw [RingEquiv.trans_apply, hΘc, hkey, hEP]

/-- **The isomorphism of completed local rings of Tag 0CBX is one of algebras over the local ring
of the base.** Let `f : X ⟶ S` carry `x` to `s`, let `A` be the completed local ring of `S` at
`s`, and let `E` identify `A⟦u, v⟧/(uv - h)` with the completed local ring of `X` at `x`
compatibly with the maps from `A` — the hypothesis `hE`, which is what Tag 0CBX's `A`-algebra
isomorphism says. Let `M : Z ⟶ S` carry a point `w` to `s`, and let `Ψ` identify the completed
local ring of `Z` at `w` with the same power series quotient, compatibly with the maps from the
local ring of `S` at `s`. Then the composite isomorphism
`𝒪^∧_{X, x} ≅ A⟦u, v⟧/(uv - h) ≅ 𝒪^∧_{Z, w}` commutes with the two maps out of the local ring of
`S` at `s`.

This is the last hypothesis of [Stacks, Tag 0GDX], in the shape the tag states it. -/
public theorem comp_algebraMap_stalkHomAt_eq_of_ringEquiv
    {X S Z : Scheme.{u}} (f : X ⟶ S) (x : X) {w : Z} (M : Z ⟶ S) (hM : M w = f x)
    {h : AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x))}
    (E : (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))) ⧸
          Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) ≃+*
        AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hE : ∀ a, E (algebraMap _ _ a) =
      adicCompletionMap (f.stalkMap x).hom (maximalIdeal (S.presheaf.stalk (f x)))
        (maximalIdeal (X.presheaf.stalk x))
        (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom) a)
    (Ψ : AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w) ≃+*
      (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
          (S.presheaf.stalk (f x))) ⧸
        Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}))
    (hΨ : ∀ z : S.presheaf.stalk (f x),
      Ψ (algebraMap (Z.presheaf.stalk w)
          (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w))
          (M.stalkHomAt hM z)) =
        algebraMap (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))) _
          (algebraMap (S.presheaf.stalk (f x))
            (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
              (S.presheaf.stalk (f x))) z)) :
    (E.symm.trans Ψ.symm).toRingHom.comp
        ((algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (f.stalkHomAt (rfl : f x = f x))) =
      (algebraMap (Z.presheaf.stalk w)
        (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w))).comp
        (M.stalkHomAt hM) := by
  refine RingHom.ext fun z => ?_
  have h1 : algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
        (f.stalkHomAt (rfl : f x = f x) z) =
      adicCompletionMap (f.stalkMap x).hom (maximalIdeal (S.presheaf.stalk (f x)))
        (maximalIdeal (X.presheaf.stalk x))
        (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom)
        (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))) z) := by
    rw [stalkHomAt_rfl]
    exact (RingHom.congr_fun (adicCompletionMap_comp_algebraMap (f.stalkMap x).hom
      (maximalIdeal (S.presheaf.stalk (f x))) (maximalIdeal (X.presheaf.stalk x))
      (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom)) z).symm
  have h3 : E.symm (adicCompletionMap (f.stalkMap x).hom
        (maximalIdeal (S.presheaf.stalk (f x))) (maximalIdeal (X.presheaf.stalk x))
        (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom)
        (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))) z)) =
      algebraMap (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
          (S.presheaf.stalk (f x))) _
        (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))) z) :=
    E.symm_apply_eq.mpr (hE _).symm
  change Ψ.symm (E.symm (algebraMap (X.presheaf.stalk x) _
    (f.stalkHomAt (rfl : f x = f x) z))) = _
  rw [h1, h3]
  exact (Ψ.symm_apply_eq).mpr (hΨ z).symm

/-- **Tag 0CBY's diagram from the formal local structure of Tag 0CBX.** Let `f : X ⟶ S` be
locally of finite type over a locally Noetherian base, let `x` be a point of `X` whose image has
a G-ring for local ring, and suppose the completed local ring of `X` at `x` is
`A⟦u, v⟧/(uv - h)` as an `A`-algebra, where `A` is the completed local ring of `S` at the image
of `x` and `h` lies in its maximal ideal — that is, suppose the conclusion of Tag 0CBX. Then the
diagram of Tag 0CBY is in hand at `x`.

This is [Stacks, Tag 0GDX] applied to the standard nodal family: the formal fibre of the family
along the morphism `Spec A ⟶ Spec ℤ[a]` classifying `h` is the nodal chart `A[u, v]/(uv - h)`,
whose completed local ring at the origin is the quotient of the power series ring that Tag 0CBX
produces, so the tag's hypothesis on the two completed local rings holds; its conclusion is the
étale-local approximation out of which
`Stacks.NodalEtaleLocalStructure.standardNodalDiagramOfEtaleApproximation` builds the
diagram. -/
public theorem nonempty_standardNodalDiagram_of_exists_algEquiv_adicCompletion
    {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] (x : X)
    (hG : IsGRing (S.presheaf.stalk (f x)))
    (hCBX :
      letI : Algebra
          (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x)))
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :=
        (adicCompletionMap (f.stalkMap x).hom (maximalIdeal (S.presheaf.stalk (f x)))
          (maximalIdeal (X.presheaf.stalk x))
          (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom)).toAlgebra
      ∃ h : AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x)),
        h ∈ maximalIdeal
            (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x))) ∧
          Nonempty ((MvPowerSeries (Fin 2)
                (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
                  (S.presheaf.stalk (f x))) ⧸
              Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) ≃ₐ[
                AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x))]
              AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))) :
    Nonempty (StandardNodalDiagram f x) := by
  let : Algebra
      (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x)))
      (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :=
    (adicCompletionMap (f.stalkMap x).hom (maximalIdeal (S.presheaf.stalk (f x)))
      (maximalIdeal (X.presheaf.stalk x))
      (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom)).toAlgebra
  obtain ⟨h, hh, ⟨E⟩⟩ := hCBX
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
      (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x)))
        (S.presheaf.stalk (f x))))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (S.presheaf.stalk (f x))
      (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x)))))
  obtain ⟨y, hysnd, hbase, Ψ, hΨ⟩ :=
    exists_point_ringEquiv_adicCompletion_pullback_standard
      (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x))) h hh
      (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
        (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x)))))
  obtain ⟨V, -, τ, hτ, yτ, -, -, W, -, F, hF, hFet, -, hFcomm⟩ :=
    exists_elementaryEtaleNeighborhood_absoluteApproximation_full f
      (standardNodalFamily (ULift.{u} ℤ)) locallyOfFiniteType_from_nodalParameterBase x (f x) rfl
      ((nodalParameterMap (intRingHom
        (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x)))) h)
        (closedPoint
          (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x)))))
      (pullback.fst (standardNodalFamily (ULift.{u} ℤ)) _ y) hG
      (Scheme.stalkClosedPointTo (nodalParameterMap (intRingHom
        (AdicCompletion (maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x)))) h)).hom
      inferInstance y rfl hysnd (E.toRingEquiv.symm.trans Ψ.symm) hbase
      (comp_algebraMap_stalkHomAt_eq_of_ringEquiv f x _ hbase E.toRingEquiv
        (fun a => E.commutes a) Ψ hΨ)
  have := V.etale_toBase
  have := W.etale_toBase
  have := hFet
  exact ⟨standardNodalDiagramOfEtaleApproximation V.toBase τ W.toBase F W.point hF hFcomm⟩

end Stacks.NodalEtaleLocalStructure

end
