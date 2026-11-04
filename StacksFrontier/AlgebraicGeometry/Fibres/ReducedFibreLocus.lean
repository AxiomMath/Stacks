module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Fibres.ReducedGenericFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible

/-!
# The locus of geometrically reduced fibres of an affine morphism

For a morphism `f : X ⟶ Y` of schemes the set of points of `Y` whose fibre is geometrically
reduced is, for an affine morphism, the fibre locus `Algebra.geometricallyReducedFibreLocus` of
the corresponding algebra. This file proves that identification and deduces the affine Noetherian
case of Stacks 0579: for a morphism of finite presentation between affine schemes over a locally
Noetherian base, that set is locally constructible.

The identification is the dictionary between the two readings of "the fibre at `y` is
geometrically reduced". On schemes it is reducedness of `X_y ×_{κ(y)} Spec L` for every field `L`
over the residue field `κ(y)`; on rings it is reducedness of `C ⊗[A] K` for every field `K` over
`A` whose kernel is the prime `y`. The two quantify over the same thing, because a morphism
`Spec L ⟶ Spec A` hitting `y` is the same as a field `L` over `A` with `ker (A → L) = y`
(`AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField` in one
direction, `AlgebraicGeometry.Scheme.fromSpecResidueField_apply` in the other), and the two rings
tested agree, the pullback of the fibre along `Spec L ⟶ Spec κ(y)` being the pullback of
`Spec C ⟶ Spec A` along `Spec L ⟶ Spec A`, which is `Spec (C ⊗[A] L)`.

## Main results

* `AlgebraicGeometry.GeometricallyReduced.iff_geometricallyReduced_fiber`: a morphism is
  geometrically reduced exactly when all of its fibres are.
* `AlgebraicGeometry.geometricallyReduced_fiberToSpecResidueField_specMap_iff`: the fibre of
  `Spec C ⟶ Spec A` at a prime `p` is geometrically reduced exactly when `p` lies in
  `Algebra.geometricallyReducedFibreLocus A C`.
* `AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber_of_isAffine`: the affine
  Noetherian case of Stacks 0579.

## Implementation notes

The pasting of the two pullback squares — the fibre square and the square base-changing the fibre
to `L` — is `CategoryTheory.IsPullback.paste_horiz`, and the resulting square is compared with
`AlgebraicGeometry.pullbackSpecIso`; so the vertex is identified with `Spec (C ⊗[A] L)` without
computing the fibre itself.

The reduction from an arbitrary morphism of affine schemes to `Spec.map` is
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality`, which exhibits the comparison square as
cartesian because both horizontal maps are isomorphisms; Stacks 0576 then transports the locus,
and Stacks 054I transports local constructibility back along the isomorphism.

## References

* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 0576](https://stacks.math.columbia.edu/tag/0576)
* [Stacks Project, Tag 054I](https://stacks.math.columbia.edu/tag/054I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Geometric reducedness is a condition on the fibres.** A morphism of schemes is geometrically
reduced exactly when every one of its fibres is geometrically reduced over the residue field of
its image point.

This is `AlgebraicGeometry.geometrically_iff_forall_fiberToSpecResidueField` for reducedness, and
it is the form in which the hypothesis and the conclusion of Stacks 0579 are stated. -/
theorem GeometricallyReduced.iff_geometricallyReduced_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) :
    GeometricallyReduced f ↔ ∀ y, GeometricallyReduced (f.fiberToSpecResidueField y) := by
  simp only [GeometricallyReduced.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]

/-- The base change of the fibre of `Spec C ⟶ Spec A` at `p` along a field-valued point `q` of
`Spec κ(p)` is `Spec (C ⊗[A] L)`, where `L` is that field and `A → L` is the composite ring map;
so one is reduced exactly when the other is.

Pasting the fibre square with the square defining the base change along `q` exhibits the vertex as
the pullback of `Spec C ⟶ Spec A` along `Spec L ⟶ Spec A`, and
`AlgebraicGeometry.pullbackSpecIso` identifies that pullback with `Spec (C ⊗[A] L)`. -/
private theorem isReduced_pullback_fiberToSpecResidueField_iff {L : Type u} [Field L]
    [Algebra A L] (p : Spec (CommRingCat.of A))
    (q : Spec (CommRingCat.of L) ⟶ Spec ((Spec (CommRingCat.of A)).residueField p))
    (hq : q ≫ (Spec (CommRingCat.of A)).fromSpecResidueField p =
      Spec.map (CommRingCat.ofHom (algebraMap A L))) :
    IsReduced (pullback
        ((Spec.map (CommRingCat.ofHom (algebraMap A C))).fiberToSpecResidueField p) q) ↔
      _root_.IsReduced (C ⊗[A] L) := by
  have h1 := IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))
    ((Spec (CommRingCat.of A)).fromSpecResidueField p)
  have h2 := IsPullback.of_hasPullback
    ((Spec.map (CommRingCat.ofHom (algebraMap A C))).fiberToSpecResidueField p) q
  have h3 := h2.paste_horiz h1
  rw [hq] at h3
  let e := h3.isoPullback ≪≫ pullbackSpecIso A C L
  refine ⟨fun h => (affine_isReduced_iff (CommRingCat.of (C ⊗[A] L))).mp
    (ObjectProperty.prop_of_iso (P := (IsReduced ·)) e h), fun h => ?_⟩
  have h' : _root_.IsReduced (CommRingCat.of (C ⊗[A] L)) := h
  exact ObjectProperty.prop_of_iso (P := (IsReduced ·)) e.symm inferInstance

/-- The closed point of `Spec K` maps to `p` exactly when `p` is the kernel of `A → K`. -/
private theorem map_closedPoint_eq_iff_ker_eq {K : Type u} [Field K] [Algebra A K]
    (p : Spec (CommRingCat.of A)) :
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) (IsLocalRing.closedPoint K) = p ↔
      RingHom.ker (algebraMap A K) = p.asIdeal := by
  refine PrimeSpectrum.ext_iff.trans ?_
  change Ideal.comap _ (IsLocalRing.maximalIdeal K) = _ ↔ _
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  rfl

/-- **The geometrically reduced fibre locus of an affine morphism, on rings.** The fibre of
`Spec C ⟶ Spec A` at a prime `p` of `A` is geometrically reduced exactly when `p` lies in
`Algebra.geometricallyReducedFibreLocus A C`, that is, `C ⊗[A] K` is reduced for every field `K`
over `A` with `ker (A → K) = p`.

The two conditions quantify over the same fields: a field `K` over `A` with kernel `p` gives a
morphism `Spec K ⟶ Spec A` whose image is `p`, which factors through `Spec κ(p)`, and conversely a
field-valued point of `Spec κ(p)` gives a field over `A` with kernel `p`, because `κ(p)` is a field
and the kernel of `A → κ(p)` is `p`. At such a field the two rings tested agree, by
`AlgebraicGeometry.isReduced_pullback_fiberToSpecResidueField_iff`. -/
theorem geometricallyReduced_fiberToSpecResidueField_specMap_iff (p : Spec (CommRingCat.of A)) :
    GeometricallyReduced
        ((Spec.map (CommRingCat.ofHom (algebraMap A C))).fiberToSpecResidueField p) ↔
      p ∈ Algebra.geometricallyReducedFibreLocus A C := by
  refine ⟨fun hgr K _ _ hker => ?_, fun hp => ?_⟩
  · obtain rfl := (map_closedPoint_eq_iff_ker_eq (K := K) p).mpr hker
    exact (isReduced_pullback_fiberToSpecResidueField_iff _ _
      (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K
        (Spec (CommRingCat.of A)) (Spec.map (CommRingCat.ofHom (algebraMap A K))))).mp
      (pullback_of_geometrically hgr.geometrically_isReduced K _)
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y => ?_⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ (Spec (CommRingCat.of A)).fromSpecResidueField p)
  algebraize [ψ.hom]
  have hpt : (Spec.map ψ) (IsLocalRing.closedPoint L) = p :=
    (congrArg (fun k : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of A) =>
      k (IsLocalRing.closedPoint L)) hψ).trans
      ((Spec (CommRingCat.of A)).fromSpecResidueField_apply p (y (IsLocalRing.closedPoint L)))
  have hker := (map_closedPoint_eq_iff_ker_eq (K := L) p).mp hpt
  exact (isReduced_pullback_fiberToSpecResidueField_iff p y hψ.symm).mpr (hp L hker)

/-- **The affine Noetherian case of Stacks 0579.** For a morphism `g : X ⟶ S` of finite
presentation between affine schemes with `S` locally Noetherian, the set of points of `S` whose
fibre is geometrically reduced is locally constructible.

Comparing `g` with `Spec Γ(X, ⊤) ⟶ Spec Γ(S, ⊤)` gives a cartesian square with isomorphisms along
the top and bottom, so Stacks 0576 identifies the locus with the inverse image of the locus of the
latter; that locus is `Algebra.geometricallyReducedFibreLocus Γ(S, ⊤) Γ(X, ⊤)` by
`AlgebraicGeometry.geometricallyReduced_fiberToSpecResidueField_specMap_iff`, which is
constructible by `Algebra.isConstructible_geometricallyReducedFibreLocus'`; and Stacks 054I takes
local constructibility back along the isomorphism. -/
@[stacks 0579 "affine Noetherian case: `X` and `S` affine with `S` locally Noetherian. The source
states the lemma for an arbitrary quasi-compact morphism locally of finite presentation.",
  ega "IV 9.9.3" "affine Noeth., reduced",
  ega "IV 9.9.5" "reduced fibres, affine",
  ega "IV 9.7.7" "(iii), affine Noeth."]
theorem isLocallyConstructible_geometricallyReduced_fiber_of_isAffine {X S : Scheme.{u}}
    (g : X ⟶ S) [IsAffine X] [IsAffine S] [IsLocallyNoetherian S] (hg : FinitePresentation g) :
    IsLocallyConstructible {y : S | GeometricallyReduced (g.fiberToSpecResidueField y)} := by
  have _ : LocallyOfFinitePresentation g := hg.1
  algebraize [g.appTop.hom]
  have hfp : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
    RingHom.finitePresentation_algebraMap.mp g.finitePresentation_appTop
  have hN : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian (X := S) ⟨⊤, isAffineOpen_top S⟩
  have hsq : IsPullback X.isoSpec.hom g (Spec.map g.appTop) S.isoSpec.hom :=
    IsPullback.of_horiz_isIso (CommSq.mk (Scheme.isoSpec_hom_naturality g))
  rw [geometricallyReduced_fiber_set_eq_preimage_of_isPullback
    (Spec.map g.appTop) g X.isoSpec.hom S.isoSpec.hom hsq]
  refine isLocallyConstructible_preimage S.isoSpec.hom ?_
  have hset : {y : ↥(Spec Γ(S, ⊤)) |
        GeometricallyReduced ((Spec.map g.appTop).fiberToSpecResidueField y)} =
      Algebra.geometricallyReducedFibreLocus ↥Γ(S, ⊤) ↥Γ(X, ⊤) :=
    Set.ext geometricallyReduced_fiberToSpecResidueField_specMap_iff
  rw [hset]
  exact (Algebra.isConstructible_geometricallyReducedFibreLocus' _ _).isLocallyConstructible

end AlgebraicGeometry

end
