module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceSplit.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.SectionLocusDVR
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingConsequences
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Reduced
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksFrontier.Topology.Constructible.NoetherianNeighbourhood
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduction of Stacks 055Q to the discrete valuation ring case

Let `f : X ⟶ Y` be a morphism of schemes with a section `s` and let `X⁰ ⊆ X` be the union of the
connected components of the fibres of `f` containing the corresponding value of `s`
(Stacks 055L). `AlgebraicGeometry.isOpen_locus_of_isDiscreteValuationRing` proves Stacks 055R
when the base is the spectrum of a discrete valuation ring. This file carries out the *topological
reduction*: it deduces from that case the statement that `X⁰` is stable under generalization on a
locally Noetherian source, and then applies Stacks 0540 to turn that into the neighbourhood
statement of Stacks 055Q.

The reduction is the middle paragraph of the source's proof of Stacks 055Q. Given a
specialization `x' ⤳ x` with `x ∈ X⁰`, Stacks 054F supplies a discrete valuation ring `R` and a
morphism `g : Spec R ⟶ X` taking the generic point to `x'` and the closed point to `x`. Base
changing `f` along `g ≫ f : Spec R ⟶ Y` produces a morphism `X_R ⟶ Spec R` carrying two
sections: the base change `s_R` of `s`, which is the one defining `(X_R)⁰`, and the tautological
section `t` coming from `g`. Stacks 055M identifies `(X_R)⁰` with the inverse image of `X⁰`, so
`t` of the closed point lies in `(X_R)⁰`; the discrete valuation ring case says `(X_R)⁰` is open,
hence stable under generalization, so `t` of the generic point lies in `(X_R)⁰` too, and its
image in `X` is `x'`.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_of_isLocallyNoetherian'`
  is the topological reduction: on a locally Noetherian source, `X⁰` contains every
  generalization of each of its points over which the fibre is geometrically reduced.
* `AlgebraicGeometry.ConnectedAlongSection.stableUnderGeneralization_locus` is the same statement
  packaged for a morphism all of whose fibres are geometrically reduced.
* `AlgebraicGeometry.ConnectedAlongSection.isLocallyNoetherian_base` is the local Noetherianity
  of the base of a sectioned morphism whose source is locally Noetherian.
* `AlgebraicGeometry.ConnectedAlongSection.isConstructible_locus` is the constructibility of `X⁰`
  on a Noetherian source, the input Stacks 0540 needs.
* `AlgebraicGeometry.ConnectedAlongSection.locus_mem_nhds_of_isConstructible` is Stacks 055Q for
  a Noetherian source.
* `AlgebraicGeometry.ConnectedAlongSection.isOpen_locus_of_isConstructible` is Stacks 055R for a
  Noetherian source.

## Implementation notes

**Where the constructibility comes from.** The source's proof of Stacks 055Q applies Stacks 0540
to `E = X⁰`, and Stacks 0540 *requires `E` to be constructible*. That input is
`AlgebraicGeometry.ConnectedAlongSection.isConstructible_locus` below: Stacks 055P,
`AlgebraicGeometry.ConnectedAlongSection.isLocallyConstructible_locus`, makes `X⁰` locally
constructible for a morphism of finite presentation with a section, and a locally constructible
subset of a Noetherian scheme is constructible, the underlying space being prespectral,
quasi-compact and quasi-separated. Finite presentation is not an extra hypothesis here: a
Noetherian source makes `f` quasi-compact and quasi-separated, and it makes the base locally
Noetherian through the section, so `f` locally of finite type is locally of finite presentation.
The `\uses` list of Stacks 055Q does not mention Stacks 055P, but the appeal to Stacks 0540
cannot do without it: in `Spec ℤ` the set `{(0), (p)}` is stable under generalization and is not
a neighbourhood of `(p)`, so generalization-stability alone is strictly weaker than the
conclusion.

**The Noetherian hypothesis on the source.** What is not carried out here is the source's other
reduction, the limit approximation descending `f` and `s` to a finite type `ℤ`-algebra; that is
what removes the Noetherian hypothesis, since stability under generalization pulls back along any
continuous map and Stacks 055M identifies the locus of a base change with the inverse image of
the locus. Stacks 055Q and 055R without any Noetherian hypothesis are
`AlgebraicGeometry.ConnectedAlongSection.locus_mem_nhdsSet_fiberComponent` and
`AlgebraicGeometry.ConnectedAlongSection.isOpen_locus`, proved along the route of
Stacks 055N → 055P → 055Q.

**Non-vacuity.** `IsOpen`, `StableUnderGeneralization` and `∈ nhds x` are all satisfied by `∅`
and by `Set.univ`, so the statements below would be worthless if `X⁰` were not pinned down.
It is: `AlgebraicGeometry.ConnectedAlongSection.locus_inter_preimage` computes `X⁰ ∩ X_y` as the
connected component of `s y` in `X_y` for every `y`, which determines `X⁰` completely;
`AlgebraicGeometry.ConnectedAlongSection.section_mem_locus` shows `X⁰ ≠ ∅` unconditionally; and
`AlgebraicGeometry.ConnectedAlongSection.locus_ne_univ_of_not_isPreconnected_preimage` below
shows `X⁰ ≠ Set.univ` as soon as one fibre fails to be preconnected — a condition none of the
hypotheses here excludes. The hypothesis that the fibre be geometrically reduced is genuinely
consumed: it is what produces the instance
`IsReduced (q.fiber (IsLocalRing.closedPoint R))` required by the discrete valuation ring case,
whose own engine is Stacks 055J, and the slogan of Stacks 055J — a flat degeneration of a
disconnected scheme is disconnected or nonreduced — is exactly the failure of this reduction
without it.

## References

* [Stacks Project, Tag 055P](https://stacks.math.columbia.edu/tag/055P)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
* [Stacks Project, Tag 055R](https://stacks.math.columbia.edu/tag/055R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

/-- A scheme over a field is reduced as soon as its structure morphism is geometrically reduced:
base change along the identity. -/
@[ega "IV 4.6.1" "(b) ⇒ (e)"]
theorem isReduced_of_geometricallyReduced_over_field {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [GeometricallyReduced p] : IsReduced Z :=
  GeometricallyReduced.geometrically_isReduced (𝟙 (Spec (.of k))) (𝟙 Z) p
    (show IsPullback (𝟙 Z) p p (𝟙 (Spec (.of k))) from IsPullback.of_horiz_isIso ⟨by simp⟩)

namespace ConnectedAlongSection

/-- `X⁰` is not all of `X` as soon as some fibre of `f` fails to be preconnected. Together with
`AlgebraicGeometry.ConnectedAlongSection.section_mem_locus`, which says `X⁰` is never empty, this
is what keeps the openness statements below from being vacuous. -/
theorem locus_ne_univ_of_not_isPreconnected_preimage (D : ConnectedAlongSection.{u}) (y : D.Y)
    (h : ¬ _root_.IsPreconnected (D.f ⁻¹' {y} : Set D.X)) :
    D.locus ≠ Set.univ :=
  fun he => h (D.locus_eq_univ_iff.mp he y)

/-- **The discrete valuation ring case of Stacks 055R, transported along a base change.** Let
`g : Spec R ⟶ X` be a morphism from the spectrum of a discrete valuation ring and suppose the
fibre of `f` through the image of the closed point is geometrically reduced. If that image lies
in `X⁰` then so does the image of the generic point.

This is the engine of the topological reduction. Base changing `f` along `g ≫ f` gives a morphism
`X_R ⟶ Spec R`, which is again flat and locally of finite type and whose closed fibre is the
fibre of `f` through `g` of the closed point, hence reduced. Stacks 055M identifies `(X_R)⁰` with
the inverse image of `X⁰`. The morphism `g` itself provides a second section `t` of `X_R ⟶ Spec R`
besides the base change of `s`; the point `t` of the closed point lies in `(X_R)⁰` and
specializes from `t` of the generic point, and
`AlgebraicGeometry.stableUnderGeneralization_locus_of_isDiscreteValuationRing` concludes. -/
theorem mem_locus_genericPoint_of_mem_locus_closedPoint (D : ConnectedAlongSection.{u})
    [Flat D.f] [LocallyOfFiniteType D.f]
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (g : Spec (.of R) ⟶ D.X)
    (hred : GeometricallyReduced
      (D.f.fiberToSpecResidueField (D.f (g (IsLocalRing.closedPoint R)))))
    (hx : g (IsLocalRing.closedPoint R) ∈ D.locus) :
    g (genericPoint (Spec (.of R))) ∈ D.locus := by
  have hsfac : ((g ≫ D.f) ≫ D.s) ≫ D.f = 𝟙 (Spec (.of R)) ≫ (g ≫ D.f) := by
    rw [Category.assoc, D.section_fac, Category.comp_id, Category.id_comp]
  have hsRq : pullback.lift ((g ≫ D.f) ≫ D.s) (𝟙 (Spec (.of R))) hsfac ≫
      pullback.snd D.f (g ≫ D.f) = 𝟙 _ := pullback.lift_snd _ _ _
  have hbc : (g ≫ D.f) (IsLocalRing.closedPoint R) =
      D.f (g (IsLocalRing.closedPoint R)) := Scheme.Hom.comp_apply g D.f _
  have hgr : GeometricallyReduced
      ((pullback.snd D.f (g ≫ D.f)).fiberToSpecResidueField
        (IsLocalRing.closedPoint R)) := by
    have hset := geometricallyReduced_fiber_set_eq_preimage_of_isPullback D.f
      (pullback.snd D.f (g ≫ D.f)) (pullback.fst D.f (g ≫ D.f)) (g ≫ D.f)
      (IsPullback.of_hasPullback D.f (g ≫ D.f))
    have hmem : (g ≫ D.f) (IsLocalRing.closedPoint R) ∈
        {y : D.Y | GeometricallyReduced (D.f.fiberToSpecResidueField y)} :=
      Set.mem_of_eq_of_mem hbc hred
    exact (Set.ext_iff.mp hset (IsLocalRing.closedPoint R)).mpr hmem
  have hfibred : IsReduced ((pullback.snd D.f (g ≫ D.f)).fiber
      (IsLocalRing.closedPoint R)) :=
    isReduced_fiber_of_geometricallyReduced_fiberToSpecResidueField _ _ hgr
  have hlocus := locus_eq_preimage_of_isPullback D
    ⟨pullback D.f (g ≫ D.f), Spec (.of R), pullback.snd D.f (g ≫ D.f),
      pullback.lift ((g ≫ D.f) ≫ D.s) (𝟙 (Spec (.of R))) hsfac, hsRq⟩
    (pullback.fst D.f (g ≫ D.f)) (g ≫ D.f)
    (IsPullback.of_hasPullback D.f (g ≫ D.f)) (pullback.lift_fst _ _ _)
  have hstab := stableUnderGeneralization_locus_of_isDiscreteValuationRing
    (pullback.snd D.f (g ≫ D.f))
    (pullback.lift ((g ≫ D.f) ≫ D.s) (𝟙 (Spec (.of R))) hsfac) hsRq
  have htfac : g ≫ D.f = 𝟙 (Spec (.of R)) ≫ (g ≫ D.f) := (Category.id_comp _).symm
  have htpe : pullback.lift g (𝟙 (Spec (.of R))) htfac ≫ pullback.fst D.f (g ≫ D.f) = g :=
    pullback.lift_fst _ _ _
  have htp : ∀ z : Spec (.of R),
      pullback.fst D.f (g ≫ D.f) (pullback.lift g (𝟙 (Spec (.of R))) htfac z) = g z := fun z =>
    (Scheme.Hom.comp_apply _ _ z).symm.trans
      (congrArg (fun m : Spec (.of R) ⟶ D.X => m z) htpe)
  have htc : pullback.lift g (𝟙 (Spec (.of R))) htfac (IsLocalRing.closedPoint R) ∈
      ConnectedAlongSection.locus
        ⟨pullback D.f (g ≫ D.f), Spec (.of R), pullback.snd D.f (g ≫ D.f),
          pullback.lift ((g ≫ D.f) ≫ D.s) (𝟙 (Spec (.of R))) hsfac, hsRq⟩ :=
    (Set.ext_iff.mp hlocus _).mpr (Set.mem_preimage.mpr (Set.mem_of_eq_of_mem (htp _) hx))
  have hgenpre : pullback.fst D.f (g ≫ D.f)
      (pullback.lift g (𝟙 (Spec (.of R))) htfac
        (genericPoint ↥(Spec (CommRingCat.of R)))) ∈ D.locus :=
    (Set.ext_iff.mp hlocus _).mp
      (hstab ((genericPoint_specializes (α := ↥(Spec (CommRingCat.of R)))
        (IsLocalRing.closedPoint R)).map (Scheme.Hom.continuous _)) htc)
  exact Set.mem_of_eq_of_mem (htp _).symm hgenpre

/-- **The topological reduction of Stacks 055Q to the discrete valuation ring case.** On a
locally Noetherian source, if `x ∈ X⁰`, the fibre of `f` through `x` is geometrically reduced and
`x' ⤳ x`, then `x' ∈ X⁰`.

Stacks 054F realises the specialization on the spectrum of a discrete valuation ring, and
`AlgebraicGeometry.ConnectedAlongSection.mem_locus_genericPoint_of_mem_locus_closedPoint`
transports the discrete valuation ring case of Stacks 055R back along it.

Only `AlgebraicGeometry.LocallyOfFiniteType` is assumed of `f`, not finite presentation, which
on a locally Noetherian source is the same condition; this is what distinguishes the statement
from `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_of_isLocallyNoetherian`,
and the conclusion is reached here from the discrete valuation ring case alone. -/
theorem mem_locus_of_specializes_of_isLocallyNoetherian' (D : ConnectedAlongSection.{u})
    [IsLocallyNoetherian D.X] [Flat D.f] [LocallyOfFiniteType D.f]
    {x x' : D.X} (hspec : x' ⤳ x) (hx : x ∈ D.locus)
    (hred : GeometricallyReduced (D.f.fiberToSpecResidueField (D.f x))) :
    x' ∈ D.locus := by
  obtain ⟨R, _, _, _, g, hgη, rfl⟩ := exists_dvr_morphism_of_specializes D.X hspec
  exact Set.mem_of_eq_of_mem hgη.symm
    (D.mem_locus_genericPoint_of_mem_locus_closedPoint g hred hx)

/-- **The topological reduction of Stacks 055R to the discrete valuation ring case.** On a
locally Noetherian source, if every fibre of `f` is geometrically reduced then `X⁰` is stable
under generalization. -/
theorem stableUnderGeneralization_locus (D : ConnectedAlongSection.{u})
    [IsLocallyNoetherian D.X] [Flat D.f] [LocallyOfFiniteType D.f]
    [GeometricallyReduced D.f] :
    StableUnderGeneralization D.locus :=
  fun _ _ hspec hmem =>
    D.mem_locus_of_specializes_of_isLocallyNoetherian' hspec hmem inferInstance

/-- The base of a sectioned morphism is locally Noetherian as soon as the source is. The section
is an immersion, because composing it with `f` gives the identity, so it is a closed immersion
into an open subscheme of `X`. -/
theorem isLocallyNoetherian_base (D : ConnectedAlongSection.{u}) [IsLocallyNoetherian D.X] :
    IsLocallyNoetherian D.Y :=
  have : IsImmersion D.s :=
    Stacks.ConormalSequenceSplit.isImmersion_of_section D.f D.s D.section_fac
  isLocallyNoetherian_of_isClosedImmersion D.s.liftCoborder

/-- **The constructibility of `X⁰` on a Noetherian source.** For a sectioned morphism locally of
finite type with a Noetherian source, the locus `X⁰` is constructible.

Stacks 055P makes `X⁰` locally constructible: the base is locally Noetherian by
`AlgebraicGeometry.ConnectedAlongSection.isLocallyNoetherian_base`, so a morphism locally of
finite type is locally of finite presentation, and a Noetherian source makes it quasi-compact
and quasi-separated. The underlying space of a Noetherian scheme is prespectral, quasi-compact
and quasi-separated, so a locally constructible subset of it is constructible. -/
@[sga "3 VIB 3.7" "special case"]
theorem isConstructible_locus (D : ConnectedAlongSection.{u})
    [AlgebraicGeometry.IsNoetherian D.X] [LocallyOfFiniteType D.f] :
    IsConstructible D.locus :=
  have : IsLocallyNoetherian D.Y := D.isLocallyNoetherian_base
  have : QuasiSeparatedSpace D.X := ⟨fun _ _ _ _ _ _ => NoetherianSpace.isCompact _⟩
  (isLocallyConstructible_locus D).isConstructible

/-- **Stacks 055Q for a Noetherian source.** If `X` is a Noetherian scheme, `f` is flat and
locally of finite type and the fibre of `f` through `x ∈ X⁰` is geometrically reduced, then `X⁰`
is a neighbourhood of `x`.

Quantified over the points `x` of `X⁰` lying over a point `y` of `Y`, this is the conclusion of
the source: `X⁰` is a neighbourhood of `X⁰_y`. -/
@[stacks 055Q "the topological reduction to the discrete valuation ring case, for a Noetherian
source", ega "IV 15.6.5" "Noeth. source"]
theorem locus_mem_nhds_of_isConstructible (D : ConnectedAlongSection.{u})
    [AlgebraicGeometry.IsNoetherian D.X] [Flat D.f] [LocallyOfFiniteType D.f]
    {x : D.X} (hx : x ∈ D.locus)
    (hred : GeometricallyReduced (D.f.fiberToSpecResidueField (D.f x))) :
    D.locus ∈ nhds x := by
  refine (D.isConstructible_locus.mem_nhds_iff_forall_subset_closure_inter x).mpr
    fun Z hZc hZi hxZ => ?_
  have hgen := hZi.isGenericPoint_genericPoint hZc
  calc Z = closure ({hZi.genericPoint} : Set D.X) := (hZi.closure_genericPoint hZc).symm
    _ ⊆ closure (D.locus ∩ Z) := closure_mono (Set.singleton_subset_iff.mpr
        ⟨D.mem_locus_of_specializes_of_isLocallyNoetherian' (hgen.specializes hxZ) hx hred,
          hgen.mem⟩)

/-- **Stacks 055R for a Noetherian source.** If `X` is a Noetherian scheme and `f` is flat and
locally of finite type with geometrically reduced fibres, then `X⁰` is open. -/
@[stacks 055R "the topological reduction to the discrete valuation ring case, for a Noetherian
source", ega "IV 15.6.5" "Noeth. source"]
theorem isOpen_locus_of_isConstructible (D : ConnectedAlongSection.{u})
    [AlgebraicGeometry.IsNoetherian D.X] [Flat D.f] [LocallyOfFiniteType D.f]
    [GeometricallyReduced D.f] :
    IsOpen D.locus :=
  isOpen_iff_mem_nhds.mpr fun _ hx => D.locus_mem_nhds_of_isConstructible hx inferInstance

end ConnectedAlongSection

end AlgebraicGeometry

end
