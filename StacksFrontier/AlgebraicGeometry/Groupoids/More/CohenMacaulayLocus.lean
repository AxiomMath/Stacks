module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.GroupoidSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.MaximalLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Witnesses
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
public import StacksCore.Tactic.StacksAttribute

/-!
# The Cohen–Macaulay locus in a groupoid slice

In the flat, locally finitely presented groupoid situation, the largest open of
`U' ×_{g, U, t} R` on which the induced map to `U` is Cohen–Macaulay is pulled back from an open
of `U'`.  Maximal Cohen–Macaulay opens exist for every morphism locally of finite presentation —
the union of all Cohen–Macaulay opens is one, because Cohen–Macaulayness at a point is detected
on any open neighbourhood — and they commute with flat, locally finitely presented base change,
so `AlgebraicGeometry.exists_open_with_preimage_maximal_locus` applies.

## Main results

* `AlgebraicGeometry.exists_open_with_preimage_maximal_cohenMacaulayLocus` identifies the
  largest Cohen–Macaulay locus with the preimage of an open.

## Implementation notes

The locally Noetherian property of the fibres, required by the definition of a Cohen–Macaulay
morphism, is included in the locus predicate rather than assumed: it is automatic for a morphism
locally of finite presentation, but the predicate has to be stated for an arbitrary morphism in
order to be a `MorphismProperty`.  The maximality assertion is expressed by `IsGreatest` for the
open subscheme.

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- For a morphism locally of finite presentation, an open subscheme is a Cohen–Macaulay locus
exactly when the morphism is Cohen–Macaulay at each of its points. -/
private theorem cohenMacaulay_on_open_iff {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (U : X.Opens) :
    (∃ hfU : ∀ y : Y, IsLocallyNoetherian ((U.ι ≫ f).fiber y),
      Scheme.Hom.IsCohenMacaulay (U.ι ≫ f) hfU) ↔
    ∀ x : X, x ∈ U → Scheme.Hom.IsCohenMacaulayAt f
      (fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y) x := by
  have hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y) :=
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f
  constructor
  · rintro ⟨hU, hCM⟩ x hx
    exact isCohenMacaulayAt_right_of_comp_of_flatAt U.ι f hf hU ⟨x, hx⟩ (hCM ⟨x, hx⟩)
      ((Flat.iff_flat_stalkMap U.ι).mp inferInstance ⟨x, hx⟩)
  · exact fun h => ⟨isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (U.ι ≫ f),
      fun xU => isCohenMacaulayAt_comp U.ι f
        (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation U.ι) hf _
        xU (Scheme.Hom.isCohenMacaulayAt_of_isOpenImmersion U.ι
          (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation U.ι) xU)
        (h xU.1 xU.2)⟩

/-- Every morphism locally of finite presentation has a greatest Cohen–Macaulay open: the union
of all of them. -/
private theorem exists_greatest_cohenMacaulay_open {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    ∃ V : X.Opens,
      IsGreatest
        {U : X.Opens | ∃ hf : ∀ y : Y, IsLocallyNoetherian ((U.ι ≫ f).fiber y),
          Scheme.Hom.IsCohenMacaulay (U.ι ≫ f) hf} V := by
  classical
  let I := {U : X.Opens // ∃ hf : ∀ y : Y,
    IsLocallyNoetherian ((U.ι ≫ f).fiber y), Scheme.Hom.IsCohenMacaulay (U.ι ≫ f) hf}
  let V : X.Opens := ⨆ U : I, U.1
  have hfV : ∀ y : Y, IsLocallyNoetherian ((V.ι ≫ f).fiber y) :=
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (V.ι ≫ f)
  have hV : Scheme.Hom.IsCohenMacaulay (V.ι ≫ f) hfV := by
    intro xV
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp xV.2
    obtain ⟨hfU, hCMU⟩ := U.2
    have hUV : U.1 ≤ V := le_iSup (fun T : I => T.1) U
    let j : U.1.toScheme ⟶ V.toScheme := X.homOfLE hUV
    let xU : U.1.toScheme := ⟨xV.1, hxU⟩
    have hxj : j xU = xV := by
      apply Subtype.ext
      change (j ≫ V.ι) xU = V.ι xV
      rw [Scheme.homOfLE_ι]
      rfl
    have hcomp : j ≫ V.ι ≫ f = U.1.ι ≫ f := by simp [j]
    have hfComp : ∀ y : Y, IsLocallyNoetherian ((j ≫ V.ι ≫ f).fiber y) := by
      simpa only [hcomp] using hfU
    have hsource : Scheme.Hom.IsCohenMacaulayAt (j ≫ V.ι ≫ f) hfComp xU := by
      simpa only [hcomp] using hCMU xU
    simpa only [hxj] using isCohenMacaulayAt_right_of_comp_of_flatAt
      j (V.ι ≫ f) hfV hfComp xU hsource ((Flat.iff_flat_stalkMap j).mp inferInstance xU)
  exact ⟨V, ⟨hfV, hV⟩, fun U hU => le_iSup (fun T : I => T.1) ⟨U, hU⟩⟩

/-- For a pullback square, Cohen–Macaulayness at `x'` of the base change `f'` is equivalent to
Cohen–Macaulayness of the canonical projection at the corresponding point of the pullback. -/
private theorem isCohenMacaulayAt_pullback_snd_iff {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (q : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback p f' f q) [LocallyOfFiniteType q]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hf' : ∀ y' : Y', IsLocallyNoetherian (f'.fiber y')) (x' : X') :
    Scheme.Hom.IsCohenMacaulayAt (pullback.snd f q)
      (isLocallyNoetherian_fiber_pullback f q hf) (sq.isoPullback.hom x') ↔
    Scheme.Hom.IsCohenMacaulayAt f' hf' x' := by
  have hmap := sq.isoPullback_hom_snd
  have hfComp : ∀ y' : Y',
      IsLocallyNoetherian ((sq.isoPullback.hom ≫ pullback.snd f q).fiber y') := by
    intro y'
    rw [hmap]
    exact hf' y'
  have hiff : Scheme.Hom.IsCohenMacaulayAt (sq.isoPullback.hom ≫ pullback.snd f q) hfComp x' ↔
      Scheme.Hom.IsCohenMacaulayAt f' hf' x' := by
    constructor
    · intro h
      convert h using 1
      exact hmap.symm
    · intro h
      convert h using 1
  constructor
  · intro h
    exact hiff.1 (isCohenMacaulayAt_comp sq.isoPullback.hom (pullback.snd f q)
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _)
      (isLocallyNoetherian_fiber_pullback f q hf) hfComp x'
      (Scheme.Hom.isCohenMacaulayAt_of_isOpenImmersion sq.isoPullback.hom
        (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _) x') h)
  · exact fun h => isCohenMacaulayAt_right_of_comp_of_flatAt sq.isoPullback.hom
      (pullback.snd f q) (isLocallyNoetherian_fiber_pullback f q hf) hfComp x' (hiff.2 h)
      ((Flat.iff_flat_stalkMap _).mp inferInstance x')

/-- Cohen–Macaulayness transfers from a morphism to its base change along a morphism locally of
finite type. -/
private theorem cohenMacaulayAt_pullback_forward {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (q : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback p f' f q) [LocallyOfFiniteType q]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hf' : ∀ y' : Y', IsLocallyNoetherian (f'.fiber y')) (x' : X')
    (h : Scheme.Hom.IsCohenMacaulayAt f hf (p x')) :
    Scheme.Hom.IsCohenMacaulayAt f' hf' x' := by
  have hfst : (pullback.fst f q) (sq.isoPullback.hom x') = p x' :=
    congrArg (fun k : X' ⟶ X => k x') sq.isoPullback_hom_fst
  exact (isCohenMacaulayAt_pullback_snd_iff f q p f' sq hf hf' x').1
    (isCohenMacaulayAt_pullback f q hf _ (by simpa only [hfst] using h))

/-- Cohen–Macaulayness descends from a flat base change along a morphism locally of finite
type. -/
private theorem cohenMacaulayAt_pullback_backward {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (q : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback p f' f q) [LocallyOfFiniteType q] [Flat q]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hf' : ∀ y' : Y', IsLocallyNoetherian (f'.fiber y')) (x' : X')
    (h : Scheme.Hom.IsCohenMacaulayAt f' hf' x') :
    Scheme.Hom.IsCohenMacaulayAt f hf (p x') := by
  have hfst : (pullback.fst f q) (sq.isoPullback.hom x') = p x' :=
    congrArg (fun k : X' ⟶ X => k x') sq.isoPullback_hom_fst
  simpa only [hfst] using isCohenMacaulayAt_of_pullback_of_flat_base f q hf _
    ((Flat.iff_flat_stalkMap q).mp inferInstance _)
    ((isCohenMacaulayAt_pullback_snd_iff f q p f' sq hf hf' x').2 h)

/-- The maximal Cohen–Macaulay locus of `h : U' ×_{g,U,t} R ⟶ U` is the
inverse image of an open of `U'`. -/
@[stacks 047W "cohen_macaulay"]
public theorem exists_open_with_preimage_maximal_cohenMacaulayLocus
    (D : FlatLocallyFinitelyPresentedGroupoidSituation) :
    ∃ W : D.U'.Opens,
      IsGreatest
        {V : D.fiberProduct.Opens |
          ∃ hf : ∀ y : D.groupoid.objects.left,
              IsLocallyNoetherian ((V.ι ≫ D.h).fiber y),
            Scheme.Hom.IsCohenMacaulay (V.ι ≫ D.h) hf}
        ((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W) := by
  let P : MorphismProperty Scheme := fun X Y f =>
    ∃ hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y),
      Scheme.Hom.IsCohenMacaulay f hf
  let Q : MorphismProperty Scheme := @LocallyOfFinitePresentation
  let R : MorphismProperty Scheme := fun X Y f => Flat f ∧ LocallyOfFinitePresentation f
  have hRQ : R ≤ Q := fun X Y f hf => hf.2
  have hmax : ∀ {X Y : Scheme} (f : X ⟶ Y), Q f →
      ∃ V : X.Opens, IsGreatest {W : X.Opens | P (W.ι ≫ f)} V := by
    intro X Y f hf
    have : LocallyOfFinitePresentation f := hf
    simpa only [P] using exists_greatest_cohenMacaulay_open f
  have hbase : ∀ {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {p : X' ⟶ X} {q : Y' ⟶ Y}, Q f → R q → IsPullback p f' f q →
      ∀ {V : X.Opens}, IsGreatest {W : X.Opens | P (W.ι ≫ f)} V →
        IsGreatest {W' : X'.Opens | P (W'.ι ≫ f')} (p ⁻¹ᵁ V) := by
    intro X Y X' Y' f f' p q hf hq hp V hV
    have : LocallyOfFinitePresentation f := hf
    have : Flat q := hq.1
    have : LocallyOfFinitePresentation q := hq.2
    have : LocallyOfFinitePresentation f' :=
      MorphismProperty.of_isPullback hp (P := @LocallyOfFinitePresentation) inferInstance
    have hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y) :=
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f
    have hf' : ∀ y' : Y', IsLocallyNoetherian (f'.fiber y') :=
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f'
    have : Flat p :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip (P := @Flat) inferInstance
    have : LocallyOfFinitePresentation p :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip
        (P := @LocallyOfFinitePresentation) inferInstance
    refine ⟨(cohenMacaulay_on_open_iff f' _).2 fun x' hx' =>
      cohenMacaulayAt_pullback_forward f q p f' hp hf hf' x'
        ((cohenMacaulay_on_open_iff f V).mp hV.1 _ hx'), fun W' hW' => ?_⟩
    let A : X.Opens := ⟨p '' (W' : Set X'), p.isOpenMap (W' : Set X') W'.2⟩
    have hAP : P (A.ι ≫ f) := by
      refine (cohenMacaulay_on_open_iff f A).2 ?_
      rintro _ ⟨x', hxW', rfl⟩
      exact cohenMacaulayAt_pullback_backward f q p f' hp hf hf' x'
        ((cohenMacaulay_on_open_iff f' W').mp hW' x' hxW')
    exact fun x' hxW' => hV.2 hAP ⟨x', hxW', rfl⟩
  exact exists_open_with_preimage_maximal_locus
    P Q R hRQ hmax hbase D.groupoid D.g
    (show R D.groupoid.source.left from ⟨inferInstance, inferInstance⟩)
    (show R D.groupoid.target.left from ⟨inferInstance, inferInstance⟩)
    (show Q D.g from inferInstance)

end AlgebraicGeometry
