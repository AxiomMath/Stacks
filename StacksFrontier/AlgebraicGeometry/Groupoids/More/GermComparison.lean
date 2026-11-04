module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CommonField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs

/-!
# The germs of the source map at two arrows with the same target

Two arrows `r`, `r'` of a groupoid scheme with the same target are the first projection and the
composite of a single point `ξ` of the scheme of composable pairs, and the second projection
`r̃` of that point is an arrow from the source of `r'` to the source of `r`.  Base changing the
source map along the target map at `r̃` and along the source map at `r̃` produces two schemes
over the germ `(R, r̃)`, and both are the scheme of composable pairs: the first by the cartesian
square relating the two projections, the second by the cartesian square relating the composite
and the second projection.  So the two germs of the source map, at `r` over the source of `r`
and at `r'` over the source of `r'`, become isomorphic after a base change which is as good as
the source and target maps are.

## Main definitions

* `AlgebraicGeometry.GermIsoOverBase` is condition (2) of the source's comparison predicate: the
  two base changes are isomorphic as germs over the base germ, at points lying over the two
  distinguished source points.
* `AlgebraicGeometry.IsoLocallyOnBase` says that two morphisms of germs are isomorphic locally
  on the base in the topology belonging to a property of morphisms of schemes.
* `AlgebraicGeometry.FlatIsoLocallyOnBase` says that two morphisms of germs are flat locally on
  the base isomorphic.

## Main results

* `AlgebraicGeometry.exists_germIsoOverBase_source` produces the base germ and the isomorphism
  of base changes for two arrows with the same target.
* `AlgebraicGeometry.flatIsoLocallyOnBase_source` is part (3): for flat source and target maps
  the two germs of the source map are flat locally on the base isomorphic.
* `AlgebraicGeometry.isoLocallyOnBase_source` is part (4) for an arbitrary property of
  morphisms of schemes, and `AlgebraicGeometry.isoLocallyOnBase_source_etale`,
  `AlgebraicGeometry.isoLocallyOnBase_source_smooth`,
  `AlgebraicGeometry.isoLocallyOnBase_source_syntomic` and
  `AlgebraicGeometry.isoLocallyOnBase_source_fppf` are its four cases.
* `AlgebraicGeometry.source_fiber_comparison_of_target_eq` is the whole lemma: its four parts
  conjoined, under no hypotheses beyond the groupoid scheme, the two arrows and the equality of
  their targets.

## Implementation notes

A germ is a pointed scheme, and the source's comparison predicate asks for a pointed scheme
`(S'', s'')` together with two *morphisms of germs* out of it.  A morphism of germs is a
morphism defined on an open neighbourhood of the distinguished point, so a pair of them is a
pair of morphisms defined on one common open neighbourhood `W` of `s''`; replacing `(S'', s'')`
by `(W, s'')` — which is legitimate because the pointed scheme is itself existentially
quantified, and which changes neither of the two base changes nor the condition of being an
isomorphism over the base, as `W.ι` is a monomorphism — turns the two morphisms of germs into
genuine morphisms of schemes out of the base.  That is the shape used here: the base germ is a
scheme `T` with a point `w`, and `g`, `g'` are morphisms of schemes out of `T`.  For the same
reason the property required of `g` and `g'` is asked of them outright rather than only at `w`:
`W` may be shrunk until it holds.  The two morphisms being compared are morphisms of schemes
rather than of germs, which again loses nothing, since only the germ of the base change at the
chosen point enters the condition and shrinking the source of `f` cuts that base change down to
an open subscheme containing that point.

Condition (2) is `AlgebraicGeometry.GermIsoOverBase`.  The two base changes are Mathlib's
`CategoryTheory.Limits.pullback`; a point of the first lying over `(w, x)` is a point whose two
projections are `w` and `x`.  An isomorphism of germs between the two base changes is recorded
as one scheme `Z` with a point `z` and two open immersions of `Z` into the two base changes
carrying `z` to the two chosen points: an open immersion is an isomorphism onto an open
subscheme, so this is exactly an open neighbourhood of each of the two points together with an
isomorphism between them matching the points.  Being an isomorphism over the base germ is
commutation of the two open immersions with the two first projections.

"Flat at a point" is flatness of the induced homomorphism of local rings, as in
`AlgebraicGeometry.MorphismOfGerms.IsFlat`; this is weaker than flatness of `g`, which is what
makes part (3) a statement about a genuinely weaker comparison than part (4).

## References

* [Stacks Project, Tag 02YF](https://stacks.math.columbia.edu/tag/02YF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The base changes of `f : X ⟶ S` along `g : T ⟶ S` and of `f' : X' ⟶ S'` along `g' : T ⟶ S'`
are isomorphic as germs over the germ `(T, w)`, at points lying over `(w, x)` and over
`(w, x')`.

This is condition (2) of the comparison predicate of Stacks 02YF. -/
def GermIsoOverBase {T S S' X X' : Scheme.{u}} (g : T ⟶ S) (g' : T ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S') (w : T) (x : X) (x' : X') : Prop :=
  ∃ (y : ↥(pullback g f)) (y' : ↥(pullback g' f')),
    (pullback.fst g f) y = w ∧ (pullback.snd g f) y = x ∧
      (pullback.fst g' f') y' = w ∧ (pullback.snd g' f') y' = x' ∧
      ∃ (Z : Scheme.{u}) (z : Z) (a : Z ⟶ pullback g f) (b : Z ⟶ pullback g' f'),
        IsOpenImmersion a ∧ IsOpenImmersion b ∧ a z = y ∧ b z = y' ∧
          b ≫ pullback.fst g' f' = a ≫ pullback.fst g f

/-- The morphisms of germs `f : (X, x) ⟶ (S, f x)` and `f' : (X', x') ⟶ (S', f' x')` are
*isomorphic locally on the base* in the topology belonging to the property `P` of morphisms of
schemes: there is a germ `(T, w)` with two morphisms to the two base germs which have `P`, along
which the two base changes become isomorphic germs over `(T, w)`.

Taking `P` to be open immersions, étale, smooth, syntomic, or flat and locally of finite
presentation gives the Zariski, étale, smooth, syntomic and fppf cases of Stacks 02YF. -/
def IsoLocallyOnBase (P : MorphismProperty Scheme.{u}) {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (x : X) (f' : X' ⟶ S') (x' : X') : Prop :=
  ∃ (T : Scheme.{u}) (w : T) (g : T ⟶ S) (g' : T ⟶ S'),
    g w = f x ∧ g' w = f' x' ∧ P g ∧ P g' ∧ GermIsoOverBase g g' f f' w x x'

/-- The morphisms of germs `f : (X, x) ⟶ (S, f x)` and `f' : (X', x') ⟶ (S', f' x')` are *flat
locally on the base isomorphic*: there is a germ `(T, w)` with two morphisms to the two base
germs which are flat at `w`, along which the two base changes become isomorphic germs over
`(T, w)`.

Flatness at `w` is much weaker than any of the conditions appearing in
`AlgebraicGeometry.IsoLocallyOnBase`, as a flat morphism need not be open. -/
def FlatIsoLocallyOnBase {X S X' S' : Scheme.{u}} (f : X ⟶ S) (x : X) (f' : X' ⟶ S') (x' : X') :
    Prop :=
  ∃ (T : Scheme.{u}) (w : T) (g : T ⟶ S) (g' : T ⟶ S'),
    g w = f x ∧ g' w = f' x' ∧ (g.stalkMap w).hom.Flat ∧ (g'.stalkMap w).hom.Flat ∧
      GermIsoOverBase g g' f f' w x x'

/-- A commutative square which is a pullback gives an isomorphism of its corner with the
pullback of the flipped cospan, compatible with both projections. -/
private theorem exists_iso_pullback_of_isPullback {P X Y Z : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g) :
    ∃ e : P ≅ pullback g f,
      e.hom ≫ pullback.fst g f = q ∧ e.hom ≫ pullback.snd g f = p :=
  ⟨h.flip.isoPullback, h.flip.isoPullback_hom_fst, h.flip.isoPullback_hom_snd⟩

/-- For two arrows with the same target there is an arrow `w` from the source of the second to
the source of the first along which the two base changes of the source map, one along the target
map and one along the source map, are isomorphic germs over `(R, w)` at points lying over the
two given arrows. -/
theorem exists_germIsoOverBase_source {S : Scheme.{u}} (G : GroupoidScheme S)
    (r r' : G.arrows.left) (h : G.target.left r = G.target.left r') :
    ∃ w : G.arrows.left, G.target.left w = G.source.left r ∧
      G.source.left w = G.source.left r' ∧
      GermIsoOverBase G.target.left G.source.left G.source.left G.source.left w r r' := by
  obtain ⟨ξ, hfst, hcomp, htarget, hsource⟩ := exists_composable_point_with_comp G r r' h
  refine ⟨(pullback.snd G.source G.target).left ξ, htarget, hsource, ?_⟩
  have hA : IsPullback (pullback.fst G.source G.target).left
      (pullback.snd G.source G.target).left G.source.left G.target.left := by
    simpa using (IsPullback.of_hasPullback G.source G.target).map (Over.forget S)
  have hB : IsPullback G.comp.left (pullback.snd G.source G.target).left
      G.source.left G.source.left := by
    simpa using (GroupoidScheme.comp_source_isPullback G).map (Over.forget S)
  obtain ⟨eA, hAf, hAs⟩ := exists_iso_pullback_of_isPullback hA
  obtain ⟨eB, hBf, hBs⟩ := exists_iso_pullback_of_isPullback hB
  refine ⟨eA.hom ξ, eB.hom ξ, ?_, ?_, ?_, ?_, (pullback G.source G.target).left, ξ,
    eA.hom, eB.hom, inferInstance, inferInstance, rfl, rfl, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hAf]
  · rw [← Scheme.Hom.comp_apply, hAs]; exact hfst
  · rw [← Scheme.Hom.comp_apply, hBf]
  · rw [← Scheme.Hom.comp_apply, hBs]; exact hcomp
  · rw [hAf, hBf]

/-- **Stacks 02YF (3).** If the source and target maps of a groupoid scheme are flat, then for
two arrows with the same target the two germs of the source map, at the first arrow over its
source and at the second arrow over its source, are flat locally on the base isomorphic. -/
@[stacks 02YF "(3)"]
theorem flatIsoLocallyOnBase_source {S : Scheme.{u}} (G : GroupoidScheme S)
    (hs : Flat G.source.left) (ht : Flat G.target.left)
    (r r' : G.arrows.left) (h : G.target.left r = G.target.left r') :
    FlatIsoLocallyOnBase G.source.left r G.source.left r' := by
  obtain ⟨w, htw, hsw, hiso⟩ := exists_germIsoOverBase_source G r r' h
  exact ⟨G.arrows.left, w, G.target.left, G.source.left, htw, hsw,
    (Flat.iff_flat_stalkMap _).1 ht w, (Flat.iff_flat_stalkMap _).1 hs w, hiso⟩

/-- **Stacks 02YF (4).** If the source and target maps of a groupoid scheme have a property `P`
of morphisms of schemes, then for two arrows with the same target the two germs of the source
map, at the first arrow over its source and at the second arrow over its source, are isomorphic
locally on the base in the topology belonging to `P`. -/
@[stacks 02YF "(4)"]
theorem isoLocallyOnBase_source {S : Scheme.{u}} (G : GroupoidScheme S)
    (P : MorphismProperty Scheme.{u}) (hs : P G.source.left) (ht : P G.target.left)
    (r r' : G.arrows.left) (h : G.target.left r = G.target.left r') :
    IsoLocallyOnBase P G.source.left r G.source.left r' := by
  obtain ⟨w, htw, hsw, hiso⟩ := exists_germIsoOverBase_source G r r' h
  exact ⟨G.arrows.left, w, G.target.left, G.source.left, htw, hsw, ht, hs, hiso⟩

/-- **Stacks 02YF (4), the étale case.** -/
@[stacks 02YF "(4) etale"]
theorem isoLocallyOnBase_source_etale {S : Scheme.{u}} (G : GroupoidScheme S)
    (hs : Etale G.source.left) (ht : Etale G.target.left)
    (r r' : G.arrows.left) (h : G.target.left r = G.target.left r') :
    IsoLocallyOnBase @Etale G.source.left r G.source.left r' :=
  isoLocallyOnBase_source G _ hs ht r r' h

/-- **Stacks 02YF (4), the smooth case.** -/
@[stacks 02YF "(4) smooth"]
theorem isoLocallyOnBase_source_smooth {S : Scheme.{u}} (G : GroupoidScheme S)
    (hs : Smooth G.source.left) (ht : Smooth G.target.left)
    (r r' : G.arrows.left) (h : G.target.left r = G.target.left r') :
    IsoLocallyOnBase @Smooth G.source.left r G.source.left r' :=
  isoLocallyOnBase_source G _ hs ht r r' h

/-- **Stacks 02YF (4), the syntomic case.** -/
@[stacks 02YF "(4) syntomic"]
theorem isoLocallyOnBase_source_syntomic {S : Scheme.{u}} (G : GroupoidScheme S)
    (hs : Syntomic G.source.left) (ht : Syntomic G.target.left)
    (r r' : G.arrows.left) (h : G.target.left r = G.target.left r') :
    IsoLocallyOnBase @Syntomic G.source.left r G.source.left r' :=
  isoLocallyOnBase_source G _ hs ht r r' h

/-- **Stacks 02YF (4), the fppf case:** source and target flat and locally of finite
presentation. -/
@[stacks 02YF "(4) fppf"]
theorem isoLocallyOnBase_source_fppf {S : Scheme.{u}} (G : GroupoidScheme S)
    (hs : Flat G.source.left) (hs' : LocallyOfFinitePresentation G.source.left)
    (ht : Flat G.target.left) (ht' : LocallyOfFinitePresentation G.target.left)
    (r r' : G.arrows.left) (h : G.target.left r = G.target.left r') :
    IsoLocallyOnBase (@Flat ⊓ @LocallyOfFinitePresentation) G.source.left r
      G.source.left r' :=
  isoLocallyOnBase_source G _ ((MorphismProperty.inf_iff _ _ _).2 ⟨hs, hs'⟩)
    ((MorphismProperty.inf_iff _ _ _).2 ⟨ht, ht'⟩) r r' h

/-- **Stacks 02YF.** Let `(U, R, s, t, c)` be a groupoid over a scheme `S` and let `r`, `r'` be
two arrows with the same target.  Writing `u = s r` and `u' = s r'`, and `F_u = s⁻¹(u)`,
`F_{u'} = s⁻¹(u')` for the scheme theoretic fibres of the source map:

1. there is a field `k` extending both `κ(u)` and `κ(u')` together with an isomorphism
   `(F_u)_k ≅ (F_{u'})_k`;
2. that isomorphism may be chosen so that a point lying over `r` maps to a point lying over
   `r'`;
3. if `s` and `t` are flat then the morphisms of germs `s : (R, r) ⟶ (U, u)` and
   `s : (R, r') ⟶ (U, u')` are flat locally on the base isomorphic;
4. if `s` and `t` are étale (resp. smooth, syntomic, or flat and locally of finite
   presentation) then those two morphisms of germs are locally on the base isomorphic in the
   étale (resp. smooth, syntomic, fppf) topology.

The four parts are `AlgebraicGeometry.exists_common_field_fiber_iso`,
`AlgebraicGeometry.exists_common_field_fiber_iso_mapping_point`,
`AlgebraicGeometry.flatIsoLocallyOnBase_source` and the four cases
`AlgebraicGeometry.isoLocallyOnBase_source_etale`,
`AlgebraicGeometry.isoLocallyOnBase_source_smooth`,
`AlgebraicGeometry.isoLocallyOnBase_source_syntomic`,
`AlgebraicGeometry.isoLocallyOnBase_source_fppf`; the flatness, étaleness, smoothness,
syntomicity and finite presentation assumptions of parts (3) and (4) appear as hypotheses of
those parts, exactly as in the source, and not of the lemma. -/
@[stacks 02YF]
theorem source_fiber_comparison_of_target_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    (r r' : G.arrows.left) (h : G.target.left r = G.target.left r') :
    (∃ (K : Type u) (_ : Field K)
      (_ : Algebra (G.objects.left.residueField (G.source.left r)) K)
      (_ : Algebra (G.objects.left.residueField (G.source.left r')) K),
      Nonempty
        (Over.mk (pullback.snd
          (G.source.left.fiberToSpecResidueField (G.source.left r))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (G.objects.left.residueField (G.source.left r)) K)))) ≅
        Over.mk (pullback.snd
          (G.source.left.fiberToSpecResidueField (G.source.left r'))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (G.objects.left.residueField (G.source.left r')) K)))))) ∧
    (∃ (K : Type u) (_ : Field K)
      (_ : Algebra (G.objects.left.residueField (G.source.left r)) K)
      (_ : Algebra (G.objects.left.residueField (G.source.left r')) K),
      let g : Spec (.of K) ⟶ Spec (.of (G.objects.left.residueField (G.source.left r))) :=
        Spec.map (CommRingCat.ofHom
          (algebraMap (G.objects.left.residueField (G.source.left r)) K))
      let g' : Spec (.of K) ⟶ Spec (.of (G.objects.left.residueField (G.source.left r'))) :=
        Spec.map (CommRingCat.ofHom
          (algebraMap (G.objects.left.residueField (G.source.left r')) K))
      let P : Scheme.{u} :=
        pullback (G.source.left.fiberToSpecResidueField (G.source.left r)) g
      let _P' : Scheme.{u} :=
        pullback (G.source.left.fiberToSpecResidueField (G.source.left r')) g'
      let POver : Over (Spec (.of K)) := Over.mk
        (pullback.snd (G.source.left.fiberToSpecResidueField (G.source.left r)) g)
      let POver' : Over (Spec (.of K)) := Over.mk
        (pullback.snd (G.source.left.fiberToSpecResidueField (G.source.left r')) g')
      ∃ (x : P) (e : POver ≅ POver'),
        ((pullback.fst
            (G.source.left.fiberToSpecResidueField (G.source.left r)) g) ≫
              G.source.left.fiberι (G.source.left r)).base x = r ∧
          ((pullback.fst
            (G.source.left.fiberToSpecResidueField (G.source.left r')) g') ≫
              G.source.left.fiberι (G.source.left r')).base (e.hom.left.base x) = r') ∧
    (Flat G.source.left → Flat G.target.left →
      FlatIsoLocallyOnBase G.source.left r G.source.left r') ∧
    (Etale G.source.left → Etale G.target.left →
      IsoLocallyOnBase @Etale G.source.left r G.source.left r') ∧
    (Smooth G.source.left → Smooth G.target.left →
      IsoLocallyOnBase @Smooth G.source.left r G.source.left r') ∧
    (Syntomic G.source.left → Syntomic G.target.left →
      IsoLocallyOnBase @Syntomic G.source.left r G.source.left r') ∧
    (Flat G.source.left → LocallyOfFinitePresentation G.source.left →
      Flat G.target.left → LocallyOfFinitePresentation G.target.left →
      IsoLocallyOnBase (@Flat ⊓ @LocallyOfFinitePresentation) G.source.left r
        G.source.left r') :=
  ⟨exists_common_field_fiber_iso G r r' h,
    exists_common_field_fiber_iso_mapping_point G r r' h,
    fun hs ht ↦ flatIsoLocallyOnBase_source G hs ht r r' h,
    fun hs ht ↦ isoLocallyOnBase_source_etale G hs ht r r' h,
    fun hs ht ↦ isoLocallyOnBase_source_smooth G hs ht r r' h,
    fun hs ht ↦ isoLocallyOnBase_source_syntomic G hs ht r r' h,
    fun hs hs' ht ht' ↦ isoLocallyOnBase_source_fppf G hs hs' ht ht' r r' h⟩

end AlgebraicGeometry
