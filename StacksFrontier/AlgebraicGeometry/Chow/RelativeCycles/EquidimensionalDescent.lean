module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSupport
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EquidimensionalCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatPullbackSupport
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksCore.Tactic.StacksAttribute

/-!
# Equidimensionality of a family of cycles under base change and flat pullback

Equidimensionality of a family of cycles on the fibres of `f : X ⟶ S` is preserved by base
change along any morphism `g : S' ⟶ S` of the base and by flat pullback along any morphism
`j : U ⟶ X` of the source which is flat, locally of finite type and of relative dimension `e`
— the pullback being a family of `(r + e)`-cycles. Both operations change the support by taking
its inverse image, and a closed subset bounding the support pulls back to a closed subset
bounding the new one: under base change its relative dimension over the new base is unchanged,
and under flat pullback it grows by exactly `e`.

Taken in jointly surjective families, both operations moreover detect equidimensionality. Let
`{g i : T i ⟶ S}` be an fppf covering, with projections `p i : X ×_S T i ⟶ X` and
`q i : X ×_S T i ⟶ T i`. A family `α` of `r`-cycles on the fibres of `f` is equidimensional
exactly when every base change `g i ^* α` is.

The same criterion holds for a jointly surjective family `{f i : X i ⟶ X}` of flat morphisms
locally of finite type of relative dimension `e`: there `α` is equidimensional exactly when
every flat pullback `f i ^* α`, a family of `(r + e)`-cycles on the fibres of `X i / S`, is.

Equidimensionality is a condition on the support alone, so both statements are descent
statements for closed subsets of bounded relative dimension, the support of a base change or
of a flat pullback being the inverse image of the support of `α` by Tag 0H4V. In one direction
a bounding closed subscheme `W ⊆ X` pulls back to the bounding closed subscheme
`W ×_X (X ×_S T i)` of `X ×_S T i`, whose relative dimension over `T i` is bounded because
relative dimension is stable under base change.
In the other direction, the members `g i` of an fppf covering are universally open, hence so are
the projections `p i`; so if `V i ⊆ X ×_S T i` bounds `p i ⁻¹' Supp α`, then
`X ∖ ⋃ i p i '' (X ×_S T i ∖ V i)` is a closed subset of `X` containing `Supp α` whose preimage
in `X ×_S T i` lies in `V i`, and the local dimension of its fibres is read off there.

## Main results

* `Stacks.Chow.exists_idealSheafData_of_fppfCovering` — a subset of the source is contained in a
  closed subscheme of relative dimension at most `r` over the base as soon as its preimage in
  each member of an fppf covering is.
* `Stacks.Chow.isEquidimensional_iff_forall_of_fppfCovering` — the support form of the descent
  along an fppf covering of the base.
* `Stacks.Chow.isEquidimensional_iff_forall_baseChangeFamily` — **Tag 0H5M**: equidimensionality
  of a family of cycles on the fibres is local for an fppf covering of the base.
* `Stacks.Chow.isEquidimensional_iff_forall_of_jointlySurjective_flat` — the support form of the
  descent along a jointly surjective family of flat morphisms of the source.
* `Stacks.Chow.isEquidimensional_iff_forall_flatPullbackFamily` — **Tag 0H5N**:
  equidimensionality of a family of cycles on the fibres may be checked on the flat pullbacks
  along a jointly surjective family of flat morphisms of the source locally of finite type of
  fixed relative dimension.
* `Stacks.Chow.isEquidimensional_baseChangeFamily` — base change along an arbitrary morphism of
  the base preserves equidimensionality.
* `Stacks.Chow.isEquidimensional_flatPullbackFamily` — flat pullback along a morphism of the
  source of relative dimension `e` carries an equidimensional family of `r`-cycles to an
  equidimensional family of `(r + e)`-cycles.

## Implementation notes

The base-changed and the flat-pulled-back families enter the two descent arguments only through
their supports, so each argument is carried out once for an arbitrary family of cycles whose
support is the inverse image of the support of `α`; `Stacks.Chow.supportOfFamily_baseChangeFamily`
and `Stacks.Chow.supportOfFamily_flatPullbackFamily`, the base-change and flat-pullback clauses
of Tag 0H4V, then specialize those arguments to the base change `g i ^* α` of Tag 0H4N and to
the flat pullback `f i ^* α` of Section 0H4N. The relative-cycle condition of Tag 0H50 plays no
role and is absent from the statements, which therefore hold for every family of cycles on the
fibres.

The two stability statements, in contrast, are about the base change and the flat pullback
themselves, so there the support identification enters directly: its base-change half as proved
in `Stacks.Chow.supportOfFamily_baseChangeFamily`, and for a flat pullback only the inclusion
of supports, which is all that is needed and which follows from the coefficient of a flat
pullback at a point being a multiple of the coefficient at its image.

Closed subsets are presented as supports of ideal sheaves, as in the definition of
`Stacks.Chow.IsEquidimensional`; the bounding subscheme built in the descent direction is the
one attached to the vanishing ideal of the closed subset constructed above.

For a covering of the source by flat morphisms of exact relative dimension `e` the dimension
bound on the base is recovered by subtracting `e`, the local dimension of a fibre of a
composition with a flat first factor being the sum of the local dimensions of the fibres of the
two factors.

## References

* [Stacks Project, Tag 0H5K](https://stacks.math.columbia.edu/tag/0H5K)
* [Stacks Project, Tag 0H5M](https://stacks.math.columbia.edu/tag/0H5M)
* [Stacks Project, Tag 0H5N](https://stacks.math.columbia.edu/tag/0H5N)
* [Stacks Project, Tag 0H4V](https://stacks.math.columbia.edu/tag/0H4V)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

section FppfCovering

variable {S : Scheme.{u}} {I : Type v} {T : I → Scheme.{u}}

/-- Every member of an fppf covering is flat. -/
theorem flat_of_mem_fppfPrecoverage (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fppfPrecoverage S) (i : I) : Flat (g i) := by
  rw [Scheme.fppfPrecoverage_eq_inf] at hg
  exact ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp hg.1).2 i

/-- Every member of an fppf covering is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_mem_fppfPrecoverage (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fppfPrecoverage S) (i : I) :
    LocallyOfFinitePresentation (g i) := by
  rw [Scheme.fppfPrecoverage_eq_inf] at hg
  exact ((Scheme.ofArrows_mem_precoverage_iff (P := @LocallyOfFinitePresentation)).mp hg.2).2 i

/-- An fppf covering is jointly surjective. -/
theorem exists_mem_range_of_mem_fppfPrecoverage (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fppfPrecoverage S) (s : S) :
    ∃ i, s ∈ Set.range (g i) := by
  rw [Scheme.fppfPrecoverage_eq_inf] at hg
  exact ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp hg.1).1 s

/-- A member of an fppf covering of a locally Noetherian scheme is locally Noetherian, being
locally of finite type over it. -/
theorem isLocallyNoetherian_of_mem_fppfPrecoverage [IsLocallyNoetherian S] (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fppfPrecoverage S) (i : I) :
    IsLocallyNoetherian (T i) :=
  let : LocallyOfFinitePresentation (g i) :=
    locallyOfFinitePresentation_of_mem_fppfPrecoverage g hg i
  LocallyOfFiniteType.isLocallyNoetherian (g i)

end FppfCovering

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### Fibres of a closed subscheme of bounded relative dimension -/

/-- The local dimension of a fibre at any of its points is bounded by the relative dimension of
the morphism, which is read at the corresponding point of the source. -/
private theorem topologicalKrullDimAt_fiber_le {Y S : Scheme.{u}} (h : Y ⟶ S)
    [LocallyOfFiniteType h] {d : ℕ} (hh : RelativeDimensionLE h d) {y : Y} {s : S}
    (hys : h y = s) (z : h.fiber s) (hz : y = h.fiberι s z) :
    topologicalKrullDimAt (h.fiber s) z ≤ (d : WithBot ℕ∞) := by
  subst hys
  have hpoint : h.asFiber y = z := by
    apply (h.fiberHomeo (h y)).injective
    apply Subtype.ext
    change h.fiberι (h y) (h.asFiber y) = h.fiberι (h y) z
    simpa only [h.fiberι_asFiber] using hz
  simpa only [relativeDimensionLEAt_iff, hpoint] using hh y

/-- A morphism of relative dimension at most `d` has fibres of dimension at most `d`, the
dimension of a space being the supremum of its local dimensions. -/
private theorem topologicalKrullDim_fiber_le {Y S : Scheme.{u}} (h : Y ⟶ S)
    [LocallyOfFiniteType h] {d : ℕ} (hh : RelativeDimensionLE h d) (s : S) :
    topologicalKrullDim (h.fiber s) ≤ (d : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun z => ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim]
  exact topologicalKrullDimAt_fiber_le h hh
    (Set.mem_singleton_iff.mp (h.fiberHomeo s z).2) z rfl

/-- The fibre over `s` of a closed subscheme `W ⊆ X` of `X/S` is the part of `W` lying in the
fibre `X_s`: the fibre of `W ⟶ X ⟶ S` over `s` is homeomorphic to the support of the pullback
of the ideal sheaf of `W` to `X_s`. -/
private def fiberSupportHomeo {X S : Scheme.{u}} (f : X ⟶ S) (W : X.IdealSheafData) (s : S) :
    (W.subschemeι ≫ f).fiber s ≃ₜ (W.comap (f.fiberι s)).support :=
  let J := W.comap (f.fiberι s)
  let e := W.comapIso (f.fiberι s) ≪≫ pullbackSymmetry (f.fiberι s) W.subschemeι ≪≫
    pullbackRightPullbackFstIso f (S.fromSpecResidueField s) W.subschemeι
  e.hom.homeomorph.symm.trans (J.subschemeIso.hom.homeomorph.trans J.gluedHomeo)

/-- If `W ⊆ X` has relative dimension at most `d` over `S`, then the part of `W` in each fibre
of `X/S` has dimension at most `d`. -/
private theorem topologicalKrullDim_comap_support_le {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {d : ℕ} (W : X.IdealSheafData)
    (hW : RelativeDimensionLE (W.subschemeι ≫ f) d) (s : S) :
    topologicalKrullDim (W.comap (f.fiberι s)).support ≤ (d : WithBot ℕ∞) :=
  calc topologicalKrullDim (W.comap (f.fiberι s)).support
      = topologicalKrullDim ((W.subschemeι ≫ f).fiber s) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (fiberSupportHomeo f W s).isHomeomorph).symm
    _ ≤ (d : WithBot ℕ∞) := topologicalKrullDim_fiber_le _ hW s

/-- A bound on the relative dimension of a closed subscheme of `X/S` is inherited by every
closed subscheme whose support is smaller: the local dimension of a fibre of the smaller one is
bounded by the dimension of the corresponding fibre of the larger one. -/
private theorem relativeDimensionLE_of_support_subset {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {d : ℕ} (A B : X.IdealSheafData)
    (hAB : (A.support : Set X) ⊆ (B.support : Set X))
    (hB : RelativeDimensionLE (B.subschemeι ≫ f) d) :
    RelativeDimensionLE (A.subschemeι ≫ f) d := by
  intro x
  rw [relativeDimensionLEAt_iff]
  set s := f (A.subschemeι x) with hs
  set JA := A.comap (f.fiberι s) with hJA
  set JB := B.comap (f.fiberι s) with hJB
  have hfiber : (JA.support : Set (f.fiber s)) ⊆ (JB.support : Set (f.fiber s)) := by
    intro z hz
    rw [hJA, Scheme.IdealSheafData.support_comap] at hz
    rw [hJB, Scheme.IdealSheafData.support_comap]
    exact hAB hz
  have hdimAB : topologicalKrullDim JA.support ≤ topologicalKrullDim JB.support := by
    have hrange : (JA.support : Set (f.fiber s)) ⊆
        Set.range (Subtype.val : JB.support → f.fiber s) := fun z hz => ⟨⟨z, hfiber hz⟩, rfl⟩
    let C : Set JB.support := (Subtype.val : JB.support → f.fiber s) ⁻¹' JA.support
    let e : C ≃ₜ JA.support :=
      (Topology.IsEmbedding.subtypeVal.homeomorphImage C).trans
        (Homeomorph.setCongr (Set.image_preimage_eq_of_subset hrange))
    calc topologicalKrullDim JA.support = topologicalKrullDim C :=
          (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm
      _ ≤ topologicalKrullDim JB.support := topologicalKrullDim_subspace_le _ C
  have hdimA : topologicalKrullDimAt ((A.subschemeι ≫ f).fiber s)
      ((A.subschemeι ≫ f).asFiber x) ≤ topologicalKrullDim JA.support :=
    (topologicalKrullDimAt_eq_of_homeomorph (fiberSupportHomeo f A s) _).trans_le
      (topologicalKrullDimAt_le_topologicalKrullDim _)
  exact hdimA.trans (hdimAB.trans (topologicalKrullDim_comap_support_le f B hB s))

/-! ### A closed subscheme pulled back along a morphism of the ambient scheme -/

/-- The closed immersion of the pullback of an ideal sheaf sits in a commuting square over the
closed immersion of the ideal sheaf itself. -/
private theorem comap_subschemeι_comp {X Y : Scheme.{u}} (p : X ⟶ Y) (W : Y.IdealSheafData) :
    (W.comap p).subschemeι ≫ p =
      (W.comap p).subschemeMap W p (W.le_map_comap p) ≫ W.subschemeι :=
  (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm

/-- That square is cartesian: the pullback of an ideal sheaf cuts out the fibre product of the
closed subscheme with the ambient morphism. -/
private theorem isPullback_comap_subschemeι {X Y : Scheme.{u}} (p : X ⟶ Y)
    (W : Y.IdealSheafData) :
    IsPullback (W.comap p).subschemeι ((W.comap p).subschemeMap W p (W.le_map_comap p)) p
      W.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (comap_subschemeι_comp p W) <| by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]

/-- For a closed subscheme `W ⊆ X` of `X/S` and a morphism `gg : T ⟶ S`, the closed subscheme
`W ×_X (X ×_S T)` of `X ×_S T` is the base change of `W` along `gg`. -/
private theorem isPullback_comap_subschemeι_comp {X S T : Scheme.{u}} (f : X ⟶ S) (gg : T ⟶ S)
    (W : X.IdealSheafData) :
    IsPullback ((W.comap (pullback.fst f gg)).subschemeMap W (pullback.fst f gg)
        (W.le_map_comap _))
      ((W.comap (pullback.fst f gg)).subschemeι ≫ pullback.snd f gg) (W.subschemeι ≫ f) gg :=
  (isPullback_comap_subschemeι (pullback.fst f gg) W).flip.paste_vert
    (IsPullback.of_hasPullback f gg)

/-- A bound on the relative dimension of a closed subscheme of `X/S` is inherited by its base
change along any morphism of the base. -/
private theorem relativeDimensionLE_comap_subschemeι {X S T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (gg : T ⟶ S) {d : ℕ} (W : X.IdealSheafData)
    (hW : RelativeDimensionLE (W.subschemeι ≫ f) d) :
    RelativeDimensionLE ((W.comap (pullback.fst f gg)).subschemeι ≫ pullback.snd f gg) d :=
  RelativeDimensionLE.of_isPullback (isPullback_comap_subschemeι_comp f gg W) hW

/-- The map of closed subschemes induced by a morphism `p`, followed by the closed immersion of
`W` and a morphism `f`, is the closed immersion of the pullback followed by `p ≫ f`. -/
private theorem subschemeMap_comp_subschemeι_comp {X Y S : Scheme.{u}} (p : X ⟶ Y)
    (W : Y.IdealSheafData) (f : Y ⟶ S) :
    (W.comap p).subschemeι ≫ p ≫ f =
      (W.comap p).subschemeMap W p (W.le_map_comap p) ≫ W.subschemeι ≫ f := by
  rw [← Category.assoc, comap_subschemeι_comp, Category.assoc]

/-- A point of a closed subscheme `W ⊆ Y` lying under a point of `X` lifts to the pullback of `W`
along `p : X ⟶ Y`. -/
private theorem exists_subschemeMap_eq {X Y : Scheme.{u}} (p : X ⟶ Y) (W : Y.IdealSheafData)
    (w : W.subscheme) (x : X) (hx : p x = W.subschemeι w) :
    ∃ z, (W.comap p).subschemeMap W p (W.le_map_comap p) z = w := by
  obtain ⟨z, hz⟩ : x ∈ Set.range (W.comap p).subschemeι := by
    rw [(W.comap p).range_subschemeι, coe_support_comap, Set.mem_preimage, hx,
      ← W.range_subschemeι]
    exact Set.mem_range_self w
  refine ⟨z, W.subschemeι.isClosedEmbedding.injective ?_⟩
  calc W.subschemeι ((W.comap p).subschemeMap W p (W.le_map_comap p) z)
      = p ((W.comap p).subschemeι z) :=
        (congrArg (fun k => k z) (comap_subschemeι_comp p W)).symm
    _ = W.subschemeι w := hz ▸ hx

/-! ### Descent of the dimension bound -/

/-- A subset `E` of `X` lies in a closed set whose preimage in each member of a family of open
maps `p i` lies in a prescribed closed set `V i`, as soon as the preimage of `E` does. -/
private theorem exists_idealSheafData_comap_support_subset {X : Scheme.{u}} (E : Set X)
    {I : Type v} {Y : I → Scheme.{u}} (p : ∀ i, Y i ⟶ X) (hp : ∀ i, IsOpenMap (p i))
    (V : ∀ i, (Y i).IdealSheafData) (hV : ∀ i, p i ⁻¹' E ⊆ (V i).support) :
    ∃ W : X.IdealSheafData, E ⊆ (W.support : Set X) ∧
      ∀ i, ((W.comap (p i)).support : Set (Y i)) ⊆ (V i).support := by
  set bad : Set X := ⋃ i, p i '' ((V i).support : Set (Y i))ᶜ with hbad
  have hbadopen : IsOpen bad :=
    isOpen_iUnion fun i => hp i _ (V i).support.isClosed.isOpen_compl
  obtain ⟨W, hW⟩ : ∃ W : X.IdealSheafData, (W.support : Set X) = badᶜ :=
    ⟨.vanishingIdeal ⟨badᶜ, hbadopen.isClosed_compl⟩, by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl⟩
  refine ⟨W, ?_, fun i y hy => ?_⟩
  · rw [hW]
    intro x hx hxbad
    obtain ⟨i, y, hyout, hxy⟩ := Set.mem_iUnion.mp hxbad
    exact hyout (hV i (by rw [Set.mem_preimage, hxy]; exact hx))
  · rw [coe_support_comap, Set.mem_preimage, hW] at hy
    by_contra hno
    exact hy (Set.mem_iUnion.mpr ⟨i, y, hno, rfl⟩)

/-- Descent of a bound on the relative dimension of a closed subscheme containing a given subset
along a jointly surjective family of flat morphisms locally of finite presentation of the base.
Away from the complements of the given bounding subschemes the dimension bound holds, and those
complements have open image because the projections are universally open. -/
private theorem exists_idealSheafData_of_jointlySurjective {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (E : Set X) {I : Type v} {T : I → Scheme.{u}}
    (g : ∀ i, T i ⟶ S) [∀ i, Flat (g i)] [∀ i, LocallyOfFinitePresentation (g i)]
    (hsurj : ∀ x : X, ∃ i, x ∈ Set.range (pullback.fst f (g i)))
    (h : ∀ i, ∃ V : (pullback f (g i)).IdealSheafData,
      pullback.fst f (g i) ⁻¹' E ⊆ (V.support : Set ↥(pullback f (g i))) ∧
        RelativeDimensionLE (V.subschemeι ≫ pullback.snd f (g i)) r) :
    ∃ W : X.IdealSheafData, E ⊆ (W.support : Set X) ∧
      RelativeDimensionLE (W.subschemeι ≫ f) r := by
  choose V hVsupp hVdim using h
  obtain ⟨W, hWE, hWV⟩ := exists_idealSheafData_comap_support_subset E
    (fun i => pullback.fst f (g i)) (fun i => (pullback.fst f (g i)).isOpenMap) V hVsupp
  refine ⟨W, hWE, fun w => ?_⟩
  obtain ⟨i, y, hiy⟩ := hsurj (W.subschemeι w)
  obtain ⟨z, hqz⟩ := exists_subschemeMap_eq (pullback.fst f (g i)) W w y hiy
  have hdim := relativeDimensionLE_of_support_subset (pullback.snd f (g i)) _ (V i) (hWV i)
    (hVdim i)
  rw [relativeDimensionLEAt_iff]
  have hdimEq := topologicalKrullDimAt_fiber_eq_of_isPullback
    (isPullback_comap_subschemeι_comp f (g i) W) z
  rw [hqz] at hdimEq
  have hbound := hdim z
  rw [relativeDimensionLEAt_iff, hdimEq] at hbound
  exact hbound

/-- A subset of the source is contained in a closed subscheme of relative dimension at most `r`
over the base as soon as its preimage in each member of an fppf covering of the base is. -/
theorem exists_idealSheafData_of_fppfCovering {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (E : Set X) {I : Type v} {T : I → Scheme.{u}}
    (g : ∀ i, T i ⟶ S) (hg : Presieve.ofArrows T g ∈ Scheme.fppfPrecoverage S)
    (h : ∀ i, ∃ V : (pullback f (g i)).IdealSheafData,
      pullback.fst f (g i) ⁻¹' E ⊆ (V.support : Set ↥(pullback f (g i))) ∧
        RelativeDimensionLE (V.subschemeι ≫ pullback.snd f (g i)) r) :
    ∃ W : X.IdealSheafData, E ⊆ (W.support : Set X) ∧
      RelativeDimensionLE (W.subschemeι ≫ f) r := by
  have : ∀ i, Flat (g i) := flat_of_mem_fppfPrecoverage g hg
  have : ∀ i, LocallyOfFinitePresentation (g i) :=
    locallyOfFinitePresentation_of_mem_fppfPrecoverage g hg
  have hX : Presieve.ofArrows (fun i => pullback f (g i)) (fun i => pullback.fst f (g i))
      ∈ Scheme.fppfPrecoverage X :=
    Precoverage.mem_coverings_of_isPullback g hg f (fun i => pullback.fst f (g i))
      (fun i => pullback.snd f (g i)) fun i => IsPullback.of_hasPullback f (g i)
  exact exists_idealSheafData_of_jointlySurjective f r E g
    (exists_mem_range_of_mem_fppfPrecoverage _ hX) h

/-- The support form of Tag 0H5M: for an fppf covering `{g i : T i ⟶ S}` of the base, a family
of `r`-cycles on the fibres of `f : X ⟶ S` is equidimensional exactly when each family on the
fibres of `X ×_S T i ⟶ T i` whose support is the preimage of its support is equidimensional.
The base changes of the family have that property, by the base-change clause of Tag 0H4V. -/
@[stacks 0H5M "generalized: the families over the covering are an argument and enter only \
through their supports, so no relative-cycle condition is needed; \
`isEquidimensional_iff_forall_baseChangeFamily` instantiates them at the base changes themselves"]
theorem isEquidimensional_iff_forall_of_fppfCovering {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r)
    {I : Type v} {T : I → Scheme.{u}} (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fppfPrecoverage S)
    (β : ∀ i, FamilyOfCycles (pullback.snd f (g i)) r)
    (hβ : ∀ i, supportOfFamily (pullback.snd f (g i)) (β i) =
      pullback.fst f (g i) ⁻¹' supportOfFamily f α) :
    letI (i : I) : IsLocallyNoetherian (T i) :=
      isLocallyNoetherian_of_mem_fppfPrecoverage g hg i
    (IsEquidimensional f r α ↔
      ∀ i, IsEquidimensional (pullback.snd f (g i)) r (β i)) := by
  have (i : I) : IsLocallyNoetherian (T i) :=
    isLocallyNoetherian_of_mem_fppfPrecoverage g hg i
  constructor
  · rintro ⟨W, hsupp, hdim⟩ i
    refine ⟨W.comap (pullback.fst f (g i)), ?_, ?_⟩
    · rw [hβ i, coe_support_comap]
      exact Set.preimage_mono hsupp
    · exact relativeDimensionLE_comap_subschemeι f (g i) W hdim
  · intro hall
    refine exists_idealSheafData_of_fppfCovering f r (supportOfFamily f α) g hg fun i => ?_
    obtain ⟨V, hVs, hVd⟩ := hall i
    exact ⟨V, hβ i ▸ hVs, hVd⟩

/-- **Stacks Project, Tag 0H5M.** Equidimensionality of a family of `r`-cycles on the fibres of
`f : X ⟶ S` is local for an fppf covering `{g i : T i ⟶ S}` of the base: the family is
equidimensional exactly when every base change `g i ^* α` is. -/
@[stacks 0H5M]
theorem isEquidimensional_iff_forall_baseChangeFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r)
    {I : Type v} {T : I → Scheme.{u}} (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fppfPrecoverage S) :
    letI (i : I) : IsLocallyNoetherian (T i) :=
      isLocallyNoetherian_of_mem_fppfPrecoverage g hg i
    (IsEquidimensional f r α ↔
      ∀ i, IsEquidimensional (pullback.snd f (g i)) r (baseChangeFamily f (g i) r α)) :=
  isEquidimensional_iff_forall_of_fppfCovering f r α g hg
    (fun i => baseChangeFamily f (g i) r α)
    fun i => supportOfFamily_baseChangeFamily f (g i) r α

/-! ### Descent along a jointly surjective family of flat morphisms of the source -/

/-- At any point of the source, the fibre of a morphism of relative dimension `e` through that
point has local dimension exactly `e`: the fibre is equidimensional of dimension `e`, and a
scheme locally of finite type over a field has local dimension equal to its dimension at each
of its points. -/
private theorem topologicalKrullDimAt_fiber_apply_eq_of_relativeDimension {Y Z : Scheme.{u}}
    (g : Y ⟶ Z) [LocallyOfFiniteType g] {e : ℕ} (hg : RelativeDimension g e) (y : Y) :
    topologicalKrullDimAt (g.fiber (g y)) (g.asFiber y) = (e : WithBot ℕ∞) := by
  have hFT : LocallyOfFiniteType (g.fiberToSpecResidueField (g y)) := by
    change LocallyOfFiniteType (pullback.snd g (Z.fromSpecResidueField (g y)))
    infer_instance
  obtain ⟨heq, hdim⟩ := hg (g y) ⟨g.asFiber y⟩
  exact AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional (Z.residueField (g y))
    (g.fiber (g y)) (g.fiberToSpecResidueField (g y)) heq hdim (g.asFiber y)

/-- A morphism of relative dimension `e` has relative dimension at most `e`. -/
private theorem relativeDimensionLE_of_relativeDimension {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [LocallyOfFiniteType g] {e : ℕ} (hg : RelativeDimension g e) : RelativeDimensionLE g e :=
  fun y => (topologicalKrullDimAt_fiber_apply_eq_of_relativeDimension g hg y).le

/-- A relative-dimension bound depends only on the morphism and on the bound, so it transports
along an equality of morphisms and an equality of bounds. -/
private theorem relativeDimensionLE_of_eq {Y Z : Scheme.{u}} {g k : Y ⟶ Z}
    [LocallyOfFiniteType g] [LocallyOfFiniteType k] {d d' : ℕ} (hgk : g = k) (hdd : d = d')
    (hg : RelativeDimensionLE g d) : RelativeDimensionLE k d' := by
  subst hgk
  subst hdd
  exact hg

/-- A bound `r` on the relative dimension of a closed subscheme `W ⊆ X` of `X/S` becomes the bound
`r + e` for its pullback along a morphism `j` of relative dimension at most `e`. -/
private theorem relativeDimensionLE_comap_subschemeι_comp {X Y S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (j : Y ⟶ X) [LocallyOfFiniteType j] {r e : ℕ} (W : X.IdealSheafData)
    (hj : RelativeDimensionLE j e) (hW : RelativeDimensionLE (W.subschemeι ≫ f) r) :
    RelativeDimensionLE ((W.comap j).subschemeι ≫ j ≫ f) (r + e) := by
  have hqft : LocallyOfFiniteType ((W.comap j).subschemeMap W j (W.le_map_comap j)) :=
    MorphismProperty.of_isPullback (isPullback_comap_subschemeι j W)
      (P := @LocallyOfFiniteType) inferInstance
  exact relativeDimensionLE_of_eq (subschemeMap_comp_subschemeι_comp j W f).symm (Nat.add_comm e r)
    (RelativeDimensionLE.comp _ (W.subschemeι ≫ f)
      (RelativeDimensionLE.of_isPullback (isPullback_comap_subschemeι j W) hj) hW)

/-- Subtracting the relative dimension of a flat factor: if `g` is flat of relative dimension
exactly `e` and the composition `g ≫ k` has relative dimension at most `r + e`, then `k` has
relative dimension at most `r` at every point of the image of `g`. The local dimension of a
fibre of `g ≫ k` is the sum of those of the fibres of `g` and of `k` because `g` is flat, and
the summand contributed by `g` is `e`, which may be cancelled. -/
private theorem relativeDimensionLEAt_of_flat_relativeDimension {Y Z T : Scheme.{u}} (g : Y ⟶ Z)
    (k : Z ⟶ T) [LocallyOfFiniteType g] [LocallyOfFiniteType k] [Flat g] (r e : ℕ)
    (hg : RelativeDimension g e) (hcomp : RelativeDimensionLE (g ≫ k) (r + e)) (y : Y) :
    RelativeDimensionLEAt k r (g y) := by
  rw [relativeDimensionLEAt_iff]
  have hlocal := topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt g k y (Flat.stalkMap g y)
  rw [topologicalKrullDimAt_fiber_apply_eq_of_relativeDimension g hg y] at hlocal
  have hbot : (e : WithBot ℕ∞) ≠ ⊥ := by simp
  have htop : (e : WithBot ℕ∞) ≠ ⊤ := fun he =>
    (by simp : (e : ℕ∞) ≠ ⊤) (WithBot.coe_eq_top.mp he)
  refine (WithBot.add_le_add_iff_right' hbot htop).mp ?_
  calc topologicalKrullDimAt (k.fiber (k (g y))) (k.asFiber (g y)) + (e : WithBot ℕ∞)
      = (e : WithBot ℕ∞) + topologicalKrullDimAt (k.fiber (k (g y))) (k.asFiber (g y)) :=
        add_comm _ _
    _ = topologicalKrullDimAt ((g ≫ k).fiber ((g ≫ k) y)) ((g ≫ k).asFiber y) := hlocal.symm
    _ ≤ ((r + e : ℕ) : WithBot ℕ∞) := hcomp y
    _ = (r : WithBot ℕ∞) + (e : WithBot ℕ∞) := by norm_cast

/-- The support form of Tag 0H5N: for a jointly surjective family `{fi i : Xi i ⟶ X}` of flat
morphisms locally of finite type of relative dimension `e`, a family of `r`-cycles on the fibres
of `f : X ⟶ S` is equidimensional exactly when each family of `(r + e)`-cycles on the fibres of
`Xi i ⟶ S` whose support is the preimage of its support is equidimensional. The flat pullbacks
of the family have that property, by the flat-pullback clause of Tag 0H4V. -/
theorem isEquidimensional_iff_forall_of_jointlySurjective_flat {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r e : ℕ) (α : FamilyOfCycles f r)
    {I : Type v} {Xi : I → Scheme.{u}} (fi : ∀ i, Xi i ⟶ X)
    [∀ i, LocallyOfFiniteType (fi i)] [∀ i, Flat (fi i)]
    (hdim : ∀ i, RelativeDimension (fi i) e)
    (hsurj : ∀ x : X, ∃ i, x ∈ Set.range (fi i))
    (β : ∀ i, FamilyOfCycles (fi i ≫ f) (r + e))
    (hβ : ∀ i, supportOfFamily (fi i ≫ f) (β i) = fi i ⁻¹' supportOfFamily f α) :
    IsEquidimensional f r α ↔ ∀ i, IsEquidimensional (fi i ≫ f) (r + e) (β i) := by
  classical
  constructor
  · rintro ⟨W, hsupp, hdimW⟩ i
    refine ⟨W.comap (fi i), ?_, ?_⟩
    · rw [hβ i, coe_support_comap]
      exact Set.preimage_mono hsupp
    · exact relativeDimensionLE_comap_subschemeι_comp f (fi i) W
        (relativeDimensionLE_of_relativeDimension (fi i) (hdim i)) hdimW
  · intro hall
    have hX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    choose V hVsupp hVdim using fun i =>
      (isEquidimensional_iff (fi i ≫ f) (r + e) (β i)).mp (hall i)
    obtain ⟨W, hWE, hWV⟩ := exists_idealSheafData_comap_support_subset (supportOfFamily f α) fi
      (fun i => (fi i).isOpenMap) V fun i => by rw [← hβ i]; exact hVsupp i
    refine ⟨W, hWE, fun w => ?_⟩
    obtain ⟨i, y, hiy⟩ := hsurj (W.subschemeι w)
    obtain ⟨z, hqz⟩ := exists_subschemeMap_eq (fi i) W w y hiy
    have hpull := isPullback_comap_subschemeι (fi i) W
    have hqft : LocallyOfFiniteType
        ((W.comap (fi i)).subschemeMap W (fi i) (W.le_map_comap (fi i))) :=
      MorphismProperty.of_isPullback hpull (P := @LocallyOfFiniteType) inferInstance
    have hqflat : Flat ((W.comap (fi i)).subschemeMap W (fi i) (W.le_map_comap (fi i))) :=
      MorphismProperty.of_isPullback hpull (P := @Flat) inferInstance
    have hcomp := relativeDimensionLE_of_eq (subschemeMap_comp_subschemeι_comp (fi i) W f) rfl
      (relativeDimensionLE_of_support_subset (fi i ≫ f) _ (V i) (hWV i) (hVdim i))
    rw [← hqz]
    exact relativeDimensionLEAt_of_flat_relativeDimension _ (W.subschemeι ≫ f) r e
      (RelativeDimension.of_isPullback hpull (hdim i)) hcomp z

/-- **Stacks Project, Tag 0H5N.** Equidimensionality of a family of `r`-cycles on the fibres of
`f : X ⟶ S` can be checked after a jointly surjective family `{fi i : Xi i ⟶ X}` of flat
morphisms locally of finite type of relative dimension `e`: the family is equidimensional
exactly when every flat pullback `fi i ^* α`, a family of `(r + e)`-cycles on the fibres of
`Xi i ⟶ S`, is. -/
@[stacks 0H5N]
theorem isEquidimensional_iff_forall_flatPullbackFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r e : ℕ) (α : FamilyOfCycles f r)
    {I : Type v} {Xi : I → Scheme.{u}} (fi : ∀ i, Xi i ⟶ X)
    [∀ i, LocallyOfFiniteType (fi i)] [∀ i, Flat (fi i)]
    (hdim : ∀ i, RelativeDimension (fi i) e)
    (hsurj : ∀ x : X, ∃ i, x ∈ Set.range (fi i)) :
    IsEquidimensional f r α ↔
      ∀ i, IsEquidimensional (fi i ≫ f) (r + e)
        (flatPullbackFamily f (fi i ≫ f) (fi i) rfl e (hdim i) r α) :=
  isEquidimensional_iff_forall_of_jointlySurjective_flat f r e α fi hdim hsurj
    (fun i => flatPullbackFamily f (fi i ≫ f) (fi i) rfl e (hdim i) r α)
    fun i => supportOfFamily_flatPullbackFamily f (fi i ≫ f) (fi i) rfl e (hdim i) r α

/-! ### Stability of equidimensionality under base change and flat pullback -/

/-- **Stacks Project, Tag 0H5K, the base-change clause.** The base change of an equidimensional
family of `r`-cycles along an arbitrary morphism `g : S' ⟶ S` of the base is equidimensional:
its support is the inverse image of the support of the original family, and the base change of
a bounding closed subscheme bounds it and has the same relative dimension over `S'`. -/
@[stacks 0H5K "base change"]
theorem isEquidimensional_baseChangeFamily {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (g : S' ⟶ S) [IsLocallyNoetherian S']
    (r : ℕ) (α : FamilyOfCycles f r) (hα : IsEquidimensional f r α) :
    IsEquidimensional (pullback.snd f g) r (baseChangeFamily f g r α) := by
  obtain ⟨W, hsupp, hdim⟩ := hα
  refine ⟨W.comap (pullback.fst f g), ?_, relativeDimensionLE_comap_subschemeι f g W hdim⟩
  rw [supportOfFamily_baseChangeFamily f g r α, coe_support_comap]
  exact Set.preimage_mono hsupp

/-- The support of the flat pullback of a cycle on a fibre is contained in the inverse image of
its support: the coefficient of the pullback at a point is a multiple of the coefficient of the
cycle at the image point, and the inverse image of the support is closed. -/
private theorem tsupport_fiberCycleFlatPullback_subset {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU) (e : ℕ) (he : RelativeDimension j e)
    (s : S) (r : ℕ) (c : FiberCycleGroup f s r) :
    tsupport (fiberCycleFlatPullback f fU j h e he s r c : AlgebraicCycle (fU.fiber s) ℤ) ⊆
      fiberRestrict f fU j h s ⁻¹' tsupport (c : AlgebraicCycle (f.fiber s) ℤ) := by
  refine closure_minimal ?_
    ((isClosed_tsupport _).preimage (fiberRestrict f fU j h s).continuous)
  intro y hy
  rw [Function.mem_support, fiberCycleFlatPullback_apply] at hy
  exact subset_closure (Function.mem_support.mpr (mul_ne_zero_iff.mp hy).1)

/-- The support of the flat pullback of a family of cycles on fibres is contained in the inverse
image of the support of the family: a point of the former lies in the support of the pullback of
the member over its image in the base, hence over a point of the support of that member. -/
private theorem supportOfFamily_flatPullbackFamily_subset {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU) (e : ℕ) (he : RelativeDimension j e)
    (r : ℕ) (α : FamilyOfCycles f r) :
    supportOfFamily fU (flatPullbackFamily f fU j h e he r α) ⊆ j ⁻¹' supportOfFamily f α := by
  intro y hy
  obtain ⟨s, z, hz, hzy⟩ := (mem_supportOfFamily fU _ y).mp hy
  refine (mem_supportOfFamily f α (j y)).mpr
    ⟨s, fiberRestrict f fU j h s z,
      tsupport_fiberCycleFlatPullback_subset f fU j h e he s r (α s) hz, ?_⟩
  have hι := congrArg (fun k : fU.fiber s ⟶ X => k z) (fiberRestrict_fiberι f fU j h s)
  simp only [Scheme.Hom.comp_apply] at hι
  rw [hι, hzy]

/-- **Stacks Project, Tag 0H5K, the flat-pullback clause.** The flat pullback of an
equidimensional family of `r`-cycles along a morphism `j : U ⟶ X` of schemes over `S` which is
flat, locally of finite type and of relative dimension `e` is an equidimensional family of
`(r + e)`-cycles: the inverse image of a closed subscheme bounding the support of the original
family bounds the support of the pullback, and its relative dimension over `S` is at most
`r + e` because it maps to the bounding subscheme by a morphism of relative dimension `e`. -/
@[stacks 0H5K "flat pullback"]
theorem isEquidimensional_flatPullbackFamily {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (fU : U ⟶ S) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU) (e : ℕ)
    (he : RelativeDimension j e) (r : ℕ) (α : FamilyOfCycles f r)
    (hα : IsEquidimensional f r α) :
    IsEquidimensional fU (r + e) (flatPullbackFamily f fU j h e he r α) := by
  obtain ⟨W, hsupp, hdimW⟩ := hα
  subst h
  refine ⟨W.comap j, ?_, relativeDimensionLE_comap_subschemeι_comp f j W
    (relativeDimensionLE_of_relativeDimension j he) hdimW⟩
  rw [coe_support_comap]
  exact (supportOfFamily_flatPullbackFamily_subset f _ j rfl e he r α).trans
    (Set.preimage_mono hsupp)

end Stacks.Chow

end
