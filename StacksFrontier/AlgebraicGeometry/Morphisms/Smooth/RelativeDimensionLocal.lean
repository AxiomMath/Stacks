module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Defs
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.RelativeDimensionStrata
public import StacksFrontier.Topology.Dimension.IsolatedPoint

/-!
# Smoothness of a given relative dimension is étale local

For a morphism of schemes `f : X ⟶ Y` the relative dimension of a smooth morphism is read off the
fibres: if `f` is smooth of relative dimension `n` near `x`, then the fibre `X_{f x}` has
dimension `n` at `x` (`AlgebraicGeometry.fiberDimensionAt_eq_of_smoothOfRelativeDimension`), and
conversely a smooth morphism whose fibres all have local dimension `n` is smooth of relative
dimension `n` (`Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq`). Since the local
fibre dimension is unchanged by restriction to an open, all the statements below reduce to
comparisons of fibre dimensions.

## Main results

* `AlgebraicGeometry.smoothOfRelativeDimension_unique`: the relative dimension of a morphism
  near a point is well defined.
* `AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_smoothOfRelativeDimension`: smoothness of
  relative dimension `n` is étale local on source and target. Étale morphisms are smooth of
  relative dimension `0`, which gives precomposition and base change; for the local criterion,
  `f` is smooth by the corresponding result for smoothness, so it is smooth of some relative
  dimension `m` near each point `x`, and comparing with the étale neighbourhood of `x` on which
  the relative dimension is `n` gives `m = n`.
* `AlgebraicGeometry.SmoothOfRelativeDimension.eq_zero_of_locallyQuasiFinite`: the fibres of a
  locally quasi-finite morphism are discrete, so have dimension `0`.
* `AlgebraicGeometry.exists_smoothOfRelativeDimension_nbhd_of_fiber`: a flat morphism locally of
  finite presentation whose fibre over `y` is smooth of relative dimension `n` is smooth of
  relative dimension `n` near every point over `y`. Smoothness at points of the fibre is the
  fibrewise criterion [Stacks, Tag 01V9], and the fibre dimension there is `n`.

## References

* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If `f` restricted to an open `U` is smooth of relative dimension `n`, then the fibre of `f`
through any point of `U` has dimension `n` at that point. -/
theorem fiberDimensionAt_eq_of_smoothOfRelativeDimension_ι {n : ℕ} {X Y : Scheme.{u}}
    (f : X ⟶ Y) {U : X.Opens} [SmoothOfRelativeDimension n (U.ι ≫ f)] (x : U) :
    topologicalKrullDimAt (f.fiber (f (U.ι x))) (f.asFiber (U.ι x)) = (n : WithBot ℕ∞) :=
  (fiberDimensionAt_comp_openImmersion U.ι f x).symm.trans
    (fiberDimensionAt_eq_of_smoothOfRelativeDimension (U.ι ≫ f) n x)

/-- If `f` restricted to an open `U` is smooth and the fibres of `f` have dimension `n` at every
point of `U`, then `f` restricted to `U` is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_ι_of_fiberDimensionAt_eq {n : ℕ} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : X.Opens) [Smooth (U.ι ≫ f)]
    (h : ∀ x : U, topologicalKrullDimAt (f.fiber (f (U.ι x))) (f.asFiber (U.ι x)) =
      (n : WithBot ℕ∞)) :
    SmoothOfRelativeDimension n (U.ι ≫ f) :=
  Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ n fun x =>
    (fiberDimensionAt_comp_openImmersion U.ι f x).trans (h x)

/-- A morphism with a point in its source is smooth of at most one relative dimension. -/
theorem SmoothOfRelativeDimension.eq_of_smoothOfRelativeDimension {n m : ℕ} {X Y : Scheme.{u}}
    (f : X ⟶ Y) [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] (x : X) :
    n = m := by
  have h := (fiberDimensionAt_eq_of_smoothOfRelativeDimension f n x).symm.trans
    (fiberDimensionAt_eq_of_smoothOfRelativeDimension f m x)
  exact_mod_cast h

/-- Two open neighbourhoods of a point on which a morphism is smooth of relative dimensions `n`
and `m` force `n = m`. -/
theorem smoothOfRelativeDimension_unique {n m : ℕ} {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    {U V : X.Opens} (hU : x ∈ U) (hV : x ∈ V)
    (hn : SmoothOfRelativeDimension n (U.ι ≫ f)) (hm : SmoothOfRelativeDimension m (V.ι ≫ f)) :
    n = m := by
  have h := (fiberDimensionAt_eq_of_smoothOfRelativeDimension_ι (n := n) f (U := U)
    ⟨x, hU⟩).symm.trans (fiberDimensionAt_eq_of_smoothOfRelativeDimension_ι (n := m) f (U := V)
      ⟨x, hV⟩)
  exact_mod_cast h

/-- A smooth morphism is smooth of some relative dimension near every point; the
neighbourhood is the open and closed locus of [Stacks, Tag 02NM] where the fibre dimension is
that of the point. (`AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_nbhd` is the same
statement in another file, whose imports are much heavier.) -/
private theorem exists_smoothOfRelativeDimension_relativeDimensionOpen {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f]
    (x : X) : ∃ (n : ℕ) (U : X.Opens), x ∈ U ∧ SmoothOfRelativeDimension n (U.ι ≫ f) :=
  ⟨relativeDimensionFunction f (isCohenMacaulay_fiber_of_smooth f) x,
    relativeDimensionOpen f (isCohenMacaulay_fiber_of_smooth f)
      (relativeDimensionFunction f (isCohenMacaulay_fiber_of_smooth f) x),
    (mem_relativeDimensionOpen f _ _ x).2 rfl,
    smoothOfRelativeDimension_relativeDimensionOpen f _⟩

/-- Smoothness of relative dimension `n` is étale local on the source and the target. -/
theorem isEtaleLocalOnSourceAndTarget_smoothOfRelativeDimension (n : ℕ) :
    IsEtaleLocalOnSourceAndTarget (@SmoothOfRelativeDimension.{u} n) where
  precomp := ⟨fun {X Y Z} i hi f hf => by
    have : Etale i := hi
    have : SmoothOfRelativeDimension n f := hf
    have h : SmoothOfRelativeDimension (0 + n) (i ≫ f) := inferInstance
    rwa [Nat.zero_add] at h⟩
  pullbackSnd_of_etale f hf g _ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (self := smoothOfRelativeDimension_isStableUnderBaseChange n)
      (IsPullback.of_hasPullback f g) hf
  iff_forall_exists_etale_neighborhood f := by
    refine ⟨fun hf x => ⟨_, _, 𝟙 _, 𝟙 _, f, x, inferInstance, inferInstance, rfl, by simp, hf⟩,
      fun H => ?_⟩
    have : Smooth f := (isEtaleLocalOnSourceAndTarget_smooth.iff_forall_exists_etale_neighborhood
      f).2 fun x => by
        obtain ⟨U, V, a, b, h, u, ha, hb, hu, hc, hh⟩ := H x
        exact ⟨U, V, a, b, h, u, ha, hb, hu, hc, SmoothOfRelativeDimension.smooth n h⟩
    refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f n fun x => ?_
    obtain ⟨U, V, a, b, h, u, ha, hb, hu, hc, hh⟩ := H x
    obtain ⟨m, W, hxW, hW⟩ := exists_smoothOfRelativeDimension_relativeDimensionOpen f x
    have : Etale a := ha
    have : Etale b := hb
    have : SmoothOfRelativeDimension n h := hh
    have : SmoothOfRelativeDimension 0 (a ∣_ W) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (self := smoothOfRelativeDimension_isStableUnderBaseChange 0)
        (isPullback_morphismRestrict a W).flip inferInstance
    have h₁ : SmoothOfRelativeDimension (0 + m) ((a ∣_ W) ≫ W.ι ≫ f) := inferInstance
    have h₂ : SmoothOfRelativeDimension (0 + (n + 0)) ((a ⁻¹ᵁ W).ι ≫ h ≫ b) := inferInstance
    have e : (a ∣_ W) ≫ W.ι ≫ f = (a ⁻¹ᵁ W).ι ≫ h ≫ b := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hc]
    rw [e] at h₁
    have hu' : u ∈ a ⁻¹ᵁ W := by rw [Scheme.Hom.mem_preimage, hu]; exact hxW
    have hmn := SmoothOfRelativeDimension.eq_of_smoothOfRelativeDimension
      ((a ⁻¹ᵁ W).ι ≫ h ≫ b) (n := 0 + m) (m := 0 + (n + 0)) ⟨u, hu'⟩
    simp only [Nat.zero_add, Nat.add_zero] at hmn
    rw [← hmn]
    exact fiberDimensionAt_eq_of_smoothOfRelativeDimension_ι (n := m) f (U := W) ⟨x, hxW⟩

/-- A nonempty scheme which is smooth of relative dimension `n` and locally quasi-finite over a
base has `n = 0`. -/
theorem SmoothOfRelativeDimension.eq_zero_of_locallyQuasiFinite {n : ℕ} {X Y : Scheme.{u}}
    (f : X ⟶ Y) [SmoothOfRelativeDimension n f] [LocallyQuasiFinite f] [Nonempty X] : n = 0 := by
  let x : X := Classical.arbitrary X
  have : DiscreteTopology (f.fiber (f x)) := IsLocallyArtinian.discreteTopology
  have h := (fiberDimensionAt_eq_of_smoothOfRelativeDimension f n x).symm.trans
    (topologicalKrullDimAt_eq_zero_of_isIsolatedPoint _ (isOpen_discrete _))
  exact_mod_cast h

/-- A flat morphism locally of finite presentation whose fibre over `y` is smooth of relative
dimension `n` is smooth of relative dimension `n` near every point over `y`. -/
theorem exists_smoothOfRelativeDimension_nbhd_of_fiber {n : ℕ} {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (y : Y)
    [SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)] (x : X) (hx : f x = y) :
    ∃ U : X.Opens, x ∈ U ∧ SmoothOfRelativeDimension n (U.ι ≫ f) := by
  subst hx
  have hsq : IsPullback (f.fiberι (f x)) (f.fiberToSpecResidueField (f x)) f
      (Y.fromSpecResidueField (f x)) := IsPullback.of_hasPullback _ _
  have : Smooth (f.fiberToSpecResidueField (f x)) := SmoothOfRelativeDimension.smooth n _
  -- the fibre dimension of `f` at `x` is `n`
  have hdx : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (n : WithBot ℕ∞) := by
    have h := (topologicalKrullDimAt_fiber_eq_of_isPullback hsq (f.asFiber x)).symm.trans
      (fiberDimensionAt_eq_of_smoothOfRelativeDimension _ n (f.asFiber x))
    have key : ∀ z w : X, z = w → topologicalKrullDimAt (f.fiber (f z)) (f.asFiber z) =
        topologicalKrullDimAt (f.fiber (f w)) (f.asFiber w) := fun _ _ h => h ▸ rfl
    exact (key _ _ (f.fiberι_asFiber x).symm).trans h
  -- `x` lies in the smooth locus `O` of `f`
  set O := f.smoothLocus with hO
  have hxO : x ∈ O := by
    have h := Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hsq (Or.inl inferInstance)
    rw [Scheme.Hom.smoothLocus_eq_top] at h
    have h' : f.asFiber x ∈ (f.fiberι (f x)) ⁻¹ᵁ f.smoothLocus := h ▸ trivial
    rwa [Scheme.Hom.mem_preimage, f.fiberι_asFiber] at h'
  have : Smooth (O.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, ← hO,
      eq_top_iff]
    intro z _
    exact z.2
  obtain ⟨m, W, hxW, hW⟩ :=
    exists_smoothOfRelativeDimension_relativeDimensionOpen (O.ι ≫ f) ⟨x, hxO⟩
  -- fibre dimensions over `W`
  have hdW (w : W) : topologicalKrullDimAt (f.fiber (f (O.ι (W.ι w)))) (f.asFiber (O.ι (W.ι w))) =
      (m : WithBot ℕ∞) :=
    (fiberDimensionAt_comp_openImmersion O.ι f (W.ι w)).symm.trans
      (fiberDimensionAt_eq_of_smoothOfRelativeDimension_ι (n := m) (O.ι ≫ f) w)
  have hmn : m = n := by
    have h := (hdW ⟨⟨x, hxO⟩, hxW⟩).symm.trans hdx
    exact_mod_cast h
  subst hmn
  have hle : O.ι ''ᵁ W ≤ O := O.ι_image_le W
  refine ⟨O.ι ''ᵁ W, ⟨⟨x, hxO⟩, hxW, rfl⟩, ?_⟩
  have : Smooth ((O.ι ''ᵁ W).ι ≫ f) := by
    rw [← X.homOfLE_ι hle, Category.assoc]
    infer_instance
  refine smoothOfRelativeDimension_ι_of_fiberDimensionAt_eq f _ fun z => ?_
  obtain ⟨w, hw, hwz⟩ := z.2
  have key : ∀ z w : X, z = w → topologicalKrullDimAt (f.fiber (f z)) (f.asFiber z) =
      topologicalKrullDimAt (f.fiber (f w)) (f.asFiber w) := fun _ _ h => h ▸ rfl
  exact (key _ _ hwz.symm).trans (hdW ⟨w, hw⟩)

end AlgebraicGeometry

end
