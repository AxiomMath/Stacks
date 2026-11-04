module

public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.GroupoidSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.MaximalLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension

/-!
# The maximal relative-dimension locus in a groupoid slice

Work in the groupoid situation of a scheme `U'` mapping to the object scheme of a groupoid
whose structure maps are locally of finite type, and let
`h : U' ×_{g, U, t} R ⟶ U` be the composite of the projection to the arrow scheme with the
source map.  The locus of the fibre product on which `h` has relative dimension at most `d`
is open, and it is the inverse image along the projection to `U'` of an open of `U'`.

That the locus is open is the pointwise openness of the fibre-dimension function.  That it
descends to `U'` is the general transfer principle for maximal loci of a groupoid
presentation, applied to the property "locally of finite type and of relative dimension at
most `d`": the property admits maximal open loci for locally-of-finite-type morphisms, and
those loci are stable under base change because the fibres of a morphism and of its base
change have the same local dimension.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.exists_open_with_preimage_maximal_relativeDimensionLE`: the greatest open
  of `U' ×_{g, U, t} R` on which `h` has relative dimension at most `d` is the inverse image of
  an open of `U'`.

## Implementation notes

The maximality assertion is phrased with `IsGreatest` on the lattice of opens, matching the
Cohen–Macaulay locus of the same situation.  The relative-dimension bound is applied to the
restriction `V.ι ≫ h` of `h` to an open `V`, so the transfer principle can be invoked with the
property taken on composites; the local lemma that an open immersion does not change the local
dimension of a fibre is what identifies the restricted bound with the pointwise one.

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- On an open `W` where `f` has relative dimension at most `d`, every fibre through a point of
`W` has local dimension at most `d`. -/
private lemma topologicalKrullDimAt_fiber_le_of_relativeDimensionLE
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ} {W : X.Opens}
    (hW : RelativeDimensionLE (W.ι ≫ f) d) {x : X} (hx : x ∈ W) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞) := by
  have h := hW ⟨x, hx⟩
  unfold RelativeDimensionLEAt at h
  rwa [fiberDimensionAt_comp_openImmersion W.ι f ⟨x, hx⟩] at h

/-- The open where the fibre dimension of `f` is at most `d` has relative dimension at most `d`. -/
private lemma relativeDimensionLE_fiberDimensionAt_le_opens
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (d : ℕ) :
    RelativeDimensionLE
      (Scheme.Opens.ι (⟨_, isOpen_setOf_fiberDimensionAt_le f d⟩ : X.Opens) ≫ f) d := by
  intro x
  rw [relativeDimensionLEAt_iff, fiberDimensionAt_comp_openImmersion _ f x]
  exact x.property

/-- The relative-dimension-at-most-`d` locus of a locally finite type morphism is its greatest
open of relative dimension at most `d`. -/
private lemma exists_greatest_relativeDimensionLE_locus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (d : ℕ) :
    ∃ V : X.Opens, IsGreatest {W : X.Opens | RelativeDimensionLE (W.ι ≫ f) d} V :=
  ⟨_, relativeDimensionLE_fiberDimensionAt_le_opens f d, fun _ hW _ hx ↦
    topologicalKrullDimAt_fiber_le_of_relativeDimensionLE f hW hx⟩

/-- A point lies in the greatest relative-dimension-at-most-`d` open exactly when the fibre
through it has local dimension at most `d`. -/
private lemma greatest_relativeDimensionLE_locus_mem_iff
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (d : ℕ) (V : X.Opens)
    (hV : IsGreatest {W : X.Opens | RelativeDimensionLE (W.ι ≫ f) d} V) (x : X) :
    x ∈ V ↔ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞) :=
  ⟨topologicalKrullDimAt_fiber_le_of_relativeDimensionLE f hV.1,
    fun hx ↦ hV.2 (relativeDimensionLE_fiberDimensionAt_le_opens f d) hx⟩

/-- In the locally finite type groupoid situation, the relative-dimension-at-most-`d` locus of
`h : U' ×_{g, U, t} R ⟶ U` is the inverse image of an open of `U'`, and it is the greatest open
on which the restriction of `h` has that dimension bound.

This is **Stacks Project, Tag 047W, case (1)**. -/
@[stacks 047W "relative dimension at most d"]
public theorem exists_open_with_preimage_maximal_relativeDimensionLE
    (D : LocallyOfFiniteTypeGroupoidSituation) (d : ℕ) :
    let _ : LocallyOfFiniteType
        (pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left) := inferInstance
    ∃ W : D.U'.Opens,
      IsGreatest
        {V : (pullback D.g D.groupoid.target.left).Opens |
          RelativeDimensionLE
            (V.ι ≫ pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left) d}
        ((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W) := by
  let P : MorphismProperty Scheme := fun X Y f ↦
    ∃ (_ : LocallyOfFiniteType f), RelativeDimensionLE f d
  let Q : MorphismProperty Scheme := @LocallyOfFiniteType
  have hPQ {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFiniteType f] :
      P f ↔ RelativeDimensionLE f d := by
    refine ⟨fun ⟨h, hd⟩ ↦ ?_, fun hd ↦ ⟨inferInstance, hd⟩⟩
    simpa only [Subsingleton.elim h (inferInstance : LocallyOfFiniteType f)] using hd
  have hmax : ∀ {X Y : Scheme} (f : X ⟶ Y), Q f →
      ∃ V : X.Opens, IsGreatest {W : X.Opens | P (W.ι ≫ f)} V := by
    intro X Y f hf
    let _ : LocallyOfFiniteType f := hf
    simpa only [hPQ] using exists_greatest_relativeDimensionLE_locus f d
  have hbase : ∀ {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {p : X' ⟶ X} {q : Y' ⟶ Y}, Q f → Q q → IsPullback p f' f q →
      ∀ {V : X.Opens}, IsGreatest {W : X.Opens | P (W.ι ≫ f)} V →
        IsGreatest {W' : X'.Opens | P (W'.ι ≫ f')} (p ⁻¹ᵁ V) := by
    intro X Y X' Y' f f' p q hf hq hp V hV
    let _ : LocallyOfFiniteType f := hf
    let _ : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback hp (P := @LocallyOfFiniteType) inferInstance
    simp only [hPQ] at hV ⊢
    constructor
    · intro x
      rw [relativeDimensionLEAt_iff, fiberDimensionAt_comp_openImmersion (p ⁻¹ᵁ V).ι f' x]
      change topologicalKrullDimAt (f'.fiber (f' x.1)) (f'.asFiber x.1) ≤ (d : WithBot ℕ∞)
      rw [topologicalKrullDimAt_fiber_eq_of_isPullback hp x.1]
      exact (greatest_relativeDimensionLE_locus_mem_iff f d V hV (p x.1)).mp x.property
    · intro W hW x hx
      apply (greatest_relativeDimensionLE_locus_mem_iff f d V hV (p x)).mpr
      rw [← topologicalKrullDimAt_fiber_eq_of_isPullback hp x]
      exact topologicalKrullDimAt_fiber_le_of_relativeDimensionLE f' hW hx
  have h := exists_open_with_preimage_maximal_locus P Q Q (fun {_ _} _ h ↦ h)
    hmax hbase D.groupoid D.g inferInstance inferInstance inferInstance
  simpa only [hPQ] using h

end AlgebraicGeometry
