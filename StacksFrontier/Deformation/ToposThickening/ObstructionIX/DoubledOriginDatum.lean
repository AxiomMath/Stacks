module

public import StacksFrontier.AlgebraicGeometry.Scheme.Separation.DoubledOrigin

/-!
# The canonical doubled-origin gluing datum

`StacksFrontier.AlgebraicGeometry.Scheme.Separation.DoubledOrigin` builds the gluing data
`AlgebraicGeometry.doubledOriginGlueData` of two copies of countably infinite-dimensional affine
space glued by the identity off the origin, and states the results about the doubled-origin scheme
for an arbitrary `AlgebraicGeometry.DoubledOriginData`, which is gluing data *together with*
identifications of its charts and overlaps with the prescribed models. What it does not record is
that the canonical gluing data carries such identifications. This file supplies them.

## Main definitions

* `AlgebraicGeometry.doubledOriginIndexEquiv`: the identification of `Fin 2` with the index type of
  `AlgebraicGeometry.doubledOriginGlueData`.
* `AlgebraicGeometry.doubledOriginDatum`: the canonical `DoubledOriginData`, whose underlying
  gluing data is `AlgebraicGeometry.doubledOriginGlueData`.

## Main results

* `AlgebraicGeometry.doubledOriginOverlapι_self` and
  `AlgebraicGeometry.doubledOriginOverlapι_of_ne` compute the canonical inclusion of a standard
  overlap, and `AlgebraicGeometry.doubledOriginOverlapSwap_self`,
  `AlgebraicGeometry.doubledOriginOverlapSwap_of_ne` the overlap symmetry.
* `AlgebraicGeometry.doubledOriginGlueData_V_self`,
  `AlgebraicGeometry.doubledOriginGlueData_V_of_ne`,
  `AlgebraicGeometry.doubledOriginGlueData_f_self`,
  `AlgebraicGeometry.doubledOriginGlueData_f_of_ne`,
  `AlgebraicGeometry.doubledOriginGlueData_t_self` and
  `AlgebraicGeometry.doubledOriginGlueData_t_of_ne` compute the overlaps, the overlap inclusions
  and the transition maps of the canonical gluing data.

## Implementation notes

`doubledOriginOverlap`, `doubledOriginOverlapι` and `doubledOriginOverlapSwap` are defined by a
case split on whether the two chart indices agree, and the two branches of `doubledOriginOverlapι`
and `doubledOriginOverlapSwap` are obtained by transporting a morphism along the resulting type
equation. The transport is inert, so each of the six computation lemmas above is a reflexivity once
the indices are concrete; `fin_cases` makes them so, and that is the whole proof. Stating them is
what lets the fields of `doubledOriginDatum` be proved by `eqToHom` algebra instead of by a defeq
check inside each rewrite.

The index type of `doubledOriginGlueData` is `ULift (Fin 2)`, but only after the gluing data
unfolds. `doubledOriginIndexEquiv` therefore ascribes `Equiv.ulift.symm` at the glue data's *own*
index type: used through that name, an index never carries a cast, so `rw` and `simp` can abstract
over the terms built from it. Written inline as `Equiv.ulift.symm`, every such rewrite instead has
to re-check `Fin 2 ≃ ULift (Fin 2)` against `Fin 2 ≃ (doubledOriginGlueData k).J`, which no longer
type-checks once the surrounding goal has been normalized.

For the same reason the chart and overlap identifications of the canonical gluing data are opaque
at `implicit` transparency, which is where instance search and the rewrite machinery look;
`doubledOriginGlueData` and `CategoryTheory.GlueData.ofGlueData'` are therefore marked
`implicit_reducible` for this file.

## References

* [Stacks Project, Tag 01KL](https://stacks.math.columbia.edu/tag/01KL)
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k]

attribute [local implicit_reducible] AlgebraicGeometry.doubledOriginGlueData
  CategoryTheory.GlueData.ofGlueData'

/-- The self-overlap of a chart is the whole affine space. -/
public lemma doubledOriginOverlap_self (i : Fin 2) :
    doubledOriginOverlap k i i = infiniteAffineSpace k :=
  ite_eq_left rfl

/-- The overlap of two distinct charts is the punctured affine space. -/
public lemma doubledOriginOverlap_of_ne {i j : Fin 2} (h : i ≠ j) :
    doubledOriginOverlap k i j = (puncturedInfiniteAffineSpace k).toScheme :=
  ite_eq_right h

/-- On a self-overlap the canonical inclusion is the identity. -/
public lemma doubledOriginOverlapι_self (i : Fin 2) :
    doubledOriginOverlapι k i i = eqToHom (doubledOriginOverlap_self k i) := by
  fin_cases i <;> rfl

/-- On the overlap of two distinct charts the canonical inclusion is the inclusion of the
punctured affine space. -/
public lemma doubledOriginOverlapι_of_ne {i j : Fin 2} (h : i ≠ j) :
    doubledOriginOverlapι k i j =
      eqToHom (doubledOriginOverlap_of_ne k h) ≫ (puncturedInfiniteAffineSpace k).ι := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | rfl

/-- The symmetry of a self-overlap is the identity. -/
public lemma doubledOriginOverlapSwap_self (i : Fin 2) :
    doubledOriginOverlapSwap k i i = 𝟙 (doubledOriginOverlap k i i) := by
  fin_cases i <;> rfl

/-- The symmetry of the overlap of two distinct charts is the identification of both with the
punctured affine space. -/
public lemma doubledOriginOverlapSwap_of_ne {i j : Fin 2} (h : i ≠ j) :
    doubledOriginOverlapSwap k i j =
      eqToHom ((doubledOriginOverlap_of_ne k h).trans
        (doubledOriginOverlap_of_ne k (Ne.symm h)).symm) := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | rfl

/-- The two charts of the canonical gluing data, indexed by `Fin 2`. -/
public def doubledOriginIndexEquiv : Fin 2 ≃ (doubledOriginGlueData k).J :=
  Equiv.ulift.symm

/-- Distinct chart indices name distinct charts of the canonical gluing data. -/
public lemma doubledOriginIndexEquiv_ne {i j : Fin 2} (h : i ≠ j) :
    doubledOriginIndexEquiv k i ≠ doubledOriginIndexEquiv k j :=
  fun hq ↦ h ((doubledOriginIndexEquiv k).injective hq)

/-- Every chart of the canonical gluing data is the affine space. -/
public lemma doubledOriginGlueData_U (a : (doubledOriginGlueData k).J) :
    (doubledOriginGlueData k).U a = infiniteAffineSpace k := rfl

/-- The self-overlap of a chart of the canonical gluing data is the affine space. -/
public lemma doubledOriginGlueData_V_self (a : (doubledOriginGlueData k).J) :
    (doubledOriginGlueData k).V (a, a) = infiniteAffineSpace k := by
  dsimp only [doubledOriginGlueData, CategoryTheory.GlueData.ofGlueData']
  exact dite_eq_left rfl

/-- The overlap of two distinct charts of the canonical gluing data is the punctured affine
space. -/
public lemma doubledOriginGlueData_V_of_ne {a b : (doubledOriginGlueData k).J} (h : a ≠ b) :
    (doubledOriginGlueData k).V (a, b) = (puncturedInfiniteAffineSpace k).toScheme := by
  dsimp only [doubledOriginGlueData, CategoryTheory.GlueData.ofGlueData']
  exact dite_eq_right h

/-- The inclusion of a self-overlap into its chart is the identity. -/
public lemma doubledOriginGlueData_f_self (a : (doubledOriginGlueData k).J) :
    (doubledOriginGlueData k).f a a =
      eqToHom ((doubledOriginGlueData_V_self k a).trans
        (doubledOriginGlueData_U k a).symm) := by
  dsimp only [doubledOriginGlueData, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f']
  split_ifs with h
  · rfl
  · exact absurd rfl h

/-- The inclusion of the overlap of two distinct charts into the first of them is the inclusion of
the punctured affine space. -/
public lemma doubledOriginGlueData_f_of_ne {a b : (doubledOriginGlueData k).J} (h : a ≠ b) :
    (doubledOriginGlueData k).f a b =
      eqToHom (doubledOriginGlueData_V_of_ne k h) ≫ (puncturedInfiniteAffineSpace k).ι := by
  dsimp only [doubledOriginGlueData, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f']
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- The transition map of a self-overlap is the identity. -/
public lemma doubledOriginGlueData_t_self (a : (doubledOriginGlueData k).J) :
    (doubledOriginGlueData k).t a a = 𝟙 ((doubledOriginGlueData k).V (a, a)) := by
  dsimp only [doubledOriginGlueData, CategoryTheory.GlueData.ofGlueData']
  split_ifs with h
  · simp
  · exact absurd rfl h

/-- The transition map between the two overlaps of a pair of distinct charts is the identification
of both with the punctured affine space. -/
public lemma doubledOriginGlueData_t_of_ne {a b : (doubledOriginGlueData k).J} (h : a ≠ b) :
    (doubledOriginGlueData k).t a b =
      eqToHom ((doubledOriginGlueData_V_of_ne k h).trans
        (doubledOriginGlueData_V_of_ne k (Ne.symm h)).symm) := by
  dsimp only [doubledOriginGlueData, CategoryTheory.GlueData.ofGlueData']
  split_ifs with h'
  · exact absurd h' h
  · simp

/-- The standard overlap of two charts is the overlap of the canonical gluing data. -/
public lemma doubledOriginOverlap_eq_glueData_V (i j : Fin 2) :
    doubledOriginOverlap k i j =
      (doubledOriginGlueData k).V
        (doubledOriginIndexEquiv k i, doubledOriginIndexEquiv k j) := by
  classical
  by_cases h : i = j
  · subst j
    rw [doubledOriginOverlap_self, doubledOriginGlueData_V_self]
  · rw [doubledOriginOverlap_of_ne k h,
      doubledOriginGlueData_V_of_ne k (doubledOriginIndexEquiv_ne k h)]

/-- **Stacks Project, Tag 01KL.** Countably infinite-dimensional affine space with its origin
doubled, as a `DoubledOriginData`: the canonical gluing data of two copies of the affine space,
together with the identifications of its charts and overlaps with the standard models. -/
@[stacks 01KL "doubled_origin_scheme"]
public def doubledOriginDatum : DoubledOriginData k where
  glueData := doubledOriginGlueData k
  indexEquiv := doubledOriginIndexEquiv k
  chartIso i := eqToIso (doubledOriginGlueData_U k (doubledOriginIndexEquiv k i))
  overlapIso i j := eqToIso (doubledOriginOverlap_eq_glueData_V k i j)
  overlap_f i j := by
    classical
    by_cases h : i = j
    · subst j
      rw [doubledOriginGlueData_f_self]
      simp [eqToIso, doubledOriginOverlapι_self]
    · rw [doubledOriginGlueData_f_of_ne k (doubledOriginIndexEquiv_ne k h)]
      simp [eqToIso, doubledOriginOverlapι_of_ne k h]
  transition i j := by
    classical
    by_cases h : i = j
    · subst j
      simp [eqToIso, doubledOriginOverlapSwap_self]
    · rw [doubledOriginGlueData_t_of_ne k (doubledOriginIndexEquiv_ne k h)]
      simp [eqToIso, doubledOriginOverlapSwap_of_ne k h]

end AlgebraicGeometry

end

end
