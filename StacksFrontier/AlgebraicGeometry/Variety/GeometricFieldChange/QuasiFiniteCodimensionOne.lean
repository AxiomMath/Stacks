module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

/-!
# Quasi-finiteness and finiteness in codimension one

Let `f : X ⟶ Y` be locally of finite type and let `y` be a point of `Y` whose local ring is
Noetherian of dimension at most one. If `f` is generically quasi-finite — in any one of four
standard senses — then `f` is quasi-finite at every point of `X` above `y`; if moreover `f` is
proper, then `f` is finite over an open neighbourhood of `y`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.genericPoints_mem_dense_open` and
  `AlgebraicGeometry.scheme_genericPoints_mem_dense_open`: a generic point of a Noetherian space,
  respectively of a locally Noetherian scheme, lies in every dense open.
* `AlgebraicGeometry.quasiFiniteAt_of_target_stalk_dimension_le_one`: quasi-finiteness at every
  point above `y`.
* `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one`: for a proper
  morphism, an open neighbourhood of `y` over which `f` is finite.

## Implementation notes

Generic points of irreducible components are the points of `genericPoints`. The parenthetical
formulation of the source is used for the residue-field hypotheses: for a morphism locally of
finite type, algebraicity of `κ(η)/κ(f η)` is equivalent to finiteness. The algebra structures
are the canonical ones induced by `AlgebraicGeometry.Scheme.Hom.residueFieldMap`, and
specialization of `f η` to `y` is `Specializes (f η) y`. The fourth alternative, that `f` is
quasi-finite at a dense set of points, is expressed by density of the set of points at which it
is quasi-finite. Restriction of a morphism over an open subscheme is Mathlib's `f ∣_ V`.

## References

* [Stacks Project, Tag 0AB6](https://stacks.math.columbia.edu/tag/0AB6)
* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

private lemma eq_of_specializes_genericPoint
    {T : Type*} [TopologicalSpace T] [T0Space T] [QuasiSober T]
    {x x' : T} (hx : x ∈ genericPoints T) (h : Specializes x' x) : x' = x :=
  (h.antisymm (specializes_iff_closure_subset.mpr
    ((genericPoints.component ⟨x, hx⟩).2.2 isIrreducible_singleton.closure
      (specializes_iff_closure_subset.mp h)))).eq

private lemma quasiFiniteAt_of_genericPoint_of_isAlgebraic
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (η : X)
    (hη : η ∈ genericPoints X)
    (hηalg : letI := (f.residueFieldMap η).hom.toAlgebra
      Algebra.IsAlgebraic (Y.residueField (f η)) (X.residueField η)) :
    quasiFiniteAt f η := by
  have hnoGeneralization :
      ¬ ∃ z : f.fiber (f η), z ≠ f.asFiber η ∧ z ⤳ f.asFiber η := by
    rintro ⟨z, hzne, hspec⟩
    have hspec' : Specializes (f.fiberι (f η) z) η := by
      simpa only [Scheme.Hom.fiberι_asFiber] using
        hspec.map (f.fiberι (f η)).continuous
    exact hzne ((f.fiberι (f η)).isEmbedding.injective (by
      rw [Scheme.Hom.fiberι_asFiber]
      exact eq_of_specializes_genericPoint hη hspec'))
  have hchar := (quasiFiniteAt_tfae f η).out 3 1
  exact hchar.mp ⟨isClosed_asFiber_of_isAlgebraic_residueField f η hηalg,
    hnoGeneralization⟩

/-- **A generic point of a Noetherian space lies in every dense open.** The irreducible
component of which it is the generic point has a nonempty open subset, which meets the dense
open, and the generic point specializes to any point of that subset. -/
@[ega "0 2.1.4" "special case"]
public lemma genericPoints_mem_dense_open {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] {D : Set Y} (hD : IsOpen D)
    (hd : Dense D) {y : Y} (hy : y ∈ genericPoints Y) : y ∈ D := by
  obtain ⟨V, hV, hVne, hVZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure {y}) hy
  obtain ⟨z, hzV, hzD⟩ := hd.inter_open_nonempty V hV hVne
  exact (specializes_iff_mem_closure.mpr (hVZ hzV)).mem_open hD hzD

/-- **A generic point of a locally Noetherian scheme lies in every dense open.** A locally
Noetherian scheme need not be a Noetherian space, so
`AlgebraicGeometry.genericPoints_mem_dense_open` is applied on an affine open containing the
point, which is Noetherian and in which the point is still a generic point. -/
public lemma scheme_genericPoints_mem_dense_open (Y : Scheme.{u})
    [IsLocallyNoetherian Y] {D : Set Y} (hD : IsOpen D)
    (hd : Dense D) {y : Y} (hy : y ∈ genericPoints Y) : y ∈ D := by
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  have : IsNoetherian V := { __ := isLocallyNoetherian_of_isOpenImmersion V.ι }
  let v : V := ⟨y, hyV⟩
  have hcomp : V.ι ⁻¹' closure ({y} : Set Y) ∈ irreducibleComponents V :=
    preimage_mem_irreducibleComponents hy V.ι.isOpenEmbedding
      ⟨y, subset_closure (Set.mem_singleton y), v, rfl⟩
  have hv : v ∈ genericPoints V := by
    show closure ({v} : Set V) ∈ irreducibleComponents V
    convert hcomp using 1
    rw [V.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      V.ι.continuous]
    congr 1
    ext z
    exact Subtype.ext_iff
  have hvD := genericPoints_mem_dense_open
    (hD.preimage V.ι.continuous) (hd.preimage V.ι.isOpenEmbedding.isOpenMap) hv
  change V.ι v ∈ D at hvD
  simpa [v] using hvD

private lemma quasiFiniteAt_of_genericPoint_of_isLocallyNoetherian_dense
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hY : IsLocallyNoetherian Y)
    (hD : Dense {x : X | quasiFiniteAt f x})
    (η : X) (hη : η ∈ genericPoints X) : quasiFiniteAt f η := by
  have : IsLocallyNoetherian Y := hY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact (mem_quasiFiniteLocus_iff f η).mp
    (scheme_genericPoints_mem_dense_open X (quasiFiniteLocus f).2
      (hD.mono fun x hx => (mem_quasiFiniteLocus_iff f x).mpr hx) hη)

/-- The scheme-theoretic fibre of a morphism locally of finite type is locally
Noetherian, being of finite type over a field. -/
@[sga "6 X 7.16" "partial"]
private lemma fiber_isLocallyNoetherian {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (s : Y) : IsLocallyNoetherian (f.fiber s) :=
  inferInstanceAs (IsLocallyNoetherian (pullback f (Y.fromSpecResidueField s)))

/-- Quasi-finiteness at `x` is zero-dimensionality of the fibre at `x`. -/
private lemma quasiFiniteAt_iff_topologicalKrullDimAt_fiber_eq_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    quasiFiniteAt f x ↔ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 0 := by
  have := fiber_isLocallyNoetherian f (f x)
  rw [topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint]
  exact (quasiFiniteAt_tfae f x).out 1 2

/-- **Stacks Project, Tag 0AB6.** A locally finite type morphism which is generically
quasi-finite is quasi-finite above a point with Noetherian local ring of dimension at most
one. It suffices to impose the generic condition only on components whose generic points
specialize to the chosen point, or alternatively to assume quasi-finiteness at every generic
point or on a dense set over a locally Noetherian target. -/
@[stacks 0AB6]
theorem quasiFiniteAt_of_target_stalk_dimension_le_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (hyNoetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hyDimension : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric :
      (∀ η : X, η ∈ genericPoints X →
        letI := (f.residueFieldMap η).hom.toAlgebra
        Algebra.IsAlgebraic (Y.residueField (f η)) (X.residueField η)) ∨
      (∀ η : X, η ∈ genericPoints X → Specializes (f η) y →
        letI := (f.residueFieldMap η).hom.toAlgebra
        Algebra.IsAlgebraic (Y.residueField (f η)) (X.residueField η)) ∨
      (∀ η : X, η ∈ genericPoints X → quasiFiniteAt f η) ∨
      (IsLocallyNoetherian Y ∧ Dense {x : X | quasiFiniteAt f x})) :
    ∀ x : X, f x = y → quasiFiniteAt f x := by
  intro x hx
  have hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 0 := by
    apply topologicalKrullDimAt_fiber_eq_zero_of_ringKrullDim_stalk_le_one f x
      (hx.symm ▸ hyNoetherian) (hx.symm ▸ hyDimension)
    intro η hη hηx
    have hqf : quasiFiniteAt f η := by
      rcases hgeneric with hA | hB | hC | hD
      · exact quasiFiniteAt_of_genericPoint_of_isAlgebraic f η hη (hA η hη)
      · exact quasiFiniteAt_of_genericPoint_of_isAlgebraic f η hη
          (hB η hη (by simpa [hx] using
            (specializes_iff_mem_closure.mpr hηx).map f.continuous))
      · exact hC η hη
      · exact quasiFiniteAt_of_genericPoint_of_isLocallyNoetherian_dense f hD.1 hD.2 η hη
    exact (quasiFiniteAt_iff_topologicalKrullDimAt_fiber_eq_zero f η).mp hqf
  exact (quasiFiniteAt_iff_topologicalKrullDimAt_fiber_eq_zero f x).mpr hdim


/-- **Stacks Project, Tag 0AB7.** A proper morphism which is generically quasi-finite is finite
over a neighbourhood of a point whose local ring is Noetherian of dimension at most one. -/
@[stacks 0AB7] theorem exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y)
    [IsNoetherianRing (Y.presheaf.stalk y)] (hy : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (h : (∀ (η : X), η ∈ genericPoints X → letI := (f.residueFieldMap η).hom.toAlgebra
        Algebra.IsAlgebraic (Y.residueField (f η)) (X.residueField η)) ∨
      ((∀ (η : X), η ∈ genericPoints X → Specializes (f η) y →
          letI := (f.residueFieldMap η).hom.toAlgebra
          Algebra.IsAlgebraic (Y.residueField (f η)) (X.residueField η)) ∨
        ((∀ (η : X), η ∈ genericPoints X → quasiFiniteAt f η) ∨
          (IsLocallyNoetherian Y ∧ Dense {x : X | quasiFiniteAt f x})))) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := by
  refine exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y
    ((f.isCompact_preimage_singleton y).finite ?_)
  rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
  rintro ⟨x, rfl⟩
  rw [← (f.fiberHomeo (f x)).symm.isOpen_image, Set.image_singleton]
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp
    (quasiFiniteAt_of_target_stalk_dimension_le_one f (f x) inferInstance hy h x rfl).2

end AlgebraicGeometry

end
