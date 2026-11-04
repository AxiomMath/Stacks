module

public import StacksFrontier.AlgebraicGeometry.LimitFibreDimensionBound.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Specialization
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The dimension hypothesis of `AttainedAtSomeStage` is needed

`Stacks.AlgebraicGeometry.LimitFibreDimensionBound.AttainedAtSomeStage` says that a point `z` of
the limit at which the local fibre dimension is at most `d` already has local fibre dimension at
most `d` at some stage. Without the condition on `z` the statement

    ∀ z : ↥cX.pt, ∃ i : I, cX.π.app i z ∈ boundedFibreDimension X S f d i

is false. The witness is the one-object system whose only component morphism is the structure
morphism of the affine line `𝔸¹_ℚ = Spec ℚ[X] ⟶ Spec ℚ`, with `d = 0`: every fibre of that
morphism is the whole affine line, of dimension `1`, so no point of the limit has local fibre
dimension `≤ 0` at any stage.

## Main results

* `topologicalKrullDimAt_fiber_eq_of_subsingleton`: when the target of `f` is a one-point space,
  the local dimension of the fibre of `f` through `x` is the local dimension of the source at
  `x` — the fibre is then all of the source.
* `not_topologicalKrullDimAt_le_zero`: `𝔸¹_ℚ` has local dimension `> 0` at every point, because
  the local ring at each closed point is the localization of a principal ideal domain at a
  nonzero prime, whose height is nonzero.
* `not_attained_of_forall_exists`: the statement above without the condition on `z` is
  **false** for this witness at `d = 0`.
* `attained_witness`: `AttainedAtSomeStage` itself holds for the same witness, vacuously.

## Implementation notes

The witness satisfies every hypothesis of Tag 05M5 — the transitions of the base are
identities, hence affine; `Spec ℚ` is quasi-compact and quasi-separated; the component
morphism is of finite type; and the comparison into the base change is an isomorphism, hence a
closed immersion — and `sysCone` is a limit cone. It does not satisfy the dimension hypothesis
`hdim` of the tag, since its fibres have dimension `1`, not `0`.

`Spec ℚ` has one point, so the fibre of the structure morphism through any point is the whole
affine line; the local dimension of `Spec ℚ[X]` at a point is the least of the Krull dimensions
of the local rings at its closed specializations (Stacks 0A21,
`AlgebraicGeometry.topologicalKrullDimAt_eq_iInf_closedSpecializations`); and each of those is
the height of a maximal ideal of `ℚ[X]`, nonzero because `ℚ[X]` is a domain in which `⊥` is not
maximal.

## References

* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Refute05M5Heart

open Stacks.AlgebraicGeometry.LimitFibreDimensionBound

/-! ### The fibre over a one-point base is the whole source -/

/-- If the target of `f` has at most one point, the fibre of `f` through `x` is all of `X`, so
the local dimension of the fibre at `x` is the local dimension of `X` at `x`. -/
public theorem topologicalKrullDimAt_fiber_eq_of_subsingleton {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Subsingleton ↥Y] (x : ↥X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = topologicalKrullDimAt ↥X x := by
  have hset : f ⁻¹' {f x} = (Set.univ : Set ↥X) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  calc topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)
      = topologicalKrullDimAt ↥(f ⁻¹' {f x}) ⟨x, rfl⟩ := by
        refine (topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo (f x))
          (f.asFiber x)).trans ?_
        congr 1
        exact Subtype.ext (f.fiberι_asFiber x)
    _ = topologicalKrullDimAt ↥(Set.univ : Set ↥X) ⟨x, trivial⟩ := by
        refine (topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hset)
          ⟨x, rfl⟩).trans ?_
        congr 1
    _ = topologicalKrullDimAt ↥X x :=
        topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.Set.univ ↥X) ⟨x, trivial⟩

/-! ### The affine line over `ℚ` and its closed point `(X)` -/

/-- The affine line `𝔸¹_ℚ = Spec ℚ[X]`, the source of the witness system. -/
public noncomputable def affineLine : Scheme.{0} := Spec (CommRingCat.of (Polynomial ℚ))

/-- The structure morphism `𝔸¹_ℚ ⟶ Spec ℚ`. -/
public noncomputable def lineProj : affineLine ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ)))

/-- `Spec ℚ` has a single point. -/
public instance subsingleton_specRat : Subsingleton ↥(Spec (CommRingCat.of ℚ)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum ℚ))

/-- `ℚ[X]` is a finitely generated `ℚ`-algebra, so `𝔸¹_ℚ ⟶ Spec ℚ` is of finite type. -/
public instance locallyOfFiniteType_lineProj : LocallyOfFiniteType lineProj := by
  let : Algebra.FiniteType ℚ ℚ := Module.Finite.finiteType ℚ
  have h : RingHom.FiniteType (algebraMap ℚ (Polynomial ℚ)) :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa using h

/-- The ideal `(X)` of `ℚ[X]` is prime. -/
public instance isPrime_spanX : (Ideal.span {(Polynomial.X : Polynomial ℚ)}).IsPrime := by
  rw [Ideal.span_singleton_prime Polynomial.X_ne_zero]
  exact Polynomial.prime_X

/-- The ideal `(X)` of `ℚ[X]` is nonzero. -/
public theorem spanX_ne_bot : (Ideal.span {(Polynomial.X : Polynomial ℚ)}) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact Polynomial.X_ne_zero

/-- The ideal `(X)` of `ℚ[X]` is maximal: a nonzero prime of a principal ideal domain. -/
public theorem isMaximal_spanX : (Ideal.span {(Polynomial.X : Polynomial ℚ)}).IsMaximal :=
  IsPrime.to_maximal_ideal spanX_ne_bot

/-- The closed point `(X)` of the affine line. -/
public noncomputable def closedPt : ↥affineLine :=
  (⟨Ideal.span {(Polynomial.X : Polynomial ℚ)}, isPrime_spanX⟩ : PrimeSpectrum (Polynomial ℚ))

/-- The closed point `(X)` is closed. -/
public theorem isClosed_closedPt : IsClosed ({closedPt} : Set ↥affineLine) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal
    (show PrimeSpectrum (Polynomial ℚ) from closedPt)).mpr isMaximal_spanX

/-- `⊥` is not a maximal ideal of `ℚ[X]`: it would then equal the maximal ideal `(X)`, which is
nonzero. So every maximal ideal of `ℚ[X]` is nonzero, hence of nonzero height. -/
public theorem bot_not_isMaximal : ¬ (⊥ : Ideal (Polynomial ℚ)).IsMaximal := fun h ↦
  spanX_ne_bot (h.eq_of_le isMaximal_spanX.ne_top bot_le).symm

/-- At a closed point of `𝔸¹_ℚ` the local ring has Krull dimension at least one: the stalk is
the localization of `ℚ[X]` at a maximal ideal, so its dimension is that ideal's height, which
is nonzero because the ideal is nonzero and `ℚ[X]` is a domain. -/
public theorem one_le_ringKrullDim_stalk (x : ↥affineLine)
    (hx : IsClosed ({x} : Set ↥affineLine)) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (affineLine.presheaf.stalk x) := by
  have hmax : (show PrimeSpectrum (Polynomial ℚ) from x).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal
      (show PrimeSpectrum (Polynomial ℚ) from x)).mp hx
  let : Algebra (Polynomial ℚ) (affineLine.presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra (Polynomial ℚ) x
  let : IsLocalization.AtPrime (affineLine.presheaf.stalk x)
      (show PrimeSpectrum (Polynomial ℚ) from x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (Polynomial ℚ)) x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (show PrimeSpectrum (Polynomial ℚ) from x).asIdeal (affineLine.presheaf.stalk x),
    ← WithBot.coe_one, WithBot.coe_le_coe]
  have hne : (show PrimeSpectrum (Polynomial ℚ) from x).asIdeal.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact fun hbot ↦ bot_not_isMaximal (hbot ▸ hmax)
  exact Order.one_le_iff_ne_zero.mpr hne

/-- **`𝔸¹_ℚ` has local dimension `> 0` at every point.** By Stacks 0A21 the local dimension of
a scheme locally of finite type over a field is the least of the dimensions of the local rings
at the closed specializations of the point, and each of those is at least one. -/
public theorem not_topologicalKrullDimAt_le_zero (z : ↥affineLine) :
    ¬ topologicalKrullDimAt ↥affineLine z ≤ (0 : WithBot ℕ∞) := by
  have hone : (1 : WithBot ℕ∞) ≤
      ⨅ x' : {x' : ↥affineLine // z ⤳ x' ∧ IsClosed ({x'} : Set ↥affineLine)},
        ringKrullDim (affineLine.presheaf.stalk x'.1) :=
    le_iInf fun x' ↦ one_le_ringKrullDim_stalk x'.1 x'.2.2
  rw [topologicalKrullDimAt_eq_iInf_closedSpecializations lineProj z]
  intro hle
  exact absurd (hone.trans hle) (by simp)

/-- The local dimension of `𝔸¹_ℚ` at the closed point `(X)` is **not** `≤ 0`. -/
public theorem not_topologicalKrullDimAt_closedPt_le_zero :
    ¬ topologicalKrullDimAt ↥affineLine closedPt ≤ (0 : WithBot ℕ∞) :=
  not_topologicalKrullDimAt_le_zero closedPt

/-! ### The witness system -/

/-- The index category: one object, one morphism. -/
public abbrev Ix : Type := Discrete PUnit.{1}

/-- The constant system of sources, `𝔸¹_ℚ` at the single stage. -/
public noncomputable def sysX : Ix ⥤ Scheme.{0} := (Functor.const Ix).obj affineLine

/-- The constant system of bases, `Spec ℚ` at the single stage. -/
public noncomputable def sysS : Ix ⥤ Scheme.{0} := (Functor.const Ix).obj (Spec (CommRingCat.of ℚ))

/-- The constant morphism of systems, `lineProj` at the single stage. -/
public noncomputable def sysF : sysX ⟶ sysS := (Functor.const Ix).map lineProj

/-- The limit cone of the constant system: its point is `𝔸¹_ℚ` and its projection is the
identity. -/
public noncomputable def sysCone : Cone sysX where
  pt := affineLine
  π := 𝟙 _

/-- Every component of the witness morphism of systems is `lineProj`, of finite type. -/
public instance locallyOfFiniteType_sysF_app (i : Ix) : LocallyOfFiniteType (sysF.app i) :=
  inferInstanceAs (LocallyOfFiniteType lineProj)

/-- The projection of the witness cone is the identity on points. -/
public theorem sysCone_π_app (i : Ix) (z : ↥sysCone.pt) : sysCone.π.app i z = z := rfl

/-! ### The refutation -/

/-- No point of `𝔸¹_ℚ` has local fibre dimension `≤ 0` for `lineProj`. -/
private theorem not_topologicalKrullDimAt_fiber_lineProj_le_zero (z : ↥affineLine) :
    ¬ topologicalKrullDimAt (lineProj.fiber (lineProj z)) (lineProj.asFiber z) ≤
      ((0 : ℕ) : WithBot ℕ∞) := by
  rw [Nat.cast_zero, topologicalKrullDimAt_fiber_eq_of_subsingleton lineProj z]
  exact not_topologicalKrullDimAt_le_zero z

/-- **`AttainedAtSomeStage` without the dimension hypothesis on `z` is false.** At `d = 0` for
the witness system it would say that every point of the affine line has local fibre dimension
`≤ 0` at some stage; the closed point `(X)` has local fibre dimension `1`, and there is only one
stage. -/
public theorem not_attained_of_forall_exists :
    ¬ ∀ z : ↥sysCone.pt, ∃ i : Ix,
      sysCone.π.app i z ∈ boundedFibreDimension sysX sysS sysF 0 i := by
  intro h
  obtain ⟨i, hi⟩ := h closedPt
  rw [mem_boundedFibreDimension_iff] at hi
  exact not_topologicalKrullDimAt_fiber_lineProj_le_zero closedPt hi

/-! ### `AttainedAtSomeStage` for the witness -/

/-- **`AttainedAtSomeStage` holds for the witness.** `lineProj` is the morphism between the
limits of the witness system, and no point of the limit has local fibre dimension `≤ 0`, so the
implication is vacuously true. -/
public theorem attained_witness : AttainedAtSomeStage sysX sysS sysF sysCone lineProj 0 :=
  fun z hz ↦ (not_topologicalKrullDimAt_fiber_lineProj_le_zero z hz).elim

end Stacks.AlgebraicGeometry.Refute05M5Heart

end
