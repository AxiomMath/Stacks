module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing

/-!
# Coheight at a generic point of a fibre of a flat morphism

Let `f : X ⟶ S` be flat, with `X` and `S` locally Noetherian, and let `x : X` be a generic point
of an irreducible component of the fibre of `f` through `x`. Then `x` and its image have the same
coheight: the dimension formula for a flat local homomorphism expresses the dimension of
`𝒪_{X,x}` as the dimension of `𝒪_{S,f x}` plus the dimension of the local ring of the fibre at
`x`, and the last summand vanishes because a generic point of an irreducible component is maximal
for the specialization order.

Over a Dedekind base this computes the coheight outright: a point of `Spec A` other than the
generic one has coheight one, so a generic point of a fibre of `f` over such a point has coheight
one in `X`. This is the hypothesis of
`Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk`.

## Main results

* `Ideal.height_eq_one_of_isDedekindDomain`: a nonzero prime of a Dedekind domain has height one.
* `AlgebraicGeometry.coheight_eq_coheight_base_of_asFiber_mem_genericPoints`: the coheight of a
  generic point of a fibre of a flat morphism equals the coheight of its image.
* `AlgebraicGeometry.coheight_fiberι_eq_coheight_of_mem_genericPoints`: the same statement
  phrased for a point of the scheme-theoretic fibre over a given base point.
* `AlgebraicGeometry.coheight_fiberι_eq_one_of_isDedekindDomain`: over a Dedekind base, a generic
  point of the fibre over a nonzero prime has coheight one.

## References

* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [Stacks Project, Tag 02JS](https://stacks.math.columbia.edu/tag/02JS)
-/

@[expose] public section

open CategoryTheory Order

universe u

/-- A prime of a Dedekind domain other than the zero ideal has height one: it is not a minimal
prime, and the Krull dimension of a Dedekind domain is at most one. -/
theorem Ideal.height_eq_one_of_isDedekindDomain {A : Type u} [CommRing A] [IsDedekindDomain A]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) : p.height = 1 := by
  have hle : (p.height : WithBot ℕ∞) ≤ (1 : ℕ) :=
    (ringKrullDim_le_iff_height_le (R := A) (1 : ℕ)).mp
      (Ring.krullDimLE_iff.mp inferInstance) ‹p.IsPrime›
  have hne : p.height ≠ 0 := fun h => hp (Ideal.height_eq_zero_iff_eq_bot.mp h)
  exact le_antisymm (by exact_mod_cast hle) (Order.one_le_iff_ne_zero.mpr hne)

namespace AlgebraicGeometry

/-- A point of a scheme-theoretic fibre which is a generic point of an irreducible component of
that fibre is the canonical point of the fibre through its image in the ambient scheme. -/
private lemma asFiber_mem_genericPoints {X S : Scheme.{u}} (f : X ⟶ S) {s : S} {y : f.fiber s}
    (hy : y ∈ genericPoints ↥(f.fiber s)) {x : X} (hxy : f.fiberι s y = x)
    (hb : f.base x = s) : f.asFiber x ∈ genericPoints ↥(f.fiber (f.base x)) := by
  subst hb
  have : f.asFiber x = y :=
    (f.fiberι _).isEmbedding.injective (by rw [f.fiberι_asFiber, hxy])
  rwa [this]

/-- **The coheight of a generic point of a fibre of a flat morphism.** If `f : X ⟶ S` is flat
between locally Noetherian schemes and `x` is a generic point of an irreducible component of the
fibre of `f` through `x`, then `x` and `f x` have the same coheight. -/
theorem coheight_eq_coheight_base_of_asFiber_mem_genericPoints {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsLocallyNoetherian X] [IsLocallyNoetherian S] {x : X}
    (hx : f.asFiber x ∈ genericPoints ↥(f.fiber (f.base x))) :
    coheight x = coheight (f.base x) := by
  have hzero : ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) = 0 :=
    Stacks.Chow.ringKrullDim_stalk_eq_zero_of_mem_genericPoints ⟨f.asFiber x, hx⟩
  have key := ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat f x
  rw [hzero, add_zero, ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at key
  exact_mod_cast key

/-- **The coheight of a generic point of a fibre of a flat morphism**, phrased for a point of the
scheme-theoretic fibre over a given base point. -/
theorem coheight_fiberι_eq_coheight_of_mem_genericPoints {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] {s : S} {y : f.fiber s}
    (hy : y ∈ genericPoints ↥(f.fiber s)) : coheight (f.fiberι s y) = coheight s := by
  have hb : f.base (f.fiberι s y) = s := by
    have hmem : f.fiberι s y ∈ f.base ⁻¹' {s} := f.range_fiberι s ▸ Set.mem_range_self y
    simpa using hmem
  rw [coheight_eq_coheight_base_of_asFiber_mem_genericPoints f
    (asFiber_mem_genericPoints f hy rfl hb), hb]

/-- **A generic point of a fibre of a flat morphism locally of finite type over a Dedekind base
has coheight one.** The base point is required to be other than the generic point of `Spec A`,
which for a Dedekind domain is the same as requiring it to be a closed point. -/
theorem coheight_fiberι_eq_one_of_isDedekindDomain {A : Type u} [CommRing A] [IsDedekindDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f]
    {s : Spec (.of A)} (hs : s.asIdeal ≠ ⊥) {y : f.fiber s}
    (hy : y ∈ genericPoints ↥(f.fiber s)) : coheight (f.fiberι s y) = 1 := by
  have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsDedekindDomain ↥(CommRingCat.of A) := inferInstanceAs (IsDedekindDomain A)
  have : s.asIdeal.IsPrime := s.isPrime
  rw [coheight_fiberι_eq_coheight_of_mem_genericPoints f hy,
    ← idealHeight_eq_coheight (.of A) s]
  exact Ideal.height_eq_one_of_isDedekindDomain hs

end AlgebraicGeometry
