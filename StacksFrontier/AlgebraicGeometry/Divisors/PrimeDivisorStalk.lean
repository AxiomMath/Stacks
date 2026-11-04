module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.OrderOfVanishingInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Prime divisors by the dimension of the local ring, and finiteness of Weil divisors

A prime divisor of a scheme is an integral closed subscheme of codimension one.  Equivalently,
by Stacks 02IZ, it is an integral closed subscheme whose generic point `ξ` has a local ring
`𝒪_{X, ξ}` of dimension one; that is the form the definition takes in the Exercises chapter.
This file proves the two conditions equivalent for an arbitrary scheme, so that
`AlgebraicGeometry.PrimeDivisor` is the type both formulations define.

For a Noetherian scheme the underlying space is quasi-compact, so a locally finite family of
supports has only finitely many nonempty members.  A Weil divisor on a Noetherian scheme is
therefore a *finite* formal linear combination of prime divisors with integer coefficients,
which is the form the definition takes in the Exercises chapter.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_eq_one_iff_codimension_closureSingleton_eq_one`: the
  dimension of the local ring at a point is one exactly when the closure of that point has
  codimension one.
* `AlgebraicGeometry.PrimeDivisor.ringKrullDim_stalk_genericPoint_eq_one`: the local ring at
  the generic point of a prime divisor has dimension one.
* `AlgebraicGeometry.PrimeDivisor.support_nonempty`: a prime divisor has nonempty support.
* `LocallyFinite.finite_setOf_nonempty`: on a compact space only finitely many members of a
  locally finite family are nonempty.
* `AlgebraicGeometry.mem_weilDivisor_iff_finite_support`: on a Noetherian scheme a coefficient
  family is a Weil divisor exactly when its support is finite.
* `AlgebraicGeometry.weilDivisorEquivFinsupp`: on a Noetherian scheme the Weil divisors are the
  finitely supported integer coefficient families, that is the finite formal linear
  combinations of prime divisors.

## Implementation notes

The equivalence of the two codimension conditions is assembled from two library facts rather
than reproved: Mathlib's `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, which is Stacks
02IZ, identifies the dimension of the local ring with the coheight of the point in the
specialization order, and `AlgebraicGeometry.coheight_eq_codimension_closureSingleton`
identifies that coheight with the codimension of the closure of the point.  The first is valued
in `WithBot ℕ∞` and the second in `ℕ∞`, so the two readings of `= 1` are compared by a cast.

Nothing here introduces a second prime divisor or Weil divisor notion: both statements are
about the library's `AlgebraicGeometry.PrimeDivisor` and `AlgebraicGeometry.WeilDivisor`.

The effective Cartier divisors of the Exercises chapter are likewise the library's.  There a
closed subscheme `D ⊆ S` is called an effective Cartier divisor when every point of `D` has an
affine open neighbourhood `Spec A = U` with `D ∩ U = Spec (A / (f))` for a nonzerodivisor
`f ∈ A`; the library takes as the definition that the ideal sheaf of `D` is invertible, and
`Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal`, which is Stacks 01WS, proves the
two equivalent.  So the notion is registered on `Stacks.Divisors.IsEffectiveCartierDivisor`
rather than restated.

## References

* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public noncomputable section

open TopologicalSpace

universe u

/-- On a compact space only finitely many members of a locally finite family are nonempty. -/
theorem LocallyFinite.finite_setOf_nonempty {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : ι → Set X} (hf : LocallyFinite f) : {i | (f i).Nonempty}.Finite := by
  choose U hU hfin using hf
  obtain ⟨t, -, hcover⟩ := isCompact_univ.elim_nhds_subcover U fun x _ => hU x
  refine (t.finite_toSet.biUnion fun x _ => hfin x).subset fun i ⟨y, hy⟩ => ?_
  obtain ⟨x, hxt, hxU⟩ := by simpa using hcover (Set.mem_univ y)
  exact Set.mem_biUnion hxt ⟨y, hy, hxU⟩

namespace AlgebraicGeometry

/-- **Stacks 02IZ, read at a point.** The local ring of a scheme at a point has dimension one
exactly when the closure of that point has codimension one.  The left-hand side is the
condition imposed on the generic point of a prime divisor in Tag 02AR, the right-hand side the
condition imposed in Tag 0BE2. -/
@[ega "IV 21.6.2" "p = 1", ega "IV 5.1.2" "codimension one", sga "1 II 5.9" "special case"]
theorem ringKrullDim_stalk_eq_one_iff_codimension_closureSingleton_eq_one
    {X : Scheme.{u}} (ξ : X) :
    ringKrullDim (X.presheaf.stalk ξ) = 1 ↔
      codimension (IrreducibleCloseds.closureSingleton ξ) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_codimension_closureSingleton]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- The local ring of the ambient scheme at the generic point of a prime divisor has dimension
one.  This is the defining condition of a prime divisor as Tag 02AR states it, read on the
prime divisors of Tag 0BE2. -/
theorem PrimeDivisor.ringKrullDim_stalk_genericPoint_eq_one {X : Scheme.{u}}
    (Z : PrimeDivisor X) : ringKrullDim (X.presheaf.stalk Z.genericPoint) = 1 :=
  (ringKrullDim_stalk_eq_one_iff_codimension_closureSingleton_eq_one _).mpr
    Z.codimension_closureSingleton_genericPoint

/-- The support of a prime divisor is nonempty: it is the image of the underlying closed
subscheme, which is integral and hence nonempty. -/
theorem PrimeDivisor.support_nonempty {X : Scheme.{u}} (Z : PrimeDivisor X) :
    (Z.support : Set X).Nonempty := by
  have := Z.integral
  have h := Scheme.IdealSheafData.range_subschemeι Z.idealSheaf
  show ((Z.idealSheaf.support : Closeds X) : Set X).Nonempty
  exact h ▸ Set.range_nonempty _

/-- **Stacks 02AR part (1), on a Noetherian scheme.** An integer coefficient family indexed by
the prime divisors is a Weil divisor exactly when it has finite support, that is exactly when
it is a finite formal linear combination of prime divisors.  The underlying space of a
Noetherian scheme is quasi-compact, so local finiteness of the supports is finiteness. -/
theorem mem_weilDivisor_iff_finite_support {X : Scheme.{u}} [IsNoetherian X]
    (D : PrimeDivisor X → ℤ) :
    D ∈ WeilDivisor X ↔ (Function.support D).Finite := by
  rw [mem_weilDivisor_iff]
  refine ⟨fun h => h.finite_setOf_nonempty.subset fun Z hZ => ?_,
    fun h x => ⟨Set.univ, Filter.univ_mem, h.subset fun Z hZ => ?_⟩⟩
  · simp only [Function.mem_support] at hZ
    simp only [Set.mem_ofPred_eq, ite_eq_right hZ]
    exact Z.support_nonempty
  · simp only [Set.mem_ofPred_eq] at hZ
    simp only [Function.mem_support]
    intro he
    simp [he] at hZ

/-- **Stacks 02AR part (1), as a formal linear combination.** On a Noetherian scheme the Weil
divisors are exactly the finitely supported integer coefficient families indexed by the prime
divisors, that is the formal linear combinations `Σ nᵢ [Zᵢ]` with integer coefficients. -/
def weilDivisorEquivFinsupp {X : Scheme.{u}} [IsNoetherian X] :
    WeilDivisor X ≃+ (PrimeDivisor X →₀ ℤ) where
  toFun D := ⟨((mem_weilDivisor_iff_finite_support D.1).mp D.2).toFinset, D.1, fun Z => by simp⟩
  invFun D := ⟨D, (mem_weilDivisor_iff_finite_support (D : PrimeDivisor X → ℤ)).mpr
    D.hasFiniteSupport⟩
  left_inv D := by ext Z; rfl
  right_inv D := by ext Z; rfl
  map_add' D E := by ext Z; rfl

add_to_stacks 02AR "prime_divisor" AlgebraicGeometry.PrimeDivisor

add_to_stacks 02AR "weil_divisor" AlgebraicGeometry.WeilDivisor

add_to_stacks 02AR "effective_cartier_divisor" Stacks.Divisors.IsEffectiveCartierDivisor

end AlgebraicGeometry

end
