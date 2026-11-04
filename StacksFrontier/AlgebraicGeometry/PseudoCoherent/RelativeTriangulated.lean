module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeSummand
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Objects pseudo-coherent relative to a base form a saturated triangulated subcategory

Let `f : X ⟶ S` be a morphism of schemes locally of finite type. The objects of `D(𝒪_X)` that
are pseudo-coherent relative to `S` (Stacks 09UI) form a strictly full, saturated, triangulated
subcategory of `D(𝒪_X)`: the property is invariant under isomorphism, holds for a zero object,
is stable under all integer shifts, satisfies two out of three in a distinguished triangle, and
passes to direct summands.

The two-out-of-three rules are Stacks 09UL and the summand rule is Stacks 09UN, both proved; what
this file adds is the zero object, the behaviour under shifts, and the packaging of relative
pseudo-coherence as a property of the objects of `D(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentRelativeTo` is relative pseudo-coherence packaged
  as a property of the objects of `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_isZero` and
  `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherent.of_isZero`: a zero object is relatively
  pseudo-coherent.
* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.shift` and
  `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherent.shift`: shifting an object by `n` shifts the
  relative pseudo-coherence bound by `-n`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_of_biprod`,
  `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherent.of_biprod_left` and
  `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherent.of_biprod_right`: the degree-free form of
  Stacks 09UN.
* `AlgebraicGeometry.Scheme.Hom.isClosedUnderIsomorphisms_isPseudoCoherentRelativeTo`,
  `AlgebraicGeometry.Scheme.Hom.isTriangulated_isPseudoCoherentRelativeTo` and
  `AlgebraicGeometry.Scheme.Hom.isSaturated_isPseudoCoherentRelativeTo`: the three assertions
  whose conjunction says that the relatively pseudo-coherent objects form a strictly full
  saturated triangulated subcategory.

## Implementation notes

Strict fullness is `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`, the
triangulated-subcategory condition is `CategoryTheory.ObjectProperty.IsTriangulated` and
saturation is `CategoryTheory.ObjectProperty.IsSaturated` (Stacks 05RB).

Every statement here is reduced to the local condition of Stacks 09UI at a single closed
immersion `i : U ⟶ 𝔸ⁿ_V`, where it is sheaf-level pseudo-coherence of the derived pushforward
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff`). For the zero
object the covers are produced from nothing, by the remark preceding Stacks 09UI
(`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`); for a shift the covers
witnessing the hypothesis are reused unchanged, restriction along an open immersion and
pushforward along a closed immersion being exact, hence commuting with the shift.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.6 (09UL)](https://stacks.math.columbia.edu/tag/09UL)
* [The Stacks Project, Lemma 36.61.9 (09UN)](https://stacks.math.columbia.edu/tag/09UN)
* [The Stacks Project, Definition 13.6.1 (05RB)](https://stacks.math.columbia.edu/tag/05RB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

/-! ### The zero object -/

/-- A zero object of `D(𝒪_X)` is `m`-pseudo-coherent relative to `S`, for every `m`: at each
compatible pair of affine opens a closed immersion into an affine space exists, and the derived
pushforward of a zero object along it is zero. -/
public theorem isPseudoCoherentFrom_of_isZero {E : DerivedCategory X.Modules} (hE : IsZero E)
    (m : ℤ) : IsPseudoCoherentFrom f E m := by
  refine isPseudoCoherentFrom_of_forall_affinePair f E m fun U V hUV => ?_
  obtain ⟨n, i, hi, hio⟩ := exists_isClosedImmersion_affineSpace_resLE f V U hUV
  have := hi
  refine ⟨n, i, hi, hio, (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).2 ?_⟩
  refine (RingedSpace.isPseudoCoherent_iff_forall.{u, u + 1} _).1 ?_ m
  exact RingedSpace.isPseudoCoherent_of_isZero.{u, u + 1}
    ((Scheme.Modules.pushforward i).mapDerivedCategory.map_isZero
      ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.map_isZero hE))

/-- A zero object of `D(𝒪_X)` is pseudo-coherent relative to `S`. -/
public theorem IsPseudoCoherent.of_isZero {E : DerivedCategory X.Modules} (hE : IsZero E) :
    IsPseudoCoherent f E :=
  fun m => isPseudoCoherentFrom_of_isZero f hE m

/-! ### Shifts -/

/-- Shifting an object of `D(𝒪_X)` by `n` shifts its relative pseudo-coherence bound by `-n`:
restriction to an open subscheme and pushforward along a closed immersion are exact, hence
commute with the shift, and the sheaf-level statement is
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.shift`. -/
public theorem IsPseudoCoherentFrom.shift {E : DerivedCategory X.Modules} {m : ℤ}
    (h : IsPseudoCoherentFrom f E m) (n : ℤ) :
    IsPseudoCoherentFrom f (E⟦n⟧) (m - n) := by
  obtain ⟨ι, V, hV, hU⟩ := h
  refine ⟨ι, V, hV, fun j => ?_⟩
  obtain ⟨κ, U, hUcover, hUloc⟩ := hU j
  refine ⟨κ, U, hUcover, fun k => ?_⟩
  obtain ⟨hle, N, g, hg, hcomm, hpc⟩ := hUloc k
  have := hg
  refine ⟨hle, N, g, hg, hcomm, ?_⟩
  rw [Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff] at hpc ⊢
  refine RingedSpace.IsPseudoCoherentFrom.ofIso.{u, u + 1} (hpc.shift n) ?_
  exact ((((Scheme.Modules.pushforward g).mapDerivedCategory.commShiftIso n).app
      ((Scheme.Modules.restrictFunctor (U k).1.ι).mapDerivedCategory.obj E)).symm ≪≫
    (Scheme.Modules.pushforward g).mapDerivedCategory.mapIso
      ((((Scheme.Modules.restrictFunctor (U k).1.ι).mapDerivedCategory.commShiftIso
        n).app E).symm))

/-- A shift of an object pseudo-coherent relative to `S` is pseudo-coherent relative to `S`: the
degree shift is absorbed by quantifying over all bounds. -/
public theorem IsPseudoCoherent.shift {E : DerivedCategory X.Modules}
    (h : IsPseudoCoherent f E) (n : ℤ) : IsPseudoCoherent f (E⟦n⟧) := by
  intro m
  have hm := IsPseudoCoherentFrom.shift f (h (m + n)) n
  rwa [add_sub_cancel_right] at hm

/-! ### Direct summands and distinguished triangles -/

/-- **Stacks 09UN in all degrees.** If a binary biproduct in `D(𝒪_X)` is pseudo-coherent relative
to `S`, then so are both of its summands. -/
public theorem isPseudoCoherent_of_biprod (E K : DerivedCategory X.Modules)
    (h : IsPseudoCoherent f (E ⊞ K)) : IsPseudoCoherent f E ∧ IsPseudoCoherent f K :=
  ⟨fun m => (isPseudoCoherentFrom_of_biprod f E K m (h m)).1,
    fun m => (isPseudoCoherentFrom_of_biprod f E K m (h m)).2⟩

/-- **Stacks 09UN in all degrees, first summand.** -/
public theorem IsPseudoCoherent.of_biprod_left (E K : DerivedCategory X.Modules)
    (h : IsPseudoCoherent f (E ⊞ K)) : IsPseudoCoherent f E :=
  (isPseudoCoherent_of_biprod f E K h).1

/-- **Stacks 09UN in all degrees, second summand.** -/
public theorem IsPseudoCoherent.of_biprod_right (E K : DerivedCategory X.Modules)
    (h : IsPseudoCoherent f (E ⊞ K)) : IsPseudoCoherent f K :=
  (isPseudoCoherent_of_biprod f E K h).2

/-! ### The subcategory of relatively pseudo-coherent objects -/

/-- The objects of `D(𝒪_X)` that are pseudo-coherent relative to `S` (Stacks 09UI), viewed as a
property of the objects of `D(𝒪_X)`. The packaging is what lets the closure properties be stated
as conditions on a subcategory. -/
public def isPseudoCoherentRelativeTo : ObjectProperty (DerivedCategory X.Modules) :=
  fun E => IsPseudoCoherent f E

/-- An object of `D(𝒪_X)` lies in `isPseudoCoherentRelativeTo` exactly when it is pseudo-coherent
relative to `S`. -/
public theorem isPseudoCoherentRelativeTo_iff (E : DerivedCategory X.Modules) :
    isPseudoCoherentRelativeTo f E ↔ IsPseudoCoherent f E :=
  Iff.rfl

/-- The objects of `D(𝒪_X)` pseudo-coherent relative to `S` form a *strictly full* subcategory:
relative pseudo-coherence is invariant under isomorphism in `D(𝒪_X)`. -/
public theorem isClosedUnderIsomorphisms_isPseudoCoherentRelativeTo :
    (isPseudoCoherentRelativeTo f).IsClosedUnderIsomorphisms :=
  ⟨fun e h => h.of_iso f e⟩

/-- The objects of `D(𝒪_X)` pseudo-coherent relative to `S` form a *triangulated* subcategory:
the property contains the zero object, is stable under all shifts, and is closed under
extensions. -/
@[sga "6 III 1.4"]
public theorem isTriangulated_isPseudoCoherentRelativeTo :
    (isPseudoCoherentRelativeTo f).IsTriangulated := by
  let _ := isClosedUnderIsomorphisms_isPseudoCoherentRelativeTo f
  let _ : (isPseudoCoherentRelativeTo f).ContainsZero :=
    ⟨⟨0, isZero_zero _, IsPseudoCoherent.of_isZero f (isZero_zero _)⟩⟩
  let _ : (isPseudoCoherentRelativeTo f).IsStableUnderShift ℤ :=
    ⟨fun n => ⟨fun _ hE => IsPseudoCoherent.shift f hE n⟩⟩
  exact { ext₂' T hT h₁ h₃ :=
    ObjectProperty.le_isoClosure _ _ (isPseudoCoherent_obj₂_of_distinguished f T hT h₁ h₃) }

/-- The objects of `D(𝒪_X)` pseudo-coherent relative to `S` form a *saturated* (thick)
subcategory: a direct summand of a relatively pseudo-coherent object is relatively
pseudo-coherent. -/
public theorem isSaturated_isPseudoCoherentRelativeTo :
    (isPseudoCoherentRelativeTo f).IsSaturated := by
  let _ := isClosedUnderIsomorphisms_isPseudoCoherentRelativeTo f
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [ObjectProperty.isoClosure_eq_self] at h ⊢
  · exact IsPseudoCoherent.of_biprod_left f _ _ h
  · exact IsPseudoCoherent.of_biprod_right f _ _ h

end AlgebraicGeometry.Scheme.Hom

end
