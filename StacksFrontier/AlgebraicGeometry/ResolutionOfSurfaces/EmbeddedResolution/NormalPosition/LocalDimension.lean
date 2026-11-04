module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.AmbientCurveResolution
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierAfterPointBlowups
import all
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierAfterPointBlowups

/-!
# Integral effective Cartier divisors on a surface: local dimensions

Let `W` be a locally Noetherian scheme of dimension two and let `Y ⊆ W` be an integral closed
subscheme which is an effective Cartier divisor, with generic point `ξ`. The local ring of `W`
at `ξ` has dimension one (Krull's principal ideal theorem), so every other point of `Y` has a
two-dimensional local ring and is a closed point of `W`, and `Y` itself has dimension at most
one. Two distinct such divisors meet in a finite set of closed points.

## Main results

* `Stacks.ResolutionOfSurfaces.eq_of_genericPoint_mem_support`: an integral effective Cartier
  divisor containing the generic point of another one is equal to it.
* `Stacks.ResolutionOfSurfaces.ringKrullDim_stalk_eq_two_of_mem_support` and
  `Stacks.ResolutionOfSurfaces.isClosed_singleton_of_mem_support_of_ne`: a non-generic point of an
  integral effective Cartier divisor on a surface has a two-dimensional local ring and is
  closed.
* `Stacks.ResolutionOfSurfaces.topologicalKrullDim_subscheme_le_one` and
  `Stacks.ResolutionOfSurfaces.topologicalKrullDim_subscheme_eq_one`: such a divisor has
  dimension at most one, and exactly one when it has a second point.
* `Stacks.ResolutionOfSurfaces.finite_inter_support_of_ne`: two distinct such divisors on a
  Noetherian surface meet in finitely many closed points with two-dimensional local rings.

## Implementation notes

Points of a scheme carry the specialization preorder, in which `x ≤ y` means that `y`
specializes to `x`, so generic points are maximal. The dimension of the local ring at `x` is the
coheight of `x` (`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`), and the dimension of the
scheme is the Krull dimension of this preorder. All arguments below are comparisons of heights
and coheights along the chain `x < ξ`.

## References

* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

variable {W : Scheme.{u}}

/-! ### The generic point of an integral closed subscheme -/

/-- The dimension of a scheme is the Krull dimension of its specialization order. -/
private theorem topologicalKrullDim_eq_krullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X := by
  let _ : PartialOrder X := specializationOrder X
  exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

/-- A point lies on an integral closed subscheme exactly when the generic point of the subscheme
specializes to it. -/
private theorem mem_support_iff_specializes (Y : W.IdealSheafData) [IsIntegral Y.subscheme]
    (x : W) :
    x ∈ (Y.support : Set W) ↔ Y.subschemeι (genericPoint Y.subscheme) ⤳ x := by
  rw [← Y.range_subschemeι]
  constructor
  · rintro ⟨y, rfl⟩
    exact (genericPoint_specializes y).map Y.subschemeι.continuous
  · intro h
    exact h.mem_closed (Y.range_subschemeι ▸ Y.support.isClosed) ⟨_, rfl⟩

/-- A point that is a proper specialization of `ξ` lies strictly below `ξ`. -/
private theorem lt_of_specializes_of_ne {X : Scheme.{u}} {x ξ : X} (h : ξ ⤳ x) (hne : x ≠ ξ) :
    x < ξ :=
  lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h) fun hge =>
    hne (Specializes.antisymm h (Scheme.le_iff_specializes.mp hge)).eq.symm

/-- A point of an integral closed subscheme lies below its generic point. -/
private theorem le_genericPoint_of_mem_support (Y : W.IdealSheafData) [IsIntegral Y.subscheme]
    {x : W} (hx : x ∈ (Y.support : Set W)) :
    x ≤ Y.subschemeι (genericPoint Y.subscheme) :=
  Scheme.le_iff_specializes.mpr ((mem_support_iff_specializes Y x).mp hx)

/-- A point of an integral closed subscheme other than its generic point lies strictly below
it. -/
private theorem lt_genericPoint_of_mem_support_of_ne (Y : W.IdealSheafData)
    [IsIntegral Y.subscheme] {x : W} (hx : x ∈ (Y.support : Set W))
    (hne : x ≠ Y.subschemeι (genericPoint Y.subscheme)) :
    x < Y.subschemeι (genericPoint Y.subscheme) := by
  exact lt_of_specializes_of_ne ((mem_support_iff_specializes Y x).mp hx) hne

/-- The generic point of an integral effective Cartier divisor has a one-dimensional local
ring. -/
private theorem coheight_genericPoint [IsLocallyNoetherian W] (Y : W.IdealSheafData)
    [IsIntegral Y.subscheme] (hY : IsEffectiveCartierDivisor Y) :
    Order.coheight (Y.subschemeι (genericPoint Y.subscheme)) = 1 := by
  have h := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor Y hY
    (genericPoint Y.subscheme)
    ⟨⟨Set.univ, by simp [irreducibleComponents_eq_singleton]⟩, genericPoint_spec _⟩
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-! ### Local dimensions along an integral effective Cartier divisor -/

/-- The cast of `2 : ℕ∞` into `WithBot ℕ∞` is `2`. -/
private theorem coe_two : ((2 : ℕ∞) : WithBot ℕ∞) = 2 := rfl

/-- **An integral effective Cartier divisor containing the generic point of another is equal to
it.** Both generic points have one-dimensional local rings, so neither can strictly generalize
the other, and two reduced closed subschemes with the same support are equal. -/
public theorem eq_of_genericPoint_mem_support [IsLocallyNoetherian W] (Y Y' : W.IdealSheafData)
    [IsIntegral Y.subscheme] [IsIntegral Y'.subscheme] (hY : IsEffectiveCartierDivisor Y)
    (hY' : IsEffectiveCartierDivisor Y')
    (h : Y.subschemeι (genericPoint Y.subscheme) ∈ (Y'.support : Set W)) : Y = Y' := by
  have heq : Y.subschemeι (genericPoint Y.subscheme) =
      Y'.subschemeι (genericPoint Y'.subscheme) := by
    by_contra hne
    have hlt := lt_genericPoint_of_mem_support_of_ne Y' h hne
    have h2 := Order.coheight_add_one_le hlt
    rw [coheight_genericPoint Y hY, coheight_genericPoint Y' hY'] at h2
    norm_num at h2
  refine eq_of_support_eq Y Y' (SetLike.coe_injective (Set.ext fun x => ?_))
  rw [mem_support_iff_specializes, mem_support_iff_specializes, heq]

/-- **A non-generic point of an integral effective Cartier divisor on a surface has a
two-dimensional local ring.** It lies strictly below the generic point, whose local ring is
one-dimensional, and no local ring of `W` has dimension above two. -/
public theorem ringKrullDim_stalk_eq_two_of_mem_support [IsLocallyNoetherian W]
    (hdim : topologicalKrullDim W = 2) (Y : W.IdealSheafData) [IsIntegral Y.subscheme]
    (hY : IsEffectiveCartierDivisor Y) {x : W} (hx : x ∈ (Y.support : Set W))
    (hne : x ≠ Y.subschemeι (genericPoint Y.subscheme)) :
    ringKrullDim (W.presheaf.stalk x) = 2 := by
  refine le_antisymm (ringKrullDim_stalk_le hdim x) ?_
  have h2 := Order.coheight_add_one_le (lt_genericPoint_of_mem_support_of_ne Y hx hne)
  rw [coheight_genericPoint Y hY, one_add_one_eq_two] at h2
  rw [ringKrullDim_stalk_eq_coheight, ← coe_two]
  exact WithBot.coe_le_coe.mpr h2

/-- **A non-generic point of an integral effective Cartier divisor on a surface is a closed
point.** Its local ring is two-dimensional, so it has no proper specialization. -/
public theorem isClosed_singleton_of_mem_support_of_ne [IsLocallyNoetherian W]
    (hdim : topologicalKrullDim W = 2) (Y : W.IdealSheafData) [IsIntegral Y.subscheme]
    (hY : IsEffectiveCartierDivisor Y) {x : W} (hx : x ∈ (Y.support : Set W))
    (hne : x ≠ Y.subschemeι (genericPoint Y.subscheme)) :
    IsClosed ({x} : Set W) := by
  have h2 := ringKrullDim_stalk_eq_two_of_mem_support hdim Y hY hx hne
  rw [ringKrullDim_stalk_eq_coheight] at h2
  refine isClosed_singleton_of_codimension_two hdim x ?_
  rw [coheight_eq_codimension x]
  exact WithBot.coe_le_coe.mp (by rw [coe_two]; exact h2.ge)

/-- **An integral effective Cartier divisor on a surface has dimension at most one.** Every
point of it lies below its generic point, whose height in `W` is at most one because its
coheight is one and `W` has dimension two. -/
public theorem topologicalKrullDim_subscheme_le_one [IsLocallyNoetherian W]
    (hdim : topologicalKrullDim W = 2) (Y : W.IdealSheafData) [IsIntegral Y.subscheme]
    (hY : IsEffectiveCartierDivisor Y) :
    topologicalKrullDim Y.subscheme ≤ 1 := by
  set ξ := Y.subschemeι (genericPoint Y.subscheme)
  have : Nonempty W := ⟨ξ⟩
  have hξdim : Order.height ξ ≤ 1 := by
    have hsum : Order.height ξ + Order.coheight ξ ≤ 2 := by
      have h := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := W)
      rw [← topologicalKrullDim_eq_krullDim, hdim] at h
      have h' : ((Order.height ξ + Order.coheight ξ : ℕ∞) : WithBot ℕ∞) ≤ 2 := by
        rw [h]
        exact WithBot.coe_le_coe.mpr
          (le_iSup (fun a : W => Order.height a + Order.coheight a) ξ)
      rw [← coe_two] at h'
      exact WithBot.coe_le_coe.mp h'
    rw [coheight_genericPoint Y hY] at hsum
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp
      (by simpa [one_add_one_eq_two] using hsum)
  have hmono : StrictMono Y.subschemeι.base := by
    intro a c hac
    refine lt_of_le_not_ge ?_ fun hca => hac.not_ge (Scheme.le_iff_specializes.mpr ?_)
    · exact Scheme.le_iff_specializes.mpr
        ((Scheme.le_iff_specializes.mp hac.le).map Y.subschemeι.continuous)
    · exact Y.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
        (Scheme.le_iff_specializes.mp hca)
  rw [topologicalKrullDim_eq_krullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun y => ?_
  have h1 : Order.height y ≤ Order.height ξ :=
    (Order.height_le_height_apply_of_strictMono _ hmono y).trans
      (Order.height_mono (le_genericPoint_of_mem_support Y
        (by rw [← Y.range_subschemeι]; exact ⟨y, rfl⟩)))
  exact_mod_cast h1.trans hξdim

/-- **An integral effective Cartier divisor on a surface with a non-generic point has dimension
exactly one.** -/
public theorem topologicalKrullDim_subscheme_eq_one [IsLocallyNoetherian W]
    (hdim : topologicalKrullDim W = 2) (Y : W.IdealSheafData) [IsIntegral Y.subscheme]
    (hY : IsEffectiveCartierDivisor Y) {x : W} (hx : x ∈ (Y.support : Set W))
    (hne : x ≠ Y.subschemeι (genericPoint Y.subscheme)) :
    topologicalKrullDim Y.subscheme = 1 := by
  refine le_antisymm (topologicalKrullDim_subscheme_le_one hdim Y hY) ?_
  rw [← Y.range_subschemeι] at hx
  obtain ⟨y, rfl⟩ := hx
  have hlt : y < genericPoint Y.subscheme :=
    lt_of_specializes_of_ne (genericPoint_specializes y) fun h => hne (congrArg _ h)
  have h1 : (1 : ℕ∞) ≤ Order.coheight y :=
    le_add_self.trans (Order.coheight_add_one_le hlt)
  rw [topologicalKrullDim_eq_krullDim]
  exact le_trans (by exact_mod_cast h1) (Order.coheight_le_krullDim y)

/-- **Two distinct integral effective Cartier divisors on a Noetherian surface meet in finitely
many closed points, each with a two-dimensional local ring.** A common point cannot be the
generic point of either divisor, by `Stacks.ResolutionOfSurfaces.eq_of_genericPoint_mem_support`,
so it is a closed point with a two-dimensional local ring; a closed set of closed points of a
Noetherian scheme is finite. -/
public theorem finite_inter_support_of_ne [IsNoetherian W] (hdim : topologicalKrullDim W = 2)
    (Y Y' : W.IdealSheafData) [IsIntegral Y.subscheme] [IsIntegral Y'.subscheme]
    (hY : IsEffectiveCartierDivisor Y) (hY' : IsEffectiveCartierDivisor Y') (hne : Y ≠ Y') :
    ((Y.support : Set W) ∩ Y'.support).Finite ∧
      ∀ x ∈ (Y.support : Set W) ∩ Y'.support,
        IsClosed ({x} : Set W) ∧ ringKrullDim (W.presheaf.stalk x) = 2 := by
  have key : ∀ x ∈ (Y.support : Set W) ∩ Y'.support,
      IsClosed ({x} : Set W) ∧ ringKrullDim (W.presheaf.stalk x) = 2 := by
    rintro x ⟨hx, hx'⟩
    have hxne : x ≠ Y.subschemeι (genericPoint Y.subscheme) := by
      rintro rfl
      exact hne (eq_of_genericPoint_mem_support Y Y' hY hY' hx')
    exact ⟨isClosed_singleton_of_mem_support_of_ne hdim Y hY hx hxne,
      ringKrullDim_stalk_eq_two_of_mem_support hdim Y hY hx hxne⟩
  exact ⟨finite_of_forall_isClosed_singleton (Y.support.isClosed.inter Y'.support.isClosed)
    fun x hx => (key x hx).1, key⟩

end Stacks.ResolutionOfSurfaces

end
