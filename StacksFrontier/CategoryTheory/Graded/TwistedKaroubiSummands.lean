module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubi
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Direct sums of twisted idempotents through a common ambient object

Let `C` be a category graded over a ring `R`. Two twisted idempotents `M = (X, p, m)` and
`N = (Y, q, m)` with the same twist have a direct sum as soon as `X` and `Y` are direct summands of
a common object `W` of `C` in degree zero: given `iₓ : X ⟶ W`, `πₓ : W ⟶ X`, `i_y : Y ⟶ W`,
`π_y : W ⟶ Y` of degree zero with `iₓ ≫ πₓ = 1`, `iₓ ≫ π_y = 0`, `i_y ≫ πₓ = 0`, `i_y ≫ π_y = 1`,
the triple `(W, πₓ p iₓ + π_y q i_y, m)` is a direct sum of `M` and `N`, with projections `πₓ p`,
`π_y q` and inclusions `p iₓ`, `q i_y`. A twisted idempotent whose idempotent is zero is a zero
object.

For the category of Chow motives this is the case of equal twists of Stacks 0FGF, `W` being the
disjoint union of the two schemes.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.SummandData.summandsObj`: the triple
  `(W, πₓ p iₓ + π_y q i_y, m)`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.SummandData.biproductDataOfSummands`: it is a
  direct sum of `M` and `N`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.isZero_of_p_eq_zero`: a twisted idempotent with
  zero idempotent is a zero object.
-/

@[expose] public section

namespace CategoryTheory.GradedCategory.TwistedKaroubi

open CategoryTheory.Limits

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]

/-- A twisted idempotent whose idempotent is zero is a zero object: every morphism into or out
of it is fixed by the zero idempotent. -/
theorem isZero_of_p_eq_zero (M : TwistedKaroubi R C) (hM : M.p = 0) : IsZero M := by
  refine ⟨fun N ↦ ⟨⟨⟨0⟩, fun f ↦ hom_ext ?_⟩⟩, fun N ↦ ⟨⟨⟨0⟩, fun f ↦ hom_ext ?_⟩⟩⟩
  · rw [← (val_mem f).2.1, hM, Limits.zero_comp]
    exact (zero_val M N).symm
  · rw [← (val_mem f).2.2, hM, Limits.comp_zero]
    exact (zero_val N M).symm

/-- The data of a direct sum decomposition of an object `W` of `C` into two objects `X` and `Y`,
in degree zero. -/
structure SummandData (X Y W : C) where
  /-- The inclusion of `X`. -/
  ιX : X ⟶ W
  /-- The projection onto `X`. -/
  πX : W ⟶ X
  /-- The inclusion of `Y`. -/
  ιY : Y ⟶ W
  /-- The projection onto `Y`. -/
  πY : W ⟶ Y
  ιX_mem : ιX ∈ grade (R := R) X W 0
  πX_mem : πX ∈ grade (R := R) W X 0
  ιY_mem : ιY ∈ grade (R := R) Y W 0
  πY_mem : πY ∈ grade (R := R) W Y 0
  ιX_πX : ιX ≫ πX = 𝟙 X
  ιX_πY : ιX ≫ πY = 0
  ιY_πX : ιY ≫ πX = 0
  ιY_πY : ιY ≫ πY = 𝟙 Y

namespace SummandData

attribute [reassoc] ιX_πX ιX_πY ιY_πX ιY_πY

section Proj

variable {X Y W : C} (d : SummandData (R := R) X Y W)

/-- The idempotent `πₓ p iₓ + π_y q i_y` of `W` cutting out the direct sum of `(X, p)` and
`(Y, q)`. -/
def proj (p : X ⟶ X) (q : Y ⟶ Y) : W ⟶ W :=
  d.πX ≫ p ≫ d.ιX + d.πY ≫ q ≫ d.ιY

/-- `(πₓ p iₓ + π_y q i_y) πₓ = πₓ p`. -/
theorem proj_πX (p : X ⟶ X) (q : Y ⟶ Y) : d.proj p q ≫ d.πX = d.πX ≫ p := by
  simp [proj, d.ιX_πX, d.ιY_πX]

/-- `(πₓ p iₓ + π_y q i_y) π_y = π_y q`. -/
theorem proj_πY (p : X ⟶ X) (q : Y ⟶ Y) : d.proj p q ≫ d.πY = d.πY ≫ q := by
  simp [proj, d.ιX_πY, d.ιY_πY]

/-- `iₓ (πₓ p iₓ + π_y q i_y) = p iₓ`. -/
theorem ιX_proj (p : X ⟶ X) (q : Y ⟶ Y) : d.ιX ≫ d.proj p q = p ≫ d.ιX := by
  simp [proj, reassoc_of% d.ιX_πX, reassoc_of% d.ιX_πY]

/-- `i_y (πₓ p iₓ + π_y q i_y) = q i_y`. -/
theorem ιY_proj (p : X ⟶ X) (q : Y ⟶ Y) : d.ιY ≫ d.proj p q = q ≫ d.ιY := by
  simp [proj, reassoc_of% d.ιY_πX, reassoc_of% d.ιY_πY]

/-- If `p` and `q` have degree zero, then so does `πₓ p iₓ + π_y q i_y`. -/
theorem proj_mem {p : X ⟶ X} {q : Y ⟶ Y} (hp : p ∈ grade (R := R) X X 0)
    (hq : q ∈ grade (R := R) Y Y 0) : d.proj p q ∈ grade (R := R) W W 0 := by
  refine Submodule.add_mem _ ?_ ?_
  · simpa using comp_mem (R := R) (comp_mem (R := R) d.ιX_mem hp) d.πX_mem
  · simpa using comp_mem (R := R) (comp_mem (R := R) d.ιY_mem hq) d.πY_mem

/-- If `p` and `q` are idempotent, then so is `πₓ p iₓ + π_y q i_y`. -/
theorem proj_idem {p : X ⟶ X} {q : Y ⟶ Y} (hp : p ≫ p = p) (hq : q ≫ q = q) :
    d.proj p q ≫ d.proj p q = d.proj p q := by
  simp only [proj, Preadditive.add_comp, Preadditive.comp_add, Category.assoc, d.ιX_πX_assoc,
    d.ιX_πY_assoc, d.ιY_πX_assoc, d.ιY_πY_assoc, Limits.zero_comp, Limits.comp_zero, add_zero,
    zero_add, reassoc_of% hp, reassoc_of% hq]

end Proj

variable {W : C} {M N : TwistedKaroubi R C}

/-- The direct sum `(W, πₓ p iₓ + π_y q i_y, m)` of `M = (X, p, m)` and `N = (Y, q, n)`; its twist
is that of `M`. -/
abbrev summandsObj (M N : TwistedKaroubi R C) (d : SummandData (R := R) M.X N.X W) :
    TwistedKaroubi R C where
  X := W
  p := d.proj M.p N.p
  p_mem := d.proj_mem M.p_mem N.p_mem
  idem := d.proj_idem M.idem N.idem
  twist := M.twist

variable (d : SummandData (R := R) M.X N.X W)

/-- The projection `πₓ p : (W, πₓ p iₓ + π_y q i_y, m) ⟶ (X, p, m)`. -/
def summandsFst : summandsObj M N d ⟶ M :=
  Hom.mk (d.πX ≫ M.p) (by
    refine ⟨?_, ?_, ?_⟩
    · have := comp_mem (R := R) M.p_mem d.πX_mem
      rw [zero_add] at this
      rwa [sub_self]
    · rw [← Category.assoc, d.proj_πX, Category.assoc, M.idem]
    · rw [Category.assoc, M.idem])

/-- The projection `π_y q : (W, πₓ p iₓ + π_y q i_y, m) ⟶ (Y, q, n)`, for `m = n`. -/
def summandsSnd (h : M.twist = N.twist) : summandsObj M N d ⟶ N :=
  Hom.mk (d.πY ≫ N.p) (by
    refine ⟨?_, ?_, ?_⟩
    · have := comp_mem (R := R) N.p_mem d.πY_mem
      rw [zero_add] at this
      rwa [show N.twist - M.twist = 0 by rw [h, sub_self]]
    · rw [← Category.assoc, d.proj_πY, Category.assoc, N.idem]
    · rw [Category.assoc, N.idem])

/-- The inclusion `p iₓ : (X, p, m) ⟶ (W, πₓ p iₓ + π_y q i_y, m)`. -/
def summandsInl : M ⟶ summandsObj M N d :=
  Hom.mk (M.p ≫ d.ιX) (by
    refine ⟨?_, ?_, ?_⟩
    · have := comp_mem (R := R) d.ιX_mem M.p_mem
      rw [zero_add] at this
      rwa [sub_self]
    · rw [← Category.assoc, M.idem]
    · rw [Category.assoc, d.ιX_proj, ← Category.assoc, M.idem])

/-- The inclusion `q i_y : (Y, q, n) ⟶ (W, πₓ p iₓ + π_y q i_y, m)`, for `m = n`. -/
def summandsInr (h : M.twist = N.twist) : N ⟶ summandsObj M N d :=
  Hom.mk (N.p ≫ d.ιY) (by
    refine ⟨?_, ?_, ?_⟩
    · have := comp_mem (R := R) d.ιY_mem N.p_mem
      rw [zero_add] at this
      rwa [show M.twist - N.twist = 0 by rw [h, sub_self]]
    · rw [← Category.assoc, N.idem]
    · rw [Category.assoc, d.ιY_proj, ← Category.assoc, N.idem])

/-- **The direct sum of two twisted idempotents with the same twist** through a common ambient
object: `(W, πₓ p iₓ + π_y q i_y, m)` with projections `πₓ p`, `π_y q` and inclusions `p iₓ`,
`q i_y`. -/
def biproductDataOfSummands (h : M.twist = N.twist) : BinaryBiproductData M N where
  bicone :=
    { pt := summandsObj M N d
      fst := summandsFst d
      snd := summandsSnd d h
      inl := summandsInl d
      inr := summandsInr d h
      inl_fst := hom_ext (by
        change (M.p ≫ d.ιX) ≫ d.πX ≫ M.p = M.p
        rw [Category.assoc, d.ιX_πX_assoc, M.idem])
      inl_snd := hom_ext (by
        change (M.p ≫ d.ιX) ≫ d.πY ≫ N.p = 0
        rw [Category.assoc, d.ιX_πY_assoc, Limits.zero_comp, Limits.comp_zero])
      inr_fst := hom_ext (by
        change (N.p ≫ d.ιY) ≫ d.πX ≫ M.p = 0
        rw [Category.assoc, d.ιY_πX_assoc, Limits.zero_comp, Limits.comp_zero])
      inr_snd := hom_ext (by
        change (N.p ≫ d.ιY) ≫ d.πY ≫ N.p = N.p
        rw [Category.assoc, d.ιY_πY_assoc, N.idem]) }
  isBilimit := isBinaryBilimitOfTotal _ (by
    ext
    change (d.πX ≫ M.p) ≫ M.p ≫ d.ιX + (d.πY ≫ N.p) ≫ N.p ≫ d.ιY = d.proj M.p N.p
    rw [Category.assoc, reassoc_of% M.idem, Category.assoc, reassoc_of% N.idem]
    rfl)

/-- The cone point of `biproductDataOfSummands d h` is `summandsObj M N d`. -/
theorem biproductDataOfSummands_pt (h : M.twist = N.twist) :
    (biproductDataOfSummands d h).bicone.pt = summandsObj M N d :=
  rfl

end SummandData

end CategoryTheory.GradedCategory.TwistedKaroubi
