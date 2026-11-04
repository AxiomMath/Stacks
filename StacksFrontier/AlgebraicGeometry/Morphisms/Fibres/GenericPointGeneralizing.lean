module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointCoheight
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

/-!
# Generic points of fibres, read in the ambient scheme

For a morphism `f : X ⟶ S` and a point `x : X`, membership of `f.asFiber x` in the generic
points of the scheme-theoretic fibre `f.fiber (f x)` is a condition on `x` inside `X`: it says
that no proper generalization of `x` in `X` lies over `f x`.  The fibre is homeomorphic to the
set-theoretic fibre by `AlgebraicGeometry.Scheme.Hom.fiberHomeo`, and generic points of a
scheme are exactly the points maximal for the specialization order, by
`AlgebraicGeometry.mem_genericPoints_iff_isMax`.

That reformulation makes the condition transport along any morphism `π : Y ⟶ X` which lifts
generalizations: a generalization of `π y` lying over `f (π y)` lifts to a generalization of `y`
lying over `f (π y)`, hence equals `y` when `y` is a generic point of its own fibre of `π ≫ f`.
This is the step of the reduced fibre theorem which says that a point of the normalized base
change which is a generic point of its fibre lies over a point of `X` with the same property.

Also recorded is the converse of
`AlgebraicGeometry.coheight_eq_coheight_base_of_asFiber_mem_genericPoints`: for a flat morphism
of locally Noetherian schemes, a point whose coheight equals the coheight of its image — the
latter being finite — is a generic point of its own fibre.  The dimension formula for a flat
morphism expresses the coheight of `x` as the coheight of `f x` plus the dimension of the local
ring of the fibre at `x`, so the two conditions both say that the last summand vanishes.

## Main results

* `AlgebraicGeometry.mem_genericPoints_asFiber_iff`: the generic-point condition on a fibre,
  read as a condition on the ambient scheme.
* `AlgebraicGeometry.mem_genericPoints_asFiber_of_generalizingMap`: the condition transports
  along a morphism lifting generalizations.
* `AlgebraicGeometry.mem_genericPoints_asFiber_of_coheight_eq` and
  `AlgebraicGeometry.coheight_eq_coheight_base_iff_asFiber_mem_genericPoints`: the converse of
  the coheight computation at a generic point of a fibre, and the resulting equivalence.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **A point is a generic point of its own fibre exactly when no proper generalization of it
lies in the same fibre.** The scheme-theoretic fibre through `x` is homeomorphic to the
set-theoretic one, and a generic point of a scheme is a point maximal for the specialization
order. -/
theorem mem_genericPoints_asFiber_iff (f : X ⟶ S) (x : X) :
    f.asFiber x ∈ genericPoints ↥(f.fiber (f.base x)) ↔
      ∀ x' : X, x' ⤳ x → f.base x' = f.base x → x' = x := by
  have hle : ∀ a b : f.fiber (f.base x), a ≤ b ↔ f.fiberι (f.base x) b ⤳ f.fiberι (f.base x) a :=
    fun a b => by
      rw [Scheme.le_iff_specializes, (f.fiberι (f.base x)).isEmbedding.isInducing.specializes_iff]
  have hrange := f.range_fiberι (f.base x)
  rw [mem_genericPoints_iff_isMax]
  constructor
  · intro hmax x' hspec hfx
    obtain ⟨t, rfl⟩ : x' ∈ Set.range (f.fiberι (f.base x)) := by rw [hrange]; exact hfx
    have h1 : f.asFiber x ≤ t := (hle _ _).mpr (by rwa [f.fiberι_asFiber])
    have h2 := (hle _ _).mp (hmax h1)
    rw [f.fiberι_asFiber] at h2
    exact (h2.antisymm hspec).symm.eq
  · intro hgen t ht
    have hspec := (hle _ _).mp ht
    rw [f.fiberι_asFiber] at hspec
    refine le_of_eq ((f.fiberι (f.base x)).isEmbedding.injective ?_)
    rw [f.fiberι_asFiber]
    exact hgen _ hspec (hrange.le (Set.mem_range_self t))

/-- **The generic-point condition on a fibre transports along a morphism which lifts
generalizations.** Let `π : Y ⟶ X` be a morphism whose underlying map lifts generalizations —
for instance a flat morphism — and let `f : X ⟶ S`. If `y : Y` is a generic point of its own
fibre of `π ≫ f`, then `π y` is a generic point of its own fibre of `f`.

A generalization `x'` of `π y` lying over `f (π y)` lifts to a generalization `y'` of `y`, and
that `y'` lies over `f (π y)` too, so it is `y` and `x'` is `π y`. -/
theorem mem_genericPoints_asFiber_of_generalizingMap {Y : Scheme.{u}} (π : Y ⟶ X) (f : X ⟶ S)
    (hπ : GeneralizingMap π.base) {y : Y}
    (hy : (π ≫ f).asFiber y ∈ genericPoints ↥((π ≫ f).fiber ((π ≫ f).base y))) :
    f.asFiber (π.base y) ∈ genericPoints ↥(f.fiber (f.base (π.base y))) := by
  rw [mem_genericPoints_asFiber_iff] at hy ⊢
  intro x' hspec hfx
  obtain ⟨y', hy', rfl⟩ := hπ hspec
  have : y' = y := by
    refine hy y' hy' ?_
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact hfx
  rw [this]

/-- **A point of a flat morphism whose coheight equals that of its image is a generic point of
its own fibre.** This is the converse of
`AlgebraicGeometry.coheight_eq_coheight_base_of_asFiber_mem_genericPoints`; the coheight of the
image has to be finite, since the dimension formula is cancelled by it. -/
theorem mem_genericPoints_asFiber_of_coheight_eq (f : X ⟶ S) [Flat f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian S] {x : X} (hne : coheight (f.base x) ≠ ⊤)
    (h : coheight x = coheight (f.base x)) :
    f.asFiber x ∈ genericPoints ↥(f.fiber (f.base x)) := by
  set d := ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) with hd
  have key := ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat f x
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, h] at key
  rw [← ringKrullDim_stalk_eq_zero_iff_mem_genericPoints, ← hd]
  refine add_right_cancel_of_ne_top_of_ne_bot
    (c := ((coheight (f.base x) : ℕ∞) : WithBot ℕ∞)) (by simpa using hne) WithBot.coe_ne_bot ?_
  rw [zero_add, add_comm]
  exact key.symm

/-- **The coheight of a point of a flat morphism equals that of its image exactly when the point
is a generic point of its own fibre**, the coheight of the image being finite. -/
theorem coheight_eq_coheight_base_iff_asFiber_mem_genericPoints (f : X ⟶ S) [Flat f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] {x : X} (hne : coheight (f.base x) ≠ ⊤) :
    coheight x = coheight (f.base x) ↔
      f.asFiber x ∈ genericPoints ↥(f.fiber (f.base x)) :=
  ⟨mem_genericPoints_asFiber_of_coheight_eq f hne,
    coheight_eq_coheight_base_of_asFiber_mem_genericPoints f⟩

end AlgebraicGeometry

end
