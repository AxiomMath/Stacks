module

public import Mathlib.Algebra.Group.Action.Pretransitive

/-!
# Reconstructing a free transitive action from its difference map

An additive group `G` acts freely and transitively on a nonempty set `α` exactly when the
"difference" map `α × α → G` is well behaved: the bijection `e : α × α ≃ α × G` whose first
coordinate is the first projection and whose second coordinate vanishes on the diagonal and
satisfies the cocycle identity `d a b + d b c = d a c` is the same data as a free transitive
`G`-action on `α`.

This file performs that reconstruction once, abstractly, so that the deformation-theoretic
statements need only produce the bijection `e`.

## Main definitions

* `Deformation.addActionOfPairEquiv`: the additive action reconstructed from such a bijection.

## Main results

* `Deformation.addActionOfPairEquiv_pointwiseBijective`: from any fixed point, the action is a
  bijection from `G` onto `α`; equivalently the action is free and transitive.
* `Deformation.pairEquiv_inverse_difference`: the difference of a point from its translate is
  the translating vector.
* `Deformation.injective_difference_of_vadd`: for an action whose difference map inverts
  translation and which is pointwise bijective, the difference from a fixed point is injective.
* `Deformation.map_vadd_of_natural_difference`: a map of such actions whose difference maps are
  intertwined by a map of the acting groups is equivariant.

## Implementation notes

The action is oriented as a left additive action, so `t +ᵥ a` is the point whose difference
from `a` is `t`. Only `AddCommMonoid G` is required: commutativity is used to reorder
`d a b + d b c`, and no inverses are needed because the bijection `e` already provides them.

The last two results are stated for a bare `VAdd` rather than for `AddAction`, since the
functoriality statement they serve installs its actions locally.
-/

@[expose] public section

namespace Deformation

/-! ### The action attached to a difference bijection -/

section

/-- The additive action of `G` on `α` reconstructed from a bijection `α × α ≃ α × G` which
fixes the first coordinate, vanishes on the diagonal and satisfies the cocycle identity: the
translate of `a` by `t` is the second coordinate of `e.symm (a, t)`. -/
@[instance_reducible]
public noncomputable def addActionOfPairEquiv
    {G α : Type*} [AddCommMonoid G]
    (e : (α × α) ≃ (α × G))
    (hfirst : ∀ a b, (e (a, b)).1 = a)
    (hzero : ∀ a, (e (a, a)).2 = 0)
    (hcocycle : ∀ a b c, (e (a, b)).2 + (e (b, c)).2 = (e (a, c)).2) :
    AddAction G α := by
  let d : α → α → G := fun a b => (e (a, b)).2
  let act : G → α → α := fun t a => (e.symm (a, t)).2
  have hinv (t : G) (a : α) : e (a, act t a) = (a, t) := by
    have h := hfirst (e.symm (a, t)).1 (e.symm (a, t)).2
    rw [e.apply_symm_apply] at h
    exact e.eq_symm_apply.mp (Prod.ext h rfl)
  have hactDiff (a b : α) : act (d a b) a = b :=
    congrArg Prod.snd
      (e.symm_apply_eq.mpr (Prod.ext (hfirst a b).symm rfl : (a, d a b) = e (a, b)))
  refine
    { vadd := act
      add_vadd := ?_
      zero_vadd := ?_ }
  · intro t s a
    let b := act s a
    let c := act t b
    have hs : d a b = s := congrArg Prod.snd (hinv s a)
    have ht : d b c = t := congrArg Prod.snd (hinv t b)
    have hdiff : d a c = t + s := by
      rw [add_comm, ← hs, ← ht]
      exact (hcocycle a b c).symm
    rw [← hdiff]
    exact hactDiff a c
  · intro a
    exact congrArg Prod.snd
      (e.symm_apply_eq.mpr (Prod.ext (hfirst a a).symm (hzero a).symm : (a, 0) = e (a, a)))

/-- Applying `e` to the first coordinate `a` and the translate of `a` by `t` recovers `(a, t)`. -/
private theorem pair_equiv_apply_symm_snd
    {G α : Type*} (e : (α × α) ≃ (α × G))
    (hfirst : ∀ a b, (e (a, b)).1 = a) (a : α) (t : G) :
    e (a, (e.symm (a, t)).2) = (a, t) := by
  have h := hfirst (e.symm (a, t)).1 (e.symm (a, t)).2
  rw [e.apply_symm_apply] at h
  exact e.eq_symm_apply.mp (Prod.ext h rfl)

/-- From any fixed point, translation by a vector is a bijection onto the whole set: the
reconstructed action is free and transitive. -/
public theorem addActionOfPairEquiv_pointwiseBijective
    {G α : Type*} [AddCommMonoid G]
    (e : (α × α) ≃ (α × G))
    (hfirst : ∀ a b, (e (a, b)).1 = a)
    (a : α) : Function.Bijective (fun t : G => (e.symm (a, t)).2) := by
  have hinv := pair_equiv_apply_symm_snd e hfirst a
  refine ⟨fun s t h => ?_, fun b => ⟨(e (a, b)).2, ?_⟩⟩
  · exact congrArg Prod.snd
      ((hinv s).symm.trans ((congrArg (fun z : α => e (a, z)) h).trans (hinv t)))
  · exact congrArg Prod.snd
      (e.symm_apply_eq.mpr (Prod.ext (hfirst a b).symm rfl : (a, (e (a, b)).2) = e (a, b)))

/-- The difference of a point from its translate is the translating vector. -/
public theorem pairEquiv_inverse_difference
    {G α : Type*} (e : (α × α) ≃ (α × G))
    (hfirst : ∀ a b, (e (a, b)).1 = a) (a : α) (t : G) :
    (e (a, (e.symm (a, t)).2)).2 = t := by
  exact congrArg Prod.snd (pair_equiv_apply_symm_snd e hfirst a t)

end

/-! ### Equivariance from naturality of the difference map -/

section

/-- If translation inverts the difference map and is pointwise bijective, then the difference
from a fixed point is injective. -/
public theorem injective_difference_of_vadd
    {G α : Type*} [VAdd G α]
    (difference : α → α → G)
    (hdiff : ∀ (a : α) (t : G), difference a (t +ᵥ a) = t)
    (hbij : ∀ a : α, Function.Bijective (fun t : G => t +ᵥ a)) :
    ∀ a : α, Function.Injective (difference a) := by
  intro a b c hbc
  obtain ⟨tb, rfl⟩ := (hbij a).2 b
  obtain ⟨tc, rfl⟩ := (hbij a).2 c
  simp only [hdiff] at hbc
  rw [hbc]

/-- A map of sets with difference-determined translations is equivariant for any map of the
acting groups that intertwines the two difference maps. -/
public theorem map_vadd_of_natural_difference
    {G H α β : Type*} [VAdd G α] [VAdd H β]
    (difference₁ : α → α → G) (difference₂ : β → β → H)
    (hdiff₁ : ∀ (a : α) (t : G), difference₁ a (t +ᵥ a) = t)
    (hdiff₂ : ∀ (a : β) (t : H), difference₂ a (t +ᵥ a) = t)
    (hbij₂ : ∀ a : β, Function.Bijective (fun t : H => t +ᵥ a))
    (F : α → β) (L : G → H)
    (hnat : ∀ a b, difference₂ (F a) (F b) = L (difference₁ a b)) :
    ∀ a t, F (t +ᵥ a) = L t +ᵥ F a := by
  intro a t
  apply injective_difference_of_vadd difference₂ hdiff₂ hbij₂ (F a)
  rw [hnat, hdiff₁, hdiff₂]

end

end Deformation
