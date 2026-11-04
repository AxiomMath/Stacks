module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.Basic

/-!
# The affine bases of an inverse system with surjective transitions are closed subschemes

Let `(Aₙ)` be an inverse system of rings indexed by `ℕᵒᵖ` whose consecutive transition maps
`Aₙ₊₁ → Aₙ` are surjective, and let `A = lim Aₙ`. Then every projection `A → Aₙ` out of the
inverse limit is surjective as well, so each `Spec Aₙ → Spec A` is a closed immersion, as is
each transition `Spec Aₙ → Spec Aₙ₊₁`. These are the facts that make the affine bases of
Grothendieck's existence theorem closed subschemes of the inverse-limit base, and hence, after
base change, make its infinitesimal neighbourhoods closed subschemes and closed subspaces.

## Main results

* `CommRingCat.exists_cone_lift_of_compatible`: a family of elements of the rings of a diagram,
  compatible with the transition maps, is the family of components of an element of the limit.
* `CommRingCat.surjective_π_app_of_surjective_succ`: for an inverse system indexed by `ℕᵒᵖ` with
  surjective consecutive transition maps, every projection out of the limit is surjective.
* `AlgebraicGeometry.GrothendieckExistence.isClosedImmersion_baseProjection` and
  `AlgebraicGeometry.GrothendieckExistence.isClosedImmersion_baseTransition`: the affine base at
  a level is a closed subscheme of the inverse-limit base, and of the affine base at the next
  level.

## Implementation notes

`CategoryTheory.Limits.Concrete.surjective_π_app_zero_of_surjective_map` is the same statement
for the projection to level `0` only, in any concrete category whose forgetful functor preserves
sequential limits. The projection to level `n` is not a composite of that one with anything —
the transition maps point the wrong way — so the lifts are chosen again here, starting from
level `n` rather than from level `0`.

An element of a limit of rings is produced from a compatible family by the comparison with the
cone on the free commutative ring on one generator, whose points are exactly the elements of a
ring; this is the device of `CommRingCat.Limits.isUnit_iff_forall_isUnit`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u'

namespace CommRingCat

/-- A family of elements of the rings of a diagram, compatible with the transition maps, is the
family of components of an element of the limit.

The element is the image of the generator under the comparison morphism from the cone on the
free commutative ring on one generator whose component at `j` sends the generator to `a j`. -/
theorem exists_cone_lift_of_compatible {J : Type u'} [SmallCategory J] {F : J ⥤ CommRingCat.{u}}
    {c : Cone F} (hc : IsLimit c) (a : ∀ j, F.obj j)
    (ha : ∀ {i j : J} (f : i ⟶ j), (F.map f).hom (a i) = a j) :
    ∃ x : c.pt, ∀ j, (c.π.app j).hom x = a j := by
  let s : Cone F := .mk (CommRingCat.of (FreeCommRing PUnit))
    { app := fun j ↦ ofHom (FreeCommRing.lift (fun _ ↦ a j))
      naturality := fun i j f ↦ by
        ext1
        show FreeCommRing.lift (fun _ ↦ a j) = _
        ext x
        simpa using (ha f).symm }
  refine ⟨(hc.lift s).hom (FreeCommRing.of PUnit.unit), fun j ↦ ?_⟩
  show (hc.lift s ≫ c.π.app j).hom (FreeCommRing.of PUnit.unit) = a j
  rw [hc.fac s j]
  exact FreeCommRing.lift_of ..

/-- Two consecutive transition maps of an inverse system indexed by `ℕᵒᵖ` compose to the
transition map between the outer levels. -/
private theorem map_homOfLE_op_apply_map_homOfLE_op {F : ℕᵒᵖ ⥤ CommRingCat.{u}} {a b c : ℕ}
    (h₁ : a ≤ b) (h₂ : b ≤ c) (x : F.obj (op c)) :
    (F.map (homOfLE h₁).op).hom ((F.map (homOfLE h₂).op).hom x) =
      (F.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [Subsingleton.elim (homOfLE (h₁.trans h₂)).op ((homOfLE h₂).op ≫ (homOfLE h₁).op),
    F.map_comp]
  rfl

/-- For an inverse system of rings indexed by `ℕᵒᵖ` whose consecutive transition maps are
surjective, every projection out of the limit is surjective.

Given an element of the ring at level `n`, lifts of it are chosen at every higher level, and
the resulting family is pushed down to all levels; it is compatible because any two morphisms
with the same source and target in `ℕᵒᵖ` are equal. -/
theorem surjective_π_app_of_surjective_succ {F : ℕᵒᵖ ⥤ CommRingCat.{u}} {c : Cone F}
    (hc : IsLimit c)
    (hF : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    Function.Surjective (c.π.app (op n)).hom := by
  classical
  intro x
  -- the chosen lifts of `x` to the levels above `n`
  let b : (k : ℕ) → F.obj (op (n + k)) := Nat.rec x fun k y ↦ (hF (n + k) y).choose
  have hb : ∀ k : ℕ, (F.map (homOfLE (Nat.le_succ (n + k))).op).hom (b (k + 1)) = b k :=
    fun k ↦ (hF (n + k) (b k)).choose_spec
  have hchain : ∀ k l : ℕ, ∀ h : k ≤ l,
      (F.map (homOfLE (Nat.add_le_add_left h n)).op).hom (b l) = b k := by
    intro k l h
    induction l, h using Nat.le_induction with
    | base =>
      rw [Subsingleton.elim (homOfLE (Nat.add_le_add_left (le_refl k) n)).op (𝟙 (op (n + k))),
        F.map_id]
      rfl
    | succ l hl ih =>
      rw [← map_homOfLE_op_apply_map_homOfLE_op (Nat.add_le_add_left hl n) (Nat.le_succ (n + l)),
        hb l]
      exact ih
  -- the family of all their images, which is `x` at level `n`
  set a : ∀ j : ℕᵒᵖ, F.obj j := fun j ↦
    (F.map (homOfLE (Nat.le_add_left j.unop n)).op).hom (b j.unop) with ha'
  have ha : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), (F.map f).hom (a i) = a j := by
    intro i j f
    obtain ⟨p⟩ := i
    obtain ⟨q⟩ := j
    have hqp : q ≤ p := leOfHom f.unop
    rw [ha', Subsingleton.elim f (homOfLE hqp).op]
    dsimp only
    rw [map_homOfLE_op_apply_map_homOfLE_op, ← hchain q p hqp,
      map_homOfLE_op_apply_map_homOfLE_op]
  obtain ⟨y, hy⟩ := exists_cone_lift_of_compatible hc a ha
  refine ⟨y, ?_⟩
  rw [hy (op n), ha']
  dsimp only
  exact hchain 0 n (Nat.zero_le n)

end CommRingCat

namespace AlgebraicGeometry.GrothendieckExistence

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u})
  (hF : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom)

include hF

/-- The projection from the inverse-limit ring onto the ring at level `n` is surjective, when
the consecutive transition maps of the inverse system are. -/
theorem surjective_limit_π (n : ℕ) : Function.Surjective (limit.π F (op n)).hom :=
  CommRingCat.surjective_π_app_of_surjective_succ (limit.isLimit F) hF n

/-- The affine base at level `n` is a closed subscheme of the inverse-limit base. -/
theorem isClosedImmersion_baseProjection (n : ℕ) : IsClosedImmersion (baseProjection F n) :=
  IsClosedImmersion.spec_of_surjective _ (surjective_limit_π F hF n)

/-- The affine base at level `n` is a closed subscheme of the affine base at level `n + 1`. -/
theorem isClosedImmersion_baseTransition (n : ℕ) : IsClosedImmersion (baseTransition F n) :=
  IsClosedImmersion.spec_of_surjective _ (hF n)

end AlgebraicGeometry.GrothendieckExistence

end
