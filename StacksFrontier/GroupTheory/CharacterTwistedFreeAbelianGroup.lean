module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The character twist of the free abelian group on a set with a group action

Let a group `G` act on a set `α` and let `χ : G → ℤˣ` be a character. The *character twist* of
the free abelian group on `α` is the quotient of `FreeAbelianGroup α` by the subgroup generated
by the elements `of (g • a) - χ g • of a`. It is the algebra underlying the twisted free abelian
sheaf attached to a group acting on an object of a site.

When the action of `G` on `α` is free, the twist is free abelian on the orbits of `α`, with the
class of a point `a₀` a basis vector up to the sign `χ g`. Rather than exhibiting that basis the
file constructs, for each point `a₀` with trivial stabiliser, the coordinate functional at the
orbit of `a₀`: an additive map to `ℤ` sending the class of `a₀` to `1`. That retraction is what
makes the class of `a₀` a nonzero element of infinite order, and makes `t ↦ t ⊗ [a₀]` injective
for every abelian group of coefficients.

## Main definitions

* `FreeAbelianGroup.characterSubgroup` is the subgroup of relations imposed by `χ`.
* `FreeAbelianGroup.CharacterTwist` is the quotient by those relations, and
  `FreeAbelianGroup.characterClass` is the class of a point of `α` in it.
* `FreeAbelianGroup.characterCoordinate` is the coordinate functional at the orbit of a point
  with trivial stabiliser.

## Main results

* `FreeAbelianGroup.characterCoordinate_characterClass_self`: the coordinate functional at the
  orbit of `a₀` takes the value `1` on the class of `a₀`.
* `FreeAbelianGroup.injective_tmul_characterClass`: for any abelian group `M` the map
  `t ↦ t ⊗ₜ [a₀]` into `M ⊗_ℤ CharacterTwist` is injective.
* `FreeAbelianGroup.zsmul_characterClass_injective`: the class of `a₀` has infinite order.
* `AddMonoidHom.injective_zsmul_of_eq_one` and `AddMonoidHom.injective_tmul_of_eq_one` are the
  two consequences of a coordinate functional, for an arbitrary abelian group.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public section

universe u v

/-! ### Elements with a coordinate functional -/

namespace AddMonoidHom

/-- An element on which some additive map to `ℤ` takes the value `1` has infinite order. -/
theorem injective_zsmul_of_eq_one {Q : Type*} [AddCommGroup Q] (r : Q →+ ℤ) {z : Q}
    (hz : r z = 1) : Function.Injective fun n : ℤ => n • z := by
  intro m n hmn
  have h := congrArg r hmn
  rw [map_zsmul, map_zsmul, hz] at h
  simpa using h

/-- An element on which some additive map to `ℤ` takes the value `1` generates a direct summand:
tensoring with it is injective, for every abelian group of coefficients. -/
theorem injective_tmul_of_eq_one {M Q : Type*} [AddCommGroup M] [AddCommGroup Q] (r : Q →+ ℤ)
    {z : Q} (hz : r z = 1) : Function.Injective fun t : M => t ⊗ₜ[ℤ] z := by
  let e : TensorProduct ℤ M Q →ₗ[ℤ] M :=
    (TensorProduct.rid ℤ M).toLinearMap ∘ₗ TensorProduct.map LinearMap.id r.toIntLinearMap
  have hid : ∀ t : M, e (t ⊗ₜ[ℤ] z) = t := by
    intro t
    change
      (TensorProduct.rid ℤ M) (TensorProduct.map LinearMap.id r.toIntLinearMap (t ⊗ₜ[ℤ] z)) = t
    rw [TensorProduct.map_tmul]
    show (TensorProduct.rid ℤ M) (t ⊗ₜ[ℤ] r z) = t
    rw [hz, TensorProduct.rid_tmul, one_smul]
  intro t t' htt
  have := congrArg e htt
  rwa [hid, hid] at this

end AddMonoidHom

namespace FreeAbelianGroup

variable {G : Type u} [Group G] {α : Type v} (ρ : G →* Function.End α) (χ : G →* ℤˣ)

/-- The subgroup of relations imposed by the character `χ` on the free abelian group on `α`:
the generator at `g • a` is `χ g` times the generator at `a`. -/
def characterSubgroup : AddSubgroup (FreeAbelianGroup α) :=
  AddSubgroup.closure {x | ∃ (g : G) (a : α), x = of (ρ g a) - (χ g : ℤ) • of a}

/-- The character twist of the free abelian group on `α`: the free abelian group on `α` modulo
the relations imposed by `χ`. -/
abbrev CharacterTwist : Type v := FreeAbelianGroup α ⧸ characterSubgroup ρ χ

/-- The class of a point of `α` in the character twist. -/
def characterClass (a : α) : CharacterTwist ρ χ := QuotientAddGroup.mk (of a)

variable {ρ χ}

/-- The class of `g • a` is `χ g` times the class of `a`. -/
theorem characterClass_apply (g : G) (a : α) :
    characterClass ρ χ (ρ g a) = (χ g : ℤ) • characterClass ρ χ a := by
  have h : of (ρ g a) - (χ g : ℤ) • of a ∈ characterSubgroup ρ χ :=
    AddSubgroup.subset_closure ⟨g, a, rfl⟩
  have h' := (QuotientAddGroup.eq_iff_sub_mem (N := characterSubgroup ρ χ)).mpr h
  rwa [QuotientAddGroup.mk_zsmul] at h'

section Coordinate

variable (ρ χ)

open scoped Classical in
/-- The weight of a point `b` of `α` relative to a base point `a₀`: the value of the character
at the group element carrying `a₀` to `b`, and `0` when `b` is not in the orbit of `a₀`. -/
noncomputable def characterWeight (a₀ b : α) : ℤ :=
  if h : ∃ g : G, ρ g a₀ = b then (χ h.choose : ℤ) else 0

variable {ρ χ}

/-- The weight of a point `b` outside the orbit of `a₀` is `0`. -/
theorem characterWeight_eq_zero {a₀ b : α} (h : ¬ ∃ g : G, ρ g a₀ = b) :
    characterWeight ρ χ a₀ b = 0 := by
  classical
  simp [characterWeight, h]

/-- If `a₀` has trivial stabiliser, the weight of `g • a₀` relative to `a₀` is `χ g`. -/
theorem characterWeight_of_apply {a₀ : α} (hfree : Function.Injective fun g : G => ρ g a₀)
    (g : G) : characterWeight ρ χ a₀ (ρ g a₀) = (χ g : ℤ) := by
  classical
  have hex : ∃ k : G, ρ k a₀ = ρ g a₀ := ⟨g, rfl⟩
  rw [characterWeight, dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg (fun k : G => ((χ k : ℤ))) (hfree hex.choose_spec)

/-- The action of `g * h` on `a` is the action of `g` on the action of `h` on `a`. -/
theorem apply_mul_apply (g h : G) (a : α) : ρ (g * h) a = ρ g (ρ h a) := by
  rw [map_mul]
  rfl

/-- The identity of `G` acts trivially on `α`. -/
theorem apply_one (a : α) : ρ (1 : G) a = a := by
  rw [map_one]
  rfl

/-- The weight function transforms according to `χ`. -/
theorem characterWeight_apply {a₀ : α} (hfree : Function.Injective fun g : G => ρ g a₀) (g : G)
    (b : α) :
    characterWeight ρ χ a₀ (ρ g b) = (χ g : ℤ) * characterWeight ρ χ a₀ b := by
  classical
  by_cases hb : ∃ k : G, ρ k a₀ = b
  · obtain ⟨k, rfl⟩ := hb
    rw [← apply_mul_apply, characterWeight_of_apply hfree, characterWeight_of_apply hfree,
      map_mul, Units.val_mul]
  · have hgb : ¬ ∃ k : G, ρ k a₀ = ρ g b := by
      rintro ⟨k, hk⟩
      refine hb ⟨g⁻¹ * k, ?_⟩
      rw [apply_mul_apply, hk, ← apply_mul_apply, inv_mul_cancel, apply_one]
    rw [characterWeight_eq_zero hgb, characterWeight_eq_zero hb, mul_zero]

/-- The coordinate functional at the orbit of `a₀`, read on the free abelian group on `α`. -/
noncomputable def characterWeightHom (a₀ : α) : FreeAbelianGroup α →+ ℤ :=
  FreeAbelianGroup.lift (characterWeight ρ χ a₀)

/-- The map `characterWeightHom a₀` sends the generator at `b` to the weight of `b`. -/
@[simp]
theorem characterWeightHom_of (a₀ b : α) :
    characterWeightHom (ρ := ρ) (χ := χ) a₀ (of b) = characterWeight ρ χ a₀ b :=
  FreeAbelianGroup.lift_apply_of _ _

/-- If `a₀` has trivial stabiliser, the relations imposed by `χ` lie in the kernel of
`characterWeightHom`. -/
theorem characterSubgroup_le_ker {a₀ : α} (hfree : Function.Injective fun g : G => ρ g a₀) :
    characterSubgroup ρ χ ≤ (characterWeightHom (ρ := ρ) (χ := χ) a₀).ker := by
  rw [characterSubgroup, AddSubgroup.closure_le]
  rintro x ⟨g, a, rfl⟩
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_zsmul, characterWeightHom_of,
    sub_eq_zero, characterWeight_apply hfree g a, smul_eq_mul]

/-- The coordinate functional at the orbit of a point `a₀` with trivial stabiliser: the additive
map from the character twist to `ℤ` taking the class of `a₀` to `1`. -/
noncomputable def characterCoordinate {a₀ : α} (hfree : Function.Injective fun g : G => ρ g a₀) :
    CharacterTwist ρ χ →+ ℤ :=
  QuotientAddGroup.lift _ (characterWeightHom (ρ := ρ) (χ := χ) a₀)
    (characterSubgroup_le_ker hfree)

/-- The coordinate functional at the orbit of `a₀` sends the class of `b` to the weight of `b`. -/
@[simp]
theorem characterCoordinate_characterClass {a₀ : α}
    (hfree : Function.Injective fun g : G => ρ g a₀) (b : α) :
    characterCoordinate (χ := χ) hfree (characterClass ρ χ b) = characterWeight ρ χ a₀ b :=
  (characterWeightHom_of (ρ := ρ) (χ := χ) a₀ b)

/-- The coordinate functional at the orbit of `a₀` takes the value `1` on the class of `a₀`. -/
@[simp]
theorem characterCoordinate_characterClass_self {a₀ : α}
    (hfree : Function.Injective fun g : G => ρ g a₀) :
    characterCoordinate (χ := χ) hfree (characterClass ρ χ a₀) = 1 := by
  rw [characterCoordinate_characterClass]
  have h1 : characterWeight ρ χ a₀ (ρ (1 : G) a₀) = ((χ 1 : ℤˣ) : ℤ) :=
    characterWeight_of_apply hfree 1
  rw [apply_one] at h1
  rw [h1, map_one, Units.val_one]

/-- The class of a point with trivial stabiliser has infinite order in the character twist. -/
theorem zsmul_characterClass_injective {a₀ : α}
    (hfree : Function.Injective fun g : G => ρ g a₀) :
    Function.Injective fun n : ℤ => n • characterClass ρ χ a₀ :=
  AddMonoidHom.injective_zsmul_of_eq_one _ (characterCoordinate_characterClass_self hfree)

/-- For any abelian group of coefficients `M`, tensoring with the class of a point `a₀` with
trivial stabiliser is injective. This is the statement that the class of `a₀` generates a direct
summand of the character twist. -/
theorem injective_tmul_characterClass {M : Type*} [AddCommGroup M] {a₀ : α}
    (hfree : Function.Injective fun g : G => ρ g a₀) :
    Function.Injective fun t : M => t ⊗ₜ[ℤ] characterClass ρ χ a₀ :=
  AddMonoidHom.injective_tmul_of_eq_one _ (characterCoordinate_characterClass_self hfree)

end Coordinate

end FreeAbelianGroup

end
