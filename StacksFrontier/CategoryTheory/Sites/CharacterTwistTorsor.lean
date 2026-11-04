module

public import StacksFrontier.CategoryTheory.Sites.CharacterTwist
public import StacksFrontier.GroupTheory.CharacterTwistedFreeAbelianGroup
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The character twist attached to a torsor under a group acting on an object of a site

Let `C` be a site and let a group `G` act on an object `W` of `C` by automorphisms. The object `W`
is a *`G`-torsor over the final object* when the three conditions of
`CategoryTheory.IsTorsorObject` hold: every object of `C` is covered by objects admitting a
morphism to `W`, any two morphisms `V ⟶ W` become translates of each other by a group element
locally on `V`, and that group element is unique except over the objects covered by the empty
sieve. These are the properties of the quotient morphism `W ⟶ W/G` of a free action of a finite
group that Stacks 0727 uses.

For the twisted free abelian sheaf `ℤ(χ)` attached to a character `χ : G → ℤˣ`, the class of a
morphism `p : V ⟶ W` in the twist presheaf generates a direct summand, so it has infinite order and
tensoring with it is injective; and locally on an object lying over `W` every section of the twist
presheaf is an integer multiple of that class. Together these say that `ℤ(χ)` is free of rank one
over `W`.

## Main definitions

* `CategoryTheory.splittingSieve` is the sieve of arrows whose source admits a morphism to `W`,
  and `CategoryTheory.translationSieve` the sieve of arrows along which two morphisms to `W`
  become translates of each other.
* `CategoryTheory.IsTorsorObject` is the torsor condition.
* `CategoryTheory.actEnd` is the action of `G` on the morphisms into `W` by postcomposition.
* `CategoryTheory.IsTorsorObject.twistCoordinate` is the coordinate functional of the twist
  presheaf at a morphism into `W`.

## Main results

* `CategoryTheory.IsTorsorObject.injective_comp_act`: over an object not covered by the empty
  sieve the group acts freely on the morphisms into `W`.
* `CategoryTheory.IsTorsorObject.zsmul_twistedGenerator_injective` and
  `CategoryTheory.IsTorsorObject.injective_tmul_twistedGenerator`: the class of a morphism
  `p : V ⟶ W` has infinite order in the twist presheaf and generates a direct summand.
* `CategoryTheory.IsTorsorObject.exists_sieve_twistedGenerator_zsmul`: locally on an object
  lying over `W` every section of the twist presheaf is an integer multiple of the class of the
  structure morphism.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] {W : C} {G : Type w} [Group G]

/-! ### The automorphisms attached to the group elements -/

section Act

variable (act : G →* Aut W)

/-- Acting by a product is acting by the two factors in turn. -/
theorem act_hom_mul (g g' : G) : (act (g * g')).hom = (act g').hom ≫ (act g).hom := by
  rw [map_mul]
  rfl

/-- Acting by the unit is the identity. -/
theorem act_hom_one : (act (1 : G)).hom = 𝟙 W := by
  rw [map_one]
  rfl

/-- The action of `G` on the morphisms into `W` by postcomposition with the automorphisms. -/
def actEnd (V : C) : G →* Function.End (V ⟶ W) where
  toFun g φ := φ ≫ (act g).hom
  map_one' := funext fun φ => by
    simp only [act_hom_one, Category.comp_id]
    rfl
  map_mul' g g' := funext fun φ => by
    simp only [act_hom_mul, ← Category.assoc]
    rfl

/-- The action on morphisms into `W` is postcomposition with the automorphism. -/
@[simp]
theorem actEnd_apply (V : C) (g : G) (φ : V ⟶ W) : actEnd act V g φ = φ ≫ (act g).hom := rfl

variable (χ : G →* ℤˣ)

/-- The relations imposed by `χ` on the free abelian group on the morphisms into `W` are the
relations of the character twist of that free abelian group. -/
theorem characterSubgroup_actEnd (V : C) :
    FreeAbelianGroup.characterSubgroup (actEnd act V) χ = characterRelations W act χ V := rfl

/-- The quotient map from the free abelian group on the morphisms `V ⟶ W` onto the value of the
twist presheaf at `V`. -/
def twistProjection (V : C) :
    FreeAbelianGroup (V ⟶ W) →+ (characterTwistPresheaf W act χ).obj (op V) where
  toFun z := QuotientAddGroup.mk z
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The projection sends the generator of a morphism `φ` to its class in the twist presheaf. -/
@[simp]
theorem twistProjection_of {V : C} (φ : V ⟶ W) :
    twistProjection act χ V (FreeAbelianGroup.of φ) = twistedGenerator W act χ φ := rfl

/-- The class of a morphism in the twist presheaf is its class in the character twist of the free
abelian group. -/
theorem twistedGenerator_eq_characterClass {V : C} (φ : V ⟶ W) :
    twistedGenerator W act χ φ = FreeAbelianGroup.characterClass (actEnd act V) χ φ := rfl

end Act

/-! ### Torsors over the final object -/

/-- The sieve on `V` consisting of the arrows whose source admits a morphism to `W`. -/
def splittingSieve (W V : C) : Sieve V where
  arrows Y _ := Nonempty (Y ⟶ W)
  downward_closed := fun hf k => hf.elim fun φ => ⟨k ≫ φ⟩

/-- The sieve on `V` consisting of the arrows along which two morphisms `φ ψ : V ⟶ W` become
translates of each other under the action of `G`. -/
def translationSieve (act : G →* Aut W) {V : C} (φ ψ : V ⟶ W) : Sieve V where
  arrows _ f := ∃ g : G, f ≫ ψ = f ≫ φ ≫ (act g).hom
  downward_closed := by
    rintro Y Z f ⟨g, hg⟩ k
    refine ⟨g, ?_⟩
    rw [Category.assoc, hg, Category.assoc]

/-- An object `W` of a site with an action of a group `G` by automorphisms is a *`G`-torsor over
the final object* when every object is covered by objects admitting a morphism to `W`, any two
morphisms into `W` become translates of each other locally, and the translating group element is
unique except over the objects covered by the empty sieve. -/
@[sga "4 IV 5.9" "special case"]
structure IsTorsorObject (act : G →* Aut W) (J : GrothendieckTopology C) : Prop where
  /-- The morphisms to `W` cover every object. -/
  splittingSieve_mem (V : C) : splittingSieve W V ∈ J V
  /-- Two morphisms into `W` are translates of each other, locally on the source. -/
  translationSieve_mem {V : C} (φ ψ : V ⟶ W) : translationSieve act φ ψ ∈ J V
  /-- The action is free, over the objects that the empty sieve does not cover. -/
  eq_one_of_comp_act {V : C} (φ : V ⟶ W) (g : G) (hg : φ ≫ (act g).hom = φ) :
    (⊥ : Sieve V) ∈ J V ∨ g = 1

namespace IsTorsorObject

variable {act : G →* Aut W} {J : GrothendieckTopology C} (h : IsTorsorObject act J)
  (χ : G →* ℤˣ)

include h

/-- **The action on the morphisms into `W` is free**, over an object that the empty sieve does
not cover. -/
theorem injective_comp_act {V : C} (p : V ⟶ W) (hV : (⊥ : Sieve V) ∉ J V) :
    Function.Injective fun g : G => actEnd act V g p := by
  intro g g' hgg
  have hcancel : (act g').hom ≫ (act g'⁻¹).hom = 𝟙 W := by
    rw [← act_hom_mul, inv_mul_cancel, act_hom_one]
  have hgg' : p ≫ (act g).hom = p ≫ (act g').hom := hgg
  have key : p ≫ (act (g'⁻¹ * g)).hom = p := by
    rw [act_hom_mul, ← Category.assoc, hgg', Category.assoc, hcancel, Category.comp_id]
  rcases h.eq_one_of_comp_act p _ key with hbot | hone
  · exact absurd hbot hV
  · exact (inv_mul_eq_one.mp hone).symm

/-- The relations imposed by the character are killed by the weight functional at a morphism
`p : V ⟶ W`, over an object that the empty sieve does not cover. -/
theorem characterRelations_le_ker {V : C} (p : V ⟶ W) (hV : (⊥ : Sieve V) ∉ J V) :
    characterRelations W act χ V ≤
      (FreeAbelianGroup.characterWeightHom (ρ := actEnd act V) (χ := χ) p).ker := by
  rw [characterRelations, AddSubgroup.closure_le]
  rintro x ⟨g, φ, rfl⟩
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_zsmul,
    FreeAbelianGroup.characterWeightHom_of, sub_eq_zero, smul_eq_mul]
  exact FreeAbelianGroup.characterWeight_apply (h.injective_comp_act p hV) g φ

/-- **The coordinate functional of the twist presheaf at a morphism `p : V ⟶ W`**, over an
object that the empty sieve does not cover: the additive map to `ℤ` taking the class of `p` to
`1` and the class of a morphism outside the orbit of `p` to `0`. -/
noncomputable def twistCoordinate {V : C} (p : V ⟶ W) (hV : (⊥ : Sieve V) ∉ J V) :
    (characterTwistPresheaf W act χ).obj (op V) →+ ℤ :=
  QuotientAddGroup.lift (characterRelations W act χ V)
    (FreeAbelianGroup.characterWeightHom (ρ := actEnd act V) (χ := χ) p)
    (h.characterRelations_le_ker χ p hV)

/-- The coordinate functional at `p` takes the value `1` on the class of `p`. -/
@[simp]
theorem twistCoordinate_twistedGenerator_self {V : C} (p : V ⟶ W) (hV : (⊥ : Sieve V) ∉ J V) :
    h.twistCoordinate χ p hV (twistedGenerator W act χ p) = 1 := by
  have h1 := FreeAbelianGroup.characterWeight_of_apply (ρ := actEnd act V) (χ := χ)
    (h.injective_comp_act p hV) 1
  rw [FreeAbelianGroup.apply_one, map_one, Units.val_one] at h1
  exact (FreeAbelianGroup.characterWeightHom_of (ρ := actEnd act V) (χ := χ) p p).trans h1

/-- The class of a morphism `p : V ⟶ W` has infinite order in the twist presheaf, over an object
that the empty sieve does not cover. -/
theorem zsmul_twistedGenerator_injective {V : C} (p : V ⟶ W) (hV : (⊥ : Sieve V) ∉ J V) :
    Function.Injective fun n : ℤ => n • twistedGenerator W act χ p :=
  AddMonoidHom.injective_zsmul_of_eq_one _ (h.twistCoordinate_twistedGenerator_self χ p hV)

/-- **The class of a morphism `p : V ⟶ W` generates a direct summand of the twist presheaf**,
over an object that the empty sieve does not cover: for every abelian group of coefficients `M`
the map `t ↦ t ⊗ [p]` is injective. -/
theorem injective_tmul_twistedGenerator {M : Type*} [AddCommGroup M] {V : C} (p : V ⟶ W)
    (hV : (⊥ : Sieve V) ∉ J V) :
    Function.Injective fun t : M => t ⊗ₜ[ℤ] twistedGenerator W act χ p :=
  AddMonoidHom.injective_tmul_of_eq_one _ (h.twistCoordinate_twistedGenerator_self χ p hV)

/-- A section of the twist presheaf written as a class of an element of the free abelian group
is, locally on an object lying over `W`, an integer multiple of the class of the structure
morphism. -/
private theorem exists_sieve_twistedGenerator_zsmul_mk {V : C} (p : V ⟶ W)
    (z : FreeAbelianGroup (V ⟶ W)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃V' : C⦄ (f : V' ⟶ V), S f →
      ∃ n : ℤ, (characterTwistPresheaf W act χ).map f.op
          (twistProjection act χ V z) =
        n • twistedGenerator W act χ (f ≫ p) := by
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
    refine ⟨⊤, J.top_mem V, fun V' f _ => ⟨0, ?_⟩⟩
    rw [map_zero, map_zero, zero_zsmul]
  | of φ =>
    refine ⟨translationSieve act p φ, h.translationSieve_mem p φ, fun V' f hf => ?_⟩
    obtain ⟨g, hg⟩ := hf
    refine ⟨(χ g : ℤ), ?_⟩
    rw [twistProjection_of, characterTwistPresheaf_map_twistedGenerator,
      show f ≫ φ = (f ≫ p) ≫ (act g).hom by rw [hg, Category.assoc], twistedGenerator_act]
  | neg φ ih =>
    obtain ⟨S, hS, hfam⟩ := ih
    refine ⟨S, hS, fun V' f hf => ?_⟩
    obtain ⟨n, hn⟩ := hfam f hf
    exact ⟨-n, by rw [map_neg, map_neg, hn, neg_zsmul]⟩
  | add z z' hz hz' =>
    obtain ⟨S, hS, hfam⟩ := hz
    obtain ⟨S', hS', hfam'⟩ := hz'
    refine ⟨S ⊓ S', J.intersection_covering hS hS', fun V' f hf => ?_⟩
    obtain ⟨n, hn⟩ := hfam f hf.1
    obtain ⟨n', hn'⟩ := hfam' f hf.2
    exact ⟨n + n', by rw [map_add, map_add, hn, hn', add_zsmul]⟩

/-- **Locally on an object lying over `W`, every section of the twist presheaf is an integer
multiple of the class of the structure morphism.** -/
theorem exists_sieve_twistedGenerator_zsmul {V : C} (p : V ⟶ W)
    (x : (characterTwistPresheaf W act χ).obj (op V)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃V' : C⦄ (f : V' ⟶ V), S f →
      ∃ n : ℤ, (characterTwistPresheaf W act χ).map f.op x =
        n • twistedGenerator W act χ (f ≫ p) := by
  induction x using QuotientAddGroup.induction_on with
  | H z => exact h.exists_sieve_twistedGenerator_zsmul_mk χ p z

end IsTorsorObject

end CategoryTheory

end
