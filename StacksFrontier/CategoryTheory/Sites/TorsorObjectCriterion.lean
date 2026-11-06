module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.SingleObj
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistTorsor

/-!
# Criteria producing a torsor over the final object of a site

`CategoryTheory.IsTorsorObject act J` asks three things of an action of a group `G` by
automorphisms on an object `W` of a site: the morphisms into `W` cover every object, two
morphisms into `W` are translates of each other locally on their source, and the translating
group element is unique except over the objects covered by the empty sieve.

This file reduces each of the three to an input of the shape geometry produces, and exhibits an
inhabitant.

The middle condition is the one that is not a reformulation. It is produced here from a
*kernel-pair presentation*: an object `R` with two morphisms to `W` exhibiting it as the fibre
product of `W` with itself over an object admitting at most one morphism from anywhere, together
with a morphism `W ⟶ R` for each group element, the first splitting the first projection and the
second realizing the automorphism of that element, and the requirement that every morphism into
`R` factors through one of those copies of `W` locally on its source. That requirement is where
the content sits: it says `R` is the disjoint union of `G` copies of `W` as seen by the
topology, not on the nose.

## Main definitions

* `CategoryTheory.summandSieve` is the sieve of arrows along which a morphism into `R` factors
  through one of the `G`-indexed morphisms `W ⟶ R`.
* `CategoryTheory.singleObjAut` is the action of a group on the single object of its one-object
  groupoid by its own translations.

## Main results

* `CategoryTheory.splittingSieve_mem_of_le`, `CategoryTheory.translationSieve_mem_of_isPullback`
  and `CategoryTheory.eq_one_of_comp_act_of_free_on` produce the three conditions one at a time,
  and `CategoryTheory.isTorsorObject_of_isPullback` assembles them.
* `CategoryTheory.isTorsorObject_of_simplyTransitive`: an action which is transitive and free on
  the morphisms into `W` globally, with those morphisms never absent, is a torsor over the final
  object for *every* topology.
* `CategoryTheory.isTorsorObject_singleObjAut`: **a group is a torsor over itself.** The single
  object of the one-object groupoid of `G`, acted on by `G` through its own translations,
  satisfies the three conditions for every topology on that groupoid.

## Implementation notes

`CategoryTheory.isTorsorObject_singleObjAut` holds for an arbitrary group `G`, and
`CategoryTheory.bot_notMem_trivial` says the empty sieve covers nothing in the trivial topology,
so taking that topology there leaves the third condition as freeness of the action on the
morphisms into `W` outright, with no escape. The two together are therefore a witness that the
three conditions are jointly satisfiable without forcing `G` to be trivial, which the escape
clause of `CategoryTheory.IsTorsorObject.eq_one_of_comp_act` makes a real question.

The subterminality hypothesis of `CategoryTheory.translationSieve_mem_of_isPullback` is stated
as uniqueness of the morphisms into the base of the kernel pair rather than as
`CategoryTheory.Limits.IsTerminal`, because the sites that arise as the small site of a quotient
have their final object only up to isomorphism and the weaker form is what the proof uses: it
serves only to produce the morphism into `R` out of a pair of morphisms into `W`.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {W : C} {G : Type w} [Group G]

/-! ### The three conditions one at a time -/

section Fields

variable {act : G →* Aut W} {J : GrothendieckTopology C}

/-- The morphisms into `W` cover an object as soon as some covering sieve of it has all of its
sources admitting a morphism to `W`. -/
theorem splittingSieve_mem_of_le {V : C} {S : Sieve V} (hS : S ∈ J V)
    (hfam : ∀ ⦃V' : C⦄ (f : V' ⟶ V), S f → Nonempty (V' ⟶ W)) :
    splittingSieve W V ∈ J V := by
  refine J.superset_covering ?_ hS
  intro V' f hf
  exact hfam f hf

/-- The sieve on `V` consisting of the arrows `f` along which a morphism `d : V ⟶ R` factors
through one of the morphisms `ι g : W ⟶ R`. -/
def summandSieve {R : C} (ι : G → (W ⟶ R)) {V : C} (d : V ⟶ R) : Sieve V where
  arrows Y f := ∃ (g : G) (e : Y ⟶ W), f ≫ d = e ≫ ι g
  downward_closed := by
    rintro Y Z f ⟨g, e, he⟩ k
    exact ⟨g, k ≫ e, by rw [Category.assoc, he, Category.assoc]⟩

/-- **Two morphisms into `W` are translates of each other locally on their source** as soon as
`W` has a kernel pair over an object receiving at most one morphism from anywhere, the kernel
pair receives one copy of `W` for each group element, splitting the first projection and
realizing the automorphism of that element on the second, and every morphism into the kernel
pair factors through one of those copies locally on its source.

The last condition is the disjointness of the copies as the topology sees it; the first three
are formal. -/
theorem translationSieve_mem_of_isPullback {T R : C} {w : W ⟶ T} {p₁ p₂ : R ⟶ W}
    (hT : ∀ (V : C) (f f' : V ⟶ T), f = f') (hpb : IsPullback p₁ p₂ w w) (ι : G → (W ⟶ R))
    (hι₁ : ∀ g : G, ι g ≫ p₁ = 𝟙 W) (hι₂ : ∀ g : G, ι g ≫ p₂ = (act g).asIso.hom)
    (hcov : ∀ ⦃V : C⦄ (d : V ⟶ R), summandSieve ι d ∈ J V) {V : C} (φ ψ : V ⟶ W) :
    translationSieve act φ ψ ∈ J V := by
  have hw : φ ≫ w = ψ ≫ w := hT V _ _
  have hfst : hpb.lift φ ψ hw ≫ p₁ = φ := hpb.lift_fst _ _ _
  have hsnd : hpb.lift φ ψ hw ≫ p₂ = ψ := hpb.lift_snd _ _ _
  refine J.superset_covering ?_ (hcov (hpb.lift φ ψ hw))
  rintro V' f ⟨g, e, he⟩
  have key : ∀ (x : V ⟶ W) (q : R ⟶ W), hpb.lift φ ψ hw ≫ q = x → f ≫ x = e ≫ ι g ≫ q := by
    intro x q h
    rw [← h, ← Category.assoc, he, Category.assoc]
  have h₁ := key φ p₁ hfst
  have h₂ := key ψ p₂ hsnd
  rw [hι₁, Category.comp_id] at h₁
  rw [hι₂] at h₂
  exact ⟨g, by rw [h₂, ← h₁, Category.assoc]⟩

/-- **The translating group element is unique** as soon as the action is free on the morphisms
into `W` out of the objects of some class which reaches every object that the empty sieve does
not cover. -/
theorem eq_one_of_comp_act_of_free_on {P : C → Prop}
    (hfree : ∀ ⦃V' : C⦄, P V' → ∀ (φ : V' ⟶ W) (g : G), φ ≫ (act g).asIso.hom = φ → g = 1) {V : C}
    (hV : (⊥ : Sieve V) ∉ J V → ∃ V' : C, P V' ∧ Nonempty (V' ⟶ V)) (φ : V ⟶ W) (g : G)
    (hg : φ ≫ (act g).asIso.hom = φ) :
    (⊥ : Sieve V) ∈ J V ∨ g = 1 := by
  by_cases hbot : (⊥ : Sieve V) ∈ J V
  · exact Or.inl hbot
  obtain ⟨V', hP, ⟨f⟩⟩ := hV hbot
  exact Or.inr (hfree hP (f ≫ φ) g (by rw [Category.assoc, hg]))

end Fields

/-! ### The two producers -/

/-- **A kernel-pair presentation of `W` produces a torsor over the final object.** The three
hypotheses beyond the kernel pair itself are the three conditions as geometry supplies them: a
covering of each object by objects mapping to `W`, the local disjointness of the `G` copies of
`W` in the kernel pair, and freeness of the action against a class of test objects reaching
every object the empty sieve does not cover. -/
theorem isTorsorObject_of_isPullback {act : G →* Aut W} {J : GrothendieckTopology C} {T R : C}
    {w : W ⟶ T} {p₁ p₂ : R ⟶ W} {P : C → Prop} (hT : ∀ (V : C) (f f' : V ⟶ T), f = f')
    (hpb : IsPullback p₁ p₂ w w) (ι : G → (W ⟶ R)) (hι₁ : ∀ g : G, ι g ≫ p₁ = 𝟙 W)
    (hι₂ : ∀ g : G, ι g ≫ p₂ = (act g).asIso.hom)
    (hcov : ∀ ⦃V : C⦄ (d : V ⟶ R), summandSieve ι d ∈ J V)
    (hsplit : ∀ V : C, splittingSieve W V ∈ J V)
    (hfree : ∀ ⦃V' : C⦄, P V' → ∀ (φ : V' ⟶ W) (g : G), φ ≫ (act g).asIso.hom = φ → g = 1)
    (htest : ∀ V : C, (⊥ : Sieve V) ∉ J V → ∃ V' : C, P V' ∧ Nonempty (V' ⟶ V)) :
    IsTorsorObject act J where
  splittingSieve_mem := hsplit
  translationSieve_mem := translationSieve_mem_of_isPullback hT hpb ι hι₁ hι₂ hcov
  eq_one_of_comp_act {V} φ g hg := eq_one_of_comp_act_of_free_on hfree (htest V) φ g hg

/-- **An action which is transitive and free on the morphisms into `W` globally makes `W` a
torsor over the final object, for every topology.** Both of the sieves asked to be covering are
then the maximal sieve. -/
theorem isTorsorObject_of_simplyTransitive {act : G →* Aut W} (J : GrothendieckTopology C)
    (hsplit : ∀ V : C, Nonempty (V ⟶ W))
    (htrans : ∀ {V : C} (φ ψ : V ⟶ W), ∃ g : G, ψ = φ ≫ (act g).asIso.hom)
    (hfree : ∀ {V : C} (φ : V ⟶ W) (g : G), φ ≫ (act g).asIso.hom = φ → g = 1) :
    IsTorsorObject act J where
  splittingSieve_mem V := splittingSieve_mem_of_le (J.top_mem V) fun V' _ _ => hsplit V'
  translationSieve_mem {V} φ ψ := by
    refine J.superset_covering ?_ (J.top_mem V)
    intro V' f _
    obtain ⟨g, hg⟩ := htrans φ ψ
    exact ⟨g, by rw [hg]⟩
  eq_one_of_comp_act φ g hg := Or.inr (hfree φ g hg)

/-! ### A group is a torsor over itself -/

/-- The empty sieve is not covering for the trivial topology: the only covering sieve there is
the maximal one, which contains the identity. -/
theorem bot_notMem_trivial (X : C) : (⊥ : Sieve X) ∉ GrothendieckTopology.trivial C X := by
  intro hbot
  rw [GrothendieckTopology.trivial_covering] at hbot
  have hid : (⊥ : Sieve X).arrows (𝟙 X) := by rw [hbot]; trivial
  exact hid

/-- The action of a group on the single object of its one-object groupoid by its own
translations: the automorphism attached to `g` is `g` itself. -/
def singleObjAut (G : Type w) [Group G] : G →* Aut (SingleObj.star G) where
  toFun g :=
    .of { hom := g
          inv := g⁻¹
          hom_inv_id := by rw [SingleObj.comp_as_mul, inv_mul_cancel, SingleObj.id_as_one]
          inv_hom_id := by rw [SingleObj.comp_as_mul, mul_inv_cancel, SingleObj.id_as_one] }
  map_one' := Aut.ext (Iso.ext rfl)
  map_mul' _ _ := Aut.ext (Iso.ext rfl)

/-- The underlying morphism of the automorphism `singleObjAut G g` is `g`. -/
@[simp]
theorem singleObjAut_hom (g : G) : (singleObjAut G g).asIso.hom = g := rfl

/-- **A group is a torsor over itself.** The single object of the one-object groupoid of `G`,
acted on by `G` through its own translations, satisfies the three conditions of
`CategoryTheory.IsTorsorObject` for every topology on that groupoid: the morphisms into it are
the elements of `G`, which are never absent, and on which `G` acts transitively and freely. -/
theorem isTorsorObject_singleObjAut (J : GrothendieckTopology (SingleObj G)) :
    IsTorsorObject (singleObjAut G) J :=
  isTorsorObject_of_simplyTransitive J (fun _ => ⟨1⟩)
    (fun φ ψ => ⟨ψ * φ⁻¹, by
      rw [SingleObj.comp_as_mul, singleObjAut_hom, inv_mul_cancel_right]⟩)
    (fun φ g hg => by
      rw [SingleObj.comp_as_mul, singleObjAut_hom] at hg
      exact mul_right_cancel (hg.trans (one_mul φ).symm))

end CategoryTheory

end
