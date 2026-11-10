module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistTorsor
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Over

/-!
# The character twist is locally free of rank one over a torsor

Let `C` be a site, let a group `G` act by automorphisms on an object `W` of `C` which is a
`G`-torsor over the final object, and let `χ : G → ℤˣ` be a character. Seen on the localized
site `Over W`, the twist `ℤ(χ)` is free of rank one: an object `V` of `Over W` comes with a
distinguished morphism `V.hom : V.left ⟶ W`, hence with a distinguished section of the twist
presheaf, namely the class of `V.hom`, and that section is a basis locally on `Over W`.

This file records that freeness as the statement that the comparison morphism from the constant
presheaf with value `ℤ` on `Over W` to the restriction of the twist presheaf is locally
injective and locally surjective, and deduces that the pullback of the sheaf `ℤ(χ)` to the
localized site is the constant sheaf with value `ℤ`.

## Main definitions

* `CategoryTheory.constantToCharacterTwistOver` is the morphism of presheaves on `Over W` from
  the constant presheaf with value `ℤ` to the restriction of the twist presheaf, taking the
  integer `n` over an object `V` to `n` times the class of the structure morphism of `V`.
* `CategoryTheory.characterTwistOverIso` identifies the pullback of `ℤ(χ)` to the localized site
  `Over W` with the constant sheaf with value `ℤ`.

## Main results

* `CategoryTheory.isLocallyInjective_constantToCharacterTwistOver`: the comparison morphism is
  locally injective.
* `CategoryTheory.isLocallySurjective_constantToCharacterTwistOver`: the comparison morphism is
  locally surjective.

## Implementation notes

The identification of the sheaves is obtained by sheafifying the comparison morphism, which
inverts it because the morphism is locally bijective, and then transporting along the
compatibility of sheafification with the restriction of presheaves along `Over.forget W`. That
compatibility is stated for a continuous and cocontinuous functor, so it requires the right Kan
extension along `(Over.forget W).op` to exist pointwise; this is why the limits hypothesis on
`AddCommGrpCat` appears, the indexing categories being of the size of `Over W`.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] {W : C} {G : Type w} [Group G]

/-! ### The comparison morphism on the localized site -/

section Comparison

variable (act : G →* Aut W) (χ : G →* ℤˣ)

/-- The comparison morphism from the constant presheaf with value `ℤ` on the localized site
`Over W` to the restriction of the twist presheaf along `Over.forget W`: over an object `V` of
`Over W` it takes the integer `n` to `n` times the class of the structure morphism of `V`. -/
def constantToCharacterTwistOver :
    (Functor.const (Over W)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) ⟶
      (Over.forget W).op ⋙ characterTwistPresheaf W act χ where
  app X := AddCommGrpCat.ofHom
    { toFun n := n.down • twistedGenerator W act χ X.unop.hom
      map_zero' := zero_zsmul _
      map_add' a b := add_zsmul _ _ _ }
  naturality X Y m := by
    apply AddCommGrpCat.hom_ext
    ext n
    change _ = (characterTwistPresheaf W act χ).map (m.unop.left).op
      ((n : ULift.{v} ℤ).down • twistedGenerator W act χ X.unop.hom)
    rw [map_zsmul, characterTwistPresheaf_map_twistedGenerator, Over.w m.unop]
    rfl

/-- The comparison morphism takes the integer `n` over an object `V` of `Over W` to `n` times
the class of the structure morphism of `V`. -/
@[simp]
lemma constantToCharacterTwistOver_app (V : Over W) (n : ULift.{v} ℤ) :
    (constantToCharacterTwistOver act χ).app (op V) n =
      n.down • twistedGenerator W act χ V.hom :=
  rfl

end Comparison

/-! ### Local bijectivity of the comparison morphism -/

section Torsor

variable {act : G →* Aut W} {J : GrothendieckTopology C}

/-- **The comparison morphism is locally injective** for the topology induced on `Over W`: two
integers with the same multiple of the class of a structure morphism agree locally. -/
theorem isLocallyInjective_constantToCharacterTwistOver (h : IsTorsorObject act J)
    (χ : G →* ℤˣ) :
    Presheaf.IsLocallyInjective (J.over W) (constantToCharacterTwistOver act χ) := by
  constructor
  intro X n m hnm
  by_cases hbot : (⊥ : Sieve X.unop.left) ∈ J X.unop.left
  · refine (J.over W).superset_covering bot_le ?_
    have hmem := J.overEquiv_symm_mem_over X.unop ⊥ hbot
    rwa [show (Sieve.overEquiv X.unop).symm ⊥ = ⊥ by ext V' f; simp] at hmem
  · have heq : n = m :=
      ULift.ext (h.zsmul_twistedGenerator_injective χ X.unop.hom hbot hnm)
    subst heq
    simp

/-- **The comparison morphism is locally surjective** for the topology induced on `Over W`:
locally on an object lying over `W` every section of the twist presheaf is an integer multiple
of the class of the structure morphism. -/
theorem isLocallySurjective_constantToCharacterTwistOver (h : IsTorsorObject act J)
    (χ : G →* ℤˣ) :
    Presheaf.IsLocallySurjective (J.over W) (constantToCharacterTwistOver act χ) := by
  constructor
  intro V x
  obtain ⟨S, hS, hfam⟩ := h.exists_sieve_twistedGenerator_zsmul χ V.hom x
  refine (J.over W).superset_covering ?_ (J.overEquiv_symm_mem_over V S hS)
  intro V' g hg
  obtain ⟨n, hn⟩ := hfam g.left hg
  refine ⟨ULift.up n, ?_⟩
  rw [constantToCharacterTwistOver_app]
  change _ = (characterTwistPresheaf W act χ).map g.left.op x
  rw [hn, Over.w g]

/-! ### The twist is constant on the localized site -/

variable [HasSheafify J AddCommGrpCat.{v}] [HasWeakSheafify (J.over W) AddCommGrpCat.{v}]
  [(J.over W).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [Limits.HasLimitsOfSize.{v, max u v} AddCommGrpCat.{v}]

/-- **The twist `ℤ(χ)` becomes constant on the localized site `Over W`**: its pullback along
`Over.forget W` is the constant sheaf with value `ℤ`. This is the sheaf-theoretic form of the
freeness of rank one of `ℤ(χ)` over a torsor. -/
@[stacks 0727 "the twist is locally free of rank one"]
noncomputable def characterTwistOverIso (h : IsTorsorObject act J) (χ : G →* ℤˣ) :
    (constantSheaf (J.over W) AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) ≅
      (J.overPullback AddCommGrpCat.{v} W).obj (characterTwist W act χ J) := by
  letI := isLocallyInjective_constantToCharacterTwistOver h χ
  letI := isLocallySurjective_constantToCharacterTwistOver h χ
  haveI : IsIso ((presheafToSheaf (J.over W) AddCommGrpCat.{v}).map
      (constantToCharacterTwistOver act χ)) :=
    (GrothendieckTopology.W_iff _ _).mp (GrothendieckTopology.W_of_isLocallyBijective _ _)
  have e : (presheafToSheaf (J.over W) AddCommGrpCat.{v}).obj
        ((Functor.const (Over W)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ))) ≅
      (presheafToSheaf (J.over W) AddCommGrpCat.{v}).obj
        ((Over.forget W).op ⋙ characterTwistPresheaf W act χ) :=
    asIso ((presheafToSheaf (J.over W) AddCommGrpCat.{v}).map
      (constantToCharacterTwistOver act χ))
  exact e ≪≫ ((Over.forget W).pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{v} (J.over W) J).app (characterTwistPresheaf W act χ)

end Torsor

end CategoryTheory

end
