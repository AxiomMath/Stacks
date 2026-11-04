module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Nonempty finite colimits (Stacks 04AW)

Stacks 04AW is the variant of 002Q in which the empty diagram is excluded: a
category has all colimits of *nonempty* finite shapes exactly when it has
coproducts of pairs together with coequalizers, equivalently coproducts of pairs
together with pushouts. Dropping the empty shape is exactly dropping the demand
for an initial object, and that is what makes the statement different from 002Q.

Mathlib has no notion of "nonempty finite colimits" — its `HasFiniteColimits`
quantifies over every finite shape, empty included — so condition (1) is
formalized here as the class `HasNonemptyFiniteColimits`, whose single field
records `HasColimitsOfShape J C` for every small finite nonempty `J`. Conditions
(2) and (3) are Mathlib's `HasBinaryCoproducts`, `HasCoequalizers` and
`HasPushouts`.

The substantial direction is (2) → (1). Mathlib's
`hasColimit_of_coequalizer_and_coproduct` builds a colimit of `F : J ⥤ C` from
coequalizers plus the two coproducts indexed by `J` and by the arrows of `J`;
both index types are finite and, when `J` is nonempty, nonempty. So the work is
to produce coproducts of nonempty finite families from binary coproducts alone,
which is done by induction over `Fin (n + 1)` using Mathlib's `extendCofan` /
`extendCofanIsColimit`. The induction starts at `Fin 1` rather than `Fin 0`,
which is precisely where the initial object would otherwise be needed.

This file is the exact dual of `StacksFrontier.CategoryTheory.Limits.Finite.Nonempty`
(Stacks 04AU) and is kept structurally symmetric with it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C]

/-- `HasNonemptyFiniteColimits C` says that `C` has all colimits of shape `J` for `J` a
small, finite, *nonempty* category; equivalently, every nonempty finite diagram in `C`
has a colimit. Unlike Mathlib's `HasFiniteColimits` this deliberately omits the empty
shape, so it does not require an initial object. -/
@[stacks_fixed 04AW]
class HasNonemptyFiniteColimits : Prop where
  /-- Colimits of every small, finite, nonempty shape exist in `C`. -/
  out : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J], HasColimitsOfShape J C

/-- Nonempty finite colimits give coproducts of pairs: `Discrete WalkingPair` is a
finite nonempty shape. -/
lemma hasBinaryCoproducts_of_hasNonemptyFiniteColimits
    [HasNonemptyFiniteColimits C] : HasBinaryCoproducts C :=
  HasNonemptyFiniteColimits.out (Discrete WalkingPair)

/-- Nonempty finite colimits give coequalizers: `WalkingParallelPair` is a finite
nonempty shape. -/
lemma hasCoequalizers_of_hasNonemptyFiniteColimits
    [HasNonemptyFiniteColimits C] : HasCoequalizers C :=
  HasNonemptyFiniteColimits.out WalkingParallelPair

/-- A discrete diagram over `Fin 1` always has a colimit (given by its unique value).
This is the base case of the induction below, and it needs no hypothesis on `C`. -/
private lemma hasColimit_discrete_fin_one (g : Fin 1 → C) :
    HasColimit (Discrete.functor g) := by
  refine HasColimit.mk ⟨Cofan.mk (g 0) (fun i => eqToHom (by rw [Subsingleton.elim i 0])), ?_⟩
  refine Cofan.IsColimit.mk _ (fun t => t.inj 0) (fun t i => ?_) (fun t m hm => ?_)
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp [Cofan.mk, Cofan.inj]
  · simpa using hm 0

/-- Given binary coproducts, induction on `n` shows every discrete diagram over `Fin (n+1)`
has a colimit, by extending the inductive cofan with a binary cofan via `extendCofan`. -/
private lemma hasColimit_discrete_fin_succ [HasBinaryCoproducts C]
    (n : ℕ) (g : Fin (n + 1) → C) :
    HasColimit (Discrete.functor g) := by
  induction n with
  | zero => exact hasColimit_discrete_fin_one C g
  | succ k ih =>
    let g' : Fin (k + 1) → C := fun i => g i.succ
    let c₁ := colimit.cocone (Discrete.functor g')
    let c₂ : BinaryCofan (g 0) c₁.pt := colimit.cocone (pair (g 0) c₁.pt)
    exact HasColimit.mk ⟨extendCofan c₁ c₂,
      extendCofanIsColimit g (colimit.isColimit _) (colimit.isColimit _)⟩

/-- Transport existence of a colimit of a discrete diagram along an equivalence of index types. -/
private lemma hasColimit_discrete_transport
    {I J : Type} (e : I ≃ J) (f : I → C)
    (h : HasColimit (Discrete.functor (f ∘ e.symm))) :
    HasColimit (Discrete.functor f) := by
  let eq : Discrete I ≌ Discrete J := Discrete.equivalence e
  have : HasColimit (eq.functor ⋙ Discrete.functor (f ∘ ⇑e.symm)) :=
    hasColimit_equivalence_comp eq
  have iso : eq.functor ⋙ Discrete.functor (f ∘ ⇑e.symm) ≅ Discrete.functor f :=
    Discrete.natIso fun i => eqToIso (show (f ∘ ⇑e.symm) (e i.as) = f i.as by simp)
  exact hasColimit_of_iso iso.symm

/-- Discrete diagrams over a finite nonempty type have colimits, assuming binary coproducts. -/
private lemma hasColimit_discrete_of_finite_nonempty
    [HasBinaryCoproducts C] (I : Type) [Finite I] [Nonempty I] (f : I → C) :
    HasColimit (Discrete.functor f) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  match n, e with
  | 0, e => exact (e (Classical.arbitrary I)).elim0
  | n + 1, e =>
    exact hasColimit_discrete_transport C e f
      (hasColimit_discrete_fin_succ C n (f ∘ e.symm))

/-- From coproducts of pairs and coequalizers one obtains all nonempty finite colimits:
`hasColimit_of_coequalizer_and_coproduct` needs the coproducts indexed by the objects and
by the arrows of the shape, and both of those index types are finite and nonempty. -/
lemma hasNonemptyFiniteColimits_of_hasBinaryCoproducts_and_hasCoequalizers
    [HasBinaryCoproducts C] [HasCoequalizers C] : HasNonemptyFiniteColimits C := by
  refine ⟨fun J _ _ _ => ⟨fun F => ?_⟩⟩
  have : Nonempty (Σ p : J × J, p.1 ⟶ p.2) :=
    ⟨⟨⟨Classical.arbitrary J, Classical.arbitrary J⟩, 𝟙 _⟩⟩
  have : HasColimit (Discrete.functor F.obj) :=
    hasColimit_discrete_of_finite_nonempty C J F.obj
  have : HasColimit (Discrete.functor (fun g : Σ p : J × J, p.1 ⟶ p.2 => F.obj g.fst.1)) :=
    hasColimit_discrete_of_finite_nonempty C _ _
  exact hasColimit_of_coequalizer_and_coproduct F

/-- **Stacks 04AW.** For a category `C` the following are equivalent:
1. nonempty finite colimits exist in `C`;
2. coproducts of pairs and coequalizers exist in `C`;
3. coproducts of pairs and pushouts exist in `C`. -/
@[stacks 04AW]
theorem hasNonemptyFiniteColimits_tfae :
    List.TFAE
      [ HasNonemptyFiniteColimits C
      , HasBinaryCoproducts C ∧ HasCoequalizers C
      , HasBinaryCoproducts C ∧ HasPushouts C ] := by
  tfae_have 1 → 2 := fun _ =>
    ⟨hasBinaryCoproducts_of_hasNonemptyFiniteColimits C,
      hasCoequalizers_of_hasNonemptyFiniteColimits C⟩
  tfae_have 2 → 1 := fun ⟨_, _⟩ =>
    hasNonemptyFiniteColimits_of_hasBinaryCoproducts_and_hasCoequalizers C
  tfae_have 2 → 3 := fun ⟨_, _⟩ =>
    ⟨inferInstance, hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers C⟩
  tfae_have 3 → 2 := fun ⟨_, _⟩ =>
    ⟨inferInstance, hasCoequalizers_of_hasPushouts_and_binary_coproducts⟩
  tfae_finish

end CategoryTheory.Limits
