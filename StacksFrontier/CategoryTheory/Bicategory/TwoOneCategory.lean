module

public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import StacksCore.Tactic.StacksAttribute

/-!
# `(2,1)`-categories and their final objects

A *(strict) `(2,1)`-category* is a strict bicategory all of whose `2`-morphisms are isomorphisms.
A *final object* of a `(2,1)`-category is an object `T` such that every object admits a
`1`-morphism to `T`, and any two such are isomorphic by a unique `2`-morphism.

## Main definitions

* `CategoryTheory.Bicategory.IsTwoOneCategory`: a strict, locally groupoidal bicategory.
* `CategoryTheory.Bicategory.IsBiterminal`: every hom-category `X ⟶ T` has a terminal object.
* `CategoryTheory.Bicategory.IsStrictBiterminal`: every hom-category `X ⟶ T` is trivial.
* `CategoryTheory.Bicategory.IsBiterminal.isoOfHoms`: the `2`-isomorphism between two
  `1`-morphisms into a bi-terminal object.
* `CategoryTheory.Bicategory.isTerminal_of_isBiterminal`: a bi-terminal object of a locally
  discrete bicategory is terminal.
* `CategoryTheory.Bicategory.InducedBicategory.homGroupoid`: a hom-category of a full
  sub-`2`-category is a groupoid when the corresponding ambient hom-category is.

## Main results

* `CategoryTheory.Bicategory.IsStrictBiterminal.isBiterminal`: a strict bi-terminal object is
  bi-terminal.
* `CategoryTheory.Bicategory.isBiterminal_iff`: in a locally groupoidal bicategory, `T` is
  bi-terminal exactly when it is a final object in the sense above.
* `CategoryTheory.Bicategory.isTwoOneCategory_locallyDiscrete`: a locally discrete bicategory is
  a `(2,1)`-category.
* `CategoryTheory.Bicategory.isBiterminal_iff_isTerminal`: on a locally discrete bicategory,
  bi-terminality is terminality.

## References

* [Stacks Project, Tag 003I](https://stacks.math.columbia.edu/tag/003I)
* [Stacks Project, Tag 003P](https://stacks.math.columbia.edu/tag/003P)
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory

open CategoryTheory Limits

/-- A *(strict) `(2,1)`-category* is a `2`-category — that is, a strict bicategory — in which
every `2`-morphism is an isomorphism, the latter spelled as Mathlib's
`Bicategory.IsLocallyGroupoid`, i.e. each hom-category `a ⟶ b` is a groupoid. -/
@[stacks 003I]
def IsTwoOneCategory (B : Type u) [Bicategory.{w, v} B] : Prop :=
  Bicategory.Strict B ∧ IsLocallyGroupoid B

variable {B : Type u} [Bicategory.{w, v} B]

/-- A *final object* of a `(2,1)`-category `B`, defined as an object `T` such that every
hom-category `X ⟶ T` has a terminal object. In a locally groupoidal `B` this says that every
object admits a `1`-morphism to `T`, and any two such are isomorphic by a unique `2`-morphism
(`CategoryTheory.Bicategory.isBiterminal_iff`). -/
@[stacks 003P]
def IsBiterminal (T : B) : Prop := ∀ X : B, HasTerminal (X ⟶ T)

/-- Terminality on the nose: every hom-category `X ⟶ T` is trivial, that is, there is a unique
`1`-morphism into `T` and its only `2`-endomorphism is the identity. So the hom-category is
isomorphic, not merely equivalent, to the terminal category. -/
def IsStrictBiterminal (T : B) : Prop :=
  ∀ X : B, Nonempty (X ⟶ T) ∧ Subsingleton (X ⟶ T) ∧ ∀ f g : X ⟶ T, Subsingleton (f ⟶ g)

section Biterminal

variable {T : B}

/-- A category with an object `t` equal to every object and subsingleton hom-sets has a terminal
object. -/
private lemma hasTerminal_of_forall_eq {D : Type*} [Category D] (t : D) (h : ∀ f, f = t)
    (hs : ∀ f g : D, Subsingleton (f ⟶ g)) : HasTerminal D :=
  (IsTerminal.ofUniqueHom (fun f => eqToHom (h f)) fun _ _ => (hs _ _).elim _ _).hasTerminal

/-- A strict bi-terminal object is bi-terminal. -/
lemma IsStrictBiterminal.isBiterminal (hT : IsStrictBiterminal T) : IsBiterminal T := fun X =>
  have ⟨⟨t⟩, _, hs⟩ := hT X
  hasTerminal_of_forall_eq t (Subsingleton.elim · t) hs

/-- In a locally groupoidal bicategory, `T` is bi-terminal exactly when every object admits a
`1`-morphism to `T` and any two such are isomorphic by a unique `2`-morphism. -/
lemma isBiterminal_iff [IsLocallyGroupoid B] :
    IsBiterminal T ↔
      (∀ Y : B, Nonempty (Y ⟶ T)) ∧
        ∀ (Y : B) (f g : Y ⟶ T), ∃! η : f ⟶ g, IsIso η := by
  refine ⟨fun h => ⟨fun Y => have := h Y; ⟨⊤_ _⟩, fun Y f g => have := h Y; ?_⟩,
    fun ⟨hne, huniq⟩ Y => ?_⟩
  · exact ⟨terminal.from f ≫ inv (terminal.from g), inferInstance,
      fun η _ => (IsIso.eq_comp_inv _).2 (terminal.hom_ext _ _)⟩
  · choose η _ hη using huniq Y
    exact (IsTerminal.ofUniqueHom (η · (hne Y).some)
      fun f m => hη f _ m inferInstance).hasTerminal

/-- Any two `1`-morphisms into a bi-terminal object are `2`-isomorphic. -/
noncomputable def IsBiterminal.isoOfHoms [IsLocallyGroupoid B] (hT : IsBiterminal T) {Y : B}
    (f g : Y ⟶ T) : f ≅ g :=
  haveI := hT Y
  asIso (terminal.from f ≫ inv (terminal.from g))

end Biterminal

section LocallyDiscrete

variable {C : Type u} [Category.{v} C]

/-- A locally discrete bicategory is a `(2,1)`-category. -/
lemma isTwoOneCategory_locallyDiscrete : IsTwoOneCategory (LocallyDiscrete C) :=
  ⟨inferInstance, fun a b => inferInstanceAs (IsGroupoid (Discrete (a.as ⟶ b.as)))⟩

/-- A terminal object of `C` is bi-terminal in the locally discrete bicategory on `C`. -/
lemma isBiterminal_of_isTerminal {x : C} (hx : IsTerminal x) :
    IsBiterminal (⟨x⟩ : LocallyDiscrete C) := fun y =>
  hasTerminal_of_forall_eq (⟨hx.from y.as⟩ : y ⟶ (⟨x⟩ : LocallyDiscrete C))
    (fun f => Discrete.ext (hx.hom_ext f.as _)) fun _ _ => inferInstance

/-- A bi-terminal object of the locally discrete bicategory on `C` is terminal in `C`. -/
noncomputable def isTerminal_of_isBiterminal {x : C}
    (hx : IsBiterminal (⟨x⟩ : LocallyDiscrete C)) : IsTerminal x :=
  IsTerminal.ofUniqueHom
    (fun y => haveI := hx ⟨y⟩; (⊤_ ((⟨y⟩ : LocallyDiscrete C) ⟶ ⟨x⟩)).as)
    (fun y m => haveI := hx ⟨y⟩
      congrArg Discrete.as
        (LocallyDiscrete.eq_of_hom (terminal.from (⟨m⟩ : (⟨y⟩ : LocallyDiscrete C) ⟶ ⟨x⟩))))

/-- On a locally discrete bicategory, bi-terminality and Mathlib's `IsTerminal` agree. -/
lemma isBiterminal_iff_isTerminal {x : C} :
    IsBiterminal (⟨x⟩ : LocallyDiscrete C) ↔ Nonempty (IsTerminal x) :=
  ⟨fun hx => ⟨isTerminal_of_isBiterminal hx⟩, fun ⟨hx⟩ => isBiterminal_of_isTerminal hx⟩

end LocallyDiscrete

section Induced

variable {C : Type u} [Bicategory.{w, v} C] {A : Type*} {F : A → C}

/-- A hom-category of a full sub-`2`-category `CategoryTheory.Bicategory.InducedBicategory C F`
is a groupoid as soon as the corresponding hom-category of `C` is. In particular a full
sub-`2`-category of a `(2,1)`-category is a `(2,1)`-category. -/
instance InducedBicategory.homGroupoid (X Y : InducedBicategory C F)
    [IsGroupoid (F X ⟶ F Y)] : IsGroupoid (X ⟶ Y) where
  all_isIso {_f _g} η :=
    have h : (InducedBicategory.isoMk (asIso η.hom)).hom = η := InducedBicategory.hom₂_ext rfl
    h ▸ (inferInstance : IsIso (InducedBicategory.isoMk (asIso η.hom)).hom)

end Induced

end CategoryTheory.Bicategory
