module

public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 00AI — pushforward along a closed immersion is not right exact

Let `i : Z → X` be the inclusion of a closed subset and let `x ∈ X` be a point outside `Z`.
For every sheaf of sets `F` on `Z` the stalk `(i_*F)_x` is a singleton — a terminal object of
`Type` — which is `ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange`, that is,
Stacks 00AE.

Applying this to `F = * ⨿ *` shows that `i_*` does not preserve binary coproducts: the stalk of
`i_*(* ⨿ *)` at `x` is a one-point set, while the stalk of `i_** ⨿ i_**` at `x` is a two-point set,
because taking stalks of sheaves is a left adjoint (Mathlib's `stalkSkyscraperSheafAdjunction`) and
so commutes with coproducts. This is what Stacks 00AI means by `i_*` being *not right exact*, and
it rules out a right adjoint for `i_*`.

Only the existence of a point of `X` off `Z` is used, so the hypotheses are exactly those of the
tag: `i` is a closed embedding and some `x ∈ X` is not in the image of `i`. The sheaf `F` may be
taken to be any sheaf on `Z` whatsoever, since Stacks 00AE applies to all of them; the statements
below use the final sheaf, as the tag does.

## Main results

* `ClosedImmersionSheaves.isEmpty_isTerminal_coprod_self`: in `Type u`, the coproduct `A ⨿ A` of a
  terminal object with itself is not terminal (the two coprojections would coincide).
* `ClosedImmersionSheaves.not_preservesColimitsOfShape_sheafPushforward`: `i_*` does not preserve
  binary coproducts of sheaves of sets.
* `ClosedImmersionSheaves.not_isLeftAdjoint_sheafPushforward`: `i_*` has no right adjoint.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open TopCat
open scoped AlgebraicGeometry

universe u

namespace ClosedImmersionSheaves

open TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Sheaf TopCat.Presheaf.stalk
  TopCat.Presheaf.stalkFunctor

/-- **A two-point set is not a one-point set.** If `A` is a terminal object of `Type u` then the
coproduct `A ⨿ A` is not terminal: terminality of `A ⨿ A` would force the two coprojections
`A ⟶ A ⨿ A` to be equal, hence — descending along them the two injections `A → A ⊕ A` — would
identify `Sum.inl a` with `Sum.inr a`. -/
theorem isEmpty_isTerminal_coprod_self {A : Type u} (hA : IsTerminal A) :
    IsEmpty (IsTerminal (A ⨿ A)) := by
  refine ⟨fun hAA => ?_⟩
  have hinl : (coprod.inl : A ⟶ A ⨿ A) = coprod.inr := hAA.hom_ext _ _
  have h : TypeCat.ofHom (Sum.inl : A → A ⊕ A) = TypeCat.ofHom (Sum.inr : A → A ⊕ A) := by
    rw [← coprod.inl_desc (X := A) (Y := A) (TypeCat.ofHom (Sum.inl : A → A ⊕ A))
      (TypeCat.ofHom (Sum.inr : A → A ⊕ A)), hinl, coprod.inr_desc]
  have h2 := congrArg (fun φ : A ⟶ A ⊕ A => φ (hA.from PUnit PUnit.unit)) h
  simp at h2

variable {X Z : TopCat.{u}} (i : Z ⟶ X)

/-- **Stacks 00AI, first half.** For `i : Z ⟶ X` a closed embedding and `x ∈ X` outside the image
of `i`, the pushforward `i_* : Sh(Z, Type) ⥤ Sh(X, Type)` does not preserve binary coproducts, i.e.
it is not right exact.

Take `F` to be the final sheaf `*` on `Z`. Stacks 00AE makes the stalk at `x` of `i_*G` terminal
for *every* sheaf `G` on `Z`, in particular for `G = F` and for `G = F ⨿ F`. Taking stalks of
sheaves is a left adjoint, so it preserves the coproduct; if `i_*` preserved it too, the terminal
set `(i_*(F ⨿ F))_x` would be the coproduct of the terminal set `(i_*F)_x` with itself, which
`isEmpty_isTerminal_coprod_self` forbids. -/
@[stacks 00AI "i_* is not right exact as a functor between categories of sheaves of sets",
  sga "4 IV 3.1.2" "u_* not right exact"]
theorem not_preservesColimitsOfShape_sheafPushforward
    (hi : IsClosedEmbedding (ConcreteCategory.hom i)) (x : X)
    (hx : x ∉ Set.range (ConcreteCategory.hom i)) :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair) (Sheaf.pushforward (Type u) i) := by
  intro hpre
  let : HasBinaryCoproducts (Z.Sheaf (Type u)) :=
    inferInstanceAs (HasBinaryCoproducts
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) (Type u)))
  let : HasBinaryCoproducts (X.Sheaf (Type u)) :=
    inferInstanceAs (HasBinaryCoproducts
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)))
  set F : Z.Sheaf (Type u) := ⊤_ (Z.Sheaf (Type u))
  have hterm : ∀ G : Z.Sheaf (Type u),
      IsTerminal ((Sheaf.forget (Type u) X ⋙ Presheaf.stalkFunctor (Type u) x).obj
        ((Sheaf.pushforward (Type u) i).obj G)) :=
    fun G => isTerminalStalkPushforwardOfNotMemRange i G.property hi x hx
  have e : (Sheaf.forget (Type u) X ⋙ Presheaf.stalkFunctor (Type u) x).obj
        ((Sheaf.pushforward (Type u) i).obj F) ⨿
      (Sheaf.forget (Type u) X ⋙ Presheaf.stalkFunctor (Type u) x).obj
        ((Sheaf.pushforward (Type u) i).obj F) ≅
      (Sheaf.forget (Type u) X ⋙ Presheaf.stalkFunctor (Type u) x).obj
        ((Sheaf.pushforward (Type u) i).obj (F ⨿ F)) :=
    PreservesColimitPair.iso (Sheaf.forget (Type u) X ⋙ Presheaf.stalkFunctor (Type u) x)
        ((Sheaf.pushforward (Type u) i).obj F) ((Sheaf.pushforward (Type u) i).obj F) ≪≫
      (Sheaf.forget (Type u) X ⋙ Presheaf.stalkFunctor (Type u) x).mapIso
        (PreservesColimitPair.iso (Sheaf.pushforward (Type u) i) F F)
  exact (isEmpty_isTerminal_coprod_self (hterm F)).false
    (IsTerminal.ofIso (hterm (F ⨿ F)) e.symm)

/-- **Stacks 00AI, second half.** For `i : Z ⟶ X` a closed embedding and `x ∈ X` outside the image
of `i`, the pushforward `i_* : Sh(Z, Type) ⥤ Sh(X, Type)` has no right adjoint: a functor with a
right adjoint preserves all colimits, and `i_*` does not preserve binary coproducts. -/
@[stacks 00AI "in particular i_* cannot have a right adjoint"]
theorem not_isLeftAdjoint_sheafPushforward
    (hi : IsClosedEmbedding (ConcreteCategory.hom i)) (x : X)
    (hx : x ∉ Set.range (ConcreteCategory.hom i)) :
    ¬ (Sheaf.pushforward (Type u) i).IsLeftAdjoint := by
  intro h
  exact not_preservesColimitsOfShape_sheafPushforward i hi x hx inferInstance

end ClosedImmersionSheaves
