module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# The sheaf of sets supported on the objects covered by the empty sieve

On any site `(C, J)` the assignment sending an object `U` to a one-element set when the empty
sieve covers `U`, and to the empty set otherwise, is a sheaf of sets. It is the initial object
of the category of sheaves of sets, and it is initial with no size relation between the site
and the values of the sheaf: it is built directly out of the covering condition, so neither
sheafification nor a colimit is involved.

## Main definitions

* `CategoryTheory.emptySheaf`: the sheaf of sets with a section over exactly the objects
  covered by the empty sieve.
* `CategoryTheory.emptySheafIsInitial`: it is an initial object.

## Main results

* `CategoryTheory.hasInitialSheafOfTypes`: sheaves of sets on any site have an initial object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory

section EmptySheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The sheaf of sets with a section over exactly the objects covered by the empty sieve. -/
public def emptySheaf : Sheaf J (Type w) where
  obj :=
    { obj := fun U => ULift.{w} (PLift ((⊥ : Sieve U.unop) ∈ J U.unop))
      map := fun f => ↾fun h => ⟨⟨by
        simpa using J.pullback_stable f.unop h.down.down⟩⟩ }
  property := by
    rw [isSheaf_iff_isSheaf_of_type]
    intro U S hS x hx
    refine ⟨⟨⟨J.transitive hS ⊥ ?_⟩⟩, ?_, ?_⟩
    · intro V f hf
      simpa using (x f hf).down.down
    · intro V f hf
      exact Subsingleton.elim _ _
    · intro y hy
      exact Subsingleton.elim _ _

/-- The empty sheaf is an initial object of the category of sheaves of sets. -/
public noncomputable def emptySheafIsInitial : IsInitial (emptySheaf.{u, v, w} J) := by
  classical
  let h (F : Sheaf J (Type w)) (U : C) (e : (⊥ : Sieve U) ∈ J U) :
      Unique (F.obj.obj (op U)) :=
    Types.isTerminalEquivUnique _ (F.isTerminalOfBotCover U e)
  refine IsInitial.ofUniqueHom (fun F => (⟨{
    app := fun U => ↾fun x => (h F U.unop x.down.down).default
    naturality := ?_ }⟩ : emptySheaf J ⟶ F)) ?_
  · rename_i F
    intro U V f
    ext x
    let := h F V.unop ((emptySheaf J).obj.map f x).down.down
    exact Subsingleton.elim _ _
  · intro F f
    ext U x
    let := h F U.unop x.down.down
    exact Subsingleton.elim _ _

/-- Sheaves of sets on any site have an initial object, with no size relation between the site
and the values. -/
theorem hasInitialSheafOfTypes : HasInitial (Sheaf J (Type w)) :=
  (emptySheafIsInitial J).hasInitial

end EmptySheaf

end CategoryTheory
