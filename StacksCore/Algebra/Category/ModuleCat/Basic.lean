module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!

# Main Results

* `Equivalence.nontrivialModuleTransfer`: If `M` is a nontrivial module over a ring `R`,
  and `e : ModuleCat R ≌ ModuleCat S` is an equivalence of module categories,
  then `e.functor.obj M` is a nontrivial module over `S`.

-/

@[expose] public section

universe u v

variable {R : Type u} [Ring R]

instance CategoryTheory.Equivalence.nontrivialModuleTransfer {R S : Type*} [Ring R] [Ring S]
    (e : ModuleCat R ≌ ModuleCat S) (M : ModuleCat R) [h : Nontrivial M] :
    Nontrivial (e.functor.obj M) := by
  by_contra! inst1
  have hM : Limits.IsZero M := Functor.id_obj M ▸ CategoryTheory.Iso.isZero_iff
    (e.unitIso.app M)|>.2 <| Functor.map_isZero e.inverse <| ModuleCat.isZero_of_subsingleton <|
    e.functor.obj M
  exact (@not_nontrivial M <| ModuleCat.subsingleton_of_isZero hM) h
