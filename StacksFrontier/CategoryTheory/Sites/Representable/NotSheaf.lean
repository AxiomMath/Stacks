module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# A representable presheaf need not be a sheaf

On a site whose topology lets the empty sieve cover an object `U`, the sheaf condition for the
empty sieve forces every sheaf of sets to have a section over `U`. A representable presheaf
`h_X = Hom(-, X)` has no section over `U` as soon as there is no morphism `U ⟶ X`, so it is not
a sheaf. The discrete category on two objects with the indiscrete (largest) topology is such a
site, which shows that representable presheaves are not sheaves in every topology on every site.

## Main results

* `CategoryTheory.not_isSheaf_yoneda_obj_of_bot_mem`: if the empty sieve covers `U` and there is
  no morphism `U ⟶ X`, then `yoneda.obj X` is not a sheaf.
* `CategoryTheory.exists_not_isSheaf_yoneda_obj`: there are a site and an object of it whose
  representable presheaf is not a sheaf.
-/

@[expose] public section

open Opposite

universe v u

namespace CategoryTheory

/-- If the empty sieve covers `U` and there is no morphism from `U` to `X`, the presheaf
represented by `X` is not a sheaf. -/
public theorem not_isSheaf_yoneda_obj_of_bot_mem {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {U X : C} (hU : (⊥ : Sieve U) ∈ J U) (hUX : IsEmpty (U ⟶ X)) :
    ¬ Presheaf.IsSheaf J (yoneda.obj X) := by
  intro h
  obtain ⟨t, -⟩ := ((isSheaf_iff_isSheaf_of_type J _).mp h) ⊥ hU
    (fun _ f hf ↦ ((Sieve.bot_apply f).mp hf).elim)
    (fun _ _ _ _ _ f _ hf ↦ ((Sieve.bot_apply f).mp hf).elim)
  exact hUX.false t

/-- Representable presheaves are not sheaves in every topology on every site: there are a small
category `C`, a Grothendieck topology `J` on `C` and an object `X` of `C` such that the
representable presheaf `h_X = yoneda.obj X` is not a sheaf for `J`. The witness is the discrete
category on `ULift Bool` with the largest topology `⊤`, in which the empty sieve covers
`true` while there is no morphism `true ⟶ false`. -/
@[stacks 03ND "the closing assertion: some representable presheaf on some site is not a sheaf"]
public theorem exists_not_isSheaf_yoneda_obj :
    ∃ (C : Type u) (_ : SmallCategory C) (J : GrothendieckTopology C) (X : C),
      ¬ Presheaf.IsSheaf J (yoneda.obj X) :=
  ⟨Discrete (ULift.{u} Bool), inferInstance, ⊤, ⟨⟨false⟩⟩,
    not_isSheaf_yoneda_obj_of_bot_mem (U := ⟨⟨true⟩⟩) ⊤ trivial
      ⟨fun f ↦ Bool.noConfusion (congrArg ULift.down (Discrete.eq_of_hom f))⟩⟩

end CategoryTheory
