module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksCore.Tactic.EgaSgaAttribute

/-! # Characterization of sheaf theoretically empty objects

Let `C` be a site and let `U` be an object of `C`.  Following Stacks 04B5, `U` is *sheaf
theoretically empty* when the sheafification of the canonical map `∅ ⟶ h_U` from the empty
(initial) presheaf to the presheaf represented by `U` is an isomorphism of sheaves.  Stacks 04B6
says that this happens exactly when every sheaf has a single section over `U`, exactly when the
sheafification `∅^#` of the empty presheaf has a single section over `U`, exactly when `∅^#(U)` is
merely nonempty, and exactly when the empty sieve is a covering sieve of `U`.  It also records that
sheaf theoretic emptiness passes to every object admitting a morphism to `U`.

The bridge between the sheaf-theoretic clauses and the combinatorial clause `⊥ ∈ J U` is local
surjectivity of the unit `P ⟶ P^#`: a section of `∅^#` over `U` is locally in the image of
`∅ ⟶ ∅^#`, and since `∅` has no sections at all the resulting covering sieve is the empty sieve.

## Main results

* `emptyPresheaf`, `emptyPresheafTo` and `isInitialEmptyPresheaf`: the empty presheaf of sets, the
  unique map out of it, and the fact that it is an initial presheaf.
* `subsingleton_and_nonempty_sections_of_bot_mem` (Stacks 04B6, (5) implies (2)): if the empty
sieve covers `U`, then every sheaf has exactly one section over `U`.
* `bot_mem_of_nonempty_sheafify_emptyPresheaf` (Stacks 04B6, (4) implies (5)): if `∅^#(U)` is
  nonempty then the empty sieve covers `U`.
* `isIso_map_emptyPresheafTo_of_sections` (Stacks 04B6, (2) implies (1)): if every sheaf has
exactly one section over `U` then `U` is sheaf theoretically empty.
* `nonempty_sheafify_emptyPresheaf_of_isIso` (Stacks 04B6, (1) implies (4)): a sheaf theoretically
  empty `U` has `∅^#(U)` nonempty.
* `tfae_sheafTheoreticallyEmpty` (Stacks 04B6): the five conditions are equivalent.
* `isIso_map_emptyPresheafTo_of_hom` (Stacks 04B6, the final assertion): sheaf theoretic emptiness
  is inherited by any object mapping to a sheaf theoretically empty object.

The four single implications are steps towards the equivalence, not clauses of it, so the tag
`04B6` is registered only on `tfae_sheafTheoreticallyEmpty` and on the final assertion
`isIso_map_emptyPresheafTo_of_hom`.

Tags covered: 04B6.
-/

@[expose] public section

namespace StacksSheafTheoreticallyEmpty

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The empty presheaf of sets on `C`: the constant presheaf with value the empty type.  This is
the presheaf written `∅` in Stacks 04B5. -/
def emptyPresheaf : Cᵒᵖ ⥤ Type u := (Functor.const Cᵒᵖ).obj PEmpty

/-- The unique morphism from the empty presheaf to a presheaf `P`. -/
def emptyPresheafTo (P : Cᵒᵖ ⥤ Type u) : emptyPresheaf (C := C) ⟶ P where
  app _ := TypeCat.ofHom fun x => PEmpty.elim x
  naturality _ _ _ := by ext x; exact PEmpty.elim x

/-- The empty presheaf is an initial object of the category of presheaves of sets on `C`. -/
@[sga "3 IV 4.4.4"]
def isInitialEmptyPresheaf : IsInitial (emptyPresheaf (C := C)) :=
  IsInitial.ofUniqueHom (fun P => emptyPresheafTo P)
    (fun _ _ => by ext X x; exact PEmpty.elim x)

/-- A morphism out of the empty presheaf has empty image sieves: an arrow in the image sieve of a
section would provide a section of the empty presheaf. -/
theorem imageSieve_eq_bot {P : Cᵒᵖ ⥤ Type u} (f : emptyPresheaf (C := C) ⟶ P) {U : C}
    (s : P.obj (op U)) : Presheaf.imageSieve f s = ⊥ := by
  ext V g
  simp only [Presheaf.imageSieve_apply, Sieve.bot_apply, iff_false]
  rintro ⟨t, -⟩
  exact PEmpty.elim t

/-- **Stacks 04B6**, (5) implies (2).  If the empty sieve is a covering sieve of `U`, then every
sheaf of sets has exactly one section over `U`.

A single implication of the five-fold equivalence, hence a proper part of the one assertion of
Stacks 04B6 and not a clause of it, so it carries no `@[stacks 04B6]` attribute.  The tag sits on
`tfae_sheafTheoreticallyEmpty` and on `isIso_map_emptyPresheafTo_of_hom`, at lines 155 and 173
of this file.  Do not restore the attribute here. -/
@[sga "4 II 4.6.1" "Clause 1"]
theorem subsingleton_and_nonempty_sections_of_bot_mem {U : C} (hU : (⊥ : Sieve U) ∈ J U)
    (F : Sheaf J (Type u)) :
    Subsingleton (F.obj.obj (op U)) ∧ Nonempty (F.obj.obj (op U)) := by
  have hT := F.isTerminalOfBotCover U hU
  refine ⟨⟨fun x y => ?_⟩, ⟨hT.from PUnit PUnit.unit⟩⟩
  exact types_congr_hom
    (hT.hom_ext (TypeCat.ofHom fun _ : PUnit => x) (TypeCat.ofHom fun _ : PUnit => y)) PUnit.unit

/-- **Stacks 04B6**, (4) implies (5).  If the sheafification of the empty presheaf has a section
over `U`, then the empty sieve is a covering sieve of `U`.  Indeed the unit `∅ ⟶ ∅^#` is locally
surjective, so the section is locally in the image of a map whose source has no sections.

A single implication of the five-fold equivalence, hence a proper part of the one assertion of
Stacks 04B6 and not a clause of it, so it carries no `@[stacks 04B6]` attribute.  The tag sits on
`tfae_sheafTheoreticallyEmpty` and on `isIso_map_emptyPresheafTo_of_hom`, at lines 155 and 173
of this file.  Do not restore the attribute here. -/
@[sga "4 II 4.6.1" "Clause 1", sga "4 II 4.6.2" "partial"]
theorem bot_mem_of_nonempty_sheafify_emptyPresheaf [HasWeakSheafify J (Type u)] {U : C}
    (h : Nonempty ((sheafify J (emptyPresheaf (C := C))).obj (op U))) :
    (⊥ : Sieve U) ∈ J U := by
  obtain ⟨s⟩ := h
  have hmem := Presheaf.imageSieve_mem J (toSheafify J (emptyPresheaf (C := C))) (U := op U) s
  rwa [imageSieve_eq_bot] at hmem

/-- **Stacks 04B6**, (2) implies (1).  If every sheaf of sets has exactly one section over `U`,
then `U` is sheaf theoretically empty: both `∅^#` and `h_U^#` are initial sheaves, and any
morphism between initial objects is an isomorphism.

A single implication of the five-fold equivalence, hence a proper part of the one assertion of
Stacks 04B6 and not a clause of it, so it carries no `@[stacks 04B6]` attribute.  The tag sits on
`tfae_sheafTheoreticallyEmpty` and on `isIso_map_emptyPresheafTo_of_hom`, at lines 155 and 173
of this file.  Do not restore the attribute here. -/
theorem isIso_map_emptyPresheafTo_of_sections [HasWeakSheafify J (Type u)] {U : C}
    (h : ∀ F : Sheaf J (Type u), Subsingleton (F.obj.obj (op U)) ∧ Nonempty (F.obj.obj (op U))) :
    IsIso ((presheafToSheaf J (Type u)).map (emptyPresheafTo (yoneda.obj U))) := by
  have hE : IsInitial ((presheafToSheaf J (Type u)).obj (emptyPresheaf (C := C))) :=
    isInitialEmptyPresheaf.isInitialObj _ _
  have e : ∀ F : Sheaf J (Type u),
      ((presheafToSheaf J (Type u)).obj (yoneda.obj U) ⟶ F) ≃ F.obj.obj (op U) := fun F =>
    ((sheafificationAdjunction J (Type u)).homEquiv (yoneda.obj U) F).trans yonedaEquiv
  have hY : IsInitial ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) := by
    refine IsInitial.ofUniqueHom (fun F => (e F).symm (h F).2.some) fun F m => (e F).injective ?_
    have := (h F).1
    exact Subsingleton.elim _ _
  exact ⟨⟨hY.to _, hE.hom_ext _ _, hY.hom_ext _ _⟩⟩

/-- **Stacks 04B6**, (1) implies (4).  If `U` is sheaf theoretically empty, then `∅^#(U)` is
nonempty: transport the identity of `U`, viewed as a section of `h_U^#` over `U`, through the
inverse isomorphism.

A single implication of the five-fold equivalence, hence a proper part of the one assertion of
Stacks 04B6 and not a clause of it, so it carries no `@[stacks 04B6]` attribute.  The tag sits on
`tfae_sheafTheoreticallyEmpty` and on `isIso_map_emptyPresheafTo_of_hom`, at lines 155 and 173
of this file.  Do not restore the attribute here. -/
theorem nonempty_sheafify_emptyPresheaf_of_isIso [HasWeakSheafify J (Type u)] {U : C}
    (h : IsIso ((presheafToSheaf J (Type u)).map (emptyPresheafTo (yoneda.obj U)))) :
    Nonempty ((sheafify J (emptyPresheaf (C := C))).obj (op U)) :=
  ⟨(inv ((presheafToSheaf J (Type u)).map (emptyPresheafTo (yoneda.obj U)))).hom.app (op U)
    ((toSheafify J (yoneda.obj U)).app (op U) (yonedaEquiv (𝟙 (yoneda.obj U))))⟩

/-- The empty sieve is covering on the source of any morphism whose target has covering empty
sieve, because the pullback of the empty sieve is the empty sieve. -/
theorem bot_mem_of_bot_mem {U U' : C} (f : U' ⟶ U) (hU : (⊥ : Sieve U) ∈ J U) :
    (⊥ : Sieve U') ∈ J U' := by
  simpa using J.pullback_stable f hU

open List in
/-- **Stacks 04B6.**  For an object `U` of a site `(C, J)` the following are equivalent:
(1) `U` is sheaf theoretically empty, i.e. `∅^# ⟶ h_U^#` is an isomorphism of sheaves;
(2) every sheaf of sets has exactly one section over `U`;
(3) `∅^#(U)` has exactly one element;
(4) `∅^#(U)` is nonempty;
(5) the empty sieve is a covering sieve of `U`. -/
@[stacks 04B6]
theorem tfae_sheafTheoreticallyEmpty [HasWeakSheafify J (Type u)] (U : C) :
    TFAE [IsIso ((presheafToSheaf J (Type u)).map (emptyPresheafTo (yoneda.obj U))),
      ∀ F : Sheaf J (Type u), Subsingleton (F.obj.obj (op U)) ∧ Nonempty (F.obj.obj (op U)),
      Subsingleton ((sheafify J (emptyPresheaf (C := C))).obj (op U)) ∧
        Nonempty ((sheafify J (emptyPresheaf (C := C))).obj (op U)),
      Nonempty ((sheafify J (emptyPresheaf (C := C))).obj (op U)),
      (⊥ : Sieve U) ∈ J U] := by
  tfae_have 5 → 2 := fun h F => subsingleton_and_nonempty_sections_of_bot_mem J h F
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 4 := fun h => h.2
  tfae_have 4 → 5 := fun h => bot_mem_of_nonempty_sheafify_emptyPresheaf J h
  tfae_have 2 → 1 := fun h => isIso_map_emptyPresheafTo_of_sections J h
  tfae_have 1 → 4 := fun h => nonempty_sheafify_emptyPresheaf_of_isIso J h
  tfae_finish

/-- **Stacks 04B6**, final assertion.  If `U` is sheaf theoretically empty, then so is `U'` for
every morphism `U' ⟶ U` of `C`. -/
@[stacks 04B6]
theorem isIso_map_emptyPresheafTo_of_hom [HasWeakSheafify J (Type u)] {U U' : C} (f : U' ⟶ U)
    (h : IsIso ((presheafToSheaf J (Type u)).map (emptyPresheafTo (yoneda.obj U)))) :
    IsIso ((presheafToSheaf J (Type u)).map (emptyPresheafTo (yoneda.obj U'))) :=
  isIso_map_emptyPresheafTo_of_sections J
    (subsingleton_and_nonempty_sections_of_bot_mem J
      (bot_mem_of_bot_mem J f
        (bot_mem_of_nonempty_sheafify_emptyPresheaf J
          (nonempty_sheafify_emptyPresheaf_of_isIso J h))))

end StacksSheafTheoreticallyEmpty
