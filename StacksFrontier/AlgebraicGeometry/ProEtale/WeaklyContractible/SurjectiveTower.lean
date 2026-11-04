module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WeaklyContractibleProducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Situation

/-!
# Inverse limits of surjective towers of modules on a weakly contractible site

Let `(Fₙ)` be a countable inverse system of sheaves of modules on a ringed site carrying a
covering collection of weakly contractible objects, and suppose every transition map
`Fₙ₊₁ ⟶ Fₙ` is surjective. Then the projection `lim Fₙ ⟶ F₀` out of the inverse limit is
surjective. This is Stacks 0947(3).

The argument is the one of the source. Over a weakly contractible object `U` the sections functor
is exact, so every transition map is surjective on sections over `U`; and it commutes with
countable inverse limits, so the sections of `lim Fₙ` over `U` are the compatible families of
sections. A compatible family above a given section of `F₀` is then built by lifting one stage at
a time. Surjectivity on sections over every member of a covering collection is local
surjectivity, which for sheaves of modules is the same as being an epimorphism.

## Main results

* `Stacks.WeaklyContractible.epi_limit_π_zero_of_epi_map_succ`: **Stacks 0947(3)**, the
  projection from the inverse limit of a surjective tower of sheaves of modules onto its bottom
  term is an epimorphism.

## Implementation notes

The tower is a functor `ℕᵒᵖ ⥤ SheafOfModules O`, so the source's `F₁` is the term at `0` and the
source's surjectivity of `Fₙ₊₁ → Fₙ` is `Epi (G.map (homOfLE (Nat.le_succ n)).op)`. Surjectivity
of a morphism of sheaves of modules is epimorphicity, by
`Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`.

The lifting is done on sections *as types*: the sections functor over `U` composed with the
forgetful functor to types preserves countable inverse limits, and a limit cone in types is
identified with the compatible families by `CategoryTheory.Limits.Types.isLimitEquivSections`.
Compatibility of the family that the recursion produces with *every* transition map, and not only
with the successive ones, is an induction on the gap; it uses that a morphism of a preorder
category is `homOfLE` of the inequality it carries.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947), part (3)
* [Stacks Project, Tag 0946](https://stacks.math.columbia.edu/tag/0946)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u t

namespace Stacks.WeaklyContractible

/-- A tower of types whose successive transition maps are surjective has a compatible family
above any prescribed element of its bottom term. -/
private theorem surjective_sections_eval_zero_of_surjective_succ {F : ℕᵒᵖ ⥤ Type w}
    (hF : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective fun s : F.sections ↦ s.1 ⟨0⟩ := by
  intro y
  let g : ∀ n : ℕ, F.obj ⟨n⟩ := Nat.rec y fun n a ↦ Classical.choose (hF n a)
  have hg : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op (g (n + 1)) = g n :=
    fun n ↦ Classical.choose_spec (hF n (g n))
  have hkey : ∀ (e d : ℕ) (h : e ≤ d), F.map (homOfLE h).op (g d) = g e := by
    intro e d h
    induction d, h using Nat.le_induction with
    | base => simp
    | succ d hd ih =>
      rwa [← homOfLE_comp hd (Nat.le_succ d), op_comp, F.map_comp, types_comp_apply, hg d]
  exact ⟨⟨fun j ↦ g j.unop, fun {j k} f ↦ hkey k.unop j.unop f.unop.le⟩, rfl⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

open Stacks.SheafOfModules.WeaklyContractible in
/-- **Stacks 0947(3).** On a ringed site with a covering collection of weakly contractible
objects, let `G` be a countable inverse system of sheaves of modules whose transition maps
`Gₙ₊₁ ⟶ Gₙ` are all epimorphisms. Then the projection `lim G ⟶ G₀` from the inverse limit onto
the bottom term of the tower is an epimorphism. -/
@[stacks 0947 "(3)"]
theorem epi_limit_π_zero_of_epi_map_succ
    (S : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    (G : ℕᵒᵖ ⥤ SheafOfModules.{t} S.O)
    (hG : ∀ n : ℕ, Epi (G.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (limit.π G ⟨0⟩) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (isLocallySurjective_of_surjective_of_hasEnoughObjects J _ S.B S.hasEnoughObjects
      fun U hU ↦ ?_)
  let T : SheafOfModules.{t} S.O ⥤ Type t :=
    sectionsOver.{t} S.O U ⋙ forget AddCommGrpCat.{t}
  have hT : IsLimit (T.mapCone (limit.cone G)) := isLimitOfPreserves T (limit.isLimit G)
  have hsucc : ∀ n : ℕ,
      Function.Surjective ((G ⋙ T).map (homOfLE (Nat.le_succ n)).op) := fun n ↦ by
    have := hG n
    exact surjective_sections_of_epi (G.map (homOfLE (Nat.le_succ n)).op) U
      fun _ _ _ h ↦ S.isWeaklyContractible hU _ _ _ h
  intro y
  obtain ⟨s, hs⟩ := surjective_sections_eval_zero_of_surjective_succ hsucc y
  exact ⟨(Types.isLimitEquivSections hT).symm s,
    (Types.isLimitEquivSections_symm_apply hT s ⟨0⟩).trans hs⟩

end Stacks.WeaklyContractible

end
