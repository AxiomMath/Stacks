module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections
import StacksCore.Tactic.StacksAttribute

/-!
# Sections of a direct sum of sheaves of modules on a quasi-compact open

Let `R` be a sheaf of rings on a topological space `X` and let `U ⊆ X` be an open subset
which is quasi-compact. Then the canonical map
`⨁ᵢ Fᵢ(U) ⟶ (⨁ᵢ Fᵢ)(U)` from the direct sum of the modules of sections to the sections of
the direct sum is an isomorphism, for an arbitrary index set.

The statement is phrased as preservation of colimits of discrete shape by the evaluation
functor, which carries the canonical comparison map and its naturality with it rather than
naming them separately.

## Main results

* `Stacks.SheafOfModules.preservesCoproducts_evaluation_of_isCompact`: evaluation of sheaves
  of `R`-modules on a quasi-compact open subset preserves coproducts of any shape.

## Implementation notes

The underlying site-theoretic input is Stacks 0935 for the site of opens, in the form
`Stacks.Sites.sheafOfModules_sections_preserves_coproducts`; the only work here is to see
that a quasi-compact open is a quasi-compact object of `Opens.grothendieckTopology X`, and to
transfer from the `AddCommGrpCat`-valued sections functor to the `ModuleCat`-valued
evaluation functor.

That transfer needs care with universes. The index set lives in a universe `v` unrelated to
the universe `w` of the sections of `R`, so a coproduct of `v`-many sheaves of modules has
sections in `max v w` while `SheafOfModules.evaluation` lands in `ModuleCat.{w}`. Composing
with `ModuleCat.uliftFunctor` and with `AddCommGrpCat.uliftFunctor` puts both sides in
`max v w`, and the forgetful functor to abelian groups reflects isomorphisms, hence reflects
colimits of discrete shape; so the statement for evaluation follows from the statement for
sections.

The result is stated for a sheaf of rings on an arbitrary topological space rather than for
the structure sheaf of a ringed space, which is the special case `R = 𝒪_X`.

## References

* [Stacks Project, Tag 01AI](https://stacks.math.columbia.edu/tag/01AI)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{w}) {I : Type v}

/-- A quasi-compact open subset is a quasi-compact object of the site of opens: a covering
family of it admits a finite subfamily which still covers. -/
@[sga "4 VI 1.6.1" "partial"]
theorem isQuasiCompactObject_of_isCompact (U : Opens X) (hU : IsCompact (U : Set X)) :
    (Opens.grothendieckTopology X).IsQuasiCompactObject U := by
  intro 𝒰 h𝒰
  obtain ⟨F, hF⟩ := hU.elim_finite_subcover (fun i => (𝒰.X i : Set X))
    (fun i => (𝒰.X i).isOpen) (by
      intro x hx
      change ∀ y ∈ U, ∃ (V : Opens X) (f : V ⟶ U), 𝒰.sieve₀ f ∧ y ∈ V at h𝒰
      obtain ⟨V, f, hf, hxV⟩ := h𝒰 x hx
      obtain ⟨i, g, hi⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
      exact Set.mem_iUnion.mpr ⟨i, g.le hxV⟩)
  refine ⟨𝒰.restrictIndex (fun i : F => i.1),
    ⟨fun i => i.1, fun _ => 𝟙 _, fun _ => Category.id_comp _⟩, ?_, ?_⟩
  · show ∀ x ∈ U, ∃ (V : Opens X) (f : V ⟶ U),
      (𝒰.restrictIndex (fun i : F => i.1)).sieve₀ f ∧ x ∈ V
    intro x hx
    obtain ⟨i, hiF, hxi⟩ := Set.mem_iUnion₂.mp (hF hx)
    exact ⟨𝒰.X i, 𝒰.f i, (𝒰.restrictIndex (fun i : F => i.1)).sieve₀_f ⟨i, hiF⟩, hxi⟩
  · exact (Set.toFinite F).subset (Set.range_subset_iff.2 fun j => j.2)

/-- **Stacks Project, Tag 01AI.** On a quasi-compact open subset, taking sections commutes
with direct sums of sheaves of modules. -/
@[stacks 01AI]
theorem preservesCoproducts_evaluation_of_isCompact
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    PreservesColimitsOfShape (Discrete I)
      (_root_.SheafOfModules.evaluation.{w} R (op U)) := by
  let G := CategoryTheory.forget₂ (ModuleCat.{max v w, w} (R.obj.obj (op U)))
    AddCommGrpCat.{max v w}
  let F := (_root_.SheafOfModules.evaluation.{w} R (op U)) ⋙
    ModuleCat.uliftFunctor.{v} (R.obj.obj (op U))
  have : ReflectsColimitsOfShape (Discrete I) G := by
    dsimp only [G]
    apply reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : PreservesColimitsOfShape (Discrete I) AddCommGrpCat.uliftFunctor.{v, w} :=
    ⟨inferInstance⟩
  have : PreservesColimitsOfShape (Discrete I) (F ⋙ G) := by
    show PreservesColimitsOfShape (Discrete I)
      ((_root_.SheafOfModules.toSheaf.{w} R ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj (op U)) ⋙
          AddCommGrpCat.uliftFunctor.{v, w})
    have : PreservesColimitsOfShape (Discrete I)
        (_root_.SheafOfModules.toSheaf.{w} R ⋙
          (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj (op U)) :=
      Sites.sheafOfModules_sections_preserves_coproducts
        (Opens.grothendieckTopology X) R U (isQuasiCompactObject_of_isCompact U hU) I
    infer_instance
  have : PreservesColimitsOfShape (Discrete I) F :=
    preservesColimitsOfShape_of_reflects_of_preserves (J := Discrete I) (F := F) (G := G)
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (J := Discrete I) (F := _root_.SheafOfModules.evaluation.{w} R (op U))
    (G := ModuleCat.uliftFunctor.{v} (R.obj.obj (op U)))

end Stacks.SheafOfModules

end
