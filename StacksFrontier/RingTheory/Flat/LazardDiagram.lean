module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksFrontier.RingTheory.Flat.Lazard
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lazard's theorem as a filtered colimit in `ModuleCat`

Lazard's theorem (Stacks 058G) is proved in `StacksFrontier.RingTheory.Flat.Lazard` in its
unbundled form: a flat module is the `Module.DirectLimit` of a directed system of free finite
modules.  This file restates the forward direction in the language of `CategoryTheory`, as a
filtered diagram in `ModuleCat R` together with a colimit cocone, which is the shape a
filtered-colimit argument can consume directly.

The translation is Mathlib's `ModuleCat.directLimitIsColimit`, which exhibits
`Module.DirectLimit G f` as a `CategoryTheory.Limits.IsColimit` of the diagram
`ModuleCat.directLimitDiagram G f`, together with the fact that a nonempty directed preorder is
filtered as a category (`CategoryTheory.isFiltered_of_directed_le_nonempty`).

## Main results

* `exists_isFiltered_diagram_free_finite_of_flat`: a flat module is the colimit of a filtered
  diagram of free finite modules in `ModuleCat R`, up to isomorphism of the colimit point.
* `exists_isFiltered_diagram_free_finite_colimit_eq_of_flat`: the same, with the colimit cocone
  transported so that its point *is* `ModuleCat.of R M`.

## References

* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

/-- **Lazard's theorem, categorical form.**  A flat module `M` over a commutative ring `R` is the
colimit of a filtered diagram of free finite `R`-modules.

Concretely: there is a small filtered category `J`, a diagram `D : J ⥤ ModuleCat R` whose values
are all free and finite over `R`, and a colimit cocone `c` on `D` whose point is isomorphic to
`ModuleCat.of R M`.

This is a restatement of `flat_exists_directLimit_free_finite`; the index preorder produced there
is nonempty and directed, hence filtered as a category, and its `Module.DirectLimit` is the
categorical colimit of `ModuleCat.directLimitDiagram` by `ModuleCat.directLimitIsColimit`. -/
@[sga "3 VIIA 4.2.1" "more general",
  sga "4 V 8.2.12" "special case",
  sga "4 XVII 5.5.1.1" "commutative rings",
  sga "4 XVII 5.5.6.3" "partial"]
theorem exists_isFiltered_diagram_free_finite_of_flat {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ ModuleCat.{u} R)
      (c : Limits.Cocone D) (_ : Limits.IsColimit c),
      (∀ j, Module.Free R (D.obj j)) ∧ (∀ j, Module.Finite R (D.obj j)) ∧
        Nonempty (c.pt ≅ ModuleCat.of R M) := by
  obtain ⟨ι, _, _, _, _, G, _, _, f, _, hfree, hfin, ⟨e⟩⟩ :=
    flat_exists_directLimit_free_finite (R := R) M
  exact ⟨ι, inferInstance, inferInstance, ModuleCat.directLimitDiagram G f,
    ModuleCat.directLimitCocone G f, ModuleCat.directLimitIsColimit G f, hfree, hfin,
    ⟨e.toModuleIso⟩⟩

/-- **Lazard's theorem, categorical form with the colimit point on the nose.**  A flat module `M`
over a commutative ring `R` carries a colimit cocone, with point exactly `ModuleCat.of R M`, on a
filtered diagram of free finite `R`-modules.

This is `exists_isFiltered_diagram_free_finite_of_flat` with the cocone of
`ModuleCat.directLimitCocone` extended along the isomorphism `Module.DirectLimit G f ≅ M`; being a
colimit transports along `CategoryTheory.Limits.IsColimit.ofIsoColimit`.  The equality `c.pt =
ModuleCat.of R M` — rather than a mere isomorphism — is what lets a consumer rewrite the colimit
of the diagram as `M` itself. -/
@[sga "3 VIIA 4.2.1" "more general",
  sga "4 V 8.2.12" "special case",
  sga "4 XVII 5.5.1.1" "commutative rings",
  sga "4 XVII 5.5.6.3" "partial"]
theorem exists_isFiltered_diagram_free_finite_colimit_eq_of_flat {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ ModuleCat.{u} R)
      (c : Limits.Cocone D) (_ : Limits.IsColimit c),
      (∀ j, Module.Free R (D.obj j)) ∧ (∀ j, Module.Finite R (D.obj j)) ∧
        c.pt = ModuleCat.of R M := by
  obtain ⟨ι, _, _, _, _, G, _, _, f, _, hfree, hfin, ⟨e⟩⟩ :=
    flat_exists_directLimit_free_finite (R := R) M
  refine ⟨ι, inferInstance, inferInstance, ModuleCat.directLimitDiagram G f,
    (ModuleCat.directLimitCocone G f).extend e.toModuleIso.hom,
    Limits.IsColimit.ofIsoColimit (ModuleCat.directLimitIsColimit G f)
      (Limits.Cocone.ext e.toModuleIso), hfree, hfin, rfl⟩

end

end
