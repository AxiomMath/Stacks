module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHullAdjunction.Basic

/-!
# A criterion for the reflexive-hull adjunction

The reflexive-hull adjunction of [Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
is proved in `StacksFrontier/AlgebraicGeometry/ReflexiveHullAdjunction/Basic.lean` under two
separate hypotheses on the hull `F^∨∨` of a coherent module: that it is coherent, and that it
is reflexive.  This file replaces that pair by a single hypothesis on the *dual* `F^∨`, and
then weakens the reflexivity half of that hypothesis to an epimorphism condition.

The weakening rests on a fact about duals that holds on any scheme, with no coherence and no
hypothesis on `X`: the canonical map `F^∨ ⟶ F^∨∨∨` of a dual module to its double dual is a
*split* monomorphism, its retraction being the dual of the canonical map of `F`.  So for a
dual module the only thing reflexivity can fail to supply is surjectivity.

## Main results

* `isReflexive_dualSheaf_of_isReflexive`: the dual of a reflexive module is reflexive.
* `isReflexive_dualSheaf_iff_epi`: a dual module is reflexive exactly when its canonical map
  to its double dual is an epimorphism.
* `reflexiveHullAdjunction_of_dualSheaf`: the adjunction, from the single hypothesis that the
  dual of a coherent module is coherent and reflexive.
* `reflexiveHullAdjunction_of_epi`: the same, with reflexivity of the dual replaced by the
  epimorphism condition.

## Implementation notes

Both hypotheses of `ReflexiveHull.reflexiveHullAdjunction` concern `F^∨∨`, which is the dual
of `F^∨`; applying a statement about duals twice therefore discharges both at once.  The
single hypothesis used here is formally stronger than the conjunction of the two it replaces,
because the two speak only about modules of the form `F^∨∨` while this one speaks about
`G^∨` for every coherent `G`.  It is nevertheless the statement one proves: it is
[Stacks, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4) at `G = 𝒪_X` together with
coherence of the internal Hom, [Stacks, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2).
Neither is available in this library.

`IsReflexive` is a plain `def` rather than an abbreviation, so unfolding it to `IsIso` is done
explicitly where instance search has to see through it.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveHull

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveHullCriterion

variable {X : Scheme.{u}}

/-- The dual of an isomorphism is an isomorphism. -/
theorem isIso_dualMap {F G : X.Modules} (u : F ⟶ G) (h : IsIso u) : IsIso (dualMap u) := by
  refine ⟨dualMap (inv u), ?_, ?_⟩
  · rw [← dualMap_comp, IsIso.inv_hom_id, dualMap_id]
  · rw [← dualMap_comp, IsIso.hom_inv_id, dualMap_id]

/-- **The dual of a reflexive module is reflexive.**  If the canonical map of `G` is an
isomorphism then so is its dual, and the triangle identity exhibits the canonical map of
`G^∨` as the inverse of that dual. -/
theorem isReflexive_dualSheaf_of_isReflexive (G : X.Modules) (h : IsReflexive G) :
    IsReflexive (dualSheaf G) := by
  have hr : IsIso (dualMap (toDoubleDual G)) := isIso_dualMap _ h
  have hinv : toDoubleDual (dualSheaf G) = inv (dualMap (toDoubleDual G)) := by
    rw [← Category.comp_id (toDoubleDual (dualSheaf G)),
      ← IsIso.hom_inv_id (dualMap (toDoubleDual G)), ← Category.assoc,
      toDoubleDual_dualMap_comp G, Category.id_comp]
  change IsIso (toDoubleDual (dualSheaf G))
  rw [hinv]
  infer_instance

/-- **A dual module is reflexive exactly when its canonical map to the double dual is an
epimorphism.**  Injectivity is automatic for a dual, by `isSplitMono_toDoubleDual_dualSheaf`,
so surjectivity is the whole of the condition. -/
theorem isReflexive_dualSheaf_iff_epi (G : X.Modules) :
    IsReflexive (dualSheaf G) ↔ Epi (toDoubleDual (dualSheaf G)) := by
  refine ⟨fun (_ : IsIso (toDoubleDual (dualSheaf G))) => inferInstance, fun _ => ?_⟩
  have := isSplitMono_toDoubleDual_dualSheaf G
  exact isIso_of_epi_of_isSplitMono _

/-- **Stacks Tag 0EBH, the adjunction, from one hypothesis on duals.**  If the dual of every
coherent module is coherent and reflexive, then the double-dual functor is left adjoint to the
inclusion of coherent reflexive modules into coherent modules, with the canonical bidual map
as its unit.

The hypothesis is applied twice: once to `F` and once to `F^∨`, which is coherent by the first
application.  That discharges both hypotheses of
`Stacks.AlgebraicGeometry.ReflexiveHull.reflexiveHullAdjunction`, which concern `F^∨∨`. -/
noncomputable def reflexiveHullAdjunction_of_dualSheaf (X : Scheme.{u})
    (H : ∀ F : X.Modules, F.IsCoherent →
      (dualSheaf F).IsCoherent ∧ IsReflexive (dualSheaf F)) :
    { p : (Σ L : CoherentModules X ⥤ CoherentReflexiveModules X, L ⊣ inclusion X) //
      ∀ F : CoherentModules X,
        ∃ h : (p.1.obj F).obj.obj = reflexiveHull F.obj,
          (p.2.unit.app F).hom ≫ eqToHom h = (toReflexiveHull F.obj).1 } :=
  reflexiveHullAdjunction X (fun F hF => (H (dualSheaf F) (H F hF).1).1)
    (fun F hF => (H (dualSheaf F) (H F hF).1).2)

/-- **Stacks Tag 0EBH, the adjunction, from coherence and surjectivity.**  The same as
`reflexiveHullAdjunction_of_dualSheaf`, with reflexivity of the dual replaced by the weaker
requirement that its canonical map to the double dual be an epimorphism. -/
noncomputable def reflexiveHullAdjunction_of_epi (X : Scheme.{u})
    (H : ∀ F : X.Modules, F.IsCoherent →
      (dualSheaf F).IsCoherent ∧ Epi (toDoubleDual (dualSheaf F))) :
    { p : (Σ L : CoherentModules X ⥤ CoherentReflexiveModules X, L ⊣ inclusion X) //
      ∀ F : CoherentModules X,
        ∃ h : (p.1.obj F).obj.obj = reflexiveHull F.obj,
          (p.2.unit.app F).hom ≫ eqToHom h = (toReflexiveHull F.obj).1 } :=
  reflexiveHullAdjunction_of_dualSheaf X
    (fun F hF => ⟨(H F hF).1, (isReflexive_dualSheaf_iff_epi F).2 (H F hF).2⟩)

end Stacks.AlgebraicGeometry.ReflexiveHullCriterion
