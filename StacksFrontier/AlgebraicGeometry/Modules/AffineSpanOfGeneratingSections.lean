module

public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AffineExtensionSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiCompactCoproductSections

/-!
# Global generating sections span the sections over an affine open

Let `F` be a quasi-coherent module on a scheme `Y` and let `σ : F.GeneratingSections` be a family
of global sections generating it, that is, a family whose associated morphism
`σ.π : 𝒪_Y^{(σ.I)} ⟶ F` out of the free module is an epimorphism.  This file proves that over an
**affine** open `O` of `Y` the sections `Γ(F, O)` are spanned, over `Γ(Y, O)`, by the
restrictions of the members of `σ`.

Generation by global sections is an epimorphism of sheaves, hence a priori only a *local*
statement about sections; what makes it a statement about the sections over `O` is the
`H¹`-vanishing half of [Stacks, Tag 01XB], in the form
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`: an epimorphism of quasi-coherent
modules is surjective on the sections over an affine open.  A section of `F` over `O` is
therefore the image of a section of the free module, and over a quasi-compact object of the site
the sections of a free module are the finitely supported families of functions
(`Stacks.Sites.bijective_freeSectionsMap`), so that image is a finite `Γ(Y, O)`-combination of
the restricted generators.

This is the converse direction to `Stacks.AffineGermSpan.span_range_germ_sections_eq_top`, which
spans a *stalk* by the germs of the sections over an affine open; here a *module of sections* is
spanned by the restrictions of global sections.

## Main results

* `Stacks.AffineSpanOfGeneratingSections.mem_span_eval_of_generatingSections`: **the sections of
  `F` over an affine open are spanned by the values there of a global generating family.**
* `Stacks.AffineSpanOfGeneratingSections.mem_span_restrict_top_of_generatingSections`: the same
  with the generators written as the restrictions of the values at the open `⊤`, which is the
  shape a global generating family produced on a scheme presents itself in.

## Hypotheses carried, and why

Quasi-coherence of `F` and affineness of `O` are both inputs of
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`, which is where the cohomological
content sits, and neither can be dropped: on a non-affine open the sections functor is not exact
on quasi-coherent modules, and for a module that is not quasi-coherent there is no Čech vanishing
to run.  Quasi-coherence of the free module `𝒪_Y^{(σ.I)}`, the other hypothesis of that
statement, is found by instance search and needs no finiteness of `σ.I`.

**No finiteness of the index type is used.**  The finite support comes from the description of
the sections of the free module over a quasi-compact object, not from the index type, so the
statements below hold for a generating family indexed by an arbitrary type and in particular do
not need `Finite σ.I`.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.AffineSpanOfGeneratingSections

variable {Y : Scheme.{u}}

/-- **The sections of a quasi-coherent module over an affine open are spanned by the values
there of a global generating family.**

The epimorphism `σ.π` out of the free module is surjective on the sections over the affine open
`O` by the `H¹`-vanishing half of [Stacks, Tag 01XB]; the sections of the free module over `O`,
a quasi-compact object of the site of opens, are the finitely supported families of functions on
`O`; and `σ.π` carries such a family to the corresponding finite combination of the values of
`σ`. -/
theorem mem_span_eval_of_generatingSections (M : Y.Modules) [M.IsQuasicoherent]
    (σ : M.GeneratingSections) (O : Y.Opens) (hO : IsAffineOpen O) (y : M.val.obj (op O)) :
    y ∈ Submodule.span (Y.ringCatSheaf.obj.obj (op O))
      (Set.range fun i => (σ.s i).eval (op O)) := by
  classical
  obtain ⟨z, hz⟩ := @Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen Y
    (SheafOfModules.free σ.I) M σ.π inferInstance inferInstance σ.epi O hO y
  have hqc : (Opens.grothendieckTopology (Y : TopCat.{u})).IsQuasiCompactObject O :=
    Stacks.SheafOfModules.isQuasiCompactObject_of_isCompact O hO.isCompact
  obtain ⟨c, rfl⟩ := (Stacks.Sites.bijective_freeSectionsMap (R := Y.ringCatSheaf) σ.I O hqc).2 z
  have hdec := AlgebraicGeometry.Space.AffineExtension.freeHomEquiv_symm_app_freeSectionsMap
    (R := Y.ringCatSheaf) M σ.s (op O) c
  rw [← hz, hdec]
  exact Finsupp.mem_span_range_iff_exists_finsupp.2
    ⟨c, (Finsupp.linearCombination_apply _ _).symm⟩

/-- **The sections over an affine open are spanned by the restrictions of the global sections of
a generating family.**  This is
`Stacks.AffineSpanOfGeneratingSections.mem_span_eval_of_generatingSections` with the generators
written through the compatibility of a global section with restriction. -/
theorem mem_span_restrict_top_of_generatingSections (M : Y.Modules) [M.IsQuasicoherent]
    (σ : M.GeneratingSections) (O : Y.Opens) (hO : IsAffineOpen O) (y : M.val.obj (op O)) :
    y ∈ Submodule.span (Y.ringCatSheaf.obj.obj (op O))
      (Set.range fun i => M.val.map (homOfLE (le_top : O ≤ ⊤)).op ((σ.s i).eval (op ⊤))) :=
  funext (fun i => (σ.s i).2 (homOfLE (le_top : O ≤ ⊤)).op) ▸
    mem_span_eval_of_generatingSections M σ O hO y

end Stacks.AffineSpanOfGeneratingSections

end
