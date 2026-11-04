module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# Quasi-isomorphy of complexes of sheaves of modules is local on the site

Let `R` be a sheaf of rings on a site `(C, J)` and let `φ : K ⟶ L` be a morphism of cochain
complexes of `R`-modules. This file proves that `φ` is a quasi-isomorphism as soon as its
degreewise restriction to the slice site over each member of a family of objects covering the
final object is one.

The two inputs are both already in the library. Restriction to a slice is exact, hence preserves
homology, so the restriction of the degree-`n` homology map of `φ` is — up to the comparison
isomorphism `CategoryTheory.ShortComplex.mapHomologyIso` — the degree-`n` homology map of the
restriction of `φ`; and invertibility of a morphism of sheaves of modules is local on the site
(`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`). So the homology maps of `φ`
are locally invertible, hence invertible, which is quasi-isomorphy.

## Main results

* `Stacks.SheafOfModules.preservesHomology_overFunctor`: restriction of sheaves of modules to a
  slice of the site preserves homology.
* `Stacks.SheafOfModules.quasiIso_overFunctor_mapHomologicalComplex_map`: **the degreewise
  restriction of a quasi-isomorphism to a slice is a quasi-isomorphism**, which is also the
  statement for `AlgebraicGeometry.RingedSite.restrictComplex`, that functor being this one.
* `Stacks.SheafOfModules.isIso_overFunctor_map_homologyMap`: the restriction to a slice of a
  homology map of `φ` is invertible as soon as the restriction of `φ` is a quasi-isomorphism.
* `Stacks.SheafOfModules.quasiIso_of_coversTop`: **quasi-isomorphy is local on the site.**

## Implementation notes

The homology comparison is taken in the `CategoryTheory.ShortComplex` form rather than in a
`HomologicalComplex` form, because Mathlib provides the naturality of the comparison only there
(`CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality`). This costs nothing:
`HomologicalComplex.homologyMap` is *defined* as the short-complex homology map of the image of
`φ` under `HomologicalComplex.shortComplexFunctor`, and the short complex at `n` of a degreewise
restricted complex is the restriction of the short complex at `n`, by definitional unfolding. So
the two spellings are interchangeable by `exact`.

Mathlib's `HomologicalComplex.quasiIso_map_iff_of_preservesHomology` is the same comparison in
the reverse direction, but it asks the functor to reflect isomorphisms, which restriction to a
single slice does not do. The covering family is exactly what replaces that hypothesis.

`SheafOfModules.overFunctor_preservesHomology` of
`StacksFrontier/CategoryTheory/Sites/Modules/OverFunctorExact.lean` is the same conclusion as
`preservesHomology_overFunctor` below, but it assumes the site to have binary products and the
slice site to have sheafification. Neither holds on a general ringed site, so the route
taken here is through `Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits`
and `overFunctor_preservesEpimorphisms`, which need only the base site. The two names are kept
apart so that opening both namespaces stays unambiguous.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Restriction of sheaves of modules to a slice of the site preserves homology.** It preserves
finite limits and epimorphisms, which for an additive functor between abelian categories is
enough. -/
theorem preservesHomology_overFunctor (V : C) :
    (SheafOfModules.overFunctor.{w} R V).PreservesHomology := by
  let F := SheafOfModules.overFunctor.{w} R V
  let : PreservesFiniteLimits F := LocalCokernel.overFunctor_preservesFiniteLimits V
  let : F.PreservesEpimorphisms := LocalCokernel.overFunctor_preservesEpimorphisms V
  exact F.preservesHomology_of_preservesEpis_and_kernels

variable {K L : CochainComplex (SheafOfModules.{w} R) ℤ}

/-- **The degreewise restriction of a quasi-isomorphism to a slice of the site is a
quasi-isomorphism.** Restriction preserves homology, and `HomologicalComplex`
`.quasiIso_map_of_preservesHomology` is that implication for an arbitrary additive functor
preserving homology.

The restriction functor appearing here is the one
`AlgebraicGeometry.RingedSite.restrictComplex` is defined by, so this is also the statement for
that spelling. It is a theorem and not an instance, as
`Stacks.SheafOfModules.preservesHomology_overFunctor` is: instance search would have to produce
`PreservesHomology` for the restriction functor, which is itself only a theorem, so a consumer
introduces this one as a term. -/
theorem quasiIso_overFunctor_mapHomologicalComplex_map (V : C) (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso (((SheafOfModules.overFunctor.{w} R V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) :=
  let := preservesHomology_overFunctor (R := R) V
  inferInstance

/-- **The restriction of a homology map is the homology map of the restriction.** If the
degreewise restriction of `φ` to the slice over `V` is a quasi-isomorphism, then the restriction
to that slice of the degree-`n` homology map of `φ` is invertible.

The comparison `CategoryTheory.ShortComplex.mapHomologyIso` for the exact restriction functor
identifies the two, and its naturality turns the hypothesis into the conclusion. -/
theorem isIso_overFunctor_map_homologyMap (V : C) (φ : K ⟶ L)
    (hφ : QuasiIso (((SheafOfModules.overFunctor.{w} R V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)) (n : ℤ) :
    IsIso ((SheafOfModules.overFunctor.{w} R V).map (HomologicalComplex.homologyMap φ n)) := by
  let F := SheafOfModules.overFunctor.{w} R V
  let : F.PreservesHomology := preservesHomology_overFunctor V
  have hmid : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map
      ((HomologicalComplex.shortComplexFunctor (SheafOfModules.{w} R)
        (ComplexShape.up ℤ) n).map φ))) := by
    rw [← ShortComplex.quasiIso_iff]
    exact (quasiIsoAt_iff
      (((SheafOfModules.overFunctor.{w} R V).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) n).1 (hφ.quasiIsoAt n)
  have hnat := ShortComplex.mapHomologyIso_hom_naturality (F := F)
    (φ := (HomologicalComplex.shortComplexFunctor (SheafOfModules.{w} R)
      (ComplexShape.up ℤ) n).map φ)
  have h2 : IsIso ((((HomologicalComplex.shortComplexFunctor (SheafOfModules.{w} R)
      (ComplexShape.up ℤ) n).obj K).mapHomologyIso F).hom ≫
        F.map (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor
          (SheafOfModules.{w} R) (ComplexShape.up ℤ) n).map φ))) := by
    rw [← hnat]
    infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (Iso.isIso_hom _) h2

/-- **Quasi-isomorphy of complexes of sheaves of modules is local on the site.** Let `V : ι → C`
be a family of objects covering the final object of the site. A morphism of cochain complexes of
`R`-modules whose degreewise restriction to the slice over each `V i` is a quasi-isomorphism is
itself a quasi-isomorphism.

Quasi-isomorphy is invertibility of every homology map; restriction to a slice preserves
homology, so the hypothesis says that each homology map of `φ` is invertible over each member of
the family, and invertibility of a morphism of sheaves of modules is local. -/
theorem quasiIso_of_coversTop {ι : Type*} {V : ι → C} (hV : J.CoversTop V) (φ : K ⟶ L)
    (hφ : ∀ i, QuasiIso (((SheafOfModules.overFunctor.{w} R (V i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV _
    fun i => isIso_overFunctor_map_homologyMap (V i) φ (hφ i) n

end Stacks.SheafOfModules

end
