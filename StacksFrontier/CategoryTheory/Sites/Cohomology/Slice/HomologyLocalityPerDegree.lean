module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality

/-!
# Invertibility of a single homology map is local on the site, degree by degree

Let `R` be a sheaf of rings on a site `(C, J)` and let `φ : K ⟶ L` be a morphism of cochain
complexes of `R`-modules. `Stacks.SheafOfModules.quasiIso_of_coversTop` deduces that `φ` is a
quasi-isomorphism from the restrictions of `φ` to the slices over one family of objects covering
the final object being quasi-isomorphisms. That form fixes the family once and for all, across
every degree.

This file splits the statement by degree. Invertibility of the degree-`n` homology map of `φ`
follows from invertibility of the degree-`n` homology maps of its restrictions to a covering
family, and a *different* family may be used in each degree.

## Main results

* `Stacks.SheafOfModules.isIso_homologyMap_of_coversTop`: one degree, one covering family.
* `Stacks.SheafOfModules.quasiIso_of_coversTop_degreewise`: quasi-isomorphy from a covering
  family chosen separately in each degree.

## Implementation notes

Restriction to a slice is exact, so it takes the degree-`n` homology map of `φ` to the degree-`n`
homology map of the restriction of `φ`, up to the comparison isomorphism
`CategoryTheory.ShortComplex.mapHomologyIso`. That identification is
`Stacks.SheafOfModules.isIso_overFunctor_map_homologyMap`, which is stated from quasi-isomorphy
of the whole restricted morphism; only its degree-`n` part is used, so the degreewise form is
reproved here from `quasiIsoAt_iff_isIso_homologyMap` rather than obtained from it.

The index types of the covering families are allowed to vary with the degree, which is what makes
the statement usable when the family comes from an approximation whose range depends on the
degree.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable {K L : CochainComplex (SheafOfModules.{w} R) ℤ}

/-- **The restriction to a slice of a single homology map of `φ` is the corresponding homology
map of the restriction of `φ`.** If the degree-`n` homology map of the degreewise restriction of
`φ` to the slice over `V` is invertible, then so is the restriction to that slice of the
degree-`n` homology map of `φ`. Nothing is assumed in the other degrees. -/
theorem isIso_overFunctor_map_homologyMap_of_isIso (V : C) (φ : K ⟶ L) (n : ℤ)
    (hφ : IsIso (HomologicalComplex.homologyMap
      (((SheafOfModules.overFunctor.{w} R V).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) n)) :
    IsIso ((SheafOfModules.overFunctor.{w} R V).map (HomologicalComplex.homologyMap φ n)) := by
  let F := SheafOfModules.overFunctor.{w} R V
  let : F.PreservesHomology := preservesHomology_overFunctor V
  let S := HomologicalComplex.shortComplexFunctor (SheafOfModules.{w} R) (ComplexShape.up ℤ) n
  have hmid : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map (S.map φ))) := by
    rw [← ShortComplex.quasiIso_iff]
    exact (quasiIsoAt_iff ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) n).1
      ((quasiIsoAt_iff_isIso_homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
        n).2 hφ)
  have h2 : IsIso (((S.obj K).mapHomologyIso F).hom ≫
      F.map (ShortComplex.homologyMap (S.map φ))) := by
    rw [← ShortComplex.mapHomologyIso_hom_naturality (F := F) (φ := S.map φ)]
    infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ((S.obj K).mapHomologyIso F).isIso_hom h2

/-- **Invertibility of a single homology map of a morphism of complexes of sheaves of modules is
local on the site.** Let `V : ι → C` be a family of objects covering the final object. If the
degree-`n` homology map of the degreewise restriction of `φ` to the slice over each `V i` is
invertible, then the degree-`n` homology map of `φ` is invertible. -/
theorem isIso_homologyMap_of_coversTop {ι : Type t} {V : ι → C} (hV : J.CoversTop V)
    (φ : K ⟶ L) (n : ℤ)
    (hφ : ∀ i, IsIso (HomologicalComplex.homologyMap
      (((SheafOfModules.overFunctor.{w} R (V i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) n)) :
    IsIso (HomologicalComplex.homologyMap φ n) :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV _
    fun i => isIso_overFunctor_map_homologyMap_of_isIso (V i) φ n (hφ i)

/-- **Quasi-isomorphy from a covering family chosen degree by degree.** If for every integer `n`
there is a family of objects covering the final object over each member of which the degree-`n`
homology map of the restriction of `φ` is invertible, then `φ` is a quasi-isomorphism. The family
is allowed to depend on `n`, which `Stacks.SheafOfModules.quasiIso_of_coversTop` does not
permit. -/
theorem quasiIso_of_coversTop_degreewise {ι : ℤ → Type t} {V : (n : ℤ) → ι n → C}
    (hV : ∀ n : ℤ, J.CoversTop (V n)) (φ : K ⟶ L)
    (hφ : ∀ (n : ℤ) (i : ι n), IsIso (HomologicalComplex.homologyMap
      (((SheafOfModules.overFunctor.{w} R (V n i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) n)) :
    QuasiIso φ :=
  (quasiIso_iff φ).2 fun n =>
    (quasiIsoAt_iff_isIso_homologyMap φ n).2
      (isIso_homologyMap_of_coversTop (hV n) φ n (hφ n))

end Stacks.SheafOfModules

end
