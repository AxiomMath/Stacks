module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FactorizationToRelation
public import StacksFrontier.CategoryTheory.Sites.Topos.TypeSheafJointEpi
public import StacksFrontier.CategoryTheory.Sites.Topos.TypeSheafSections
public import Mathlib.CategoryTheory.Sites.Limits

/-! # The inverse image of the factorization-to-relation epimorphism

Let `(C, J)` and `(D, K)` be sites, `Φ : Sh(D) ⥤ Sh(C)` a left exact, colimit-preserving functor
between their categories of sheaves of sets, `R` a sheaf of rings on `(D, K)` with commuting
sections and `M` a sheaf of `R`-modules.  For each `n` the morphisms

`factorizationToRelation R M n l : factorizationSheaf R M n l ⟶ relationSheaf R M n`

assemble, over all ranks `l`, into one morphism out of the coproduct `⨿_l`, and Stacks 08FC part
(2) for `M` says exactly that that morphism is an epimorphism.  This file proves that the
corresponding morphism for the inverse-image sheaf of rings and module of Stacks 03D2 is then an
epimorphism too.

That is the whole categorical content of Stacks 05VD, in the route that avoids Stacks 03CR: the
relation side is carried across by left exactness (the sheaf of relations is a finite limit, see
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackRelationSheaf`), the factorization
side is carried across in the easy direction, the `∃ l` is carried across because `Φ` preserves
coproducts, and epimorphy is carried across because `Φ` has a right adjoint.

## Main results

* `Stacks.Sheaves.ToposPullback.epi_sigmaDesc_factorizationToRelation_map`: the inverse image of
  the factorization-to-relation epimorphism is an epimorphism.

## Implementation notes

**The hypotheses on `Φ` are exactly the three properties of an inverse image that the argument
uses**, stated as instance arguments rather than derived from an adjunction, so that the lemma
applies to any functor with them: left exactness, preservation of the coproduct over `ℕ`, and
preservation of epimorphisms.  For the inverse image of a morphism of topoi all three come from
`CategoryTheory.MorphismOfTopoi.preservesFiniteLimits` and from its adjunction.

**No sheafification hypothesis is needed here.**  Epimorphy is used as epimorphy, not as local
surjectivity, so `HasSheafify` appears only where the two are compared — in
`StacksFrontier.CategoryTheory.Sites.Topos.TypeSheafJointEpi` and
`StacksFrontier.CategoryTheory.Sites.Topos.TypeSheafSections`, which this file imports for the
callers' benefit but does not use itself.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf
open Stacks.Sheaves.RelationSheaf

universe ww ww' vv uu vv' uu'

namespace Stacks.Sheaves.ToposPullback

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteLimits Φ]
  (R : Sheaf K RingCat.{ww'}) (M : SheafOfModules.{ww'} R) (n : ℕ)
  (hc : ∀ (Y : Dᵒᵖ) (x y : (sectionsFunctor K Y).obj (ringSheaf R)), x * y = y * x)

section

variable [HasCoproduct (fun l : ℕ => factorizationSheaf R M n l)]
  [HasCoproduct (fun l : ℕ => Φ.obj (factorizationSheaf R M n l))]
  [HasCoproduct (fun l : ℕ => factorizationSheaf (pullbackRingSheaf J Φ R)
    (pullbackModuleObj J Φ R M) n l)]

omit [HasCoproduct (fun l : ℕ => factorizationSheaf (pullbackRingSheaf J Φ R)
  (pullbackModuleObj J Φ R M) n l)] in
include hc in
/-- The coproduct comparison intertwines the inverse image of the factorization-to-relation
morphism with the factorization-to-relation morphism of the inverse images, after the
rank-by-rank comparison on the source. -/
theorem sigmaComparison_comp_map_sigmaDesc :
    Limits.sigmaComparison Φ (fun l : ℕ => factorizationSheaf R M n l) ≫
        (Φ.map (Limits.Sigma.desc (fun l : ℕ => factorizationToRelation R M n l hc)) ≫
          (relationSheafIsoPullback J Φ R M n).inv) =
      Limits.Sigma.desc (fun l : ℕ => factorizationSheafComparison J Φ R M n l ≫
        factorizationToRelation (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l
          (pullback_sections_mul_comm J Φ hc)) := by
  refine Limits.Sigma.hom_ext (f := fun l : ℕ => Φ.obj (factorizationSheaf R M n l))
    _ _ (fun l => ?_)
  rw [← Category.assoc, Limits.ι_comp_sigmaComparison, ← Category.assoc, ← Φ.map_comp,
    Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc,
    factorizationSheafComparison_comp_factorizationToRelation J Φ R M n l hc]

omit [HasCoproduct (fun l : ℕ => factorizationSheaf R M n l)] in
include hc in
/-- Descending along the coproduct one rank at a time factors through the coproduct of the
rank-by-rank comparisons. -/
theorem sigmaDesc_comp_eq :
    Limits.Sigma.desc (fun l : ℕ => factorizationSheafComparison J Φ R M n l ≫
        factorizationToRelation (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l
          (pullback_sections_mul_comm J Φ hc)) =
      Limits.Sigma.desc (fun l : ℕ => factorizationSheafComparison J Φ R M n l ≫
          Limits.Sigma.ι (fun l : ℕ => factorizationSheaf (pullbackRingSheaf J Φ R)
            (pullbackModuleObj J Φ R M) n l) l) ≫
        Limits.Sigma.desc (fun l : ℕ =>
          factorizationToRelation (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l
            (pullback_sections_mul_comm J Φ hc)) := by
  refine Limits.Sigma.hom_ext (f := fun l : ℕ => Φ.obj (factorizationSheaf R M n l))
    _ _ (fun l => ?_)
  rw [Limits.Sigma.ι_comp_desc, ← Category.assoc, Limits.Sigma.ι_comp_desc, Category.assoc,
    Limits.Sigma.ι_comp_desc]

include hc in
/-- **The inverse image of the factorization-to-relation epimorphism is an epimorphism.**
Stacks 08FC part (2) for a sheaf of modules is the epimorphy of the left-hand side; this says
that it passes to the inverse image, which is the categorical content of Stacks 05VD. -/
theorem epi_sigmaDesc_factorizationToRelation_map
    [Limits.PreservesColimit
      (Discrete.functor (fun l : ℕ => factorizationSheaf R M n l)) Φ]
    [Φ.PreservesEpimorphisms]
    (h : Epi (Limits.Sigma.desc (fun l : ℕ => factorizationToRelation R M n l hc))) :
    Epi (Limits.Sigma.desc (fun l : ℕ =>
      factorizationToRelation (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l
        (pullback_sections_mul_comm J Φ hc))) := by
  have hmap : Epi (Φ.map (Limits.Sigma.desc
      (fun l : ℕ => factorizationToRelation R M n l hc))) := Φ.map_epi _
  have hcomp : Epi (Limits.sigmaComparison Φ (fun l : ℕ => factorizationSheaf R M n l) ≫
      (Φ.map (Limits.Sigma.desc (fun l : ℕ => factorizationToRelation R M n l hc)) ≫
        (relationSheafIsoPullback J Φ R M n).inv)) := by
    have : Epi (Limits.sigmaComparison Φ (fun l : ℕ => factorizationSheaf R M n l)) :=
      IsIso.epi_of_iso _
    infer_instance
  rw [sigmaComparison_comp_map_sigmaDesc J Φ R M n hc,
    sigmaDesc_comp_eq J Φ R M n hc] at hcomp
  exact epi_of_epi (Limits.Sigma.desc (fun l : ℕ => factorizationSheafComparison J Φ R M n l ≫
      Limits.Sigma.ι (fun l : ℕ => factorizationSheaf (pullbackRingSheaf J Φ R)
        (pullbackModuleObj J Φ R M) n l) l))
    (Limits.Sigma.desc (fun l : ℕ =>
      factorizationToRelation (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l
        (pullback_sections_mul_comm J Φ hc)))

end

end Stacks.Sheaves.ToposPullback

end
