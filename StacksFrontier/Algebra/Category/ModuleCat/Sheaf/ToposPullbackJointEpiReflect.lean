module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFactorizationIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackJointEpi

/-! # The factorization-to-relation epimorphism is reflected by an exact inverse image

Let `Φ : Sh(K, Type) ⥤ Sh(J, Type)` preserve finite limits and let `M` be a sheaf of modules over a
sheaf of rings `R` on `K` with commuting sections. If the factorization-to-relation morphism of the
inverse images `Φ R` and `Φ M` (Stacks 08FC part (2)) is an epimorphism, then so is the inverse
image under `Φ` of the factorization-to-relation morphism of `R` and `M`. This is the converse of
`Stacks.Sheaves.ToposPullback.epi_sigmaDesc_factorizationToRelation_map`.

## Main results

* `Stacks.Sheaves.ToposPullback.epi_map_sigmaDesc_factorizationToRelation`: **epimorphy of the
  factorization-to-relation morphism of the inverse images gives epimorphy of the inverse image
  of the factorization-to-relation morphism.**

## References

* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 0DH3](https://stacks.math.columbia.edu/tag/0DH3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
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
  [HasCoproduct (fun l : ℕ => factorizationSheaf R M n l)]
  [HasCoproduct (fun l : ℕ => Φ.obj (factorizationSheaf R M n l))]
  [HasCoproduct (fun l : ℕ => factorizationSheaf (pullbackRingSheaf J Φ R)
    (pullbackModuleObj J Φ R M) n l)]

include hc in
/-- **Epimorphy of the factorization-to-relation morphism of the inverse images gives epimorphy of
the inverse image of the factorization-to-relation morphism.** The converse of
`Stacks.Sheaves.ToposPullback.epi_sigmaDesc_factorizationToRelation_map`. -/
theorem epi_map_sigmaDesc_factorizationToRelation
    [PreservesColimit (Discrete.functor (fun l : ℕ => factorizationSheaf R M n l)) Φ]
    (h : Epi (Sigma.desc (fun l : ℕ =>
      factorizationToRelation (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l
        (pullback_sections_mul_comm J Φ hc)))) :
    Epi (Φ.map (Sigma.desc (fun l : ℕ => factorizationToRelation R M n l hc))) := by
  have hrhs : Epi (Sigma.desc (fun l : ℕ => factorizationSheafComparison J Φ R M n l ≫
      factorizationToRelation (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l
        (pullback_sections_mul_comm J Φ hc))) := by
    rw [sigmaDesc_comp_eq J Φ R M n hc]
    refine epi_comp' ?_ h
    have hiso : ∀ l : ℕ, Epi (factorizationSheafComparison J Φ R M n l) :=
      fun l => IsIso.epi_of_iso _
    have hmap : Epi (CategoryTheory.Limits.Sigma.map
        (fun l : ℕ => factorizationSheafComparison J Φ R M n l)) :=
      CategoryTheory.Limits.Sigma.map_epi _
    exact hmap
  rw [← sigmaComparison_comp_map_sigmaDesc J Φ R M n hc] at hrhs
  have h2 : Epi (Φ.map (Sigma.desc (fun l : ℕ => factorizationToRelation R M n l hc)) ≫
      (relationSheafIsoPullback J Φ R M n).inv) :=
    epi_of_epi (CategoryTheory.Limits.sigmaComparison Φ
      (fun l : ℕ => factorizationSheaf R M n l)) _
  have h3 : Epi ((Φ.map (Sigma.desc (fun l : ℕ => factorizationToRelation R M n l hc)) ≫
        (relationSheafIsoPullback J Φ R M n).inv) ≫
      (relationSheafIsoPullback J Φ R M n).hom) :=
    epi_comp' h2 (IsIso.epi_of_iso _)
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h3
  exact h3

end Stacks.Sheaves.ToposPullback

end
