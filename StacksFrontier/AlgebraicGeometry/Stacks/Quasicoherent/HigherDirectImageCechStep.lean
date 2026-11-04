module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerreFirstQuadrant
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageRuleSpectralSequenceAbutment
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.ModuleHigherDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.EtaleModuleSmoothCoveringSpectralSequence

/-!
# The Čech step of the proof of Stacks 076Z

Let `M` be a rule in the sense of **Stacks 076Z** which cuts out a weak Serre subcategory of
`Mod(𝒴_étale, 𝒪_𝒴)` at every algebraic stack `𝒴` (hypothesis (1)). Let `c : 𝒰 ⟶ 𝒳` be a
`1`-morphism of algebraic stacks which is representable by algebraic spaces, surjective and
smooth, and let `f : 𝒳 ⟶ 𝒴` be a further `1`-morphism. If, for a sheaf of modules `𝓕` on
`𝒳_étale`, every higher direct image `Rᵠ(f ∘ cₚ)_* cₚ⁻¹𝓕` along the terms `cₚ` of the relative
Čech nerve of `c` lies in `M_𝒴`, then so does every `Rⁿf_*𝓕`.

This is the step of the source's proof which is iterated four times: the spectral sequence of
**Stacks 072G** has exactly those terms on its first page, it is first quadrant, and part (4) of
**Stacks 0132** puts its abutment into the weak Serre subcategory.

## Main results

* `AlgebraicGeometry.Stack.StackEtaleModuleRule.mem_higherDirectImage_of_cechPages`.

## Implementation notes

All higher direct images here are those of **Stacks 06WE**,
`AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`, and all inverse images are
`AlgebraicGeometry.Stack.modulePullback`; the spectral sequence of
`Stacks.RelativeCech.ModulePushforwardSpectralSequenceData` is stated with the direct and inverse
images of the relative Čech construction instead, and is converted by
`AlgebraicGeometry.Stack.moduleHigherDirectImageIso` and
`AlgebraicGeometry.Stack.relativeCechModuleInverseImage_eq_modulePullback_anyUniverse`.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u t

namespace AlgebraicGeometry.Stack.StackEtaleModuleRule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (c : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)

/-- The structure functor of the degree `n` term of the relative Čech nerve of `c`, over the
strict presentation of `𝒳` by `f`, is fibred in groupoids. -/
theorem isFiberedInGroupoids_cechTerm (n : ℕ) :
    (Stacks.RelativeCech.Tuple.projection
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (CatFiberedInGroupoids.homFunctor c.hom) n ⋙
      CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p).IsFiberedInGroupoids :=
  Stacks.RelativeCech.tupleProjection_comp_isFiberedInGroupoids B S hS _ _ _
    (AlgebraicStacks.isFiberedInGroupoids_strict₂ B S hS c f)
    (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f)
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids
      (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f) rfl) n

/-- **The Čech step of Stacks 076Z.** Let `M` satisfy hypothesis (1) of **Stacks 076Z**, let
`c : 𝒰 ⟶ 𝒳` be representable by algebraic spaces, surjective and smooth, and let `f : 𝒳 ⟶ 𝒴`.
If for a sheaf of modules `𝓕` on `𝒳_étale` every `Rᵠ(f ∘ cₚ)_* cₚ⁻¹𝓕` lies in `M_𝒴`, where
`cₚ` runs over the terms of the relative Čech nerve of `c`, then every `Rⁿf_*𝓕` lies in `M_𝒴`. -/
theorem mem_higherDirectImage_of_cechPages (M : StackEtaleModuleRule B S hS)
    (hserre : IsWeakSerre.{u, t} B S hS M)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS c.hom.hom)
    (hsurj : Stack.IsSurjective B S hS c) (hsmooth : AlgebraicStacks.IsSmooth B S hS c)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f) (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hpage : ∀ p q : ℕ, M 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
        (Stacks.RelativeCech.Tuple.projection
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
            (CatFiberedInGroupoids.homFunctor c.hom) p ⋙
          CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        𝒴.val.val.p (isFiberedInGroupoids_cechTerm B S hS c f p) 𝒴.val.isFiberedInGroupoids
        (Stacks.RelativeCech.Tuple.projection
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
            (CatFiberedInGroupoids.homFunctor c.hom) p ⋙
          CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
        (etaleTopology_le_topology B) q).obj
        ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
          (Stacks.RelativeCech.Tuple.projection
              (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
              (CatFiberedInGroupoids.homFunctor c.hom) p ⋙
            CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_cechTerm B S hS c f p)
          (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f)
          (Stacks.RelativeCech.Tuple.projection
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
            (CatFiberedInGroupoids.homFunctor c.hom) p) rfl (etaleTopology B)
          (etaleTopology_le_topology B)).obj F)).val)
    (n : ℕ) :
    M 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
        (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f) 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
        (etaleTopology_le_topology B) n).obj F).val := by
  obtain ⟨D⟩ := AlgebraicStacks.exists_etaleModuleDirectImageSpectralSequenceData
    B S hS c f hrep hsurj hsmooth F
  let := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  let : Abelian (SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS
      𝒴.val.val.p 𝒴.val.isFiberedInGroupoids SiteKind.etale)) :=
    SheafOfModules.instAbelian.{u + 1, u, u, u + 1} _
  let P : ObjectProperty (SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS
      𝒴.val.val.p 𝒴.val.isFiberedInGroupoids SiteKind.etale)) :=
    toObjectProperty.{u, t} B S hS M 𝒴
  have : P.IsWeakSerreClass := hserre 𝒴
  have habuts : CategoryTheory.SpectralSequence.AbutsTo D.sequence _ := D.abutment
  have key := habuts.prop_of_prop_page_firstQuadrant P le_rfl D.firstQuadrant
    (fun p q => by
      refine P.prop_of_iso (Iso.symm ?_) (hpage p q)
      refine D.pageOneIso p q ≪≫ ?_
      rw [relativeCechModuleInverseImage_eq_modulePullback_anyUniverse]
      exact (moduleHigherDirectImageIso.{u, u + 1, u, u + 1, u} B S hS _ _ _ _ _ _
        SiteKind.etale q).app _) (n : ℤ)
  simp only [show ¬ ((n : ℤ) < 0) by lia, ite_false, Int.toNat_natCast] at key
  exact P.prop_of_iso ((moduleHigherDirectImageIso.{u, u + 1, u, u + 1, u} B S hS _ _ _ _ _ _
    SiteKind.etale n).app F) key

end AlgebraicGeometry.Stack.StackEtaleModuleRule

end
