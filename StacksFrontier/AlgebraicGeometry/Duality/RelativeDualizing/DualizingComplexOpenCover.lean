module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingBaseChange.FibreDualizingCharts

/-!
# Being a dualizing complex is local on an open cover

An object `K` of `D(𝒪_X)` on a locally Noetherian scheme is a dualizing complex as soon as its
restriction to each member of an open cover is one: the affine opens of the members form an affine
open cover of `X`, and [Stacks, Tag 0A86] applies. This is the sense in which "being a dualizing
complex on a scheme is a local property" in [Stacks, Tag 0AU5].

## Main results

* `Stacks.Duality.hasDualizingModelOn_opensRange_fromSpec_ι` — a dualizing model of `K|_U` on an
  affine open `V ⊆ U` is one of `K` on the image of `V` in `X`.
* `Stacks.Duality.isDualizingComplex_of_isDualizingComplex_restrict` — `K` is dualizing when its
  restrictions to the members of an open cover are.

## References

* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **A dualizing model of a restriction is a dualizing model.** If `K|_U` carries a dualizing
model on an affine open `V` of `U`, then `K` carries one on the image of `V` in `X`. -/
theorem hasDualizingModelOn_opensRange_fromSpec_ι (K : DerivedCategory X.Modules) (U : X.Opens)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V)
    (h : HasDualizingModelOn ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) V hV) :
    HasDualizingModelOn K (hV.fromSpec ≫ U.ι).opensRange (isAffineOpen_opensRange _) := by
  have : IsNoetherianRing Γ(U.toScheme, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let := HasDerivedCategory.standard V.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(U.toScheme, V))
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  refine hasDualizingModelOn_opensRange (hV.fromSpec ≫ U.ι) K ω hω ?_
  let Φ : Scheme.Modules.restrictFunctor (hV.fromSpec ≫ U.ι) ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor V.ι ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.inv :=
    Scheme.Modules.restrictFunctorComp hV.fromSpec U.ι ≪≫
      Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι)
  let i₁ := (Functor.mapDerivedCategoryCongr Φ).app K
  let i₂ := ((Functor.mapDerivedCategoryCompIsoOfCompIso
      (Iso.refl (Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.restrictFunctor V.ι ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.inv))).app K).symm
  let i₃ := ((Functor.mapDerivedCategoryCompIsoOfCompIso
      (Iso.refl (Scheme.Modules.restrictFunctor V.ι ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.inv))).app
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K)).symm
  let i₄ := (Scheme.Modules.restrictFunctor hV.isoSpec.inv).mapDerivedCategory.mapIso e
  let i₅ := (Functor.mapDerivedCategoryCompIsoOfCompIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ hV.restrictIsoSpecCompIso ≪≫
      Functor.rightUnitor (tilde.functor Γ(U.toScheme, V)))).app ω
  exact i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅

/-- **Being a dualizing complex is local** ([Stacks, Tag 0A86] read on an open cover). If the
restriction of `K ∈ D(𝒪_X)` to every member of an open cover of `X` is a dualizing complex, then
`K` is a dualizing complex. -/
theorem isDualizingComplex_of_isDualizingComplex_restrict {K : DerivedCategory X.Modules}
    {ι : Type*} (U : ι → X.Opens) (hcov : ⨆ i, U i = ⊤)
    (h : ∀ i, IsDualizingComplex ((Scheme.Modules.restrictFunctor (U i).ι).mapDerivedCategory.obj
      K)) :
    IsDualizingComplex K := by
  refine isDualizingComplex_of_hasDualizingModelOn_cover
    (ι := Σ i, {V : (U i).toScheme.Opens // IsAffineOpen V})
    (fun a => (a.2.2.fromSpec ≫ (U a.1).ι).opensRange)
    (fun _ => isAffineOpen_opensRange _)
    (top_unique fun x _ => ?_)
    (fun a => hasDualizingModelOn_opensRange_fromSpec_ι K (U a.1) a.2.1 a.2.2 (h a.1 a.2.1 a.2.2))
  have hx : x ∈ ⨆ i, U i := hcov ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let y : (U i).toScheme := ⟨x, hi⟩
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    (U i).toScheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV⟩⟩, ?_⟩
  obtain ⟨z, hz⟩ : y ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  exact ⟨z, by simp [Scheme.Hom.comp_base, hz, y]⟩

end Stacks.Duality

end
