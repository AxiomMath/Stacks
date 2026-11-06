module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Product

/-!
# A coproduct with all but finitely many factors killed is the product

The source's proof of the generic-point decomposition opens with the sentence *"Observe that a
locally finite direct sum of sheaves of modules is equal to the product"*. This file provides the
two inputs that sentence needs: the comparison morphism from a coproduct to a product becomes
invertible under any functor that kills all but finitely many of the factors, and restriction to
an open subscheme is such a functor for the generic-point family, because it preserves both the
coproduct and the product.

## Main results

* `Stacks.AlgebraicGeometry.GenericPointCoproduct.isIso_map_coproductToProduct_of_finite`: a
  functor between a category with zero morphisms and a preadditive category carries the canonical
  morphism `∐ F ⟶ ∏ᶜ F` to an isomorphism as soon as it preserves the coproduct and the product
  and all but finitely many of the images `G.obj (F i)` are zero.
* `Stacks.AlgebraicGeometry.GenericPointCoproduct.isIso_piComparison_restrictFunctor` and
  `preservesLimit_discrete_restrictFunctor`: restriction to an open subscheme preserves the
  product of a family of `𝒪_X`-modules.
* `Stacks.AlgebraicGeometry.GenericPointCoproduct.isZero_of_subsingleton_sections`: a sheaf of
  modules with no sections anywhere is a zero object.

## Implementation notes

`Stacks.AlgebraicGeometry.NormalizationQuotient.map_coproductToProduct_isIso` is the same
statement under the hypothesis that *at most one* image is nonzero, which is the shape the
skyscraper decomposition of a closed discrete subset needs. The generic-point family is not of
that shape: an open set may contain several generic points, and only finitely many. The inverse
is therefore the finite sum `∑ G(π i) ≫ G(ι i)` over the nonzero indices rather than a single
projection, so preadditivity of the target is used where the earlier lemma needed only a zero
object. Both composites are checked one leg at a time against the preserved colimit and limit, so
the zero indices contribute nothing and no decidability of the vanishing locus is required.

Restriction to an open subscheme preserves coproducts for free, since it is a left adjoint by
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. It preserves products too, but not by
instance search: the comparison morphism is checked on sections instead, exactly as in
`Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isIso_restrictPiLift`, whose index-dropping
this specialises away.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointCoproduct

/-! ### The comparison of a coproduct with a product under a functor -/

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [Preadditive D]

/-- A functor sends the canonical morphism from a coproduct to a product to an isomorphism as
soon as it kills all but finitely many of the factors. -/
theorem isIso_map_coproductToProduct_of_finite {ι : Type*} [DecidableEq ι] (F : ι → C)
    [HasProduct F] [HasCoproduct F] (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [PreservesLimit (Discrete.functor F) G] [PreservesColimit (Discrete.functor F) G]
    (hfin : {i | ¬ IsZero (G.obj (F i))}.Finite) :
    IsIso (G.map (Sigma.desc (Pi.ι F))) := by
  classical
  have hS : ∀ i ∉ hfin.toFinset, IsZero (G.obj (F i)) := by
    intro i hi
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
  have hc := isColimitOfPreserves G (colimit.isColimit (Discrete.functor F))
  have hl := isLimitOfPreserves G (limit.isLimit (Discrete.functor F))
  have hdiag : ∀ j : ι, G.map (Sigma.ι F j) ≫ G.map (Sigma.desc (Pi.ι F)) ≫ G.map (Pi.π F j)
      = 𝟙 (G.obj (F j)) := by
    intro j
    rw [← G.map_comp, ← G.map_comp, ← Category.assoc, Sigma.ι_desc, Pi.ι_π_eq_id, G.map_id]
  have hoff : ∀ i j : ι, i ≠ j →
      G.map (Sigma.ι F j) ≫ G.map (Sigma.desc (Pi.ι F)) ≫ G.map (Pi.π F i) = 0 := by
    intro i j hij
    rw [← G.map_comp, ← G.map_comp, ← Category.assoc, Sigma.ι_desc,
      Pi.ι_π_of_ne F (Ne.symm hij), G.map_zero]
  refine ⟨⟨∑ i ∈ hfin.toFinset, G.map (Pi.π F i) ≫ G.map (Sigma.ι F i), ?_, ?_⟩⟩
  · refine hc.hom_ext ?_
    rintro ⟨j⟩
    by_cases hj : j ∈ hfin.toFinset
    · show G.map (Sigma.ι F j) ≫ _ = G.map (Sigma.ι F j) ≫ _
      rw [Category.comp_id]
      simp only [Preadditive.comp_sum]
      rw [Finset.sum_eq_single_of_mem (f := fun i ↦ G.map (Sigma.ι F j) ≫
          G.map (Sigma.desc (Pi.ι F)) ≫ G.map (Pi.π F i) ≫ G.map (Sigma.ι F i)) j hj
          fun i _ hij ↦ by
            rw [← Category.assoc (G.map (Sigma.desc (Pi.ι F))) (G.map (Pi.π F i)),
              ← Category.assoc, hoff i j hij, Limits.zero_comp],
        ← Category.assoc (G.map (Sigma.desc (Pi.ι F))) (G.map (Pi.π F j)),
        ← Category.assoc, hdiag j, Category.id_comp]
    · exact (hS j hj).eq_of_src _ _
  · refine hl.hom_ext ?_
    rintro ⟨j⟩
    by_cases hj : j ∈ hfin.toFinset
    · show _ ≫ G.map (Pi.π F j) = _ ≫ G.map (Pi.π F j)
      rw [Category.id_comp]
      simp only [Preadditive.sum_comp, Category.assoc]
      rw [Finset.sum_eq_single_of_mem (f := fun i ↦ G.map (Pi.π F i) ≫ G.map (Sigma.ι F i) ≫
          G.map (Sigma.desc (Pi.ι F)) ≫ G.map (Pi.π F j)) j hj
          fun i _ hij ↦ by rw [hoff j i (Ne.symm hij), Limits.comp_zero],
        hdiag j, Category.comp_id]
    · exact (hS j hj).eq_of_tgt _ _

/-! ### Restriction to an open subscheme preserves products -/

variable {X : Scheme.{u}} {ι : Type u}

/-- The restriction to an open set of a product of `𝒪_X`-modules is the product of the
restrictions. The sections of a product over an open set are the product of the sections of the
factors, and the sections of a restriction over an open set of the subscheme are the sections of
the module over its image, so both sides have the same sections and the comparison morphism is
the identification between them. -/
theorem isIso_piComparison_restrictFunctor (V : X.Opens) (F : ι → X.Modules) :
    IsIso (piComparison (Scheme.Modules.restrictFunctor V.ι) F) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  have hL := MeromorphicQuasicoherent.bijective_piApp F (V.ι ''ᵁ W)
  have hR := MeromorphicQuasicoherent.bijective_piApp
    (fun i ↦ (Scheme.Modules.restrictFunctor V.ι).obj (F i)) W
  refine (Function.Bijective.of_comp_iff' hR _).1 ?_
  have key : ∀ x i,
      (Pi.π (fun b ↦ (Scheme.Modules.restrictFunctor V.ι).obj (F b)) i).app W
        ((piComparison (Scheme.Modules.restrictFunctor V.ι) F).app W x) =
      (Pi.π F i).app (V.ι ''ᵁ W) x := fun x i ↦ by
    rw [MeromorphicQuasicoherent.comp_app_apply, piComparison, Pi.lift_comp_π,
      MeromorphicQuasicoherent.restrictFunctor_map_app]
    rfl
  exact (congrArg Function.Bijective (funext₂ key)).mpr hL

/-- Restriction to an open subscheme preserves the product of a family of `𝒪_X`-modules. -/
theorem preservesLimit_discrete_restrictFunctor (V : X.Opens) (F : ι → X.Modules) :
    PreservesLimit (Discrete.functor F) (Scheme.Modules.restrictFunctor V.ι) :=
  have := isIso_piComparison_restrictFunctor V F
  PreservesProduct.of_iso_comparison _ F

/-! ### A sheaf of modules with no sections -/

/-- A sheaf of modules all of whose groups of sections are trivial is a zero object. -/
theorem isZero_of_subsingleton_sections {Y : Scheme.{u}} (M : Y.Modules)
    (h : ∀ U : Y.Opens, Subsingleton Γ(M, U)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  rw [Scheme.Modules.Hom.zero_app]
  ext x
  exact (h U).elim _ _

end Stacks.AlgebraicGeometry.GenericPointCoproduct

end
