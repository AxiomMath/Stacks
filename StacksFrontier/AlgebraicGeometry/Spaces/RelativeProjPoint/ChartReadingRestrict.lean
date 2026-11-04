module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.RestrictionDatum
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs

/-!
# The restriction datum of Stacks 084A on chart readings

In Situation 0849 the restriction datum of Stacks 084A
(`AlgebraicGeometry.Space.RelativeProjSituation.gradedAlgebraRestriction`) identifies, along a
morphism `τ : T' ⟶ T` of test objects and scheme points `v`, `v' = v ∘ τ`, the restriction
`(v'^*𝒜)` with the inverse image `τ^*(v^*𝒜)` by
`AlgebraicGeometry.Space.RelativeProjSituation.pointRestrict`.  This file reads that
identification on the global sections given by the chart readings
`AlgebraicGeometry.Space.chartOpenReading`: for a morphism `k : V' ⟶ V` of étale charts of `X`
and a section `a` of `𝒜_n` over `V`, the restriction map sends the reading of `a|_{V'}` to the
pullback along `τ` of the reading of `a`.

## Main results

* `AlgebraicGeometry.Space.pointComparison_app_val_app_pullbackSectionsHom`: the comparison
  `τ^*(v^*𝒜) ⟶ v'^*𝒜` on the pullback of a global section is the restriction map.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointRestrict_app_val_app_chartOpenReading`:
  **the restriction datum carries the reading of `a|_{V'}` to the pullback of the reading of
  `a`**.

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange (pullbackSectionsHom le_preimage_top
  pullbackSectionsHom_top)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **The comparison of restricted algebras on the pullback of a global section is the
restriction map.**  The comparison `τ^*(f^*𝒜) ⟶ (f ∘ τ)^*𝒜` is the transpose of the restriction
map `f^*𝒜 ⟶ τ_*((f ∘ τ)^*𝒜)`, and the pullback of a global section is the unit applied to it. -/
theorem pointComparison_app_val_app_pullbackSectionsHom
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1)
    (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ)
    (a : ((zariskiReading T (etalePointAlgebra A T f)).piece n).val.obj (op ⊤)) :
    ((pointComparison A τ f f' hf).app n).val.app (op ⊤)
        (pullbackSectionsHom ((BigFppfOver.toScheme B S hS).map τ)
          ((zariskiReading T (etalePointAlgebra A T f)).piece n) ⊤ ⊤ (le_preimage_top _ ⊤) a) =
      ((pointRestriction A τ f f' hf).app n).val.app (op ⊤) a := by
  have h := (homEquiv_pointComparison_app A τ f f' hf n).symm.trans
    (Adjunction.homEquiv_unit _ _ _ _)
  refine (congrArg _ (pullbackSectionsHom_top ((BigFppfOver.toScheme B S hS).map τ)
    ((zariskiReading T (etalePointAlgebra A T f)).piece n) a)).trans ?_
  exact (congrArg (fun m => m.val.app (op ⊤) a) h).symm

namespace RelativeProjSituation

variable (t : RelativeProjSituation.{u, u})

/-- **The restriction datum of Stacks 084A on chart readings.**  For a morphism `k : V' ⟶ V` of
étale charts of `X`, with underlying `τ : T' ⟶ T`, and a section `a` of `𝒜_n` over `V`, the
restriction map `(v'^*𝒜)_n ⟶ τ^*(v^*𝒜)_n` of the restriction datum sends the reading of `a|_{V'}`
over `T'` to the pullback along `τ` of the reading of `a` over `T`. -/
theorem pointRestrict_app_val_app_chartOpenReading
    {V V' : SmallEtale t.site t.base t.containsBase t.space.1} (k : V' ⟶ V) (n : ℤ)
    (a : (t.algebra.piece n).val.obj (op V)) :
    ((pointRestrict k.hom.left V.1.hom V'.1.hom (CostructuredArrow.w k.hom)).app n).val.app
        (op ⊤) (chartOpenReading t.algebra V' ⊤ n ((t.algebra.piece n).val.map k.op a)) =
      pullbackSectionsHom ((BigFppfOver.toScheme t.site t.base t.containsBase).map k.hom.left)
        ((zariskiReading V.1.left (etalePointAlgebra t.algebra V.1.left V.1.hom)).piece n) ⊤ ⊤
        (le_preimage_top _ ⊤) (chartOpenReading t.algebra V ⊤ n a) := by
  have e1 := pointRestriction_chartOpenReading t.algebra n k ⊤ a
  have e2 := pointComparison_app_val_app_pullbackSectionsHom t.algebra k.hom.left V.1.hom
    V'.1.hom (CostructuredArrow.w k.hom) n (chartOpenReading t.algebra V ⊤ n a)
  have e3 := congrArg (fun m => m.val.app (op ⊤)
      (pullbackSectionsHom ((BigFppfOver.toScheme t.site t.base t.containsBase).map k.hom.left)
        ((zariskiReading V.1.left (etalePointAlgebra t.algebra V.1.left V.1.hom)).piece n) ⊤ ⊤
        (le_preimage_top _ ⊤) (chartOpenReading t.algebra V ⊤ n a)))
    (@IsIso.hom_inv_id _ _ _ _ _
      (isIso_pointComparisonUnital_app k.hom.left V.1.hom V'.1.hom (CostructuredArrow.w k.hom) n))
  refine Eq.trans ?_ e3
  refine congrArg (fun z => ((pointRestrict k.hom.left V.1.hom V'.1.hom
    (CostructuredArrow.w k.hom)).app n).val.app (op ⊤) z) ?_
  exact (e1.symm.trans e2.symm)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
