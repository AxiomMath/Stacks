module

public import StacksFrontier.Algebra.DGA.Abelian.KernelCokernel
public import StacksFrontier.Algebra.DGA.Abelian.ProductCoproduct
import all StacksFrontier.Algebra.DGA.Abelian.ProductCoproduct

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The category of differential graded modules is abelian, complete and cocomplete

## Main results

* `differentialGradedModule_abelian`: the category `Mod_(A, d)` is abelian.
* `differentialGradedModule_hasLimits`: the category `Mod_(A, d)` has all small limits.
* `differentialGradedModule_hasColimits`: the category `Mod_(A, d)` has all small colimits.

## References

* [Stacks Project, Tag 09JJ](https://stacks.math.columbia.edu/tag/09JJ)
-/

open CategoryTheory CategoryTheory.Limits

universe u v w w' w'' t

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

namespace DifferentialGradedModule

/-- The category `Mod_(A, d)` has all products indexed by types in the universe of the carriers. -/
instance instHasProducts : HasProducts.{w} (DifferentialGradedModule.{u, v, w} A) := by
  intro I
  have hP : ∀ (f : I → DifferentialGradedModule.{u, v, w} A), HasProduct f := by
    intro f
    apply HasLimit.mk
    refine ⟨Fan.mk (prodObj f) (prodπ f), ?_⟩
    refine Fan.IsLimit.mk _ (fun s ↦ prodLift f (fun i ↦ s.proj i)) ?_ ?_
    · intro s j
      apply Hom.ext
      ext t
      rfl
    · intro s m hm
      apply Hom.ext
      apply LinearMap.ext
      intro t
      apply Subtype.ext
      funext i
      exact LinearMap.congr_fun (congrArg Hom.toFun (hm i)) t
  exact ⟨fun {F} ↦ hasLimit_of_iso (Discrete.natIsoFunctor (F := F)).symm⟩

/-- The category `Mod_(A, d)` has all coproducts indexed by types in the universe of the
carriers. -/
instance instHasCoproducts : HasCoproducts.{w} (DifferentialGradedModule.{u, v, w} A) := by
  intro I
  have hC : ∀ (f : I → DifferentialGradedModule.{u, v, w} A), HasCoproduct f := by
    intro f
    apply HasColimit.mk
    refine ⟨Cofan.mk (coprodObj f) (coprodι f), ?_⟩
    refine Cofan.IsColimit.mk _ (fun t ↦ coprodDesc f (fun i ↦ t.inj i)) ?_ ?_
    · intro t j
      apply Hom.ext
      ext y
      change coprodDescent0 f (fun i ↦ t.inj i) ((coprodι f j).toFun y) = (t.inj j).toFun y
      exact coprodDescent0_incl f (fun i ↦ t.inj i) j y
    · intro t m hm
      apply Hom.ext
      ext x
      classical
      let w : ↥(coprodSub f) := x
      set s := (coprodSub_finite f (w : ∀ j, (f j).M) w.2).toFinset with hs_def
      have hsx : {i | (w : ∀ j, (f j).M) i ≠ 0} ⊆ (↑s : Set I) := by
        rw [hs_def, Set.Finite.coe_toFinset]
      have hrepr := coprodSub_repr f w s hsx
      change m.toFun w = (coprodDesc f (fun i ↦ t.inj i)).toFun w
      rw [hrepr, map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hmi := LinearMap.congr_fun (congrArg Hom.toFun (hm i)) ((w : ∀ j, (f j).M) i)
      change m.toFun ((coprodι f i).toFun _) = (coprodDesc f (fun i ↦ t.inj i)).toFun
          ((coprodι f i).toFun _)
      rw [coprodDesc_toFun_apply, coprodDescent0_incl f (fun i ↦ t.inj i) i]
      exact hmi
  exact ⟨fun {F} ↦ hasColimit_of_iso (Discrete.natIsoFunctor (F := F))⟩

end DifferentialGradedModule

/-- The category `Mod_(A, d)` of right differential graded `A`-modules is abelian. -/
@[stacks 09JJ "abelian"]
theorem differentialGradedModule_abelian (A : DifferentialGradedAlgebra.{u, v} R) :
    Nonempty (Abelian (DifferentialGradedModule.{u, v, w} A)) := by
  have : HasFiniteProducts (DifferentialGradedModule.{u, v, w} A) :=
    hasFiniteProducts_of_hasProducts.{w} _
  have : HasEqualizers (DifferentialGradedModule.{u, v, w} A) :=
    Preadditive.hasEqualizers_of_hasKernels
  exact ⟨Abelian.mk⟩

/-- The category `Mod_(A, d)` of right differential graded `A`-modules has all limits indexed by
categories in the universe `w` of the carriers. -/
@[stacks 09JJ "limits"]
theorem differentialGradedModule_hasLimits (A : DifferentialGradedAlgebra.{u, v} R) :
    HasLimitsOfSize.{w, w} (DifferentialGradedModule.{u, v, w} A) := by
  have : HasEqualizers (DifferentialGradedModule.{u, v, w} A) :=
    Preadditive.hasEqualizers_of_hasKernels
  exact has_limits_of_hasEqualizers_and_products

/-- The category `Mod_(A, d)` of right differential graded `A`-modules has all colimits indexed by
categories in the universe `w` of the carriers. -/
@[stacks 09JJ "colimits"]
theorem differentialGradedModule_hasColimits (A : DifferentialGradedAlgebra.{u, v} R) :
    HasColimitsOfSize.{w, w} (DifferentialGradedModule.{u, v, w} A) := by
  have : HasCoequalizers (DifferentialGradedModule.{u, v, w} A) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  exact has_colimits_of_hasCoequalizers_and_coproducts
