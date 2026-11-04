module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnASliceGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives

/-!
# Pseudo-coherence from derived approximations on coverings

On a ringed site, an object of `D(O)` admitting, on a covering family of every object, derived
strictly perfect approximations which are isomorphisms on cohomology above `m` and surjective in
degree `m` is `m`-pseudo-coherent (Stacks 08FT), for sites and modules in arbitrary universes.

## Main results

* `isPseudoCoherentFrom_of_forall_coveringFamily_derived_approximation`: derived strictly perfect
  approximations on a covering of every object make an object of `D(O)` `m`-pseudo-coherent.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

section Slice

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hSliceDer : ∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory

attribute [local instance] ovFunctorLimits ovFunctorColimits

/-- Suppose every object `U` of `C` admits a covering `{V → U}` over each member of which a
strictly perfect complex of `O|_V`-modules approximates `E|_V` in the derived category: a morphism
to the derived restriction which is invertible on cohomology in degrees `> m` and epic in degree
`m`. Then `E` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_forall_coveringFamily_derived_approximation
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        ∃ P : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
          ∃ β : DerivedCategory.Q.obj P ⟶
              (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                V).mapDerivedCategory.obj E,
            (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β)) ∧
            Epi ((DerivedCategory.homologyFunctor _ m).map β)) :
    X.IsPseudoCoherentFrom E m := by
  classical
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  have hrepr : ∀ V : X.C, DerivedCategory.Q.obj (X.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj E := fun V =>
    ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.mapIso eK
  refine ⟨K, fun U => ?_, ⟨eK⟩⟩
  obtain ⟨S, hS, hmodels⟩ := h U
  have hlocal : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∃ T : Sieve V, T ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
          ∃ P' : CochainComplex
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P' ∧
            ∃ α' : P' ⟶ X.restrictComplex K W,
              (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
              Epi (HomologicalComplex.homologyMap α' m) := by
    intro V f hf
    obtain ⟨P, hP, β, hiso, hepi⟩ := hmodels f hf
    refine X.exists_coveringSieve_approximation_of_derived_general V K m P hP
      (β ≫ (hrepr V).inv) (fun j hj => ?_) ?_
    · rw [Functor.map_comp]
      have := hiso j hj
      infer_instance
    · rw [Functor.map_comp]
      exact epi_comp' hepi (IsIso.epi_of_iso _)
  choose T hT hmodel using hlocal
  have hbind : Sieve.bind S (fun {_} {f} hf => T f hf) ∈ X.J U := by
    refine X.J.transitive hS _ fun V f hf => ?_
    obtain ⟨W, k, s, hs, hfac⟩ := hf
    refine X.J.superset_covering (fun Z g hg => ?_)
      (X.J.pullback_stable k (hT s hs))
    exact ⟨W, g ≫ k, s, hs, hg, by simp [hfac, Category.assoc]⟩
  refine ⟨(Sieve.bind S (fun {_} {f} hf => T f hf)).arrows, ?_, ?_⟩
  · rwa [Sieve.generate_sieve]
  intro V g hg
  obtain ⟨W, k, s, hs, hk, _⟩ :=
    (show Sieve.bind S (fun {_} {f} hf => T f hf) g from hg)
  exact hmodel s hs k hk

end Slice

end AlgebraicGeometry.RingedSite

end
