module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnASlice
import StacksCore.Tactic.StacksAttribute

/-!
# One covering of the final object with strictly perfect approximations suffices

Let `(C, O)` be a ringed site whose underlying category has a final object `X`, and let `E` be
an object of `D(O)`. If there are a covering `{U_i → X}` of that final object, strictly perfect
complexes `E_i` of `O_{U_i}`-modules and maps `α_i : E_i → E|_{U_i}` in `D(O_{U_i})` which are
isomorphisms on cohomology in every degree `> m` and surjective in degree `m`, then `E` is
`m`-pseudo-coherent.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_covering_of_terminal`: an object of
  `D(O)` which, over the members of one covering of the final object, is approximated by strictly
  perfect complexes in degrees `≥ m` is `m`-pseudo-coherent.

## References

* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.RingedSite

section Terminal

variable (X : RingedSite.{u, u, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hSliceDer : ∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory

attribute [local instance] preservesFiniteLimitsOverFunctor preservesFiniteColimitsOverFunctor

/-- If the members of a covering of a terminal object are covered by objects satisfying `Q`, then
every object has a covering by objects satisfying `Q`. -/
private theorem _root_.CategoryTheory.GrothendieckTopology.exists_covering_of_terminal_covering
    {C : Type*} [Category C] (J : GrothendieckTopology C) {T : C} (hT : IsTerminal T)
    (S : Presieve T) (hS : Sieve.generate S ∈ J T) (Q : C → Prop)
    (hkey : ∀ ⦃V⦄ (f : V ⟶ T), S f →
      ∃ TV : Sieve V, TV ∈ J V ∧ ∀ ⦃W⦄ (g : W ⟶ V), TV g → Q W)
    (U : C) : ∃ R : Presieve U, Sieve.generate R ∈ J U ∧ ∀ ⦃Y⦄ (q : Y ⟶ U), R q → Q Y := by
  have key2 : ∀ (Z : C) (p : Z ⟶ U), ((Sieve.generate S).pullback (hT.from U)).arrows p →
      ∃ TZ : Sieve Z, TZ ∈ J Z ∧ ∀ ⦃Y⦄ (k : Y ⟶ Z), TZ k → Q Y := by
    rintro Z p ⟨V, g, f, hf, -⟩
    obtain ⟨TV, hTV, hTVdata⟩ := hkey f hf
    exact ⟨TV.pullback g, J.pullback_stable g hTV, fun _ k hk => hTVdata (k ≫ g) hk⟩
  refine ⟨(Sieve.bind ((Sieve.generate S).pullback (hT.from U)).arrows
    fun Z p hp => (key2 Z p hp).choose).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact J.bind_covering (J.pullback_stable _ hS) fun Z p hp => (key2 Z p hp).choose_spec.1
  · rintro Y q ⟨Z, k, p, hp, hk, rfl⟩
    exact (key2 Z p hp).choose_spec.2 k hk

/-- Let `(C, O)` be a ringed site, let `E` be an object of `D(O)` and let `T` be a final object of
`C`. If a covering `{V → T}` of `T` carries over each of its members a strictly perfect complex `P`
of `O|_V`-modules and a morphism `P ⟶ E|_V` of `D(O|_V)` which is an isomorphism on cohomology in
every degree `> m` and an epimorphism on cohomology in degree `m`, then `E` is `m`-pseudo-coherent.
-/
@[stacks 08FU "part (1)"]
theorem isPseudoCoherentFrom_of_covering_of_terminal
    (T : X.C) (hT : IsTerminal T)
    (E : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (S : Presieve T) (hS : Sieve.generate S ∈ X.J T)
    (hdata : ∀ ⦃V : X.C⦄ (f : V ⟶ T), S f →
      ∃ P : CochainComplex
          (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
        ∃ α : DerivedCategory.Q.obj P ⟶
            (SheafOfModules.overFunctor.{0}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj E,
          (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor _ m).map α)) :
    X.IsPseudoCoherentFrom E m := by
  classical
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
        DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  refine ⟨K, ?_, ⟨eK⟩⟩
  intro U
  refine X.J.exists_covering_of_terminal_covering hT S hS
    (fun W => ∃ P : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
      ∃ α : P ⟶ X.restrictComplex K W,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m)) ?_ U
  intro V f hf
  obtain ⟨P, hP, α, hiso, hepi⟩ := hdata f hf
  have erep : DerivedCategory.Q.obj (X.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{0}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj E :=
    ((SheafOfModules.overFunctor.{0}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{0}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.mapIso eK
  have hinv : IsIso erep.inv := erep.isIso_inv
  refine X.exists_coveringSieve_approximation_of_derived V K m P hP (α ≫ erep.inv) ?_ ?_
  · intro j hj
    have := hiso j hj
    rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp]
    exact epi_comp' hepi (IsIso.epi_of_iso _)

end Terminal

end AlgebraicGeometry.RingedSite

end
