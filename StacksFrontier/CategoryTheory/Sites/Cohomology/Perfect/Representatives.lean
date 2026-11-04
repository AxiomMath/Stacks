module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of a representative of a perfect derived object

Let `(C, O)` be a ringed site and let `E` be a perfect object of `D(O)`. Then *every* complex of
`O`-modules representing `E` is a perfect complex. This is part (2) of Stacks 08G6.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfectComplex_of_isPerfect_representation`: Stacks 08G6,
  part (2).

## Implementation notes

Perfectness of `E` gives a strictly perfect model of *some* representative `P` above a covering
of each object; transporting it to a given representative `F` uses Stacks 08FR twice, once
inside `AlgebraicGeometry.RingedSite.exists_coveringSieve_quasiIso_of_derivedIso` to turn the
derived comparison into a map of complexes, and once more at the level of the site to compose
the two coverings. The resulting two layers of covering sieves are combined with `Sieve.bind`.

## References

* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{0}]
variable [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] preservesFiniteLimitsOverFunctor preservesFiniteColimitsOverFunctor

variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hDer : ∀ V : X.C, HasDerivedCategory.{d}
    (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))]

attribute [local instance] localModelsHasDerivedOver

/-- The restriction to a slice of a derived isomorphism between two complexes on the site. -/
private def restrictDerivedIso
    {P F : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj F) (V : X.C) :
    DerivedCategory.Q.obj (X.restrictComplex P V) ≅
      DerivedCategory.Q.obj (X.restrictComplex F V) :=
  ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app P).symm ≪≫
    (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.mapIso e ≪≫
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          V).mapDerivedCategoryFactors.app F

/-- A strictly perfect model of one representative above `V` becomes, after passing to a
covering sieve of `V`, a strictly perfect model of any other representative. -/
private theorem exists_coveringSieve_strictlyPerfect_model
    {P F : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj F)
    (V : X.C) {E : CochainComplex
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) E)
    (q : E ⟶ X.restrictComplex P V) (hq : QuasiIso q) :
    ∃ T : Sieve V, T ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (h : W ⟶ V), T h →
        ∃ E' : CochainComplex
            (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) E' ∧
            ∃ r : E' ⟶ X.restrictComplex F W, QuasiIso r := by
  let : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C :=
      SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) q).2 hq
  obtain ⟨T, hT, hquasi⟩ := exists_coveringSieve_quasiIso_of_derivedIso X V hE
    (asIso (DerivedCategory.Q.map q) ≪≫ restrictDerivedIso X e V)
  refine ⟨T, hT, ?_⟩
  intro W h hh
  obtain ⟨β, hβ⟩ := hquasi h hh
  let := hβ
  let c := (Stacks.SheafOfModules.overFunctorMapComplexIso
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h).app F
  refine ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h hE,
    β ≫ c.hom, ?_⟩
  let : IsIso c.hom := c.isIso_hom
  infer_instance

/-- **Stacks 08G6, part (2).** Let `(C, O)` be a ringed site and let `K` be a perfect object of
`D(O)`. Then every complex of `O`-modules representing `K` is a perfect complex. -/
@[stacks 08G6 "perfect_independent_of_representative"]
theorem isPerfectComplex_of_isPerfect_representation
    {K : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : X.IsPerfect K)
    {F : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hF : Nonempty (DerivedCategory.Q.obj F ≅ K)) :
    X.IsPerfectComplex F := by
  classical
  obtain ⟨P, hP, ⟨ePK⟩⟩ := hK
  obtain ⟨eFK⟩ := hF
  intro U
  obtain ⟨S, hS, hmodels⟩ := hP U
  have refined : ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g →
      ∃ T : Sieve V, T ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (h : W ⟶ V), T h →
          ∃ E' : CochainComplex
              (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) E' ∧
              ∃ r : E' ⟶ X.restrictComplex F W, QuasiIso r := by
    intro V g hg
    obtain ⟨E, hE, q, hq⟩ := hmodels g hg
    exact exists_coveringSieve_strictlyPerfect_model X (ePK ≪≫ eFK.symm) V hE q hq
  choose T hT hTlocal using refined
  have hbind : Sieve.bind S (fun {_} {g} hg => T g hg) ∈ X.J U := by
    refine X.J.transitive hS _ ?_
    rintro V g ⟨V₀, h, g₀, hg₀, rfl⟩
    refine X.J.superset_covering (fun W k hk => ?_) (X.J.pullback_stable h (hT g₀ hg₀))
    rw [Sieve.pullback_apply] at hk ⊢
    exact ⟨V₀, k ≫ h, g₀, hg₀, hk, by simp⟩
  refine ⟨(Sieve.bind S (fun {_} {g} hg => T g hg)).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]; exact hbind
  rintro W f ⟨V, h, g, hg, hh, rfl⟩
  exact hTlocal g hg h hh

end AlgebraicGeometry.RingedSite

end
