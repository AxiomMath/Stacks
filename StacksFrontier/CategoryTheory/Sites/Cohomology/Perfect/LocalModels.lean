module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Strictly perfect models on a covering of a final object

Let `(C, O)` be a ringed site whose underlying category has a final object `T`, and let `E` be
an object of `D(O)`. If there are a covering `{V → T}`, strictly perfect complexes `P_V` of
`O|_V`-modules and isomorphisms `P_V ≅ E|_V` in `D(O|_V)`, then `E` is perfect. This is part (1)
of Stacks 08G6.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_quasiIso_of_derivedIso`: an isomorphism in
  the derived category out of a strictly perfect complex becomes, after restriction along the
  arrows of a covering sieve, an honest quasi-isomorphism of complexes.
* `AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect`: Stacks
  08G6, part (1), with the covering given above every object of the site rather than above a
  final object.
* `AlgebraicGeometry.RingedSite.isPerfect_of_coveringFamily_strictlyPerfect`: Stacks 08G6,
  part (1).

## Implementation notes

Perfectness of `E` requires a strictly perfect model locally above *every* object of `C`, while
the hypothesis provides one only above a covering of the final object `T`. The two are
reconciled by pulling the covering sieve of `T` back along the unique arrow `U ⟶ T`; the models
are then restricted along arrows of the site, which is
`Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general`.

The hypothesis is an isomorphism with the *derived* restriction `E|_V`, as in the source, rather
than with the image of the restriction of a chosen representative of `E`. The passage between
the two is `Functor.mapDerivedCategoryFactors` for the restriction functor.

Turning a derived isomorphism into a map of complexes is Stacks 08FR, which is available only
for a site whose objects and morphisms live in the same universe; this file is therefore stated
at `RingedSite.{u, u, w}`, with the objects and the morphisms of the site tied together but the
sections of the structure sheaf and of the modules free, whereas
`AlgebraicGeometry.RingedSite.IsPerfect` is defined with all of them independent. The sections
of the modules are on the diagonal with those of the structure sheaf because strict perfectness
compares a module with `SheafOfModules.free I` for `I` in the ring universe.

## References

* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
variable [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction to a slice of the site preserves finite limits, at a free universe of the
sections. -/
local instance localModelsPreservesFiniteLimitsOverFunctor (V : X.C) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V

/-- Restriction to a slice of the site preserves finite colimits, at a free universe of the
sections. -/
local instance localModelsPreservesFiniteColimitsOverFunctor (V : X.C) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hDer : ∀ V : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))]

/-- The derived category of sheaves of modules over each slice of the site. -/
local instance localModelsHasDerivedOver (V : X.C) :
    HasDerivedCategory.{d}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
  hDer V

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- An isomorphism `P ≅ F` of `D(O|_V)` whose source is a strictly perfect complex becomes, after
restriction along the arrows of a covering sieve of `V`, the image of a quasi-isomorphism of
complexes. This is Stacks 08FR together with the fact that restriction along an arrow of the
site is exact, so that it detects quasi-isomorphisms through the localisation functor. -/
theorem exists_coveringSieve_quasiIso_of_derivedIso (V : X.C)
    {P F : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj F) :
    ∃ S : Sieve V, S ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (f : W ⟶ V), S f →
        ∃ β : ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
            ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
          QuasiIso β := by
  obtain ⟨S, hS, hβ⟩ := exists_coveringSieve_complexMap X V hP e.hom
  refine ⟨S, hS, ?_⟩
  intro W f hf
  obtain ⟨hsheaf, hlocal, hadd, hlim, hcolim, β, hcomm⟩ := hβ f hf
  let := hsheaf
  let := hlocal
  let : HasDerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
    HasDerivedCategory.standard _
  let := hadd
  let := hlim
  let := hcolim
  have hcomp : IsIso
      ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          f).mapDerivedCategory.map e.hom ≫
        (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          f).mapDerivedCategoryFactors.hom.app F) :=
    inferInstance
  rw [hcomm] at hcomp
  exact ⟨β, (DerivedCategory.isIso_Q_map_iff_quasiIso _ β).mp
    ((isIso_comp_left_iff
      ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        f).mapDerivedCategoryFactors.hom.app P)
      (DerivedCategory.Q.map β)).mp hcomp)⟩

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- A strictly perfect model of the restriction of a chosen representative `K` of `E` to the
slice over `V`, taken in the derived category, is refined by honest quasi-isomorphisms over the
members of a covering sieve of `V`. -/
private theorem exists_coveringSieve_quasiIso_models (V : X.C)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {P : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (α : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (X.restrictComplex K V)) :
    ∃ S' : Sieve V, S' ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (g : W ⟶ V), S' g →
        ∃ Q' : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) Q' ∧
            ∃ q : Q' ⟶ X.restrictComplex K W, QuasiIso q := by
  obtain ⟨S', hS', hquasi⟩ := exists_coveringSieve_quasiIso_of_derivedIso X V hP α
  refine ⟨S', hS', ?_⟩
  intro W g hg
  obtain ⟨β, hβ⟩ := hquasi g hg
  let := hβ
  let c := (Stacks.SheafOfModules.overFunctorMapComplexIso
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K
  refine ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP, β ≫ c.hom, ?_⟩
  let : IsIso c.hom := c.isIso_hom
  infer_instance

/-- Strictly perfect models of `E|_V` over the members of a covering of `U` give a covering sieve
of `U` over whose arrows the restriction of a representative `K` of `E` receives quasi-isomorphisms
from strictly perfect complexes. -/
private theorem exists_coveringSieve_quasiIso_of_models (U : X.C)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E) (S : Presieve U) (hS : Sieve.generate S ∈ X.J U)
    (hmodels : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∃ P : CochainComplex
          (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
          Nonempty (DerivedCategory.Q.obj P ≅
            (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              V).mapDerivedCategory.obj E)) :
    ∃ R : Sieve U, R ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U), R g →
        ∃ Q' : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) Q' ∧
            ∃ q : Q' ⟶ X.restrictComplex K V, QuasiIso q := by
  have hrepr : ∀ V : X.C, DerivedCategory.Q.obj (X.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj E := fun V =>
    ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.mapIso eK
  have hlocal : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∃ S' : Sieve V, S' ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (g : W ⟶ V), S' g →
          ∃ Q' : CochainComplex
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) Q' ∧
              ∃ q : Q' ⟶ X.restrictComplex K W, QuasiIso q := by
    intro V f hf
    obtain ⟨P, hP, ⟨α⟩⟩ := hmodels f hf
    exact exists_coveringSieve_quasiIso_models X V K hP (α ≪≫ (hrepr V).symm)
  choose Sv hSv hmodel using hlocal
  refine ⟨Sieve.bind S (fun {_} {f} hf => Sv f hf), ?_, ?_⟩
  · refine X.J.transitive hS _ fun V f hf => ?_
    obtain ⟨W, k, s, hs, hfac⟩ := hf
    refine X.J.superset_covering (fun Z g hg => ?_)
      (X.J.pullback_stable k (hSv s hs))
    exact ⟨W, g ≫ k, s, hs, hg, by simp [hfac, Category.assoc]⟩
  · intro V g hg
    obtain ⟨W, k, s, hs, hk, _⟩ := hg
    exact hmodel s hs k hk

/-- **Strictly perfect models on a covering of every object make an object of `D(O)` perfect.**
Let `E` be an object of `D(O)` and suppose that every object `U` of `C` admits a covering
`{V → U}` over each member of which there are a strictly perfect complex `P_V` of
`O|_V`-modules and an isomorphism `P_V ≅ E|_V` in `D(O|_V)`. Then `E` is perfect.

This is the form of Stacks 08G6, part (1) which does not ask the site for a final object, and
is the form in which the criteria that produce local models above an arbitrary object — such as
Stacks 08G7 — consume it; `isPerfect_of_coveringFamily_strictlyPerfect` is the statement of the
source, where a single covering of the final object suffices. -/
theorem isPerfect_of_forall_coveringFamily_strictlyPerfect
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        ∃ P : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
            Nonempty (DerivedCategory.Q.obj P ≅
              (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                V).mapDerivedCategory.obj E)) :
    X.IsPerfect E := by
  classical
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  refine ⟨K, fun U => ?_, ⟨eK⟩⟩
  obtain ⟨S, hS, hmodels⟩ := h U
  obtain ⟨R, hR, hmodel⟩ := exists_coveringSieve_quasiIso_of_models X U E K eK S hS hmodels
  exact ⟨R.arrows, by rwa [Sieve.generate_sieve], hmodel⟩

/-- **Stacks 08G6, part (1).** Let `(C, O)` be a ringed site whose underlying category has a
final object `T` and let `E` be an object of `D(O)`. If there are a covering `{V → T}`, strictly
perfect complexes `P_V` of `O|_V`-modules and isomorphisms `P_V ≅ E|_V` in `D(O|_V)`, then `E` is
perfect. -/
@[stacks 08G6 "local_strictly_perfect_implies_perfect"]
theorem isPerfect_of_coveringFamily_strictlyPerfect
    (T : X.C) (hT : IsTerminal T)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∃ S : Presieve T, Sieve.generate S ∈ X.J T ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ T), S f →
        ∃ P : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
            Nonempty (DerivedCategory.Q.obj P ≅
              (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                V).mapDerivedCategory.obj E)) :
    X.IsPerfect E := by
  classical
  obtain ⟨S, hS, hmodels⟩ := h
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  obtain ⟨R, hR, hmodel⟩ := exists_coveringSieve_quasiIso_of_models X T E K eK S hS hmodels
  exact ⟨K, fun U => ⟨(R.pullback (hT.from U)).arrows,
    by simpa using X.J.pullback_stable (hT.from U) hR, fun V g hg => hmodel _ hg⟩, ⟨eK⟩⟩

end AlgebraicGeometry.RingedSite

end
