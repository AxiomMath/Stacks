module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMapGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# Strictly perfect models on a covering, at independent site universes

Let `(C, O)` be a ringed site whose underlying category has a final object `T`, and let `E` be an
object of `D(O)`. If there are a covering `{V → T}`, strictly perfect complexes `P_V` of
`O|_V`-modules and isomorphisms `P_V ≅ E|_V` in `D(O|_V)`, then `E` is perfect. This is part (1) of
Stacks 08G6, here with the objects and the morphisms of `C` in independent universes. At the same
generality, a strictly perfect local model of a complex restricts along an arrow of the site, and
every complex representing a perfect object is a perfect complex.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect_general`: Stacks
  08G6, part (1), with the covering given above every object of the site rather than above a final
  object.
* `AlgebraicGeometry.RingedSite.isPerfect_of_coveringFamily_strictlyPerfect_general`: Stacks 08G6,
  part (1).
* `AlgebraicGeometry.RingedSite.exists_localModel_restrictComplex_of_hom`: a strictly perfect local
  model of a complex over an object restricts to one over any object mapping to it.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_of_isPerfect`: every complex representing a
  perfect object of `D(O)` is a perfect complex.

## Implementation notes

The sections of the modules lie in the universe of the sections of the structure sheaf: strict
perfectness compares a module with `SheafOfModules.free I` for `I` in the universe of the ring.

## References

* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

section CoveringFamilies

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
variable [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [HasDerivedCategory.{d}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O))]
variable [hDer : ∀ V : X.C, HasDerivedCategory.{d}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V))]

-- Exactness of restriction to a slice, and the derived category of a slice.
attribute [local instance] ovFunctorLimits ovFunctorColimits
  locallyOverRingSheafHasDerivedCategory

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O))] in
/-- A strictly perfect model of the restriction of a chosen representative `K` of `E` to the slice
over `V`, taken in the derived category, is refined by honest quasi-isomorphisms over the members
of a covering sieve of `V`. -/
private theorem exists_coveringSieve_quasiIso_models_general (V : X.C)
    (K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)) ℤ)
    {P : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V) P)
    (α : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (X.restrictComplex K V)) :
    ∃ S' : Sieve V, S' ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (g : W ⟶ V), S' g →
        ∃ Q' : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over W)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over W) Q' ∧
            ∃ q : Q' ⟶ X.restrictComplex K W, QuasiIso q := by
  obtain ⟨S', hS', hquasi⟩ := exists_coveringSieve_quasiIso_of_derivedIso_general X V hP α
  refine ⟨S', hS', fun W g hg => ?_⟩
  obtain ⟨β, hβ⟩ := hquasi g hg
  let c := (Stacks.SheafOfModules.overFunctorMapComplexIso
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) g).app K
  refine ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) g hP,
    β ≫ c.hom, inferInstance⟩

/-- **Strictly perfect models on a covering of every object make an object of `D(O)` perfect.**
Let `E` be an object of `D(O)` and suppose that every object `U` of `C` admits a covering `{V → U}`
over each member of which there are a strictly perfect complex `P_V` of `O|_V`-modules and an
isomorphism `P_V ≅ E|_V` in `D(O|_V)`. Then `E` is perfect. -/
theorem isPerfect_of_forall_coveringFamily_strictlyPerfect_general
    (E : DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)))
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        ∃ P : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V) P ∧
            Nonempty (DerivedCategory.Q.obj P ≅
              (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
                V).mapDerivedCategory.obj E)) :
    X.IsPerfect E := by
  classical
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)) ℤ,
      DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  have hrepr : ∀ V : X.C, DerivedCategory.Q.obj (X.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
        V).mapDerivedCategory.obj E := fun V =>
    ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
      V).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
        V).mapDerivedCategory.mapIso eK
  refine ⟨K, fun U => ?_, ⟨eK⟩⟩
  obtain ⟨S, hS, hmodels⟩ := h U
  have hlocal : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∃ S' : Sieve V, S' ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (g : W ⟶ V), S' g →
          ∃ Q' : CochainComplex
              (SheafOfModules.{w}
                ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over W) Q' ∧
              ∃ q : Q' ⟶ X.restrictComplex K W, QuasiIso q := by
    intro V f hf
    obtain ⟨P, hP, ⟨α⟩⟩ := hmodels f hf
    exact exists_coveringSieve_quasiIso_models_general X V K hP (α ≪≫ (hrepr V).symm)
  choose Sv hSv hmodel using hlocal
  have hbind : Sieve.bind S (fun {_} {f} hf => Sv f hf) ∈ X.J U := by
    refine X.J.transitive hS _ fun V f hf => ?_
    obtain ⟨W, k, s, hs, hfac⟩ := hf
    refine X.J.superset_covering (fun Z g hg => ?_)
      (X.J.pullback_stable k (hSv s hs))
    exact ⟨W, g ≫ k, s, hs, hg, by simp [hfac, Category.assoc]⟩
  refine ⟨(Sieve.bind S (fun {_} {f} hf => Sv f hf)).arrows, by rwa [Sieve.generate_sieve], ?_⟩
  intro V g hg
  obtain ⟨W, k, s, hs, hk, _⟩ :=
    (show Sieve.bind S (fun {_} {f} hf => Sv f hf) g from hg)
  exact hmodel s hs k hk

/-- Let `(C, O)` be a ringed site whose underlying category has a final object `T` and let `E` be
an object of `D(O)`. If there are a covering `{V → T}`, strictly perfect complexes `P_V` of
`O|_V`-modules and isomorphisms `P_V ≅ E|_V` in `D(O|_V)`, then `E` is perfect. -/
@[stacks 08G6 "local_strictly_perfect_implies_perfect"]
theorem isPerfect_of_coveringFamily_strictlyPerfect_general
    (T : X.C) (hT : IsTerminal T)
    (E : DerivedCategory (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)))
    (h : ∃ S : Presieve T, Sieve.generate S ∈ X.J T ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ T), S f →
        ∃ P : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V) P ∧
            Nonempty (DerivedCategory.Q.obj P ≅
              (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
                V).mapDerivedCategory.obj E)) :
    X.IsPerfect E := by
  classical
  obtain ⟨S, hS, hmodels⟩ := h
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)) ℤ,
      DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  have hrepr : ∀ V : X.C, DerivedCategory.Q.obj (X.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
        V).mapDerivedCategory.obj E := fun V =>
    ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
      V).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
        V).mapDerivedCategory.mapIso eK
  have hlocal : ∀ ⦃V : X.C⦄ (f : V ⟶ T), S f →
      ∃ S' : Sieve V, S' ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (g : W ⟶ V), S' g →
          ∃ Q' : CochainComplex
              (SheafOfModules.{w}
                ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over W) Q' ∧
              ∃ q : Q' ⟶ X.restrictComplex K W, QuasiIso q := by
    intro V f hf
    obtain ⟨P, hP, ⟨α⟩⟩ := hmodels f hf
    exact exists_coveringSieve_quasiIso_models_general X V K hP (α ≪≫ (hrepr V).symm)
  choose Sv hSv hmodel using hlocal
  have hbind : Sieve.bind S (fun {_} {f} hf => Sv f hf) ∈ X.J T := by
    refine X.J.transitive hS _ fun V f hf => ?_
    obtain ⟨W, k, s, hs, hfac⟩ := hf
    refine X.J.superset_covering (fun Z g hg => ?_)
      (X.J.pullback_stable k (hSv s hs))
    exact ⟨W, g ≫ k, s, hs, hg, by simp [hfac, Category.assoc]⟩
  refine ⟨K, fun U => ⟨((Sieve.bind S (fun {_} {f} hf => Sv f hf)).pullback (hT.from U)).arrows,
    by simpa using X.J.pullback_stable (hT.from U) hbind, ?_⟩, ⟨eK⟩⟩
  intro V g hg
  obtain ⟨W, k, s, hs, hk, _⟩ :=
    (show Sieve.bind S (fun {_} {f} hf => Sv f hf) (g ≫ hT.from U) from hg)
  exact hmodel s hs k hk

end CoveringFamilies

section ChosenRepresentative

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
variable [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hDer : ∀ V : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))]

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  hDer in
/-- **A strictly perfect local model restricts along an arrow of the site.**  If over `V` a
strictly perfect complex maps quasi-isomorphically to the restriction of `K`, then so does its
restriction over any `W` mapping to `V`. -/
theorem exists_localModel_restrictComplex_of_hom
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V W : X.C} (g : W ⟶ V)
    (h : ∃ P : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
        ∃ q : P ⟶ X.restrictComplex K V, QuasiIso q) :
    ∃ P : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
        ∃ q : P ⟶ X.restrictComplex K W, QuasiIso q := by
  obtain ⟨P, hP, q, hq⟩ := h
  let G := SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
  have : PreservesFiniteLimits G :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g
  have : PreservesFiniteColimits G :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g
  have : G.Additive := ⟨by intros; ext; rfl⟩
  have : G.PreservesHomology := Functor.preservesHomologyOfExact G
  let c := (Stacks.SheafOfModules.overFunctorMapComplexIso
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K
  refine ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP,
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ c.hom, ?_⟩
  have : IsIso c.hom := c.isIso_hom
  infer_instance

/-- **Every complex representing a perfect object of `D(O)` is a perfect complex.** -/
theorem isPerfectComplex_of_isPerfect
    {E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hE : X.IsPerfect E)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E) :
    X.IsPerfectComplex K := by
  classical
  obtain ⟨N, hN, ⟨eN⟩⟩ := hE
  have hrepr : ∀ V : X.C, DerivedCategory.Q.obj (X.restrictComplex N V) ≅
      DerivedCategory.Q.obj (X.restrictComplex K V) := fun V =>
    ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app N).symm ≪≫
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.mapIso (eN ≪≫ eK.symm) ≪≫
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategoryFactors.app K
  intro U
  obtain ⟨S, hS, hmodels⟩ := hN U
  have hlocal : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∃ S' : Sieve V, S' ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (g : W ⟶ V), S' g →
          ∃ Q' : CochainComplex
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) Q' ∧
              ∃ q : Q' ⟶ X.restrictComplex K W, QuasiIso q := by
    intro V f hf
    obtain ⟨P, hP, q, hq⟩ := hmodels f hf
    have : IsIso (DerivedCategory.Q.map q) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
    obtain ⟨S', hS', hquasi⟩ := exists_coveringSieve_quasiIso_of_derivedIso_general X V hP
      (asIso (DerivedCategory.Q.map q) ≪≫ hrepr V)
    refine ⟨S', hS', fun W g hg => ?_⟩
    obtain ⟨β, hβ⟩ := hquasi g hg
    let c := (Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K
    refine ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP, β ≫ c.hom, inferInstance⟩
  choose Sv hSv hmodel using hlocal
  refine ⟨fun {W} p => ∃ (V : X.C) (f : V ⟶ U) (hf : S f) (g : W ⟶ V),
    Sv f hf g ∧ p = g ≫ f, ?_, ?_⟩
  · refine X.J.transitive hS _ fun V f hf => ?_
    obtain ⟨V', a, f', hf', rfl⟩ := hf
    refine X.J.superset_covering ?_ (X.J.pullback_stable a (hSv f' hf'))
    intro Z k hk
    exact ⟨_, 𝟙 _, _, ⟨V', f', hf', k ≫ a, hk, rfl⟩, by simp⟩
  · rintro W p ⟨V, f, hf, g, hg, rfl⟩
    exact hmodel f hf g hg


end ChosenRepresentative

end AlgebraicGeometry.RingedSite

end
