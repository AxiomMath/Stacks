module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.ComplexFunctorExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.CechIsTheDerivedFunctor

/-!
# Čech cohomology of presheaves as a cohomological δ-functor: Stacks 01EK

Let `R` be a presheaf of rings on a space, `U` an open, and `(Uᵢ)` a family of opens contained
in `U`. Stacks 01EK says that the Čech cohomology functors `Ȟⁿ((Uᵢ), -)` on presheaves of
`R`-modules, with values in modules over the ring `R(U)` of sections on `U`, form a
cohomological δ-functor: every short exact sequence of presheaves of `R`-modules has natural
connecting morphisms and a long exact Čech cohomology sequence.

The input is the exactness of the Čech complex functor, which is Stacks 01EJ
(`Stacks.Cohomology.CechExactFunctor.presheafCechComplexFunctor_exact`). An exact functor into
cochain complexes carries a short exact sequence to a short exact sequence of complexes, and
the long exact homology sequence of the latter is the δ-functor structure; that step is
`Stacks.Cohomology.CechDerived.deltaFunctor`, proved for Stacks 01EN.

The construction returns the δ-functor *together with* the identification of its degree-`n`
component with degree-`n` Čech cohomology, because that identification is what consumers of
01EK — in particular Stacks 01EN — use to recognize the δ-functor as Čech cohomology. It holds
by `rfl`.

## Main definitions

* `deltaFunctorOfExactCochainComplex`: the cohomological δ-functor `Hⁿ(G(-))` of an exact
  functor `G` into cochain complexes, bundled with the identification of its components.
* `presheafCechCohomologyDeltaFunctor`: **Stacks 01EK**, the Čech cohomology δ-functor on
  presheaves of `R`-modules.

## Main results

* `presheafCechCohomologyDeltaFunctor_functor`: the degree-`n` component is the degree-`n`
  cohomology of the Čech complex functor of Stacks 01EJ.
* `presheafCechCohomologyDeltaFunctor_zero`: the degree-zero component is degree-zero Čech
  cohomology, which is the normalization Stacks 01EN compares with
  `CategoryTheory.Functor.toRightDerivedZero`.
* `preservesFiniteLimits_presheafCechCohomologyZero`: degree-zero Čech cohomology is left
  exact, the first half of the derived-functor comparison of Stacks 01EN.

## Implementation notes

The covering equation `⨆ i, Uᵢ = U` is not used: neither the Čech complex functor of Stacks
01EJ nor its exactness needs the family to cover `U`, so the δ-functor is constructed for an
arbitrary family of opens contained in `U`, exactly as in Stacks 01EJ.

The index universe `w` of the family and the module universe `v` are independent of the space
universe `u` and the ring universe `r`; the module universe of the Čech complex is `max v w`,
forced by the indexed products over `(p+1)`-tuples of indices.

## References

* [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u r v w v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.CechCohomologyDelta

section Abstract

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- **The cohomological δ-functor of an exact functor into cochain complexes.** If
`G : A ⥤ CochainComplex B ℕ` is exact then it carries short exact sequences of `A` to short
exact sequences of cochain complexes, and the cohomology objects `Hⁿ(G(-))` form a
cohomological δ-functor whose connecting morphisms are those of the long exact homology
sequence. The identification of the degree-`n` component with `Hⁿ(G(-))` is part of the data,
since that is what identifies the δ-functor; it holds by `rfl`. -/
def deltaFunctorOfExactCochainComplex (G : A ⥤ CochainComplex B ℕ)
    (hG : exactFunctor A (CochainComplex B ℕ) G) :
    { F : DeltaFunctor A B //
      ∀ n : ℕ, F.functor n = G ⋙ HomologicalComplex.homologyFunctor B (up ℕ) n } :=
  letI : G.Additive := exactFunctor_le_additiveFunctor A (CochainComplex B ℕ) G hG
  letI : PreservesFiniteLimits G := ((exactFunctor_iff G).1 hG).1
  letI : PreservesFiniteColimits G := ((exactFunctor_iff G).1 hG).2
  ⟨CechDerived.deltaFunctor G fun _ hS ↦ hS.map_of_exact G, fun _ ↦ rfl⟩

end Abstract

section Cech

variable {X : Type u} [TopologicalSpace X]

/-- **Stacks Project, Tag 01EK.** The Čech cohomology functors of a family of opens contained
in `U` form a cohomological δ-functor from presheaves of modules over the structure presheaf
`R` to modules over the ring `R(U)` of sections on `U`, and its degree-`n` component is
degree-`n` Čech cohomology, that is, the degree-`n` cohomology of the Čech complex functor of
Stacks 01EJ. The connecting morphisms are those of the long exact homology sequence of the
short exact sequence of Čech complexes produced by the exactness of Stacks 01EJ. -/
def presheafCechCohomologyDeltaFunctor
    (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) (U : Opens X) {ι : Type w}
    (obj : ι → Opens X) (le : ∀ i, obj i ≤ U) :
    { F : DeltaFunctor (PresheafOfModules.{max v w} R)
        (ModuleCat.{max v w} (R.obj (op U))) //
      ∀ n : ℕ, F.functor n =
        CechExactFunctor.presheafCechComplexFunctor R U obj le ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{max v w} (R.obj (op U))) (up ℕ) n } :=
  deltaFunctorOfExactCochainComplex _
    (CechExactFunctor.presheafCechComplexFunctor_exact R U obj le)

variable (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) (U : Opens X) {ι : Type w}
  (obj : ι → Opens X) (le : ∀ i, obj i ≤ U)

/-- The degree-`n` component of the Čech cohomology δ-functor of Stacks 01EK is degree-`n`
Čech cohomology. -/
theorem presheafCechCohomologyDeltaFunctor_functor (n : ℕ) :
    (presheafCechCohomologyDeltaFunctor.{u, r, v, w} R U obj le).1.functor n =
      CechExactFunctor.presheafCechComplexFunctor.{u, r, v, w} R U obj le ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max v w} (R.obj (op U))) (up ℕ) n :=
  (presheafCechCohomologyDeltaFunctor.{u, r, v, w} R U obj le).2 n

/-- The degree-zero component of the Čech cohomology δ-functor of Stacks 01EK is degree-zero
Čech cohomology. This is the functor that Stacks 01EN right-derives. -/
theorem presheafCechCohomologyDeltaFunctor_zero :
    (presheafCechCohomologyDeltaFunctor.{u, r, v, w} R U obj le).1.functor 0 =
      CechExactFunctor.presheafCechComplexFunctor.{u, r, v, w} R U obj le ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max v w} (R.obj (op U))) (up ℕ) 0 :=
  presheafCechCohomologyDeltaFunctor_functor.{u, r, v, w} R U obj le 0

/-- **Degree-zero Čech cohomology is left exact.** The degree-zero functor of any cohomological
δ-functor is left exact, because the long exact sequence makes `0 → Ȟ⁰(X₁) → Ȟ⁰(X₂) → Ȟ⁰(X₃)`
exact for every short exact sequence of presheaves of `R`-modules. This is the input Stacks
01EN needs in order to compare Čech cohomology with the right derived functors of its
degree-zero part. -/
instance preservesFiniteLimits_presheafCechCohomologyZero :
    PreservesFiniteLimits
      ((presheafCechCohomologyDeltaFunctor.{u, r, v, w} R U obj le).1.functor 0) :=
  CechDerived.preservesFiniteLimits_functor_zero _

/-- **The Čech complex functor carries short exact sequences to short exact sequences.** This
is the degreewise exactness of Stacks 01EJ, packaged as the hypothesis the δ-functor
construction consumes; it is also the `cechExact` input of Stacks 01EN. -/
theorem presheafCechComplexFunctor_shortExact
    (S : ShortComplex (PresheafOfModules.{max v w} R)) (hS : S.ShortExact) :
    letI : (CechExactFunctor.presheafCechComplexFunctor.{u, r, v, w} R U obj le).Additive :=
      exactFunctor_le_additiveFunctor _ _ _
        (CechExactFunctor.presheafCechComplexFunctor_exact R U obj le)
    (S.map (CechExactFunctor.presheafCechComplexFunctor.{u, r, v, w} R U obj le)).ShortExact :=
  let hex := CechExactFunctor.presheafCechComplexFunctor_exact.{u, r, v, w} R U obj le
  let : PreservesFiniteLimits
      (CechExactFunctor.presheafCechComplexFunctor.{u, r, v, w} R U obj le) :=
    ((exactFunctor_iff _).1 hex).1
  let : PreservesFiniteColimits
      (CechExactFunctor.presheafCechComplexFunctor.{u, r, v, w} R U obj le) :=
    ((exactFunctor_iff _).1 hex).2
  let : (CechExactFunctor.presheafCechComplexFunctor.{u, r, v, w} R U obj le).Additive :=
    exactFunctor_le_additiveFunctor _ _ _ hex
  hS.map_of_exact _

end Cech

end Stacks.Cohomology.CechCohomologyDelta

end
