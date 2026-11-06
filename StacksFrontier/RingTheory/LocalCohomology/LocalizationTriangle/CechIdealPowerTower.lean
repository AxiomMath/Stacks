module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.StrictMilnorTriangle
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechConeSurjective
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.ComplementLongExact

/-!
# The tower of Čech cones of the adic quotients of a module

Stacks 0BLX compares the derived `I`-adic completion of the derived sections `RΓ(V, M̃)` on
`V = Spec A ∖ V(J)` with the derived limit of the tower `n ↦ RΓ(V, (M/IⁿM)^~)`. For the Čech
localization triangle datum the `complement` functor is
`Stacks.LocalCohomology.cechConeFunctor f ⋙ DerivedCategory.Q`, so that tower is the image under
`DerivedCategory.Q` of the *cochain-complex* tower

`n ↦ (cechConeFunctor f).obj (M/IⁿM)`,

which this file names `Stacks.LocalCohomology.cechIdealPowerTower`. The tower is therefore already
strictified, and the question of a derived limit for it is settled by
`DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi`, which computes one — object *and*
projections — from the ordinary inverse limit, provided the transition maps are epimorphisms.

This file discharges that proviso. The transition maps of
`Stacks.LocalCohomology.idealPowerQuotientTower` are surjective, being induced by the identity of
`M`, and `Stacks.LocalCohomology.cechConeFunctor` carries a surjection to a degreewise surjection
(`Stacks.LocalCohomology.surjective_cechConeFunctor_map`). So the concrete degreewise-surjectivity
hypotheses of the strict Milnor triangle theorems hold at this instantiation, and the tower has a
derived limit with projections pinned at `Q.obj (limit (cechIdealPowerTower f I M))`.

## Main results

* `Stacks.LocalCohomology.surjective_idealPowerQuotientTower_map` — the transition maps of the
  adic quotient tower are surjective.
* `Stacks.LocalCohomology.cechIdealPowerTower` — the tower of Čech cones of the adic quotients.
* `Stacks.LocalCohomology.surjective_cechIdealPowerTower_map` — its transition maps are
  degreewise surjective, which is the `h₁`/`h₂`/`h₃` hypothesis shape of the strict Milnor
  triangle theorems.
* `Stacks.LocalCohomology.epi_cechIdealPowerTower_map` — the same as an epimorphism.
* `Stacks.LocalCohomology.isDerivedLimitWithProjections_Q_limit_cechIdealPowerTower` — the
  resulting pinned derived limit, at the image under `Q` of the ordinary inverse limit.
* `Stacks.LocalCohomology.isNilpotent_smul_id_idealPowerQuotientTower` — an element of `I` acts
  nilpotently on every stage of the adic quotient tower.
* `Stacks.LocalCohomology.isDerivedComplete_Q_limit_cechIdealPowerTower` — that derived limit is
  derived `I`-complete.
* `Stacks.LocalCohomology.isIso_limitLift_homology_zero_cechIdealPowerTower` and
  `Stacks.LocalCohomology.homologyZeroLimitCechIdealPowerTowerIso` — its degree-zero cohomology
  is the limit of the degree-zero cohomologies of the terms, through the limit projections:
  `H⁰(RΓ(U, F^∧)) = lim H⁰(U, F/IⁿF)`.

## Implementation notes

The derived `I`-completeness of the limit is the argument of Stacks 091W run directly at this
instantiation rather than through `isDerivedComplete_of_isMilnorTriangle`, whose functor `F` is an
endofunctor of `D(R)`; here the tower is one of cochain complexes and the functor
`cechConeFunctor f ⋙ DerivedCategory.Q` goes from modules to `D(R)`. The two inputs of that
argument are available all the same. `NoetherianAdicCompletion.IsDerivedLimitWithProjections`
unfolds to exactly a distinguished Milnor triangle, so the pinned derived limit above supplies the
triangle; and nilpotence of the scalar action transports from the module to the Čech cone through
`isNilpotent_smul_id_map`, since `cechConeFunctor` is `R`-linear
(`Stacks.LocalCohomology.cechConeFunctor_linear`) as is `DerivedCategory.Q`. Two-out-of-three in
that triangle (`isDerivedCompleteAt_of_distTriang`) and stability of completeness under countable
products (`isDerivedCompleteAt_pi`) then reduce the claim to the stages, where
`Stacks.LocalCohomology.smul_id_idealPowerQuotientTower_eq_zero` kills `a ^ n` on `M/IⁿM`.

## References

* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **The transition maps of the adic quotient tower are surjective.** They are induced by the
identity of `M`, so they are the quotient maps `M/IᵏM ⟶ M/IⁿM` for `n ≤ k` and every class lifts
along them. -/
public theorem surjective_idealPowerQuotientTower_map (I : Ideal R) (M : ModuleCat.{max u v} R)
    {m n : ℕᵒᵖ} (g : m ⟶ n) :
    Function.Surjective ((idealPowerQuotientTower.{u, v} I M).map g).hom := by
  intro x
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (I ^ n.unop • (⊤ : Submodule R M)) x
  exact ⟨Submodule.mkQ _ y, hy⟩

variable (f : Fin r → R)

/-- **The tower of Čech cones of the adic quotients of `M`.** Composing the adic quotient tower
`n ↦ M/IⁿM` with the cone of the Čech augmentation gives a tower of cochain complexes whose image
under `DerivedCategory.Q` is the tower `n ↦ RΓ(V, (M/IⁿM)^~)` of Stacks 0BLX. -/
public abbrev cechIdealPowerTower (I : Ideal R) (M : ModuleCat.{max u v} R) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ :=
  idealPowerQuotientTower.{u, v} I M ⋙ cechConeFunctor.{v} f

/-- **The transition maps of the Čech cone tower are degreewise surjective.** This is the
hypothesis shape `h₁`/`h₂`/`h₃` of the strict Milnor triangle theorems, discharged at the Čech
instantiation: the adic quotient tower has surjective transition maps, and the cone of the Čech
augmentation preserves surjectivity in each degree. -/
public theorem surjective_cechIdealPowerTower_map (I : Ideal R) (M : ModuleCat.{max u v} R)
    {m n : ℕᵒᵖ} (g : m ⟶ n) (p : ℤ) :
    Function.Surjective (((cechIdealPowerTower.{v} f I M).map g).f p) :=
  surjective_cechConeFunctor_map (M := (idealPowerQuotientTower.{u, v} I M).obj m)
    (N := (idealPowerQuotientTower.{u, v} I M).obj n) f
    ((idealPowerQuotientTower.{u, v} I M).map g)
    (surjective_idealPowerQuotientTower_map I M g) p

/-- **The transition maps of the Čech cone tower are epimorphisms.** -/
public instance epi_cechIdealPowerTower_map (I : Ideal R) (M : ModuleCat.{max u v} R)
    (n : ℕ) : Epi ((cechIdealPowerTower.{v} f I M).map (homOfLE (Nat.le_succ n)).op) :=
  DerivedCategory.epi_map_of_surjective
    (fun k q ↦ surjective_cechIdealPowerTower_map f I M (homOfLE (Nat.le_succ k)).op q) n

/-- **The tower of Čech cones has a derived limit with pinned projections**, namely the image
under `DerivedCategory.Q` of its ordinary inverse limit, with the images of the ordinary limit
projections as its projections.

Nothing here is chosen: both the object and the projections are computed from the tower. This is
`DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi` with its epimorphism hypothesis
discharged by `Stacks.LocalCohomology.surjective_cechIdealPowerTower_map`. -/
public theorem isDerivedLimitWithProjections_Q_limit_cechIdealPowerTower
    (I : Ideal R) (M : ModuleCat.{max u v} R) :
    ∃ _ : HasProduct (fun n : ℕ ↦
        (cechIdealPowerTower.{v} f I M ⋙ DerivedCategory.Q).obj ⟨n⟩),
      NoetherianAdicCompletion.IsDerivedLimitWithProjections
        (cechIdealPowerTower.{v} f I M ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj (limit (cechIdealPowerTower.{v} f I M)))
        (fun n : ℕ ↦
          DerivedCategory.Q.map (limit.π (cechIdealPowerTower.{v} f I M) ⟨n⟩)) :=
  DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi (cechIdealPowerTower.{v} f I M)

/-! ### Derived completeness of the limit -/

/-- **An element of `I` acts nilpotently on every stage of the adic quotient tower.** The `n`-th
stage is `M/IⁿM`, on which `aⁿ` is already zero for `a ∈ I`, so `a • 𝟙` is nilpotent of
exponent `n`. -/
public theorem isNilpotent_smul_id_idealPowerQuotientTower (I : Ideal R)
    (M : ModuleCat.{max u v} R) (n : ℕᵒᵖ) {a : R} (ha : a ∈ I) :
    IsNilpotent (a • (1 : End ((idealPowerQuotientTower.{u, v} I M).obj n))) :=
  ⟨n.unop, by
    refine End.ext ?_
    rw [smul_id_pow]
    exact smul_id_idealPowerQuotientTower_eq_zero I M n (Ideal.pow_mem_pow ha n.unop)⟩

/-- **The limit of the Čech cone tower is derived `I`-complete.** This is the hypothesis
`hcomplete` of
`Stacks.Algebraization.exists_normalized_isDerivedLimitWithProjections_of_isIso_completionDescent`
at the Čech instantiation, where the complement functor is
`Stacks.LocalCohomology.cechConeFunctor f ⋙ DerivedCategory.Q`.

The pinned derived limit of
`Stacks.LocalCohomology.isDerivedLimitWithProjections_Q_limit_cechIdealPowerTower` is a
distinguished Milnor triangle whose other two vertices are the countable product of the
stages. Derived completeness holds at each stage, because `a ∈ I` acts nilpotently on `M/IⁿM` and
both `cechConeFunctor f` and `DerivedCategory.Q` are `R`-linear; it passes to the product, and
then to the limit by two-out-of-three. -/
public theorem isDerivedComplete_Q_limit_cechIdealPowerTower (I : Ideal R)
    (M : ModuleCat.{max u v} R) :
    IsDerivedComplete I (DerivedCategory.Q.obj (limit (cechIdealPowerTower.{v} f I M))) := by
  obtain ⟨hprod, δ, hδ⟩ := isDerivedLimitWithProjections_Q_limit_cechIdealPowerTower.{v} f I M
  have := hprod
  intro a ha
  have hterm : ∀ n : ℕ, IsDerivedCompleteAt
      ((cechIdealPowerTower.{v} f I M ⋙ DerivedCategory.Q).obj ⟨n⟩) a := fun n =>
    isDerivedCompleteAt_of_isNilpotent
      (isNilpotent_smul_id_map (cechConeFunctor.{v} f ⋙ DerivedCategory.Q)
        (isNilpotent_smul_id_idealPowerQuotientTower I M ⟨n⟩ ha))
  exact isDerivedCompleteAt_of_distTriang hδ (isDerivedCompleteAt_pi hterm)
    (isDerivedCompleteAt_pi hterm)

/-! ### Degree-zero cohomology of the limit -/

/-- **`H⁰` of the limit of the Čech cone tower is the limit of the `H⁰` of its terms.** The map
`H⁰(Q(lim_n C(M/IⁿM))) ⟶ lim_n H⁰(Q C(M/IⁿM))` induced by the limit projections is an
isomorphism, `C` being the cone of the Čech augmentation on `f`.

In the language of Stacks 0EIF: `Q(lim_n C(M/IⁿM))` is `RΓ(U, F^∧) = R lim RΓ(U, F/IⁿF)` with
its pinned projections (`isDerivedLimitWithProjections_Q_limit_cechIdealPowerTower`), the terms
`RΓ(U, F/IⁿF)` have no cohomology in degree `-1`
(`Stacks.LocalCohomology.isZero_homologyComplement_of_neg`), so the `R¹lim` term of the Milnor
sequence vanishes and `H⁰(U, F^∧) = lim H⁰(U, F/IⁿF)` — Stacks 0D60 in degree zero. -/
public theorem isIso_limitLift_homology_zero_cechIdealPowerTower (I : Ideal R)
    (M : ModuleCat.{max u v} R) :
    IsIso (limit.lift ((cechIdealPowerTower.{v} f I M ⋙ DerivedCategory.Q) ⋙
        DerivedCategory.homologyFunctor _ 0)
      ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).mapCone
        (limit.cone (cechIdealPowerTower.{v} f I M)))) :=
  DerivedCategory.isIso_limitLift_homology_Q_limit_of_epi (cechIdealPowerTower.{v} f I M) 0
    fun n ↦ isZero_homologyComplement_of_neg.{v} f
      ((idealPowerQuotientTower.{u, v} I M).obj ⟨n⟩) (0 - 1) (by omega)

/-- **`H⁰(RΓ(U, F^∧)) ≅ lim H⁰(RΓ(U, F/IⁿF))`**, in the Čech model: the isomorphism of
`isIso_limitLift_homology_zero_cechIdealPowerTower`. Its composite with the `n`-th limit
projection is `H⁰` of the `n`-th projection of the limit, by
`homologyZeroLimitCechIdealPowerTowerIso_hom_comp_π`. -/
public def homologyZeroLimitCechIdealPowerTowerIso (I : Ideal R) (M : ModuleCat.{max u v} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
        (DerivedCategory.Q.obj (limit (cechIdealPowerTower.{v} f I M))) ≅
      limit ((cechIdealPowerTower.{v} f I M ⋙ DerivedCategory.Q) ⋙
        DerivedCategory.homologyFunctor _ 0) :=
  haveI := isIso_limitLift_homology_zero_cechIdealPowerTower.{v} f I M
  asIso (limit.lift ((cechIdealPowerTower.{v} f I M ⋙ DerivedCategory.Q) ⋙
      DerivedCategory.homologyFunctor _ 0)
    ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).mapCone
      (limit.cone (cechIdealPowerTower.{v} f I M))))

/-- The composite of `homologyZeroLimitCechIdealPowerTowerIso` with the `n`-th limit projection
is `H⁰` of the `n`-th limit projection of the Čech cone tower. -/
@[reassoc]
public theorem homologyZeroLimitCechIdealPowerTowerIso_hom_comp_π (I : Ideal R)
    (M : ModuleCat.{max u v} R) (n : ℕᵒᵖ) :
    (homologyZeroLimitCechIdealPowerTowerIso.{v} f I M).hom ≫
        limit.π ((cechIdealPowerTower.{v} f I M ⋙ DerivedCategory.Q) ⋙
          DerivedCategory.homologyFunctor _ 0) n =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
        (DerivedCategory.Q.map (limit.π (cechIdealPowerTower.{v} f I M) n)) :=
  limit.lift_π _ n

end Stacks.LocalCohomology

end
