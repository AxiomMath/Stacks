module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.IdealPowerDirectSum
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBaseFunctor

/-!
# Finiteness of the cohomology of `Iⁿ F_(n+1)` in every degree

In the situation of Stacks 0EJU the subsheaf `Iⁿ F_(n+1)` of `F_(n+1)` is a finite direct sum of
copies of `F_1` (`Stacks.Algebraization.exists_isoDirectSum_idealPowerSub`). Cohomology over the
base ring `A` is a right derived functor of an additive functor, hence additive, hence carries
that direct sum to a finite product. So in *every* degree `p` the finiteness of `Hᵖ(U, F_1)` as
an `A`-module propagates to every `Hᵖ(U, Iⁿ F_(n+1))`.

In degree zero this is `Stacks.Algebraization.finite_idealPowerSections_of_isoDirectSum`, proved
without derived functors because sections are not derived there. The degree that the source of
Stacks 0EJU needs and that file does not supply is degree **one**: hypothesis (3) of Stacks 0EJU
asks for `H⁰(U, F_1)` *and* `H¹(U, F_1)` to be finite `A`-modules, and the degree-one half is
used, through Cohomology 0GYK and 0GYM, on the graded module `⨁ₙ H¹(U, Iⁿ F_(n+1))`. Its
homogeneous pieces being finite `A`-modules is what this file proves.

## Main results

* `Stacks.Algebraization.finite_cohomologyOverBase_idealPowerSub_of_isoDirectSum` — from the
  direct-sum decomposition, finiteness of `Hᵖ(U, F_1)` gives finiteness of every
  `Hᵖ(U, Iⁿ F_(n+1))`.
* `Stacks.Algebraization.finite_cohomologyOverBase_idealPowerSub_of_flatLocalBase` — the same
  with the decomposition discharged from hypotheses (1) and (2) of Stacks 0EJU.
* `Stacks.Algebraization.finite_cohomologyOverBase_idealPowerSub_of_hasFiniteLowDegreeCohomology`
  — both low degrees at once, run off hypothesis (3) of the source as it is recorded in this
  library, `Stacks.Algebraization.HasFiniteLowDegreeCohomology`.

## Implementation notes

The cohomology object is `Stacks.LocalCohomology.cohomologyOverBase`, which is the spelling
hypothesis (3) uses in `Stacks.Algebraization.HasFiniteLowDegreeCohomology`. It is restriction of
scalars applied to a derived functor, so it is not itself a functor in the sheaf; the functorial
form is `Stacks.LocalCohomology.cohomologyOverBaseFunctor`, and
`Stacks.LocalCohomology.cohomologyOverBaseIsoRightDerived` identifies the two. The decomposition
is transported with `Stacks.LocalCohomology.cohomologyOverBaseLinearEquivOfIso`, and the direct
sum is split by `CategoryTheory.Functor.mapBiproduct` followed by `ModuleCat.biproductIsoPi`,
exactly as in degree zero.

Two instance obstacles are dealt with here rather than at the use sites. Additivity of a right
derived functor is not found by instance search, because `CategoryTheory.Functor.rightDerived` is
a composite of the injective-resolutions functor with a homology functor and neither factor's
additivity is an instance at that spelling; `Stacks.LocalCohomology.rightDerived_additive`
supplies it once. And the biproduct has to be formed in `AlgebraicGeometry.Scheme.Modules`, where
`Stacks.Algebraization.hasFiniteBiproducts_schemeModules` applies, rather than at the
`SheafOfModules` spelling of the same category, which is why
`Stacks.Algebraization.baseCohomologyFunctor` ascribes the domain.

## References

* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 0EJS](https://stacks.math.columbia.edu/tag/0EJS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v w

namespace Stacks.LocalCohomology

section DerivedAdditive

variable {C : Type*} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

/-- Taking injective resolutions is an additive functor to the homotopy category: two descents of
`f` and of `g` add to a descent of `f + g`, and descents are unique up to homotopy. -/
theorem injectiveResolutions_additive : (injectiveResolutions C).Additive where
  map_add {X Y} f g := by
    have h : (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (f + g) (injectiveResolution Y) (injectiveResolution X)) =
        (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X) +
            InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X)) := by
      apply HomotopyCategory.eq_of_homotopy
      apply InjectiveResolution.descHomotopy (f + g) <;>
        simp [Preadditive.comp_add, Preadditive.add_comp]
    exact h.trans ((HomotopyCategory.quotient C (ComplexShape.up ℕ)).map_add)

/-- **The right derived functors of an additive functor are additive.** -/
theorem rightDerived_additive {D : Type*} [Category.{w} D] [Abelian D]
    (G : C ⥤ D) [G.Additive] (p : ℕ) : (G.rightDerived p).Additive := by
  have := injectiveResolutions_additive (C := C)
  dsimp [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory]
  infer_instance

end DerivedAdditive

/-- Cohomology over the base ring is additive, being a right derived functor of the additive
functor of `A`-linear global sections. -/
instance cohomologyOverBaseFunctor_additive {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (p : ℕ) :
    (cohomologyOverBaseFunctor.{u, v} A f p).Additive :=
  rightDerived_additive (sectionsOverBase.{u, v} A f) p

end Stacks.LocalCohomology

namespace Stacks.Algebraization

attribute [local instance] hasFiniteBiproducts_schemeModules

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- `Hᵖ(U, -)` over the base ring `A`, with its domain written as
`AlgebraicGeometry.Scheme.Modules`. That is the same category as `SheafOfModules` over the
structure sheaf, but it is the spelling at which the finite biproducts of
`Stacks.Algebraization.hasFiniteBiproducts_schemeModules` are found. -/
abbrev baseCohomologyFunctor (p : ℕ) : S.U.toScheme.Modules ⥤ ModuleCat.{u} S.A :=
  Stacks.LocalCohomology.cohomologyOverBaseFunctor.{u, u} S.A S.U.ι p

/-- Cohomology over the base is additive at this spelling of its domain too. -/
instance baseCohomologyFunctor_additive (p : ℕ) : (baseCohomologyFunctor S p).Additive :=
  Stacks.LocalCohomology.cohomologyOverBaseFunctor_additive.{u, u} S.U.ι p

/-- Finiteness of `Hᵖ(U, -)` over the base is carried from `F_1` to a finite direct sum of copies
of it: the functor is additive, so it turns the direct sum into a product of `k` copies. -/
theorem finite_baseCohomologyFunctor_biproduct (p k : ℕ)
    (hp : Module.Finite S.A ((baseCohomologyFunctor S p).obj (F.obj.obj (op 0)))) :
    Module.Finite S.A
      ((baseCohomologyFunctor S p).obj (⨁ fun _ : Fin k => F.obj.obj (op 0))) := by
  have hpi : Module.Finite S.A
      (Fin k → ((baseCohomologyFunctor S p).obj (F.obj.obj (op 0)) : Type u)) :=
    Module.Finite.pi
  exact Module.Finite.equiv
    (M := (Fin k → ((baseCohomologyFunctor S p).obj (F.obj.obj (op 0)) : Type u)))
    (((baseCohomologyFunctor S p).mapBiproduct (fun _ : Fin k => F.obj.obj (op 0))).trans
      (ModuleCat.biproductIsoPi _)).symm.toLinearEquiv

/-- **Stacks Project, Tag 0EJU (the finiteness step, in every degree).** If `Iⁿ F_(n+1)` is
isomorphic to a finite direct sum of copies of `F_1` for every `n`, and `Hᵖ(U, F_1)` is a finite
`A`-module, then every `Hᵖ(U, Iⁿ F_(n+1))` is a finite `A`-module.

For `p = 0` this is `Stacks.Algebraization.finite_idealPowerSections_of_isoDirectSum`; the degree
the source needs beyond that one is `p = 1`. -/
theorem finite_cohomologyOverBase_idealPowerSub_of_isoDirectSum (p : ℕ)
    (hp : Module.Finite S.A
      (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι (F.obj.obj (op 0)) p))
    (hdec : ∀ n : ℕ, ∃ k : ℕ, Nonempty ((⨁ fun _ : Fin k => F.obj.obj (op 0)) ≅
      (idealPowerSub S F n).toSheafOfModules)) :
    ∀ n : ℕ, Module.Finite S.A (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι
      ((idealPowerSub S F n).toSheafOfModules) p) := by
  intro n
  obtain ⟨k, ⟨e⟩⟩ := hdec n
  have key : ∀ G : S.U.toScheme.Modules,
      Module.Finite S.A (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι G p) ↔
        Module.Finite S.A ((baseCohomologyFunctor S p).obj G) := fun G =>
    Module.Finite.equiv_iff
      (Stacks.LocalCohomology.cohomologyOverBaseIsoRightDerived.{u, u} S.A S.U.ι G p).toLinearEquiv
  have hbip := finite_baseCohomologyFunctor_biproduct S F p k ((key _).1 hp)
  exact (key _).2 (Module.Finite.equiv ((baseCohomologyFunctor S p).mapIso e).toLinearEquiv)

/-- **The finiteness step of the proof of Stacks 0EJU, in every degree.** Over a Noetherian local
base `R → A` with `I = 𝔪 A` and formal stalks flat over `R`
along `U ∩ Y`, finiteness of `Hᵖ(U, F_1)` gives finiteness of every `Hᵖ(U, Iⁿ F_(n+1))`.

The decomposition is `Stacks.Algebraization.exists_isoDirectSum_idealPowerSub`. -/
theorem finite_cohomologyOverBase_idealPowerSub_of_flatLocalBase (B : FlatLocalBase S F) (p : ℕ)
    (hp : Module.Finite S.A
      (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι (F.obj.obj (op 0)) p)) :
    ∀ n : ℕ, Module.Finite S.A (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι
      ((idealPowerSub S F n).toSheafOfModules) p) :=
  finite_cohomologyOverBase_idealPowerSub_of_isoDirectSum S F p hp
    fun m => exists_isoDirectSum_idealPowerSub S F B m

/-- **Hypothesis (3) of Stacks 0EJU in use.** Under hypotheses (1), (2) and (3) of
Stacks 0EJU, every `H⁰(U, Iⁿ F_(n+1))` and every `H¹(U, Iⁿ F_(n+1))` is a finite `A`-module.

Hypothesis (3) is `Stacks.Algebraization.HasFiniteLowDegreeCohomology`, the same predicate
Stacks 0EJS uses. The degree-zero conclusion is
`Stacks.Algebraization.finite_idealPowerSections_of_flatLocalBase`; this adds the degree-one one,
which is what conditions (a) and (b) of Stacks 0EHH are derived from in the source. -/
theorem finite_cohomologyOverBase_idealPowerSub_of_hasFiniteLowDegreeCohomology
    (B : FlatLocalBase S F) (h3 : HasFiniteLowDegreeCohomology S F) :
    (∀ n : ℕ, Module.Finite S.A (idealPowerSections S F n)) ∧
      ∀ n : ℕ, Module.Finite S.A (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι
        ((idealPowerSub S F n).toSheafOfModules) 1) :=
  ⟨finite_idealPowerSections_of_flatLocalBase S F B h3.1,
    finite_cohomologyOverBase_idealPowerSub_of_flatLocalBase S F B 1 h3.2⟩

end Stacks.Algebraization

end
