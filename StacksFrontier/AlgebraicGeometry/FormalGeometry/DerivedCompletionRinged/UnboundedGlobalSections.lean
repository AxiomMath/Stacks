module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalSectionsCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalCalculation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Pushforward
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# Unbounded derived global sections and the identity of Tag 0BLX

Let `A` be a ring, `I ⊂ A` a finitely generated ideal, `(𝒞, 𝒪)` a ringed site with `𝒪` a sheaf
of `A`-algebras, `𝓘 = I𝒪` the ideal sheaf `I` generates and `ℱ` a sheaf of `𝒪`-modules. The
identity of [Stacks, Tag 0BLX] is
```
RΓ(𝒞, ℱ)^∧ = RΓ(𝒞, ℱ^∧)   in D(A),
```
the completion on the left along `I` and the one on the right along `I𝒪`. This file supplies the
functor the right hand side needs — `A`-linear derived global sections on the *unbounded* derived
category — and proves the identity, as an isomorphism in `D(A)`, in the regime in which this
library has the derived completion functor on `D(𝒪)` at all.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsOverUnbounded`:
  **`RΓ(𝒞, -) : D(𝒪) ⥤ D(A)`**, the total right derived functor of `A`-linear global sections on
  the whole unbounded derived category.
* `AlgebraicGeometry.RingedSite.homotopyGlobalSectionsOver` and
  `AlgebraicGeometry.RingedSite.derivedGlobalSectionsOverUnboundedUnit`: the functor it is
  derived from, and the canonical comparison exhibiting it as that derived functor.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_map_derivedCompletionUnit_derivedGlobalSections`: the
  canonical map `RΓ(𝒞, K) ⟶ RΓ(𝒞, K^∧)` is invertible when the local sections of `I𝒪` are
  nilpotent — the left hand side of the identity.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_derivedGlobalSectionsOverUnbounded`:
  `RΓ(𝒞, K)` is derived complete along `I` when every `a ∈ I` has nilpotent image in
  `Γ(𝒞, 𝒪)` — the right hand side of the identity.
* `AlgebraicGeometry.RingedSite.smul_id_derivedGlobalSectionsOverUnbounded_eq_zero`: a scalar
  killed by `ρ` acts as zero on `RΓ(𝒞, K)`, which is what makes that work.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_map_derivedGlobalSectionsOverUnbounded`:
  **[Stacks, Tag 08U1]** for this functor — `RΓ(𝒞, -)` carries a derived inverse limit in `D(𝒪)`
  to one in `D(A)`. This is the first of the two ingredients the general case of Tag 0BLX needs;
  see the implementation note below.
* `AlgebraicGeometry.RingedSite.exists_iso_derivedCompletion_derivedGlobalSections`:
  **the identity of [Stacks, Tag 0BLX]** in that regime, as an isomorphism in `D(A)`, together
  with the derived completion functor on `D(A)` it is stated with.

## Implementation notes

*Why an unbounded `RΓ`.* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsOver` of
`GlobalSectionsCompletion.lean` is the right derived functor of `Γ(𝒞, -)` on `D⁺(𝒪)`, which is
enough for `RΓ(𝒞, ℱ)` of a sheaf but not for `RΓ(𝒞, ℱ^∧)`: the derived completion `ℱ^∧` is not
known to be bounded below, and the Koszul formula [Stacks, Tag 0A0E] does not make it so, being a
derived limit of a tower that is not uniformly bounded. So the right hand side of Tag 0BLX cannot
be formed with the bounded-below functor unless a bounded-below representative of `ℱ^∧` is
supplied from outside. The total right derived functor on the unbounded
`D(𝒪)` exists with no such input, `Mod(𝒪)` being Grothendieck abelian and hence having
K-injective resolutions
(`Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck`); it is defined here in
the same shape as `AlgebraicGeometry.RingedSite.derivedSectionsOver` of `LocalCalculation.lean`,
which does this for the sections over a single object of the site. Both sides of the identity
below are therefore formed with one and the same `RΓ(𝒞, -) : D(𝒪) ⥤ D(A)`.

The comparison of this functor with the bounded-below
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsOver` — both are right derived functors of
`Γ(𝒞, -)`, so they agree on `D⁺(𝒪)` — is not proved here; the statements below do not use it,
being stated throughout with the unbounded functor. It is proved, on bounded below complexes, as
`AlgebraicGeometry.RingedSite.nonempty_iso_derivedGlobalSectionsOverUnbounded_of_plus` of
`GlobalSectionsCompletionWhole.lean`.

*The regime of the identity.* The derived completion functor on `D(𝒪)` is [Stacks, Tag 099F],
which this library has only for a sheaf of ideals whose local sections are nilpotent
(`isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent`, in `NilpotentIdeal.lean`). That
hypothesis is therefore carried, and *discharged*: the instance is produced from it inside the
statement rather than assumed. For the completion on `D(A)` to be the identity on `RΓ(𝒞, ℱ)` the
corresponding hypothesis is that `ρ a` be nilpotent in `Γ(𝒞, 𝒪)` for every `a ∈ I`. That does
not follow from the nilpotence of the local sections of `I𝒪` — a section of `I𝒪` is nilpotent
with an exponent that may vary with the object of the site, so `ρ a` need not be nilpotent in
`Γ(𝒞, 𝒪)` — and it does not make `A` itself `I`-adically complete, nor the completion functor on
`D(A)` trivial: `A = ℤ_p`, `I = (p)` and `𝒪` a sheaf of `ℤ/pⁿ`-algebras satisfies it. Both
hypotheses are hypotheses on the data, not stand-ins for unproved results: the finite generation
of `I` and the relation `𝓘 = I𝒪` are the source's own, and the two nilpotence hypotheses
restrict the statement to a special case of the source's rather than assume any part of its
conclusion.

In that regime both completions are the identity and the identity of Tag 0BLX is the composite of
its two halves, exactly as [Stacks, Tag 0CQI] is assembled in `LocalCalculation.lean` for the
sections over an object. The general case is the one the source proves in a line, by applying
[Stacks, Tag 0A0G] to the morphism of ringed topoi `(𝒞, 𝒪) ⟶ (pt, A)`; of Tag 0A0G this library
has the comparison map and a criterion for its invertibility
(`PushforwardCommutesCompletion.lean`) but not the invertibility, and there is no morphism of
ringed sites or ringed topoi from a general ringed site to the ringed point, so that route is not
available — see the "How Tag 0BLX is completed" section of `GlobalSectionsCompletion.lean`. The
general case is proved by another route, through the Koszul formula
(`nonempty_iso_derivedCompletion_derivedGlobalSections` of
`GlobalSectionsCompletionKoszulIdentity.lean`), and the whole tag is
`exists_iso_and_pages_derivedCompletion_globalSections` of `GlobalSectionsCompletionWhole.lean`.

*The route that is open, and the one thing it still needs.* [Stacks, Tag 0A0E] is now proved,
`AlgebraicGeometry.RingedSite.isDerivedLimit_koszulTower_completionFunctor` of
`KoszulCechHomotopyColimit.lean`, so `ℱ^∧` is a derived limit of `n ↦ ℱ ⊗^𝐋_𝒪 K_n^∨` for the
Koszul complexes on the powers of generators of `I𝒪`; the module-side formula is
`AdicKoszulAdjunction.koszulPowerDerivedLimit_isLeftAdjoint` of
`StacksFrontier/Homology/DerivedComplete/AdicDerivedCompletion.lean`, [Stacks, Tag 0920], which
exhibits the completion functor on `D(A)` as the derived limit of `n ↦ L ⊗^𝐋_A L_n^∨`; and
`isDerivedLimit_map_derivedGlobalSectionsOverUnbounded` below carries the one derived limit
through `RΓ(𝒞, -)`. What is missing between them is the **Koszul projection formula**

```
RΓ(𝒞, ℱ ⊗^𝐋_𝒪 K_n^∨) ≅ RΓ(𝒞, ℱ) ⊗^𝐋_A L_n^∨,
```

derived global sections commuting with tensoring by a bounded complex of finite free modules.
What exists is the two-term case: on a ringed site and for `RΓ(𝒞, -)` itself,
`AlgebraicGeometry.RingedSite.nonempty_iso_koszulConeTower_derivedGlobalSections` of
`PrincipalKoszulGlobalSections.lean` in this directory, which carries the tower of cones of the
powers of multiplication by one global section to the `f`-power Koszul tower of `RΓ(𝒞, E)` over
`A`; and on a ringed *space*,
`Stacks.Cohomology.KoszulTowerSections.nonempty_iso_koszulTower_derivedSections` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/PrincipalKoszulTowerDerivedSections.lean`, with the
full `r = 1` assembly of this identity there,
`nonempty_iso_derivedSections_koszulTower_derivedCompletion` of the namespace
`Stacks.Cohomology.PrincipalFormalFunctions`, in `PrincipalFormalFunctionsDiagram.lean`.

Neither reaches the tower of this tag, even at `r = 1`. The tower of [Stacks, Tag 0A0E] is formed
with the *derived dual* `K_n^∨ = R𝑆heafHom_𝒪(K_n, 𝒪)`, and that dual *is* now identified with the
Koszul cochain complex in degrees `-r, …, 0`, by
`AlgebraicGeometry.RingedSite.derivedDualKoszulPowerComplexIso` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/DualOfKoszulComplex.lean`, so the Koszul
cochain complex is available as a complex of finite free modules with the transposed differentials.
What is still missing before the two-term formula can act, at `r = 1`, is the derived tensor
product of an object of `D(𝒪)` with a two-term complex of free modules of rank one identified with
a cone of multiplication by `f^(n+1)`, and the compatibility of the identification with the
transition maps of the Koszul system, which the tower-level statement needs. Beyond those the
general case would need the Koszul cochain complex of
`AlgebraicGeometry.RingedSite.koszulPowerComplex` presented as an `r`-fold iterated cone of
two-term complexes, and the same on the module side for `AdicKoszul.canonicalKoszulPowerSystem`,
whose terms come from `Koszul.seqComplex`; and then the universe comparison between
`D(ModuleCat.{u} A)`, where `RΓ(𝒞, -)` lands, and the `D(ModuleCat.{max u v} (ULift.{v} A))` of
`AdicKoszul.tensorKoszulPowerSystem`.

The projection formula for a *site*, [Stacks, Tag 0944], is not proved either: only its map,
`Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap`, and a dévissage missing
its base case, and in any case it is about `Rf_*` rather than `RΓ(𝒞, -)`, which is not an `Rf_*`
here for want of a morphism to the ringed point.

*The completion functor on `D(A)`.* Produced, not assumed: for a finitely generated `I` the
inclusion of the derived-complete objects of `D(A)` has a left adjoint by [Stacks, Tag 0920], and
that is read off the package of [Stacks, Tag 0BKE],
`AdicFilteredCompletion.exists_spectralSequence_derivedCompletion_homology`, which is also what
the first spectral sequence of Tag 0BLX in `GlobalSectionsCompletion.lean` uses. The functor is
existentially quantified for the same reason it is there: the library fixes no choice of it.

## References

* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 0920](https://stacks.math.columbia.edu/tag/0920)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0BKE](https://stacks.math.columbia.edu/tag/0BKE)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0CQI](https://stacks.math.columbia.edu/tag/0CQI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

section Unbounded

variable (X : RingedSite.{u, u, u}) (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

/-- `A`-linear global sections read on the homotopy category of cochain complexes of
`𝒪`-modules, with values in `D(A)`. Its total right derived functor is
`derivedGlobalSectionsOverUnbounded`. -/
abbrev homotopyGlobalSectionsOver :
    HomotopyCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (moduleGlobalSectionsOver X A ρ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- **`RΓ(𝒞, -) : D(𝒪) ⥤ D(A)`**, `A`-linear derived global sections on the whole unbounded
derived category. It exists because `Mod(𝒪)` is Grothendieck abelian, hence has functorial
K-injective resolutions; no boundedness of the argument is needed, which is what the right hand
side of [Stacks, Tag 0BLX] requires. -/
abbrev derivedGlobalSectionsOverUnbounded :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (homotopyGlobalSectionsOver X A ρ).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (ComplexShape.up ℤ))

/-- The canonical comparison from termwise `A`-linear global sections to their total right
derived functor. -/
abbrev derivedGlobalSectionsOverUnboundedUnit :
    homotopyGlobalSectionsOver X A ρ ⟶
      DerivedCategory.Qh ⋙ derivedGlobalSectionsOverUnbounded X A ρ :=
  (homotopyGlobalSectionsOver X A ρ).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (ComplexShape.up ℤ))

/-- The comparison exhibits `derivedGlobalSectionsOverUnbounded` as the right derived functor of
`A`-linear global sections, which is the universal property characterizing it. -/
instance derivedGlobalSectionsOverUnbounded_isRightDerivedFunctor :
    (derivedGlobalSectionsOverUnbounded X A ρ).IsRightDerivedFunctor
      (derivedGlobalSectionsOverUnboundedUnit X A ρ)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (ComplexShape.up ℤ)) :=
  inferInstance

/-- `A`-linear global sections preserve countable products: they are
`Hom_𝒪(𝒪, -)`, which preserves all limits, followed by restriction of scalars along `ρ`. -/
instance preservesLimitsOfShape_discrete_moduleGlobalSectionsOver :
    PreservesLimitsOfShape (Discrete ℕ) (moduleGlobalSectionsOver X A ρ) :=
  haveI : PreservesLimitsOfShape (Discrete ℕ)
      (ModuleCat.restrictScalars.{u} ((globalSectionMulEnd X).comp ρ)) :=
    ⟨fun {_} ↦ inferInstance⟩
  haveI : PreservesLimitsOfSize.{0, 0}
      (preadditiveCoyonedaObj (SheafOfModules.unit (ringSheaf X.O))) :=
    preservesSmallestLimits_of_preservesLimits _
  comp_preservesLimitsOfShape
    (preadditiveCoyonedaObj (SheafOfModules.unit (ringSheaf X.O)))
    (ModuleCat.restrictScalars ((globalSectionMulEnd X).comp ρ))

/-- **`RΓ(𝒞, -)` over a base ring commutes with `R lim`**: `A`-linear derived global sections
carry a derived inverse limit in `D(𝒪)` to a derived inverse limit in `D(A)`.

This is [Stacks, Tag 08U1] for `derivedGlobalSectionsOverUnbounded`, through
`Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`: the functor is the right derived
functor of `moduleGlobalSectionsOver` by
`derivedGlobalSectionsOverUnbounded_isRightDerivedFunctor`, that functor preserves countable
products, `Mod(𝒪)` is Grothendieck abelian and the countable products of `ModuleCat A` are
exact. This is the site-and-base-ring form of [Stacks, Tag 0D6K], whose `Γ(𝒞, -)`-valued form
is `Stacks.Cohomology.DerivedGlobalSections.isDerivedLimit_map_derivedGlobalSections`, and the
ringed-site counterpart of [Stacks, Tag 0D60] for a ringed space,
`Stacks.Cohomology.DerivedSectionsOverBase.isDerivedLimit_map_derivedSectionsOver`. -/
@[stacks 08U1 "for A-linear derived global sections on a ringed site"]
theorem isDerivedLimit_map_derivedGlobalSectionsOverUnbounded
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O)))
    (hL : Pretriangulated.IsDerivedLimit K L) :
    ∃ h : HasProduct
        (fun n : ℕ ↦ (derivedGlobalSectionsOverUnbounded X A ρ).obj (K.obj ⟨n⟩)),
      @Pretriangulated.IsDerivedLimit (DerivedCategory (ModuleCat.{u} A)) _ _ _ _ _ _
        (K ⋙ derivedGlobalSectionsOverUnbounded X A ρ) h
        ((derivedGlobalSectionsOverUnbounded X A ρ).obj L) := by
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
    moduleCat_hasExactLimitsOfShape_discrete A ℕ
  obtain ⟨p, δ, htri⟩ := hL
  obtain ⟨hprod, δ', htri'⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
    (F := moduleGlobalSectionsOver X A ρ) (derivedGlobalSectionsOverUnbounded X A ρ)
    (derivedGlobalSectionsOverUnboundedUnit X A ρ) K L p ⟨δ, htri⟩
  let := hprod
  exact ⟨hprod, _, δ', htri'⟩

end Unbounded

section Identity

/-- The unit of the reflector onto a full subcategory is invertible at an object of that
subcategory: the inclusion is fully faithful, so the unit is invertible on its image. This is
`AlgebraicGeometry.RingedSite.isIso_derivedCompletionUnit_app` of `ReflectorCompletion.lean`,
stated for an arbitrary object property. -/
private theorem isIso_ofIsRightAdjoint_unit_app {C : Type*} [Category C] (P : ObjectProperty C)
    [(ObjectProperty.ι P).IsRightAdjoint] {L : C} (hL : P L) :
    IsIso ((Adjunction.ofIsRightAdjoint (ObjectProperty.ι P)).unit.app L) := by
  have h : IsIso (Functor.whiskerLeft (ObjectProperty.ι P)
      (Adjunction.ofIsRightAdjoint (ObjectProperty.ι P)).unit) := inferInstance
  exact NatIso.isIso_app_of_isIso
    (Functor.whiskerLeft (ObjectProperty.ι P)
      (Adjunction.ofIsRightAdjoint (ObjectProperty.ι P)).unit)
    (⟨L, hL⟩ : ObjectProperty.FullSubcategory P)

variable (A : Type u) [CommRing A] (I : Ideal A) (X : RingedSite.{u, u, u})
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)
  (𝓘 : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **The left hand side of the identity of [Stacks, Tag 0BLX]**, for an ideal sheaf whose local
sections are nilpotent: the canonical map `RΓ(𝒞, K) ⟶ RΓ(𝒞, K^∧)` is invertible.

Every object of `D(𝒪)` is derived complete along a sheaf of ideals whose local sections are
nilpotent, so `K ⟶ K^∧` is itself invertible and derived global sections carry it to an
isomorphism. The instance the derived completion functor needs — the conclusion of
[Stacks, Tag 099F] — is produced from the nilpotence hypothesis, not assumed. -/
theorem isIso_map_derivedCompletionUnit_derivedGlobalSections
    (hnil : ∀ (V : X.C) (g : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op V)),
      g ∈ 𝓘.toSubmodule.obj (op V) → IsNilpotent g)
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    letI : (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint :=
      isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent X 𝓘 hnil
    IsIso ((derivedGlobalSectionsOverUnbounded X A ρ).map
      ((derivedCompletionUnit X 𝓘).app K)) := by
  let : (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint :=
    isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent X 𝓘 hnil
  have := isIso_derivedCompletionUnit_app X 𝓘
    (isDerivedComplete_of_forall_isNilpotent X 𝓘 hnil K)
  exact (derivedGlobalSectionsOverUnbounded X A ρ).map_isIso _

/-- A scalar killed by `ρ` acts as zero on `Γ(𝒞, M)`: the `A`-action there is restriction of
scalars along `globalSectionMulEnd ∘ ρ`, which sends it to zero. -/
theorem smul_id_moduleGlobalSectionsOver_eq_zero (c : A) (hc : ρ c = 0)
    (P : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    c • 𝟙 ((moduleGlobalSectionsOver X A ρ).obj P) = 0 := by
  have h0 : ((globalSectionMulEnd X).comp ρ) c = 0 := by
    rw [RingHom.comp_apply, hc, map_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((globalSectionMulEnd X).comp ρ) c •
    (show ((preadditiveCoyonedaObj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj P) from x) = 0
  rw [h0, zero_smul]

/-- A scalar killed by `ρ` acts as zero on `RΓ(𝒞, K)` for every `K ∈ D(𝒪)`.

Both `0 ∈ ℤ` and `c ∈ A` are carried to multiplication by `c` on the image of `Γ(𝒞, -)`, by
`smul_id_moduleGlobalSectionsOver_eq_zero`, and a right derived functor inherits that — this is
`Stacks.SemilinearFunctor.map_smul_id_rightDerived` of `Pushforward.lean`. Applying it twice, at
the target scalars `c` and `0`, identifies `c • 𝟙 (RΓ(𝒞, K))` with `0 • 𝟙 (RΓ(𝒞, K))`. -/
theorem smul_id_derivedGlobalSectionsOverUnbounded_eq_zero (b : A) (hb : ρ b = 0)
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    b • 𝟙 ((derivedGlobalSectionsOverUnbounded X A ρ).obj K) = 0 := by
  have hchain : ∀ c : A, ρ c = 0 →
      ∀ M : HomotopyCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ),
        (homotopyGlobalSectionsOver X A ρ).map ((0 : ℤ) • 𝟙 M) =
          c • 𝟙 ((homotopyGlobalSectionsOver X A ρ).obj M) := by
    intro c hc M
    refine Stacks.SemilinearFunctor.map_smul_id_comp
      ((moduleGlobalSectionsOver X A ρ).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (0 : ℤ) c (fun N => ?_) M
    refine Stacks.SemilinearFunctor.map_smul_id_mapHomotopyCategory
      (moduleGlobalSectionsOver X A ρ) (0 : ℤ) c (fun P => ?_) (ComplexShape.up ℤ) N
    rw [zero_smul, Functor.map_zero,
      smul_id_moduleGlobalSectionsOver_eq_zero A X ρ c hc P]
  have key : ∀ c : A, ρ c = 0 →
      (derivedGlobalSectionsOverUnbounded X A ρ).map ((0 : ℤ) • 𝟙 K) =
        c • 𝟙 ((derivedGlobalSectionsOverUnbounded X A ρ).obj K) := fun c hc ↦
    Stacks.SemilinearFunctor.map_smul_id_rightDerived
      (derivedGlobalSectionsOverUnbounded X A ρ)
      (derivedGlobalSectionsOverUnboundedUnit X A ρ)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (ComplexShape.up ℤ))
      (0 : ℤ) c (hchain c hc) K
  rw [← key b hb, key 0 (map_zero ρ), zero_smul]

/-- **The right hand side of the identity of [Stacks, Tag 0BLX]**: `RΓ(𝒞, K)` is already derived
complete along `I`, so its derived completion is itself, as soon as every element of `I` has
nilpotent image in `Γ(𝒞, 𝒪)`.

If `(ρ a)ⁿ = 0` then `ρ (aⁿ) = 0`, so `aⁿ` acts as zero on `RΓ(𝒞, K)` by
`smul_id_derivedGlobalSectionsOverUnbounded_eq_zero`; since `(a • 𝟙)ⁿ = aⁿ • 𝟙`, multiplication
by `a` is nilpotent, and an object on which a scalar acts nilpotently is derived complete at it.
The hypothesis holds a fortiori when the elements of `I` are nilpotent in `A`. -/
theorem isDerivedComplete_derivedGlobalSectionsOverUnbounded
    (hρnil : ∀ a ∈ I, IsNilpotent (ρ a))
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    _root_.IsDerivedComplete I ((derivedGlobalSectionsOverUnbounded X A ρ).obj K) := by
  intro a ha
  obtain ⟨n, hn⟩ := hρnil a ha
  refine isDerivedCompleteAt_of_isNilpotent ⟨n, ?_⟩
  ext
  rw [smul_id_pow, End.zero_asHom]
  exact smul_id_derivedGlobalSectionsOverUnbounded_eq_zero A X ρ (a ^ n)
    (by rw [map_pow, hn]) K

/-- **The identity `RΓ(𝒞, ℱ)^∧ = RΓ(𝒞, ℱ^∧)` of [Stacks, Tag 0BLX], in the nilpotent regime.**
Let `A` be a ring, `I ⊂ A` a
finitely generated ideal, `(𝒞, 𝒪)` a ringed site with `𝒪` a sheaf of `A`-algebras, `𝓘 = I𝒪` the
ideal sheaf `I` generates and `ℱ` a sheaf of `𝒪`-modules. Then the derived completion of
`RΓ(𝒞, ℱ)` along `I` is `RΓ(𝒞, ℱ^∧)`, the derived completion of `ℱ` being taken along `I𝒪`. The
derived completion functor on `D(A)` is produced rather than assumed, by [Stacks, Tag 0920].

This is proved in the regime in which both completions are available and are the identity: the
local sections of `I𝒪` nilpotent, which is the hypothesis under which this library has
[Stacks, Tag 099F] and hence `(-)^∧` on `D(𝒪)` at all, and the image `ρ a` of each `a ∈ I`
nilpotent in `Γ(𝒞, 𝒪)`, which is the corresponding hypothesis on the `A`-algebra structure and
does not follow from the first. Both are restrictions of the source's generality, not
substitutes for any part of its conclusion; the instance [Stacks, Tag 099F] provides is
discharged from the first rather than carried. The derived completion functor on `D(A)` is not
itself trivial under these hypotheses — `A` may be `I`-adically incomplete — what is proved is
that it is the identity on `RΓ(𝒞, ℱ)`.

The two halves are `isIso_map_derivedCompletionUnit_derivedGlobalSections`, which identifies
`RΓ(𝒞, ℱ^∧)` with `RΓ(𝒞, ℱ)`, and `isDerivedComplete_derivedGlobalSectionsOverUnbounded`, which
identifies `RΓ(𝒞, ℱ)^∧` with `RΓ(𝒞, ℱ)` — the same assembly as [Stacks, Tag 0CQI] in
`LocalCalculation.lean`. The source's one-line proof of the general case applies
[Stacks, Tag 0A0G] to the morphism of ringed topoi `(𝒞, 𝒪) ⟶ (pt, A)`; that route is not
available here, and the module documentation says what is. The general case is proved through the
Koszul formula, as `nonempty_iso_derivedCompletion_derivedGlobalSections` of
`GlobalSectionsCompletionKoszulIdentity.lean`.

This is one part of the tag and carries no `@[stacks 0BLX]` attribute: the whole lemma, at the
source's own hypotheses, is
`AlgebraicGeometry.RingedSite.exists_iso_and_pages_derivedCompletion_globalSections` of
`GlobalSectionsCompletionWhole.lean`, which is registered. -/
theorem exists_iso_derivedCompletion_derivedGlobalSections
    (hI : I.FG) (h𝓘 : IsIdealSheafGeneratedBy A I X ρ 𝓘)
    (hρnil : ∀ a ∈ I, IsNilpotent (ρ a))
    (hnil : ∀ (V : X.C) (g : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op V)),
      g ∈ 𝓘.toSubmodule.obj (op V) → IsNilpotent g)
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    letI : (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint :=
      isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent X 𝓘 hnil
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ _root_.IsDerivedComplete I L
    ∃ completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory,
      Nonempty (completion ⊣ P.ι) ∧
      Nonempty ((completion ⋙ P.ι).obj
          ((derivedGlobalSectionsOverUnbounded X A ρ).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F)) ≅
        (derivedGlobalSectionsOverUnbounded X A ρ).obj
          ((derivedCompletion X 𝓘).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F))) := by
  -- `h𝓘` is what makes `𝓘` be `I𝒪`; it is a hypothesis of the source statement rather than an
  -- input of this derivation, so it is recorded and not consumed.
  obtain ⟨-, -⟩ := h𝓘
  let : (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint :=
    isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent X 𝓘 hnil
  set P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun L ↦ _root_.IsDerivedComplete I L with hP
  set S := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F with hS
  set L := (derivedGlobalSectionsOverUnbounded X A ρ).obj S with hL
  obtain ⟨completion₀, adj₀, -⟩ :=
    AdicFilteredCompletion.exists_spectralSequence_derivedCompletion_homology A I hI L
  have : (ObjectProperty.ι P).IsRightAdjoint := ⟨completion₀, ⟨adj₀⟩⟩
  refine ⟨(ObjectProperty.ι P).leftAdjoint, ⟨Adjunction.ofIsRightAdjoint _⟩, ⟨?_⟩⟩
  have hcomplete : P L :=
    isDerivedComplete_derivedGlobalSectionsOverUnbounded A I X ρ hρnil _
  have := isIso_ofIsRightAdjoint_unit_app P hcomplete
  have : IsIso ((derivedGlobalSectionsOverUnbounded X A ρ).map
      ((derivedCompletionUnit X 𝓘).app S)) :=
    isIso_map_derivedCompletionUnit_derivedGlobalSections A X ρ 𝓘 hnil S
  exact (asIso ((Adjunction.ofIsRightAdjoint (ObjectProperty.ι P)).unit.app L)).symm ≪≫
    asIso ((derivedGlobalSectionsOverUnbounded X A ρ).map ((derivedCompletionUnit X 𝓘).app S))

end Identity

end AlgebraicGeometry.RingedSite

end
