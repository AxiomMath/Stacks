module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjections
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyLimit

/-!
# The canonical projections of completed local cohomology onto the tower

Let `I` and `J` be ideals of a commutative ring `A`, let `M` be an `A`-module and `Z = V(J)`.
The tower `n ↦ RΓ_Z(M/IⁿM)` of `Dualizing.adicQuotientLocalCohomologySystem` carries a canonical
cone with vertex `RΓ_Z(M)`, obtained by applying `RΓ_Z` to the quotient maps `M ⟶ M/IⁿM`.

Every term of the tower is derived `I`-complete, because `Iⁿ` annihilates `M/IⁿM`. So each
canonical map `RΓ_Z(M) ⟶ RΓ_Z(M/IⁿM)` factors *uniquely* through the derived `I`-adic completion
unit `RΓ_Z(M) ⟶ RΓ_Z(M)^∧`, and that factorization is what this file names: the **canonical
projection**

`Dualizing.completedLocalCohomologyProjection : RΓ_Z(M)^∧ ⟶ RΓ_Z(M/IⁿM)`.

These projections form a cone, and they are pinned: they are characterized by their composites
with the completion unit being the canonical maps, so no choice is involved. This is the arrow
that `Dualizing.completedLocalCohomologyToLimit` fails to provide — that map is cut out by
`Classical.choose` from a Milnor existential whose only clause about the projections refers to
the structural map of an unpinned `CategoryTheory.Pretriangulated.IsDerivedLimit` witness.

## Main definitions

* `Dualizing.adicQuotientProjection` — the quotient map `M ⟶ M/IⁿM`, into the `n`-th term of
  `AlgebraicGeometry.ProEtale.adicQuotientModuleSystem`.
* `Dualizing.localCohomologyAdicQuotientMap` — the canonical map
  `RΓ_Z(M) ⟶ RΓ_Z(M/IⁿM)`, into the `n`-th term of
  `Dualizing.adicQuotientLocalCohomologySystem`.
* `Dualizing.completedLocalCohomologyProjection` — the canonical projection
  `RΓ_Z(M)^∧ ⟶ RΓ_Z(M/IⁿM)`.

## Main results

* `Dualizing.adicQuotientProjection_succ_comp_map`,
  `Dualizing.localCohomologyAdicQuotientMap_succ_comp_map` — both families are cones.
* `Dualizing.isDerivedComplete_adicQuotientLocalCohomologySystem_obj` — every term of the tower
  is derived `I`-complete.
* `Dualizing.completedLocalCohomologyUnit_comp_projection` — the defining property: the
  completion unit followed by the canonical projection is the canonical map.
* `Dualizing.completedLocalCohomologyProjection_unique` — the canonical projection is the only
  map with that property.
* `Dualizing.completedLocalCohomologyProjection_succ_comp_map`,
  `Dualizing.completedLocalCohomologyProjection_comp_map` — the canonical projections form a
  cone.
* `Dualizing.isDerivedComplete_of_isDerivedLimitWithProjections` — a derived limit of the tower
  is derived `I`-complete.
* `Dualizing.exists_isDerivedLimitWithProjections_lift_localCohomologyAdicQuotientMap` — the
  tower has a derived-limit presentation with projections, and the canonical maps factor through
  them.
* `Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection` — the canonical
  projections present `RΓ_Z(M)^∧` as a derived limit of the tower, as soon as one presentation
  with projections has a derived-completion unit for its lift.

## Implementation notes

The conclusion of
`Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection` is the pinned form
of [Stacks, Tag 0EEW] part (1), and it is what the Artinian argument for part (1) of
[Stacks, Tag 0EFY] at `T = {𝔪}` consumes. What remains in order to obtain it unconditionally,
combining that theorem with
`Dualizing.exists_isDerivedLimitWithProjections_lift_localCohomologyAdicQuotientMap`, is exactly
one statement:

> for a derived-limit presentation `K'`, `π'` of the tower `n ↦ RΓ_Z(M/IⁿM)` and the lift
> `v : RΓ_Z(M) ⟶ K'` of the cone of canonical maps, composing with `v` is a bijection
> `Hom(K', E) ⟶ Hom(RΓ_Z(M), E)` for every derived `I`-complete `E`;

that is, `v` is a derived `I`-adic completion unit. The library has [Stacks, Tag 0EEW] part (1)
only as `Dualizing.isDerivedLimit_completedLocalCohomology`, whose `IsDerivedLimit` pins no cone
and therefore says nothing about `v`. The data that would supply it is carried by the Koszul and
Čech models of derived completion — `AdicKoszul.KoszulPowerCompletion` has a `unit_projection`
field and `NoetherianAdicCompletion.koszulPowerCompletion_idealPowerCone` gives
`IsDerivedLimitWithProjections` for the ideal-power tensor tower together with the unit
compatibility — but those statements live over `ULift` of the ring, through
`AdicKoszul.derivedUniverseLift`, and bringing them down requires identifying
`NoetherianAdicCompletion.derivedReductionMap` across that universe lift and across the
pro-isomorphism of
`Dualizing.AdicQuotientComparison.exists_idealPowerTensor_adicQuotient_comparison`.

## References

* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

section Cone

variable (A : Type u) [CommRing A]

/-- The quotient map `M ⟶ M/IⁿM`, landing in the `n`-th term of the tower
`AlgebraicGeometry.ProEtale.adicQuotientModuleSystem`. -/
def adicQuotientProjection (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    M ⟶ (adicQuotientModuleSystem A I M).obj (op n) :=
  ModuleCat.ofHom (Submodule.mkQ (I ^ n • (⊤ : Submodule A M)))

/-- The quotient maps `M ⟶ M/IⁿM` form a cone on the tower `n ↦ M/IⁿM`. -/
theorem adicQuotientProjection_succ_comp_map (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    adicQuotientProjection A I M (n + 1) ≫
        (adicQuotientModuleSystem A I M).map (homOfLE (Nat.le_succ n)).op =
      adicQuotientProjection A I M n := by
  rw [adicQuotientModuleSystem_map A I M (Nat.le_succ n)]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  rfl

/-- The quotient maps `M ⟶ M/IⁿM` are compatible with every transition map of the tower, not
only with the successor ones. -/
theorem adicQuotientProjection_comp_map (I : Ideal A) (M : ModuleCat.{u} A) {n m : ℕ}
    (h : n ≤ m) :
    adicQuotientProjection A I M m ≫ (adicQuotientModuleSystem A I M).map (homOfLE h).op =
      adicQuotientProjection A I M n := by
  rw [adicQuotientModuleSystem_map A I M h]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  rfl

/-- The canonical map `RΓ_Z(M) ⟶ RΓ_Z(M/IⁿM)`, landing in the `n`-th term of the tower
`Dualizing.adicQuotientLocalCohomologySystem`: local cohomology applied to the quotient map. -/
def localCohomologyAdicQuotientMap (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A) (n : ℕ) :
    (Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶
      (adicQuotientLocalCohomologySystem A I J hJ M).obj (op n) :=
  (Stacks.LocalCohomology.localCohomologyDerived A J hJ).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (adicQuotientProjection A I M n))

/-- The canonical maps `RΓ_Z(M) ⟶ RΓ_Z(M/IⁿM)` form a cone on the tower
`n ↦ RΓ_Z(M/IⁿM)`: they are the image of the cone of quotient maps under a functor. -/
theorem localCohomologyAdicQuotientMap_succ_comp_map (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ) :
    localCohomologyAdicQuotientMap A I J hJ M (n + 1) ≫
        (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op =
      localCohomologyAdicQuotientMap A I J hJ M n := by
  let G := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
    Stacks.LocalCohomology.localCohomologyDerived A J hJ
  change G.map (adicQuotientProjection A I M (n + 1)) ≫
    G.map ((adicQuotientModuleSystem A I M).map (homOfLE (Nat.le_succ n)).op) = _
  rw [← G.map_comp, adicQuotientProjection_succ_comp_map A I M n]
  rfl

/-- The canonical maps `RΓ_Z(M) ⟶ RΓ_Z(M/IⁿM)` are compatible with every transition map of the
tower, not only with the successor ones. -/
theorem localCohomologyAdicQuotientMap_comp_map (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) {n m : ℕ} (h : n ≤ m) :
    localCohomologyAdicQuotientMap A I J hJ M m ≫
        (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE h).op =
      localCohomologyAdicQuotientMap A I J hJ M n := by
  let G := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
    Stacks.LocalCohomology.localCohomologyDerived A J hJ
  change G.map (adicQuotientProjection A I M m) ≫
    G.map ((adicQuotientModuleSystem A I M).map (homOfLE h).op) = _
  rw [← G.map_comp, adicQuotientProjection_comp_map A I M h]
  rfl

end Cone

section Complete

variable (A : Type u) [CommRing A]

/-- A power of `I` annihilates the adic quotient `M/IⁿM`. -/
theorem pow_le_annihilator_adicQuotient (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    (I ^ n : Ideal A) ≤ Module.annihilator A ((adicQuotientModuleSystem A I M).obj (op n)) := by
  intro a ha
  refine Module.mem_annihilator.2 fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    change a • (Submodule.Quotient.mk y : M ⧸ (I ^ n • (⊤ : Submodule A M))) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- **Every term of the tower is derived `I`-complete.** The `n`-th term is `RΓ_Z(M/IⁿM)`, and
`Iⁿ` annihilates `M/IⁿM`, so every cohomology module of that local cohomology is annihilated by
`Iⁿ` and therefore derived `I`-complete. -/
theorem isDerivedComplete_adicQuotientLocalCohomologySystem_obj (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ) :
    IsDerivedComplete I ((adicQuotientLocalCohomologySystem A I J hJ M).obj (op n)) :=
  Stacks.Algebraization.isDerivedComplete_localCohomology_of_pow_le_annihilator I J hJ n
    ((adicQuotientModuleSystem A I M).obj (op n)) (pow_le_annihilator_adicQuotient A I M n)

end Complete

section Projection

variable (A : Type u) [CommRing A]

/-- The derived `I`-adic completion unit `RΓ_Z(M) ⟶ RΓ_Z(M)^∧`, with its target spelled as
`Dualizing.completedLocalCohomology`. -/
def completedLocalCohomologyUnit (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A) :
    (Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶
      completedLocalCohomology A I J hI hJ M :=
  (Stacks.Algebraization.adicCompletionUnit A I hI).app
    ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))

/-- **The universal property of the completion unit, with the completion spelled as
`Dualizing.completedLocalCohomology`.** Composing with the unit is a bijection from maps out of
`RΓ_Z(M)^∧` to maps out of `RΓ_Z(M)`, for every derived `I`-complete target. -/
theorem completedLocalCohomologyUnit_comp_bijective (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (E : DerivedCategory (ModuleCat.{u} A)) (hE : IsDerivedComplete I E) :
    Function.Bijective (fun g : completedLocalCohomology A I J hI hJ M ⟶ E ↦
      completedLocalCohomologyUnit A I J hI hJ M ≫ g) :=
  Stacks.Algebraization.completionUnit_comp_bijective I hI
    ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) E hE

/-- **The canonical projection `RΓ_Z(M)^∧ ⟶ RΓ_Z(M/IⁿM)`.** The target is derived `I`-complete,
so the canonical map `RΓ_Z(M) ⟶ RΓ_Z(M/IⁿM)` factors uniquely through the completion unit; this
is that factorization. Nothing is chosen: `Dualizing.completedLocalCohomologyProjection_unique`
says it is the only map whose composite with the unit is the canonical map. -/
def completedLocalCohomologyProjection (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ) :
    completedLocalCohomology A I J hI hJ M ⟶
      (adicQuotientLocalCohomologySystem A I J hJ M).obj (op n) :=
  Classical.choose ((completedLocalCohomologyUnit_comp_bijective A I J hI hJ M
      ((adicQuotientLocalCohomologySystem A I J hJ M).obj (op n))
      (isDerivedComplete_adicQuotientLocalCohomologySystem_obj A I J hJ M n)).2
    (localCohomologyAdicQuotientMap A I J hJ M n))

/-- **The defining property of the canonical projection.** The completion unit followed by the
`n`-th canonical projection is the canonical map `RΓ_Z(M) ⟶ RΓ_Z(M/IⁿM)`. -/
theorem completedLocalCohomologyUnit_comp_projection (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ) :
    completedLocalCohomologyUnit A I J hI hJ M ≫
        completedLocalCohomologyProjection A I J hI hJ M n =
      localCohomologyAdicQuotientMap A I J hJ M n :=
  Classical.choose_spec ((completedLocalCohomologyUnit_comp_bijective A I J hI hJ M
      ((adicQuotientLocalCohomologySystem A I J hJ M).obj (op n))
      (isDerivedComplete_adicQuotientLocalCohomologySystem_obj A I J hJ M n)).2
    (localCohomologyAdicQuotientMap A I J hJ M n))

/-- **The canonical projection is the only map with its defining property.** Composition with
the completion unit is injective on maps into a derived `I`-complete object. -/
theorem completedLocalCohomologyProjection_unique (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ)
    (g : completedLocalCohomology A I J hI hJ M ⟶
      (adicQuotientLocalCohomologySystem A I J hJ M).obj (op n))
    (hg : completedLocalCohomologyUnit A I J hI hJ M ≫ g =
      localCohomologyAdicQuotientMap A I J hJ M n) :
    g = completedLocalCohomologyProjection A I J hI hJ M n :=
  (completedLocalCohomologyUnit_comp_bijective A I J hI hJ M
      ((adicQuotientLocalCohomologySystem A I J hJ M).obj (op n))
      (isDerivedComplete_adicQuotientLocalCohomologySystem_obj A I J hJ M n)).1
    (hg.trans (completedLocalCohomologyUnit_comp_projection A I J hI hJ M n).symm)

/-- **The canonical projections form a cone.** Both the `n`-th projection and the `(n+1)`-st
followed by the transition map compose with the completion unit to give the `n`-th canonical
map, and composition with the unit is injective on maps into a derived `I`-complete object. -/
theorem completedLocalCohomologyProjection_succ_comp_map (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ) :
    completedLocalCohomologyProjection A I J hI hJ M (n + 1) ≫
        (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op =
      completedLocalCohomologyProjection A I J hI hJ M n := by
  refine (completedLocalCohomologyProjection_unique A I J hI hJ M n _ ?_).symm.symm
  rw [← Category.assoc, completedLocalCohomologyUnit_comp_projection A I J hI hJ M (n + 1),
    localCohomologyAdicQuotientMap_succ_comp_map A I J hJ M n]

/-- The canonical projections are compatible with every transition map of the tower. -/
theorem completedLocalCohomologyProjection_comp_map (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) {n m : ℕ} (h : n ≤ m) :
    completedLocalCohomologyProjection A I J hI hJ M m ≫
        (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE h).op =
      completedLocalCohomologyProjection A I J hI hJ M n := by
  refine (completedLocalCohomologyProjection_unique A I J hI hJ M n _ ?_).symm.symm
  rw [← Category.assoc, completedLocalCohomologyUnit_comp_projection A I J hI hJ M m,
    localCohomologyAdicQuotientMap_comp_map A I J hJ M h]

/-- **A derived limit of the tower is derived `I`-complete.** The product of the terms is derived
complete, each term being so, and the presenting triangle carries completeness from its second
and third vertices to its first. -/
theorem isDerivedComplete_of_isDerivedLimitWithProjections (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (K : DerivedCategory (ModuleCat.{u} A))
    (π : ∀ n : ℕ, K ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj (op n))
    (hK : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientLocalCohomologySystem A I J hJ M) K π) :
    IsDerivedComplete I K := by
  obtain ⟨δ, hT⟩ := hK
  intro a ha
  refine isDerivedCompleteAt_of_distTriang hT ?_ ?_ <;>
    exact isDerivedCompleteAt_pi fun n ↦
      isDerivedComplete_adicQuotientLocalCohomologySystem_obj A I J hJ M n a ha

/-- **The tower has a derived-limit presentation with projections through which the canonical
maps factor.** Completing the Milnor difference map to a distinguished triangle gives a
presentation with projections, and the cone of canonical maps `RΓ_Z(M) ⟶ RΓ_Z(M/IⁿM)` factors
through those projections.

Combined with
`Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection`, this reduces the
pinned form of [Stacks, Tag 0EEW] part (1) to a single statement about the lift `v`: that it has
the universal property of the derived `I`-adic completion unit. -/
theorem exists_isDerivedLimitWithProjections_lift_localCohomologyAdicQuotientMap
    (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A) :
    ∃ (K' : DerivedCategory (ModuleCat.{u} A))
      (π' : ∀ n : ℕ, K' ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj (op n))
      (v : (Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶ K'),
      NoetherianAdicCompletion.IsDerivedLimitWithProjections
          (adicQuotientLocalCohomologySystem A I J hJ M) K' π' ∧
        ∀ n : ℕ, v ≫ π' n = localCohomologyAdicQuotientMap A I J hJ M n := by
  obtain ⟨K', π', hK'⟩ :=
    NoetherianAdicCompletion.exists_isDerivedLimitWithProjections_of_hasProduct
      (adicQuotientLocalCohomologySystem A I J hJ M)
  obtain ⟨v, hv⟩ := hK'.exists_lift (localCohomologyAdicQuotientMap A I J hJ M)
    (localCohomologyAdicQuotientMap_succ_comp_map A I J hJ M)
  exact ⟨K', π', v, hK', hv⟩

/-- **The canonical projections present `RΓ_Z(M)^∧` as a derived limit of the tower, as soon as
some presentation with projections has a derived-completion unit for its lift.**

Let `K'` be a derived limit of `n ↦ RΓ_Z(M/IⁿM)` with projections `π'`, and let
`v : RΓ_Z(M) ⟶ K'` be a map whose composites with the `π'` are the canonical maps. If `v` has
the universal property of the derived `I`-adic completion unit — composing with it is a bijection
onto maps from `RΓ_Z(M)` into every derived `I`-complete object — then `K'` is isomorphic to
`RΓ_Z(M)^∧` over `RΓ_Z(M)`, the isomorphism carries `π'` to the canonical projections, and the
canonical projections therefore present `RΓ_Z(M)^∧` as a derived limit of the tower.

This isolates what is missing for Tag 0EEW part (1) *with its unit*: the library's
`Dualizing.isDerivedLimit_completedLocalCohomology` gives the derived-limit property as a bare
existential, which pins no cone, so the arrow of Tag 0EFR cannot be compared with the canonical
projections. What has to be produced instead is a presentation whose lift is a completion
unit — exactly the data the Koszul and Čech models of derived completion carry, through
`AdicKoszul.KoszulPowerCompletion.unit_projection` and
`CechCompletion.cechCompletion_isReflection`. -/
theorem isDerivedLimitWithProjections_completedLocalCohomologyProjection
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A)
    (K' : DerivedCategory (ModuleCat.{u} A))
    (π' : ∀ n : ℕ, K' ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj (op n))
    (hK' : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientLocalCohomologySystem A I J hJ M) K' π')
    (v : (Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶ K')
    (hv : ∀ n : ℕ, v ≫ π' n = localCohomologyAdicQuotientMap A I J hJ M n)
    (hrefl : ∀ E : DerivedCategory (ModuleCat.{u} A), IsDerivedComplete I E →
      Function.Bijective (fun g : K' ⟶ E ↦ v ≫ g)) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientLocalCohomologySystem A I J hJ M) (completedLocalCohomology A I J hI hJ M)
      (completedLocalCohomologyProjection A I J hI hJ M) := by
  have hcompleteK' : IsDerivedComplete I K' :=
    isDerivedComplete_of_isDerivedLimitWithProjections A I J hJ M K' π' hK'
  have hcompleteKc : IsDerivedComplete I (completedLocalCohomology A I J hI hJ M) :=
    ((derivedCompletion A I hI).obj
      ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))).property
  obtain ⟨α, hα⟩ := (completedLocalCohomologyUnit_comp_bijective A I J hI hJ M K'
    hcompleteK').2 v
  obtain ⟨β, hβ⟩ := (hrefl _ hcompleteKc).2 (completedLocalCohomologyUnit A I J hI hJ M)
  have hα' : completedLocalCohomologyUnit A I J hI hJ M ≫ α = v := hα
  have hβ' : v ≫ β = completedLocalCohomologyUnit A I J hI hJ M := hβ
  have hαβ : α ≫ β = 𝟙 _ := by
    refine (completedLocalCohomologyUnit_comp_bijective A I J hI hJ M _ hcompleteKc).1
      (a₁ := α ≫ β) (a₂ := 𝟙 _) ?_
    change completedLocalCohomologyUnit A I J hI hJ M ≫ α ≫ β =
      completedLocalCohomologyUnit A I J hI hJ M ≫ 𝟙 _
    rw [← Category.assoc, hα', hβ', Category.comp_id]
  have hβα : β ≫ α = 𝟙 _ := by
    refine (hrefl _ hcompleteK').1 (a₁ := β ≫ α) (a₂ := 𝟙 _) ?_
    change v ≫ β ≫ α = v ≫ 𝟙 _
    rw [← Category.assoc, hβ', hα', Category.comp_id]
  let e : completedLocalCohomology A I J hI hJ M ≅ K' := ⟨α, β, hαβ, hβα⟩
  have hπ : (fun n : ℕ ↦ e.hom ≫ π' n) =
      completedLocalCohomologyProjection A I J hI hJ M := by
    funext n
    refine completedLocalCohomologyProjection_unique A I J hI hJ M n _ ?_
    change completedLocalCohomologyUnit A I J hI hJ M ≫ α ≫ π' n = _
    rw [← Category.assoc, hα', hv n]
  have := hK'.of_iso e
  rwa [hπ] at this

end Projection

end Dualizing

end
