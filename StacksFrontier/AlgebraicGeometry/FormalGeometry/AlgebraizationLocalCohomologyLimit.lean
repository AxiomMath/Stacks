module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparisonLocal
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CechCompletionUnit
public import StacksFrontier.RingTheory.LocalCohomology.MittagLefflerAdicQuotientShrink

/-!
# `Hⁱ_J(M)` is the limit of the `Hⁱ_J(M/IⁿM)` under the hypotheses of Stacks 0DXP

Let `(A, 𝔪)` be a Noetherian local ring, `I` an ideal, `M` a finite `A`-module and `J` an ideal
with `V(J) ∩ V(I) = {𝔪}`. This file proves that the canonical map

`Hⁱ_J(M) ⟶ lim_n Hⁱ_J(M/IⁿM)`

is an isomorphism as soon as the derived `I`-adic completion unit `RΓ_J(M) ⟶ RΓ_J(M)^∧` is an
isomorphism on degree-`i` cohomology — which for `i ≤ s` and `J ⊆ J₀` is the conclusion of
Stacks 0DXP, recorded as `Stacks.Algebraization.IsLocalAlgebraizationIdeal`.

Two inputs combine. The canonical projections `RΓ_J(M)^∧ ⟶ RΓ_J(M/IⁿM)` present `RΓ_J(M)^∧` as a
derived limit of the tower `n ↦ RΓ_J(M/IⁿM)`, which is part (1) of Stacks 0EEW pinned to those
projections, available for a finite module over a Noetherian ring as
`Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite`. Tag 0DXJ
in the pinned form of
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.isIso_of_comp_limit_π` then inverts the
comparison `Hⁱ(RΓ_J(M)^∧) ⟶ lim_n Hⁱ_J(M/IⁿM)`, provided the tower one degree below is
Mittag-Leffler; that is
`Stacks.LocalCohomology.isMittagLefflerCategorical_adicQuotientLocalCohomologySystem`, which is
where the hypothesis `V(J) ∩ V(I) = {𝔪}` is used. Since the composite of the completion unit with
that comparison is the canonical map, by
`Dualizing.completedLocalCohomologyUnit_comp_projection`, the canonical map is invertible.

## Main definitions

* `Stacks.Algebraization.localCohomologyAdicQuotientCone` — the cone on `n ↦ Hⁱ_J(M/IⁿM)` with
  vertex `Hⁱ_J(M)` formed by the canonical maps.
* `Stacks.Algebraization.completedLocalCohomologyProjectionCone` — the same with vertex
  `Hⁱ(RΓ_J(M)^∧)`, formed by the canonical projections.

## Main results

* `Stacks.Algebraization.isIso_completedLocalCohomologyProjectionToLimit` — Tag 0DXJ for
  the canonical projections.
* `Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit` — the canonical map
  `Hⁱ_J(M) ⟶ lim_n Hⁱ_J(M/IⁿM)` is an isomorphism.
* `Stacks.Algebraization.isIso_homology_completedLocalCohomologyUnit_of_isLocalAlgebraizationIdeal`
  — Stacks 0DXP read at the completion unit at `J` itself.
* `Stacks.Algebraization.surjective_localCohomologyAdicQuotientToLimit` — the surjectivity
  that the comparison clause of Stacks 0DXQ consumes.

## References

* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe v₁ u₁ u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A]

/-! ### Cones on a tower indexed by `ℕᵒᵖ` -/

/-- A compatible family of maps into the terms of a tower indexed by `ℕᵒᵖ` is a cone. The
compatibility is asked for the transitions `Fₘ ⟶ Fₙ` of an inequality `n ≤ m`, which is every
morphism of `ℕᵒᵖ` because `ℕ` is a poset. -/
public def natCone {C : Type u₁} [Category.{v₁} C] (F : ℕᵒᵖ ⥤ C) (X : C)
    (c : ∀ n : ℕ, X ⟶ F.obj (op n))
    (hc : ∀ {n m : ℕ} (h : n ≤ m), c m ≫ F.map (homOfLE h).op = c n) :
    Cone F where
  pt := X
  π :=
  { app := fun n => c n.unop
    naturality := fun m n f => by
      have hf : F.map f = F.map (homOfLE (leOfHom f.unop)).op :=
        congrArg F.map (Subsingleton.elim _ _)
      rw [hf, hc (leOfHom f.unop), Functor.const_obj_map]
      exact Category.id_comp _ }

/-- The leg of `natCone F X c hc` at `n` is `c n`. -/
@[simp]
public theorem natCone_π_app {C : Type u₁} [Category.{v₁} C] (F : ℕᵒᵖ ⥤ C) (X : C)
    (c : ∀ n : ℕ, X ⟶ F.obj (op n))
    (hc : ∀ {n m : ℕ} (h : n ≤ m), c m ≫ F.map (homOfLE h).op = c n) (n : ℕ) :
    (natCone F X c hc).π.app (op n) = c n :=
  rfl

/-! ### The two cones on the tower of local cohomology modules -/

/-- The cone on `n ↦ Hⁱ_J(M/IⁿM)` with vertex `Hⁱ_J(M)` whose legs are the canonical maps
`Hⁱ_J(M) ⟶ Hⁱ_J(M/IⁿM)`. Its limit comparison is the map of Stacks 0DXJ. -/
public def localCohomologyAdicQuotientCone (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A)
    (r : ℤ) :
    Cone (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) :=
  natCone _ _
    (fun n => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
      (Dualizing.localCohomologyAdicQuotientMap A I J hJ M n))
    (fun {n m} h => by
      rw [Functor.comp_map,
        ← (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map_comp,
        Dualizing.localCohomologyAdicQuotientMap_comp_map A I J hJ M h])

/-- The cone on `n ↦ Hⁱ_J(M/IⁿM)` with vertex `Hⁱ(RΓ_J(M)^∧)` whose legs are the canonical
projections of `Dualizing.completedLocalCohomologyProjection`. -/
public def completedLocalCohomologyProjectionCone (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (r : ℤ) :
    Cone (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) :=
  natCone _ _
    (fun n => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
      (Dualizing.completedLocalCohomologyProjection A I J hI hJ M n))
    (fun {n m} h => by
      rw [Functor.comp_map,
        ← (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map_comp,
        Dualizing.completedLocalCohomologyProjection_comp_map A I J hI hJ M h])

/-- **The canonical map `Hʳ_J(M) ⟶ lim_n Hʳ_J(M/IⁿM)`**: the limit comparison of the cone of
canonical maps. This is the arrow of Tag 0DXJ at the source of the completion unit. -/
public def localCohomologyAdicQuotientToLimit (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj
        ((localCohomologyDerived A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ⟶
      limit (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) :=
  limit.lift _ (localCohomologyAdicQuotientCone A I J hJ M r)

/-- The canonical map `Hʳ_J(M) ⟶ lim_n Hʳ_J(M/IⁿM)` followed by the `n`-th limit projection is the
canonical map `Hʳ_J(M) ⟶ Hʳ_J(M/IⁿM)`. -/
@[reassoc]
public theorem localCohomologyAdicQuotientToLimit_π (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (r : ℤ) (n : ℕ) :
    localCohomologyAdicQuotientToLimit A I J hJ M r ≫
        limit.π (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) (op n) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
        (Dualizing.localCohomologyAdicQuotientMap A I J hJ M n) :=
  limit.lift_π _ _

/-- **The comparison `Hʳ(RΓ_J(M)^∧) ⟶ lim_n Hʳ_J(M/IⁿM)` of Tag 0DXJ**, built from the canonical
projections. -/
public def completedLocalCohomologyProjectionToLimit (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj
        (Dualizing.completedLocalCohomology A I J hI hJ M) ⟶
      limit (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) :=
  limit.lift _ (completedLocalCohomologyProjectionCone A I J hI hJ M r)

/-- The comparison `Hʳ(RΓ_J(M)^∧) ⟶ lim_n Hʳ_J(M/IⁿM)` followed by the `n`-th limit projection is
the map on `Hʳ` of the canonical projection `RΓ_J(M)^∧ ⟶ RΓ_J(M/IⁿM)`. -/
@[reassoc]
public theorem completedLocalCohomologyProjectionToLimit_π (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (r : ℤ) (n : ℕ) :
    completedLocalCohomologyProjectionToLimit A I J hI hJ M r ≫
        limit.π (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) (op n) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
        (Dualizing.completedLocalCohomologyProjection A I J hI hJ M n) :=
  limit.lift_π _ _

/-! ### Tag 0DXJ for the canonical projections -/

variable [IsLocalRing A] [IsNoetherianRing A]

/-- **Tag 0DXJ at the canonical projections.** For a finite module `M` and an ideal `J` with
`V(J) ∩ V(I) = {𝔪}`, the comparison `Hʳ(RΓ_J(M)^∧) ⟶ lim_n Hʳ_J(M/IⁿM)` built from the canonical
projections is an isomorphism.

The canonical projections present `RΓ_J(M)^∧` as a derived limit of the tower, which is part (1)
of Stacks 0EEW pinned to them, and the tower `n ↦ H^{r-1}_J(M/IⁿM)` one degree below is
Mittag-Leffler. -/
public theorem isIso_completedLocalCohomologyProjectionToLimit (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (r : ℤ) :
    IsIso (completedLocalCohomologyProjectionToLimit A I J
      I.fg_of_isNoetherianRing J.fg_of_isNoetherianRing M r) :=
  NoetherianAdicCompletion.IsDerivedLimitWithProjections.isIso_of_comp_limit_π A
    (Dualizing.adicQuotientLocalCohomologySystem A I J J.fg_of_isNoetherianRing M)
    (Dualizing.completedLocalCohomology A I J I.fg_of_isNoetherianRing
      J.fg_of_isNoetherianRing M)
    (Dualizing.completedLocalCohomologyProjection A I J I.fg_of_isNoetherianRing
      J.fg_of_isNoetherianRing M)
    (Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite A I J
      I.fg_of_isNoetherianRing J.fg_of_isNoetherianRing M)
    r
    (isMittagLefflerCategorical_adicQuotientLocalCohomologySystem A I J M hV (r - 1))
    _ (completedLocalCohomologyProjectionToLimit_π A I J _ _ M r)

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- The canonical map `Hʳ_J(M) ⟶ lim_n Hʳ_J(M/IⁿM)` is the completion unit followed by the
comparison of Tag 0DXJ: the completion unit composed with the `n`-th canonical projection is the
`n`-th canonical map. -/
public theorem localCohomologyAdicQuotientToLimit_eq (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (r : ℤ) :
    localCohomologyAdicQuotientToLimit A I J hJ M r =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
          (Dualizing.completedLocalCohomologyUnit A I J hI hJ M) ≫
        completedLocalCohomologyProjectionToLimit A I J hI hJ M r := by
  refine limit.hom_ext fun j => ?_
  obtain ⟨n⟩ := j
  rw [localCohomologyAdicQuotientToLimit_π, Category.assoc,
    completedLocalCohomologyProjectionToLimit_π,
    ← (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map_comp]
  exact congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
    (Dualizing.completedLocalCohomologyUnit_comp_projection A I J hI hJ M n).symm

/-- **The canonical map `Hʳ_J(M) ⟶ lim_n Hʳ_J(M/IⁿM)` is an isomorphism**, provided the derived
`I`-adic completion unit `RΓ_J(M) ⟶ RΓ_J(M)^∧` is an isomorphism on degree-`r` cohomology. -/
public theorem isIso_localCohomologyAdicQuotientToLimit (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (r : ℤ)
    (hunit : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
      (Dualizing.completedLocalCohomologyUnit A I J I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing M))) :
    IsIso (localCohomologyAdicQuotientToLimit A I J J.fg_of_isNoetherianRing M r) := by
  have hq := isIso_completedLocalCohomologyProjectionToLimit A I J M hV r
  rw [localCohomologyAdicQuotientToLimit_eq A I J I.fg_of_isNoetherianRing
    J.fg_of_isNoetherianRing M r]
  have := hunit
  have := hq
  infer_instance

/-! ### Stacks 0DXP read at the completion unit -/

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- The arrow of Stacks 0DXP is the derived `I`-adic completion unit at `RΓ_{J'}(M)` followed by
the identification of the completions at `J'` and at `J`. This is the same `rfl` as
`Stacks.Algebraization.localCohomologyToCompletedLocalCohomology_eq_unit_comp`, for two
possibly different ideals. -/
public theorem localCohomologyToCompletedLocalCohomology_eq_unit_comp'
    (I J J' : Ideal A) (hI : I.FG) (hJ : J.FG) (hJ' : J'.FG) (M : ModuleCat.{u} A)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    localCohomologyToCompletedLocalCohomology A I J J' hI hJ hJ' M hV =
      Dualizing.completedLocalCohomologyUnit A I J' hI hJ' M ≫
        (completedLocalCohomologyShrinkIso A I J J' hI hJ hJ' M hV).hom :=
  rfl

variable {A}

/-- **Stacks 0DXP, read at the completion unit at `J` itself.** The conclusion of Stacks 0DXP is
that `RΓ_J(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism on cohomology in degrees `i ≤ s`. That arrow is the
completion unit `RΓ_J(M) ⟶ RΓ_J(M)^∧` followed by the identification
`RΓ_J(M)^∧ ≅ RΓ_𝔪(M)^∧`, so the unit itself is invertible on cohomology in those degrees. -/
public theorem isIso_homology_completedLocalCohomologyUnit_of_isLocalAlgebraizationIdeal
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} {hI : I ≠ ⊤} {s : ℤ} {J₀ : Ideal A}
    (H : IsLocalAlgebraizationIdeal (M := M) I hI s J₀)
    (J : Ideal A) (hJ : J ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (Dualizing.completedLocalCohomologyUnit A I J I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing (ModuleCat.of A M))) := by
  have h := H.isIso J hJ hV i hi
  set e := completedLocalCohomologyShrinkIso A I (maximalIdeal A) J I.fg_of_isNoetherianRing
    (Ideal.fg_of_isNoetherianRing _) J.fg_of_isNoetherianRing (ModuleCat.of A M)
    (zeroLocus_inter_eq_maximalIdeal_inter hI hV)
  rw [localCohomologyToCompletedLocalCohomology_eq_unit_comp' A I (maximalIdeal A) J
      I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) J.fg_of_isNoetherianRing
      (ModuleCat.of A M) (zeroLocus_inter_eq_maximalIdeal_inter hI hV),
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map_comp] at h
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map e.hom)

/-- **The surjectivity of the canonical map `Hʳ_J(M) ⟶ lim_n Hʳ_J(M/IⁿM)`**, under the hypotheses
of Stacks 0DXP. This is the input that the comparison clause of Stacks 0DXQ at `i = 0` consumes
on the right-hand end of the four-term sequence. -/
public theorem surjective_localCohomologyAdicQuotientToLimit
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} {hI : I ≠ ⊤} {s : ℤ} {J₀ : Ideal A}
    (H : IsLocalAlgebraizationIdeal (M := M) I hI s J₀)
    (J : Ideal A) (hJ : J ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (r : ℤ) (hr : r ≤ s) :
    Function.Surjective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J J.fg_of_isNoetherianRing
        (ModuleCat.of A M) r)) := by
  have := isIso_localCohomologyAdicQuotientToLimit A I J (ModuleCat.of A M) hV r
    (isIso_homology_completedLocalCohomologyUnit_of_isLocalAlgebraizationIdeal H J hJ hV r hr)
  exact (ConcreteCategory.bijective_of_isIso _).2

end Stacks.Algebraization

end
