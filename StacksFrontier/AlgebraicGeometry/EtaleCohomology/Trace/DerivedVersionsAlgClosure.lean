module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDerivedHomologyIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PerfectClosureCurveModel

/-!
# The derived versions of Tag 03VM over an arbitrary field

Let `k` be any field, `k̄` an algebraic closure of `k`, `X` a geometrically connected smooth curve
over `k` with `X_{k̄} ≇ ℙ¹_{k̄}`, and `Λ` a finite ring with `#Λ ∈ k^*`. [Stacks, Tag 03VM] asserts
two "derived versions" in which the Galois group `Gal(k^{sep}/k) = Aut(k̄/k)` acts:

* `RΓ_c(X_{k̄}, ℱ_ρ) = LH₀(π₁(X_{k̄}, η̄), M(-1))` in `D(Λ[[Aut(k̄/k)]])` (the shift `[-2]` is
  implicit in the source, see `errata.md`), and
* `RΓ(X_{k̄}, ℱ_ρ) = RH⁰(π₁(X_{k̄}, η̄), M)` in the derived category of discrete `Λ`-modules with a
  continuous action of `Aut(k̄/k)`.

The main declarations of `CompactSupportDerivedHomologyIso` and `GeometricDerivedGaloisInvariants`
prove them when `k̄` is separable over `k` (e.g. `k` perfect, in particular finite). This file
removes that hypothesis by passing to the relative perfect closure `k'` of `k` in `k̄`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/PerfectClosureCurveModel.lean`):

* `X' = X ×_k k'` is a geometrically connected smooth curve over the perfect field `k'`, over
  which `k̄` is separable;
* nothing the statements see changes: `X'_{k̄} = X_{k̄}` (so the étale cohomology of `X_{k̄}` and
  the geometric fundamental group are those of `X'_{k̄}`), `Aut(k̄/k') = Aut(k̄/k)` as topological
  groups (`perfectClosureAlgEquivContinuousMulEquiv`), and the action of `σ` on `X_{k̄}` through
  `id_X × Spec σ` is the action on `X'_{k̄}` through `id_{X'} × Spec σ`;
* a representation `ρ` of `π₁(X, η̄)` is read on `X'` by restriction along
  `π₁(X', η̄') ⟶ π₁(X, η̄)` (`AlgebraicGeometry.perfectClosureModelRes`), and the sheaf it gives
  on `X'` is the inverse image of `ℱ_ρ` (Tag 0DV6,
  `AlgebraicGeometry.representationSheafPullbackIso`).

Forgetting the Galois action, the étale sides are the objects defined directly from `X` over `k`
and `ℱ_ρ`: `RΓ_c(X_{k̄}, ℱ_ρ)` and `RΓ(X_{k̄}, ℱ_ρ|_{X_{k̄}})`
(`AlgebraicGeometry.perfectClosureCompactSupportForgetIso`,
`AlgebraicGeometry.perfectClosureGaloisDerivedSectionsForgetIso` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/DerivedVersionsAlgClosureComparison.lean`).

On the group side, `π₁(X') ≅ π₁(X)` and `Aut(k̄/k') = Aut(k̄/k)` carry the projection
`π₁(X') ⟶ Aut(k̄/k')` of `X'` to the projection `π₁(X) ⟶ Aut(k̄/k)` of `X`
(`AlgebraicGeometry.perfectClosureAlgEquiv_geometricGaloisProjection`), and the sixth assertion is
stated with `RH⁰` defined from `X` over `k`
(`AlgebraicGeometry.geometricGaloisDerivedKernelInvariantsIsoOfAlgClosure`, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/DerivedVersionsAlgClosureGroup.lean`).

So the Galois-equivariant objects of the two derived versions over `k` are the ones over `k'`,
transported along `Aut(k̄/k) ≅ Aut(k̄/k')`: by restriction of scalars along
`Λ[[Aut(k̄/k)]] ≅ Λ[[Aut(k̄/k')]]` for the first, and by restriction of the continuous action for
the second.

## Main definitions

* `AlgebraicGeometry.perfectClosureCompactSupportDerived`: `M ↦ RΓ_c(X_{k̄}, ℱ_ρ)` in
  `D(Λ[[Aut(k̄/k)]])`.
* `AlgebraicGeometry.perfectClosureDerivedHomologyTwist`: `M ↦ LH₀(π₁(X_{k̄}, η̄), M(-1))` in
  `D(Λ[[Aut(k̄/k)]])`.
* `AlgebraicGeometry.perfectClosureGaloisDerivedInvariants`: `M ↦ RH⁰(π₁(X_{k̄}, η̄), M)` in
  `D⁺` of discrete `Λ`-modules with continuous `Aut(k̄/k)`-action.
* `AlgebraicGeometry.perfectClosureGaloisDerivedSections`: `M ↦ RΓ^{Gal}(X_{k̄}, ℱ_ρ)` there.

## Main results

* `AlgebraicGeometry.compactSupportDerivedHomologyIsoOfAlgClosure`: the third assertion of 03VM,
  for every field `k`.
* `AlgebraicGeometry.geometricGaloisDerivedInvariantsIsoOfAlgClosure`: the sixth assertion of
  03VM with its Galois action, for every field `k`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.GroupCohomology Stacks.ContinuousCohomology Stacks.GroupHomology Stacks.Frobenius
open Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

section TransportGeneric

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] (e : H ≃ₜ* G) (Λ : Type) [Ring Λ]

/-- **`D(Λ[[G]]) ⥤ D(Λ[[H]])`** for an isomorphism `e : H ≃ G` of topological groups: restriction
of scalars along `Λ[[H]] ≅ Λ[[G]]`, an exact functor. -/
abbrev completedGroupAlgebraDerivedTransport :
    DerivedCategory (ModuleCat.{u + 1} (CompletedGroupAlgebra Λ G)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (CompletedGroupAlgebra Λ H)) :=
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
    (CompletedGroupAlgebra.mapRingEquiv (Λ := Λ) e).toRingHom
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
    (CompletedGroupAlgebra.mapRingEquiv (Λ := Λ) e).toRingHom
  (ModuleCat.restrictScalars.{u + 1}
    (CompletedGroupAlgebra.mapRingEquiv (Λ := Λ) e).toRingHom).mapDerivedCategory

/-- **`D⁺(Λ[G]-discrete) ⥤ D⁺(Λ[H]-discrete)`** for an isomorphism `e : H ≃ G` of topological
groups: restriction of the continuous action along `e`, an exact functor. -/
abbrev continuousModuleDerivedTransport :
    DerivedCategory.Plus (Stacks.Injectives.ContinuousModule.{0, u, u + 1} Λ G) ⥤
      DerivedCategory.Plus (Stacks.Injectives.ContinuousModule.{0, u, u + 1} Λ H) :=
  haveI := additive_continuousModuleRes.{0, u, u + 1} Λ
    (ContinuousMonoidHom.toContinuousMonoidHom e)
  haveI := preservesFiniteLimits_continuousModuleRes.{0, u, u + 1} Λ
    (ContinuousMonoidHom.toContinuousMonoidHom e)
  haveI := preservesFiniteColimits_continuousModuleRes.{0, u, u + 1} Λ
    (ContinuousMonoidHom.toContinuousMonoidHom e)
  (continuousModuleRes.{0, u, u + 1} Λ
    (ContinuousMonoidHom.toContinuousMonoidHom e)).mapDerivedCategoryPlus

end TransportGeneric

section Transport

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
  (Λ : Type) [Ring Λ]

/-- **`D(Λ[[Aut(k̄/k')]]) ⥤ D(Λ[[Aut(k̄/k)]])`**, `k'` the relative perfect closure of `k` in `k̄`:
restriction of scalars along `Λ[[Aut(k̄/k)]] ≅ Λ[[Aut(k̄/k')]]`. -/
abbrev perfectClosureDerivedTransport :
    DerivedCategory (ModuleCat.{u + 1} (CompletedGroupAlgebra Λ (K ≃ₐ[perfectClosure k K] K))) ⥤
      DerivedCategory (ModuleCat.{u + 1} (CompletedGroupAlgebra Λ (K ≃ₐ[k] K))) :=
  completedGroupAlgebraDerivedTransport (perfectClosureAlgEquivContinuousMulEquiv k K).symm Λ

/-- `Aut(k̄/k) ⟶ Aut(k̄/k')`, as a continuous homomorphism. -/
abbrev perfectClosureAutHom : (K ≃ₐ[k] K) →ₜ* (K ≃ₐ[perfectClosure k K] K) :=
  ContinuousMonoidHom.toContinuousMonoidHom (perfectClosureAlgEquivContinuousMulEquiv k K).symm

/-- **`D⁺(Λ[Aut(k̄/k')]-discrete) ⥤ D⁺(Λ[Aut(k̄/k)]-discrete)`**: restriction of the continuous
action along `Aut(k̄/k) ≅ Aut(k̄/k')`. -/
abbrev perfectClosureGaloisModulesTransport :
    DerivedCategory.Plus (GaloisModules Λ (perfectClosure k K) K) ⥤
      DerivedCategory.Plus (GaloisModules Λ k K) :=
  continuousModuleDerivedTransport (perfectClosureAlgEquivContinuousMulEquiv k K).symm Λ

end Transport

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) (Λ : Type) [Ring Λ]
  [Finite Λ]

section CompactSupport

variable (j : CompactificationOf (Over.mk f))

/-- **`M ↦ RΓ_c(X_{k̄}, ℱ_ρ)` in `D(Λ[[Aut(k̄/k)]])`, for any field `k`**: the Galois-equivariant
compactly supported cohomology `RΓ^{Gal}_c(X'_{k̄}, ℱ_{ρ|π₁(X')})` of Remark 03UI (2), computed on
`X'_{k̄} = X_{k̄}` with the compactification `X̄ ×_k k'` of `X' = X ×_k k'`
(`AlgebraicGeometry.geometricGaloisCompactSupportDerived`), read as a complex of
`Λ[[Aut(k̄/k)]]`-modules along `Aut(k̄/k) ≅ Aut(k̄/k')`. Here `k'` is the perfect closure of `k`
in `k̄`, the representation is restricted along `π₁(X') ≅ π₁(X)`, and the sheaf it gives on `X'` is
the inverse image of `ℱ_ρ` (Tag 0DV6). -/
def perfectClosureCompactSupportDerived :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (CompletedGroupAlgebra Λ (K ≃ₐ[k] K))) :=
  perfectClosureModelRes B X f K y Λ ⋙
    geometricGaloisCompactSupportDerived B (perfectClosureModel B X f K)
      (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y) Λ
      (compactificationFieldBaseChange f j (perfectClosure k K)) ⋙
    perfectClosureDerivedTransport K Λ

end CompactSupport

/-- **`M ↦ LH₀(π₁(X_{k̄}, η̄), M(-1))` in `D(Λ[[Aut(k̄/k)]])`, for any field `k`**: the derived
coinvariants of the geometric fundamental group `π₁(X'_{k̄}, η̄') = π₁(X_{k̄}, η̄)` with their
residual action of `Aut(k̄/k') = Aut(k̄/k)` (`AlgebraicGeometry.geometricDerivedHomology`), of the
Tate twist `M(-1) = Hom(μ_n(k̄), M)` (`AlgebraicGeometry.geometricTateTwist`, `n = #Λ`), read as a
complex of `Λ[[Aut(k̄/k)]]`-modules. The representation is restricted along `π₁(X') ≅ π₁(X)`. -/
def perfectClosureDerivedHomologyTwist :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (CompletedGroupAlgebra Λ (K ≃ₐ[k] K))) :=
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  perfectClosureModelRes B X f K y Λ ⋙
    (geometricTateTwist B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
        (perfectClosureModelPoint B X f K y) Λ ⋙
      geometricDerivedHomology B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
        (perfectClosureModelPoint B X f K y) Λ) ⋙
    perfectClosureDerivedTransport K Λ

/-- **Tag 03VM, homological derived clause, over any field:
`RΓ_c(X_k̄, ℱ_ρ) ≅ LH₀(π₁(X_k̄, η̄), M(-1))[-2]`** in the derived category of
`Λ[[Aut(k̄/k)]]`-modules (`Aut(k̄/k) = Gal(k^{sep}/k)`, which is `Ẑ` for `k` finite), naturally in
the finite `Λ`-module `M` with continuous action `ρ` of `π₁(X, η̄)`. Here `k` is any field, `k̄` an
algebraic closure of `k`, `X` a geometrically connected smooth curve over `k` with
`X_k̄ ≇ 𝐏¹_k̄`, and `Λ` a finite ring with `#Λ` invertible in `k`. The shift `[-2]` is implicit in
the source (see `errata.md`). The two sides are read on `X' = X ×_k k'`, `k'` the perfect closure
of `k` in `k̄`, whose geometric fibre, fundamental groups and Galois group are those of `X`; see
the module docstring. -/
@[stacks 03VM "third assertion (the derived version of the homological half): \
`RΓ_c(X_k̄, ℱ_ρ) ≅ LH₀(π₁(X_k̄, η̄), M(-1))[-2]` in the derived category of \
`Λ[[Aut(k̄/k)]]`-modules, natural in `(M, ρ)`, for an arbitrary base field `k`"]
def compactSupportDerivedHomologyIsoOfAlgClosure (j : CompactificationOf (Over.mk f))
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K)) :
    perfectClosureCompactSupportDerived B X f K y Λ j ≅
      perfectClosureDerivedHomologyTwist B X f K y Λ ⋙ shiftFunctor _ (-2 : ℤ) :=
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  Functor.isoWhiskerLeft (perfectClosureModelRes B X f K y Λ)
      (Functor.isoWhiskerRight
        (compactSupportDerivedHomologyIso B (perfectClosureModel B X f K)
          (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y) Λ
          (compactificationFieldBaseChange f j (perfectClosure k K))
          (isUnit_natCard_perfectClosure K Λ hΛ)
          (not_exists_iso_projectiveLine_perfectClosureModel B X f K hP))
        (perfectClosureDerivedTransport K Λ)) ≪≫
    Functor.isoWhiskerLeft
      (perfectClosureModelRes B X f K y Λ ⋙
        (geometricTateTwist B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
            (perfectClosureModelPoint B X f K y) Λ ⋙
          geometricDerivedHomology B (perfectClosureModel B X f K)
            (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y) Λ))
      ((perfectClosureDerivedTransport K Λ).commShiftIso (-2 : ℤ))

section GaloisInvariants

/-- **`M ↦ RH⁰(π₁(X_{k̄}, η̄), M)`, for any field `k`**, in the bounded below derived category of
discrete `Λ`-modules with a continuous action of `Aut(k̄/k)`: the right derived functor of the
invariants under the image of `π₁(X'_{k̄}, η̄') = π₁(X_{k̄}, η̄)`, with their residual action of
`π₁(X')/π₁(X'_{k̄}) = Aut(k̄/k') = Aut(k̄/k)` (`Stacks.GroupCohomology.derivedKernelInvariants`).
The representation is restricted along `π₁(X') ≅ π₁(X)`. -/
def perfectClosureGaloisDerivedInvariants :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) ⥤
      DerivedCategory.Plus (GaloisModules Λ k K) :=
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  perfectClosureModelRes B X f K y Λ ⋙
    ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (perfectClosureModel B X f K).1
          ((perfectClosureModelPoint B X f K y).map (fieldBaseChangeObjProj B
            (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
            (contains_fieldBaseChange_of_isCurve B _ _ K)).hom))) ⋙
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
      derivedKernelInvariants.{0, u + 1, u, 0} Λ
        (geometricGaloisProjection B (perfectClosureModel B X f K)
          (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y))
        (surjective_geometricGaloisProjection B (perfectClosureModel B X f K)
          (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y))) ⋙
    perfectClosureGaloisModulesTransport K Λ

/-- **`M ↦ RΓ^{Gal}(X_{k̄}, ℱ_ρ)`, for any field `k`**, in the bounded below derived category of
discrete `Λ`-modules with a continuous action of `Aut(k̄/k)`: the derived global sections on
`X'_{k̄} = X_{k̄}` with their Galois action (`Stacks.EtaleCohomology.galoisDerivedGlobalSections`)
of the sheaf attached to the restriction of `ρ` to `π₁(X')`, which is the inverse image of `ℱ_ρ`
to `X'` (Tag 0DV6), transported along `Aut(k̄/k) ≅ Aut(k̄/k')`. -/
def perfectClosureGaloisDerivedSections :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) ⥤
      DerivedCategory.Plus (GaloisModules Λ k K) :=
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  perfectClosureModelRes B X f K y Λ ⋙
    (representationSheaf.{u, 0} B (perfectClosureModel B X f K)
        ((perfectClosureModelPoint B X f K y).map (fieldBaseChangeObjProj B
          (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
          (contains_fieldBaseChange_of_isCurve B _ _ K)).hom) Λ ⋙
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
      Stacks.EtaleCohomology.galoisDerivedGlobalSections Λ
        (Over.mk (perfectClosureModelHom B X f K)) K) ⋙
    perfectClosureGaloisModulesTransport K Λ

/-- **The derived version of `H^i(X_{k̄}, ℱ_ρ) = H^i(π₁(X_{k̄}), M)` with its Galois action, over
any field** ([Stacks, Tag 03VM], "Moreover, in this case there is a derived version too"): for a
geometrically connected smooth curve `X` over a field `k`, `k̄` an algebraic closure of `k`, `Λ` a
finite ring with `#Λ` invertible in `k`, and `X_{k̄} ≇ 𝐏¹_{k̄}`, there is an isomorphism

`RH⁰(π₁(X_{k̄}), M) ≅ RΓ^{Gal}(X_{k̄}, ℱ_ρ)`

in the bounded below derived category of discrete `Λ`-modules with a continuous action of
`Aut(k̄/k) = Gal(k^{sep}/k)`, natural in the finite `Λ`-module `M` with continuous action `ρ` of
`π₁(X)`. The two sides are read on `X' = X ×_k k'`, `k'` the perfect closure of `k` in `k̄`; see
the module docstring. -/
def geometricGaloisDerivedInvariantsIsoOfAlgClosure (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K)) :
    perfectClosureGaloisDerivedInvariants B X f K y Λ ≅
      perfectClosureGaloisDerivedSections B X f K y Λ :=
  Functor.isoWhiskerLeft (perfectClosureModelRes B X f K y Λ)
    (Functor.isoWhiskerRight
      (geometricGaloisDerivedInvariantsIso B (perfectClosureModel B X f K)
        (perfectClosureModelHom B X f K) K Λ (perfectClosureModelPoint B X f K y)
        (isUnit_natCard_perfectClosure K Λ hΛ)
        (not_exists_iso_projectiveLine_perfectClosureModel B X f K hP))
      (perfectClosureGaloisModulesTransport K Λ))

end GaloisInvariants

end AlgebraicGeometry

end
