module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeInjectiveAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers

/-!
# The Galois-equivariant cohomology `RΓ(X_k̄, -)` and `RΓ_c(X_k̄, -)`

Let `k` be a field, `k̄` a separable algebraic extension (for the Trace Formula chapter: an
algebraic closure of the finite field `k`), `Q = Aut_k(k̄)` with its Krull topology, and `Λ` a
ring. For a quasi-compact and quasi-separated `k`-scheme `Y`, `F ↦ Γ(Y_k̄, F|_{Y_k̄})` with its
Galois action is a left exact functor `Γ^Gal` from sheaves of `Λ`-modules on `Y_étale` to the
category `GaloisModules Λ k k̄` of discrete `Λ[Q]`-modules
(`Stacks.EtaleCohomology.galoisGlobalSections`). This file takes its right derived functor on
bounded below derived categories, and the compactly supported version through a
compactification as in Remark 03UI (2).

## Main definitions

* `Stacks.EtaleCohomology.galoisDerivedGlobalSections` — `RΓ^Gal(Y_k̄, -) : D⁺(Y_étale, Λ) ⥤
  D⁺(GaloisModules Λ k k̄)`, the right derived functor of `Γ^Gal`.
* `Stacks.EtaleCohomology.galoisDerivedCompactSupport` — `RΓ^Gal_c(X_k̄, K) = RΓ^Gal(X̄_k̄, j_! K)`
  for a compactification `j : X ⟶ X̄` over `k`.

## Implementation notes

*The category.* The Trace Formula chapter (Tag 03VM, and Remark 03UI for the action of
`Gal(k̄/k)`) states its derived comparisons "in `D(Λ[[Ẑ]])`", `k` being finite and
`Ẑ ≅ Gal(k̄/k)`. The complexes it places there are `RΓ(X_k̄, -)` and `RΓ_c(X_k̄, -)` of
complexes of sheaves on `X`, whose cohomology modules `H^i(X_k̄, F) = colim_{k'} H^i(X_{k'}, F)`
are discrete `Λ[Ẑ]`-modules: every class comes from a finite level. The model used here is the
bounded below derived category of the abelian category of discrete `Λ[Q]`-modules, which has
enough injectives (Tag 04JF) and in which `RΓ^Gal` is an honest right derived functor, so that
its value is the complex `Γ(X_k̄, I|_{X_k̄})` with its Galois action for an injective resolution
`I` on `X`. For a finite ring `Λ` and a finite module, a discrete `Λ[Q]`-module is the same as a
`Λ[[Q]] = lim Λ[Q/U]`-module (the action factors through some finite `Q/U`), so the source's
`D(Λ[[Ẑ]])` statements about complexes with finite cohomology are faithfully modelled; the exact
functor into `D(ModuleCat Λ[[Q]])` is built separately.

*The derived category.* The definitions take the derived categories as free
`[HasDerivedCategory]` arguments; the base's `RΓ(X_k̄, -)` and `RΓ_c(X_k̄, -)` live at
`CategoryTheory.HasDerivedCategory.standard`, where the comparisons are stated.

*The unit.* `Γ^Gal(I) ⟶ RΓ^Gal(I)` is Mathlib's
    `CategoryTheory.Functor.rightDerivedFunctorPlusUnit`;
it is invertible at bounded below complexes of injectives, and typeclass inference finds this
through the derivability structure of
`Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean`.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM).
* [Stacks Project, Tag 04JF](https://stacks.math.columbia.edu/tag/04JF).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe w₁ w₂ w₃ w₄ u

namespace Stacks.EtaleCohomology

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the object
universe: the general instance is indexed by `max (u + 1) r`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galois (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

section Derived

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λ k kbar)]

/-- **`RΓ^Gal(Y_k̄, -)`**: the right derived functor, on bounded below derived categories, of
`F ↦ Γ(Y_k̄, F|_{Y_k̄})` with its action of `Aut_k(k̄)`, with values in discrete
`Λ[Aut_k(k̄)]`-modules. -/
abbrev galoisDerivedGlobalSections :
    DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y.left) ⥤
      DerivedCategory.Plus (GaloisModules Λ k kbar) :=
  (galoisGlobalSections Λ Y kbar).rightDerivedFunctorPlus

end Derived

section CompactSupport

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λ k kbar)]

/-- The ambient scheme of a compactification over `k` is quasi-compact over `k`. -/
instance quasiCompact_compactification_toBase :
    QuasiCompact (Over.mk j.toBase).hom :=
  inferInstanceAs (QuasiCompact j.toBase)

/-- The ambient scheme of a compactification over `k` is quasi-separated over `k`. -/
instance quasiSeparated_compactification_toBase :
    QuasiSeparated (Over.mk j.toBase).hom :=
  inferInstanceAs (QuasiSeparated j.toBase)

/-- **`RΓ^Gal_c(X_k̄, K) = RΓ^Gal(X̄_k̄, j_! K)`** (Remark 03UI (2)) for a bounded below complex
`K` of sheaves of `Λ`-modules on `X_étale` and a compactification `j : X ⟶ X̄` over `k`: extension
by zero to `X̄`, then the Galois-equivariant derived global sections of its restriction to
`X̄_k̄`. Forgetting the action it is `Stacks.EtaleCohomology.galoisCompactSupportCohomology`. -/
abbrev galoisDerivedCompactSupport (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    DerivedCategory.Plus (GaloisModules Λ k kbar) :=
  (galoisDerivedGlobalSections Λ (Over.mk j.toBase) kbar).obj
    (DerivedCategory.Plus.Q.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K))

end CompactSupport

/-! ### Forgetting the action -/

section Forget

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

/-- Enough injectives for discrete Galois modules (Stacks 04JF), pinned at the module universe
`u + 1`: the general instance is indexed by `max 0 u (u + 1)`. -/
local instance (priority := 3000) galoisModules_enoughInjectives (Λ : Type) [Ring Λ]
    (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λ (fieldBaseChange Y kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λ)]

omit [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λ k kbar)] in
/-- **The restriction to `Y_k̄` of an injective sheaf is acyclic for `Γ(Y_k̄, -)`**, in the form of
Stacks 015M: the unit of `RΓ(Y_k̄, -)` is invertible at it. -/
theorem rightAcyclic_etaleModuleGlobalSections_fieldBaseChange (I : EtaleModules.{u, 0} Λ Y.left)
    [Injective I] :
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightAcyclic
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj I) :=
  (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).2 fun q hq =>
    isZero_rightDerived_fieldBaseChange_of_injective Λ Y kbar I q hq

/-- **Forgetting the Galois action, `RΓ^Gal(Y_k̄, -)` is `RΓ(Y_k̄, -|_{Y_k̄})`**: the composite of
`RΓ^Gal` with the forgetful functor `D⁺(GaloisModules Λ k k̄) ⥤ D⁺(Λ)` is the derived restriction
to `Y_k̄` followed by `RΓ(Y_k̄, -)`. The underived functors agree on the nose
(`Stacks.EtaleCohomology.galoisGlobalSections_comp_underlying`); the forgetful functor is exact,
and restriction carries injective sheaves to `Γ(Y_k̄, -)`-acyclic ones
(`Stacks.EtaleCohomology.rightAcyclic_etaleModuleGlobalSections_fieldBaseChange`), so both
composites are the right derived functor of `Γ(Y_k̄, -|_{Y_k̄})` ([Stacks, Tag 015M]): the
comparison is `RΓ^Gal ⋙ U ≅ RΓ^Gal ⋙ RU ≅ R(Γ^Gal ⋙ U) = R(Γ(Y_k̄, -|)) ≅ R(-|) ⋙ RΓ(Y_k̄, -)`,
with `RU ≅ U` and `R(-|) ≅ (-|)` for the exact `U` and `-|_{Y_k̄}`. -/
def galoisDerivedGlobalSectionsForgetIso :
    galoisDerivedGlobalSections Λ Y kbar ⋙
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k]
            kbar)).mapDerivedCategoryPlus ≅
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus :=
  Functor.isoWhiskerLeft _ (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
      (kbar ≃ₐ[k] kbar)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm ≪≫
    (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic (galoisGlobalSections Λ Y kbar)
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar))
      (fun _ _ => (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (kbar ≃ₐ[k] kbar)).rightAcyclic_of_exact _)).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar))
      (fun I _ => rightAcyclic_etaleModuleGlobalSections_fieldBaseChange Λ Y kbar I) ≪≫
    Functor.isoWhiskerRight (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus _

end Forget

end Stacks.EtaleCohomology

end
