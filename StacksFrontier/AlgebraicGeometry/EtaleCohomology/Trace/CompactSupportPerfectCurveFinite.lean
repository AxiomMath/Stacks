module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CompactSupportCurveFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstructibleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfCorner
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfectness of `RΓ_c(X_k̄, F)` on a curve

Let `X` be a separated scheme of finite type and of dimension at most one over a finite field `k`,
`j : X ⟶ X̄` a compactification, `k̄` an algebraic closure of `k` and `F` a constructible sheaf of
`ℤ/pᵐℤ`-modules on `X_étale`. The cohomology over `ℤ/pℤ` of the reduction `((j_! F)|_{X̄_k̄})[p]`
is finite in every degree. Hence, for `F` flat, `RΓ_c(X_k̄, F)` is perfect, and the complexes
`Kₙ = RΓ_c(X_k̄, F'ₙ)` of the torsion-free model `F'` of an `ℓ`-adic sheaf on a curve are perfect:
this is the perfectness assertion of [Stacks, Tag 03V3] on curves, the item (1) of the proof of
[Stacks, Tag 03V2] in dimension at most one.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `module_finite_homology_derivedDirectImageSections_reduction_of_topologicalKrullDim_le_one`:
  `Hⁱ(X̄_k̄, ((j_! F)|_{X̄_k̄})[p])` is finite over `ℤ/pℤ`.
* `isPerfect_compactSupportFrobeniusCohomology_single_of_powExact_of_topologicalKrullDim_le_one`:
  `RΓ_c(X_k̄, F)` is perfect for a flat constructible `F` on a curve.
* `isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_topologicalKrullDim_le_one`, in
  the namespace `LAdicSheaf`: the complexes `Kₙ` of the torsion-free model of an `ℓ`-adic sheaf on
  a curve are perfect (the input `hP` of `LAdicSheaf.traceFormula_of_levelTraceFormula`).
* `LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le_one`:
  the groups `Hⁱ_c(X_k̄, F)` of an `ℓ`-adic sheaf on a curve are finite dimensional over `ℚ_ℓ`.

## Implementation notes

The reduction `G[p]` of `G = (j_! F)|_{X̄_k̄}` is a sheaf of `ℤ/pℤ`-modules; its cohomology is
finite over `ℤ/pℤ` as soon as it is finite over `ℤ/pᵐℤ` after restriction of scalars, which does
not change cohomology (`Stacks.EtaleCohomology.rightDerivedPlusRestrictScalarsIso`). Read over
`ℤ/pᵐℤ` it is the `p`-torsion of `G`, the kernel of multiplication by `p`, which commutes with the
exact functors `j_!` and inverse image: `G[p] ≅ j_{k̄!}((F[p])|_{X_k̄})`. So its cohomology on
`X̄_k̄` is `Hⁱ_c(X_k̄, (F[p])|_{X_k̄})`, finite by [Stacks, Tag 0GKR] since `F[p]` is constructible
(a kernel of a map of constructible sheaves) and so is its inverse image on a big étale site
containing `X_k̄` (`Stacks.EtaleCohomology.exists_isConstructibleEtaleModule_inverseImage`).

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 0GKR](https://stacks.math.columbia.edu/tag/0GKR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### Change of coefficients -/

section Coefficients

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- **Finiteness of `Hⁱ(RΓ(S, Rg_* G))` descends along restriction of scalars**: if the
cohomology of a sheaf of `Λ'`-modules is finite over `Λ` after restriction of scalars along
`ρ : Λ →+* Λ'`, it is finite over `Λ'`, restriction of scalars commuting with cohomology. -/
theorem module_finite_homology_derivedDirectImageSections_of_restrictScalars {Y S : Scheme.{u}}
    (g : Y ⟶ S) (G : EtaleModules.{u, 0} Λ' Y) (i : ℤ)
    (h : Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      (derivedDirectImageSections g Λ ((etaleModuleRestrictScalars ρ Y).obj G)))) :
    Module.Finite Λ' ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ') i).obj
      (derivedDirectImageSections g Λ' G)) := by
  let e : ∀ (R : Type) [CommRing R] (H : EtaleModules.{u, 0} R Y),
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj
          (derivedDirectImageSections g R H) ≅
        ((etaleModuleGlobalSections.{u, 0} R Y).rightDerivedPlus i).obj H := fun R _ H =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).mapIso
      (derivedDirectImageSectionsIsoDerivedGlobalSections R g H)
  let e' := (ModuleCat.restrictScalars.{u + 1} ρ).mapIso (e Λ' G) ≪≫
    rightDerivedPlusRestrictScalarsIso ρ Y G i ≪≫ (e Λ _).symm
  have : Module.Finite Λ ((ModuleCat.restrictScalars.{u + 1} ρ).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ') i).obj
        (derivedDirectImageSections g Λ' G))) :=
    Module.Finite.equiv e'.symm.toLinearEquiv
  exact ModuleCat.finite_of_finite_restrictScalars ρ _

/-- **Torsion commutes with left exact additive functors**: `E(F)[N] ≅ E(F[N])` for a left exact
additive functor `E` between sheaves of `ℤ/pᵐℤ`-modules, both being kernels of multiplication by
`N` on `E(F)`. -/
def etaleModuleTorsionMapIso {p m N : ℕ} (hN : N ∣ p ^ m) {X Y : Scheme.{u}}
    (E : EtaleModules.{u, 0} (ZMod (p ^ m)) X ⥤ EtaleModules.{u, 0} (ZMod (p ^ m)) Y)
    [E.Additive] [PreservesFiniteLimits E] (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) :
    (etaleModuleTorsion Y N hN).obj (E.obj F) ≅ E.obj ((etaleModuleTorsion X N hN).obj F) :=
  IsLimit.conePointUniqueUpToIso (isTorsionKernel_etaleModuleTorsionι (hN := hN) (E.obj F)).isLimit
    ((isTorsionKernel_etaleModuleTorsionι (hN := hN) F).map E).isLimit

/-- A sheaf of `ℤ/mℤ`-modules is torsion. -/
theorem isTorsionEtaleModule_zmod {X : Scheme.{u}} (m : ℕ) [NeZero m]
    (G : EtaleModules.{u, 0} (ZMod m) X) : IsTorsionEtaleModule.{u, 0} (ZMod m) X G :=
  fun V x => ⟨⊤, (X.smallEtaleTopology).top_mem V, fun W g _ =>
    ⟨m, Nat.pos_of_ne_zero (NeZero.ne m), by
      rw [← Nat.cast_smul_eq_nsmul (ZMod m), ZMod.natCast_self, zero_smul]⟩⟩

end Coefficients

/-! ### Compactly supported cohomology on `X_k̄` through `X̄_k̄` -/

section CompactSupport

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`RΓ(Spec k̄, R(X̄_k̄ ⟶ Spec k̄)_* (j_{k̄!} H)) = RΓ_c(X_k̄, H)`**: the compactly supported
cohomology of `X_k̄` through the base change of `j` (Definition 0GJZ) at a sheaf placed in degree
zero, extension by zero being exact. -/
def derivedDirectImageSectionsExtensionByZeroIso (Λ : Type) [Ring Λ]
    (H : EtaleModules.{u, 0} Λ (pullback f (specAlgebraMap k kbar))) :
    derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) Λ
        ((etaleModuleExtensionByZero.{u, 0} Λ
            (compactificationFieldBaseChangeImmersion f j kbar)).obj
          H) ≅
      DerivedCategory.Plus.ι.obj ((compactlySupportedCohomology.{u, 0} kbar
        (pullback.snd f (specAlgebraMap k kbar)) (compactificationFieldBaseChange f j kbar) Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj H)) :=
  DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
    ((etaleModuleDerivedDirectImage.{u, 0} Λ
      (pullback.snd j.toBase (specAlgebraMap k kbar))).mapIso
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleExtensionByZero.{u, 0} Λ (compactificationFieldBaseChangeImmersion f j kbar))
          0).app H)))

end CompactSupport

/-! ### Finiteness of the cohomology of the reduction on a curve -/

section Curve

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable {k : Type u} [Field k] (B : BigEtaleSite.{u}) (X : B.Scheme) (f : X.obj ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]

omit [IsSeparated f] [IsAlgClosed kbar] in
/-- **`Hⁱ(X̄_k̄, ((j_! F)|_{X̄_k̄})[p])` is finite as soon as compactly supported cohomology on
`X_k̄` is.** For a constructible sheaf `F` of `ℤ/pᵐℤ`-modules on a separated scheme `X` of finite
type over a field `k`, a compactification `j : X ⟶ X̄` and an algebraically closed extension `k̄`
of `k`, the cohomology over `ℤ/pℤ` of the reduction of `(j_! F)|_{X̄_k̄}` is finite in every
degree, provided `Hᵠ_c(X_k̄, G)` is a finite `ℤ/pᵐℤ`-module for every constructible `G` on `X_k̄`
(Tag 0GKR in dimension at most one, Tag 0GL0 in general). -/
theorem module_finite_homology_derivedDirectImageSections_reduction_of_finite
    (hfin : ∀ (B' : BigEtaleSite.{u}) (hY : B'.Contains (pullback f (specAlgebraMap k kbar)))
      (G : EtaleModules.{u, 0} (ZMod (p ^ m)) (pullback f (specAlgebraMap k kbar))),
      IsBigSiteConstructibleEtaleModule B' (B'.obj _ hY) (ZMod (p ^ m)) G → ∀ q : ℤ,
        Module.Finite (ZMod (p ^ m)) ((compactlySupportedCohomologyGroup.{u, 0} kbar
          (pullback.snd f (specAlgebraMap k kbar)) (compactificationFieldBaseChange f j kbar)
          (ZMod (p ^ m)) q).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X (ZMod (p ^ m)) F) (i : ℤ) :
    Module.Finite (ZMod p)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
        (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (ZMod p) ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
            ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F))))) := by
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (specAlgebraMap k kbar))
  have : QuasiSeparatedSpace ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (specAlgebraMap k kbar))
  refine module_finite_homology_derivedDirectImageSections_of_restrictScalars (torsionCoeff p m)
    _ _ i ?_
  have hN : p ∣ p ^ m := dvd_pow_self p (NeZero.ne m)
  let Λ := ZMod (p ^ m)
  let gX := pullback.fst f (specAlgebraMap k kbar)
  let E := etaleModuleExtensionByZero.{u, 0} Λ j.immersion ⋙
    etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
  have : PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} Λ
      (pullback.fst j.toBase (specAlgebraMap k kbar))) :=
    etaleModuleInverseImage_preservesFiniteLimits _ _
  let F' := (etaleModuleTorsion X.obj p hN).obj F
  have hF' : IsBigSiteConstructibleEtaleModule B X Λ F' := by
    have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B X Λ
    exact (IsBigSiteConstructibleEtaleModule B X Λ).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel ((p : ℕ) • 𝟙 F))
        (isTorsionKernel_etaleModuleTorsionι (hN := hN) F).isLimit)
      ((IsBigSiteConstructibleEtaleModule B X Λ).prop_kernel _ hF hF)
  obtain ⟨B', hY, hc⟩ := exists_isConstructibleEtaleModule_inverseImage Λ B X gX F' hF'
  have h0 := hfin B' hY ((etaleModuleInverseImage.{u, 0} Λ gX).obj F') hc i
  let e₁ : (etaleModuleTorsion _ p hN).obj (E.obj F) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ (compactificationFieldBaseChangeImmersion f j kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λ gX).obj F') :=
    etaleModuleTorsionMapIso hN E F ≪≫
      ((compactificationFieldBaseChangeExtensionByZeroIso.{u, 0} Λ f j kbar).app F').symm
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) Λ
        ((etaleModuleTorsion _ p hN).obj (E.obj F))) ≅
      (compactlySupportedCohomologyGroup.{u, 0} kbar (pullback.snd f (specAlgebraMap k kbar))
        (compactificationFieldBaseChange f j kbar) Λ i).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} Λ gX).obj F')) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
      (DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedGlobalSections.{u, 0} Λ
        (Spec (.of kbar))).mapIso ((etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd j.toBase (specAlgebraMap k kbar))).mapIso
            ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e₁))) ≪≫
        derivedDirectImageSectionsExtensionByZeroIso f j kbar Λ _)
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- **`Hⁱ(X̄_k̄, ((j_! F)|_{X̄_k̄})[p])` is finite on a curve.** For a constructible sheaf `F` of
`ℤ/pᵐℤ`-modules on a separated scheme `X` of finite type and of dimension at most one over a
field `k`, a compactification `j : X ⟶ X̄` and an algebraically closed extension `k̄` of `k`, the
cohomology over `ℤ/pℤ` of the reduction of `(j_! F)|_{X̄_k̄}` is finite in every degree. -/
theorem module_finite_homology_derivedDirectImageSections_reduction_of_topologicalKrullDim_le_one
    (hdim : topologicalKrullDim X.obj ≤ 1) (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X (ZMod (p ^ m)) F) (i : ℤ) :
    Module.Finite (ZMod p)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
        (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (ZMod p) ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
            ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F))))) := by
  have hdimk : topologicalKrullDim ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) ≤ 1 := by
    have h := topologicalKrullDim_pullback_le_of_fiber f 1
      (fun y ↦ (topologicalKrullDim_fiber_of_spec_field k f y).le.trans (by exact_mod_cast hdim))
      (specAlgebraMap k kbar)
    exact_mod_cast h
  exact module_finite_homology_derivedDirectImageSections_reduction_of_finite B X f j kbar p m
    (fun B' hY G hc q => TorsionModules.module_finite_compactlySupportedCohomologyGroup B'
      (B'.obj _ hY) (pullback.snd f (specAlgebraMap k kbar)) hdimk
      (compactificationFieldBaseChange f j kbar) _ G hc (isTorsionEtaleModule_zmod _ _) q) F hF i

/-- **Perfectness of `RΓ_c(X_k̄, F)` on a curve**, for a flat constructible sheaf `F` of
`ℤ/pᵐℤ`-modules on a separated scheme of finite type and of dimension at most one over a finite
field. -/
theorem isPerfect_compactSupportFrobeniusCohomology_single_of_powExact_of_topologicalKrullDim_le_one
    [Finite k] (hdim : topologicalKrullDim X.obj ≤ 1)
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X.obj) (hF : PowExact p m F)
    (hc : IsBigSiteConstructibleEtaleModule B X (ZMod (p ^ m)) F) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (p ^ m)) f j kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)) :=
  have := Fintype.ofFinite k
  isPerfect_compactSupportFrobeniusCohomology_single_of_powExact_of_finite f j kbar p m F hF
    (module_finite_homology_derivedDirectImageSections_reduction_of_topologicalKrullDim_le_one
      B X f j kbar p m hdim F hc)

end Curve

section LAdic

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar]

local notation "model" F => LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)

/-- The levels of an `ℓ`-adic sheaf, read on Mathlib's small étale site, are constructible. -/
theorem LAdicSheaf.isConstructibleEtaleModule_etaleLevel (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (n : ℕ) :
    IsBigSiteConstructibleEtaleModule B X (ZMod (ℓ ^ (n + 1))) (LAdicSheaf.etaleLevel B X ℓ F n) :=
  isConstructibleModuleSheaf_congr B (ZMod (ℓ ^ (n + 1))) X
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).unitIso.app
      (F.level n)) (F.constructible n)

omit [Fintype k] in
/-- **The complexes `Kₙ = RΓ_c(X_k̄, F'ₙ)` of the torsion-free model of an `ℓ`-adic sheaf on a
curve are perfect** (item (1) of the proof of [Stacks, Tag 03V2], the perfectness of
[Stacks, Tag 03V3], in dimension at most one). -/
theorem
  LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_topologicalKrullDim_le_one
    [Finite k] (hdim : topologicalKrullDim X.1 ≤ 1) (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n))) :=
  have := Fintype.ofFinite k
  LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_finite B X ℓ f j kbar F
    (fun n' i =>
      module_finite_homology_derivedDirectImageSections_reduction_of_topologicalKrullDim_le_one
      B X f j kbar ℓ (n' + 1) hdim _
      (LAdicSheaf.isConstructibleEtaleModule_etaleLevel B X ℓ (model F) n') i) n

variable (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

omit [CharP kbar p] in
include p q hcard in
/-- **The groups `Hⁱ_c(X_k̄, F)` of an `ℓ`-adic sheaf on a curve are finite dimensional over
`ℚ_ℓ`** (part of [Stacks, Tag 03V2] in dimension at most one). -/
@[sga "4½ Rapport 2.10" "special case",
  sga "4½ Rapport 4.11" "special case",
  sga "7 I 0.1.1" "special case",
  sga "7 XXI 2.0" "special case"]
theorem
  LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le_one
    (hdim : topologicalKrullDim X.1 ≤ 1) (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ) :
    Module.Finite ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
  (LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_perfect B X ℓ f j kbar p q
    hcard F · i) <|
  LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_topologicalKrullDim_le_one
    B X ℓ f j kbar hdim F

end LAdic

end Stacks.EtaleCohomology

end
