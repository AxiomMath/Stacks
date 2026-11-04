module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompactSupportFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZeroComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriekAffineEtale
public import StacksFrontier.Algebra.Homology.HomotopyCategory.KInjectiveClosure

/-!
# Sheaves of modules over a separably closed field and their cohomology

Let `k` be a separably closed field and `Λ` a ring. Taking global sections is an equivalence from
sheaves of `Λ`-modules on the small étale site of `Spec k` to `Λ`-modules (Stacks 04JN), so it is
exact (Stacks 03QO). Hence the derived global sections `RΓ(Spec k, -)`, on the bounded below and
on the unbounded derived category, commute with taking cohomology:
`Hⁱ(RΓ(Spec k, K)) ≅ Γ(Spec k, Hⁱ(K))`. When `k` is algebraically closed, a constructible sheaf
of `Λ`-modules on `Spec k` has finitely generated global sections, which are its stalk at the
canonical geometric point.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsHomologyIsoOfIsSepClosed`: on `D⁺`.
* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnboundedHomologyIsoOfIsSepClosed`:
  on `D`.
* `Stacks.EtaleCohomology.module_finite_etaleModuleGlobalSections_of_isConstructibleModuleSheaf`.

## References

* [Stacks Project, Tag 04JN](https://stacks.math.columbia.edu/tag/04JN)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry ZeroObject

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Exact

variable (k : Type u) [Field k] [IsSepClosed k] (Λ : Type r) [Ring Λ]

/-- Global sections of sheaves of `Λ`-modules over a separably closed field are exact. -/
instance etaleModuleGlobalSections_preservesFiniteColimits_of_isSepClosed :
    PreservesFiniteColimits (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))) :=
  haveI := isEquivalence_etaleModuleGlobalSections_of_isSepClosed Λ k
  inferInstance

end Exact

section Homology

variable (k : Type u) [Field k] [IsSepClosed k] (Λ : Type r) [Ring Λ]

/-- **Derived global sections over a separably closed field commute with cohomology**, on the
bounded below derived category: `Hⁿ(RΓ(Spec k, K)) ≅ Γ(Spec k, Hⁿ(K))`, because `Γ` is exact. -/
def etaleModuleDerivedGlobalSectionsHomologyIsoOfIsSepClosed
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ (Spec (.of k)))) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ n).obj
        ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of k))).obj K) ≅
      (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj K) :=
  (DerivedCategory.Plus.homologyFunctor _ n).mapIso
      ((etaleModuleGlobalSections.{u, r} Λ
        (Spec (.of k))).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app K) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))) n).app (DerivedCategory.Plus.ι.obj K)

/-- **On the unbounded derived category, derived global sections over a separably closed field
are global sections applied degreewise**: `Γ` is exact, so the unit of its total right derived
functor is invertible. -/
def etaleModuleDerivedGlobalSectionsUnboundedIsoMapDerivedCategory :
    etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of k)) ≅
      (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).mapDerivedCategory :=
  haveI : IsIso (etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ (Spec (.of k))) :=
    Functor.isIso_of_isRightDerivedFunctor_of_inverts
      (W := HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ (Spec (.of k)))
        (ComplexShape.up ℤ)) _ _ (fun K L f hf => by
        have := Localization.inverts DerivedCategory.Q
          (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ (Spec (.of k)))
            (ComplexShape.up ℤ)) f hf
        exact (NatIso.isIso_map_iff (etaleModuleGlobalSections.{u, r} Λ
          (Spec (.of k))).mapDerivedCategoryFactors f).1
          (inferInstance : IsIso ((etaleModuleGlobalSections.{u, r} Λ
            (Spec (.of k))).mapDerivedCategory.map (DerivedCategory.Q.map f))))
  haveI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ (Spec (.of k))) (ComplexShape.up ℤ))
      ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of k))) :=
    ⟨(asIso (etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ (Spec (.of k)))).symm⟩
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ (Spec (.of k))) (ComplexShape.up ℤ))
    ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) _ _ (Iso.refl _)

/-- **Derived global sections over a separably closed field commute with cohomology**, on the
unbounded derived category: `Hⁿ(RΓ(Spec k, K)) ≅ Γ(Spec k, Hⁿ(K))`, because `Γ` is exact. -/
def etaleModuleDerivedGlobalSectionsUnboundedHomologyIsoOfIsSepClosed
    (K : DerivedCategory (EtaleModules.{u, r} Λ (Spec (.of k)))) (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).obj
        ((etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of k))).obj K) ≅
      (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).obj
        ((DerivedCategory.homologyFunctor _ n).obj K) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
      ((etaleModuleDerivedGlobalSectionsUnboundedIsoMapDerivedCategory k Λ).app K) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))) n).app K

end Homology

section Finite

/-- Finiteness of a module in `ModuleCat` transfers along an isomorphism. -/
private theorem module_finite_of_iso {R : Type*} [Ring R] {M N : ModuleCat R} (e : M ≅ N)
    (h : Module.Finite R M) : Module.Finite R N :=
  Module.Finite.equiv e.toLinearEquiv

variable (B : BigEtaleSite.{u}) (k : Type u) [Field k] [IsAlgClosed k]
  (hk : B.Contains (Spec (.of k))) (Λ : Type r) [Ring Λ]

/-- **A constructible sheaf of `Λ`-modules over an algebraically closed field has finitely
generated global sections.** Its global sections are its stalk at the canonical geometric point
of `Spec k`, the identity lift being an initial étale neighbourhood, and the stalks of a
constructible sheaf are finitely generated. The sheaf lives on Mathlib's small étale site, and
its constructibility (Stacks 03RW (3)) is that of its transport to the small étale site of
Stacks 021B. -/
theorem module_finite_etaleModuleGlobalSections_of_isConstructibleModuleSheaf
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) r} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max (u + 1) r} Λ)]
    (N : EtaleModules.{u, r} Λ (Spec (.of k)))
    (hN : IsConstructibleModuleSheaf B (B.obj _ hk) Λ
      ((SmallEtale.sheafEquiv B (Spec (.of k)) hk (ModuleCat.{max (u + 1) r} Λ)).inverse.obj N)) :
    Module.Finite Λ ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).obj N) := by
  have : HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ) :=
    hasColimitsOfSizeShrink.{u, u, max (u + 1) r, max (u + 1) r} _
  let E := SmallEtale.sheafEquiv B (Spec (.of k)) hk (ModuleCat.{max (u + 1) r} Λ)
  let s : GeometricPoint (Spec (.of k)) := ⟨k, 𝟙 _⟩
  have h₁ : Module.Finite Λ (((etaleModuleStalkFunctor B (B.obj _ hk) Λ s :
      Sheaf _ (ModuleCat.{max (u + 1) r} Λ) ⥤ ModuleCat.{max (u + 1) r} Λ)).obj
        (E.inverse.obj N)) := by
    have h := stalk_prop_of_isStratifiedLocallyConstantWith B (B.obj _ hk) Λ
      (ModuleCat.isFG Λ : ModuleCat.{max (u + 1) r} Λ → Prop)
      (fun {_ _} e hE => by
        rw [ModuleCat.isFG_iff] at hE ⊢
        have := hE
        exact Module.Finite.equiv e.toLinearEquiv)
      (fun _ hE => by
        rw [ModuleCat.isFG_iff]
        have := hE
        infer_instance)
      _ hN s
    rwa [ModuleCat.isFG_iff] at h
  have h₂ := finite_sheafFiber_sheafEquiv B (B.obj _ hk) Λ s _ h₁
  let Φ := Scheme.pointSmallEtale (𝟙 (Spec (.of k)))
  have h₃ : Module.Finite Λ ((Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj N) :=
    module_finite_of_iso ((Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapIso
      (E.counitIso.app N)) h₂
  have : IsIso ((Φ.presheafFiberCocone N.obj).ι.app
      (op ⟨Scheme.Etale.mk (𝟙 (Spec (.of k))), pointSmallEtaleIdElement k⟩)) :=
    (Φ.isColimitPresheafFiberCocone N.obj).isIso_ι_app_of_isTerminal
      (op ⟨Scheme.Etale.mk (𝟙 (Spec (.of k))), pointSmallEtaleIdElement k⟩)
      (isInitialPointSmallEtaleIdElement k).op
  have h₄ : Module.Finite Λ (N.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of k)))))) :=
    module_finite_of_iso (asIso ((Φ.presheafFiberCocone N.obj).ι.app
      (op ⟨Scheme.Etale.mk (𝟙 (Spec (.of k))), pointSmallEtaleIdElement k⟩))).symm h₃
  exact module_finite_of_iso ((Sheaf.ΓNatIsoSheafSections _ _
    (isTerminalEtaleMkId (Spec (.of k)))).app N).symm h₄

/-- **The cohomology of `RΓ(Spec k, L)` is finite** when `k` is algebraically closed and the
cohomology sheaves of `L ∈ D⁺(Spec k_étale, Λ)` are constructible:
`Hⁿ(RΓ(Spec k, L)) = Γ(Spec k, Hⁿ(L))`. -/
theorem module_finite_homology_etaleModuleDerivedGlobalSections_of_isConstructibleModuleSheaf
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max (u + 1) r} Λ)]
    (L : DerivedCategory.Plus (EtaleModules.{u, r} Λ (Spec (.of k))))
    (hL : ∀ q : ℤ, IsConstructibleModuleSheaf B (B.obj _ hk) Λ
      ((SmallEtale.sheafEquiv B (Spec (.of k)) hk (ModuleCat.{max (u + 1) r} Λ)).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj L))) (n : ℤ) :
    Module.Finite Λ ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) n).obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of k))).obj L)) :=
  module_finite_of_iso (etaleModuleDerivedGlobalSectionsHomologyIsoOfIsSepClosed k Λ L n).symm
    (module_finite_etaleModuleGlobalSections_of_isConstructibleModuleSheaf B k hk Λ _ (hL n))

/-- **The cohomology of `RΓ(Spec k, L)` is finite** when `k` is algebraically closed and the
cohomology sheaves of `L ∈ D(Spec k_étale, Λ)` are constructible:
`Hⁿ(RΓ(Spec k, L)) = Γ(Spec k, Hⁿ(L))`. -/
theorem
    module_finite_homology_etaleModuleDerivedGlobalSectionsUnbounded_of_isConstructibleModuleSheaf
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max (u + 1) r} Λ)]
    (L : DerivedCategory (EtaleModules.{u, r} Λ (Spec (.of k))))
    (hL : ∀ q : ℤ, IsConstructibleModuleSheaf B (B.obj _ hk) Λ
      ((SmallEtale.sheafEquiv B (Spec (.of k)) hk (ModuleCat.{max (u + 1) r} Λ)).inverse.obj
        ((DerivedCategory.homologyFunctor _ q).obj L))) (n : ℤ) :
    Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) n).obj
      ((etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of k))).obj L)) :=
  module_finite_of_iso
    (etaleModuleDerivedGlobalSectionsUnboundedHomologyIsoOfIsSepClosed k Λ L n).symm
    (module_finite_etaleModuleGlobalSections_of_isConstructibleModuleSheaf B k hk Λ _ (hL n))

end Finite

section Empty

/-- A functor `RF` out of `D(A)` with a comparison `α : G ⟶ Q ⋙ RF` which is invertible at a zero
complex `Z` with `G(Z)` zero sends zero objects to zero objects. -/
theorem isZero_obj_of_isIso_app_of_isZero {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {D : Type*} [Category* D] {G : CochainComplex A ℤ ⥤ D}
    {RF : DerivedCategory A ⥤ D} (α : G ⟶ DerivedCategory.Q ⋙ RF) {Z : CochainComplex A ℤ}
    (hZ : IsZero Z) (hGZ : IsZero (G.obj Z)) [IsIso (α.app Z)] {K : DerivedCategory A}
    (hK : IsZero K) : IsZero (RF.obj K) :=
  hGZ.of_iso (RF.mapIso (hK.iso (DerivedCategory.Q.map_isZero hZ)) ≪≫ (asIso (α.app Z)).symm)

variable (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}} [IsEmpty X]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (Λ : Type) [Ring Λ]

/-- Every object of the derived category of sheaves of modules on an empty scheme is zero: its
cohomology sheaves are sheaves on an empty scheme. -/
theorem isZero_derivedCategory_etaleModules_of_isEmpty
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) : IsZero K := by
  have : IsIso (0 : K ⟶ 0) := (DerivedCategory.isIso_iff (f := (0 : K ⟶ 0))).2 fun n =>
    isIso_of_source_target_iso_zero _
      (isZero_etaleModules_of_isEmpty Λ X _).isoZero
      (isZero_etaleModules_of_isEmpty Λ X _).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Cohomology with compact support of an empty scheme vanishes**, on `D⁺(X_étale, Λ)`. -/
theorem isZero_compactlySupportedCohomologyGroup_of_isEmpty
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (i : ℤ) :
    IsZero ((compactlySupportedCohomologyGroup.{u, 0} k f j Λ i).obj K) := by
  have hK : IsZero K := IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι K
    (isZero_derivedCategory_etaleModules_of_isEmpty Λ _)
  have hL : IsZero ((derivedLowerShriek.{u, 0} f j Λ).obj K) := Functor.map_isZero _ hK
  exact (Functor.map_isZero _ (Functor.map_isZero _ hL)).of_iso
    (etaleModuleDerivedGlobalSectionsHomologyIsoOfIsSepClosed k Λ _ i)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Cohomology with compact support of an empty scheme vanishes**, on `D(X_étale, Λ)`. -/
theorem isZero_compactlySupportedCohomologyGroupUnbounded_of_isEmpty
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) (i : ℤ) :
    IsZero ((compactlySupportedCohomologyGroupUnbounded.{u, 0} k f j Λ i).obj K) := by
  have h₀ : IsZero (0 : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) := isZero_zero _
  have h₀' : IsZero (0 : CochainComplex (EtaleModules.{u, 0} Λ j.space) ℤ) := isZero_zero _
  have := isIso_etaleModuleDerivedExtensionByZeroUnboundedUnit_app.{u, 0} Λ j.immersion _
    (CochainComplex.isKInjective_of_isZero h₀)
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ j.toBase _
    (CochainComplex.isKInjective_of_isZero h₀')
  have h₁ : IsZero ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion).obj K) :=
    isZero_obj_of_isIso_app_of_isZero
      (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ j.immersion) h₀
      (Functor.map_isZero _ h₀) (isZero_derivedCategory_etaleModules_of_isEmpty Λ K)
  have h₂ : IsZero ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K) :=
    isZero_obj_of_isIso_app_of_isZero
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ j.toBase) h₀'
      (Functor.map_isZero _ h₀') h₁
  exact (Functor.map_isZero _ (Functor.map_isZero _ h₂)).of_iso
    (etaleModuleDerivedGlobalSectionsUnboundedHomologyIsoOfIsSepClosed k Λ _ i)

end Empty

end Stacks.EtaleCohomology

end
