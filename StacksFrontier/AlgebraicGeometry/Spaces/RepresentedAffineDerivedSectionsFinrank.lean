module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffinePushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFlatBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsTerminalObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization

/-!
# Dimensions of the derived sections of a direct image over the spectrum of a field

Let `U` be an object of the big fppf site whose scheme is affine with ring of functions
`k = Γ(U)` a field, `f : X ⟶ U` a quasi-compact and quasi-separated morphism of algebraic spaces
and `N` a quasi-coherent `𝒪_X`-module.  The derived sections `RΓ(U, Rf_*N[0])` are a complex of
`k`-vector spaces, and

`dim_k Hⁱ(RΓ(U, Rf_*N[0])) = dim_k Hⁱ(X, N)`

for `i ≥ 0`, the cohomology on the right being read over `k` through `f`; for `i < 0` the left
hand side vanishes.  This is the comparison by which a finite projective model of the derived
sections of a family (Stacks 0A1Q) computes the cohomology of its fibres.

The derived sections over `U` are the sections of the cohomology sheaves of `Rf_*N[0]` (which has
quasi-coherent cohomology, Stacks 08FA), and these are the higher direct images `Rⁱf_*N`.  Over an
affine base their global sections are `Hⁱ(X, N)` (Stacks 0732, 08EX).  It remains to compare the
sections over `U` of a quasi-coherent module `P` in the sense of the associated-module
equivalence with its global sections on the small étale site: `P` is the associated module of
`Γ(U, P) ≅ k^d`, so it is free of rank `d`, and the global sections of a free module of rank `d`
have dimension `d`.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `globalSectionsUnitLinearEquiv`: the global sections of the structure sheaf are the ring of
  global sections.
* `finrank_globalSections_free`: the global sections of the free module of rank `d` have rank `d`.
* `finrank_globalSections_eq_finrank_representedAffineSections`: the two readings of the sections
  of a quasi-coherent module over an affine field-valued `U` have the same dimension.
* `finrank_homology_representedAffineDerivedSections_derivedModulePushforward`: the identity
  above.
* `isZero_homology_representedAffineDerivedSections_derivedModulePushforward_of_neg`: the
  vanishing in negative degrees.

## Implementation notes

The derived categories are those of the standard model `HasDerivedCategory.standard`, in which
`AlgebraicGeometry.Space.representedAffineDerivedSections` and
`AlgebraicGeometry.Space.derivedModulePushforward` are stated; the instances are named inside the
statements and proofs.

## References

* [Stacks Project, Tag 0A1Q](https://stacks.math.columbia.edu/tag/0A1Q)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 08EX](https://stacks.math.columbia.edu/tag/08EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Unit

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u})

/-- The global sections of the structure sheaf, as a module over the ring of global sections, are
that ring. -/
def globalSectionsUnitLinearEquiv :
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor O).obj
      (SheafOfModules.unit O) ≃ₗ[RingCat.sectionsSubring O.obj] RingCat.sectionsSubring O.obj where
  toFun s := ⟨s.1, fun f => s.2 f⟩
  invFun r := ⟨r.1, fun f => r.2 f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end Unit

/-- **The global sections of a free module of finite rank.**  On an algebraic space `Y` whose ring
of global functions is nontrivial, the global sections of the free `𝒪_Y`-module of rank `d` form a
module of rank `d`. -/
theorem finrank_globalSections_free (Y : AlgebraicSpaces B S hS)
    [Nontrivial (RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)]
    (d : ℕ) :
    Module.finrank (RingCat.sectionsSubring
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj
        (SheafOfModules.free (ULift.{u} (Fin d)))) = d := by
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O
  let G := Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u} O
  let M := G.obj (SheafOfModules.unit O)
  let eU := globalSectionsUnitLinearEquiv O
  have : Module.Free (RingCat.sectionsSubring O.obj) M := Module.Free.of_equiv eU.symm
  have : Module.Finite (RingCat.sectionsSubring O.obj) M := Module.Finite.equiv eU.symm
  have : G.Additive := Stacks.Cohomology.SiteModules.globalSectionsFunctor_additive O
  let e₀ : SheafOfModules.free (ULift.{u} (Fin d)) ≅ ∐ fun _ : Fin d => SheafOfModules.unit O :=
    (SheafOfModules.isColimitFreeCofan (R := O) (ULift.{u} (Fin d))).coconePointUniqueUpToIso
        (coproductIsCoproduct _) ≪≫
      Sigma.whiskerEquiv (f := fun _ : ULift.{u} (Fin d) => SheafOfModules.unit O)
        (g := fun _ : Fin d => SheafOfModules.unit O) Equiv.ulift (fun _ => Iso.refl _)
  let e : G.obj (SheafOfModules.free (ULift.{u} (Fin d))) ≅ ModuleCat.of _ (Fin d → M) :=
    G.mapIso (e₀ ≪≫ (biproduct.isoCoproduct (fun _ : Fin d => SheafOfModules.unit O)).symm) ≪≫
      G.mapBiproduct _ ≪≫ ModuleCat.biproductIsoPi _
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype, eU.finrank_eq, Module.finrank_self]
  simp

/-- Dimensions do not change when the ring is replaced by an isomorphic one. -/
theorem _root_.ModuleCat.finrank_restrictScalars_ringEquiv {k K : Type*} [CommRing k] [CommRing K]
    (e : k ≃+* K) (N : ModuleCat K) :
    Module.finrank k ((ModuleCat.restrictScalars e.toRingHom).obj N) = Module.finrank K N :=
  congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv (M := (ModuleCat.restrictScalars e.toRingHom).obj N) (M₁ := N) e
      (AddEquiv.refl _) e.bijective (fun _ _ => rfl))

/-- **Global sections and sections over an affine scheme have the same dimension.**  Let `U` be an
object of the site whose scheme is affine with ring of functions `R = Γ(U)` a field, and `P` a
quasi-coherent module on the algebraic space `U` represents whose module of sections
`Γ(U, P)` over `R` is finite.  Then the global sections of `P` on the small étale site have the
same dimension over the ring of global functions: `P` is the associated module of
`Γ(U, P) ≅ R^d`, that is the free module of rank `d`. -/
theorem finrank_globalSections_eq_finrank_representedAffineSections
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (hU : IsField Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (P : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite)
    (hfin : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((representedAffineSections B S hS U).obj P)) :
    Module.finrank (RingCat.sectionsSubring
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O).obj)
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)).obj P) =
      Module.finrank Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        ((representedAffineSections B S hS U).obj P) := by
  let : Field Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := hU.toField
  let R := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let W := (representedAffineSections B S hS U).obj P
  let d := Module.finrank R W
  let b := Module.finBasis R W
  let eL : W ≃ₗ[R] DirectSum (ULift.{u} (Fin d)) fun _ => R :=
    b.equivFun ≪≫ₗ LinearEquiv.funCongrLeft R R Equiv.ulift ≪≫ₗ
      (DirectSum.linearEquivFunOnFintype R (ULift.{u} (Fin d)) fun _ => R).symm
  let eW : W ≅ ∐ fun _ : ULift.{u} (Fin d) => ModuleCat.of R R :=
    eL.toModuleIso ≪≫
      (ModuleCat.coprodIsoDirectSum fun _ : ULift.{u} (Fin d) => ModuleCat.of R R).symm
  have := isIso_representedAffineAssociatedAdjunction_counit_app B S hS P hP
  let eP : P ≅ SheafOfModules.free (ULift.{u} (Fin d)) :=
    (asIso ((representedAffineAssociatedAdjunction B S hS U).counit.app P)).symm ≪≫
      (representedAffineAssociated B S hS U).mapIso eW ≪≫
      representedAffineAssociatedSigmaUnitIso (B := B) (S := S) (hS := hS) (U := U) d
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (schemeSpace U).1).obj (schemeSpaceSelfChart U)), ⊤) :=
    show Nontrivial R from inferInstance
  have hnt : Nontrivial (RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O).obj) :=
    (globalSectionsChartRingEquiv B S hS (schemeSpace U)
      (isTerminal_of_isIso_chart B S hS _ (schemeSpaceSelfChart U))).toEquiv.nontrivial
  exact ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      _).mapIso eP).toLinearEquiv.finrank_eq.trans
    (@finrank_globalSections_free B S hS (schemeSpace U) hnt d)

/-- **The derived sections of a direct image over the spectrum of a field compute the
cohomology.**  For `U` with affine scheme and field of functions `k`, a quasi-compact and
quasi-separated `f : X ⟶ U` and a quasi-coherent `N`, if `Hⁱ(RΓ(U, Rf_*N[0]))` is finite
dimensional then its dimension is that of `Hⁱ(X, N)` read over `k` through `f` and the identity
chart of `U`. -/
theorem finrank_homology_representedAffineDerivedSections_derivedModulePushforward
    {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (hU : IsField Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace U)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) [N.IsQuasicoherentOnSite] (i : ℕ) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    haveI := hasInjectiveResolutions_modules B S hS X.1 X.2
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (i : ℤ)).obj
        ((representedAffineDerivedSections B S hS U).obj
        ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj N)))) →
    Module.finrank Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (i : ℤ)).obj
        ((representedAffineDerivedSections B S hS U).obj
        ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj N)))) =
      Module.finrank (baseChartRing B S hS (schemeSpace U) (schemeSpaceSelfChart U))
        ((baseChartRestrictScalars B S hS (schemeSpace U)
          (isTerminal_of_isIso_chart B S hS _ (schemeSpaceSelfChart U))).obj
          ((globalSectionsRestrictScalars B S hS f).obj
            (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj N))) := by
  intro hfin
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have hN0 : QcohDerived B S hS X ((DerivedCategory.singleFunctor _ 0).obj N) := by
    intro j
    rcases lt_trichotomy j 0 with hj | rfl | hj
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero (DerivedCategory.isZero_of_isGE _ 0 j hj)
    · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app N).symm ‹_›
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero (DerivedCategory.isZero_of_isLE _ 0 j hj)
  let E := (derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj N)
  have hE : QcohDerived B S hS (schemeSpace U) E :=
    qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs _ hN0
  let e₁ := representedAffineDerivedSectionsHomologyIso B S hS U E hE i
  let eR := Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (modulePushforward B S hS f)
    (derivedModulePushforward B S hS f) (derivedModulePushforwardUnit B S hS f)
    Stacks.Cohomology.Localization.enoughKInjectives N i
  let eG := cohomologyRestrictScalarsIsoGlobalSectionsHigherDirectImage B S hS f
    (isAffineSpace_yoneda B S hS U inferInstance) hfqc hfqs N
    (acyclicPushforwardOfInjective B S hS f) i
  have hcore := finrank_globalSections_eq_finrank_representedAffineSections B S hS U hU _ (hE i)
    (Module.Finite.equiv e₁.toLinearEquiv)
  exact e₁.toLinearEquiv.finrank_eq.trans (hcore.symm.trans
    ((((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      _).mapIso eR).toLinearEquiv.finrank_eq.trans eG.symm.toLinearEquiv.finrank_eq).trans
      (ModuleCat.finrank_restrictScalars_ringEquiv _ _).symm))

/-- **The derived sections of `Rf_*(N[0])` vanish in negative degrees** over an affine base. -/
theorem isZero_homology_representedAffineDerivedSections_derivedModulePushforward_of_neg
    {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace U)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) [N.IsQuasicoherentOnSite] {i : ℤ} (hi : i < 0) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) i).obj
        ((representedAffineDerivedSections B S hS U).obj
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)))) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
  have hN0 : QcohDerived B S hS X ((DerivedCategory.singleFunctor _ 0).obj N) := by
    intro j
    rcases lt_trichotomy j 0 with hj | rfl | hj
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero (DerivedCategory.isZero_of_isGE _ 0 j hj)
    · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app N).symm ‹_›
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero (DerivedCategory.isZero_of_isLE _ 0 j hj)
  let E := (derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj N)
  have hE : QcohDerived B S hS (schemeSpace U) E :=
    qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs _ hN0
  have : E.IsGE 0 := isGE_rightDerived_modulePushforward_obj_singleFunctor B S hS f
    (derivedModulePushforward B S hS f) (derivedModulePushforwardUnit B S hS f) N
  exact IsZero.of_iso
    ((representedAffineSections B S hS U).map_isZero (DerivedCategory.isZero_of_isGE E 0 i hi))
    (representedAffineDerivedSectionsHomologyIso B S hS U E hE i)

end AlgebraicGeometry.Space
