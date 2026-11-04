module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingFamily
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportResolutionModel
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.TopDegreePairingTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicResolutionRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyIntComparison
public import StacksFrontier.Algebra.Homology.SingleAugmentationKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpCocycleAct

/-!
# The base case of the derived Poincaré duality of Tag 03VM

For a member `i = (M, I)` of the Poincaré family (`AlgebraicGeometry.PoincareIndex`), with `I` an
injective resolution of `j_! ℱ_M` on the compactification `X̄`, the top-degree pairing
`H²(Γ^Gal(I)) × H⁰(Γ^Gal(ℋom^•(I, K))) → ℚ/ℤ` of the Poincaré pairing is perfect, so that `H²` of
its chain map is an isomorphism (the base case `hbase` of
`AlgebraicGeometry.quasiIso_poincarePairing`).

## Main definitions

* `AlgebraicGeometry.poincareAHomologyIso`: `Hᵐ` of the underlying complex of `Γ^Gal(I)` is
  `Hᵐ_c(X_k̄, ℱ_M)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius
open Stacks.GroupCohomology Stacks.EtaleCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- `etaleModules_enoughInjectives` at the coefficient universe `0`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_resolutionInt (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- **`res_ℤ Hⁱ(Y, N) ≅ Hⁱ(Y, res_ℤ N)` is the comparison of an exact restriction**
(`CategoryTheory.Functor.rightDerivedPlusRestrictionIso`) for global sections and restriction of
scalars to `ℤ`. -/
theorem rightDerivedPlusRestrictScalarsIntIso_eq {Λ : Type} [Ring Λ] (Y : Scheme.{u})
    (N : EtaleModules.{u, 0} Λ Y) (i : ℤ) :
    rightDerivedPlusRestrictScalarsIntIso Y N i =
      Functor.rightDerivedPlusRestrictionIso (etaleModuleGlobalSections.{u, 0} Λ Y)
        (etaleModuleGlobalSections.{u, 0} ℤ Y) (etaleModuleRestrictScalars (Int.castRingHom Λ) Y)
        (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))
        (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y)
        (fun I _ => rightAcyclic_globalSections_of_isAcyclicEverywhere _
          (isAcyclicEverywhere_restrictScalars' (Int.castRingHom Λ) I)) N i :=
  rfl

private lemma map_map_comp_chase {D E F : Type*} [Category* D] [Category* E] [Category* F]
    (H : E ⥤ D) (R : F ⥤ E) {W : D} {F0 F1 F2 : F} (a : W ⟶ H.obj (R.obj F0)) (x : F0 ⟶ F1)
    (y : F1 ⟶ F2) : (a ≫ H.map (R.map x)) ≫ H.map (R.map y) = a ≫ H.map (R.map (x ≫ y)) := by
  simp

section Model

variable {Λ : Type} [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {j : CompactificationOf (Over.mk f)}
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]

/-- **The model `Hᵐ(Γ(X̄_k̄, I|)) ≅ Hᵐ_c(X_k̄, F) ≅ Hᵐ(X̄_k̄, (j_! F)|)` is the computation of
`Hᵐ(X̄_k̄, (j_! F)|)` on the acyclic resolution `I|_{X̄_k̄}`** of `(j_! F)|_{X̄_k̄}`. -/
theorem galoisCompactSupportResolutionIso_trans_singleIso_hom (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) (m : ℤ) :
    (galoisCompactSupportResolutionIso (f := f) kbar F I m ≪≫
        galoisCompactSupportSingleIso f j kbar Λ F m).hom =
      ((etaleModuleGlobalSections.{u, 0} Λ
          (fieldBaseChange (Over.mk j.toBase) kbar)).homologyIsoRightDerivedPlusOfResolution
        ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj I.cocomplexPlus)
        (rightAcyclic_compactSupportResolutionRestriction F I)
        ((DerivedCategory.Plus.Q.mapIso
            ((etaleModuleInverseImage.{u, 0} Λ
                (pullback.fst j.toBase (specAlgebraMap k kbar))).mapCochainComplexPlus.mapIso
                (mapCochainComplexPlusSinglePlusIso
                  (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) F) ≪≫
              mapCochainComplexPlusSinglePlusIso
                (etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar)))
                ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))).symm ≪≫
          @asIso _ _ _ _ (DerivedCategory.Plus.Q.map
            (compactSupportResolutionRestrictionMap (kbar := kbar) F I))
            (isIso_Q_map_compactSupportResolutionRestrictionMap (kbar := kbar) F I)) m).hom :=
  map_map_comp_chase (DerivedCategory.Plus.homologyFunctor _ m)
    (etaleModuleGlobalSections.{u, 0} Λ
      (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedFunctorPlus
    _ _ _

end Model

section CocycleH0

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] [QuasiCompact Y.hom] [QuasiSeparated Y.hom] {Λ : Type} [Ring Λ]
  (L : CochainComplex (EtaleModules.{u, 0} Λ Y.left) ℤ)
  (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Y.left) ℤ)
  {A B : EtaleModules.{u, 0} ℤ (fieldBaseChange Y K)}
  (aL : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A ⟶ galoisBaseChangeComplex Y K L)
  (aK : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B ⟶ galoisBaseChangeComplex Y K Kc)
  [QuasiIso aL] [QuasiIso aK] [(galoisBaseChangeComplex Y K L).IsStrictlyGE 0]
  [(galoisBaseChangeComplex Y K Kc).IsStrictlyGE 0]
  (β : ((galoisHomOpE Y K L Kc).X 0).obj.obj.V)
  (hβ : ((galoisHomOpE Y K L Kc).d 0 1).hom.hom.hom.hom β = 0)

omit [QuasiIso aL] [(galoisBaseChangeComplex Y K L).IsStrictlyGE 0]
  [(galoisBaseChangeComplex Y K Kc).IsStrictlyGE 0] in
/-- The degree-zero component of the cocycle action, on the augmentation of `L`, is killed by the
differential of `K`. -/
lemma galoisHomOpCocycleAct_augmentation_d :
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫ aL.f 0 ≫
      (galoisHomOpCocycleAct Y K L Kc β hβ).f 0) ≫ (galoisBaseChangeComplex Y K Kc).d 0 1 = 0 := by
  rw [Category.assoc, Category.assoc, (galoisHomOpCocycleAct Y K L Kc β hβ).comm, ← Category.assoc,
    ← Category.assoc, CochainComplex.singleObjXSelf_inv_f_d, zero_comp]

/-- **`H⁰` of the cocycle action**: the morphism `A ⟶ B` between the sheaves resolved by `L|` and
`K|` induced by the morphism of complexes of a degree-zero cocycle `β`. -/
def galoisHomOpCocycleH0 : A ⟶ B :=
  (CochainComplex.isLimitKernelForkOfSingleQuasiIso _ B aK).lift
    (KernelFork.ofι _ (galoisHomOpCocycleAct_augmentation_d Y K L Kc aL β hβ))

omit [QuasiIso aL] [(galoisBaseChangeComplex Y K L).IsStrictlyGE 0] in
/-- The morphism `galoisHomOpCocycleH0` followed by the degree-zero component of `aK` equals the
degree-zero component of `aL` followed by that of the cocycle action. -/
lemma galoisHomOpCocycleH0_fac :
    galoisHomOpCocycleH0 Y K L Kc aL aK β hβ ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv ≫ aK.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫ aL.f 0 ≫
        (galoisHomOpCocycleAct Y K L Kc β hβ).f 0 :=
  Fork.IsLimit.lift_ι (CochainComplex.isLimitKernelForkOfSingleQuasiIso _ B aK)

omit [QuasiIso aL] [(galoisBaseChangeComplex Y K L).IsStrictlyGE 0] in
/-- **The cocycle action lies over its `H⁰`**: `aL ≫ β̃ = H⁰(β̃)[0] ≫ aK`. -/
theorem augmentation_comp_galoisHomOpCocycleAct :
    aL ≫ galoisHomOpCocycleAct Y K L Kc β hβ =
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (galoisHomOpCocycleH0 Y K L Kc aL aK β hβ) ≫ aK := by
  refine HomologicalComplex.from_single_hom_ext ?_
  have h := galoisHomOpCocycleH0_fac Y K L Kc aL aK β hβ
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self]
  rw [← cancel_epi (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h ⊢
  exact h.symm

end CocycleH0

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- `etaleModules_enoughInjectives` at the coefficient universe `0` of this file. -/
local instance (priority := 3000) etaleModules_enoughInjectives_poincareDegreeTwo (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable {B : BigEtaleSite.{u}} {X : B.Scheme} [ConnectedSpace X.1]
  {x : GeometricPoint X.1} {Λ : Type} [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] {f : X.1 ⟶ Spec (.of k)} [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] {j : CompactificationOf (Over.mk f)} (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]

/-- **`Hᵐ(Γ^Gal(I))` on underlying abelian groups is `Hᵐ_c(X_k̄, ℱ_M)`**, for a member `(M, I)` of
the Poincaré family: the `m`-th cohomology of the complex of abelian groups underlying `Γ^Gal(I)`
is isomorphic to the `m`-th compactly supported cohomology of `ℱ_M` on `X_k̄`. -/
def poincareAHomologyIso (i : PoincareIndex B X x Λ f j) (m : ℤ) :
    (Stacks.ContinuousCohomology.underlyingAb Λ
        (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)).homology m ≅
      (forget₂ (ModuleCat Λ) AddCommGrpCat).obj
        (galoisCompactSupportCohomologyGroup Λ f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf B X x Λ).obj i.M)) m) :=
  ((((etaleModuleGlobalSections.{u, 0} Λ
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex
      _).obj (((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          i.I.cocomplex)).sc m).mapHomologyIso (forget₂ (ModuleCat Λ) AddCommGrpCat) ≪≫
    (forget₂ (ModuleCat Λ) AddCommGrpCat).mapIso (galoisCompactSupportResolutionIso kbar _ i.I m)

end AlgebraicGeometry

end
