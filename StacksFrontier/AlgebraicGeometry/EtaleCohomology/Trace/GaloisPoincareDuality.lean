module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDerivedHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingFamily
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpECoeffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpECyclotomicDerivedIsoNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpECyclotomicDerivedIsoOfIsUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpEVanishingOfIsUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomPairingDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicResolutionIsoNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The derived Poincaré duality of Tag 03VM, naturally in the representation

Let `X` be a smooth geometrically connected curve over a field `k`, `k̄` an algebraic closure,
`Q = Aut_k(k̄)`, `Λ` a finite ring with `n = #Λ` invertible in `k`, and `j : X ⟶ X̄` a
compactification. For a finite `Λ`-module `M` with a continuous action of `π₁(X, x̄)` this file
identifies, in the derived category of `Λ[[Q]]`-modules and naturally in `M`,
`RΓ^Gal_c(X_k̄, ℱ_M) ≅ (RΓ^Gal(X_k̄, ℋom(ℱ_M, μ_n)))^∨[-2]`
(`AlgebraicGeometry.galoisCompactSupportPoincareDualityNatIso`).

The isomorphism at `M` is the composite of
* `RΓ^Gal(X̄_k̄, j_! ℱ_M) ≅ Γ^Gal(I)` for an injective resolution `I` of `(j_! ℱ_M)[0]`
  (`CategoryTheory.Functor.rightDerivedFunctorPlusMapSingleInjectiveIso`, natural in lifts of
  morphisms to the resolutions);
* the derived Poincaré pairing `Γ^Gal(I) ⟶ (Γ^Gal(ℋom^•(I, K)))^∨[-2]`
  (`Stacks.ContinuousCohomology.derivedPairing`), invertible by the family theorem
  `AlgebraicGeometry.quasiIso_poincarePairing`;
* `Γ^Gal(ℋom^•(I, K)) ≅ RΓ^Gal(X, ℋom(ℱ_M, μ_n))`
  (`AlgebraicGeometry.galoisHomOpECyclotomicDerivedIsoOfIsUnit`).

Here `K` is an injective resolution of `j_! μ_n` and the trace `Γ^Gal(K) ⟶ T` lifts the trace
`H²_c(X_k̄, μ_n) ⟶ ℚ/ℤ` of Tag 03VK (`AlgebraicGeometry.galoisHomOpCyclotomicTrace`).

## Hypotheses

Besides `#Λ` invertible in `k`, the isomorphism takes three inputs proved elsewhere: the
elementwise effaceability of `P ↦ H^*(X_k̄, ℱ_P)` over `Λᵐᵒᵖ` and the coeffaceability of
`Tᵢ = H_c^{2-i}(X_k̄, -)` (both hold when `X_k̄` is not the projective line), and the base case of
the family theorem (`H²` of the pairing map is an isomorphism). The naturality in `M` of the
identification of `Γ^Gal(ℋom^•(I, K))` is
`AlgebraicGeometry.galoisHomOpECyclotomicDerivedIso_hom_naturality`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open Stacks.ContinuousCohomology Stacks.AbelianInternalHom

universe u

/-! ### Right derived functors on extensions of an object placed in degree zero -/

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C C' D : Type*} [Category* C] [Category* C'] [Category* D] [Abelian C] [Abelian C']
  [Abelian D] [HasDerivedCategory C'] [HasDerivedCategory D] [EnoughInjectives C']
  (E : C ⥤ C') [E.PreservesZeroMorphisms] (G : C' ⥤ D) [G.Additive]

/-- **`RG(E(A)[0]) ≅ G(I)`** for an injective resolution `I` of `E(A)[0]` supported in degrees
`≥ 0`, with `E(A)[0]` written as the image under `E` of `A` placed in degree zero, in the derived
category of `D`. -/
def rightDerivedFunctorPlusMapSingleInjectiveIso (A : C)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor C' 0).obj (E.obj A)))
    [I.cocomplex.IsStrictlyGE 0] :
    DerivedCategory.Plus.ι.obj (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
        (E.mapCochainComplexPlus.obj ((Stacks.DerivedIndexing.singlePlusFunctor C 0).obj A)))) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cocomplex) :=
  DerivedCategory.Plus.ι.mapIso (G.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.Q.mapIso
      (Stacks.EtaleCohomology.mapCochainComplexPlusSinglePlusIso E A))) ≪≫
    (G.rightDerivedFunctorPlusSingleIsoOfAcyclic (E.obj A) I.cocomplex 0 I.ι
      (fun n => G.rightAcyclic_of_injective (I.cocomplex.X n))).symm

/-- A functor maps an equality of composites to an equality of composites. -/
private theorem map_comp_eq_map_comp {S T : Type*} [Category* S] [Category* T] (F : S ⥤ T)
    {A B B' Z : S} {f : A ⟶ B} {g : B ⟶ Z} {f' : A ⟶ B'} {g' : B' ⟶ Z} (h : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  simp only [← map_comp, h]

/-- **Naturality of `RG(E(A)[0]) ≅ G(I)`** in `A`, for a morphism of resolutions lifting `E(a)`. -/
theorem rightDerivedFunctorPlusMapSingleInjectiveIso_hom_naturality {A A' : C} (a : A ⟶ A')
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor C' 0).obj (E.obj A)))
    (I' : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor C' 0).obj (E.obj A')))
    [I.cocomplex.IsStrictlyGE 0] [I'.cocomplex.IsStrictlyGE 0] (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.singleFunctor C' 0).map (E.map a) ≫ I'.ι) :
    DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
        (E.mapCochainComplexPlus.map ((Stacks.DerivedIndexing.singlePlusFunctor C 0).map a)))) ≫
      (rightDerivedFunctorPlusMapSingleInjectiveIso E G A' I').hom =
    (rightDerivedFunctorPlusMapSingleInjectiveIso E G A I).hom ≫
      DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have h₁ := Stacks.EtaleCohomology.mapCochainComplexPlusSinglePlusIso_hom_naturality E a
  have h₂ := G.rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality (E.map a) I.cocomplex
    I'.cocomplex 0 I.ι I'.ι (fun n => G.rightAcyclic_of_injective (I.cocomplex.X n))
    (fun n => G.rightAcyclic_of_injective (I'.cocomplex.X n)) φ hφ
  have h₃ : DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C' 0).map (E.map a))) ≫
      (G.rightDerivedFunctorPlusSingleIsoOfAcyclic (E.obj A') I'.cocomplex 0 I'.ι
        (fun n => G.rightAcyclic_of_injective (I'.cocomplex.X n))).inv =
      (G.rightDerivedFunctorPlusSingleIsoOfAcyclic (E.obj A) I.cocomplex 0 I.ι
        (fun n => G.rightAcyclic_of_injective (I.cocomplex.X n))).inv ≫
      DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact h₂.symm
  have h₄ : DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
        (E.mapCochainComplexPlus.map ((Stacks.DerivedIndexing.singlePlusFunctor C 0).map a)))) ≫
      DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
        (Stacks.EtaleCohomology.mapCochainComplexPlusSinglePlusIso E A').hom)) =
      DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
        (Stacks.EtaleCohomology.mapCochainComplexPlusSinglePlusIso E A).hom)) ≫
      DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C' 0).map (E.map a))) := by
    exact map_comp_eq_map_comp (DerivedCategory.Plus.Q ⋙ G.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι) h₁
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₄).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h₃).trans (Category.assoc _ _ _).symm)))

/-- A commutative square `g ≫ e'.hom = e.hom ≫ h` with isomorphisms `e`, `e'` gives, after a
contravariant functor followed by two functors, a commutative square with the inverses. -/
theorem map_op_comp_mapIso_symm_op_hom_of_comm {C₀ D₁ D₂ D₃ : Type*} [Category* C₀] [Category* D₁]
    [Category* D₂] [Category* D₃] (F₁ : C₀ᵒᵖ ⥤ D₁) (F₂ : D₁ ⥤ D₂) (F₃ : D₂ ⥤ D₃) {X Y X' Y' : C₀}
    (e : X ≅ Y) (e' : X' ≅ Y') (g : X ⟶ X') (h : Y ⟶ Y') (w : g ≫ e'.hom = e.hom ≫ h) :
    F₃.map (F₂.map (F₁.map g.op)) ≫ (F₃.mapIso (F₂.mapIso (F₁.mapIso e.symm.op))).hom =
      (F₃.mapIso (F₂.mapIso (F₁.mapIso e'.symm.op))).hom ≫ F₃.map (F₂.map (F₁.map h.op)) := by
  have key : e.inv ≫ g = h ≫ e'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, w]
  simp only [Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom, ← Functor.map_comp, ← op_comp, key]

end CategoryTheory.Functor

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the coefficient
universe `0`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisPoincareDuality
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Sheafification of presheaves of `Λ`-modules on the small étale site, pinned at `u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_galoisPoincareDuality (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- `#Λ` is invertible in an extension field of `k` when it is invertible in `k`. -/
theorem isUnit_natCard_of_isUnit_field {k : Type*} (K : Type*) [Field k] [Field K] [Algebra k K]
    (Λ : Type*) (hΛ : IsUnit ((Nat.card Λ : ℕ) : k)) : IsUnit ((Nat.card Λ : ℕ) : K) :=
  map_natCast (algebraMap k K) (Nat.card Λ) ▸ hΛ.map (algebraMap k K)

section Resolutions

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f))

/-- The chosen member of the Poincaré family at `M`: the chosen injective resolution of
`j_! ℱ_M`, extended by zero to a complex indexed by `ℤ`. -/
def poincareChosenIndex
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    PoincareIndex B X x Λ f j where
  M := M
  I := (injectiveResolution ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
    ((representationSheaf B X x Λ).obj M))).toCochainComplexResolution
  ge := inferInstance

variable {B X x Λ f j}

/-- The chosen lift of `π : N ⟶ M` to the chosen resolutions. -/
def poincareChosenLift
    {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (π : N ⟶ M) :
    (poincareChosenIndex B X x Λ f j N).I.cocomplex ⟶
      (poincareChosenIndex B X x Λ f j M).I.cocomplex :=
  (Stacks.DerivedIndexing.descHom ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
    ((representationSheaf B X x Λ).map π))).hom'

/-- The chosen lift of `π` lifts `j_! ℱ_π`. -/
theorem poincareChosenLift_comm
    {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (π : N ⟶ M) :
    (poincareChosenIndex B X x Λ f j N).I.ι ≫ poincareChosenLift π =
      (CochainComplex.singleFunctor _ 0).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
          ((representationSheaf B X x Λ).map π)) ≫ (poincareChosenIndex B X x Λ f j M).I.ι :=
  InjectiveResolution.Hom.ι'_comp_hom' _

end Resolutions

section Model

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (j : CompactificationOf (Over.mk f))
  (K : Type u) [Field K] [Algebra k K] [Algebra.IsSeparable k K]

/-- **`RΓ^Gal_c(X_k̄, ℱ_M) ≅ Γ^Gal(I_M)`** in the derived category of discrete Galois modules,
`I_M` the chosen injective resolution of `(j_! ℱ_M)[0]`. -/
def galoisCompactSupportChosenModelIso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    DerivedCategory.Plus.ι.obj ((galoisDerivedGlobalSections Λ (Over.mk j.toBase) K).obj
        (DerivedCategory.Plus.Q.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              ((representationSheaf.{u, 0} B X x Λ).obj M))))) ≅
      DerivedCategory.Q.obj (galoisHomOpA (Over.mk j.toBase) K
        (poincareChosenIndex B X x Λ f j M).I.cocomplex) :=
  haveI := (poincareChosenIndex B X x Λ f j M).ge
  Functor.rightDerivedFunctorPlusMapSingleInjectiveIso
    (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) (galoisGlobalSections Λ (Over.mk j.toBase) K)
    ((representationSheaf.{u, 0} B X x Λ).obj M)
    (poincareChosenIndex B X x Λ f j M).I

variable {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}

omit [IsCurve k f] [Smooth f] [GeometricallyConnected f] in
/-- `RΓ^Gal_c(X_k̄, ℱ_M) ≅ Γ^Gal(I_M)` is natural in `M`. -/
theorem galoisCompactSupportChosenModelIso_hom_naturality (π : N ⟶ M) :
    DerivedCategory.Plus.ι.map ((galoisDerivedGlobalSections Λ (Over.mk j.toBase) K).map
        (DerivedCategory.Plus.Q.map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf.{u, 0} B X x Λ).map π))))) ≫
      (galoisCompactSupportChosenModelIso B X x Λ f j K M).hom =
    (galoisCompactSupportChosenModelIso B X x Λ f j K N).hom ≫
      DerivedCategory.Q.map (((galoisGlobalSections Λ (Over.mk j.toBase) K).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (poincareChosenLift π)) :=
  have := (poincareChosenIndex B X x Λ f j M).ge
  have := (poincareChosenIndex B X x Λ f j N).ge
  Functor.rightDerivedFunctorPlusMapSingleInjectiveIso_hom_naturality
    (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) (galoisGlobalSections Λ (Over.mk j.toBase) K)
    ((representationSheaf.{u, 0} B X x Λ).map π)
    (poincareChosenIndex B X x Λ f j N).I (poincareChosenIndex B X x Λ f j M).I
    (poincareChosenLift π) (poincareChosenLift_comm π)

end Model

section Duality

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosed K] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K] [CompactSpace (K ≃ₐ[k] K)]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) (n : ℕ) [NeZero n]
  (j : CompactificationOf (Over.mk f))

/-- The chosen injective resolution of `(j_! ℱ_μ)[0]` over `ℤ/n`, `μ = μ_n(k̄)`. -/
def cyclotomicChosenResolution :
    letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
    ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
        ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f K y n)))) :=
  letI := connectedSpace_of_isCurve B X f
  (injectiveResolution _).toCochainComplexResolution

/-- The chosen injective resolution `cyclotomicChosenResolution` is concentrated in degrees
`≥ 0`. -/
instance isStrictlyGE_cyclotomicChosenResolution :
    (cyclotomicChosenResolution B X f K y n j).cocomplex.IsStrictlyGE 0 :=
  letI := connectedSpace_of_isCurve B X f
  inferInstanceAs ((injectiveResolution _).toCochainComplexResolution.cocomplex.IsStrictlyGE 0)

variable (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
          ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f K y n)))))

/-- The chosen lift `Γ^Gal(K) ⟶ T` of the trace `H²(Γ^Gal(K)) ⟶ ℚ/ℤ`
(`AlgebraicGeometry.galoisHomOpCyclotomicTrace`). -/
def cyclotomicChosenTraceLift (hn : IsUnit ((n : ℕ) : K)) :
    (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ
        (K ≃ₐ[k] K)) ℤ from
        galoisHomOpG (Over.mk j.toBase) K (cyclotomicIntResolution B X f K y n j K₀)) ⟶
            traceTarget.{u, u + 1} (K ≃ₐ[k] K) 2 :=
  (exists_traceLift.{u, u + 1} (K ≃ₐ[k] K) (show CochainComplex
      (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
        galoisHomOpG (Over.mk j.toBase) K (cyclotomicIntResolution B X f K y n j K₀)) 2
    (@derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _ (show CochainComplex
        (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
        galoisHomOpG (Over.mk j.toBase) K (cyclotomicIntResolution B X f K y n j K₀)) 2
      (isLE_galoisHomOpG_cyclotomic B X f K y n j K₀)
      (galoisHomOpCyclotomicTrace B X f K y n j K₀ hn))).choose

/-- The chosen lift of the trace lifts the trace. -/
theorem cyclotomicChosenTraceLift_spec (hn : IsUnit ((n : ℕ) : K)) :
    DerivedCategory.Q.map (cyclotomicChosenTraceLift B X f K y n j K₀ hn) =
      @derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _ (show CochainComplex
          (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
        galoisHomOpG (Over.mk j.toBase) K (cyclotomicIntResolution B X f K y n j K₀)) 2
          (isLE_galoisHomOpG_cyclotomic B X f K y n j K₀)
          (galoisHomOpCyclotomicTrace B X f K y n j K₀ hn) ≫
        (@DerivedCategory.Q (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K))
          _ _ (HasDerivedCategory.standard _)).map (traceTargetι.{u, u + 1} (K ≃ₐ[k] K) 2) :=
  (exists_traceLift.{u, u + 1} (K ≃ₐ[k] K) (show CochainComplex
      (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
        galoisHomOpG (Over.mk j.toBase) K (cyclotomicIntResolution B X f K y n j K₀)) 2
    (@derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _ (show CochainComplex
        (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
        galoisHomOpG (Over.mk j.toBase) K (cyclotomicIntResolution B X f K y n j K₀)) 2
      (isLE_galoisHomOpG_cyclotomic B X f K y n j K₀)
      (galoisHomOpCyclotomicTrace B X f K y n j K₀ hn))).choose_spec

variable (Λ : Type) [Ring Λ] [Finite Λ] [Algebra (ZMod n) Λ] [ConnectedSpace X.1]
  [K₀.cocomplex.IsStrictlyGE 0] (hn : IsUnit ((n : ℕ) : K))
  (t : galoisHomOpG (Over.mk j.toBase) K (cyclotomicIntResolution B X f K y n j K₀) ⟶
    traceTarget.{u, u + 1} (K ≃ₐ[k] K) 2)

/-- **The derived Poincaré duality at `M`**, for a trace lift `t` whose pairings are
quasi-isomorphisms: `RΓ^Gal_c(X_k̄, ℱ_M) ≅ Γ^Gal(I_M) ≅ (E_M)^∨[-2] ≅
(RΓ^Gal(X, ℋom(ℱ_M, μ_n)))^∨[-2]`. -/
def galoisPoincareDualityComponentIso
    (hqi : ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
      QuasiIso (internalHomComplexOfPairing
        (poincarePairing K (cyclotomicIntResolution B X f K y n j K₀) t i)))
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    (discreteToCompletedGroupAlgebra.{0, u, u + 1} Λ (K ≃ₐ[k] K)).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj ((galoisDerivedGlobalSections Λ (Over.mk j.toBase) K).obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                ((representationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K
                  (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj M)))))) ≅
      ((pairingRestrict.{u, u + 1} Λᵐᵒᵖ (RingEquiv.opOp Λ).toRingHom
          (Q := K ≃ₐ[k] K)).mapDerivedCategory.obj
        ((derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K)).obj
          (op ((DerivedCategory.Plus.singleFunctor _ 0 ⋙
            galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) K ⋙ DerivedCategory.Plus.ι).obj
              ((etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f K
                (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ n
                  (cyclotomicContinuousModule B X f K y n)).obj (op M))))))⟦(-2 : ℤ)⟧ :=
  haveI := hqi (poincareChosenIndex B X _ Λ f j M)
  haveI := isIso_derivedPairing (2 : ℤ) _
    (poincarePairing K (cyclotomicIntResolution B X f K y n j K₀) t
      (poincareChosenIndex B X _ Λ f j M))
  (discreteToCompletedGroupAlgebra.{0, u, u + 1} Λ (K ≃ₐ[k] K)).mapDerivedCategory.mapIso
      (galoisCompactSupportChosenModelIso B X _ Λ f j K M) ≪≫
    asIso (derivedPairing (2 : ℤ) _
      (poincarePairing K (cyclotomicIntResolution B X f K y n j K₀) t
        (poincareChosenIndex B X _ Λ f j M))) ≪≫
    (shiftFunctor _ (-2 : ℤ)).mapIso
      ((pairingRestrict.{u, u + 1} Λᵐᵒᵖ (RingEquiv.opOp Λ).toRingHom
          (Q := K ≃ₐ[k] K)).mapDerivedCategory.mapIso
        ((derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K)).mapIso
          (galoisHomOpECyclotomicDerivedIso B X f K y n j K₀ Λ M
            (poincareChosenIndex B X _ Λ f j M).I
            (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X
                _ n Λ M)
            (isLocallyConstantInjective_representationSheaf_cyclotomic B X f K y n hn)).symm.op))

omit [Algebra (ZMod n) Λ] [K₀.cocomplex.IsStrictlyGE 0] in
/-- The square of the derived pairings for the chosen lift of `π : N ⟶ M`. -/
theorem galoisPoincareDerivedPairing_naturality {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1}
    Λ (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K
    (contains_fieldBaseChange_of_isCurve B X f K)).hom))} (π : N ⟶ M) :
    (discreteToCompletedGroupAlgebra.{0, u, u + 1} Λ (K ≃ₐ[k] K)).mapDerivedCategory.map
        (DerivedCategory.Q.map (((galoisGlobalSections Λ (Over.mk j.toBase) K).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (poincareChosenLift (B := B) (X := X) (x :=
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))
        (Λ := Λ) (f := f) (j := j) π))) ≫
        derivedPairing (2 : ℤ) _ (poincarePairing K (cyclotomicIntResolution B X f K y n j K₀) t
            (poincareChosenIndex B X (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j M)) =
      derivedPairing (2 : ℤ) _ (poincarePairing K (cyclotomicIntResolution B X f K y n j K₀) t
          (poincareChosenIndex B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j N)) ≫
        ((pairingRestrict.{u, u + 1} Λᵐᵒᵖ (RingEquiv.opOp Λ).toRingHom
            (Q := K ≃ₐ[k] K)).mapDerivedCategory.map
            ((derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K)).map (DerivedCategory.Q.map
          (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) K).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            (homOpComplexPrecomp (M := etaleHomOpTarget (Over.mk j.toBase)
                (cyclotomicIntResolution B X f K y n j K₀)) (poincareChosenLift (B := B) (X := X)
                (x := (y.map (fieldBaseChangeObjProj B X f K
                (contains_fieldBaseChange_of_isCurve B X f K)).hom)) (Λ := Λ) (f := f) (j := j)
                π)))).op))⟦(-2 : ℤ)⟧' :=
  derivedPairing_naturality (2 : ℤ) (poincarePairing K (cyclotomicIntResolution B X f K y n j K₀) t
      (poincareChosenIndex B X (y.map (fieldBaseChangeObjProj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j N)) (poincarePairing K
      (cyclotomicIntResolution B X f K y n j K₀) t (poincareChosenIndex B X (y.map
      (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j M))
    (((galoisGlobalSections Λ (Over.mk j.toBase) K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (poincareChosenLift (B := B) (X := X) (x :=
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))
        (Λ := Λ) (f := f) (j := j) π))
    (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) K).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
      (homOpComplexPrecomp (M := etaleHomOpTarget (Over.mk j.toBase)
          (cyclotomicIntResolution B X f K y n j K₀)) (poincareChosenLift (B := B) (X := X) (x :=
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) (Λ := Λ) (f := f) (j := j) π)))
    (poincarePairing_precomp K (cyclotomicIntResolution B X f K y n j K₀) t (poincareChosenIndex B X
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ
        f j M) (poincareChosenIndex B X (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j N) (poincareChosenLift (B := B)
        (X := X) (x := (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom)) (Λ := Λ) (f := f) (j := j) π))

/-- The square of the identifications `E_M ≅ RΓ^Gal(X, ℋom(ℱ_M, μ_n))`, dualized and shifted, for
the chosen lift of `π : N ⟶ M`, from the naturality of the identification. -/
theorem galoisPoincareDualityTarget_naturality
    {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map
        (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))} (π : N ⟶ M) :
    ((pairingRestrict.{u, u + 1} Λᵐᵒᵖ (RingEquiv.opOp Λ).toRingHom
        (Q := K ≃ₐ[k] K)).mapDerivedCategory.map
        ((derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K)).map (DerivedCategory.Q.map
          (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) K).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            (homOpComplexPrecomp (M := etaleHomOpTarget (Over.mk j.toBase)
                (cyclotomicIntResolution B X f K y n j K₀)) (poincareChosenLift (B := B) (X := X)
                (x := (y.map (fieldBaseChangeObjProj B X f K
                (contains_fieldBaseChange_of_isCurve B X f K)).hom)) (Λ := Λ) (f := f) (j := j)
                π)))).op))⟦(-2 : ℤ)⟧' ≫
        ((shiftFunctor _ (-2 : ℤ)).mapIso ((pairingRestrict.{u, u + 1} Λᵐᵒᵖ
            (RingEquiv.opOp Λ).toRingHom (Q := K ≃ₐ[k] K)).mapDerivedCategory.mapIso
          ((derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K)).mapIso
              (galoisHomOpECyclotomicDerivedIso B X f K y n j K₀ Λ M
            (poincareChosenIndex B X _ Λ f j M).I
            (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X
                _ n Λ M)
            (isLocallyConstantInjective_representationSheaf_cyclotomic B X f K y n
                hn)).symm.op))).hom =
      ((shiftFunctor _ (-2 : ℤ)).mapIso ((pairingRestrict.{u, u + 1} Λᵐᵒᵖ
          (RingEquiv.opOp Λ).toRingHom (Q := K ≃ₐ[k] K)).mapDerivedCategory.mapIso
          ((derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K)).mapIso
              (galoisHomOpECyclotomicDerivedIso B X f K y n j K₀ Λ N
            (poincareChosenIndex B X _ Λ f j N).I
            (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X
                _ n Λ N)
            (isLocallyConstantInjective_representationSheaf_cyclotomic B X f K y n
                hn)).symm.op))).hom ≫
        ((pairingRestrict.{u, u + 1} Λᵐᵒᵖ (RingEquiv.opOp Λ).toRingHom
            (Q := K ≃ₐ[k] K)).mapDerivedCategory.map
            ((derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K)).map
            ((DerivedCategory.Plus.singleFunctor _ 0 ⋙
            galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) K ⋙
            DerivedCategory.Plus.ι).map ((etaleHomOpRepresentationFunctor B X (y.map
            (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ n
            (cyclotomicContinuousModule B X f K y n)).map π.op)).op))⟦(-2 : ℤ)⟧' :=
  Functor.map_op_comp_mapIso_symm_op_hom_of_comm _ _ _
    (galoisHomOpECyclotomicDerivedIso B X f K y n j K₀ Λ M
      (poincareChosenIndex B X _ Λ f j M).I
      (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X _ n Λ
          M)
      (isLocallyConstantInjective_representationSheaf_cyclotomic B X f K y n hn))
    (galoisHomOpECyclotomicDerivedIso B X f K y n j K₀ Λ N
      (poincareChosenIndex B X _ Λ f j N).I
      (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X _ n Λ
          N)
      (isLocallyConstantInjective_representationSheaf_cyclotomic B X f K y n hn)) _ _
    (galoisHomOpECyclotomicDerivedIso_hom_naturality B X f K y n j K₀ Λ π
      (poincareChosenIndex B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j M).I (poincareChosenIndex B X
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j N).I
      (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X _ n Λ
          M)
      (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X _ n Λ
          N)
      (isLocallyConstantInjective_representationSheaf_cyclotomic B X f K y n hn)
      (poincareChosenLift (B := B) (X := X) (x :=
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) (Λ := Λ) (f := f) (j := j) π)
          (poincareChosenLift_comm π))

/-- **Naturality of the derived Poincaré duality at `M`** in `M`. -/
theorem galoisPoincareDualityComponentIso_hom_naturality
    (hqi : ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
      QuasiIso (internalHomComplexOfPairing (poincarePairing K
          (cyclotomicIntResolution B X f K y n j K₀) t i)))
    {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map
        (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))} (π : N ⟶ M) :
    (discreteToCompletedGroupAlgebra.{0, u, u + 1} Λ (K ≃ₐ[k] K)).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map ((galoisDerivedGlobalSections Λ (Over.mk j.toBase) K).map
        (DerivedCategory.Plus.Q.map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
            ((representationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K
                (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).map π)))))) ≫
      (galoisPoincareDualityComponentIso B X f K y n j K₀ Λ hn t hqi M).hom =
    (galoisPoincareDualityComponentIso B X f K y n j K₀ Λ hn t hqi N).hom ≫
      ((pairingRestrict.{u, u + 1} Λᵐᵒᵖ (RingEquiv.opOp Λ).toRingHom
          (Q := K ≃ₐ[k] K)).mapDerivedCategory.map
          ((derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K)).map
          ((DerivedCategory.Plus.singleFunctor _ 0 ⋙
          galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) K ⋙
          DerivedCategory.Plus.ι).map ((etaleHomOpRepresentationFunctor B X (y.map
          (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ n
          (cyclotomicContinuousModule B X f K y n)).map π.op)).op))⟦(-2 : ℤ)⟧' := by
  have h₁ := Functor.map_comp_eq_map_comp
    (discreteToCompletedGroupAlgebra.{0, u, u + 1} Λ (K ≃ₐ[k] K)).mapDerivedCategory
    (galoisCompactSupportChosenModelIso_hom_naturality B X (y.map (fieldBaseChangeObjProj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j K π)
  have h₂ := galoisPoincareDerivedPairing_naturality B X f K y n j K₀ Λ t π
  have h₃ := galoisPoincareDualityTarget_naturality B X f K y n j K₀ Λ hn π
  exact ((CommSq.mk h₁).vert_comp ((CommSq.mk h₂).vert_comp (CommSq.mk h₃))).w

end Duality

section Bridge

variable (Λ : Type) [Ring Λ] [Finite Λ] (Q : Type u) [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]

/-- Restriction of scalars along `mapCoeff (Λ ≅ Λᵐᵒᵖᵐᵒᵖ)`, written as `pairingRestrict` or through
`completedGroupAlgebraOpOp`, on derived categories: the two are the same functor. -/
def pairingRestrictMapDerivedCategoryIso :
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := Q))
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := Q))
    (pairingRestrict.{u, u + 1} Λᵐᵒᵖ (RingEquiv.opOp Λ).toRingHom (Q := Q)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{u + 1}
          (completedGroupAlgebraOpOp Λ (Q := Q))).mapDerivedCategory :=
  Iso.refl _

end Bridge

section PoincareDuality

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] [Algebra.IsSeparable k K]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) (Λ : Type) [Ring Λ] [Finite Λ]
  (j : CompactificationOf (Over.mk f))

/-- **The family of Poincaré pairings of Tag 03VM is a family of quasi-isomorphisms**, at the
chosen resolution `K` of `j_! μ_n` and the chosen lift of the trace. -/
theorem quasiIso_poincarePairing_cyclotomicChosen (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hEff : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      (geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λᵐᵒᵖ f K).ElementwiseEffaceable)
    (hcoeff : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      (compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j K).Coeffaceable)
    (hbase : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      ∀ (K₀ : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero (ZMod (Nat.card Λ)) j.immersion).obj
              ((representationSheaf B X _ (ZMod (Nat.card Λ))).obj
                  (cyclotomicContinuousModule B X f K y (Nat.card Λ))))))
                  [K₀.cocomplex.IsStrictlyGE 0]
        (t : (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ
            (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) ⟶
                traceTarget.{u, u + 1} (K ≃ₐ[k] K) 2),
        DerivedCategory.Q.map t =
          @derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _ (show CochainComplex
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) 2
            (isLE_galoisHomOpG_cyclotomic B X f K y (Nat.card Λ) j K₀)
            (galoisHomOpCyclotomicTrace B X f K y (Nat.card Λ) j K₀
                (isUnit_natCard_of_isUnit_field K Λ hΛ)) ≫
          (@DerivedCategory.Q
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K))
            _ _ (HasDerivedCategory.standard _)).map (traceTargetι.{u, u + 1} (K ≃ₐ[k] K) 2) →
        ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
          IsIso (HomologicalComplex.homologyMap
            (internalHomComplexOfPairing (poincarePairing K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀) t i)) 2)) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
    letI := zmodNatCardAlgebra Λ
    ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
      QuasiIso (internalHomComplexOfPairing (poincarePairing K (cyclotomicIntResolution B X f K y
          (Nat.card Λ) j (cyclotomicChosenResolution B X f K y (Nat.card Λ) j))
          (cyclotomicChosenTraceLift B X f K y (Nat.card Λ) j
          (cyclotomicChosenResolution B X f K y (Nat.card Λ) j)
          (isUnit_natCard_of_isUnit_field K Λ hΛ)) i)) :=
  let := connectedSpace_of_isCurve B X f
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
  let := zmodNatCardAlgebra Λ
  fun i =>
    quasiIso_poincarePairing K (cyclotomicIntResolution B X f K y (Nat.card Λ) j
        (cyclotomicChosenResolution B X f K y (Nat.card Λ) j)) (cyclotomicChosenTraceLift B X f K y
        (Nat.card Λ) j (cyclotomicChosenResolution B X f K y (Nat.card Λ) j)
        (isUnit_natCard_of_isUnit_field K Λ hΛ)) hcoeff
      (hbase (cyclotomicChosenResolution B X f K y (Nat.card Λ) j) (cyclotomicChosenTraceLift B X f
          K y (Nat.card Λ) j (cyclotomicChosenResolution B X f K y (Nat.card Λ) j)
          (isUnit_natCard_of_isUnit_field K Λ hΛ)) (cyclotomicChosenTraceLift_spec B X f K y
          (Nat.card Λ) j (cyclotomicChosenResolution B X f K y (Nat.card Λ) j)
          (isUnit_natCard_of_isUnit_field K Λ hΛ)))
      (fun i q hq => isZero_homology_galoisHomOpE_cyclotomic_of_isUnit B X f K y (Nat.card Λ) j
          (cyclotomicChosenResolution B X f K y (Nat.card Λ) j) Λ
          (isUnit_natCard_of_isUnit_field K Λ hΛ) _
        i.M i.I q hq)
      (fun (m : ℕ) (hm : 1 ≤ m) (_ : m ≤ 2) N =>
        galoisHomOpE_coeffacement B X f K y (Nat.card Λ) j
            (cyclotomicChosenResolution B X f K y (Nat.card Λ) j) Λ rfl hΛ hEff
          (fun M =>
              isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf
            B X _ (Nat.card Λ) Λ M)
          (isLocallyConstantInjective_representationSheaf_cyclotomic B X f K y (Nat.card Λ)
              (isUnit_natCard_of_isUnit_field K Λ hΛ))
          (fun _ _ π IM IN φ hφ => galoisHomOpECyclotomicDerivedIso_hom_naturality B X f K
              y (Nat.card Λ) j
            (cyclotomicChosenResolution B X f K y (Nat.card Λ) j) Λ π IM IN
            (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X
                _ (Nat.card Λ) Λ _)
            (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X
                _ (Nat.card Λ) Λ _)
            (isLocallyConstantInjective_representationSheaf_cyclotomic B X f K y (Nat.card Λ)
                (isUnit_natCard_of_isUnit_field K Λ hΛ)) φ hφ)
          m hm N) i

/-- The derived Poincaré duality at `M`, between the two sides as written in
`AlgebraicGeometry.geometricGaloisCompactSupportDerived` and
`AlgebraicGeometry.geometricGaloisDualCohomology`. -/
def galoisCompactSupportPoincareDualityComponent (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hqi : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
        QuasiIso (internalHomComplexOfPairing (poincarePairing K (cyclotomicIntResolution B X f K y
            (Nat.card Λ) j (cyclotomicChosenResolution B X f K y (Nat.card Λ) j))
            (cyclotomicChosenTraceLift B X f K y (Nat.card Λ) j
            (cyclotomicChosenResolution B X f K y (Nat.card Λ) j)
            (isUnit_natCard_of_isUnit_field K Λ hΛ)) i)))
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map
          (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
    letI := zmodNatCardAlgebra Λ
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    (geometricGaloisCompactSupportDerived B X f K y Λ j).obj M ≅
        (geometricGaloisDualCohomology B X f K y Λ ⋙ shiftFunctor _ (-2 : ℤ)).obj M :=
  letI := connectedSpace_of_isCurve B X f
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
  letI := zmodNatCardAlgebra Λ
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
  galoisPoincareDualityComponentIso B X f K y (Nat.card Λ) j
      (cyclotomicChosenResolution B X f K y (Nat.card Λ) j) Λ
      (isUnit_natCard_of_isUnit_field K Λ hΛ) (cyclotomicChosenTraceLift B X f K y (Nat.card Λ) j
      (cyclotomicChosenResolution B X f K y (Nat.card Λ) j)
      (isUnit_natCard_of_isUnit_field K Λ hΛ)) hqi M ≪≫
    (shiftFunctor _ (-2 : ℤ)).mapIso ((pairingRestrictMapDerivedCategoryIso Λ (K ≃ₐ[k] K)).app _)

/-- Naturality of `AlgebraicGeometry.galoisCompactSupportPoincareDualityComponent`. -/
theorem galoisCompactSupportPoincareDualityComponent_hom_naturality
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hqi : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
        QuasiIso (internalHomComplexOfPairing (poincarePairing K (cyclotomicIntResolution B X f K y
            (Nat.card Λ) j (cyclotomicChosenResolution B X f K y (Nat.card Λ) j))
            (cyclotomicChosenTraceLift B X f K y (Nat.card Λ) j
            (cyclotomicChosenResolution B X f K y (Nat.card Λ) j)
            (isUnit_natCard_of_isUnit_field K Λ hΛ)) i)))
    {M N : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map
          (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))} (π : N ⟶ M) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
    letI := zmodNatCardAlgebra Λ
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    (geometricGaloisCompactSupportDerived B X f K y Λ j).map π ≫
        (galoisCompactSupportPoincareDualityComponent B X f K y Λ j hΛ hqi M).hom =
    (galoisCompactSupportPoincareDualityComponent B X f K y Λ j hΛ hqi N).hom ≫
        (geometricGaloisDualCohomology B X f K y Λ ⋙ shiftFunctor _ (-2 : ℤ)).map π :=
  let := connectedSpace_of_isCurve B X f
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
  let := zmodNatCardAlgebra Λ
  have := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
  have := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (galoisPoincareDualityComponentIso_hom_naturality B X f K y (Nat.card Λ) j
        (cyclotomicChosenResolution B X f K y (Nat.card Λ) j) Λ
        (isUnit_natCard_of_isUnit_field K Λ hΛ) (cyclotomicChosenTraceLift B X f K y (Nat.card Λ) j
        (cyclotomicChosenResolution B X f K y (Nat.card Λ) j)
        (isUnit_natCard_of_isUnit_field K Λ hΛ))
      hqi π)).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (Functor.map_comp_eq_map_comp (shiftFunctor _ (-2 : ℤ))
      ((pairingRestrictMapDerivedCategoryIso Λ (K ≃ₐ[k] K)).hom.naturality _))).trans
      (Category.assoc _ _ _).symm

/-- The components of `AlgebraicGeometry.galoisCompactSupportPoincareDualityNatIso`. -/
def galoisCompactSupportPoincareDualityApp (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hEff : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      (geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λᵐᵒᵖ f K).ElementwiseEffaceable)
    (hcoeff : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      (compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j K).Coeffaceable)
    (hbase : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      ∀ (K₀ : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero (ZMod (Nat.card Λ)) j.immersion).obj
              ((representationSheaf B X _ (ZMod (Nat.card Λ))).obj
                  (cyclotomicContinuousModule B X f K y (Nat.card Λ))))))
                  [K₀.cocomplex.IsStrictlyGE 0]
        (t : (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ
            (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) ⟶
                traceTarget.{u, u + 1} (K ≃ₐ[k] K) 2),
        DerivedCategory.Q.map t =
          @derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _ (show CochainComplex
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) 2
            (isLE_galoisHomOpG_cyclotomic B X f K y (Nat.card Λ) j K₀)
            (galoisHomOpCyclotomicTrace B X f K y (Nat.card Λ) j K₀
                (isUnit_natCard_of_isUnit_field K Λ hΛ)) ≫
          (@DerivedCategory.Q
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K))
            _ _ (HasDerivedCategory.standard _)).map (traceTargetι.{u, u + 1} (K ≃ₐ[k] K) 2) →
        ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
          IsIso (HomologicalComplex.homologyMap
            (internalHomComplexOfPairing (poincarePairing K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀) t i)) 2))
 (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map
          (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
    letI := zmodNatCardAlgebra Λ
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    (geometricGaloisCompactSupportDerived B X f K y Λ j).obj M ≅
        (geometricGaloisDualCohomology B X f K y Λ ⋙ shiftFunctor _ (-2 : ℤ)).obj M :=
  galoisCompactSupportPoincareDualityComponent B X f K y Λ j hΛ
      (quasiIso_poincarePairing_cyclotomicChosen B X f K y Λ j hΛ hEff hcoeff hbase) M

/-- The naturality of `AlgebraicGeometry.galoisCompactSupportPoincareDualityApp`. -/
theorem galoisCompactSupportPoincareDualityApp_naturality (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hEff : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      (geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λᵐᵒᵖ f K).ElementwiseEffaceable)
    (hcoeff : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      (compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j K).Coeffaceable)
    (hbase : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      ∀ (K₀ : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero (ZMod (Nat.card Λ)) j.immersion).obj
              ((representationSheaf B X _ (ZMod (Nat.card Λ))).obj
                  (cyclotomicContinuousModule B X f K y (Nat.card Λ))))))
                  [K₀.cocomplex.IsStrictlyGE 0]
        (t : (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ
            (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) ⟶
                traceTarget.{u, u + 1} (K ≃ₐ[k] K) 2),
        DerivedCategory.Q.map t =
          @derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _ (show CochainComplex
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) 2
            (isLE_galoisHomOpG_cyclotomic B X f K y (Nat.card Λ) j K₀)
            (galoisHomOpCyclotomicTrace B X f K y (Nat.card Λ) j K₀
                (isUnit_natCard_of_isUnit_field K Λ hΛ)) ≫
          (@DerivedCategory.Q
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K))
            _ _ (HasDerivedCategory.standard _)).map (traceTargetι.{u, u + 1} (K ≃ₐ[k] K) 2) →
        ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
          IsIso (HomologicalComplex.homologyMap
            (internalHomComplexOfPairing (poincarePairing K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀) t i)) 2))
    {M N : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map
          (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))} (π : N ⟶ M) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
    letI := zmodNatCardAlgebra Λ
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    (geometricGaloisCompactSupportDerived B X f K y Λ j).map π ≫
        (galoisCompactSupportPoincareDualityApp B X f K y Λ j hΛ hEff hcoeff hbase M).hom =
      (galoisCompactSupportPoincareDualityApp B X f K y Λ j hΛ hEff hcoeff hbase N).hom ≫
          (geometricGaloisDualCohomology B X f K y Λ ⋙ shiftFunctor _ (-2 : ℤ)).map π :=
  galoisCompactSupportPoincareDualityComponent_hom_naturality B X f K y Λ j hΛ
      (quasiIso_poincarePairing_cyclotomicChosen B X f K y Λ j hΛ hEff hcoeff hbase) π

/-- **The derived Poincaré duality of Tag 03VM**:
`RΓ^Gal_c(X_k̄, ℱ_M) ≅ (RΓ^Gal(X_k̄, ℋom(ℱ_M, μ_n)))^∨[-2]` in the derived category of
`Λ[[Aut(k̄/k)]]`-modules, naturally in the finite `Λ`-module `M` with continuous
`π₁(X, x̄)`-action, `n = #Λ` invertible in `k`.

It is built from the elementwise effaceability `hEff` of `P ↦ H^*(X_k̄, ℱ_P)` over `Λᵐᵒᵖ`, the
coeffaceability `hcoeff` of `Tᵢ = H_c^{2-i}(X_k̄, -)` and the base case `hbase` (`H²` of the
Poincaré pairing map is an isomorphism, for every trace lift). -/
def galoisCompactSupportPoincareDualityNatIso (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hEff : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      (geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λᵐᵒᵖ f K).ElementwiseEffaceable)
    (hcoeff : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      (compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j K).Coeffaceable)
    (hbase : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      ∀ (K₀ : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero (ZMod (Nat.card Λ)) j.immersion).obj
              ((representationSheaf B X _ (ZMod (Nat.card Λ))).obj
                  (cyclotomicContinuousModule B X f K y (Nat.card Λ))))))
                  [K₀.cocomplex.IsStrictlyGE 0]
        (t : (show CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ
            (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) ⟶
                traceTarget.{u, u + 1} (K ≃ₐ[k] K) 2),
        DerivedCategory.Q.map t =
          @derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _ (show CochainComplex
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) 2
            (isLE_galoisHomOpG_cyclotomic B X f K y (Nat.card Λ) j K₀)
            (galoisHomOpCyclotomicTrace B X f K y (Nat.card Λ) j K₀
                (isUnit_natCard_of_isUnit_field K Λ hΛ)) ≫
          (@DerivedCategory.Q
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K))
            _ _ (HasDerivedCategory.standard _)).map (traceTargetι.{u, u + 1} (K ≃ₐ[k] K) 2) →
        ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
          IsIso (HomologicalComplex.homologyMap
            (internalHomComplexOfPairing (poincarePairing K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀) t i)) 2)) :
    geometricGaloisCompactSupportDerived B X f K y Λ j ≅
      geometricGaloisDualCohomology B X f K y Λ ⋙ shiftFunctor _ (-2 : ℤ) :=
  NatIso.ofComponents (galoisCompactSupportPoincareDualityApp B X f K y Λ j hΛ hEff hcoeff hbase)
    (galoisCompactSupportPoincareDualityApp_naturality B X f K y Λ j hΛ hEff hcoeff hbase)

end PoincareDuality

end AlgebraicGeometry

end
