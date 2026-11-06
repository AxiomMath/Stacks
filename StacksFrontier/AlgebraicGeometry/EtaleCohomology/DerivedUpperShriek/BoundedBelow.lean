module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.UnboundedAdjoint
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Derived upper shriek preserves bounded below objects

Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes and let `Λ` be a torsion ring. The right adjoint `Rf^!` of
`Rf_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` ([Stacks, Tag 0G2C]) sends `D^+(Y_étale, Λ)` into
`D^+(X_étale, Λ)`: there is `N ≥ 0` such that `H^i(K) = 0` for `i < a` implies
`H^i(Rf^!K) = 0` for `i < a - N`, [Stacks, Tag 0GLA].

## Main results

* `Stacks.EtaleCohomology.DerivedUpperShriek.isGE_obj_of_adjunction`: a right adjoint of a
  functor of bounded upper amplitude has bounded lower amplitude.
* `Stacks.EtaleCohomology.DerivedUpperShriek.isLE_obj_of_isZero_rightDerived`: [Stacks, Tag 07K7]
  part (4)(c), upper bound, for an arbitrary unbounded right derived functor.
* `Stacks.EtaleCohomology.DerivedUpperShriek.isLE_derivedLowerShriekUnbounded_obj`: the upper
  amplitude of `Rf_!`, given the vanishing of the higher direct images along `fbar`.
* `Stacks.EtaleCohomology.DerivedUpperShriek.isGE_obj_of_derivedLowerShriekUnbounded_adjunction`:
  the bound for any right adjoint of `Rf_!`, given that vanishing.

## References

* [Stacks Project, Tag 0GLA](https://stacks.math.columbia.edu/tag/0GLA)
* [Stacks Project, Tag 0G2A](https://stacks.math.columbia.edu/tag/0G2A)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace Stacks.EtaleCohomology.DerivedUpperShriek

section Adjunction

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  {F : DerivedCategory A ⥤ DerivedCategory B} {G : DerivedCategory B ⥤ DerivedCategory A}

/-- **A right adjoint of a functor of bounded upper amplitude has bounded lower amplitude.** If
`F ⊣ G` and `F` sends objects living in degrees `≤ c` to objects living in degrees `≤ c + N`,
then `G` sends objects living in degrees `≥ a` to objects living in degrees `≥ a - N`. -/
theorem isGE_obj_of_adjunction [F.Additive] (adj : F ⊣ G) (N : ℤ)
    (hF : ∀ (L : DerivedCategory A) (c : ℤ), L.IsLE c → (F.obj L).IsLE (c + N))
    (K : DerivedCategory B) (a : ℤ) (hK : K.IsGE a) : (G.obj K).IsGE (a - N) := by
  refine (DerivedCategory.TStructure.t.isGE_iff_orthogonal (a - N - 1) (a - N) (by lia)
    (G.obj K)).2 fun Y g hY ↦ ?_
  have h : (adj.homEquiv Y K).symm g = 0 :=
    DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (a - N - 1 + N) a (by lia)
      (hF Y _ hY) hK
  rw [← (adj.homEquiv Y K).apply_symm_apply g, h, adj.homAddEquiv_zero]

end Adjunction

section Amplitude

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive]

/-- The complex `I[0]` of an injective object computes the right derived functor of `F` on
`K⁺(𝒜)`, in the sense of [Stacks, Tag 05SX]. -/
theorem computesRightDerived_singleFunctor_obj_of_injective (I : A) [Injective I] :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso A) ((HomotopyCategory.Plus.singleFunctor A 0).obj I) := by
  have hres (K : HomotopyCategory.Plus A) :
      ∃ (Y : HomotopyCategory.Plus A) (f : K ⟶ Y)
        (_ : HomotopyCategory.Plus.quasiIso A f),
        IsIso (F.rightDerivedFunctorPlusUnith.app Y) := by
    obtain ⟨a, ha⟩ := (HomotopyCategory.plus_quotient_obj_iff K.obj.as).1 K.property
    let P : ObjectProperty A := fun X ↦ Injective X
    have : P.ContainsZero := ⟨0, isZero_zero A, inferInstance⟩
    obtain ⟨L, f, hf, hL, _, hge⟩ := CochainComplex.exists_quasiIso_prop_isStrictlyGE P
      (fun X ↦ ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩) a K.obj.as
    let Y : HomotopyCategory.Plus A := (HomotopyCategory.Plus.quotient A).obj ⟨L, ⟨a, hge⟩⟩
    have (i : ℤ) : Injective (Y.obj.as.X i) := hL i
    exact ⟨Y, ObjectProperty.homMk ((HomotopyCategory.quotient A _).map f),
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf, inferInstance⟩
  have : (HomotopyCategory.Plus.quasiIso A).HasLeftCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  have : ∀ m : ℤ, Injective (((HomotopyCategory.Plus.singleFunctor A 0).obj I).obj.as.X m) :=
    fun m ↦ inferInstanceAs
      (Injective (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj I).X m))
  exact (Functor.computesRightDerived_iff_isIso_app
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    DerivedCategory.Plus.Qh F.rightDerivedFunctorPlus
    (HomotopyCategory.Plus.quasiIso A) F.rightDerivedFunctorPlusUnith
    ((HomotopyCategory.Plus.singleFunctor A 0).obj I) hres).2 inferInstance

/-- **Finite cohomological dimension bounds the amplitude of an unbounded right derived
functor**, [Stacks, Tag 07K7] part (4)(c), upper bound: if `R^n F = 0` then any right derived
functor `RF : D(𝒜) ⥤ D(ℬ)` of `F` carries an object living in degrees `≤ b` to one living in
degrees `≤ b + n - 1`. -/
theorem isLE_obj_of_isZero_rightDerived [PreservesFiniteLimits F] (n : ℕ)
    (hn : ∀ X : A, IsZero ((F.rightDerived n).obj X))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (E : DerivedCategory A) (b : ℤ) (hE : E.IsLE b) : (RF.obj E).IsLE (b + n - 1) :=
  (((Functor.hasRightDerivedFunctor_of_isZero_rightDerived F F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith
    (fun X ↦ (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso A) ((HomotopyCategory.Plus.singleFunctor A 0).obj X))
    (fun _ ↦ Iff.rfl)
    (fun X ↦ ⟨Injective.under X, Injective.ι X, inferInstance,
      computesRightDerived_singleFunctor_obj_of_injective F _⟩)
    n (fun X ↦ (hn X).of_iso ((Stacks.DerivedIndexing.rightDerivedIso F n).app X).symm)).2.2
    RF α).2 E).2.2.2 b hE

end Amplitude

section Etale

open _root_.AlgebraicGeometry Stacks.Injectives.KInjectiveResolution

attribute [local instance] HasDerivedCategory.standard

universe u r

variable (Λ : Type r) [Ring Λ]

/-- **The upper amplitude of the unbounded derived direct image.** If `R^n f_* F = 0` for every
sheaf of `Λ`-modules `F`, then `Rf_* : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` sends objects living in
degrees `≤ b` to objects living in degrees `≤ b + n - 1`. -/
theorem isLE_etaleModuleDerivedDirectImageUnbounded_obj {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (hn : ∀ F : EtaleModules.{u, r} Λ X,
      IsZero (((etaleModuleDirectImage.{u, r} Λ f).rightDerived n).obj F))
    (E : DerivedCategory (EtaleModules.{u, r} Λ X)) (b : ℤ) (hE : E.IsLE b) :
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj E).IsLE (b + n - 1) :=
  isLE_obj_of_isZero_rightDerived _ n hn _
    (homotopyCategoryUnit _ _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)) E b hE

/-- **Extension by zero preserves upper bounds.** For an étale `j : U ⟶ X`, the unbounded
`Rj_! : D(U_étale, Λ) ⟶ D(X_étale, Λ)` sends objects living in degrees `≤ b` to objects living in
degrees `≤ b`. -/
theorem isLE_etaleModuleDerivedExtensionByZeroUnbounded_obj {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (E : DerivedCategory (EtaleModules.{u, r} Λ U)) (b : ℤ) (hE : E.IsLE b) :
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).obj E).IsLE b := by
  have := Stacks.Homology.isLE_mapDerivedCategory_obj (etaleModuleExtensionByZero.{u, r} Λ j) E b
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).app E).symm b

/-- **The upper amplitude of the unbounded derived lower shriek**, the upper half of
[Stacks, Tag 0G2A] (3): if `R^n fbar_* F = 0` for every sheaf of `Λ`-modules `F` on `Xbar`, then
`Rf_! = R(fbar)_* ∘ j_!` sends objects living in degrees `≤ b` to objects living in degrees
`≤ b + n - 1`. -/
theorem isLE_derivedLowerShriekUnbounded_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (n : ℕ)
    (hn : ∀ F : EtaleModules.{u, r} Λ j.space,
      IsZero (((etaleModuleDirectImage.{u, r} Λ j.toBase).rightDerived n).obj F))
    (E : DerivedCategory (EtaleModules.{u, r} Λ X)) (b : ℤ) (hE : E.IsLE b) :
    ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj E).IsLE (b + n - 1) :=
  isLE_etaleModuleDerivedDirectImageUnbounded_obj Λ j.toBase n hn _ b
    (isLE_etaleModuleDerivedExtensionByZeroUnbounded_obj Λ j.immersion E b hE)

/-- The unbounded derived lower shriek is additive. -/
instance derivedLowerShriekUnbounded_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) :
    (derivedLowerShriekUnbounded.{u, r} f j Λ).Additive := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  have : (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).Additive :=
    Functor.additive_of_iso
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j.immersion).symm
  infer_instance

/-- **The bound of [Stacks, Tag 0GLA], for any right adjoint of `Rf_!`.** If
`R^n fbar_* F = 0` for every sheaf of `Λ`-modules `F` on `Xbar`, then any right adjoint `G` of
`Rf_! = R(fbar)_* ∘ j_!` sends objects living in degrees `≥ a` to objects living in degrees
`≥ a - (n - 1)`. -/
theorem isGE_obj_of_derivedLowerShriekUnbounded_adjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (n : ℕ)
    (hn : ∀ F : EtaleModules.{u, r} Λ j.space,
      IsZero (((etaleModuleDirectImage.{u, r} Λ j.toBase).rightDerived n).obj F))
    {G : DerivedCategory (EtaleModules.{u, r} Λ Y) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X)}
    (adj : derivedLowerShriekUnbounded.{u, r} f j Λ ⊣ G)
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) (a : ℤ) (hK : K.IsGE a) :
    (G.obj K).IsGE (a - (n - 1)) :=
  isGE_obj_of_adjunction adj (n - 1) (fun L c hL ↦ by
    simpa only [add_sub_assoc] using isLE_derivedLowerShriekUnbounded_obj Λ f j n hn L c hL) K a hK

end Etale

end Stacks.EtaleCohomology.DerivedUpperShriek
