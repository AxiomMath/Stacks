module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.Homology.TorAmplitude.NilpotentCertified
public import StacksFrontier.RingTheory.Flat.TorCriterion

/-!
# Lifting a module versus lifting it in the derived category

Let `A' → A` be a surjection of commutative rings with nilpotent kernel, let `P'` be a flat
`A'`-algebra and put `P = P' ⊗[A'] A`. An `A`-flat `P`-module `M` has a flat lift to a
`P'`-module if and only if it has a bounded-above derived lift, that is, an object of `D⁻(P')`
whose derived base change to `P` is isomorphic to `M` placed in degree zero.

One direction is immediate: a flat lift, placed in degree zero, is a derived lift, because
derived base change of a flat module agrees with ordinary base change. For the converse the
derived lift is replaced by the module `H⁰` of its base change: the Tor-independence of `P'`
and `A` over `A'` makes the comparison map from the derived base change to the ordinary one an
isomorphism in degree zero, and the nilpotence of the kernel promotes `A`-flatness of `M` to
`A'`-flatness of that module, which is then a flat lift.

## Main results

* `Deformation.Examples.DerivedLift.exists_flat_lift_iff_exists_derived_lift`: the two lifting
  problems have the same answer.

## Implementation notes

The derived lift is an object of `D⁻(P')` and its derived base change is the total derived
extension-of-scalars functor; agreement with `M` in the derived category is expressed by an
isomorphism to the complex having `M` in degree zero. The tensor product `P' ⊗[A'] A` carries
its usual left `P'`-algebra and right `A`-algebra structures, and the scalar-tower hypotheses
say that the displayed `A`- and `A'`-actions are the restrictions of the actions over `P` and
`P'`. Extension of scalars has carrier in universe `max u v`, so the comparison object is the
universe lift of `M`.

The structure field `TotalDerivedExtensionScalars.comparison` is typed by
`extensionOfScalarsComplexGeneral`, whereas the base-change comparison of
`RingTheory.TorIndependence.derivedBaseChangeComparison` expects the unfolded
`ModuleCat.extendScalars _ |>.mapHomologicalComplex _ ⋙ DerivedCategory.Q`. The two agree only
after unfolding `extensionOfScalarsComplexGeneral` and `extensionOfScalarsComplex`, so both are
made `implicit_reducible` locally; without that, instance search finds the
`IsLeftDerivedFunctor` hypothesis and then rejects it on the final conversion check.

## References

* [Stacks Project, Tag 0DZ1](https://stacks.math.columbia.edu/tag/0DZ1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible]
  CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral
  CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplex

universe u v

namespace Deformation.Examples.DerivedLift

open StacksDraft.TorAmplitude

private lemma torIndependent_of_flat
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Module.Flat R B] :
    RingTheory.TorIndependence.TorIndependent R B C := by
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
  intro p hp
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by lia⟩
  let P := ModuleCat.of R B
  let N := ModuleCat.of R C
  refine Limits.IsZero.of_iso ?_
    ((projectiveResolution N).isoLeftDerivedObj (tensorLeft P) (n + 1))
  have hexact : ((projectiveResolution N).complex.sc (n + 1)).Exact :=
    (HomologicalComplex.exactAt_iff _ _).mp ((projectiveResolution N).complex_exactAt_succ n)
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    ((HomologicalComplex.exactAt_iff _ _).mpr
      (hexact.map_of_preservesLeftHomologyOf (tensorLeft P)))

private lemma derivedBaseChange_iso
    {A' A P' P : Type u} [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
    [Algebra A' A] [Algebra A' P'] [Algebra P' P] [Algebra A P] [Algebra A' P]
    [IsScalarTower A' P' P] [IsScalarTower A' A P]
    [Algebra.IsPushout A' P' A P] [Module.Flat A' P']
    (K : DerivedCategory (ModuleCat.{max u v} P')) :
    Nonempty (((ModuleCat.restrictScalars (algebraMap A P)).mapDerivedCategory.obj
        ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
          (algebraMap P' P)).functor.obj K)) ≅
      (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
        (algebraMap A' A)).functor.obj
          ((ModuleCat.restrictScalars (algebraMap A' P')).mapDerivedCategory.obj K)) := by
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
    (algebraMap A' A)
  let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
    (algebraMap P' P)
  let f : A' →+* P' := algebraMap A' P'
  let g : A' →+* A := algebraMap A' A
  let h : P' →+* P := algebraMap P' P
  let i : A →+* P := algebraMap A P
  let sq : h.comp f = i.comp g :=
    (IsScalarTower.algebraMap_eq A' P' P).symm.trans
      (IsScalarTower.algebraMap_eq A' A P)
  have : Tg.functor.IsLeftDerivedFunctor Tg.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} A') (ComplexShape.up ℤ)) :=
    Tg.isLeftDerived
  have : Th.functor.IsLeftDerivedFunctor Th.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} P') (ComplexShape.up ℤ)) :=
    Th.isLeftDerived
  have hcomp := RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u,
      u, u, u, v, max u v + 1, max u v + 1, max u v + 1, max u v + 1}
    (R := A') (A := P') (R' := A) (A' := P)
    (torIndependent_of_flat (R := A') (B := P') (C := A))
    Tg.functor Th.functor Tg.comparison Th.comparison
  let cmp := (RingTheory.TorIndependence.derivedBaseChangeComparison.{u, u, u, u, v,
      max u v + 1, max u v + 1, max u v + 1, max u v + 1} f g h i sq
    Tg.functor Th.functor Tg.comparison Th.comparison).2.1
  have : IsIso cmp := hcomp
  exact ⟨(asIso (cmp.app K)).symm⟩

private lemma flat_of_subsingleton_module
    {R : Type u} [CommRing R] {N : Type (max u v)}
    [AddCommGroup N] [Module R N] (hN : Subsingleton N) : Module.Flat R N := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ f hf x y hxy
  exact Subsingleton.elim _ _

private noncomputable def restrictedDerivedHomologyIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (i : ℤ) :
    (ModuleCat.restrictScalars f).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max u v} S) i ⋙
        ModuleCat.restrictScalars f := by
  let F := ModuleCat.restrictScalars f
  let e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℤ) i ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{max u v} S) (ComplexShape.up ℤ) i ⋙ F :=
    NatIso.ofComponents (fun X => (X.sc i).mapHomologyIso F) (fun φ =>
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v} S)
          (ComplexShape.up ℤ) i).map φ) F)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} S) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor (ModuleCat.{max u v} S) i ⋙ F))
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i)
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} S) i ⋙ F)
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i) ≪≫ e ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors
        (ModuleCat.{max u v} S) i).symm F)

private lemma isIso_pushoutComparison_app
    {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B] [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    (τ : ModuleCat.restrictScalars.{max u v} (algebraMap R A) ⋙
        ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S) ⟶
      ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B) ⋙
        ModuleCat.restrictScalars.{max u v} (algebraMap S B))
    (hτ : ∀ (M : ModuleCat.{max u v} A) (s : S) (m : M),
      τ.app M (s ⊗ₜ[R,algebraMap R S] m) =
        (algebraMap S B s) ⊗ₜ[A,algebraMap A B] m)
    (M : ModuleCat.{max u v} A) : IsIso (τ.app M) := by
  let : Module R M := Module.compHom M (algebraMap R A)
  let : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eS : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { AddEquiv.refl S with
      map_smul' := fun r s ↦ (Algebra.smul_def (R := R) (A := S) r s).symm }
  let eB : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[A] B :=
    { AddEquiv.refl B with
      map_smul' := fun a b ↦ (Algebra.smul_def (R := A) (A := B) a b).symm }
  let u := TensorProduct.congr eS (LinearEquiv.refl R M)
  let w := TensorProduct.congr eB (LinearEquiv.refl A M)
  let e := (Algebra.IsPushout.cancelBaseChange R S A B M).symm
  let ψ := w.toAddEquiv.toAddMonoidHom.comp
    ((τ.app M).hom.toAddMonoidHom.comp u.symm.toAddEquiv.toAddMonoidHom)
  have hψ : (ψ : _ → _) = ⇑e := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
      change w (τ.app M (s ⊗ₜ[R,algebraMap R S] m)) = e (s ⊗ₜ[R] m)
      rw [hτ]
      exact (Algebra.IsPushout.cancelBaseChange_symm_tmul R S A B M s m).symm
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  apply (ConcreteCategory.isIso_iff_bijective (τ.app M)).mpr
  have he : (τ.app M : _ → _) = w.symm ∘ ψ ∘ u := by
    funext x
    change τ.app M x = w.symm (w (τ.app M (u.symm (u x))))
    exact (w.symm_apply_apply (τ.app M x)).symm.trans
      (congrArg (fun y ↦ w.symm (w (τ.app M y))) (u.symm_apply_apply x)).symm
  rw [he]
  exact w.symm.bijective.comp ((hψ.symm ▸ e.bijective).comp u.bijective)

private lemma isIso_restrictDerived_map
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {X Y : DerivedCategory (ModuleCat.{max u v} S)} (g : X ⟶ Y)
    [IsIso ((ModuleCat.restrictScalars f).mapDerivedCategory.map g)] : IsIso g := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have hg : IsIso (((ModuleCat.restrictScalars f).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map g) := by
    change IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map
      ((ModuleCat.restrictScalars f).mapDerivedCategory.map g))
    infer_instance
  have hg' : IsIso ((ModuleCat.restrictScalars f).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} S) n).map g)) :=
    (NatIso.isIso_map_iff (restrictedDerivedHomologyIso f n) g).mp hg
  rw [ConcreteCategory.isIso_iff_bijective] at hg' ⊢
  exact hg'

private lemma isIso_comparison_app_of_torIndependent
    {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B] [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R A S B]
    (hTor : RingTheory.TorIndependence.TorIndependent R A S)
    (LR : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} S))
    (LA : DerivedCategory (ModuleCat.{max u v} A) ⥤ DerivedCategory (ModuleCat.{max u v} B))
    (αR : DerivedCategory.Q ⋙ LR ⟶
      (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (αA : DerivedCategory.Q ⋙ LA ⟶
      (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hLR : LR.IsLeftDerivedFunctor αR
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)))
    (hLA : LA.IsLeftDerivedFunctor αA
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)))
    (X : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hαR : IsIso (αR.app (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X))) : IsIso (αA.app X) := by
  let : LR.IsLeftDerivedFunctor αR
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) := hLR
  let : LA.IsLeftDerivedFunctor αA
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) := hLA
  let : IsIso (αR.app (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj X)) := hαR
  let Res := ModuleCat.restrictScalars.{max u v} (algebraMap R A)
  let Res' := ModuleCat.restrictScalars.{max u v} (algebraMap S B)
  let : Res.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max u v, u, u} _).isLeftAdjoint
  let : Res.IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v, u, u} _).isRightAdjoint
  let : Res'.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max u v, u, u} _).isLeftAdjoint
  let : Res'.IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v, u, u} _).isRightAdjoint
  let : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v, u, u} _).isLeftAdjoint
  let : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v, u, u} _).isLeftAdjoint
  let : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B)).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  let : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  let sq : (algebraMap A B).comp (algebraMap R A) =
      (algebraMap S B).comp (algebraMap R S) :=
    (IsScalarTower.algebraMap_eq R A B).symm.trans (IsScalarTower.algebraMap_eq R S B)
  let τ := RingTheory.TorIndependence.derivedBaseChangeComparison
    (algebraMap R A) (algebraMap R S) (algebraMap A B) (algebraMap S B) sq
    LR LA αR αA
  have : IsIso τ.2.1 :=
    RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent
      hTor LR LA αR αA
  let : Algebra.IsPushout R S A B := Algebra.IsPushout.symm inferInstance
  have : ∀ M, IsIso (τ.1.app M) := fun M ↦ isIso_pushoutComparison_app τ.1 τ.2.2.1 M
  have : IsIso τ.1 := NatIso.isIso_of_isIso_app τ.1
  have : IsIso ((NatTrans.mapHomologicalComplex τ.1 (ComplexShape.up ℤ)).app X) := by
    change IsIso ((NatIso.mapHomologicalComplex (asIso τ.1) (ComplexShape.up ℤ)).hom.app X)
    infer_instance
  have hh := congrArg (fun η ↦ η.app X) τ.2.2.2
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app] at hh
  simp only [Category.id_comp] at hh
  have : IsIso (Res'.mapDerivedCategory.map (αA.app X)) := by
    simpa only [isIso_comp_right_iff] using IsIso.of_isIso_fac_left hh
  exact isIso_restrictDerived_map (algebraMap S B) (αA.app X)

/-- A complex isomorphic to a flat module placed in degree zero is K-flat. -/
private lemma kFlat_of_iso_single {R : Type u} [CommRing R]
    {X : CochainComplex (ModuleCat.{max u v} R) ℤ} {N : ModuleCat.{max u v} R}
    [Module.Flat R N] (e : X ≅ (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N) :
    X.KFlat := by
  have : X.IsStrictlyLE 0 := CochainComplex.isStrictlyLE_of_iso e.symm 0
  let Y := (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N
  have hflat : ∀ i : ℤ, Module.Flat R (Y.X i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact Module.Flat.of_linearEquiv
        (asIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).hom).toLinearEquiv
    · have hz : IsZero (Y.X i) := by
        dsimp [Y, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N i hi
      exact flat_of_subsingleton_module (ModuleCat.isZero_iff_subsingleton.mp hz)
  have : ∀ i : ℤ, Module.Flat R (X.X i) := fun i =>
    Module.Flat.of_linearEquiv (asIso (e.hom.f i)).toLinearEquiv
  exact CochainComplex.KFlat.kFlat_of_flat X 0

/-- Derived extension of scalars of a module in degree zero is its extension of scalars in degree
zero, once the comparison map is invertible at the module placed in degree zero. -/
private noncomputable def derivedExtensionSingleIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} S))
    (α : DerivedCategory.Q ⋙ L ⟶
      (ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (N : ModuleCat.{max u v} R)
    [IsIso (α.app ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N))] :
    L.obj ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} S) 0).obj
        ((ModuleCat.extendScalars.{u, u, max u v} f).obj N) :=
  L.mapIso ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app N) ≪≫
    asIso (α.app _) ≪≫
    DerivedCategory.Q.mapIso
      (((ModuleCat.extendScalars.{u, u, max u v} f).mapCochainComplexSingleFunctor 0).app N) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} S) 0).app _).symm

/-- The comparison map of derived base change from `A'` to `P'` is invertible at a module in
degree zero whose underlying `A'`-module is flat. -/
private lemma isIso_comparison_app_single_of_flat
    {A' A P' P : Type u} [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
    [Algebra A' A] [Algebra A' P'] [Algebra P' P] [Algebra A P] [Algebra A' P]
    [IsScalarTower A' P' P] [IsScalarTower A' A P]
    [Algebra.IsPushout A' P' A P] [Module.Flat A' P'] (N : ModuleCat.{max u v} P')
    [Module.Flat A' ((ModuleCat.restrictScalars (algebraMap A' P')).obj N)] :
    IsIso ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
      (algebraMap P' P)).comparison.app
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} P') 0).obj N)) := by
  let DA := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
    (algebraMap A' A)
  let DP := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
    (algebraMap P' P)
  have hX := kFlat_of_iso_single.{u, v}
    (((ModuleCat.restrictScalars (algebraMap A' P')).mapCochainComplexSingleFunctor 0).app N)
  exact isIso_comparison_app_of_torIndependent
    (torIndependent_of_flat (R := A') (B := P') (C := A))
    DA.functor DP.functor DA.comparison DP.comparison DA.isLeftDerived DP.isLeftDerived _
    (DA.comparison_isIso_of_kFlat _ hX)

private lemma exists_flat_module_of_derived_lift
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hsurj : Function.Surjective f)
    (hnil : IsNilpotent (RingHom.ker f))
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (M : Type (max u v)) [AddCommGroup M] [Module S M]
    (hflat : Module.Flat S M)
    (hbase : Nonempty
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
        f).functor.obj K ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} S) 0).obj
          (ModuleCat.of S M))) :
    ∃ (N : ModuleCat.{max u v} R), Module.Flat R N ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) ∧
      Nonempty ((ModuleCat.extendScalars.{u, u, max u v} f).obj N ≅ ModuleCat.of S M) := by
  let FR := StacksDraft.TorAmplitude.scalarLift.{u, max u v} (R := R)
  let FS := StacksDraft.TorAmplitude.scalarLift.{u, max u v} (R := S)
  let KL := FR.mapDerivedCategory.obj K
  let DL := liftedDerivedExtension.{u, u, max u v} f
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u} f
  let ML : ModuleCat.{max u v} (ULift.{max u v} S) := FS.obj (ModuleCat.of S M)
  let fL := liftedRingHom.{u, u, max u v} f
  let T' := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring
    (ULift.{max u v} R)
  let T := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring
    (ULift.{max u v} S)
  have hflatL : Module.Flat (ULift.{max u v} S) ML :=
    (Module.Flat.ulift_left_iff (R := S) (M := M)).mpr hflat
  have hflatAmp : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      (ULift.{max u v} S)
      ((DerivedCategory.singleFunctor
        (ModuleCat.{max u v} (ULift.{max u v} S)) 0).obj ML) 0 0 :=
    (StacksDraft.TorAmplitude.hasTorDimensionLECanonical_iff_hasFlatRepresentative
      (ULift.{max u v} S) ML 0).2.2 hflatL
  have hTarget : T.HasTorAmplitudeIn
      ((DerivedCategory.singleFunctor
        (ModuleCat.{max u v} (ULift.{max u v} S)) 0).obj ML) 0 0 :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalCertified_iff
      (ULift.{max u v} S)
      ((DerivedCategory.singleFunctor
        (ModuleCat.{max u v} (ULift.{max u v} S)) 0).obj ML) 0 0).2 hflatAmp
  have : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) := D.isLeftDerived
  let eLift := @derivedExtensionLiftSquare
    _ _ inferInstance inferInstance f D.functor D.comparison D.isLeftDerived
  have hLiftIso : DL.functor.obj KL ≅
      (DerivedCategory.singleFunctor
        (ModuleCat.{max u v} (ULift.{max u v} S)) 0).obj ML := by
    let e := Classical.choice hbase
    exact (eLift.app K).symm ≪≫
      FS.mapDerivedCategory.mapIso e ≪≫
      (FS.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of S M)
  have hTarget' : T.HasTorAmplitudeIn (DL.functor.obj KL) 0 0 := by
    rw [T.hasTorAmplitudeIn_iff]
    exact (StacksDraft.TorAmplitude.hasTorAmplitude_of_iso hLiftIso 0 0).2 hTarget
  have hAmpLift : T'.HasTorAmplitudeIn KL 0 0 := by
    have : DL.functor.IsLeftDerivedFunctor DL.comparison
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{max u v} R))
          (ComplexShape.up ℤ)) := DL.isLeftDerived
    exact (@StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedExtensionScalars_certified_iff
      _ _ inferInstance inferInstance fL
      (liftedRingHom_surjective.{u, u, max u v} f hsurj)
      (liftedRingHom_isNilpotent_ker.{u, u, max u v} f hnil)
      DL.functor DL.comparison DL.isLeftDerived T' T KL 0 0).mp hTarget'
  have hCanonLift : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      (ULift.{max u v} R) KL 0 0 :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalCertified_iff
      (ULift.{max u v} R) KL 0 0).mp hAmpLift
  have hFlatRep : StacksDraft.TorAmplitude.HasFlatRepresentative KL 0 0 :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
      (ULift.{max u v} R) KL 0 0).mp hCanonLift
  obtain ⟨E, hEflat, hEGE, hELE, ⟨eE⟩⟩ := hFlatRep
  let : E.IsStrictlyGE 0 := hEGE
  let : E.IsStrictlyLE 0 := hELE
  obtain ⟨N₀, ⟨e₀⟩⟩ := CochainComplex.exists_iso_single E 0
  have hflatN₀ : Module.Flat (ULift.{max u v} R) N₀ :=
    Module.Flat.of_linearEquiv (asIso (e₀.inv.f 0)).toLinearEquiv
  let : Module.Flat (ULift.{max u v} R) N₀ := hflatN₀
  let eSingleLift : KL ≅
      (DerivedCategory.singleFunctor
        (ModuleCat.{max u v} (ULift.{max u v} R)) 0).obj N₀ :=
    eE ≪≫ DerivedCategory.Q.mapIso e₀ ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ
        (ModuleCat.{max u v} (ULift.{max u v} R)) 0).app N₀).symm
  let ER : ModuleCat.{max u v} R := FR.asEquivalence.inverse.obj N₀
  let eModule := FR.asEquivalence.counitIso.app N₀
  have hflatER : Module.Flat R ER := by
    have hflatLifted : Module.Flat (ULift.{max u v} R) ER := by
      change Module.Flat (ULift.{max u v} R) ((FR.obj ER : ModuleCat (ULift.{max u v} R)))
      exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hflatN₀ eModule.toLinearEquiv
    exact (Module.Flat.ulift_left_iff.{u, max u v, max u v}
      (R := R) (M := (ER : Type (max u v)))).mp hflatLifted
  have eKSingle : K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj ER := by
    let G := FR.mapDerivedCategory
    let eG := G.asEquivalence
    let eLiftedSingle := (FR.mapDerivedCategorySingleFunctor 0).app ER ≪≫
      (DerivedCategory.singleFunctor
        (ModuleCat.{max u v} (ULift.{max u v} R)) 0).mapIso eModule
    exact Functor.FullyFaithful.preimageIso (Functor.FullyFaithful.ofFullyFaithful G)
      (eSingleLift ≪≫ eLiftedSingle.symm)
  let EL := (CochainComplex.singleFunctor
      (ModuleCat.{max u v} (ULift.{max u v} R)) 0).obj N₀
  have hCmp : IsIso (DL.comparison.app EL) :=
    DL.comparison_isIso_of_kFlat EL (kFlat_of_iso_single.{max u v, v} (Iso.refl EL))
  let F := ModuleCat.extendScalars.{max u v, max u v, max u v} fL
  let eSingleExt := derivedExtensionSingleIso.{max u v, v} fL DL.functor DL.comparison N₀
  let eDerived : (DL.functor.obj KL) ≅
      (DerivedCategory.singleFunctor
        (ModuleCat.{max u v} (ULift.{max u v} S)) 0).obj (F.obj N₀) :=
    DL.functor.mapIso eSingleLift ≪≫ eSingleExt
  have eModules : F.obj N₀ ≅ ML := by
    let G := DerivedCategory.singleFunctor
      (ModuleCat.{max u v} (ULift.{max u v} S)) 0
    exact Functor.FullyFaithful.preimageIso (Functor.FullyFaithful.ofFullyFaithful G)
        (eDerived.symm ≪≫ hLiftIso)
  let extOrig := ModuleCat.extendScalars.{u, u, max u v} f
  have eOrig : extOrig.obj ER ≅ ModuleCat.of S M := by
    let eSquare := extensionLiftSquare.{u, u, max u v} f
    let eSource := FR.asEquivalence.counitIso.app N₀
    let e' := eSquare.app ER ≪≫ F.mapIso eSource ≪≫ eModules
    exact Functor.FullyFaithful.preimageIso (Functor.FullyFaithful.ofFullyFaithful FS) e'
  exact ⟨ER, hflatER, ⟨eKSingle⟩, ⟨eOrig⟩⟩

/-- Over a nilpotent surjection, an `A`-flat module lifts flatly if and only if
it admits a bounded-above derived lift. -/
@[stacks 0DZ1]
public theorem exists_flat_lift_iff_exists_derived_lift
    (A' A P' : Type u) [CommRing A'] [CommRing A] [CommRing P']
    [Algebra A' A] [Algebra A' P']
    (hsurj : Function.Surjective (algebraMap A' A))
    (hnil : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Module.Flat A' P']
    (M : Type v) [AddCommGroup M] [Module (TensorProduct A' P' A) M]
    [Module A M] [IsScalarTower A (TensorProduct A' P' A) M]
    [Module.Flat A M] :
    (∃ (M' : Type (max u v)) (_ : AddCommGroup M')
      (_ : Module P' M') (_ : Module A' M') (_ : IsScalarTower A' P' M'),
      Module.Flat A' M' ∧
        Nonempty
          ((ModuleCat.extendScalars.{u, u, max u v}
              (algebraMap P' (TensorProduct A' P' A))).obj
                (ModuleCat.of.{max u v, u} P' M') ≅
            ModuleCat.of.{max u v, u} (TensorProduct A' P' A) (ULift.{u} M))) ↔
      ∃ (K : DerivedCategory.Minus (ModuleCat.{max u v} P')),
        Nonempty
          ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
            (algebraMap P' (TensorProduct A' P' A))).functor.obj K.obj ≅
            (DerivedCategory.Q
              (C := ModuleCat.{max u v} (TensorProduct A' P' A))).obj
                ((CochainComplex.singleFunctor
                  (ModuleCat.{max u v} (TensorProduct A' P' A)) 0).obj
                    (ModuleCat.of.{max u v, u} (TensorProduct A' P' A)
                      (ULift.{u} M)))) := by
  constructor
  · rintro ⟨M', hM'Group, hM'P, hM'A', hM'Tower, hM'Flat, hM'Iso⟩
    let P := TensorProduct A' P' A
    let DP := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
      (algebraMap P' P)
    let Res := ModuleCat.restrictScalars (algebraMap A' P')
    let eM : M' ≃ₗ[A'] (Res.obj (ModuleCat.of P' M') : Type (max u v)) := {
      toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => (IsScalarTower.algebraMap_smul (R := A') (A := P') a x).symm }
    let : Module.Flat A' M' := hM'Flat
    let : Module.Flat A' (Res.obj (ModuleCat.of P' M') : Type (max u v)) :=
      Module.Flat.of_linearEquiv eM.symm
    have := isIso_comparison_app_single_of_flat.{u, v} (A' := A') (A := A) (ModuleCat.of P' M')
      (P := P) (P' := P')
    let eSingleExt := derivedExtensionSingleIso.{u, v} (algebraMap P' P) DP.functor
      DP.comparison (ModuleCat.of P' M')
    let Kobj := (DerivedCategory.singleFunctor (ModuleCat.{max u v} P') 0).obj
      (ModuleCat.of P' M')
    let Kminus : DerivedCategory.Minus (ModuleCat.{max u v} P') :=
      ⟨Kobj, ⟨0, by infer_instance⟩⟩
    let eTarget := (DerivedCategory.singleFunctor (ModuleCat.{max u v} P) 0).mapIso
      (Classical.choice hM'Iso) ≪≫
        (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} P) 0).app
          (ModuleCat.of P (ULift.{u} M))
    exact ⟨Kminus, ⟨eSingleExt ≪≫ eTarget⟩⟩
  · rintro ⟨K, hK⟩
    let P := TensorProduct A' P' A
    let RP := ModuleCat.restrictScalars (algebraMap A' P')
    let RA := ModuleCat.restrictScalars (algebraMap A P)
    let DP := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
      (algebraMap P' P)
    let MA : ModuleCat.{max u v} A := RA.obj (ModuleCat.of.{max u v, u} P (ULift.{u} M))
    let KA := RP.mapDerivedCategory.obj K.obj
    let DA := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
      (algebraMap A' A)
    let hBaseP := Classical.choice hK
    have hBaseChange := derivedBaseChange_iso
      (A' := A') (A := A) (P' := P') (P := P) K.obj
    have hBaseA : DA.functor.obj KA ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj MA :=
      (Classical.choice hBaseChange).symm ≪≫
        RA.mapDerivedCategory.mapIso hBaseP ≪≫
        (RA.mapDerivedCategorySingleFunctor 0).app
          (ModuleCat.of.{max u v, u} P (ULift.{u} M))
    have hFlatMA : Module.Flat A (MA : Type (max u v)) := by
      let e : (MA : Type (max u v)) ≃ₗ[A] ULift.{u} M := {
        toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro a x
          apply ULift.ext
          change (algebraMap A P a) • x.down = a • x.down
          exact IsScalarTower.algebraMap_smul (R := A) (A := P) a x.down }
      let : Module.Flat A (ULift.{u} M) :=
        Module.Flat.ulift_right_iff.mpr (inferInstance : Module.Flat A M)
      exact Module.Flat.of_linearEquiv e
    obtain ⟨NA, hNAFlat, hKASingle, -⟩ := exists_flat_module_of_derived_lift
      (f := algebraMap A' A) hsurj hnil KA (MA : Type (max u v)) hFlatMA ⟨hBaseA⟩
    let HA := (DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} P') 0).obj K.obj
    let eHA : RP.obj HA ≅ NA :=
      ((restrictedDerivedHomologyIso (algebraMap A' P') 0).app K.obj).symm ≪≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A') 0).mapIso
          (Classical.choice hKASingle)) ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{max u v} A') 0).app NA
    let : Module.Flat A' NA := hNAFlat
    have hFlatHA : Module.Flat A' (RP.obj HA) :=
      Module.Flat.of_linearEquiv eHA.toLinearEquiv
    let : Module A' (HA : Type (max u v)) := (RP.obj HA).isModule
    let : IsScalarTower A' P' (HA : Type (max u v)) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    have hzero : ∀ p : ℤ, p ≠ 0 → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} P') p).obj K.obj) := by
      intro p hp
      let H := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} P') p).obj K.obj
      have hzA : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A') p).obj KA) := by
        have hzChain : IsZero
            (((CochainComplex.singleFunctor (ModuleCat.{max u v} A') 0).obj NA).homology p) :=
          HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 NA p hp
        let Xsingle := (CochainComplex.singleFunctor (ModuleCat.{max u v} A') 0).obj NA
        let eHchain : ((DerivedCategory.homologyFunctor
            (ModuleCat.{max u v} A') p).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A') 0).obj NA)) ≅
            Xsingle.homology p :=
          (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A') p).mapIso
              ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} A') 0).app NA) ≪≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A') p).app Xsingle
        have hzSingle : IsZero ((DerivedCategory.homologyFunctor
            (ModuleCat.{max u v} A') p).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A') 0).obj NA)) :=
          IsZero.of_iso hzChain eHchain
        exact IsZero.of_iso hzSingle
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A') p).mapIso
            (Classical.choice hKASingle))
      have hzRes : IsZero (RP.obj H) :=
        IsZero.of_iso hzA ((restrictedDerivedHomologyIso (algebraMap A' P') p).app K.obj).symm
      have : Subsingleton (RP.obj H : Type (max u v)) :=
        ModuleCat.isZero_iff_subsingleton.mp hzRes
      exact ModuleCat.isZero_iff_subsingleton.mpr this
    have : K.obj.IsGE 0 := (DerivedCategory.isGE_iff K.obj 0).2 fun p hp => hzero p (by lia)
    have : K.obj.IsLE 0 := (DerivedCategory.isLE_iff K.obj 0).2 fun p hp => hzero p (by lia)
    obtain ⟨H₀, ⟨eK⟩⟩ := K.obj.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
    let eH₀ : H₀ ≅ HA :=
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} P') 0).app H₀).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} P') 0).mapIso eK.symm
    let eKSingle : K.obj ≅ (DerivedCategory.singleFunctor
        (ModuleCat.{max u v} P') 0).obj HA :=
      eK ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{max u v} P') 0).mapIso eH₀
    let ExtP := ModuleCat.extendScalars.{u, u, max u v} (algebraMap P' P)
    let : Module.Flat A' (RP.obj (ModuleCat.of P' (HA : Type (max u v)))) := hFlatHA
    have : IsIso (DP.comparison.app ((CochainComplex.singleFunctor
        (ModuleCat.{max u v} P') 0).obj (ModuleCat.of P' (HA : Type (max u v))))) :=
      isIso_comparison_app_single_of_flat.{u, v} (A' := A') (A := A)
        (ModuleCat.of P' (HA : Type (max u v)))
    let eSingleExt := derivedExtensionSingleIso.{u, v} (algebraMap P' P) DP.functor
      DP.comparison (ModuleCat.of P' (HA : Type (max u v)))
    let eMtarget := (DerivedCategory.singleFunctorIsoCompQ
      (ModuleCat.{max u v} P) 0).app (ModuleCat.of P (ULift.{u} M))
    have eDerived : DP.functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} P') 0).obj
          (ModuleCat.of P' (HA : Type (max u v)))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} P) 0).obj
          (ModuleCat.of P (ULift.{u} M)) :=
      DP.functor.mapIso eKSingle.symm ≪≫ hBaseP ≪≫ eMtarget.symm
    have eOrig : ExtP.obj (ModuleCat.of P' (HA : Type (max u v))) ≅
        ModuleCat.of P (ULift.{u} M) :=
      Functor.FullyFaithful.preimageIso
        (Functor.FullyFaithful.ofFullyFaithful
          (DerivedCategory.singleFunctor (ModuleCat.{max u v} P) 0))
        (eSingleExt.symm ≪≫ eDerived)
    exact ⟨(HA : Type (max u v)), inferInstance, inferInstance, inferInstance,
      inferInstance, hFlatHA, ⟨eOrig⟩⟩

end Deformation.Examples.DerivedLift

end
