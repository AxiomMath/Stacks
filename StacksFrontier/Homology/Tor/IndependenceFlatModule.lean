module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
import all StacksFrontier.Homology.Tor.IndependenceBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor-independent base change of a module that is flat over the base

Let `R → A` and `R → B` be homomorphisms of commutative rings, let `T` be a pushout of that
square, so `T = A ⊗[R] B`, and assume `A` and `B` are Tor independent over `R`. For an
`A`-module `M` which is flat as an `R`-module, extension of scalars along `A → T` already
computes the derived extension of scalars of `M`: no resolution is needed.

## Main results

* `RingTheory.TorIndependence.isIso_comparison_of_kFlat_restrictScalars`: the comparison from
  derived to termwise extension of scalars along `A → T` is invertible on a complex whose
  restriction to `R` is K-flat.
* `RingTheory.TorIndependence.isIso_comparison_single_of_flat`: the comparison from derived to
  termwise extension of scalars along `A → T` is invertible on a module flat over `R`.
* `RingTheory.TorIndependence.quasiIso_extendScalars_of_flat`: a quasi-isomorphism from a K-flat
  complex to such a module stays a quasi-isomorphism after extension of scalars along `A → T`.
* `RingTheory.TorIndependence.quasiIso_extendScalars_of_flat_of_flat`: the same after extension
  of scalars along `A → C`, for `C` a flat `T`-algebra.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open AlgebraicGeometry.BaseChangeTorAmplitude
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

attribute [local instance] extendScalarsAdditive
attribute [local instance_reducible] CochainComplex.extendScalarsLarge
attribute [local instance] HasDerivedCategory.standard

/-- The middle map of a three-fold composite is invertible as soon as the outer two are and the
composite equals an invertible map. -/
private theorem isIso_mid_of_eq {C : Type*} [Category C] {W X Y Z : C}
    {a : W ⟶ X} {b : X ⟶ Y} {c : Y ⟶ Z} {u : W ⟶ Z} (h : a ≫ b ≫ c = u)
    (ha : IsIso a) (hc : IsIso c) (hu : IsIso u) : IsIso b := by
  subst h
  have := IsIso.of_isIso_comp_left a (b ≫ c)
  exact IsIso.of_isIso_comp_right b c

variable {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T] [Algebra A T] [Algebra B T]
  [IsScalarTower R A T] [IsScalarTower R B T] [Algebra.IsPushout R A B T]

/-- K-flatness transports along an isomorphism of cochain complexes. -/
private theorem kFlat_of_iso {R₀ : Type u} [CommRing R₀]
    {K L : CochainComplex (ModuleCat.{u} R₀) ℤ} (e : K ≅ L) (hK : K.KFlat) : L.KFlat := by
  intro M hM
  let F :=
    (((CategoryTheory.MonoidalCategory.curriedTensor
      (ModuleCat.{u} R₀)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} R₀) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  exact HomologicalComplex.Acyclic.of_iso (F.mapIso e) (hK M hM)

/-- **A complex that is K-flat over the base computes its own derived base change.** For `A` and
`B` Tor independent over `R` and `T` a pushout of `A ← R → B`, the comparison from derived to
termwise extension of scalars along `A → T` is invertible on every complex of `A`-modules whose
restriction to `R` is K-flat. Nothing is assumed about the complex over `A`. -/
public theorem isIso_comparison_of_kFlat_restrictScalars
    (hTor : TorIndependent R A B) (KM : CochainComplex (ModuleCat.{u} A) ℤ)
    (hKM : CochainComplex.KFlat
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj KM)) :
    IsIso ((totalDerivedExtensionScalars (algebraMap A T)).comparison.app KM) := by
  let Dbase := totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)
  let Dtop := totalDerivedExtensionScalars.{u, u, u} (algebraMap A T)
  let sq : (algebraMap A T).comp (algebraMap R A) = (algebraMap B T).comp (algebraMap R B) :=
    (IsScalarTower.algebraMap_eq R A T).symm.trans (IsScalarTower.algebraMap_eq R B T)
  let cmp := @derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
    R A B T _ _ _ _ _ _ _ _
    (algebraMap R A) (algebraMap R B) (algebraMap A T) (algebraMap B T)
    sq Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
    Dbase.isLeftDerived Dtop.isLeftDerived
  have hcmp : IsIso cmp.2.1 :=
    @derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u, u, u + 1, u + 1, u + 1,
        u + 1}
      R A B T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hTor Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
      Dbase.isLeftDerived Dtop.isLeftDerived
  have hunderived : ∀ N : ModuleCat.{u} A, IsIso (cmp.1.app N) := by
    intro N
    rw [ConcreteCategory.isIso_iff_bijective]
    let : Module R N := Module.compHom N (algebraMap R A)
    let : IsScalarTower R A N := ⟨fun r a m => by
      rw [Algebra.smul_def]
      change ((algebraMap R A r) * a) • m = (algebraMap R A r) • a • m
      exact mul_smul _ _ _⟩
    let eB : (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B) ≃ₗ[R] B :=
      { AddEquiv.refl B with
        map_smul' := fun r b => (Algebra.smul_def (R := R) (A := B) r b).symm }
    let eT : (ModuleCat.restrictScalars (algebraMap A T)).obj (ModuleCat.of T T) ≃ₗ[A] T :=
      { AddEquiv.refl T with
        map_smul' := fun a x => (Algebra.smul_def (R := A) (A := T) a x).symm }
    let eA := eT.trans (Algebra.IsPushout.equiv R A B T).symm.toLinearEquiv
    let v := TensorProduct.congr eB (LinearEquiv.refl R N)
    let w := TensorProduct.congr eA (LinearEquiv.refl A N)
    let ψ := w.toAddEquiv.toAddMonoidHom.comp
      ((cmp.1.app N).hom.toAddMonoidHom.comp v.symm.toAddEquiv.toAddMonoidHom)
    have hψ : Function.Bijective ψ := by
      apply bijective_tensorProduct_baseChange
      intro b m
      change w (cmp.1.app N (v.symm (b ⊗ₜ[R] m))) = ((1 : A) ⊗ₜ[R] b) ⊗ₜ[A] m
      change w (cmp.1.app N (b ⊗ₜ[R,algebraMap R B] m)) = _
      rw [cmp.2.2.1]
      change (Algebra.IsPushout.equiv R A B T).symm (algebraMap B T b) ⊗ₜ[A] m = _
      rw [Algebra.IsPushout.equiv_symm_algebraMap_right]
    exact (v.symm.bijective.of_comp_iff _).mp ((w.bijective.of_comp_iff' _).mp hψ)
  have hcmp1 : IsIso cmp.1 := NatIso.isIso_of_isIso_app cmp.1
  have hbase : IsIso (Dbase.comparison.app
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj KM)) :=
    Dbase.comparison_isIso_of_kFlat _ hKM
  have hnat : IsIso ((NatTrans.mapHomologicalComplex cmp.1 (ComplexShape.up ℤ)).app KM) :=
    inferInstanceAs
      (IsIso ((NatIso.mapHomologicalComplex (asIso cmp.1) (ComplexShape.up ℤ)).hom.app KM))
  have heq := @derivedBaseChangeComparison_snd_app_comp_counit.{u, u, u, u, u, u + 1, u + 1,
      u + 1, u + 1}
    R A B T _ _ _ _ _ _ _ _
    (algebraMap R A) (algebraMap R B) (algebraMap A T) (algebraMap B T)
    sq Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
    Dbase.isLeftDerived Dtop.isLeftDerived KM
  have hfactR : IsIso ((ModuleCat.restrictScalars
      (algebraMap R A)).mapDerivedCategoryFactors.hom.app KM) :=
    inferInstanceAs (IsIso (((ModuleCat.restrictScalars
      (algebraMap R A)).mapDerivedCategoryFactors.app KM).hom))
  have hfactT : IsIso ((ModuleCat.restrictScalars
      (algebraMap B T)).mapDerivedCategoryFactors.hom.app
      (((ModuleCat.extendScalars (algebraMap A T)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj KM)) :=
    inferInstanceAs (IsIso (((ModuleCat.restrictScalars
      (algebraMap B T)).mapDerivedCategoryFactors.app
      (((ModuleCat.extendScalars (algebraMap A T)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj KM)).hom))
  have hcmpapp : IsIso (cmp.2.1.app (DerivedCategory.Q.obj KM)) := inferInstance
  have h1 : IsIso (Dbase.functor.map ((ModuleCat.restrictScalars
      (algebraMap R A)).mapDerivedCategoryFactors.hom.app KM)) := inferInstance
  have h3 : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex cmp.1 (ComplexShape.up ℤ)).app KM)) := inferInstance
  have hmap : IsIso ((ModuleCat.restrictScalars (algebraMap B T)).mapDerivedCategory.map
      (Dtop.comparison.app KM)) :=
    isIso_mid_of_eq heq hcmpapp hfactT (IsIso.comp_isIso' h1 (IsIso.comp_isIso' hbase h3))
  exact isIso_of_reflects_iso (Dtop.comparison.app KM)
    (ModuleCat.restrictScalars (algebraMap B T)).mapDerivedCategory

/-- **A module flat over the base computes its own derived base change.** For `A` and `B` Tor
independent over `R` and `T` a pushout of `A ← R → B`, the comparison from derived to termwise
extension of scalars along `A → T` is invertible on the single complex of an `A`-module whose
restriction to `R` is flat. -/
@[sga "3 VIB 12.7" "more general"]
public theorem isIso_comparison_single_of_flat
    (hTor : TorIndependent R A B) (M : ModuleCat.{u} A)
    (hM : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)) :
    IsIso ((totalDerivedExtensionScalars (algebraMap A T)).comparison.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M)) := by
  refine isIso_comparison_of_kFlat_restrictScalars (T := T) hTor _
    (kFlat_of_iso
      ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars (algebraMap R A)) (ComplexShape.up ℤ) 0).app M).symm
      (single_kFlat_of_flat _ hM))

/-- **Extension of scalars along a Tor-independent base change preserves a quasi-isomorphism
onto a module flat over the base.** If `K` is a K-flat complex of `A`-modules, `M` an
`A`-module whose restriction to `R` is flat, and `K ⟶ M[0]` a quasi-isomorphism, then applying
`T ⊗[A] -` in each degree again gives a quasi-isomorphism. -/
public theorem quasiIso_extendScalars_of_flat
    (hTor : TorIndependent R A B)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : CochainComplex.KFlat K)
    (M : ModuleCat.{u} A)
    (hM : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M))
    (q : K ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M) [QuasiIso q] :
    QuasiIso (((ModuleCat.extendScalars (algebraMap A T)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  let D := totalDerivedExtensionScalars (algebraMap A T)
  have hKcmp : IsIso (D.comparison.app K) := D.comparison_isIso_of_kFlat K hK
  have hMcmp : IsIso (D.comparison.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M)) :=
    isIso_comparison_single_of_flat (T := T) hTor M hM
  have hDq : IsIso (D.functor.map (DerivedCategory.Q.map q)) := inferInstance
  have hnat := D.comparison.naturality q
  have hstart : IsIso ((DerivedCategory.Q ⋙ D.functor).map q ≫
      D.comparison.app ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have hcomp : IsIso
      (D.comparison.app K ≫ (extensionOfScalarsComplexGeneral (algebraMap A T)).map q) :=
    hnat ▸ hstart
  have hq : IsIso ((extensionOfScalarsComplexGeneral (algebraMap A T)).map q) :=
    IsIso.of_isIso_comp_left (D.comparison.app K) _
  change IsIso (DerivedCategory.Q.map
      (((ModuleCat.extendScalars (algebraMap A T)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map q)) at hq
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hq

/-- For `A` and `B` Tor independent over `R`, `T` a pushout of `A ← R → B` and `C` a flat
`T`-algebra, a quasi-isomorphism from a K-flat complex of `A`-modules onto a module flat over `R`
stays a quasi-isomorphism after termwise extension of scalars along `A → C`. -/
public theorem quasiIso_extendScalars_of_flat_of_flat
    {C : Type u} [CommRing C] [Algebra A C] [Algebra T C] [IsScalarTower A T C]
    [Module.Flat T C]
    (hTor : TorIndependent R A B)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : CochainComplex.KFlat K)
    (M : ModuleCat.{u} A)
    (hM : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M))
    (q : K ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M) [QuasiIso q] :
    QuasiIso (((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  let F := ModuleCat.extendScalars (algebraMap T C)
  let E := ModuleCat.extendScalars (algebraMap A T)
  let G := ModuleCat.extendScalars (algebraMap A C)
  have hq : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map q) :=
    quasiIso_extendScalars_of_flat (T := T) hTor K hK M hM q
  have hFlim : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hFadd : F.Additive := Functor.additive_of_preserves_binary_products F
  have hq' : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ F
  let e : G ≅ E ⋙ F :=
    eqToIso (congrArg (fun φ : A →+* C => ModuleCat.extendScalars φ)
      (IsScalarTower.algebraMap_eq A T C)) ≪≫
      ModuleCat.extendScalarsComp (algebraMap A T) (algebraMap T C)
  let ec := NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)
  have hnat := ec.hom.naturality q
  have hi : IsIso (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫
      (DerivedCategory.Q.mapIso (ec.app _)).hom) := by
    change IsIso (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫ DerivedCategory.Q.map
        (ec.hom.app _))
    rw [← Functor.map_comp, hnat, Functor.map_comp]
    change IsIso (DerivedCategory.Q.map (ec.hom.app K) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map q)))
    infer_instance
  have hi' : IsIso (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :=
    IsIso.of_isIso_comp_right _ (DerivedCategory.Q.mapIso (ec.app _)).hom
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hi'

end RingTheory.TorIndependence

end
