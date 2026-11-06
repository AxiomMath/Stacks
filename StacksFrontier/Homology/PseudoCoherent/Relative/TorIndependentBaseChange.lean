module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Relative pseudo-coherence under Tor-independent base change

Let `A` be a finite-type algebra over a commutative ring `R` and let `R'` be an `R`-algebra
Tor independent from `A` over `R`. Derived extension of scalars from `A` to `R' ⊗[R] A`
carries relative `m`-pseudo-coherence over `R` to relative `m`-pseudo-coherence over `R'`, and
likewise for relative pseudo-coherence.

## Main results

* `PseudoCoherence.derivedExtensionScalars_preserves_relativelyPseudoCoherent_of_torIndependent`:
  derived extension of scalars along `A → R' ⊗[R] A` preserves relative `m`-pseudo-coherence
  and relative pseudo-coherence when `A` and `R'` are Tor independent over `R`.

## Implementation notes

The base-changed algebra is written `R' ⊗[R] A`; it is identified with `A ⊗[R] R'` by
`Algebra.TensorProduct.commRight`.

## References

* [The Stacks Project, Lemma 15.82.7 (067A)](https://stacks.math.columbia.edu/tag/067A)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The total derived extension-of-scalars functor along `f` preserves `m`-pseudo-coherence for
every `m`, and pseudo-coherence. -/
private lemma totalDerivedExtensionScalars_preserves_pseudoCoherent
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : DerivedCategory (ModuleCat.{u} R)) :
    (∀ m : ℤ, IsPseudoCoherentFrom K m →
        IsPseudoCoherentFrom ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K) m) ∧
      (IsPseudoCoherent K →
        IsPseudoCoherent ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K)) :=
  baseChange_preserves_pseudoCoherent f (totalDerivedExtensionScalars.{u, u, u} f).comparison
    (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived K

set_option backward.isDefEq.respectTransparency false in
private noncomputable def polynomialBaseChangeModuleIso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) : letI :=
      (MvPolynomial.map (σ := Fin n) (algebraMap R S)).toAlgebra
      (ModuleCat.extendScalars (algebraMap R (MvPolynomial (Fin n) R))).obj
        (ModuleCat.of R S) ≅
      ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) := by
  letI := (MvPolynomial.map (σ := Fin n) (algebraMap R S)).toAlgebra
  let P := MvPolynomial (Fin n) R
  let e := (Algebra.TensorProduct.comm R P S).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R S).toRingEquiv
  let le : P ⊗[R] S ≃ₗ[P] MvPolynomial (Fin n) S :=
    { e.toAddEquiv with
      map_smul' := by
        intro p z
        induction z using TensorProduct.inductionOn with
        | tmul q s =>
            change e ((p * q) ⊗ₜ[R] s) = _
            dsimp [e]
            rw [MvPolynomial.algebraTensorAlgEquiv_tmul,
              MvPolynomial.algebraTensorAlgEquiv_tmul, map_mul]
            simp only [Algebra.smul_def]
            ac_rfl
        | add x y hx hy =>
            rw [smul_add]
            change e (p • x + p • y) = p • e (x + y)
            rw [map_add, map_add, smul_add]
            exact congrArg₂ (· + ·) hx hy }
  exact extendScalarsAlgebraMapObjIso (ModuleCat.of R S) ≪≫ le.toModuleIso

/-- Restricting the `P`-module `A` to `R` along an `R`-algebra structure on `P` recovers `A`. -/
private def restrictScalarsLinearEquiv (R P A : Type u) [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A] :
    (ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A) ≃ₗ[R] A :=
  { toFun := fun a => (a : A)
    invFun := fun a => (a : (ModuleCat.restrictScalars (algebraMap R P)).obj
      (ModuleCat.of P A))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun r a ↦ IsScalarTower.algebraMap_smul P r (show A from a) }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictTensorIso
    {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
    (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P (A ⊗[R] M)) ≅
      (tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
        (ModuleCat.of P A))).obj M := by
  let eA := restrictScalarsLinearEquiv R P A
  let X := (ModuleCat.restrictScalars (algebraMap R P)).obj
    (ModuleCat.of P (A ⊗[R] M))
  let Y := (tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
    (ModuleCat.of P A))).obj M
  let e₀ : X ≃ₗ[R] ModuleCat.of R (A ⊗[R] M) :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r z
        induction z using TensorProduct.induction_on with
        | zero =>
            change (algebraMap R P r) • (0 : A ⊗[R] M) = r • (0 : A ⊗[R] M)
            rw [smul_zero, smul_zero]
        | tmul a m =>
            change ((algebraMap R P r) • a) ⊗ₜ[R] m = (r • a) ⊗ₜ[R] m
            rw [IsScalarTower.algebraMap_smul P r a]
        | add x y hx hy =>
            change (algebraMap R P r) • (x + y) = r • (x + y)
            rw [smul_add, smul_add]
            exact congrArg₂ (fun x y => x + y) hx hy }
  let e₁ : ModuleCat.of R (A ⊗[R] M) ≃ₗ[R] Y :=
    (TensorProduct.congr eA.symm (LinearEquiv.refl R M))
  exact (e₀.trans e₁).toModuleIso

set_option backward.isDefEq.respectTransparency false in
private noncomputable def cancelPolynomialBaseChangeNatIso
    {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A] :
    ModuleCat.extendScalars (algebraMap R P) ⋙ tensorLeft (ModuleCat.of P A) ⋙
      ModuleCat.restrictScalars (algebraMap R P) ≅
      tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact ((ModuleCat.restrictScalars (algebraMap R P)).mapIso
        ((tensorLeft (ModuleCat.of P A)).mapIso (extendScalarsAlgebraMapObjIso M))) ≪≫
      ((ModuleCat.restrictScalars (algebraMap R P)).mapIso
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R P P A M).toModuleIso) ≪≫
      restrictTensorIso M
  · intro M N f
    apply ModuleCat.hom_ext
    ext z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m =>
        induction m using TensorProduct.induction_on with
        | zero => rfl
        | tmul p x => rfl
        | add x y hx hy =>
            rw [TensorProduct.tmul_add]
            simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hx hy
    | add x y hx hy => simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hx hy

private lemma torIndependent_polynomial_baseChange_sameUniverse
    (R A S : Type u) [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (n : ℕ)
    (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (h : TorIndependent R A S) :
    letI : Algebra (MvPolynomial (Fin n) R) A := α.toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) :=
      (MvPolynomial.map (algebraMap R S)).toAlgebra
    TorIndependent (MvPolynomial (Fin n) R) A (MvPolynomial (Fin n) S) := by
  let : Algebra (MvPolynomial (Fin n) R) A := α.toRingHom.toAlgebra
  let : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) :=
    (MvPolynomial.map (algebraMap R S)).toAlgebra
  rw [torIndependent_iff_isZero_tor] at h ⊢
  intro i hi
  let P := MvPolynomial (Fin n) R
  let P' := MvPolynomial (Fin n) S
  let F := ModuleCat.extendScalars (algebraMap R P)
  have : Module.Free R P := inferInstance
  have : Module.Flat R P := inferInstance
  let : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R P))
  let Q₀ := projectiveResolution (ModuleCat.of R S)
  let Q := F.mapProjectiveResolution Q₀
  let eS : F.obj (ModuleCat.of R S) ≅ ModuleCat.of P P' :=
    polynomialBaseChangeModuleIso n
  let eTor := ((Tor (ModuleCat P) i).obj (ModuleCat.of P A)).mapIso eS
  refine IsZero.of_iso ?_ eTor.symm
  let eQ := Q.isoLeftDerivedObj (tensorLeft (ModuleCat.of P A)) i
  refine IsZero.of_iso ?_ eQ
  rw [ModuleCat.isZero_iff_subsingleton]
  let eA := (restrictScalarsLinearEquiv R P A).toModuleIso
  have hz : IsZero (((tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
      (ModuleCat.of P A))).leftDerived i).obj (ModuleCat.of R S)) :=
    IsZero.of_iso (h i hi) (((Tor (ModuleCat R) i).mapIso eA).app (ModuleCat.of R S))
  have hz₀ : IsZero
      ((((tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj
        (ModuleCat.of P A))).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          Q₀.complex).homology i) :=
    hz.of_iso (Q₀.isoLeftDerivedObj
      (tensorLeft ((ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P A))) i).symm
  let G := ModuleCat.restrictScalars (algebraMap R P)
  let C := ((tensorLeft (ModuleCat.of P A)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj Q.complex
  have e₀ : G.obj (C.homology i) ≅
      (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology i) :=
    (ShortComplex.mapHomologyIso (C.sc i) G).symm ≪≫
      HomologicalComplex.homologyMapIso
        (Iso.refl ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj C)) i
  let e₁ := HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex
      (cancelPolynomialBaseChangeNatIso (R := R) (P := P) (A := A))
      (ComplexShape.down ℕ)).app Q₀.complex) i
  show Subsingleton (G.obj (C.homology i))
  exact ModuleCat.isZero_iff_subsingleton.mp ((hz₀.of_iso e₁).of_iso e₀)

private lemma torIndependent_polynomial_baseChange
    {R : Type u} {A : Type u} {S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (n : ℕ)
    (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (h : TorIndependent R A S) :
    letI : Algebra (MvPolynomial (Fin n) R) A := α.toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) :=
      (MvPolynomial.map (algebraMap R S)).toAlgebra
    TorIndependent (MvPolynomial (Fin n) R) A (MvPolynomial (Fin n) S) :=
  torIndependent_polynomial_baseChange_sameUniverse R A S n α h

private noncomputable def polynomialPresentationBaseChange
    {R : Type u} {A : Type u} {R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    MvPolynomial (Fin n) R' →ₐ[R'] R' ⊗[R] A :=
  (Algebra.TensorProduct.map (AlgHom.id R' R') α).comp
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R R').symm.toAlgHom

private lemma polynomialPresentationBaseChange_map
    {R : Type u} {A : Type u} {R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (p : MvPolynomial (Fin n) R) :
    polynomialPresentationBaseChange n α (MvPolynomial.map (algebraMap R R') p) =
      (1 : R') ⊗ₜ[R] α p := by
  simp [polynomialPresentationBaseChange]

private lemma polynomialPresentationBaseChange_surjective
    {R : Type u} {A : Type u} {R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (hα : Function.Surjective α) :
    Function.Surjective (polynomialPresentationBaseChange (R' := R') n α) :=
  (Algebra.FiniteType.baseChangeAux_surj R' hα).comp
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R R').symm.surjective

/-- A Tor-independent base change preserves relative `m`-pseudo-coherence for every integer `m`,
as well as relative pseudo-coherence.

The chosen `R'`-algebra `R' ⊗[R] A` is identified with the source's `A ⊗[R] R'` by
`Algebra.TensorProduct.commRight R R' A`. -/
@[stacks 067A,
  sga "6 III 1.10" "a), affine case",
  sga "6 III 1.8" "affine, E₂ = O",
  sga "6 III 4.7" "(a), special case"]
public theorem derivedExtensionScalars_preserves_relativelyPseudoCoherent_of_torIndependent
    {R : Type u} {A : Type u} {R' : Type u}
    [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Algebra.FiniteType R A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hTor : TorIndependent R A R') :
    let A' := R' ⊗[R] A
    letI : Algebra R' A' := Algebra.TensorProduct.leftAlgebra
    let f : A →+* A' := Algebra.TensorProduct.includeRight.toRingHom
    (∀ m : ℤ, IsRelativelyPseudoCoherentFrom (R := R) K m →
      IsRelativelyPseudoCoherentFrom (R := R')
        ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K)
          m) ∧
      (IsRelativelyPseudoCoherent (R := R) K →
        IsRelativelyPseudoCoherent (R := R')
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            K)) := by
  intro A' f
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  let P := MvPolynomial (Fin n) R
  let P' := MvPolynomial (Fin n) R'
  let β := polynomialPresentationBaseChange (R' := R') n α
  let : Algebra P A := α.toRingHom.toAlgebra
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  have hPP' : ∀ p : P, algebraMap P P' p = MvPolynomial.map (algebraMap R R') p :=
    fun p ↦ congrFun (congrArg DFunLike.coe MvPolynomial.algebraMap_def) p
  let : Algebra A A' := Algebra.TensorProduct.rightAlgebra
  let : Algebra P' A' := β.toRingHom.toAlgebra
  let : Algebra P A' := (β.toRingHom.comp (algebraMap P P')).toAlgebra
  have : IsScalarTower P P' A' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower P A A' := IsScalarTower.of_algebraMap_eq (fun p ↦ by
    show β (algebraMap P P' p) = (1 : R') ⊗ₜ[R] α p
    rw [hPP', polynomialPresentationBaseChange_map])
  have : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq (fun r ↦ (α.commutes r).symm)
  have : IsScalarTower R P P' := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    rw [hPP']; simp [P, P', MvPolynomial.algebraMap_eq])
  have : IsScalarTower R' P' A' := IsScalarTower.of_algebraMap_eq (fun r ↦ (β.commutes r).symm)
  have : IsScalarTower R P A' := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R A A', IsScalarTower.algebraMap_apply P A A',
      ← IsScalarTower.algebraMap_apply R P A])
  have : IsScalarTower R P' A' := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R R' A', IsScalarTower.algebraMap_apply R' P' A',
      ← IsScalarTower.algebraMap_apply R R' P'])
  have : Algebra.IsPushout P A P' A' :=
    (Algebra.IsPushout.comp_iff R P (T := A) R' P' (T' := A')).1 inferInstance
  have hTorP : TorIndependent P A P' :=
    torIndependent_polynomial_baseChange n α hTor
  let g : P →+* P' := algebraMap P P'
  let h : A →+* A' := algebraMap A A'
  let i : P' →+* A' := algebraMap P' A'
  let Dg := totalDerivedExtensionScalars.{u, u, u} g
  let Dh := derivedExtensionScalarsGeneral.{u, u, u} f
  have hcomp := @derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u,
      u, u} P A P' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTorP
    Dg.functor Dh.functor Dg.comparison Dh.comparison Dg.isLeftDerived Dh.isLeftDerived
  let comparison := @derivedBaseChangeComparison.{u, u, u, u, u}
      P A P' A' _ _ _ _ _ _ _ _ (algebraMap P A) g h i
      (IsScalarTower.algebraMap_eq P A A' ▸ IsScalarTower.algebraMap_eq P P' A')
      Dg.functor Dh.functor Dg.comparison Dh.comparison Dg.isLeftDerived Dh.isLeftDerived
  have : IsIso comparison.2.1 := hcomp
  have hfrom : ∀ m : ℤ, IsRelativelyPseudoCoherentFrom (R := R) K m →
      IsRelativelyPseudoCoherentFrom (R := R') (Dh.functor.obj K) m := by
    intro m hK
    have hP' : IsPseudoCoherentFrom
        (((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory ⋙ Dg.functor).obj K)
          m :=
      (totalDerivedExtensionScalars_preserves_pseudoCoherent g _).1 m (hK n α hα)
    exact (isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u} (R := R')
      (Dh.functor.obj K) m).1.1 ⟨n, β, polynomialPresentationBaseChange_surjective n α hα,
        isPseudoCoherentFrom_of_iso hP' (asIso (comparison.2.1.app K))⟩
  exact ⟨hfrom, fun hK m ↦ hfrom m (hK m)⟩
end PseudoCoherence
