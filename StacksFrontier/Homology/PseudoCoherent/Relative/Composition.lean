module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.Homology.PseudoCoherent.FiniteFree
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Relative pseudo-coherence along a composition of finite-type algebra maps

For a tower `R → A → B` of finite-type algebra maps in which `A` is pseudo-coherent relative to
`R`, an object of `D(B)` is pseudo-coherent relative to `A` exactly when it is pseudo-coherent
relative to `R`. So relative pseudo-coherence does not depend on how far down the tower the base
is taken, provided each step is relatively pseudo-coherent.

## Main results

* `PseudoCoherence.relativelyPseudoCoherent_iff_of_comp` (Stacks 067D).

## Implementation notes

Both sides are read off a single polynomial presentation, which tag 065H licenses. Presentations
of `A` over `R` and of `B` over `A` are combined into one presentation of `B` over `R` by
adjoining variables, and the two restrictions are compared through tag 064Z. The hypothesis that
064Z needs — that the intermediate polynomial algebra is pseudo-coherent as a module over the
smaller one — comes from flat base change along `P → MvPolynomial (Fin q) P`, which is tag 066C,
applied to `A` viewed as a relatively pseudo-coherent `P`-module.

Tags 064U, 064Z and 066C belong to Chapter 15 section 65 and are proved in
`StacksFrontier/Homology/PseudoCoherent/{Basic,ChangeOfRings}.lean`; this module cites them rather
than carrying a second copy. Tags 065H and 065I are proved in this directory, in
`Relative/Presentation.lean` and `Relative/Defs.lean`.

## References

* [The Stacks Project, Lemma 15.82.6 (067D)](https://stacks.math.columbia.edu/tag/067D)
-/

open CategoryTheory
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

private lemma isPseudoCoherentFrom_iff_of_iso
    {S : Type*} [Ring S] {X Y : DerivedCategory (ModuleCat.{u} S)} {m : ℤ} (e : X ≅ Y) :
    IsPseudoCoherentFrom X m ↔ IsPseudoCoherentFrom Y m :=
  ⟨fun h ↦ isPseudoCoherentFrom_of_iso h e,
    fun h ↦ isPseudoCoherentFrom_of_iso h e.symm⟩

private lemma isModulePseudoCoherent_restrictScalars_ringEquiv
    {R : Type u} {S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    IsModulePseudoCoherent (R := R)
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S)) := by
  let e' : R ≃ₗ[R] (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S) :=
    { e.toAddEquiv with map_smul' := fun r s ↦ e.map_mul r s }
  have := Module.Finite.equiv e'
  have := Module.Free.of_equiv e'
  exact StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free _

set_option backward.isDefEq.respectTransparency false in
/-- For an `R`-algebra `S` and an `R`-module `M`, the extension of scalars of `M` along
`algebraMap R S` is isomorphic, as an `S`-module, to the tensor product `S ⊗[R] M`. -/
noncomputable def extendScalarsAlgebraMapObjIso
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅
      ModuleCat.of S (TensorProduct R S M) := by
  have : SMulCommClass R S ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S S)) :=
    ⟨fun r s t ↦ mul_left_comm (algebraMap R S r) s (t : S)⟩
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { AddEquiv.refl S with map_smul' := fun r s ↦ (Algebra.smul_def (R := R) (A := S) r s).symm }
  let e' : (ModuleCat.extendScalars (algebraMap R S)).obj M ≃+ TensorProduct R S M :=
    (TensorProduct.congr e (LinearEquiv.refl R M)).toAddEquiv
  let l : (ModuleCat.extendScalars (algebraMap R S)).obj M ≃ₗ[S] TensorProduct R S M :=
    { e' with
      map_smul' := by
        change ∀ (s : S) (z : (ModuleCat.extendScalars (algebraMap R S)).obj M),
          e' (s • z) = s • e' z
        intro s z
        induction z using TensorProduct.induction_on with
        | zero =>
            calc
              e' (s • 0) = e' 0 := congrArg e' (smul_zero s)
              _ = 0 := e'.map_zero
              _ = s • e' 0 := by rw [e'.map_zero, smul_zero]
        | tmul t m =>
            change e' ((s • t) ⊗ₜ[R] m) = _
            simp [e', e, TensorProduct.smul_tmul']
        | add z z' hz hz' => simp only [smul_add, map_add, hz, hz'] }
  exact l.toModuleIso

private noncomputable def mvPolynomialTensorProductLinearEquiv
    {P : Type u} {A : Type u} [CommRing P] [CommRing A] [Algebra P A]
    (σ : Type*) : letI := (MvPolynomial.map (σ := σ) (algebraMap P A)).toAlgebra
    TensorProduct P (MvPolynomial σ P) A ≃ₗ[MvPolynomial σ P] MvPolynomial σ A := by
  letI := (MvPolynomial.map (σ := σ) (algebraMap P A)).toAlgebra
  let e := (Algebra.TensorProduct.comm P (MvPolynomial σ P) A).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv P A).toRingEquiv
  exact { e.toAddEquiv with
    map_smul' := by
      intro p z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul q a =>
        change e ((p * q) ⊗ₜ[P] a) = _
        have hp : algebraMap (MvPolynomial σ P) (MvPolynomial σ A) p =
            MvPolynomial.map (algebraMap P A) p := rfl
        simp [e, Algebra.smul_def, mul_left_comm, hp]
      | add a b ha hb =>
        simp only [smul_add]
        calc
          e (p • a + p • b) = e (p • a) + e (p • b) := map_add e _ _
          _ = p • e a + p • e b := by simpa using congrArg₂ (· + ·) ha hb
          _ = p • (e a + e b) := (smul_add p (e a) (e b)).symm
          _ = p • e (a + b) := by rw [map_add] }

private noncomputable def restrictScalarsCompIso
    {P : Type u} {S : Type u} {T : Type u}
    [Ring P] [Ring S] [Ring T]
    (f : P →+* S) (g : S →+* T) (h : P →+* T) (hh : h = g.comp f)
    (K : CochainComplex (ModuleCat.{u} T) ℤ) :
    DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.restrictScalars g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars h).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp' f g h hh).symm (ComplexShape.up ℤ)).app K)

private lemma isRelativelyPseudoCoherentFrom_iff_polynomialPresentation
    {P : Type u} {T : Type u} [CommRing P] [CommRing T] [Algebra P T]
    [Algebra.FiniteType P T] (K : CochainComplex (ModuleCat.{u} T) ℤ) (m : ℤ)
    (n : ℕ) (f : MvPolynomial (Fin n) P →ₐ[P] T) (hf : Function.Surjective f) :
    IsRelativelyPseudoCoherentFrom (R := P) (DerivedCategory.Q.obj K) m ↔
      IsPseudoCoherentFrom (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) m := by
  let F := ModuleCat.restrictScalars.{u} f.toRingHom
  show (∀ (n : ℕ) (f : MvPolynomial (Fin n) P →ₐ[P] T), Function.Surjective f →
    IsPseudoCoherentFrom
    ((ModuleCat.restrictScalars f.toRingHom).mapDerivedCategory.obj
      (DerivedCategory.Q.obj K)) m) ↔ _
  exact ⟨fun h ↦ isPseudoCoherentFrom_of_iso (h n f hf) (F.mapDerivedCategoryFactors.app K),
    fun h ↦ (isPseudoCoherentFrom_polynomialPresentation_independent
      (DerivedCategory.Q.obj K) m).1.mp ⟨n, f, hf,
        isPseudoCoherentFrom_of_iso h (F.mapDerivedCategoryFactors.app K).symm⟩⟩

/-- If `A` is pseudo-coherent as a `P`-module via `φ`, then `MvPolynomial (Fin q) A` is
pseudo-coherent as a module over `MvPolynomial (Fin q) P` via `MvPolynomial.map φ`. -/
private lemma isModulePseudoCoherent_mvPolynomial_map {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (q : ℕ)
    (h : IsModulePseudoCoherent (R := P) ((ModuleCat.restrictScalars.{u} φ).obj
      (ModuleCat.of A A))) :
    IsModulePseudoCoherent (R := MvPolynomial (Fin q) P)
      ((ModuleCat.restrictScalars (MvPolynomial.map (σ := Fin q) φ)).obj
        (ModuleCat.of (MvPolynomial (Fin q) A) (MvPolynomial (Fin q) A))) := by
  let : Algebra P A := φ.toAlgebra
  have hExt := (extensionScalars_preserves_pseudoCoherent
    (MvPolynomial.C : P →+* MvPolynomial (Fin q) P)
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat P (MvPolynomial (Fin q) P)))
    ((ModuleCat.restrictScalars.{u} φ).obj (ModuleCat.of A A))).2 h
  let := (MvPolynomial.map (σ := Fin q) (algebraMap P A)).toAlgebra
  let eLift : MvPolynomial (Fin q) A ≃ₗ[MvPolynomial (Fin q) P]
      (ModuleCat.restrictScalars (MvPolynomial.map (σ := Fin q) φ)).obj
        (ModuleCat.of (MvPolynomial (Fin q) A) (MvPolynomial (Fin q) A)) :=
    { AddEquiv.refl _ with map_smul' := fun _ _ ↦ rfl }
  exact IsPseudoCoherent.ofIso hExt ((DerivedCategory.singleFunctor _ 0).mapIso
    (extendScalarsAlgebraMapObjIso (R := P) (S := MvPolynomial (Fin q) P)
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) ≪≫
      ((mvPolynomialTensorProductLinearEquiv (P := P) (A := A) (Fin q)).trans eLift).toModuleIso))

private lemma relativelyPseudoCoherent_iff_of_comp_complex
    {R : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType A B]
    (hA : IsModuleRelativelyPseudoCoherent (R := R) (A := A) A)
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (m : ℤ) :
    letI : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (R := R) (S := A) (A := B) inferInstance inferInstance
    (IsRelativelyPseudoCoherentFrom (R := A) (DerivedCategory.Q.obj K) m ↔
      IsRelativelyPseudoCoherentFrom (R := R) (DerivedCategory.Q.obj K) m) ∧
    (IsRelativelyPseudoCoherent (R := A) (DerivedCategory.Q.obj K) ↔
      IsRelativelyPseudoCoherent (R := R) (DerivedCategory.Q.obj K)) := by
  let : Algebra.FiniteType R B :=
    Algebra.FiniteType.trans (R := R) (S := A) (A := B) inferInstance inferInstance
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  obtain ⟨q, β, hβ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let P := MvPolynomial (Fin n) R
  let S := MvPolynomial (Fin q) P
  let T := MvPolynomial (Fin q) A
  let f : S →+* T := MvPolynomial.map α.toRingHom
  let δ : S →ₐ[R] B := (β.restrictScalars R).comp (MvPolynomial.mapAlgHom α)
  have hf : Function.Surjective f := MvPolynomial.map_surjective α.toRingHom hα
  have hδ : Function.Surjective δ := hβ.comp hf
  let e : MvPolynomial (Fin (q + n)) R ≃ₐ[R] S :=
    (MvPolynomial.renameEquiv R (finSumFinEquiv (m := q) (n := n)).symm).trans
      (MvPolynomial.sumAlgEquiv R (Fin q) (Fin n))
  let γ : MvPolynomial (Fin (q + n)) R →ₐ[R] B := δ.comp e.toAlgHom
  have hγ : Function.Surjective γ := hδ.comp e.surjective
  have hT : IsModulePseudoCoherent (R := S)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of T T)) :=
    isModulePseudoCoherent_mvPolynomial_map α.toRingHom q <|
      (pseudoCoherent_iff_all ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj
        ((ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A A)))).mpr fun d ↦
      isPseudoCoherentFrom_of_iso (hA d n α hα)
        (((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategorySingleFunctor 0).app _)
  have main : ∀ d : ℤ,
      IsRelativelyPseudoCoherentFrom (R := A) (DerivedCategory.Q.obj K) d ↔
        IsRelativelyPseudoCoherentFrom (R := R) (DerivedCategory.Q.obj K) d := by
    intro d
    rw [isRelativelyPseudoCoherentFrom_iff_polynomialPresentation K d q β hβ,
      isRelativelyPseudoCoherentFrom_iff_polynomialPresentation K d (q + n) γ hγ]
    let L := ((ModuleCat.restrictScalars β.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    let M := ((ModuleCat.restrictScalars δ.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    exact (pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars.{_, _, u} f hT L d).1.trans <|
      (isPseudoCoherentFrom_iff_of_iso
        (restrictScalarsCompIso f β.toRingHom δ.toRingHom rfl K)).trans <|
      (pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars.{_, _, u}
        e.toRingEquiv.toRingHom
        (isModulePseudoCoherent_restrictScalars_ringEquiv e.toRingEquiv) M d).1.trans <|
      isPseudoCoherentFrom_iff_of_iso
        (restrictScalarsCompIso e.toRingEquiv.toRingHom δ.toRingHom γ.toRingHom rfl K)
  exact ⟨main m, forall_congr' main⟩

private lemma isRelativelyPseudoCoherentFrom_iff_of_iso
    {R : Type u} {B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] {K L : DerivedCategory (ModuleCat.{u} B)}
    (e : K ≅ L) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom (R := R) K m ↔
      IsRelativelyPseudoCoherentFrom (R := R) L m := by
  constructor <;> intro h n f hf
  · exact (isPseudoCoherentFrom_iff_of_iso
      ((ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory.mapIso e)).mp
        (h n f hf)
  · exact (isPseudoCoherentFrom_iff_of_iso
      ((ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory.mapIso e)).mpr
        (h n f hf)

/-- **Stacks 067D.** Relative pseudo-coherence is invariant under composition with a relatively
pseudo-coherent finite-type algebra, for every object of the derived category. -/
@[stacks 067D, sga "6 I 2.14" "(ii), affine case"]
public theorem relativelyPseudoCoherent_iff_of_comp
    {R : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType A B]
    (hA : IsModuleRelativelyPseudoCoherent (R := R) (A := A) A)
    (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ) :
    letI : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (R := R) (S := A) (A := B) inferInstance inferInstance
    (IsRelativelyPseudoCoherentFrom (R := A) K m ↔
      IsRelativelyPseudoCoherentFrom (R := R) K m) ∧
    (IsRelativelyPseudoCoherent (R := A) K ↔
      IsRelativelyPseudoCoherent (R := R) K) := by
  let : Algebra.FiniteType R B :=
    Algebra.FiniteType.trans (R := R) (S := A) (A := B) inferInstance inferInstance
  let L := (DerivedCategory.Q (C := ModuleCat.{u} B)).objPreimage K
  let e := (DerivedCategory.Q (C := ModuleCat.{u} B)).objObjPreimageIso K
  have main (d : ℤ) : IsRelativelyPseudoCoherentFrom (R := A) K d ↔
      IsRelativelyPseudoCoherentFrom (R := R) K d :=
    (isRelativelyPseudoCoherentFrom_iff_of_iso (R := A) e d).symm.trans
      ((relativelyPseudoCoherent_iff_of_comp_complex hA L d).1.trans
        (isRelativelyPseudoCoherentFrom_iff_of_iso (R := R) e d))
  exact ⟨main m, forall_congr' main⟩

end PseudoCoherence
