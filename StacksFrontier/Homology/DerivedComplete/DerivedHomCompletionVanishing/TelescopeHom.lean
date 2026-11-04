module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Homology.DerivedCategory.Telescope
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction

/-!
# The Hom complex out of the telescope resolution

This part defines `DerivedHomAway.derivedHomFromAway`, the object `RHom_A(A_f, K)`, and
identifies the Hom complex out of the two-term telescope resolution of `A_f` into a complex `I`
with a complex built from pairs of sequences in `I`, computing its differentials.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace DerivedHomAway

local instance (A : Type u) [CommRing A] :
    HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
  moduleCat_hasExactLimitsOfShape_discrete.{u} A ℕ

/-- The functorial derived-Hom object `RHom_A(A_f, K)`. -/
public noncomputable abbrev derivedHomFromAway (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    DerivedCategory (ModuleCat.{u} A) :=
  (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
    (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (Localization.Away f))), K)

local instance (A : Type u) [CommRing A] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

private noncomputable def homTelescopeIso
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (I : CochainComplex (ModuleCat.{u} A) ℤ) [I.IsKInjective]
    (eI : K ≅ DerivedCategory.Q.obj I) :
    DerivedHomAway.derivedHomFromAway A f K ≅
      DerivedCategory.Q.obj
        (CochainComplex.HomComplexR A (telescopeResolution A f) I) := by
  let aug := telescopeResolutionAugmentation A f
  let : QuasiIso aug := telescopeResolutionAugmentation_quasiIso A f
  let eK := (asIso (DerivedCategory.Q.map aug)).symm
  exact (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
    (eK.symm.op.prod eI) ≪≫
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).homIso (telescopeResolution A f) I

private theorem telescopeHom_d_zero
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) :
    (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom z).v
        0 (n + 1) (by omega) =
      z.v 0 n (by omega) ≫ I.d n (n + 1) := by
  show (δ n (n + 1) (z : Cochain (telescopeResolution A f) I n)).v
    0 (n + 1) (by omega) = _
  rw [δ_v n (n + 1) rfl z 0 (n + 1) (by omega) n 1 (by omega) rfl]
  have hd0 : (telescopeResolution A f).d 0 1 = 0 :=
    HomologicalComplex.double_d_eq_zero₀ _ _ 0 1 (by norm_num)
  rw [hd0, CategoryTheory.Limits.zero_comp, smul_zero, add_zero]

private theorem telescopeHom_d_negOne
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) :
    (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom z).v
        (-1) n (by omega) =
      z.v (-1) (n - 1) (by omega) ≫ I.d (n - 1) n +
        (n + 1).negOnePow •
          (telescopeResolution A f).d (-1) 0 ≫ z.v 0 n (by omega) := by
  show (δ n (n + 1) (z : Cochain (telescopeResolution A f) I n)).v
    (-1) n (by omega) = _
  rw [δ_v n (n + 1) rfl z (-1) n (by omega) (n - 1) 0 (by omega) rfl]

private noncomputable def telescopeHom_zero_lin
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) :
    (ℕ →₀ A) →ₗ[A] I.X n := by
  let e : (telescopeResolution A f).X 0 ≅ ModuleCat.of A (ℕ →₀ A) :=
    HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (telescopeDifferential A f))
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by norm_num)
  exact (e.inv ≫ z.v 0 n (by omega)).hom

private noncomputable def telescopeHom_neg_lin
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) :
    (ℕ →₀ A) →ₗ[A] I.X (n - 1) := by
  let e : (telescopeResolution A f).X (-1) ≅ ModuleCat.of A (ℕ →₀ A) :=
    HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (telescopeDifferential A f))
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
  exact (e.inv ≫ z.v (-1) (n - 1) (by omega)).hom

private noncomputable def telescopeHom_cross_lin
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) :
    (ℕ →₀ A) →ₗ[A] I.X n := by
  let e : (telescopeResolution A f).X (-1) ≅ ModuleCat.of A (ℕ →₀ A) :=
    HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (telescopeDifferential A f))
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
  exact (e.inv ≫ (telescopeResolution A f).d (-1) 0 ≫ z.v 0 n (by omega)).hom

private theorem telescopeDouble_diff_iso (A : Type u) [CommRing A] (f : A) :
    (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (telescopeDifferential A f))
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)).inv ≫
      (telescopeResolution A f).d (-1) 0 =
    ModuleCat.ofHom (telescopeDifferential A f) ≫
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (telescopeDifferential A f))
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by norm_num)).inv := by
  unfold telescopeResolution
  rw [HomologicalComplex.double_d (ModuleCat.ofHom (telescopeDifferential A f))
    (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by norm_num)]
  simp

private theorem telescopeHom_cross_term
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) (index : ℕ) :
    freeHomProductEquiv A (I.X n)
      ((telescopeHom_zero_lin A f I n z).comp (telescopeDifferential A f)) index =
      freeHomProductEquiv A (I.X n) (telescopeHom_zero_lin A f I n z) index -
        f • freeHomProductEquiv A (I.X n) (telescopeHom_zero_lin A f I n z) (index + 1) := by
  exact freeHomProductEquiv_precompose_telescope A (I.X n) f
    (telescopeHom_zero_lin A f I n z) index

private theorem telescopeCochain_ext
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z z' : Cochain (telescopeResolution A f) I n)
    (hneg : z.v (-1) (n - 1) (by omega) = z'.v (-1) (n - 1) (by omega))
    (hzero : z.v 0 n (by omega) = z'.v 0 n (by omega)) : z = z' := by
  apply Cochain.ext
  intro p q hpq
  by_cases hpneg : p = -1
  · subst p
    have hq : q = n - 1 := by omega
    subst q
    have ht : (⟨-1, -1 + n, by omega⟩ : Triplet n) =
        ⟨-1, n - 1, by omega⟩ := by
      congr 1
    show z ⟨-1, -1 + n, by omega⟩ = z' ⟨-1, -1 + n, by omega⟩
    rw [ht]
    exact hneg
  by_cases hpzero : p = 0
  · subst p
    have hq : q = n := by omega
    subst q
    have ht : (⟨0, 0 + n, by omega⟩ : Triplet n) =
        ⟨0, n, by omega⟩ := by
      congr 1
    show z ⟨0, 0 + n, by omega⟩ = z' ⟨0, 0 + n, by omega⟩
    rw [ht]
    exact hzero
  exact (HomologicalComplex.isZero_double_X
    (ModuleCat.ofHom (telescopeDifferential A f))
    (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) p hpneg hpzero).eq_of_src _ _

private theorem telescopeHom_two_component_injective
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    Function.Injective (fun z : (HomComplexR A (telescopeResolution A f) I).X n =>
      (telescopeHom_neg_lin A f I n z, telescopeHom_zero_lin A f I n z)) := by
  intro z z' h
  have hneg : telescopeHom_neg_lin A f I n z = telescopeHom_neg_lin A f I n z' :=
    congrArg Prod.fst h
  have hzero : telescopeHom_zero_lin A f I n z = telescopeHom_zero_lin A f I n z' :=
    congrArg Prod.snd h
  have hneg' : (z : Cochain (telescopeResolution A f) I n).v (-1) (n - 1) (by omega) =
      (z' : Cochain (telescopeResolution A f) I n).v (-1) (n - 1) (by omega) :=
    (cancel_epi (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (telescopeDifferential A f))
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)).inv).1 (ModuleCat.hom_ext hneg)
  have hzero' : (z : Cochain (telescopeResolution A f) I n).v 0 n (by omega) =
      (z' : Cochain (telescopeResolution A f) I n).v 0 n (by omega) :=
    (cancel_epi (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (telescopeDifferential A f))
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by norm_num)).inv).1
      (ModuleCat.hom_ext hzero)
  exact telescopeCochain_ext A f I n z z' hneg' hzero'

private theorem telescopeHom_two_component_surjective
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    Function.Surjective (fun z : (HomComplexR A (telescopeResolution A f) I).X n =>
      (telescopeHom_neg_lin A f I n z, telescopeHom_zero_lin A f I n z)) := by
  intro ⟨a, b⟩
  let eNeg : (telescopeResolution A f).X (-1) ≅ ModuleCat.of A (ℕ →₀ A) :=
    HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (telescopeDifferential A f))
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
  let eZero : (telescopeResolution A f).X 0 ≅ ModuleCat.of A (ℕ →₀ A) :=
    HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (telescopeDifferential A f))
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by norm_num)
  let tNeg : Triplet n := ⟨-1, n - 1, by omega⟩
  let tZero : Triplet n := ⟨0, n, by omega⟩
  let z : Cochain (telescopeResolution A f) I n := fun t => by
    by_cases hNeg : t = tNeg
    · subst t
      exact eNeg.hom ≫ ModuleCat.ofHom a
    by_cases hZero : t = tZero
    · subst t
      exact eZero.hom ≫ ModuleCat.ofHom b
    exact 0
  refine ⟨z, Prod.ext ?_ ?_⟩
  · show (eNeg.inv ≫ z.v (-1) (n - 1) (by omega)).hom = a
    simp [z, Cochain.v, tNeg, tZero, ← Category.assoc]
  · show (eZero.inv ≫ z.v 0 n (by omega)).hom = b
    simp [z, Cochain.v, tNeg, tZero, ← Category.assoc]

private noncomputable def telescopeHom_two_component_linear
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (HomComplexR A (telescopeResolution A f) I).X n →ₗ[A]
      (((ℕ →₀ A) →ₗ[A] I.X (n - 1)) × ((ℕ →₀ A) →ₗ[A] I.X n)) where
  toFun z := (telescopeHom_neg_lin A f I n z, telescopeHom_zero_lin A f I n z)
  map_add' z z' := by
    apply Prod.ext
    · change telescopeHom_neg_lin A f I n (z + z') =
        telescopeHom_neg_lin A f I n z + telescopeHom_neg_lin A f I n z'
      unfold telescopeHom_neg_lin
      rfl
    · change telescopeHom_zero_lin A f I n (z + z') =
        telescopeHom_zero_lin A f I n z + telescopeHom_zero_lin A f I n z'
      unfold telescopeHom_zero_lin
      rfl
  map_smul' scalar z := by
    apply Prod.ext
    · change telescopeHom_neg_lin A f I n (scalar • z) =
        scalar • telescopeHom_neg_lin A f I n z
      unfold telescopeHom_neg_lin
      rfl
    · change telescopeHom_zero_lin A f I n (scalar • z) =
        scalar • telescopeHom_zero_lin A f I n z
      unfold telescopeHom_zero_lin
      rfl

private noncomputable def telescopeHom_two_component_equiv
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (HomComplexR A (telescopeResolution A f) I).X n ≃ₗ[A]
      (((ℕ →₀ A) →ₗ[A] I.X (n - 1)) × ((ℕ →₀ A) →ₗ[A] I.X n)) :=
  LinearEquiv.ofBijective (telescopeHom_two_component_linear A f I n)
    ⟨telescopeHom_two_component_injective A f I n,
      telescopeHom_two_component_surjective A f I n⟩

private noncomputable def telescopeHom_product_equiv
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (HomComplexR A (telescopeResolution A f) I).X n ≃ₗ[A]
      ((ℕ → I.X (n - 1)) × (ℕ → I.X n)) :=
  (telescopeHom_two_component_equiv A f I n).trans
    ((freeHomProductEquiv A (I.X (n - 1))).prodCongr
      (freeHomProductEquiv A (I.X n)))

private theorem telescopeHom_zero_differential
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) :
    telescopeHom_zero_lin A f I (n + 1)
      (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom z) =
      (I.d n (n + 1)).hom.comp (telescopeHom_zero_lin A f I n z) := by
  let e : (telescopeResolution A f).X 0 ≅ ModuleCat.of A (ℕ →₀ A) :=
    HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (telescopeDifferential A f))
      (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by norm_num)
  show (e.inv ≫ (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom z).v
      0 (n + 1) (by omega)).hom =
    (e.inv ≫ z.v 0 n (by omega) ≫ I.d n (n + 1)).hom
  rw [telescopeHom_d_zero]

private theorem telescopeHom_neg_differential_morphism
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (eNeg : (telescopeResolution A f).X (-1) ≅ ModuleCat.of A (ℕ →₀ A))
    (eZero : (telescopeResolution A f).X 0 ≅ ModuleCat.of A (ℕ →₀ A))
    (hDouble : eNeg.inv ≫ (telescopeResolution A f).d (-1) 0 =
      ModuleCat.ofHom (telescopeDifferential A f) ≫ eZero.inv)
    (z : Cochain (telescopeResolution A f) I n) :
    eNeg.inv ≫ (δ n (n + 1) z).v (-1) n (by omega) =
    (eNeg.inv ≫ z.v (-1) (n - 1) (by omega) ≫ I.d (n - 1) n) +
      (n + 1).negOnePow •
        (ModuleCat.ofHom (telescopeDifferential A f) ≫ eZero.inv ≫
          z.v 0 n (by omega)) := by
  rw [δ_v n (n + 1) rfl z (-1) n (by omega) (n - 1) 0 (by omega) rfl]
  rw [Preadditive.comp_add]
  congr 1
  rw [Linear.comp_units_smul, ← Category.assoc, hDouble, Category.assoc]

private theorem telescopeHom_neg_differential_index
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (eNeg : (telescopeResolution A f).X (-1) ≅ ModuleCat.of A (ℕ →₀ A))
    (eZero : (telescopeResolution A f).X 0 ≅ ModuleCat.of A (ℕ →₀ A))
    (hDouble : eNeg.inv ≫ (telescopeResolution A f).d (-1) 0 =
      ModuleCat.ofHom (telescopeDifferential A f) ≫ eZero.inv)
    (z : Cochain (telescopeResolution A f) I n) (index : ℕ) :
    (eNeg.inv ≫ (δ n (n + 1) z).v (-1) n (by omega)).hom
      (Finsupp.single index 1) =
    (I.d (n - 1) n).hom
      ((eNeg.inv ≫ z.v (-1) (n - 1) (by omega)).hom (Finsupp.single index 1)) +
      (n + 1).negOnePow •
        ((eZero.inv ≫ z.v 0 n (by omega)).hom (Finsupp.single index 1) -
          f • (eZero.inv ≫ z.v 0 n (by omega)).hom
            (Finsupp.single (index + 1) 1)) := by
  have h := congrArg (fun φ : ModuleCat.of A (ℕ →₀ A) ⟶ I.X n =>
    φ.hom (Finsupp.single index 1))
    (telescopeHom_neg_differential_morphism A f I n eNeg eZero hDouble z)
  simp only [Int.reduceNeg, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_add, ModuleCat.hom_smul, ConcreteCategory.hom_ofHom, LinearMap.add_apply,
    LinearMap.smul_apply, telescopeDifferential_single, mul_one, map_sub] at h
  rw [← Finsupp.smul_single_one (index + 1) f] at h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, map_smul] using h

private noncomputable def telescopeHom_component_iso
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (HomComplexR A (telescopeResolution A f) I).X n ≅
      ModuleCat.of A ((ℕ → I.X (n - 1)) × (ℕ → I.X n)) :=
  (telescopeHom_product_equiv A f I n).toModuleIso

private noncomputable def telescopeHom_transport_complex
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ := by
  let source := HomComplexR A (telescopeResolution A f) I
  let component n := telescopeHom_component_iso A f I n
  exact CochainComplex.of
    (fun n => ModuleCat.of A ((ℕ → I.X (n - 1)) × (ℕ → I.X n)))
    (fun n => (component n).inv ≫ source.d n (n + 1) ≫ (component (n + 1)).hom)
    (fun n => by simp [Category.assoc])

private noncomputable def telescopeHom_transport_iso
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    HomComplexR A (telescopeResolution A f) I ≅
      telescopeHom_transport_complex A f I := by
  let source := HomComplexR A (telescopeResolution A f) I
  let component n := telescopeHom_component_iso A f I n
  refine HomologicalComplex.Hom.isoOfComponents (fun n => component n) ?_
  intro i j hij
  simp only [ComplexShape.up_Rel] at hij
  subst j
  dsimp only [component, source]
  simp only [telescopeHom_transport_complex, CochainComplex.of_d]
  simp

private theorem telescopeHom_pair_second_differential
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) (index : ℕ) :
    ((telescopeHom_product_equiv A f I (n + 1))
      (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom z)).2 index =
      (I.d n (n + 1)).hom ((telescopeHom_product_equiv A f I n z).2 index) := by
  show freeHomProductEquiv A (I.X (n + 1))
      (telescopeHom_zero_lin A f I (n + 1)
        (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom z))
      index =
    (I.d n (n + 1)).hom
      (freeHomProductEquiv A (I.X n) (telescopeHom_zero_lin A f I n z) index)
  rw [telescopeHom_zero_differential]
  rfl

private def telescopeHom_next_index_iso
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ModuleCat.of A ((ℕ → I.X (n + 1 - 1)) × (ℕ → I.X (n + 1))) ≅
      ModuleCat.of A ((ℕ → I.X n) × (ℕ → I.X (n + 1))) :=
  eqToIso (congrArg
    (fun degree : ℤ => ModuleCat.of A ((ℕ → I.X degree) × (ℕ → I.X (n + 1))))
    (show n + 1 - 1 = n by omega))

private theorem eqToIso_sequence_pair_fst
    (A : Type u) [CommRing A]
    {X Y Z : ModuleCat.{u} A} (h : X = Y)
    (pair : (ℕ → X) × (ℕ → Z)) (index : ℕ) :
    ((eqToIso (congrArg
      (fun M : ModuleCat.{u} A => ModuleCat.of A ((ℕ → M) × (ℕ → Z))) h)).hom pair).1
      index =
        cast (congrArg (fun M : ModuleCat.{u} A => (M : Type u)) h)
          (pair.1 index) := by
  cases h
  rfl

private theorem telescopeHom_next_index_iso_fst
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (pair : (ℕ → I.X (n + 1 - 1)) × (ℕ → I.X (n + 1))) (index : ℕ) :
    ((telescopeHom_next_index_iso A I n).hom pair).1 index =
      cast (congrArg (fun M : ModuleCat.{u} A => (M : Type u))
        (congrArg I.X (show n + 1 - 1 = n by omega))) (pair.1 index) := by
  unfold telescopeHom_next_index_iso
  exact eqToIso_sequence_pair_fst A
    (congrArg I.X (show n + 1 - 1 = n by omega)) pair index

private theorem eqToIso_sequence_pair_snd
    (A : Type u) [CommRing A]
    {X Y Z : ModuleCat.{u} A} (h : X = Y)
    (pair : (ℕ → X) × (ℕ → Z)) (index : ℕ) :
    ((eqToIso (congrArg
      (fun M : ModuleCat.{u} A => ModuleCat.of A ((ℕ → M) × (ℕ → Z))) h)).hom pair).2
      index = pair.2 index := by
  cases h
  rfl

private theorem telescopeHom_next_index_iso_snd
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (pair : (ℕ → I.X (n + 1 - 1)) × (ℕ → I.X (n + 1))) (index : ℕ) :
    ((telescopeHom_next_index_iso A I n).hom pair).2 index = pair.2 index := by
  unfold telescopeHom_next_index_iso
  exact eqToIso_sequence_pair_snd A
    (congrArg I.X (show n + 1 - 1 = n by omega)) pair index

private theorem telescopeCochain_v_cast_apply
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n q q' : ℤ)
    (hq : -1 + (n + 1) = q) (hq' : -1 + (n + 1) = q')
    (h : q = q') (w : Cochain (telescopeResolution A f) I (n + 1))
    (x : (telescopeResolution A f).X (-1)) :
    cast (congrArg (fun degree : ℤ => (I.X degree : Type u)) h)
      ((w.v (-1) q hq).hom x) = (w.v (-1) q' hq').hom x := by
  cases h
  rfl

private theorem telescopeHom_neg_index_cast
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (w : (HomComplexR A (telescopeResolution A f) I).X (n + 1))
    (index : ℕ) :
    cast (congrArg (fun M : ModuleCat.{u} A => (M : Type u))
      (congrArg I.X (show n + 1 - 1 = n by omega)))
      (freeHomProductEquiv A (I.X (n + 1 - 1))
        (telescopeHom_neg_lin A f I (n + 1) w) index) =
      ((HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (telescopeDifferential A f))
          (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)).inv ≫
        (w : Cochain (telescopeResolution A f) I (n + 1)).v (-1) n (by omega)).hom
        (Finsupp.single index 1) := by
  let eNeg := HomologicalComplex.doubleXIso₀
    (ModuleCat.ofHom (telescopeDifferential A f))
    (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
  show cast (congrArg (fun degree : ℤ => (I.X degree : Type u))
        (show n + 1 - 1 = n by omega))
      (((w : Cochain (telescopeResolution A f) I (n + 1)).v (-1)
        (n + 1 - 1) (by omega)).hom (eNeg.inv.hom (Finsupp.single index 1))) =
      ((w : Cochain (telescopeResolution A f) I (n + 1)).v (-1) n
        (by omega)).hom (eNeg.inv.hom (Finsupp.single index 1))
  exact telescopeCochain_v_cast_apply A f I n (n + 1 - 1) n
    (by omega) (by omega) (by omega) (w : Cochain _ I _) _

private theorem telescopeHom_pair_first_differential_normalized
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) (index : ℕ) :
    ((telescopeHom_next_index_iso A I n).hom
      ((telescopeHom_product_equiv A f I (n + 1))
        (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom z))).1 index =
    (I.d (n - 1) n).hom ((telescopeHom_product_equiv A f I n z).1 index) +
      (n + 1).negOnePow •
        ((telescopeHom_product_equiv A f I n z).2 index -
          f • (telescopeHom_product_equiv A f I n z).2 (index + 1)) := by
  rw [telescopeHom_next_index_iso_fst]
  show cast (congrArg (fun M : ModuleCat.{u} A => (M : Type u))
      (congrArg I.X (show n + 1 - 1 = n by omega)))
      (freeHomProductEquiv A (I.X (n + 1 - 1))
        (telescopeHom_neg_lin A f I (n + 1)
          (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom z)) index) = _
  rw [telescopeHom_neg_index_cast]
  let eNeg := HomologicalComplex.doubleXIso₀
    (ModuleCat.ofHom (telescopeDifferential A f))
    (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
  let eZero := HomologicalComplex.doubleXIso₁
    (ModuleCat.ofHom (telescopeDifferential A f))
    (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by norm_num)
  have h := telescopeHom_neg_differential_index A f I n eNeg eZero
    (telescopeDouble_diff_iso A f) (z : Cochain (telescopeResolution A f) I n) index
  show (eNeg.inv ≫ (δ n (n + 1) (z : Cochain (telescopeResolution A f) I n)).v
      (-1) n (by omega)).hom (Finsupp.single index 1) =
    (I.d (n - 1) n).hom
      ((eNeg.inv ≫ (z : Cochain (telescopeResolution A f) I n).v (-1) (n - 1)
        (by omega)).hom (Finsupp.single index 1)) +
      (n + 1).negOnePow •
        ((eZero.inv ≫ (z : Cochain (telescopeResolution A f) I n).v 0 n
          (by omega)).hom (Finsupp.single index 1) -
          f • (eZero.inv ≫ (z : Cochain (telescopeResolution A f) I n).v 0 n
            (by omega)).hom (Finsupp.single (index + 1) 1))
  exact h

end DerivedHomAway

end
