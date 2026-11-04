module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFullyFaithful
public import StacksFrontier.Algebra.DifferentialGraded.Module.WeakGeneratorIsoCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.DirectImage
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.StructureSheafPullback
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.KoszulQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.CategoryTheory.Adjunction.UnitCommutativeEnd
public import StacksFrontier.CategoryTheory.Triangulated.FullSubcategoryGenerator

/-!
# The twisted inverse image of the structure sheaf along `P^n_A → Spec A`

Let `A` be a ring, `X = P^n_A = Proj A[T₀, …, Tₙ]`, `f : X ⟶ Spec A` the structure morphism and
`a` the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec A})`. Then
`a(𝒪_{Spec A}) ≅ 𝒪_X(-n-1)[n]`. This is the content of [Stacks, Tag 0A9W] for the trivial
bundle over an affine base.

The proof is the source's. `Rf_*(𝒪_X(-n-1)[n]) ≅ 𝒪_{Spec A}`, and the adjoint `c` of such an
isomorphism is tested against the generators `𝒪_X, 𝒪_X(-1), …, 𝒪_X(-n)` of `D_QCoh(𝒪_X)`
([Stacks, Tag 0A9V]). Against `𝒪_X(-i)`, `1 ≤ i ≤ n`, both sides vanish, because
`Rf_* 𝒪_X(d) = 0` for `-n ≤ d ≤ -1`. Against `𝒪_X = Lf^* 𝒪_{Spec A}` the map is bijective
because the unit `𝒪_{Spec A} ⟶ Rf_* Lf^* 𝒪_{Spec A}` is invertible: it is split by the counit,
and the endomorphisms of `𝒪_{Spec A}` commute.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ExampleGenerator
  (isZero_of_quasiCoherentHomology_of_forall_hom_twistSum_eq_zero)

universe u

namespace Stacks.Duality.ProjectiveSpace

/-! ### Vanishing of all morphisms, transported -/

section Vanishing

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

/-- All morphisms `a ⟶ b` vanish if all morphisms between isomorphic objects do. -/
theorem forall_eq_zero_of_iso {a b a' b' : C} (e₁ : a ≅ a') (e₂ : b ≅ b')
    (h : ∀ g : a' ⟶ b', g = 0) (g : a ⟶ b) : g = 0 := by
  have : g = e₁.hom ≫ (e₁.inv ≫ g ≫ e₂.hom) ≫ e₂.inv := by simp
  rw [this, h (e₁.inv ≫ g ≫ e₂.hom), zero_comp, comp_zero]

/-- All morphisms `a ⟶ b` vanish if all morphisms `F a ⟶ F b` do, for `F` faithful. -/
theorem forall_eq_zero_of_faithful (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms]
    {a b : C} (h : ∀ g : F.obj a ⟶ F.obj b, g = 0) (g : a ⟶ b) : g = 0 :=
  F.map_injective (by rw [h (F.map g), F.map_zero])

/-- All morphisms `L N ⟶ M` vanish if all morphisms `N ⟶ R M` do, for `L ⊣ R`. -/
theorem forall_eq_zero_of_adjunction {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
    [L.PreservesZeroMorphisms] {N : D} {M : C} (h : ∀ g : N ⟶ R.obj M, g = 0)
    (g : L.obj N ⟶ M) : g = 0 := by
  rw [← (adj.homEquiv N M).symm_apply_apply g, h (adj.homEquiv N M g),
    Adjunction.homEquiv_counit, L.map_zero, zero_comp]

/-- All morphisms `N ⟶ R M` vanish if all morphisms `L N ⟶ M` do, for `L ⊣ R`. -/
theorem forall_eq_zero_of_adjunction' {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
    [R.PreservesZeroMorphisms] {N : D} {M : C} (h : ∀ g : L.obj N ⟶ M, g = 0)
    (g : N ⟶ R.obj M) : g = 0 := by
  rw [← (adj.homEquiv N M).apply_symm_apply g, h ((adj.homEquiv N M).symm g),
    Adjunction.homEquiv_unit, R.map_zero, comp_zero]

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).PreservesZeroMorphisms]

/-- All morphisms `a⟦p⟧ ⟶ b` vanish if all morphisms `a ⟶ b⟦-p⟧` do. -/
theorem forall_eq_zero_of_shift {a b : C} (p : ℤ)
    (h : ∀ g : a ⟶ b⟦-p⟧, g = 0) (g : a⟦p⟧ ⟶ b) : g = 0 :=
  forall_eq_zero_of_faithful (shiftFunctor C (-p))
    (forall_eq_zero_of_iso ((shiftFunctorCompIsoId C p (-p) (add_neg_cancel p)).app a)
      (Iso.refl _) h) g

end Vanishing

section Bijective

variable {C D : Type*} [Category C] [Category D]

/-- Precomposition with an isomorphism `e : P ≅ P'` is bijective on morphisms into `K`. -/
private theorem bijective_precomp_hom {P P' : C} (e : P ≅ P') (K : C) :
    Function.Bijective (fun f : P' ⟶ K => e.hom ≫ f) :=
  ⟨fun x y h => by simpa using congrArg (e.inv ≫ ·) h, fun g => ⟨e.inv ≫ g, by simp⟩⟩

/-- Bijectivity of `f ↦ f ≫ b` on morphisms out of `P` depends on `P` only up to isomorphism. -/
theorem bijective_comp_of_iso {P P' K X : C} (e : P ≅ P') (b : K ⟶ X)
    (h : Function.Bijective (fun f : P' ⟶ K => f ≫ b)) :
    Function.Bijective (fun f : P ⟶ K => f ≫ b) := by
  refine (Function.Bijective.of_comp_iff (fun f : P ⟶ K => f ≫ b)
    (bijective_precomp_hom e K)).1 ?_
  convert (bijective_precomp_hom e X).comp h using 1
  exact funext fun f => Category.assoc ..

/-- Bijectivity of a functor on morphisms out of `P` depends on `P` only up to isomorphism. -/
theorem bijective_map_of_iso (R : C ⥤ D) {P P' : C} (K : C) (e : P ≅ P')
    (h : Function.Bijective (fun f : P' ⟶ K => R.map f)) :
    Function.Bijective (fun f : P ⟶ K => R.map f) := by
  refine (Function.Bijective.of_comp_iff (fun f : P ⟶ K => R.map f)
    (bijective_precomp_hom e K)).1 ?_
  convert (bijective_precomp_hom (R.mapIso e) _).comp h using 1
  exact funext fun f => R.map_comp ..

end Bijective

/-! ### Projective space -/

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (n : ℕ)

local notation "𝐏" => AlgebraicGeometry.Proj (polyGrading A n)

/-- `𝒪(d)` on `P^n_A` placed in degree zero of `D(𝒪)`. -/
abbrev twistD (d : ℤ) : DerivedCategory (𝐏).Modules :=
  (DerivedCategory.singleFunctor _ 0).obj (twist A n d)

/-- Tensoring by `𝒪(1)` on `P^n_A`. -/
abbrev twistFunctor : (𝐏).Modules ⥤ (𝐏).Modules :=
  Stacks.AlgebraicGeometry.ProjTwistPowers.twistRight (polyGrading A n)

/-- Tensoring by `𝒪(1)` is an autoequivalence of the `𝒪`-modules on `P^n_A`. -/
instance isEquivalence_twistFunctor : (twistFunctor A n).IsEquivalence :=
  Stacks.AlgebraicGeometry.ProjTwistPowers.isEquivalence_twistRight _
    (Stacks.AlgebraicGeometry.ProjKoszulComplex.adjoin_degree_one_polyGrading A n)

/-- Tensoring by `𝒪(1)` is additive. -/
instance additive_twistFunctor : (twistFunctor A n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `𝒪(i) ⟶ 𝒪(j)[q]` all vanish as soon as `𝒪(i+1) ⟶ 𝒪(j+1)[q]` all vanish: tensoring by `𝒪(1)`
is an autoequivalence of `D(𝒪)` sending `𝒪(d)` to `𝒪(d+1)`. -/
theorem forall_eq_zero_twist_of_succ (i j q : ℤ)
    (h : ∀ g : twistD A n (i + 1) ⟶ (twistD A n (j + 1))⟦q⟧, g = 0)
    (g : twistD A n i ⟶ (twistD A n j)⟦q⟧) : g = 0 := by
  let T := (twistFunctor A n).mapDerivedCategory
  have : T.IsEquivalence := Stacks.Cohomology.isEquivalence_mapDerivedCategory _
  let e : ∀ d : ℤ, T.obj (twistD A n d) ≅ twistD A n (d + 1) := fun d =>
    ((twistFunctor A n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (Stacks.AlgebraicGeometry.ProjTwistPowers.twistMulIso _
          (Stacks.AlgebraicGeometry.ProjKoszulComplex.adjoin_degree_one_polyGrading A n) d)
  exact forall_eq_zero_of_faithful T (forall_eq_zero_of_iso (e i)
    ((T.commShiftIso q).app _ ≪≫ (shiftFunctor _ q).mapIso (e j)) h) g

/-- `𝒪(i) ⟶ 𝒪(j)[q]` all vanish as soon as `𝒪(i+k) ⟶ 𝒪(j+k)[q]` all vanish. -/
theorem forall_eq_zero_twist_of_add (q : ℤ) (k : ℕ) (i j i' j' : ℤ) (hi : i' = i + k)
    (hj : j' = j + k) (h : ∀ g : twistD A n i' ⟶ (twistD A n j')⟦q⟧, g = 0)
    (g : twistD A n i ⟶ (twistD A n j)⟦q⟧) : g = 0 := by
  induction k generalizing i j with
  | zero =>
    obtain rfl : i' = i := by omega
    obtain rfl : j' = j := by omega
    exact h g
  | succ k ih =>
    exact forall_eq_zero_twist_of_succ A n i j q
      (ih (i + 1) (j + 1) (by push_cast at hi; omega) (by push_cast at hj; omega)) g

/-! ### The twists `𝒪(-1), …, 𝒪(-n)` against `𝒪(-n-1)[n]` and against `a(𝒪)` -/

/-- **`Hom(𝒪, 𝒪(d)[q]) = 0` for `-n ≤ d ≤ -1`**: `𝒪_X = Lf^*𝒪_{Spec A}` and `Rf_* 𝒪(d) = 0`. -/
theorem forall_eq_zero_twist_zero (d : ℤ) (h₁ : -(n : ℤ) ≤ d) (h₂ : d < 0) (q : ℤ)
    (g : twistD A n 0 ⟶ (twistD A n d)⟦q⟧) : g = 0 := by
  have : (derivedPullback (projStructureMorphism A n)).IsLeftAdjoint :=
    (derivedAdjunction (projStructureMorphism A n)).isLeftAdjoint
  let e₀ : twist A n 0 ≅ SheafOfModules.unit (𝐏).ringCatSheaf :=
    Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading A n)
  refine forall_eq_zero_of_iso ((DerivedCategory.singleFunctor (𝐏).Modules 0).mapIso e₀ ≪≫
      (derivedPullbackStructureSheafIso (projStructureMorphism A n)).symm) (Iso.refl _) ?_ g
  exact forall_eq_zero_of_adjunction (derivedAdjunction (projStructureMorphism A n)) fun _ =>
    (((shiftFunctor _ q).map_isZero (isZero_derivedPushforward_twist A n d h₁ h₂ 0)).of_iso
      (((derivedPushforward (projStructureMorphism A n)).commShiftIso q).app _)).eq_of_tgt _ _

/-- **`Hom(𝒪(-i)[p], 𝒪(-n-1)[n]) = 0` for `1 ≤ i ≤ n`.** -/
theorem forall_eq_zero_twist_top (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) (p : ℤ)
    (g : (twistD A n (-(i : ℤ)))⟦p⟧ ⟶ (twistD A n (-(n : ℤ) - 1))⟦(n : ℤ)⟧) : g = 0 :=
  forall_eq_zero_of_shift p (fun g' => forall_eq_zero_of_iso (Iso.refl _)
    ((shiftFunctorAdd' _ (n : ℤ) (-p) (n - p) (by ring)).symm.app _)
    (forall_eq_zero_twist_of_add A n ((n : ℤ) - p) i (-(i : ℤ)) (-(n : ℤ) - 1) 0
      (-(n : ℤ) - 1 + i) (by ring) rfl
      (forall_eq_zero_twist_zero A n _ (by omega) (by omega) _)) g') g

/-! ### `D_QCoh` of an affine scheme -/

section Affine

variable (R : CommRingCat.{u})

/-- **The endomorphisms of `𝒪` in `D_QCoh(𝒪_{Spec R})` commute.** -/
theorem structureSheaf_endomorphisms_commute
    (g h : Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec R) ⟶
      Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec R)) : g ≫ h = h ≫ g :=
  (ObjectProperty.ι _).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact derived_unit_endomorphisms_commute R _ _)

end Affine

/-! ### The adjunctions in `D_QCoh` -/

local notation "𝐘" => Spec (CommRingCat.of A)
local notation "𝐒" =>
  Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of A))

/-- `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec A})` for `f : P^n_A ⟶ Spec A`. -/
abbrev pushQ : quasiCoherentDerivedCategory 𝐏 ⥤ quasiCoherentDerivedCategory 𝐘 :=
  quasiCoherentDerivedPushforward (projStructureMorphism A n)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (projStructureMorphism A n))

/-- `Lf^* : D_QCoh(𝒪_{Spec A}) ⥤ D_QCoh(𝒪_X)` for `f : P^n_A ⟶ Spec A`. -/
abbrev pullQ : quasiCoherentDerivedCategory 𝐘 ⥤ quasiCoherentDerivedCategory 𝐏 :=
  quasiCoherentDerivedPullback (projStructureMorphism A n)
    (isQuasicoherent_homology_derivedPullback' (projStructureMorphism A n))

/-- `Lf^* ⊣ Rf_*` on `D_QCoh`. -/
abbrev pullPushAdj : pullQ A n ⊣ pushQ A n :=
  quasiCoherentDerivedAdjunction (projStructureMorphism A n)
    (isQuasicoherent_homology_derivedPullback' (projStructureMorphism A n))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (projStructureMorphism A n))

/-- `𝒪(d)` placed in degree `k`, as an object of `D_QCoh(𝒪_X)`. -/
def twistShiftQ (d k : ℤ) : quasiCoherentDerivedCategory 𝐏 :=
  ⟨(DerivedCategory.singleFunctor _ k).obj (twist A n d), by
    have h0 := Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj _
      (isQuasicoherent_twist A n d)
    exact ObjectProperty.prop_of_iso _
      (((DerivedCategory.singleFunctors _).shiftIso (-k) k 0 (by omega)).app (twist A n d))
      (ObjectProperty.le_shift _ (-k) _ h0)⟩

/-- `𝒪(-n-1)[n]`, as an object of `D_QCoh(𝒪_X)`. -/
abbrev topTwist : quasiCoherentDerivedCategory 𝐏 := twistShiftQ A n (-(n : ℤ) - 1) (-(n : ℤ))

/-- `Rf_*(𝒪(-n-1)[n]) ≅ 𝒪_{Spec A}`. -/
def pushTopTwistIso : (pushQ A n).obj (topTwist A n) ≅ 𝐒 :=
  ObjectProperty.isoMk _ (nonempty_derivedPushforward_twist_top_iso A n).some

/-- `Rf_* 𝒪 ≅ 𝒪_{Spec A}`. -/
def pushTwistZeroIso : (pushQ A n).obj (twistShiftQ A n 0 0) ≅ 𝐒 :=
  ObjectProperty.isoMk _ (nonempty_derivedPushforward_twist_zero_iso A n).some

/-- `Lf^* 𝒪_{Spec A} ≅ 𝒪`. -/
def pullStructureSheafIso : (pullQ A n).obj 𝐒 ≅ twistShiftQ A n 0 0 :=
  ObjectProperty.isoMk _ (derivedPullbackStructureSheafIso (projStructureMorphism A n) ≪≫
    (DerivedCategory.singleFunctor (𝐏).Modules 0).mapIso
      ((Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading A n) :
        twist A n 0 ≅ SheafOfModules.unit (𝐏).ringCatSheaf)).symm)

/-- **The unit `𝒪_{Spec A} ⟶ Rf_* Lf^* 𝒪_{Spec A}` is an isomorphism.** -/
instance isIso_pullPushAdj_unit_app : IsIso ((pullPushAdj A n).unit.app 𝐒) :=
  Adjunction.isIso_unit_app_of_iso_of_commute (pullPushAdj A n) 𝐒
    ((pushTwistZeroIso A n).symm ≪≫ (pushQ A n).mapIso (pullStructureSheafIso A n).symm)
    (structureSheaf_endomorphisms_commute _)

/-- The right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec A})`. -/
abbrev twistedQ : quasiCoherentDerivedCategory 𝐘 ⥤ quasiCoherentDerivedCategory 𝐏 :=
  twistedInverseImage (projStructureMorphism A n)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (projStructureMorphism A n))

/-- `Rf_* ⊣ a`. -/
abbrev pushTwistedAdj : pushQ A n ⊣ twistedQ A n :=
  twistedInverseImageAdjunction (projStructureMorphism A n)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (projStructureMorphism A n))

/-- **The trace map `c : 𝒪(-n-1)[n] ⟶ a(𝒪_{Spec A})`**, adjoint to `Rf_*(𝒪(-n-1)[n]) ≅ 𝒪`. -/
def traceMap : topTwist A n ⟶ (twistedQ A n).obj 𝐒 :=
  (pushTwistedAdj A n).homEquiv _ _ (pushTopTwistIso A n).hom

/-- The generators `𝒪, 𝒪(-1), …, 𝒪(-n)` of `D_QCoh(𝒪_X)`. -/
def twistGen : ObjectProperty (quasiCoherentDerivedCategory 𝐏) :=
  fun E => ∃ i : Fin (n + 1), Nonempty (E ≅ twistShiftQ A n (-(i : ℤ)) 0)

/-- **[Stacks, Tag 0A9V]**, as a property of objects of `D_QCoh(𝒪_X)`. -/
theorem isWeakTriangulatedGenerator_twistGen : (twistGen A n).IsWeakTriangulatedGenerator :=
  ObjectProperty.isWeakTriangulatedGenerator_of_forall_hom_eq_zero _ _ fun K hK hvan =>
    isZero_of_quasiCoherentHomology_of_forall_hom_twistSum_eq_zero A n K hK fun j g => by
        refine biproduct.hom_ext' _ _ fun i => ?_
        exact (hvan (twistShiftQ A n (-(i : ℤ)) 0) ⟨i, ⟨Iso.refl _⟩⟩ j _).trans comp_zero.symm

/-- `Hom(𝒪(-i)[p], 𝒪(-n-1)[n]) = 0` in `D_QCoh(𝒪_X)` for `1 ≤ i ≤ n`. -/
theorem forall_eq_zero_twistShiftQ_topTwist (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) (p : ℤ)
    (g : (twistShiftQ A n (-(i : ℤ)) 0)⟦p⟧ ⟶ topTwist A n) : g = 0 := by
  let e₁ : (ObjectProperty.ι _).obj ((twistShiftQ A n (-(i : ℤ)) 0)⟦p⟧) ≅
      (twistD A n (-(i : ℤ)))⟦p⟧ :=
    ((ObjectProperty.ι _).commShiftIso p).app _
  let e₂ : (ObjectProperty.ι _).obj (topTwist A n) ≅ (twistD A n (-(n : ℤ) - 1))⟦(n : ℤ)⟧ :=
    (((DerivedCategory.singleFunctors (𝐏).Modules).shiftIso (n : ℤ) (-(n : ℤ)) 0
      (by omega)).app (twist A n (-(n : ℤ) - 1))).symm
  exact forall_eq_zero_of_faithful (ObjectProperty.ι _)
    (forall_eq_zero_of_iso e₁ e₂ (forall_eq_zero_twist_top A n i hi₁ hi₂ p)) g

/-- `Hom(𝒪(-i)[p], a(𝒪)) = 0` in `D_QCoh(𝒪_X)` for `1 ≤ i ≤ n`, since `Rf_* 𝒪(-i) = 0`. -/
theorem forall_eq_zero_twistShiftQ_twisted (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) (p : ℤ)
    (g : (twistShiftQ A n (-(i : ℤ)) 0)⟦p⟧ ⟶ (twistedQ A n).obj 𝐒) : g = 0 := by
  have : (twistedQ A n).IsRightAdjoint := (pushTwistedAdj A n).isRightAdjoint
  refine forall_eq_zero_of_adjunction' (pushTwistedAdj A n) (fun g' => ?_) g
  refine (IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ ?_).eq_of_src _ _
  exact ((shiftFunctor _ p).map_isZero (isZero_derivedPushforward_twist A n (-(i : ℤ))
      (by omega) (by omega) 0)).of_iso
    ((derivedPushforward (projStructureMorphism A n)).mapIso
        (((ObjectProperty.ι _).commShiftIso p).app _) ≪≫
      ((derivedPushforward (projStructureMorphism A n)).commShiftIso p).app _)

/-- `Rf_*` is bijective on `Hom(𝒪[-a], 𝒪(-n-1)[n])`, because `𝒪 = Lf^*𝒪_{Spec A}` and the unit of
`Lf^* ⊣ Rf_*` is invertible at the shifts of `𝒪_{Spec A}`. -/
theorem bijective_pushQ_map_twistZero (a : ℤ) :
    Function.Bijective (fun f : (twistShiftQ A n 0 0)⟦a⟧ ⟶ topTwist A n => (pushQ A n).map f) := by
  let := (pullPushAdj A n).leftAdjointCommShift ℤ
  have : IsIso ((pullPushAdj A n).unit.app (𝐒⟦a⟧)) :=
    Adjunction.isIso_unit_app_of_iso_of_commute (pullPushAdj A n) (𝐒⟦a⟧)
      ((shiftFunctor _ a).mapIso (asIso ((pullPushAdj A n).unit.app 𝐒)) ≪≫
        (((pushQ A n).commShiftIso a).app _).symm ≪≫
        (pushQ A n).mapIso (((pullQ A n).commShiftIso a).app 𝐒).symm)
      (fun g h => by
        obtain ⟨g', rfl⟩ := (shiftFunctor _ a).map_surjective g
        obtain ⟨h', rfl⟩ := (shiftFunctor _ a).map_surjective h
        rw [← Functor.map_comp, ← Functor.map_comp, structureSheaf_endomorphisms_commute])
  exact bijective_map_of_iso (pushQ A n) (topTwist A n)
    ((shiftFunctor _ a).mapIso (pullStructureSheafIso A n).symm ≪≫
      (((pullQ A n).commShiftIso a).app 𝐒).symm)
    (Adjunction.bijective_map_leftAdjoint_obj_of_isIso_unit_app (pullPushAdj A n) (𝐒⟦a⟧) _)

/-- **The trace map `c : 𝒪(-n-1)[n] ⟶ a(𝒪_{Spec A})` is an isomorphism.** -/
instance isIso_traceMap : IsIso (traceMap A n) := by
  refine (isWeakTriangulatedGenerator_twistGen A n).isIso_of_bijective_comp_shiftClosure _
    fun P hP => ?_
  obtain ⟨Q, a, eP, i, ⟨eQ⟩⟩ := hP
  refine bijective_comp_of_iso (eP ≪≫ (shiftFunctor _ a).mapIso eQ) _ ?_
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · rw [show (-(i : ℤ)) = 0 by simp [h0]]
    have hfun : (fun f : (twistShiftQ A n 0 0)⟦a⟧ ⟶ topTwist A n => f ≫ traceMap A n) =
        (pushTwistedAdj A n).homEquiv _ _ ∘ (fun g => g ≫ (pushTopTwistIso A n).hom) ∘
          (fun f => (pushQ A n).map f) :=
      funext fun f => ((pushTwistedAdj A n).homEquiv_naturality_left f _).symm
    rw [hfun]
    refine ((pushTwistedAdj A n).homEquiv _ _).bijective.comp
      (Function.Bijective.comp ?_ (bijective_pushQ_map_twistZero A n a))
    exact ⟨fun x y hxy => by simpa using congrArg (· ≫ (pushTopTwistIso A n).inv) hxy,
      fun g => ⟨g ≫ (pushTopTwistIso A n).inv, by simp⟩⟩
  · have h₁ := forall_eq_zero_twistShiftQ_topTwist A n i hpos (by omega) a
    have h₂ := forall_eq_zero_twistShiftQ_twisted A n i hpos (by omega) a
    exact ⟨fun x y _ => (h₁ x).trans (h₁ y).symm, fun g => ⟨0, zero_comp.trans (h₂ g).symm⟩⟩

/-- **`a(𝒪_{Spec A}) ≅ 𝒪(-n-1)[n]` on `P^n_A`**, for `a` the right adjoint of
`Rf_* : D_QCoh(𝒪_{P^n_A}) ⥤ D_QCoh(𝒪_{Spec A})`: the content of [Stacks, Tag 0A9W] for the trivial
bundle of rank `n + 1` over an affine base. The isomorphism is the trace map `traceMap`. -/
def topTwistIsoTwisted : topTwist A n ≅ (twistedQ A n).obj 𝐒 :=
  asIso (traceMap A n)

/-- **`a(𝒪_{Spec A}) ≅ 𝒪(-n-1)[n]` on `P^n_A`**, for the twisted inverse image along
`projToSpecCoeff A n` with any proof that `Rf_*` preserves quasi-coherent cohomology. -/
def topTwistIsoTwistedInverseImage
    (hpush : ∀ (K : quasiCoherentDerivedCategory 𝐏) (i : ℤ),
      ((DerivedCategory.homologyFunctor (𝐘).Modules i).obj
        ((derivedPushforward (projToSpecCoeff A n)).obj K.obj)).IsQuasicoherent) :
    topTwist A n ≅ (twistedInverseImage (projToSpecCoeff A n) hpush).obj 𝐒 :=
  topTwistIsoTwisted A n

end Stacks.Duality.ProjectiveSpace
