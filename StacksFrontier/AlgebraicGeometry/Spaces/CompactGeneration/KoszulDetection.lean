module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Koszul objects of global functions on an algebraic space with affine final chart

Let `X` be an algebraic space whose small étale site has a final object `T` with affine underlying
scheme, for instance an affine algebraic space. For a list `l = [a₁, …, aᵣ]` of global functions
on `X` the *Koszul object* `K(l)` of `D(𝒪_X)` is built from `𝒪_X[0]` by taking, for each `aᵢ`, a
cone of multiplication by `aᵢ`. This file proves the étale-site analogue of [Stacks, Tag 09IR]
for these objects:

* `K(l)` lies in `D_QCoh(𝒪_X)` and is compact there;
* its cohomology sheaves vanish over every chart on which some `aᵢ` becomes a unit;
* an object `M` of `D_QCoh(𝒪_X)` whose cohomology sheaves vanish over every chart on which some
  `aᵢ` becomes a unit, and which receives no nonzero morphism from a shift of `K(l)`, is zero.

The last statement is the detection hypothesis of the abstract half of [Stacks, Tag 09IR],
`CategoryTheory.ObjectProperty.isZero_of_rightOrthogonal_shiftClosure_singleton_of_isZero_map`,
for restriction to the open subspace `D(a₁) ∪ … ∪ D(aᵣ)`.

## Main definitions

* `AlgebraicGeometry.Space.isMulCommutative_ringSheaf_smallEtale`: the sections of `𝒪_X` commute,
  so that `𝒪_X`-modules and `D(𝒪_X)` are linear over the ring
  `Stacks.Cohomology.SiteModules.GlobalSectionRing` of global functions.
* `AlgebraicGeometry.Space.koszul`, `AlgebraicGeometry.Space.koszulQuasicoherent`: the Koszul
  object, in `D(𝒪_X)` and in `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.VanishesWhereUnit`: vanishing of the cohomology sheaves over the charts
  on which a global function becomes a unit.

## Main results

* `AlgebraicGeometry.Space.isCompactObject_koszulQuasicoherent`: `K(l)` is compact.
* `AlgebraicGeometry.Space.subsingleton_homology_koszul_sections`: `K(l)` vanishes where some
  member of `l` is a unit.
* `AlgebraicGeometry.Space.isZero_of_hom_koszul_eq_zero` and
  `AlgebraicGeometry.Space.isZero_of_rightOrthogonal_koszul`: **Koszul detection**.

## Implementation notes

The proof replaces the comparison with `D(A)` used for schemes by two facts about scalars. First,
`a • 𝟙` squares to zero on a cone of `a • 𝟙`, so each member of `l` kills a power of `K(l)`.
Second, morphisms from `K(l)` into an object vanishing where `a` is a unit are killed by a power of
`a`. For `𝒪_X[0]` this is the description of a basic open chart of `T` as a localization; for a
cone it follows from the defining triangle. Given both, a morphism `K(l) ⟶ M⟦n⟧` is killed by a
power of the next element `b` of the list, while multiplication by `b` is injective on such
morphisms once `M` is right orthogonal to the cone of `b`. Descending the list ends at `𝒪_X[0]`,
which generates `D_QCoh(𝒪_X)`.

No `@[stacks]` attribute is placed: [Stacks, Tag 09IR] is registered on its scheme-theoretic
form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-- The rings of sections of the structure sheaf of the small étale site are commutative. -/
instance isMulCommutative_ringSheaf_smallEtale (U : (smallEtaleRingedSite B S hS X hX).Cᵒᵖ) :
    IsMulCommutative
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj.obj U) :=
  ⟨⟨fun a b => (chartRing_commRing B S hS X hX U.unop).mul_comm a b⟩⟩

/-- The ring of global functions on `X`: compatible families of sections of `𝒪_X`. -/
local notation "globalRing" hX:max =>
  Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.RingedSite.O (smallEtaleRingedSite _ _ _ _ hX)))

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

attribute [local instance] DerivedCategory.homologyFunctor_linear

/-! ### Scalars on objects and on sections -/

/-- A global function acts on the sections of a sheaf of modules over a chart through its value
on that chart. -/
theorem globalRing_smul_val_app (a : globalRing hX) {M N : Modules.{u, u} B S hS X hX} (g : M ⟶ N)
    (U : SmallEtale B S hS X) (x : M.val.obj (op U)) :
    (a • g).val.app (op U) x = a.1 (op U) • g.val.app (op U) x :=
  (g.val.app (op U)).hom.map_smul _ x

/-- If `a • 𝟙` vanishes on an object `P` of `D(𝒪_X)` and `a` becomes a unit on a chart `U`, then
the cohomology sheaves of `P` have no nonzero section over `U`. -/
theorem subsingleton_homology_sections_of_smul_id_eq_zero (a : globalRing hX)
    (P : DerivedCategory (Modules.{u, u} B S hS X hX)) (N : ℕ) (hN : a ^ N • 𝟙 P = 0)
    (U : SmallEtale B S hS X) (hU : IsUnit (a.1 (op U))) (q : ℤ) :
    Subsingleton (((DerivedCategory.homologyFunctor _ q).obj P).val.obj (op U)) := by
  refine ⟨fun s t => ?_⟩
  have h0 : ∀ x : ((DerivedCategory.homologyFunctor _ q).obj P).val.obj (op U),
      (a ^ N).1 (op U) • x = 0 := by
    intro x
    have h := congrArg (fun k => k.val.app (op U) x)
      (congrArg (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) q).map hN)
    simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
    rw [globalRing_smul_val_app] at h
    exact h.trans rfl
  have hu : IsUnit ((a ^ N).1 (op U)) := by
    rw [SubmonoidClass.coe_pow, Pi.pow_apply]
    exact hU.pow N
  obtain ⟨v, hv⟩ := hu
  have hz : ∀ x : ((DerivedCategory.homologyFunctor _ q).obj P).val.obj (op U), x = 0 := by
    intro x
    rw [← one_smul (chartRing B S hS X hX U) x, ← Units.inv_mul v, mul_smul, hv, h0, smul_zero]
  rw [hz s, hz t]

/-- **Scalars on the cone of a distinguished triangle.** If a scalar `c` kills the composite
`P ⟶ Z ⟶ Z` and the composite `Z ⟶ P⟦1⟧ ⟶ P⟦1⟧` through `c • 𝟙`, then `c * c` kills `Z`. -/
theorem mul_self_smul_id_eq_zero_of_distTriang (c : globalRing hX)
    (T : Triangle (DerivedCategory (Modules.{u, u} B S hS X hX))) (hT : T ∈ distTriang _)
    (h₂ : T.mor₂ ≫ (c • 𝟙 T.obj₃) = 0) (h₃ : T.mor₃ ≫ (c • 𝟙 (T.obj₁⟦(1 : ℤ)⟧)) = 0) :
    (c * c) • 𝟙 T.obj₃ = 0 := by
  obtain ⟨ψ, hψ⟩ := Triangle.yoneda_exact₃ _ hT (c • 𝟙 T.obj₃) h₂
  rw [mul_smul]
  calc c • c • 𝟙 T.obj₃ = (c • 𝟙 T.obj₃) ≫ (c • 𝟙 T.obj₃) := by
        rw [Linear.smul_comp, Category.id_comp]
    _ = (T.mor₃ ≫ ψ) ≫ (c • 𝟙 T.obj₃) := by
        nth_rewrite 1 [hψ]
        rfl
    _ = 0 := by
        rw [Category.assoc, Linear.comp_smul, Category.comp_id, ← Category.id_comp ψ,
          ← Linear.smul_comp, ← Category.assoc, h₃, zero_comp]

/-- If `a ^ N` kills `P`, then `a ^ (2 * N)` kills the third vertex of a distinguished triangle
`P ⟶ P ⟶ Z ⟶ P⟦1⟧`. -/
theorem pow_smul_id_eq_zero_of_distTriang (a : globalRing hX)
    (T : Triangle (DerivedCategory (Modules.{u, u} B S hS X hX))) (hT : T ∈ distTriang _)
    (h₁₂ : T.obj₁ = T.obj₂) (N : ℕ) (hN : a ^ N • 𝟙 T.obj₁ = 0) :
    a ^ (2 * N) • 𝟙 T.obj₃ = 0 := by
  rw [two_mul, pow_add]
  refine mul_self_smul_id_eq_zero_of_distTriang _ T hT ?_ ?_
  · have hN₂ : a ^ N • 𝟙 T.obj₂ = 0 := h₁₂ ▸ hN
    rw [Linear.comp_smul, Category.comp_id, ← Category.id_comp T.mor₂, ← Linear.smul_comp, hN₂,
      zero_comp]
  · have : a ^ N • 𝟙 (T.obj₁⟦(1 : ℤ)⟧) = (shiftFunctor _ (1 : ℤ)).map (a ^ N • 𝟙 T.obj₁) := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rw [this, hN, Functor.map_zero, comp_zero]

/-- The square of the scalar defining a triangle `P ⟶ P ⟶ Z ⟶ P⟦1⟧` kills its third vertex. -/
theorem sq_smul_id_eq_zero_of_distTriang (a : globalRing hX)
    {P Z : DerivedCategory (Modules.{u, u} B S hS X hX)} (g : P ⟶ Z) (h : Z ⟶ P⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (a • 𝟙 P) g h ∈ distTriang _) :
    (a * a) • 𝟙 Z = 0 := by
  refine mul_self_smul_id_eq_zero_of_distTriang a _ hT ?_ ?_
  · dsimp only [Triangle.mk_mor₂, Triangle.mk_obj₃]
    rw [Linear.comp_smul, Category.comp_id, ← Category.id_comp g, ← Linear.smul_comp]
    exact comp_distTriang_mor_zero₁₂ _ hT
  · dsimp only [Triangle.mk_mor₃, Triangle.mk_obj₁]
    have : a • 𝟙 (P⟦(1 : ℤ)⟧) = (shiftFunctor _ (1 : ℤ)).map (a • 𝟙 P) := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rw [this]
    exact comp_distTriang_mor_zero₃₁ _ hT

/-! ### Koszul objects -/

variable (hX) in
/-- The Koszul object of a list of global functions: `𝒪_X[0]` for the empty list, and a cone of
multiplication by `a` on the Koszul object of `l` for `a :: l`. -/
def koszul : List (globalRing hX) → DerivedCategory (Modules.{u, u} B S hS X hX)
  | [] => (DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩)
  | a :: l => (distinguished_cocone_triangle (a • 𝟙 (koszul l))).choose

/-- The Koszul object of the empty list is `𝒪_X[0]`. -/
theorem koszul_nil :
    koszul hX [] = (DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩) := rfl

/-- The distinguished triangle `K(l) ⟶ K(l) ⟶ K(a :: l) ⟶ K(l)⟦1⟧` defining a Koszul object. -/
theorem exists_distTriang_koszul_cons (a : globalRing hX) (l : List (globalRing hX)) :
    ∃ (g : koszul hX l ⟶ koszul hX (a :: l)) (h : koszul hX (a :: l) ⟶ (koszul hX l)⟦(1 : ℤ)⟧),
      Triangle.mk (a • 𝟙 (koszul hX l)) g h ∈ distTriang _ :=
  (distinguished_cocone_triangle (a • 𝟙 (koszul hX l))).choose_spec

/-- Every member of the list kills a power of the Koszul object. -/
theorem exists_pow_smul_id_koszul_eq_zero :
    ∀ (l : List (globalRing hX)) (b : globalRing hX), b ∈ l →
      ∃ N : ℕ, b ^ N • 𝟙 (koszul hX l) = 0
  | [], _, hb => absurd hb List.not_mem_nil
  | a :: l, b, hb => by
    obtain ⟨g, h, hT⟩ := exists_distTriang_koszul_cons a l
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨2, by simpa only [pow_two] using sq_smul_id_eq_zero_of_distTriang b g h hT⟩
    · obtain ⟨N, hN⟩ := exists_pow_smul_id_koszul_eq_zero l b hb
      exact ⟨2 * N, pow_smul_id_eq_zero_of_distTriang b _ hT rfl N hN⟩

/-- **The Koszul object vanishes where one of its functions is invertible**: its cohomology
sheaves have no nonzero section over a chart on which a member of the list becomes a unit. -/
theorem subsingleton_homology_koszul_sections (l : List (globalRing hX))
    (U : SmallEtale B S hS X) (hU : ∃ b ∈ l, IsUnit (b.1 (op U))) (q : ℤ) :
    Subsingleton (((DerivedCategory.homologyFunctor _ q).obj (koszul hX l)).val.obj (op U)) := by
  obtain ⟨b, hb, hu⟩ := hU
  obtain ⟨N, hN⟩ := exists_pow_smul_id_koszul_eq_zero l b hb
  exact subsingleton_homology_sections_of_smul_id_eq_zero b _ N hN U hu q

/-- Koszul objects have quasi-coherent cohomology. -/
theorem qcohDerived_koszul : ∀ l : List (globalRing hX), QcohDerived B S hS ⟨X, hX⟩ (koszul hX l)
  | [] => qcohDerived_singleFunctor_structureModule
  | a :: l => by
    obtain ⟨g, h, hT⟩ := exists_distTriang_koszul_cons a l
    exact (QcohDerived B S hS ⟨X, hX⟩).ext_of_isTriangulatedClosed₃ _ hT (qcohDerived_koszul l)
      (qcohDerived_koszul l)

variable (hX) in
/-- The Koszul object of a list of global functions, as an object of `D_QCoh(𝒪_X)`. -/
def koszulQuasicoherent (l : List (globalRing hX)) :
    QuasicoherentDerivedCategory.{u, u} B S hS X hX :=
  ⟨koszul hX l, qcohDerived_koszul l⟩

/-- **Koszul objects are compact in `D_QCoh(𝒪_X)`** when the small étale site has a final object
with affine underlying scheme: they are built from `𝒪_X[0]` by cones. -/
theorem isCompactObject_koszulQuasicoherent (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) :
    ∀ l : List (globalRing hX), IsCompactObject.{u} (koszulQuasicoherent hX l)
  | [] => isCompactObject_unitQuasicoherent T hT hTa
  | a :: l => by
    obtain ⟨g, h, hT'⟩ := exists_distTriang_koszul_cons a l
    let P := QcohDerived B S hS ⟨X, hX⟩
    let TQ : Triangle (QuasicoherentDerivedCategory.{u, u} B S hS X hX) :=
      Triangle.mk (P.fullyFaithfulι.preimage (X := koszulQuasicoherent hX l)
          (Y := koszulQuasicoherent hX l) (a • 𝟙 (koszul hX l)))
        (P.fullyFaithfulι.preimage (X := koszulQuasicoherent hX l)
          (Y := koszulQuasicoherent hX (a :: l)) g)
        (P.fullyFaithfulι.preimage (X := koszulQuasicoherent hX (a :: l))
          (Y := (koszulQuasicoherent hX l)⟦(1 : ℤ)⟧)
          (h ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app (koszulQuasicoherent hX l)))
    have hTQ : TQ ∈ distTriang _ := by
      refine isomorphic_distinguished _ hT' _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
        (Iso.refl _) ?_ ?_ ?_)
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · have e : (P.ι.mapTriangle.obj TQ).mor₃ = h :=
          (Category.assoc _ _ _).trans ((congrArg (h ≫ ·)
            ((P.ι.commShiftIso (1 : ℤ)).inv_hom_id_app (koszulQuasicoherent hX l))).trans
              (Category.comp_id h))
        exact ((congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)).trans
          (e.trans (Category.id_comp h).symm)
    have hl := isCompactObject_koszulQuasicoherent T hT hTa l
    have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X hX
    exact isCompactObject_obj₃ TQ hTQ hl hl

/-! ### Detection -/

/-- The comparison `homFromUnitSections` is linear over the global functions. -/
theorem homFromUnitSections_smul (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (E : DerivedCategory (Modules.{u, u} B S hS X hX)) (a : globalRing hX)
    (x : (DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩) ⟶ E) :
    homFromUnitSections T hT E (a • x) = a.1 (op T) • homFromUnitSections T hT E x := by
  have key : ∀ y : (DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩) ⟶ E,
      homFromUnitSections T hT E y = ((homologyUnitIso (hX := hX)).inv ≫
        (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).map y).val.app
          (op T) (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X hX).O)).obj.obj (op T)) :=
    fun _ => rfl
  rw [key, key, Functor.map_smul, Linear.comp_smul]
  exact globalRing_smul_val_app a _ T _

/-- Local vanishing of `M` along a global function `a`: on every chart where `a` becomes a unit,
every cohomology sheaf of `M` has no nonzero section. -/
def VanishesWhereUnit (a : globalRing hX) (M : DerivedCategory (Modules.{u, u} B S hS X hX)) :
    Prop :=
  ∀ (U : SmallEtale B S hS X), IsUnit (a.1 (op U)) → ∀ q : ℤ,
    Subsingleton (((DerivedCategory.homologyFunctor _ q).obj M).val.obj (op U))

/-- Vanishing where `a` is a unit is preserved by every shift `M ↦ M⟦n⟧`. -/
theorem VanishesWhereUnit.shift {a : globalRing hX}
    {M : DerivedCategory (Modules.{u, u} B S hS X hX)}
    (hM : VanishesWhereUnit a M) (n : ℤ) : VanishesWhereUnit a (M⟦n⟧) := fun U hU q =>
  let e := (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).shiftIso n q
    (n + q) rfl).app M)
  ⟨fun _ _ => (Iso.toLinearEquiv ((SheafOfModules.evaluation _ (op U)).mapIso e)).injective
    ((hM U hU (n + q)).elim _ _)⟩

/-- **Base case of torsion**: a morphism `𝒪_X[0] ⟶ M` into an object of `D_QCoh(𝒪_X)` vanishing
where `a` is a unit is killed by a power of `a`. -/
theorem exists_pow_smul_eq_zero_of_unit (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (a : globalRing hX)
    (M : DerivedCategory (Modules.{u, u} B S hS X hX)) (hM : QcohDerived B S hS ⟨X, hX⟩ M)
    (hloc : VanishesWhereUnit a M)
    (x : (DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩) ⟶ M) :
    ∃ N : ℕ, a ^ N • x = 0 := by
  set H := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).obj M
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX H (hM 0)
  set g := a.1 (op T)
  let V := openChart B S hS X T ((chartScheme T).basicOpen g)
  let ι := openChartInclusion B S hS X T ((chartScheme T).basicOpen g)
  have haV : a.1 (op V) = chartRestrict (hF := hX) ι g := (a.2 ι.op).symm
  have hunit : IsUnit (a.1 (op V)) := by
    rw [haV]
    exact isUnit_chartRestrict_openChartInclusion_basicOpen B S hS hX T hTa g
  obtain ⟨k, hk⟩ := (chartRestrictLinear_openChart_basicOpen_eq_zero_iff B S hS hX H hcart T hTa
    g (homFromUnitSections T hT M x)).1 ((hloc V hunit 0).elim _ _)
  refine ⟨k, (bijective_homFromUnitSections T hT hTa M hM).1 ?_⟩
  rwa [homFromUnitSections_smul, map_zero, SubmonoidClass.coe_pow, Pi.pow_apply]

/-- **Torsion**: every morphism from a Koszul object into an object of `D_QCoh(𝒪_X)` vanishing
where `a` is a unit is killed by a power of `a`. -/
theorem exists_pow_smul_eq_zero_of_koszul (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (a : globalRing hX) :
    ∀ (l : List (globalRing hX)) (M : DerivedCategory (Modules.{u, u} B S hS X hX)),
      QcohDerived B S hS ⟨X, hX⟩ M → VanishesWhereUnit a M →
      ∀ x : koszul hX l ⟶ M, ∃ N : ℕ, a ^ N • x = 0
  | [], M, hM, hloc, x => exists_pow_smul_eq_zero_of_unit T hT hTa a M hM hloc x
  | b :: l, M, hM, hloc, x => by
    obtain ⟨g, h, hT'⟩ := exists_distTriang_koszul_cons b l
    obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_koszul T hT hTa a l M hM hloc (g ≫ x)
    rw [← Linear.comp_smul] at hN
    obtain ⟨z, hz⟩ : ∃ z : (koszul hX l)⟦(1 : ℤ)⟧ ⟶ M, a ^ N • x = h ≫ z :=
      Triangle.yoneda_exact₃ _ hT' (a ^ N • x) hN
    let e := (shiftFunctorCompIsoId (DerivedCategory (Modules.{u, u} B S hS X hX)) (1 : ℤ) (-1)
      (by omega)).app (koszul hX l)
    obtain ⟨N', hN'⟩ := exists_pow_smul_eq_zero_of_koszul T hT hTa a l (M⟦(-1 : ℤ)⟧)
      (qcohDerived_shift M (-1) hM) (hloc.shift (-1))
      (e.inv ≫ (shiftFunctor _ (-1 : ℤ)).map z)
    have hz' : a ^ N' • z = 0 := by
      apply (shiftFunctor (DerivedCategory (Modules.{u, u} B S hS X hX)) (-1 : ℤ)).map_injective
      rw [Functor.map_smul, Functor.map_zero]
      rw [← Linear.comp_smul] at hN'
      exact (cancel_epi e.inv).1 (hN'.trans comp_zero.symm)
    refine ⟨N' + N, ?_⟩
    rw [pow_add, mul_smul, hz, ← Linear.comp_smul, hz', comp_zero]

/-- If `b ^ N • x = 0` for a morphism `x` out of the first vertex of a triangle
`P ⟶ P ⟶ Z ⟶ P⟦1⟧` defining `Z` as a cone of `b`, and every morphism out of `Z` vanishes,
then `x = 0`. -/
private theorem eq_zero_of_pow_smul_eq_zero_of_distTriang (b : globalRing hX)
    {P Z M : DerivedCategory (Modules.{u, u} B S hS X hX)} (g : P ⟶ Z) (h : Z ⟶ P⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (b • 𝟙 P) g h ∈ distTriang _) (horth : ∀ w : Z ⟶ M, w = 0) (N : ℕ)
    (x : P ⟶ M) (hN : b ^ N • x = 0) : x = 0 := by
  induction N generalizing x with
  | zero => simpa using hN
  | succ N ih =>
    refine ih x ?_
    have h1 : (b • 𝟙 P) ≫ (b ^ N • x) = 0 := by
      rw [Linear.smul_comp, Category.id_comp, ← mul_smul, ← pow_succ']
      exact hN
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₂ _ hT _ h1
    rw [hw, horth w, comp_zero]

/-- **Koszul detection.** Let `M` be an object of `D_QCoh(𝒪_X)`, where the small étale site of
`X` has a final object with affine underlying scheme, and let `l` be a list of global functions.
If the cohomology sheaves of `M` have no nonzero section over any chart on which a member of `l`
becomes a unit, and every morphism `K(l) ⟶ M⟦n⟧` vanishes, then `M` is zero. -/
theorem isZero_of_hom_koszul_eq_zero (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) :
    ∀ (l : List (globalRing hX)) (M : DerivedCategory (Modules.{u, u} B S hS X hX)),
      QcohDerived B S hS ⟨X, hX⟩ M → (∀ a ∈ l, VanishesWhereUnit a M) →
      (∀ (n : ℤ) (x : koszul hX l ⟶ M⟦n⟧), x = 0) → IsZero M
  | [], M, hM, _, horth => isZero_of_forall_homFromUnit_eq_zero T hT hTa M hM horth
  | b :: l, M, hM, hloc, horth => by
    obtain ⟨g, h, hT'⟩ := exists_distTriang_koszul_cons b l
    refine isZero_of_hom_koszul_eq_zero T hT hTa l M hM
      (fun a ha => hloc a (List.mem_cons_of_mem b ha)) fun n x => ?_
    obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_koszul T hT hTa b l (M⟦n⟧)
      (qcohDerived_shift M n hM) ((hloc b List.mem_cons_self).shift n) x
    exact eq_zero_of_pow_smul_eq_zero_of_distTriang b g h hT' (horth n) N x hN

/-- **Graded Koszul detection.** Let `M` be an object of `D_QCoh(𝒪_X)`, where the small étale site
of `X` has a final object with affine underlying scheme, and let `l` be a list of global
functions. If the cohomology sheaves of `M` have no nonzero section over any chart on which a
member of `l` becomes a unit, and every morphism `K(l) ⟶ M⟦n⟧` with `n` in a set `D` of degrees
vanishes, then `H^q(M) = 0` for every `q ∈ D`. -/
theorem isZero_homology_of_hom_koszul_eq_zero (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (D : ℤ → Prop) :
    ∀ (l : List (globalRing hX)) (M : DerivedCategory (Modules.{u, u} B S hS X hX)),
      QcohDerived B S hS ⟨X, hX⟩ M → (∀ b ∈ l, VanishesWhereUnit b M) →
      (∀ n : ℤ, D n → ∀ x : koszul hX l ⟶ M⟦n⟧, x = 0) →
      ∀ q : ℤ, D q → IsZero ((DerivedCategory.homologyFunctor _ q).obj M)
  | [], M, hM, _, horth, q, hq =>
    isZero_homology_of_forall_homFromUnit_eq_zero T hT hTa M hM q (horth q hq)
  | b :: l, M, hM, hloc, horth, q, hq => by
    obtain ⟨g, h, hT'⟩ := exists_distTriang_koszul_cons b l
    refine isZero_homology_of_hom_koszul_eq_zero T hT hTa D l M hM
      (fun c hc => hloc c (List.mem_cons_of_mem b hc)) (fun n hn x => ?_) q hq
    have hinj : ∀ y : koszul hX l ⟶ M⟦n⟧, b • y = 0 → y = 0 := by
      intro y hy
      have h1 : (b • 𝟙 (koszul hX l)) ≫ y = 0 := by rw [Linear.smul_comp, Category.id_comp, hy]
      obtain ⟨w, hw⟩ := Triangle.yoneda_exact₂ _ hT' y h1
      rw [hw, horth n hn w, comp_zero]
    obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_koszul T hT hTa b l (M⟦n⟧)
      (qcohDerived_shift M n hM) ((hloc b List.mem_cons_self).shift n) x
    clear hT'
    induction N generalizing x with
    | zero => simpa using hN
    | succ N ih =>
      exact ih x (hinj _ (by rw [← mul_smul, ← pow_succ']; exact hN))

/-- **Koszul detection, in orthogonality form**: an object of `D_QCoh(𝒪_X)` right orthogonal to
every shift of `K(l)`, whose cohomology sheaves vanish on every chart where a member of `l` is a
unit, is zero. This is the detection hypothesis of
`CategoryTheory.ObjectProperty.isZero_of_rightOrthogonal_shiftClosure_singleton_of_isZero_map`. -/
theorem isZero_of_rightOrthogonal_koszul (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (l : List (globalRing hX))
    (M : DerivedCategory (Modules.{u, u} B S hS X hX)) (hM : QcohDerived B S hS ⟨X, hX⟩ M)
    (hloc : ∀ a ∈ l, VanishesWhereUnit a M)
    (horth : ((ObjectProperty.singleton (koszul hX l)).shiftClosure ℤ).rightOrthogonal M) :
    IsZero M := by
  refine isZero_of_hom_koszul_eq_zero T hT hTa l M hM hloc fun n y => ?_
  let e := (shiftFunctorCompIsoId (DerivedCategory (Modules.{u, u} B S hS X hX)) n (-n)
    (add_neg_cancel n)).app M
  have h0 : (shiftFunctor _ (-n)).map y ≫ e.hom = 0 :=
    horth _ ⟨koszul hX l, -n, Iso.refl _, (ObjectProperty.singleton_iff _ _).2 rfl⟩
  apply (shiftFunctor (DerivedCategory (Modules.{u, u} B S hS X hX)) (-n)).map_injective
  rw [Functor.map_zero]
  simpa using congrArg (· ≫ e.inv) h0

end AlgebraicGeometry.Space

end
