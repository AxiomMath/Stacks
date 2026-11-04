module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.Devissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.BoundedBelowSplitting
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Invertibility on bounded below objects from the shifts of the ring, without `Ext²`

Let `R` be a ring such that `Ext²` vanishes between any two `R`-modules (a Dedekind domain such
as `ℤ`), let `α : F ⟶ G` be a natural transformation of exact functors `C ⥤ D` of triangulated
categories, and let `Ψ : D(R) ⥤ C` be an exact functor commuting with direct sums. Suppose

* `F` commutes with direct sums,
* `G` commutes with direct sums of shifts of images under `Ψ` of modules placed in degrees
  bounded below by a common integer, and
* `α` is invertible at every shift of `Ψ(R)`.

Then `α` is invertible at every shift of `Ψ(M)` for every bounded below `M ∈ D(R)`.

This is the dévissage of [Stacks, Tag 0F12] read on bounded below objects, where `G` need not
commute with all direct sums (as for `Rπ_*` without a bound on the cohomological dimension, which
commutes with direct sums of families with a common lower bound, [Stacks, Tag 0GIW]). The
dévissage is: the ring, then free modules (direct sums), projective modules (retracts), all
modules (a projective resolution of length one, `Ext²` vanishing), modules placed in any degree
(shifts), and finally all bounded below objects, which are direct sums of modules placed in
degrees bounded below
(`DerivedCategory.nonempty_iso_sigma_singleFunctor_of_isGE_of_forall_ext_two_eq_zero`).

## Main results

* `Stacks.EtaleCohomology.PointProjectionFormulaBoundedBelow.isIso_app_of_isGE`: the dévissage.

## References

* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 0F0E](https://stacks.math.columbia.edu/tag/0F0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace Stacks.EtaleCohomology.PointProjectionFormulaBoundedBelow

open Stacks.CategoryTheory.ComponentwiseInvertibility
open Stacks.EtaleCohomology.ProjectionFormulaConstant

/-- A natural transformation invertible at an object is invertible at its retracts. -/
theorem isIso_app_of_retract {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (α : F ⟶ G) {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X) [IsIso (α.app Y)] :
    IsIso (α.app X) :=
  ⟨⟨G.map i ≫ inv (α.app Y) ≫ F.map r, by
      rw [← Category.assoc, ← α.naturality, Category.assoc, IsIso.hom_inv_id_assoc, ← F.map_comp,
        hir, CategoryTheory.Functor.map_id],
      by rw [Category.assoc, Category.assoc, α.naturality, IsIso.inv_hom_id_assoc,
        ← G.map_comp, hir, CategoryTheory.Functor.map_id]⟩⟩

attribute [local instance] HasDerivedCategory.standard
  Stacks.EtaleCohomology.moduleCat_isGrothendieckAbelian
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

variable {R : Type u} [Ring R] [Small.{v} R]
  {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (α : F ⟶ G)
  (Ψ : DerivedCategory (ModuleCat.{v} R) ⥤ C) [Ψ.CommShift ℤ] [Ψ.IsTriangulated]

/-- The property of an object `M ∈ D(R)` that `α` is invertible at every shift of `Ψ(M)`. -/
def Inv (M : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  ∀ n : ℤ, IsIso (α.app ((Ψ.obj M)⟦n⟧))

variable {F G α Ψ}

omit [Small.{v} R]
  [HasShift D ℤ] [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [Ψ.CommShift ℤ] [Ψ.IsTriangulated] in
/-- The property `Inv` is invariant under isomorphism in `D(R)`. -/
theorem Inv.of_iso {M M' : DerivedCategory (ModuleCat.{v} R)} (e : M ≅ M') (h : Inv F G α Ψ M) :
    Inv F G α Ψ M' := fun n =>
  (α.isIso_app_iff_of_iso ((shiftFunctor C n).mapIso (Ψ.mapIso e))).1 (h n)

omit [Small.{v} R]
  [HasShift D ℤ] [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [Ψ.IsTriangulated] in
/-- The property `Inv` is stable under shifts in `D(R)`. -/
theorem Inv.shift {M : DerivedCategory (ModuleCat.{v} R)} (h : Inv F G α Ψ M) (m : ℤ) :
    Inv F G α Ψ (M⟦m⟧) := fun n =>
  (α.isIso_app_iff_of_iso ((shiftFunctor C n).mapIso ((Ψ.commShiftIso m).app M) ≪≫
    ((shiftFunctorAdd C m n).app _).symm)).2 (h (m + n))

omit [Small.{v} R]
  [HasShift D ℤ] [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [Ψ.CommShift ℤ] [Ψ.IsTriangulated] in
/-- The property `Inv` passes to retracts in `D(R)`. -/
theorem Inv.of_retract {M M' : DerivedCategory (ModuleCat.{v} R)} (i : M ⟶ M') (r : M' ⟶ M)
    (hir : i ≫ r = 𝟙 M) (h : Inv F G α Ψ M') : Inv F G α Ψ M := fun n =>
  have := h n
  isIso_app_of_retract α ((shiftFunctor C n).map (Ψ.map i)) ((shiftFunctor C n).map (Ψ.map r))
    (by rw [← Functor.map_comp, ← Functor.map_comp, hir, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id])

omit [Small.{v} R] in
/-- Two out of three on a distinguished triangle: the first two vertices give the third. -/
theorem Inv.of_distinguished₃ (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang _) (h₁ : Inv F G α Ψ T.obj₁) (h₂ : Inv F G α Ψ T.obj₂) :
    Inv F G α Ψ T.obj₃ := fun n => by
  let S := (shiftFunctor (Triangle C) n).obj (Ψ.mapTriangle.obj T)
  have hS : S ∈ distTriang C := Triangle.shift_distinguished _ (Ψ.map_distinguished T hT) n
  exact isIso_app_third_of_distinguished F G α S hS (h₁ n) (h₂ n)
    ((α.isIso_app_iff_of_iso ((shiftFunctorAdd C n 1).app _)).1 (h₁ (n + 1)))
    ((α.isIso_app_iff_of_iso ((shiftFunctorAdd C n 1).app _)).1 (h₂ (n + 1)))

section Devissage

variable [∀ I : Type v, PreservesColimitsOfShape (Discrete I) Ψ]

omit [HasShift D ℤ] [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [Ψ.CommShift ℤ] [Ψ.IsTriangulated] in
/-- Direct sums: if `F` commutes with the direct sum of the images of a family and `G` commutes
with the direct sum of every shift of those images, `α` is invertible at every shift of the
image of the direct sum as soon as it is at every shift of every member. -/
theorem Inv.sigma (hF : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F) {J : Type v}
    (X : J → DerivedCategory (ModuleCat.{v} R))
    (hG : ∀ n : ℤ, PreservesColimit (Discrete.functor fun j => (Ψ.obj (X j))⟦n⟧) G)
    (h : ∀ j, Inv F G α Ψ (X j)) : Inv F G α Ψ (∐ X) := fun n => by
  have := hF J
  let c := (Ψ ⋙ shiftFunctor C n).mapCocone (colimit.cocone (Discrete.functor X))
  have hc : IsColimit c := isColimitOfPreserves _ (colimit.isColimit _)
  have : PreservesColimit (Discrete.functor X ⋙ (Ψ ⋙ shiftFunctor C n)) G :=
    have := hG n
    preservesColimit_of_iso_diagram G (K₁ := Discrete.functor fun j => (Ψ.obj (X j))⟦n⟧)
      (K₂ := Discrete.functor X ⋙ (Ψ ⋙ shiftFunctor C n)) (Discrete.natIso fun _ => Iso.refl _)
  exact isIso_app_of_isColimit F G α c hc (fun j => h j.as n)

/-- The `R`-module `R`, in the universe of the modules. -/
abbrev unitModule : ModuleCat.{v} R := ModuleCat.of R (Shrink.{v} R)

/-- The map `R ⟶ P` sending `1` to `p`. -/
def toModule {P : ModuleCat.{v} R} (p : P) : (unitModule : ModuleCat.{v} R) ⟶ P :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton R P p).comp (Shrink.linearEquiv R R).toLinearMap)

/-- Every module is a quotient of a direct sum of copies of `R`: the sum of the maps
`R ⟶ P`, `1 ↦ p`, over all elements `p`. -/
theorem epi_sigmaDesc_toModule (P : ModuleCat.{v} R) :
    Epi (Sigma.desc fun p : P => toModule p) := by
  rw [ModuleCat.epi_iff_surjective]
  intro p
  refine ⟨(Sigma.ι (fun _ : P => (unitModule : ModuleCat.{v} R)) p) (equivShrink R 1), ?_⟩
  rw [← ConcreteCategory.comp_apply, Sigma.ι_desc]
  simp [toModule]

/-- The functor placing a module in degree `0` of `D(R)` commutes with direct sums. -/
private theorem preservesColimitsOfShape_singleFunctor_zero (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0) := by
  have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts (ModuleCat.{v} R) J
  have : PreservesColimitsOfShape (Discrete J)
      (CochainComplex.singleFunctor (ModuleCat.{v} R) 0) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.single (ModuleCat.{v} R) (ComplexShape.up ℤ) 0))
  exact preservesColimitsOfShape_of_natIso (DerivedCategory.singleFunctorIsoCompQ _ 0).symm

/-- A projective module is a retract of a direct sum of copies of `R`. -/
private theorem exists_retract_sigma_unit (P : ModuleCat.{v} R) [Projective P] :
    ∃ (J : Type v) (i : P ⟶ ∐ fun _ : J => (unitModule : ModuleCat.{v} R))
      (r : (∐ fun _ : J => (unitModule : ModuleCat.{v} R)) ⟶ P), i ≫ r = 𝟙 P := by
  have := epi_sigmaDesc_toModule P
  exact ⟨P, Projective.factorThru (𝟙 P) (Sigma.desc fun p : P => toModule p),
    Sigma.desc fun p : P => toModule p, Projective.factorThru_comp _ _⟩

/-- Every module is the third term of a short exact sequence of projectives, when `Ext²`
vanishes. -/
private theorem exists_shortExact_projective [HasExt.{w} (ModuleCat.{v} R)]
    (hExt : ∀ (A B : ModuleCat.{v} R) (e : Abelian.Ext.{w} B A 2), e = 0) (A : ModuleCat.{v} R) :
    ∃ S : ShortComplex (ModuleCat.{v} R),
      S.ShortExact ∧ Projective S.X₁ ∧ Projective S.X₂ ∧ S.X₃ = A := by
  have := epi_sigmaDesc_toModule A
  let e := Sigma.desc fun p : A => toModule p
  let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hS : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel (kernelIsKernel e) }
  have hA : HasProjectiveDimensionLT A 2 :=
    hasProjectiveDimensionLT_of_forall_ext_eq_zero A 2 fun B x => hExt B A x
  have h₂ : HasProjectiveDimensionLT S.X₂ 1 :=
    projective_iff_hasProjectiveDimensionLT_one.mp (inferInstance : Projective S.X₂)
  exact ⟨S, hS, projective_iff_hasProjectiveDimensionLT_one.mpr
    (hS.hasProjectiveDimensionLT_X₁ 1 h₂ hA), inferInstance, rfl⟩

variable (hF : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F)
  (hG : ∀ (J : Type v) (i : J → ℤ) (A : J → ModuleCat.{v} R) (c : ℤ), (∀ j, c ≤ i j) →
    ∀ n : ℤ, PreservesColimit
      (Discrete.functor fun j => (Ψ.obj ((DerivedCategory.singleFunctor _ (i j)).obj (A j)))⟦n⟧) G)
  (hbase : Inv F G α Ψ ((DerivedCategory.singleFunctor _ 0).obj (unitModule : ModuleCat.{v} R)))

include hF hG hbase

omit [HasShift D ℤ] [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [Ψ.CommShift ℤ] [Ψ.IsTriangulated] in
/-- Free modules: direct sums of copies of `R`, placed in degree `0`. -/
theorem Inv.single_sigma_unit (J : Type v) :
    Inv F G α Ψ ((DerivedCategory.singleFunctor _ 0).obj
      (∐ fun _ : J => (unitModule : ModuleCat.{v} R))) := by
  have := preservesColimitsOfShape_singleFunctor_zero (R := R) J
  have h := Inv.sigma hF (fun _ : J => (DerivedCategory.singleFunctor _ 0).obj
      (unitModule : ModuleCat.{v} R))
    (hG J (fun _ => 0) (fun _ => unitModule) 0 (fun _ => le_rfl)) (fun _ => hbase)
  exact Inv.of_iso (PreservesCoproduct.iso (DerivedCategory.singleFunctor _ 0)
    fun _ : J => (unitModule : ModuleCat.{v} R)).symm h

omit [HasShift D ℤ] [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [Ψ.CommShift ℤ] [Ψ.IsTriangulated] in
/-- Projective modules, placed in degree `0`: retracts of free modules. -/
theorem Inv.single_projective (P : ModuleCat.{v} R) [Projective P] :
    Inv F G α Ψ ((DerivedCategory.singleFunctor _ 0).obj P) := by
  obtain ⟨J, i, r, hir⟩ := exists_retract_sigma_unit P
  exact Inv.of_retract ((DerivedCategory.singleFunctor _ 0).map i)
    ((DerivedCategory.singleFunctor _ 0).map r)
    (by rw [← Functor.map_comp, hir, CategoryTheory.Functor.map_id])
    (Inv.single_sigma_unit hF hG hbase J)

variable [HasExt.{w} (ModuleCat.{v} R)]
  (hExt : ∀ (A B : ModuleCat.{v} R) (e : Abelian.Ext.{w} B A 2), e = 0)

include hExt

/-- All modules, placed in degree `0`: a projective resolution of length one. -/
theorem Inv.single_zero (A : ModuleCat.{v} R) :
    Inv F G α Ψ ((DerivedCategory.singleFunctor _ 0).obj A) := by
  obtain ⟨S, hS, _, _, rfl⟩ := exists_shortExact_projective hExt A
  exact Inv.of_distinguished₃ _ hS.singleTriangle_distinguished
    (Inv.single_projective hF hG hbase S.X₁) (Inv.single_projective hF hG hbase S.X₂)

/-- Modules placed in any degree. -/
theorem Inv.single (A : ModuleCat.{v} R) (i : ℤ) :
    Inv F G α Ψ ((DerivedCategory.singleFunctor _ i).obj A) :=
  Inv.of_iso (((DerivedCategory.singleFunctors (ModuleCat.{v} R)).shiftIso (-i) i 0
    (by omega)).app A) ((Inv.single_zero hF hG hbase hExt A).shift (-i))

/-- **The dévissage.** `α` is invertible at every shift of `Ψ(M)` for every bounded below
`M ∈ D(R)`. -/
theorem isIso_app_of_isGE (M : DerivedCategory (ModuleCat.{v} R)) (b : ℤ) [M.IsGE b] (n : ℤ) :
    IsIso (α.app ((Ψ.obj M)⟦n⟧)) := by
  obtain ⟨A, ⟨e⟩⟩ :=
    DerivedCategory.nonempty_iso_sigma_singleFunctor_of_isGE_of_forall_ext_two_eq_zero hExt M b
  exact Inv.of_iso e (Inv.sigma hF _
    (hG (ULift.{v} ℕ) (fun k => b + k.down) A b (fun k => by omega))
    (fun k => Inv.single hF hG hbase hExt (A k) (b + k.down))) n

end Devissage

/-- If `H(X)` lies in degrees `≥ a`, then `H(X⟦n⟧)` lies in degrees `≥ a'` when `n + a' = a`. -/
private theorem isGE_obj_shift {S B : Type*} [Category* S] [Category* B] [Abelian B]
    [HasShift S ℤ] (H : S ⥤ DerivedCategory B) [H.CommShift ℤ] {X : S} (a n a' : ℤ) (h : n + a' = a)
    [(H.obj X).IsGE a] : (H.obj (X⟦n⟧)).IsGE a' := by
  have := DerivedCategory.TStructure.t.isGE_shift (H.obj X) a n a' h
  exact DerivedCategory.TStructure.t.isGE_of_iso (X := (H.obj X)⟦n⟧)
    ((H.commShiftIso n).app X).symm a'

section Bound

variable {B : Type*} [Category* B] [Abelian B] [IsGrothendieckAbelian.{v} B]

omit [IsGrothendieckAbelian.{v} B] in
/-- A retract of an object of `D(B)` lying in degrees `≥ n` lies in degrees `≥ n`. -/
theorem isGE_of_retract {X Y : DerivedCategory B} (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X)
    (n : ℤ) [Y.IsGE n] : X.IsGE n :=
  (DerivedCategory.isGE_iff X n).2 fun q hq => by
    rw [IsZero.iff_id_eq_zero]
    have h := congrArg (DerivedCategory.homologyFunctor B q).map hir
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at h
    rw [← h, (DerivedCategory.isZero_of_isGE Y n q hq).eq_of_tgt
      ((DerivedCategory.homologyFunctor B q).map i) 0, zero_comp]

variable (H : DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory B) [H.CommShift ℤ]
  [H.IsTriangulated] [∀ I : Type v, PreservesColimitsOfShape (Discrete I) H] (a : ℤ)
  (hunit : (H.obj ((DerivedCategory.singleFunctor _ 0).obj (unitModule : ModuleCat.{v} R))).IsGE a)

include hunit

omit [H.CommShift ℤ] [H.IsTriangulated] in
/-- The bound on free modules. -/
theorem isGE_obj_single_sigma_unit (J : Type v) :
    (H.obj ((DerivedCategory.singleFunctor _ 0).obj
      (∐ fun _ : J => (unitModule : ModuleCat.{v} R)))).IsGE a := by
  have := preservesColimitsOfShape_singleFunctor_zero (R := R) J
  have hs := Stacks.Duality.isGE_sigmaObj B (fun _ : J => H.obj
    ((DerivedCategory.singleFunctor _ 0).obj (unitModule : ModuleCat.{v} R))) a fun _ => hunit
  refine DerivedCategory.TStructure.t.isGE_of_iso (X := ∐ fun _ : J => H.obj
    ((DerivedCategory.singleFunctor _ 0).obj (unitModule : ModuleCat.{v} R))) ?_ a
  exact (PreservesCoproduct.iso H _).symm ≪≫ H.mapIso
    (PreservesCoproduct.iso (DerivedCategory.singleFunctor _ 0)
      fun _ : J => (unitModule : ModuleCat.{v} R)).symm

omit [H.CommShift ℤ] [H.IsTriangulated] in
/-- The bound on projective modules. -/
theorem isGE_obj_single_projective (P : ModuleCat.{v} R) [Projective P] :
    (H.obj ((DerivedCategory.singleFunctor _ 0).obj P)).IsGE a := by
  obtain ⟨J, i, r, hir⟩ := exists_retract_sigma_unit P
  have := isGE_obj_single_sigma_unit H a hunit J
  exact isGE_of_retract (H.map ((DerivedCategory.singleFunctor _ 0).map i))
    (H.map ((DerivedCategory.singleFunctor _ 0).map r))
    (by rw [← Functor.map_comp, ← Functor.map_comp, hir, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]) a

variable [HasExt.{w} (ModuleCat.{v} R)]
  (hExt : ∀ (A B : ModuleCat.{v} R) (e : Abelian.Ext.{w} B A 2), e = 0)

include hExt

/-- The bound on modules placed in degree `0`: one less, by a projective resolution of length
one. -/
theorem isGE_obj_single_zero (A : ModuleCat.{v} R) :
    (H.obj ((DerivedCategory.singleFunctor _ 0).obj A)).IsGE (a - 1) := by
  obtain ⟨S, hS, _, _, rfl⟩ := exists_shortExact_projective hExt A
  have hT := H.map_distinguished _ (rot_of_distTriang _ hS.singleTriangle_distinguished)
  have h₁ : (H.obj ((DerivedCategory.singleFunctor _ 0).obj S.X₂)).IsGE (a - 1) :=
    have := isGE_obj_single_projective H a hunit S.X₂
    DerivedCategory.TStructure.t.isGE_of_ge _ (a - 1) a (by omega)
  have h₃ : (H.obj (((DerivedCategory.singleFunctor _ 0).obj S.X₁)⟦(1 : ℤ)⟧)).IsGE (a - 1) :=
    have := isGE_obj_single_projective H a hunit S.X₁
    isGE_obj_shift H a 1 (a - 1) (by omega)
  exact DerivedCategory.TStructure.t.isGE₂ _ hT (a - 1) h₁ h₃

/-- **The bound on modules placed in any degree**: if `H(R)` lies in degrees `≥ a`, then
`H(A[-i])` lies in degrees `≥ a + i - 1` for every module `A`. -/
theorem isGE_obj_single (A : ModuleCat.{v} R) (i : ℤ) :
    (H.obj ((DerivedCategory.singleFunctor _ i).obj A)).IsGE (a + i - 1) := by
  have := isGE_obj_single_zero H a hunit hExt A
  have := isGE_obj_shift H (a - 1) (-i) (a + i - 1) (by omega)
    (X := (DerivedCategory.singleFunctor _ 0).obj A)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (X := H.obj (((DerivedCategory.singleFunctor _ 0).obj A)⟦-i⟧)) (H.mapIso
    (((DerivedCategory.singleFunctors (ModuleCat.{v} R)).shiftIso (-i) i 0
      (by omega)).app A)) _

end Bound

end Stacks.EtaleCohomology.PointProjectionFormulaBoundedBelow
