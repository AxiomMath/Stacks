module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceKernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite type for the total module of a graded module

`SheafOfModules.GradedModule.ungradedSheaf` is the total module `⨁ₙ Mₙ` of a graded module over
a sheaf of graded algebras, as a sheaf of modules over the ungraded realization of the algebra.
Sheafification preserves the sectionwise finite-type condition, so the total module of a graded
module of finite type is of finite type, both sectionwise and in Mathlib's categorical sense.

## Main results

* `Stacks.SheafOfModules.generates_sheafification`: the images of a generating family under the
  sheafification unit generate the sheafification.
* `Stacks.SheafOfModules.isFiniteType_presheaf_sheafification`: sheafification preserves
  sectionwise finite type.
* `SheafOfModules.GradedModule.generatesHomogeneous_of_generates`: generation of a graded module by
  finitely many homogeneous sections, with homogeneous coefficients
  (`SheafOfModules.GradedModule.Generates`), is generation with coefficients in the ungraded
  realization (`Stacks.GradedModule.GeneratesHomogeneous`).
* `SheafOfModules.GradedModule.isFiniteType_presheaf_ungradedSheaf` and
  `SheafOfModules.GradedModule.isFiniteType_ungradedSheaf`: the total module of a graded module
  of finite type is of finite type.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.SheafOfModules

section Sheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The sheafification unit of a presheaf of modules, as a morphism of presheaves of modules
into the restriction of scalars of the sheafification along `α`. -/
noncomputable abbrev sheafificationUnit (M₀ : PresheafOfModules.{w} R₀) :
    M₀ ⟶ (PresheafOfModules.restrictScalars α).obj
      ((_root_.SheafOfModules.forget R).obj ((PresheafOfModules.sheafification.{w} α).obj M₀)) :=
  (PresheafOfModules.sheafificationAdjunction α).unit.app M₀

/-- The image of a section under the sheafification unit, read as a section of the
sheafification. -/
noncomputable abbrev sheafifyUnitSection (M₀ : PresheafOfModules.{w} R₀) {U : C}
    (x : M₀.obj (op U)) :
    (((PresheafOfModules.sheafification.{w} α).obj M₀).val.obj (op U) : Type w) :=
  (sheafificationUnit α M₀).app (op U) x

/-- The images of a generating family under the sheafification unit generate the
sheafification. -/
theorem generates_sheafification (M₀ : PresheafOfModules.{w} R₀) {U : C} {n : ℕ}
    (s : Fin n → M₀.obj (op U)) (hs : PresheafOfModules.Generates J M₀ s) :
    PresheafOfModules.Generates J ((PresheafOfModules.sheafification.{w} α).obj M₀).val
      (fun i => sheafifyUnitSection α M₀ (s i)) := by
  classical
  intro V f t
  refine exists_cover_comb_of_bind _ f t
    (Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J M₀.presheaf) t) ?_
  intro W g hg
  obtain ⟨p, hp⟩ := hg
  obtain ⟨T, hT, hTgen⟩ := hs W (g ≫ f) p
  refine ⟨T, hT, fun Z k hk => ?_⟩
  obtain ⟨a, ha⟩ := hTgen Z k hk
  refine ⟨fun i => α.app (op Z) (a i), ?_⟩
  have h2 : ∑ i, a i • M₀.restrictₛₗ ((k ≫ g) ≫ f).op (s i) = M₀.restrictₛₗ k.op p := by
    rw [Category.assoc]; exact ha
  have h3 := congrArg ((sheafificationUnit α M₀).app (op Z)) h2
  rw [map_sum] at h3
  refine Eq.trans ?_ (h3.trans ?_)
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, show (sheafificationUnit α M₀).app (op Z) (M₀.restrictₛₗ ((k ≫ g) ≫ f).op (s i))
      = _ from PresheafOfModules.naturality_apply (sheafificationUnit α M₀) ((k ≫ g) ≫ f).op (s i)]
    rfl
  · refine (PresheafOfModules.naturality_apply (sheafificationUnit α M₀) k.op p).trans ?_
    exact congrArg
      (fun y => ((PresheafOfModules.sheafification.{w} α).obj M₀).val.restrictₛₗ k.op y) hp
      |>.trans (restrict_restrict g k t)

/-- Sheafification preserves sectionwise finite type. -/
theorem isFiniteType_presheaf_sheafification (M₀ : PresheafOfModules.{w} R₀)
    (h : PresheafOfModules.IsFiniteType J M₀) :
    PresheafOfModules.IsFiniteType J ((PresheafOfModules.sheafification.{w} α).obj M₀).val := by
  obtain ⟨I, U, hU, hgen⟩ := h.exists_generators
  refine ⟨I, U, hU, fun i => ?_⟩
  obtain ⟨n, s, hs⟩ := hgen i
  exact ⟨n, fun j => sheafifyUnitSection α M₀ (s j), generates_sheafification α M₀ s hs⟩

end Sheafification

end Stacks.SheafOfModules

/-! ### From the graded module to the total module -/

namespace SheafOfModules.GradedModule

open Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {A : SheafOfModules.GradedAlgebra.{w, w} R} [A.IsCommutative]
  (M : SheafOfModules.GradedModule.{w, w, w} A)

omit [A.IsCommutative] in
/-- Transporting a homogeneous section along an equality of degrees does not change its image in
the total module. -/
theorem incl_castHom {i j : ℤ} (h : i = j) (X : Cᵒᵖ) (y : (M.piece i).val.obj X) :
    M.toPresheafGradedModule.incl i y =
      M.toPresheafGradedModule.incl j (SheafOfModules.castHom M.piece h X y) := by
  subst h
  rw [SheafOfModules.castHom_rfl]

omit [A.IsCommutative] in
/-- Images in the total module of a finite family of homogeneous sections add up. -/
theorem sum_incl {k : ℕ} (n : ℤ) (X : Cᵒᵖ) (y : Fin k → (M.piece n).val.obj X) :
    ∑ a, M.toPresheafGradedModule.incl n (y a) =
      M.toPresheafGradedModule.incl n (∑ a, y a) :=
  (map_sum (DirectSum.of (fun j : ℤ => ((M.piece j).val.obj X : Type w)) n) y Finset.univ).symm

/-- Generation of a graded module by finitely many homogeneous sections, with homogeneous
coefficients, is generation with coefficients in the ungraded realization. -/
theorem generatesHomogeneous_of_generates {U : C} {k : ℕ} (d : Fin k → ℤ)
    (s : ∀ a, (M.piece (d a)).val.obj (op U)) (hs : M.Generates (J := J) d s) :
    M.toPresheafGradedModule.GeneratesHomogeneous J d s := by
  intro n V f x
  obtain ⟨S, hS, hcomb⟩ := (M.generates_iff_combinationSieve_mem d s).mp hs n V f x
  refine ⟨S, hS, fun W g hg => ?_⟩
  obtain ⟨c, hc⟩ := hcomb W g hg
  refine ⟨fun a => A.toPresheafGradedAlgebra.incl (n - d a) (c a), ?_⟩
  have hterm : ∀ a : Fin k,
      A.toPresheafGradedAlgebra.incl (n - d a) (c a) •
          M.toPresheafGradedModule.totalRestrict (g ≫ f).op
            (M.toPresheafGradedModule.incl (d a) (s a)) =
        M.toPresheafGradedModule.incl n
          (M.smulSection n ((M.piece (d a)).val.restrictₛₗ (g ≫ f).op (s a)) (c a)) := by
    intro a
    rw [Stacks.GradedModule.totalRestrict_incl, Stacks.GradedModule.incl_smul_incl,
      M.smulSection_apply]
    exact incl_castHom M (show d a + (n - d a) = n by omega) (op W) _
  rw [Finset.sum_congr rfl fun a _ => hterm a, sum_incl, hc,
    Stacks.GradedModule.totalRestrict_incl]
  rfl

/-- The presheaf total module of a graded module of finite type is of finite type. -/
theorem isFiniteType_presheaf_totalPresheafMod (h : M.IsFiniteType (J := J)) :
    PresheafOfModules.IsFiniteType J M.toPresheafGradedModule.totalPresheafMod := by
  obtain ⟨I, U, hU, hgen⟩ := h.exists_generators
  refine Stacks.GradedModule.isFiniteType_totalPresheafMod
    (M := M.toPresheafGradedModule) J ⟨I, U, hU, fun i => ?_⟩
  obtain ⟨k, d, s, hs⟩ := hgen i
  exact ⟨k, d, s, generatesHomogeneous_of_generates M d s hs⟩

section Sheaf

variable [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The total module `⨁ₙ Mₙ` of a graded module of finite type is of finite type, in the
sectionwise sense, as a sheaf of modules over the ungraded realization of the algebra. -/
theorem isFiniteType_presheaf_ungradedSheaf (h : M.IsFiniteType (J := J)) :
    PresheafOfModules.IsFiniteType J M.ungradedSheaf.val :=
  isFiniteType_presheaf_sheafification (A.toPresheafGradedAlgebra.toTotalSheaf J)
    M.toPresheafGradedModule.totalPresheafMod (isFiniteType_presheaf_totalPresheafMod M h)

/-- The total module `⨁ₙ Mₙ` of a graded module of finite type is of finite type in Mathlib's
categorical sense. -/
theorem isFiniteType_ungradedSheaf
    [∀ Z : C, HasWeakSheafify (J.over Z) AddCommGrpCat.{w}]
    [∀ Z : C, (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (h : M.IsFiniteType (J := J)) : M.ungradedSheaf.IsFiniteType :=
  _root_.SheafOfModules.isFiniteType_of_presheaf_isFiniteType M.ungradedSheaf
    (isFiniteType_presheaf_ungradedSheaf M h)

end Sheaf

end SheafOfModules.GradedModule
