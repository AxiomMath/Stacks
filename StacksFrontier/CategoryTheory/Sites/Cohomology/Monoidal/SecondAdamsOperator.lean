module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison
public import StacksFrontier.Homology.DerivedCategory.Monoidal.SecondAdamsOperator

/-!
# The second Adams operator for modules on a ringed site in which `2` is invertible

Let `(C, O)` be a ringed site such that `2` is a unit in every ring of sections of `O`. Then
`2` is invertible on every `O`-module, and the construction
`Stacks.SecondAdamsPerfect.secondAdams` applies to `D(Mod(O))` with its symmetric monoidal
structure of [Stacks, Tag 0FPT] (`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`) and to
any triangulated subcategory closed under summands and under the derived tensor product.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.isIso_two_smul_id_of_isUnit`: `2` is invertible on
  every sheaf of modules over a sheaf of rings whose rings of sections have `2` as a unit.
* `Stacks.SheafOfModules.DerivedMonoidal.secondAdamsOperator`: the operator
  `[L] ↦ [(L ⊗^L L)^+] - [(L ⊗^L L)^-]` on the `K`-group of such a subcategory.
* `Stacks.SheafOfModules.DerivedMonoidal.secondAdamsOperator_cls`: its value on the class of an
  object, through any splittings of the invariants and the anti-invariants of the switch.
* `Stacks.SheafOfModules.DerivedMonoidal.secondAdams_distinguished`: additivity of
  `[(L ⊗^L L)^+] - [(L ⊗^L L)^-]` along distinguished triangles.

## References

* [Stacks Project, Tag 0FEK](https://stacks.math.columbia.edu/tag/0FEK)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated

universe d u

/-- **`2` is invertible on every sheaf of modules** over a sheaf of rings in whose rings of
sections `2` is a unit: on sections, multiplication by `2` is bijective. -/
theorem SheafOfModules.isIso_two_smul_id_of_isUnit {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (h2 : ∀ U, IsUnit (2 : R.obj.obj U))
    (M : SheafOfModules.{u} R) : IsIso ((2 : ℤ) • 𝟙 M) := by
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj
  have : G.ReflectsIsomorphisms :=
    inferInstanceAs
      (SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf _).ReflectsIsomorphisms
  suffices IsIso (G.map ((2 : ℤ) • 𝟙 M)) from isIso_of_reflects_iso _ G
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have hb : Function.Bijective (fun m : M.val.obj U => (2 : R.obj.obj U) • m) := by
    refine ⟨fun a b hab => (h2 U).smul_left_cancel.1 hab, fun m =>
      ⟨(↑(h2 U).unit⁻¹ : R.obj.obj U) • m, ?_⟩⟩
    dsimp only
    rw [smul_smul, IsUnit.mul_val_inv, one_smul]
  have hfun : (fun m : M.val.obj U => (2 : R.obj.obj U) • m) =
      ⇑(ConcreteCategory.hom ((G.map ((2 : ℤ) • 𝟙 M)).app U)) := by
    funext m
    rw [two_smul, two_smul ℤ (𝟙 M)]
    rfl
  rw [← hfun]
  exact hb

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

omit [HasDerivedCategory.{d} (Mod R)] in
/-- `2` is invertible on every `O`-module when it is a unit in every ring of sections of `O`. -/
theorem isIso_two_smul_id (h2 : ∀ U, IsUnit (2 : R.obj.obj U)) (M : Mod R) :
    IsIso ((2 : ℤ) • 𝟙 M) :=
  SheafOfModules.isIso_two_smul_id_of_isUnit _ h2 M

variable (P : ObjectProperty (DerivedModules R)) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- **The second Adams operator** `[L] ↦ [(L ⊗^L L)^+] - [(L ⊗^L L)^-]` on the `K`-group of a
triangulated subcategory `P` of `D(Mod(O))`, closed under summands and under the derived tensor
product, when `2` is a unit in every ring of sections of `O`. -/
def secondAdamsOperator (h2 : ∀ U, IsUnit (2 : R.obj.obj U))
    (hsum : ∀ K L : DerivedModules R, P (K ⊞ L) → P K)
    (htensor : letI := derivedMonoidal R
      ∀ K L : DerivedModules R, P K → P L → P (K ⊗ L)) :
    K0 P.FullSubcategory →+ K0 P.FullSubcategory :=
  haveI := isIso_two_smul_id R h2
  Stacks.SecondAdamsPerfect.secondAdams (Mod R) (exists_kFlat_resolution R) P hsum htensor

variable (h2 : ∀ U, IsUnit (2 : R.obj.obj U))
  (hsum : ∀ K L : DerivedModules R, P (K ⊞ L) → P K)
  (htensor : letI := derivedMonoidal R
    ∀ K L : DerivedModules R, P K → P L → P (K ⊗ L))

/-- **`ψ²([L]) = [(L ⊗^L L)^+] - [(L ⊗^L L)^-]`** for any splittings of the idempotents
`(𝟙 ± σ)/2` of the switch `σ` of `L ⊗^L L`. -/
theorem secondAdamsOperator_cls (L : P.FullSubcategory) :
    letI := derivedMonoidal R
    letI := derivedSymmetric R
    haveI := isIso_two_smul_id R h2
    ∀ (sp : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.invariantIdempotent
          ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj)))
      (sm : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.antiInvariantIdempotent
          ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj)))
      (hp : P sp.obj) (hm : P sm.obj),
      secondAdamsOperator R P h2 hsum htensor (K0.cls L) =
        K0.cls (⟨sp.obj, hp⟩ : P.FullSubcategory) - K0.cls (⟨sm.obj, hm⟩ : P.FullSubcategory) := by
  have _ := isIso_two_smul_id R h2
  intro sp sm hp hm
  rw [secondAdamsOperator, Stacks.SecondAdamsPerfect.secondAdams_cls]
  exact Stacks.SecondAdamsPerfect.secondAdamsValue_eq (Mod R) (exists_kFlat_resolution R) P L
    sp sm hp hm

include hsum htensor in
/-- **The invariants and the anti-invariants of the switch on `L ⊗^L L` exist and lie in `P`**,
whichever splittings are taken. -/
theorem exists_switchSplittings (L : P.FullSubcategory) :
    letI := derivedMonoidal R
    letI := derivedSymmetric R
    haveI := isIso_two_smul_id R h2
    Nonempty (Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.invariantIdempotent
          ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj))) ∧
      Nonempty (Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.antiInvariantIdempotent
          ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj))) ∧
      (∀ s : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.invariantIdempotent
          ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj)), P s.obj) ∧
      (∀ s : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.antiInvariantIdempotent
          ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj)), P s.obj) := by
  have _ := isIso_two_smul_id R h2
  obtain ⟨h₁, h₂⟩ :=
    Stacks.SecondAdamsPerfect.nonempty_invariantsSplitting (Mod R) (exists_kFlat_resolution R) L.obj
  exact ⟨h₁, h₂,
    Stacks.SecondAdamsPerfect.prop_invariantsSplitting_obj (Mod R) (exists_kFlat_resolution R) P
      hsum htensor L,
    Stacks.SecondAdamsPerfect.prop_antiInvariantsSplitting_obj (Mod R) (exists_kFlat_resolution R)
      P hsum htensor L⟩

include hsum htensor in
/-- **`[(L ⊗^L L)^+] - [(L ⊗^L L)^-]` is additive along distinguished triangles of `P`**: for a
distinguished triangle `L₁ ⟶ L₂ ⟶ L₃ ⟶ L₁[1]` and any splittings `sᵢ^±` of the invariants and
the anti-invariants of the switch on `Lᵢ ⊗^L Lᵢ`,
`[s₂^+] - [s₂^-] = ([s₁^+] - [s₁^-]) + ([s₃^+] - [s₃^-])`. -/
theorem secondAdams_distinguished (T : Triangle P.FullSubcategory)
    (hT : T ∈ distTriang P.FullSubcategory) :
    letI := derivedMonoidal R
    letI := derivedSymmetric R
    haveI := isIso_two_smul_id R h2
    ∀ (sp₁ : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.invariantIdempotent
          ((β_ T.obj₁.obj T.obj₁.obj).hom : T.obj₁.obj ⊗ T.obj₁.obj ⟶ T.obj₁.obj ⊗ T.obj₁.obj)))
      (sm₁ : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.antiInvariantIdempotent
          ((β_ T.obj₁.obj T.obj₁.obj).hom : T.obj₁.obj ⊗ T.obj₁.obj ⟶ T.obj₁.obj ⊗ T.obj₁.obj)))
      (sp₂ : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.invariantIdempotent
          ((β_ T.obj₂.obj T.obj₂.obj).hom : T.obj₂.obj ⊗ T.obj₂.obj ⟶ T.obj₂.obj ⊗ T.obj₂.obj)))
      (sm₂ : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.antiInvariantIdempotent
          ((β_ T.obj₂.obj T.obj₂.obj).hom : T.obj₂.obj ⊗ T.obj₂.obj ⟶ T.obj₂.obj ⊗ T.obj₂.obj)))
      (sp₃ : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.invariantIdempotent
          ((β_ T.obj₃.obj T.obj₃.obj).hom : T.obj₃.obj ⊗ T.obj₃.obj ⟶ T.obj₃.obj ⊗ T.obj₃.obj)))
      (sm₃ : Stacks.SecondAdamsPerfect.IdempotentSplitting
        (Stacks.SecondAdamsPerfect.antiInvariantIdempotent
          ((β_ T.obj₃.obj T.obj₃.obj).hom : T.obj₃.obj ⊗ T.obj₃.obj ⟶ T.obj₃.obj ⊗ T.obj₃.obj)))
      (hp₁ : P sp₁.obj) (hm₁ : P sm₁.obj) (hp₂ : P sp₂.obj) (hm₂ : P sm₂.obj)
      (hp₃ : P sp₃.obj) (hm₃ : P sm₃.obj),
      K0.cls (⟨sp₂.obj, hp₂⟩ : P.FullSubcategory) - K0.cls (⟨sm₂.obj, hm₂⟩ : P.FullSubcategory) =
        (K0.cls (⟨sp₁.obj, hp₁⟩ : P.FullSubcategory) -
          K0.cls (⟨sm₁.obj, hm₁⟩ : P.FullSubcategory)) +
        (K0.cls (⟨sp₃.obj, hp₃⟩ : P.FullSubcategory) -
          K0.cls (⟨sm₃.obj, hm₃⟩ : P.FullSubcategory)) := by
  have _ := isIso_two_smul_id R h2
  intro sp₁ sm₁ sp₂ sm₂ sp₃ sm₃ hp₁ hm₁ hp₂ hm₂ hp₃ hm₃
  have key := Stacks.SecondAdamsPerfect.secondAdamsValue_distinguished (Mod R)
    (exists_kFlat_resolution R) P hsum htensor T hT
  rwa [Stacks.SecondAdamsPerfect.secondAdamsValue_eq (Mod R) (exists_kFlat_resolution R) P
      T.obj₂ sp₂ sm₂ hp₂ hm₂,
    Stacks.SecondAdamsPerfect.secondAdamsValue_eq (Mod R) (exists_kFlat_resolution R) P
      T.obj₁ sp₁ sm₁ hp₁ hm₁,
    Stacks.SecondAdamsPerfect.secondAdamsValue_eq (Mod R) (exists_kFlat_resolution R) P
      T.obj₃ sp₃ sm₃ hp₃ hm₃] at key

end Stacks.SheafOfModules.DerivedMonoidal

end
