module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.ExtUnit
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSum
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Morphisms between shifted twists on projective space

Let `k` be a field and `X = ℙⁿ_k = Proj k[T₀, …, Tₙ]`. In the derived category of
`𝒪_X`-modules, `Hom(𝒪(d), 𝒪(e)[j]) = Ext^j(𝒪(d), 𝒪(e)) = H^j(X, 𝒪(e - d))`. This file proves the
vanishing half of that identification: `Hom(𝒪(d), 𝒪(e)[j])` vanishes whenever
`H^j(X, 𝒪(e - d))` does, and for every `j < 0`.

## Main results

* `Stacks.AlgebraicGeometry.TwistExt.subsingleton_hom_twist_shift_of_isZero`: the vanishing for
  `j ≥ 0`, from the vanishing of the cohomology of `𝒪(e - d)`.
* `Stacks.AlgebraicGeometry.TwistExt.subsingleton_hom_twist_shift_of_neg`: the vanishing for
  `j < 0`.
* `Stacks.AlgebraicGeometry.TwistExt.subsingleton_hom_twist_shift`: the vanishing unless `j = 0`
  and `e - d ≥ 0`, or `j = n` and `e - d < 0`.
* `Stacks.AlgebraicGeometry.TwistExt.subsingleton_hom_twist_shift_of_le`: the vanishing for
  `-n ≤ e - d`, unless `j = 0 ≤ e - d`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart

universe w u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.TwistExt

open Stacks.AlgebraicGeometry.ExampleGenerator

variable (k : Type u) [Field k] (n : ℕ)

/-- `Ext` groups in the category of `𝒪_{ℙⁿ_k}`-modules, in the universe of its morphisms. -/
local instance hasExt_mods : HasExt.{u} (Mods k n) :=
  @hasExt_of_hasDerivedCategory _ _ _ (SheafOfModules.hasDerivedCategory _)

/-- `𝒪(d)` placed in degree zero of a model of the derived category of `𝒪_{ℙⁿ_k}`-modules. -/
abbrev twistObj [HasDerivedCategory.{w} (Mods k n)] (d : ℤ) : DerivedCategory (Mods k n) :=
  (DerivedCategory.singleFunctor (Mods k n) 0).obj
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d)

/-- `𝒪(d)` is invertible, in the spelling the twist functor asks for. -/
local instance isInvertible_twistingSheaf (d : ℤ) : Stacks.SheafOfModules.IsInvertible
    (ProjectiveSpectrum.Proj.structureSheaf (polyGrading k n)).obj
    (Stacks.AlgebraicGeometry.ProjTwistFunctor.projRingSheaf (polyGrading k n)).property
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
    (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf (polyGrading k n)
      (Stacks.PicardUFD.degreeOneCover k n) d)

/-- Twisting is an autoequivalence of the category of `𝒪_{ℙⁿ_k}`-modules. -/
local instance isEquivalence_twistFunctor (d : ℤ) :
    (Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor (polyGrading k n) d).IsEquivalence :=
  Stacks.AlgebraicGeometry.ProjTwistFunctor.isEquivalence_twistFunctor _ d

/-- `Ext^j(A, B)` is subsingleton exactly when `Hom(A, B[j])` is, in the derived category. -/
theorem subsingleton_ext_iff {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
    [HasExt.{u} C] (A B : C) (j : ℕ) :
    Subsingleton (Abelian.Ext.{u} A B j) ↔
      Subsingleton ((DerivedCategory.singleFunctor C 0).obj A ⟶
        ((DerivedCategory.singleFunctor C 0).obj B)⟦(j : ℤ)⟧) :=
  (Abelian.Ext.homEquiv (C := C)).subsingleton_congr

/-- Morphisms in the derived category between objects in degree zero are invariant under
isomorphisms of the two objects. -/
theorem subsingleton_hom_single_shift_congr {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{w} C] {A A' B B' : C} (eA : A ≅ A') (eB : B ≅ B') (j : ℤ) :
    Subsingleton ((DerivedCategory.singleFunctor C 0).obj A ⟶
        ((DerivedCategory.singleFunctor C 0).obj B)⟦j⟧) ↔
      Subsingleton ((DerivedCategory.singleFunctor C 0).obj A' ⟶
        ((DerivedCategory.singleFunctor C 0).obj B')⟦j⟧) :=
  (Iso.homCongr ((DerivedCategory.singleFunctor C 0).mapIso eA)
    ((shiftFunctor _ j).mapIso ((DerivedCategory.singleFunctor C 0).mapIso eB))).subsingleton_congr

/-- **`Hom(𝒪(d), 𝒪(e)[j])` vanishes when `H^j(ℙⁿ_k, 𝒪(e - d))` does.** -/
theorem subsingleton_hom_twist_shift_of_isZero [HasDerivedCategory.{w} (Mods k n)] (d e : ℤ) (j : ℕ)
    (h : IsZero
      (((ExtUnit.topSections (AlgebraicGeometry.Proj (polyGrading k n))).rightDerived j).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) (e - d)))) :
    Subsingleton (twistObj k n d ⟶ (twistObj k n e)⟦(j : ℤ)⟧) := by
  let T := Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor (polyGrading k n) (-d)
  refine (subsingleton_ext_iff (C := Mods k n) _ _ j).1 ?_
  have hbij := T.mapExt_bijective_of_preservesInjectiveObjects
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) e) j
  suffices Subsingleton (Abelian.Ext.{u}
      (T.obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d))
      (T.obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) e)) j) from
    ⟨fun x y => hbij.1 (Subsingleton.elim _ _)⟩
  have eA : T.obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d) ≅
      ExtUnit.unitModule (AlgebraicGeometry.Proj (polyGrading k n)) :=
    Stacks.AlgebraicGeometry.ProjTwistRank.tensorTwistingSheafIso k n d (-d) ≪≫
      eqToIso (by rw [add_neg_cancel]) ≪≫
      Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading k n)
  have eB : T.obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) e) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) (e - d) :=
    Stacks.AlgebraicGeometry.ProjTwistRank.tensorTwistingSheafIso k n e (-d) ≪≫
      eqToIso (by rw [sub_eq_add_neg])
  refine (subsingleton_ext_iff (C := Mods k n) _ _ j).2 ?_
  refine (subsingleton_hom_single_shift_congr eA eB (j : ℤ)).2 ?_
  exact (subsingleton_ext_iff (C := Mods k n) _ _ j).1
    (ExtUnit.subsingleton_ext_unit_of_isZero (AlgebraicGeometry.Proj (polyGrading k n)) _ j h)

/-- **No morphism lowers degree between objects in degree zero**: `Hom(A, B[j]) = 0` for `j < 0`
in the derived category of any abelian category. -/
theorem subsingleton_hom_single_shift_of_neg {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{w} C] (A B : C) {j : ℤ} (hj : j < 0) :
    Subsingleton ((DerivedCategory.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.singleFunctor C 0).obj B)⟦j⟧) := by
  have : DerivedCategory.TStructure.t.IsGE (((DerivedCategory.singleFunctor C 0).obj B)⟦j⟧)
      (-j) := DerivedCategory.TStructure.t.isGE_shift _ 0 j (-j) (by omega)
  have hA : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor C 0).obj A) 0 :=
    (inferInstance : ((DerivedCategory.singleFunctor C 0).obj A).IsLE 0)
  exact ⟨fun u v => by
    rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE u 0 (-j) (by omega) hA this,
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE v 0 (-j) (by omega) hA this]⟩

/-- **`Hom(𝒪(d), 𝒪(e)[j])` vanishes unless `j = 0` and `e - d ≥ 0`, or `j = n` and
`e - d < 0`.** -/
theorem subsingleton_hom_twist_shift [HasDerivedCategory.{w} (Mods k n)] (d e j : ℤ)
    (hj : ¬ ((j = 0 ∧ 0 ≤ e - d) ∨ (j = n ∧ e - d < 0))) :
    Subsingleton (twistObj k n d ⟶ (twistObj k n e)⟦j⟧) := by
  rcases lt_or_ge j 0 with hneg | hnn
  · exact subsingleton_hom_single_shift_of_neg _ _ hneg
  · lift j to ℕ using hnn
    refine subsingleton_hom_twist_shift_of_isZero k n d e j ?_
    have h := Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology k n (e - d) j
      (by exact_mod_cast hj)
    rwa [ModuleCat.isZero_iff_subsingleton] at h ⊢

/-- **`Hom(𝒪(d), 𝒪(e)[j])` vanishes for `-n ≤ e - d`, except for `j = 0 ≤ e - d`.** -/
theorem subsingleton_hom_twist_shift_of_le [HasDerivedCategory.{w} (Mods k n)] (d e j : ℤ)
    (hde : -(n : ℤ) ≤ e - d) (hj : j ≠ 0 ∨ e - d < 0) :
    Subsingleton (twistObj k n d ⟶ (twistObj k n e)⟦j⟧) := by
  by_cases htop : j = n ∧ e - d < 0
  · obtain ⟨rfl, hneg⟩ := htop
    refine subsingleton_hom_twist_shift_of_isZero k n d e n ?_
    have h :=
      (Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoNegative k n (e - d) hneg).isZero_iff.2
        (by
          rw [Stacks.ProjectiveSpace.Cohomology.negativeTwistPart_eq_bot_of_le k n (e - d) hde]
          exact ModuleCat.isZero_of_subsingleton _)
    rwa [ModuleCat.isZero_iff_subsingleton] at h ⊢
  · exact subsingleton_hom_twist_shift k n d e j (by omega)

end Stacks.AlgebraicGeometry.TwistExt

end
