module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroIsCompact
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Complexes of acyclic objects compute a right derived functor of finite cohomological dimension

Let `F : 𝒜 ⥤ ℬ` be a left exact additive functor out of a Grothendieck abelian category, and
assume that `F` has finite cohomological dimension: some `R^n F` vanishes identically. Then every
unbounded cochain complex `J` whose terms are right acyclic for `F` computes the right derived
functor `RF : D(𝒜) ⥤ D(ℬ)`, i.e. the unit `F(J) ⟶ RF(J)` is an isomorphism.

This is part (2) of [Stacks, Tag 07K7], which is
`CategoryTheory.Functor.hasRightDerivedFunctor_of_isZero_rightDerived` for right derived
functors along the localization `DerivedCategory.Qh` of the homotopy category. The statement here
is for an arbitrary right derived functor along the localization `DerivedCategory.Q` of cochain
complexes.

All names are in the namespace `CategoryTheory.Functor`.

## Main results

* `quasiIso_map_of_isIso_rightDerivedUnit_app`: if the unit of some right derived functor along
  `DerivedCategory.Qh` is invertible at `J`, then `F` carries every quasi-isomorphism from `J` into
  a K-injective complex to a quasi-isomorphism.
* `isIso_rightDerivedUnit_app_of_quasiIso_map`: conversely, the unit of every right derived functor
  along `DerivedCategory.Q` is invertible at `J` as soon as `F` carries some such quasi-isomorphism
  to a quasi-isomorphism.
* `quasiIso_map_of_isIso_rightDerivedUnit_app_Q`: the first statement, along `DerivedCategory.Q`.
* `isIso_app_of_rightAcyclic_of_isZero_rightDerived`: the statement above.

## References

* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- If the unit of a right derived functor of `F` along `DerivedCategory.Qh` is invertible at a
complex `J`, then `F` carries any quasi-isomorphism `s : J ⟶ I` into a K-injective complex to a
quasi-isomorphism. -/
theorem quasiIso_map_of_isIso_rightDerivedUnit_app (F : A ⥤ B) [F.Additive]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {J I : CochainComplex A ℤ} (s : J ⟶ I) [QuasiIso s] (hI : I.IsKInjective)
    (hJ : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J))) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  have hαI : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hA).2
      DerivedCategory.Qh RF α I hI
  have hs : IsIso ((DerivedCategory.Qh ⋙ RF).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)) := by
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)) :=
      (DerivedCategory.isIso_Qh_map_iff _).2
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).2
          ((HomologicalComplex.mem_quasiIso_iff s).2 inferInstance))
    exact (inferInstance : IsIso (RF.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s))))
  have hcomp : IsIso ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s) ≫
        α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
    rw [α.naturality]
    infer_instance
  have hmap : IsIso ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)) :=
    IsIso.of_isIso_comp_right _ (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s))) at hmap
  rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff] at hmap
  exact (HomologicalComplex.mem_quasiIso_iff _).1 hmap

/-- For a quasi-isomorphism `s : J ⟶ I` into a K-injective complex, the unit of a right derived
functor along `DerivedCategory.Q` is invertible at `J` iff `F` maps `s` to a quasi-isomorphism. -/
private theorem isIso_rightDerivedUnit_app_iff_quasiIso_map (F : A ⥤ B) [F.Additive]
    [IsGrothendieckAbelian.{w} A]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    {J I : CochainComplex A ℤ} (s : J ⟶ I) [QuasiIso s] (hI : I.IsKInjective) :
    IsIso (α.app J) ↔ QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  have hαI : IsIso (α.app I) :=
    Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective.{w} DerivedCategory.Q RF α
      (Stacks.Injectives.KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q F)
      I hI
  have hRs : IsIso ((DerivedCategory.Q ⋙ RF).map s) := by
    have : IsIso (DerivedCategory.Q.map s) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 inferInstance
    exact (inferInstance : IsIso (RF.map (DerivedCategory.Q.map s)))
  refine Iff.trans ?_ (DerivedCategory.isIso_Q_map_iff_quasiIso _ _)
  constructor
  · intro hJ
    have : IsIso (α.app J ≫ (DerivedCategory.Q ⋙ RF).map s) := inferInstance
    rw [← α.naturality s] at this
    exact IsIso.of_isIso_comp_right
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).map s) (α.app I)
  · intro hFs
    have : IsIso ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).map s ≫
        α.app I) := by
      have : IsIso ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).map s) := hFs
      infer_instance
    rw [α.naturality s] at this
    exact IsIso.of_isIso_comp_right (α.app J) ((DerivedCategory.Q ⋙ RF).map s)

/-- The unit of a right derived functor of `F` along `DerivedCategory.Q` is invertible at a
complex `J` as soon as `F` carries some quasi-isomorphism `s : J ⟶ I` into a K-injective complex
to a quasi-isomorphism. -/
theorem isIso_rightDerivedUnit_app_of_quasiIso_map (F : A ⥤ B) [F.Additive]
    [IsGrothendieckAbelian.{w} A]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    {J I : CochainComplex A ℤ} (s : J ⟶ I) [QuasiIso s] (hI : I.IsKInjective)
    (hs : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    IsIso (α.app J) :=
  (isIso_rightDerivedUnit_app_iff_quasiIso_map.{w} F RF α s hI).2 hs

/-- If the unit of a right derived functor of `F` along `DerivedCategory.Q` is invertible at a
complex `J`, then `F` carries any quasi-isomorphism `s : J ⟶ I` into a K-injective complex to a
quasi-isomorphism. This is the converse of `isIso_rightDerivedUnit_app_of_quasiIso_map`. -/
theorem quasiIso_map_of_isIso_rightDerivedUnit_app_Q (F : A ⥤ B) [F.Additive]
    [IsGrothendieckAbelian.{w} A]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    {J I : CochainComplex A ℤ} (s : J ⟶ I) [QuasiIso s] (hI : I.IsKInjective)
    (hJ : IsIso (α.app J)) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
  (isIso_rightDerivedUnit_app_iff_quasiIso_map.{w} F RF α s hI).1 hJ

/-- **A complex of right acyclic objects computes a right derived functor of finite
cohomological dimension** (Stacks 07K7, part (2), along `DerivedCategory.Q`). Let `F : 𝒜 ⥤ ℬ` be
a left exact additive functor out of a Grothendieck abelian category with `R^n F = 0` for some
`n`, and let `(RF, α)` be a right derived functor of `F` on unbounded complexes. Then `α` is
invertible at every cochain complex all of whose terms are right acyclic for `F`, i.e. have
vanishing higher right derived functors `R^p F` for `p > 0`. -/
@[sga "4 V 0.4" "special case",
  sga "4 XVII 1.2.10" "Right-derived case",
  sga "4½ Etat_0 4.2.3.2" "partial"]
theorem isIso_app_of_rightAcyclic_of_isZero_rightDerived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [IsGrothendieckAbelian.{w} A]
    (n : ℕ) (hvanish : ∀ X : A, IsZero ((F.rightDerived n).obj X))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (J : CochainComplex A ℤ)
    (hJ : ∀ (i : ℤ) (p : ℕ), 0 < p → IsZero ((F.rightDerived p).obj (J.X i))) :
    IsIso (α.app J) := by
  have : EnoughInjectives A := inferInstance
  have : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) :=
    Stacks.Cohomology.CompactExtensionByZero.hasRightDerivedFunctorPlus F
  have hJ' : ∀ i : ℤ, F.rightAcyclic (J.X i) := fun i =>
    (CategoryTheory.rightAcyclic_iff_isZero_rightDerived F (J.X i)).2 (hJ i)
  have hmono (X : A) : ∃ (Y : A) (i : X ⟶ Y) (_ : Mono i), F.rightAcyclic Y := by
    classical
    refine ⟨Injective.under X, Injective.ι X, inferInstance, ?_⟩
    change IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj (Injective.under X)))
    let (i : ℤ) : Injective
        (((HomotopyCategory.Plus.singleFunctor A 0).obj (Injective.under X)).obj.as.X i) :=
      inferInstanceAs (Injective
        (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (Injective.under X)).X i))
    infer_instance
  have hn (X : A) : IsZero ((DerivedCategory.Plus.homologyFunctor B n).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))) := by
    change IsZero ((F.rightDerivedPlus (n : ℤ)).obj X)
    exact (hvanish X).of_iso (CategoryTheory.rightDerivedPlusObjIso F X n)
  have h := Functor.hasRightDerivedFunctor_of_isZero_rightDerived
    F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit F.rightAcyclic
    (Stacks.Cohomology.CompactExtensionByZero.rightAcyclic_iff_computesRightDerived F) hmono n hn
  have hex := h.1
  have hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f := fun K =>
    Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A K
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let Wh := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have hJh : IsIso ((Fh.totalRightDerivedUnit DerivedCategory.Qh Wh).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)) :=
    ((h.2.2 (Fh.totalRightDerived DerivedCategory.Qh Wh)
      (Fh.totalRightDerivedUnit DerivedCategory.Qh Wh)).1 J hJ')
  obtain ⟨I, s, hI, hs⟩ := hA J
  exact isIso_rightDerivedUnit_app_of_quasiIso_map.{w} F RF α s hI
    (quasiIso_map_of_isIso_rightDerivedUnit_app F hA (Fh.totalRightDerived DerivedCategory.Qh Wh)
      (Fh.totalRightDerivedUnit DerivedCategory.Qh Wh) s hI hJh)

end CategoryTheory.Functor

end
