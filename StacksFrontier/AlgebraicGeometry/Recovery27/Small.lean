module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Recovery27.Presentation

/-!
# Smallness of the isomorphism classes of quotient presentations

On a scheme, the finite locally free modules of a fixed rank form an essentially small
class, and therefore the isomorphism classes of quotient presentations of the free module
of rank `n` form a small type.

## Main results

* `AlgebraicGeometry.Grassmannian.small_points`: the isomorphism classes of quotient
  presentations form a small type.

## References

* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Grassmannian

open Limits TopologicalSpace

/-- A module that is finite locally free of some rank is of finite type. -/
private theorem finiteType_of_finiteLocallyFreeOfRank {X : Scheme.{u}}
    (M : X.Modules) (r : ℕ)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) M r) :
    @SheafOfModules.IsFiniteType (Opens X.toPresheafedSpace) _
      (Opens.grothendieckTopology X.toPresheafedSpace) X.ringCatSheaf _ _ M := by
  have hlf := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  obtain ⟨q, _, hq⟩ := hlf.exists_isFiniteLocallyFreeData
  exact @SheafOfModules.IsFiniteType.mk.{u, u, u}
    (Opens X.toPresheafedSpace) _ (Opens.grothendieckTopology X.toPresheafedSpace)
    X.ringCatSheaf _ _ M ⟨q, hq⟩

/-- The modules on a scheme that are finite locally free of a fixed rank form an
essentially small class. -/
private theorem essentiallySmall_isFiniteLocallyFreeOfRank (X : Scheme.{u}) (r : ℕ) :
    ObjectProperty.EssentiallySmall.{u}
      (fun M : X.Modules ↦
        SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M r) := by
  have hfinite : ObjectProperty.EssentiallySmall.{u}
      (fun M : X.Modules ↦ @SheafOfModules.IsFiniteType
        (Opens X.toPresheafedSpace) _
        (Opens.grothendieckTopology X.toPresheafedSpace) X.ringCatSheaf _ _ M) := by
    change ObjectProperty.EssentiallySmall.{u}
      (fun M : SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology
          X.toLocallyRingedSpace.toRingedSpace)
          (forget₂ CommRingCat RingCat)).obj
            X.toLocallyRingedSpace.toRingedSpace.sheaf) ↦ M.IsFiniteType)
    exact Stacks.SheafOfModules.essentiallySmall_isFiniteType
      X.toLocallyRingedSpace.toRingedSpace
  exact ObjectProperty.EssentiallySmall.of_le
    (fun M hM ↦ finiteType_of_finiteLocallyFreeOfRank M r hM)

/-- Every isomorphism class of quotient presentations is represented by one whose target
lies in a prescribed subclass of the finite locally free modules of the right rank. -/
private theorem surjective_mk_structuredArrow (X : Scheme.{u}) (k n : ℕ)
    (R : ObjectProperty X.Modules)
    (hRP : R ≤ fun M ↦
      SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M (n - k))
    (hPR : (fun M : X.Modules ↦
        SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M (n - k)) ≤
      R.isoClosure) :
    Function.Surjective (fun a : {a : StructuredArrow
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) R.ι // Epi a.hom} ↦
      (⟦{ target := R.ι.obj a.1.right
          map := a.1.hom
          map_epi := a.2
          finiteLocallyFree := hRP _ a.1.right.property }⟧ : Points X k n)) := by
  intro x
  obtain ⟨q, rfl⟩ := Quotient.exists_rep x
  obtain ⟨Y, hY, ⟨e⟩⟩ := hPR q.target q.finiteLocallyFree
  let Y' : R.FullSubcategory := ⟨Y, hY⟩
  have hYeq : Y = R.ι.obj Y' := rfl
  let e' : q.target ≅ R.ι.obj Y' := e ≪≫ eqToIso hYeq
  have he : Epi e'.hom := by
    refine ⟨?_⟩
    intro Z a b hab
    have h' := congrArg (fun f ↦ e'.inv ≫ f) hab
    simpa [Category.assoc] using h'
  refine ⟨⟨StructuredArrow.mk
    (S := SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)))
    (T := R.ι) (Y := Y') (q.map ≫ e'.hom), epi_comp' q.map_epi he⟩, ?_⟩
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨e'.symm, ?_⟩
  calc
    (q.map ≫ e'.hom) ≫ e'.inv = q.map ≫ (e'.hom ≫ e'.inv) := by cat_disch
    _ = q.map ≫ 𝟙 q.target := congrArg (fun h ↦ q.map ≫ h) e'.hom_inv_id
    _ = q.map := Category.comp_id _

/-- The isomorphism classes of finite locally free rank-`n - k` quotients of the free
module of rank `n` form a small type. -/
public theorem small_points (X : Scheme.{u}) (k n : ℕ) :
    Small.{u} (Points X k n) := by
  have := essentiallySmall_isFiniteLocallyFreeOfRank X (n - k)
  obtain ⟨R, _, hRP, hPR⟩ := ObjectProperty.EssentiallySmall.exists_small_le
    (fun M : X.Modules ↦
      SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M (n - k))
  have : Small.{u} (StructuredArrow
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) R.ι) :=
    small_of_surjective (f := fun (f : Σ (Y : R.FullSubcategory),
        SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ R.ι.obj Y) ↦
        StructuredArrow.mk f.2)
      (fun f ↦ by
        obtain ⟨Y, f, rfl⟩ := f.mk_surjective
        exact ⟨⟨Y, f⟩, rfl⟩)
  exact small_of_surjective (surjective_mk_structuredArrow X k n R hRP hPR)

end AlgebraicGeometry.Grassmannian

end
