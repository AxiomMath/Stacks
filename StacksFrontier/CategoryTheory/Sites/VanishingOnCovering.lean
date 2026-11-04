module

public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Sheaves and complexes of sheaves that vanish on a covering family

Let `(C, J)` be a site. A sheaf is determined by its sections, and a sheaf is *separated*: two
sections over an object that agree after restriction along every arrow of a covering family are
equal. Consequently a sheaf whose sections vanish on every member of one covering family of an
object `X` has vanishing sections on `X` itself, and a sheaf whose sections vanish on a family
of objects that covers *every* object of the site is the zero sheaf.

The same criterion in the derived category: an object `K` of `D(Sheaf J A)` is zero as soon as
each of its homology sheaves has vanishing sections on such a family, since an object of the
unbounded derived category is zero exactly when all of its homology objects are
(`DerivedCategory.isZero_iff_forall_isZero_homology`).

## Main definitions

* `CategoryTheory.GrothendieckTopology.IsCoveringFamily`: a property of objects of a site such
  that every object admits a covering presieve whose sources all have the property.

## Main results

* `CategoryTheory.Sheaf.isZero_sections_of_isZero_sections_of_covering`: sections of a sheaf
  vanish on `X` when they vanish along one covering presieve of `X`.
* `CategoryTheory.Sheaf.isZero_of_forall_isZero_sections`: a sheaf with no sections anywhere is
  the zero sheaf.
* `CategoryTheory.Sheaf.isZero_of_isCoveringFamily`: a sheaf whose sections vanish on a covering
  family of objects is the zero sheaf.
* `CategoryTheory.Sheaf.isZero_derived_of_isCoveringFamily`: an object of the unbounded derived
  category of abelian sheaves whose homology sheaves have vanishing sections on a covering family
  of objects is zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u₂} [Category.{v₂} A]

/-- A property `P` of the objects of a site is a *covering family* when every object of the
site admits a covering presieve all of whose sources satisfy `P`. -/
def GrothendieckTopology.IsCoveringFamily (J : GrothendieckTopology C) (P : ObjectProperty C) :
    Prop :=
  ∀ X : C, ∃ R : Presieve X, Sieve.generate R ∈ J X ∧ ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → P Y

namespace Sheaf

variable [HasZeroMorphisms A]

/-- A sheaf has no sections over `X` as soon as it has no sections over the sources of one
covering presieve of `X`. -/
theorem isZero_sections_of_isZero_sections_of_covering (F : Sheaf J A) {X : C} (R : Presieve X)
    (hR : Sieve.generate R ∈ J X)
    (h : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → IsZero (F.obj.obj (op Y))) :
    IsZero (F.obj.obj (op X)) := by
  rw [IsZero.iff_id_eq_zero]
  have hsep : Presieve.IsSeparatedFor (F.obj ⋙ coyoneda.obj (op (F.obj.obj (op X)))) R :=
    Presieve.isSeparatedFor_iff_generate.2 (F.property _ _ hR).isSeparatedFor
  refine hsep.ext fun {Y} {f} hf => ?_
  simp [Functor.comp_map, (h hf).eq_of_tgt (F.obj.map f.op) 0]

/-- A sheaf with no sections over any object of the site is the zero sheaf. -/
theorem isZero_of_forall_isZero_sections (F : Sheaf J A)
    (h : ∀ X : C, IsZero (F.obj.obj (op X))) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext1
  ext X
  exact (h (unop X)).eq_of_tgt _ _

/-- A sheaf with no sections over the objects of a covering family is the zero sheaf. -/
theorem isZero_of_isCoveringFamily (F : Sheaf J A) {P : ObjectProperty C}
    (hP : J.IsCoveringFamily P) (h : ∀ Y : C, P Y → IsZero (F.obj.obj (op Y))) : IsZero F :=
  isZero_of_forall_isZero_sections F fun X =>
    let ⟨R, hR, hRP⟩ := hP X
    isZero_sections_of_isZero_sections_of_covering F R hR fun {Y} {_} hf => h Y (hRP hf)

end Sheaf

/-- An object of the unbounded derived category of abelian sheaves on a site is zero as soon as
each of its homology sheaves has no sections over the objects of a covering family. -/
theorem Sheaf.isZero_derived_of_isCoveringFamily [Abelian A] [HasFiniteLimits A]
    [HasSheafify J A] [HasDerivedCategory (Sheaf J A)] {P : ObjectProperty C}
    (hP : J.IsCoveringFamily P) (K : DerivedCategory (Sheaf J A))
    (h : ∀ (n : ℤ) (Y : C), P Y →
      IsZero (((DerivedCategory.homologyFunctor (Sheaf J A) n).obj K).obj.obj (op Y))) :
    IsZero K :=
  (DerivedCategory.isZero_iff_forall_isZero_homology K).2 fun n =>
    Sheaf.isZero_of_isCoveringFamily _ hP (h n)

end CategoryTheory

end
