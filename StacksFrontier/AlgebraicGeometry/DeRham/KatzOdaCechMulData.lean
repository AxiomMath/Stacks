module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechFiltration
public import StacksFrontier.RingTheory.Kaehler.KatzOdaCechMul
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroChart

/-!
# The wedge product of forms on the Čech intersections

Let `f : X ⟶ Y` be a smooth morphism and `g : Y ⟶ S` with `Y` and `S` affine, and let `U` be a
family of opens of `X` with affine Čech intersections. This file adds to the identification
`AlgebraicGeometry.DeRhamKatzOdaCech.formsDataTotal` of the forms of `X/S` on the intersections
with Kähler forms the wedge product of sections, which the identification carries to the wedge
product of Kähler forms ([Stacks, Tag 0FUM], the multiplication of the complex `K` of its proof).

## Main definitions

* `AlgebraicGeometry.DeRhamKatzOdaCech.sectionsMul`: the wedge product `Ω^a × Ω^b ⟶ Ω^{a+b}` of
  relative differential forms over an open.
* `AlgebraicGeometry.DeRhamKatzOdaCech.formsMulDataTotal`: `formsDataTotal` with the wedge product.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex Stacks.AlgebraicGeometry.SectionsBaseChange

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

/-! ### The wedge product of forms on sections -/

section Forms

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **The wedge product of relative differential forms over an open**, in degree `a + b`. -/
def sectionsMul (a b : ℕ) (V : X.Opens)
    (x : Γ(Scheme.Hom.relativeDifferentialForms p (a : ℤ), V))
    (y : Γ(Scheme.Hom.relativeDifferentialForms p (b : ℤ), V)) :
    Γ(Scheme.Hom.relativeDifferentialForms p ((a + b : ℕ) : ℤ), V) :=
  (eqToHom (congrArg (Stacks.AffineExteriorPower.pieceModules
      (Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials p)))
      (Nat.cast_add a b).symm)).val.app (op V)
    (((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials p)).mul (a : ℤ) b).app
      (op V) x y)

/-- Transport of sections along an equality of modules commutes with restriction. -/
theorem eqToHom_val_app_map {M N : X.Modules} (h : M = N) {V V' : X.Opens} (i : V' ⟶ V)
    (x : Γ(M, V)) :
    (eqToHom h).val.app (op V') (M.presheaf.map i.op x) =
      N.presheaf.map i.op ((eqToHom h).val.app (op V) x) := by
  subst h
  rfl

/-- **The wedge product of forms commutes with restriction.** -/
theorem sectionsMul_restrict (a b : ℕ) {V V' : X.Opens} (i : V' ⟶ V)
    (x : Γ(Scheme.Hom.relativeDifferentialForms p (a : ℤ), V))
    (y : Γ(Scheme.Hom.relativeDifferentialForms p (b : ℤ), V)) :
    (Scheme.Hom.relativeDifferentialForms p ((a + b : ℕ) : ℤ)).presheaf.map i.op
        (sectionsMul p a b V x y) =
      sectionsMul p a b V'
        ((Scheme.Hom.relativeDifferentialForms p (a : ℤ)).presheaf.map i.op x)
        ((Scheme.Hom.relativeDifferentialForms p (b : ℤ)).presheaf.map i.op y) :=
  (eqToHom_val_app_map _ i _).symm.trans (congrArg _ (((Scheme.Modules.exteriorAlgebra
    (Scheme.Hom.relativeDifferentials p)).mul (a : ℤ) b).naturality i.op x y))

end Forms

/-! ### The product with a form from the base, on the Čech intersections -/

section Affine

variable {X T : Scheme.{u}} [IsAffine T] (q : X ⟶ T)

/-- **Over an affine open, the identification with Kähler forms is multiplicative.** -/
theorem formsEquiv_sectionsEquiv_mul {V : X.Opens} (hV : IsAffineOpen V) (a b : ℕ)
    (y : (q.sectionsDeRhamComplex.X a).obj (op V)) (y' : (q.sectionsDeRhamComplex.X b).obj (op V)) :
    formsEquiv q hV (a + b) (sectionsEquiv q (a + b) V ((sectionsEquiv q (a + b) V).symm
        (sectionsMul q a b V (sectionsEquiv q a V y) (sectionsEquiv q b V y')))) =
      exteriorPower.wedgeMul a b (formsEquiv q hV a (sectionsEquiv q a V y))
        (formsEquiv q hV b (sectionsEquiv q b V y')) := by
  rw [LinearEquiv.apply_symm_apply]
  have hs : sectionsMul q a b V (sectionsEquiv q a V y) (sectionsEquiv q b V y') =
      (eqToHom (congrArg (Stacks.AffineExteriorPower.pieceModules
        (Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials q)))
        (Nat.cast_add a b).symm)).val.app (op V)
      (((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials q)).mul
        (a : ℤ) b).app (op V) (sectionsEquiv q a V y) (sectionsEquiv q b V y')) := rfl
  rw [hs]
  exact Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_mul q hV
    (isAffineOpen_top T) (le_preimage_top q V) a b _ _

end Affine

section Intersections

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S] [Smooth f]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t))

/-- **The forms of `X/S` on the Čech intersections, with their wedge product**: the data
`formsDataTotal` together with the wedge product of sections. -/
def formsMulDataTotal :
    Stacks.KatzOda.Cech.FormsMulData (U := U) (chartData f g U haff)
      (P := (f ≫ g).sectionsDeRhamComplex) where
  L a _ t := Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ), inter U t)
  instAddCommGroup _ _ _ := inferInstance
  instModule a _ t := baseModule (f ≫ g) (Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ))
    (inter U t)
  s a _ t := sectionsEquiv (f ≫ g) a (inter U t)
  e' a m t := formsEquiv (f ≫ g) (@haff m t) a
  e'_smul a m t r y := formsEquiv_smul (f ≫ g) (@haff m t) a r y
  e'_cres a m t j y := formsEquiv_sectionsEquiv_cres U haff (f ≫ g) a m t j y
  e'_d a m t y := formsEquiv_sectionsEquiv_d (f ≫ g) (@haff m t) a y
  mul a b _ t y y' := (sectionsEquiv (f ≫ g) (a + b) (inter U t)).symm
    (sectionsMul (f ≫ g) a b (inter U t) (sectionsEquiv (f ≫ g) a (inter U t) y)
      (sectionsEquiv (f ≫ g) b (inter U t) y'))
  e'_mul a b m t y y' := formsEquiv_sectionsEquiv_mul (f ≫ g) (@haff m t) a b y y'

/-- Forgetting the wedge product of `formsMulDataTotal` recovers `formsDataTotal`. -/
theorem formsMulDataTotal_toFormsData :
    (formsMulDataTotal f g U haff).toFormsData = formsDataTotal f g U haff :=
  rfl

end Intersections

end AlgebraicGeometry.DeRhamKatzOdaCech

end
