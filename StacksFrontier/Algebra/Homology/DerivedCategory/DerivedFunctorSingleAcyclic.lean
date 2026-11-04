module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived

/-!
# A right derived functor at an acyclic object placed in degree zero

Let `w : A ⥤ B` be a left exact functor of abelian categories, `A` with enough injectives, and
let `Rw : D(A) ⥤ D(B)` be a right derived functor of `w` on the unbounded derived categories,
with unit `α`. The unit of `Rw` read at the complexes `X[0]` is a natural transformation

`w(X)[0] ⟶ Rw(X[0])`,

and it is an isomorphism at every object `X` with `Rⁿw(X) = 0` for `n > 0`: both sides then have
cohomology only in degree `0`, where the comparison is `w ≅ R⁰w`.

## Main definitions

* `Stacks.DerivedFunctor.singleUnit`: the transformation `w(-)[0] ⟶ Rw(-[0])`.

## Main results

* `Stacks.DerivedFunctor.isIso_singleUnit_app`: it is invertible at a `w`-acyclic object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (w : A ⥤ B) [w.Additive] (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ Rw)

/-- **The unit of a right derived functor at the objects placed in degree zero**, as a natural
transformation `w(-)[0] ⟶ Rw(-[0])`. -/
def singleUnit :
    w ⋙ DerivedCategory.singleFunctor B 0 ⟶ DerivedCategory.singleFunctor A 0 ⋙ Rw :=
  (mapSingleQhIso w 0).inv ≫ Functor.whiskerLeft (HomotopyCategory.singleFunctor A 0) α ≫
    (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQh A 0) Rw).inv

/-- In degree zero, the unit at an object placed in degree zero is the comparison `w ⟶ R⁰w`,
up to the identifications of its source and target. -/
lemma homologyFunctor_map_singleUnit_app (X : A) :
    (homologyFunctor B 0).map ((singleUnit w Rw α).app X) =
      (homologyFunctor B 0).map ((mapSingleQhIso w 0).inv.app X) ≫
        (singleUnitHomology w Rw α 0).app X ≫
          (homologyFunctor B 0).map
            ((Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQh A 0) Rw).inv.app
              X) := by
  simp only [singleUnit, NatTrans.comp_app, Functor.map_comp, singleUnitHomology_app]
  rfl

variable [Rw.CommShift ℤ] [Rw.IsTriangulated]
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [EnoughInjectives A] [PreservesFiniteLimits w]

/-- **The unit of a right derived functor is invertible at a `w`-acyclic object placed in degree
zero.** The source `w(X)[0]` has cohomology only in degree `0`; so does the target, below
degree `0` because `Rw` keeps `X[0]` in `D^{≥ 0}` (`hGE`) and above because
`Hⁿ(Rw(X[0])) = Rⁿw(X)` vanishes there; and in degree `0` the comparison is `w ≅ R⁰w`. -/
theorem isIso_singleUnit_app
    (hGE : ∀ X : A, (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0)
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : A) (hX : ∀ n : ℕ, 0 < n → IsZero ((w.rightDerived n).obj X)) :
    IsIso ((singleUnit w Rw α).app X) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have h₁ : IsZero ((homologyFunctor B n).obj
        ((DerivedCategory.singleFunctor B 0).obj (w.obj X))) :=
      DerivedCategory.isZero_of_isGE _ 0 n hn
    have := hGE X
    have h₂ : IsZero ((homologyFunctor B n).obj
        (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X))) :=
      DerivedCategory.isZero_of_isGE _ 0 n hn
    exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
  · have := isIso_singleUnitHomology_app w Rw α hGE
      (fun J hJ => isIso_unit_app_single_of_injective w Rw α hres J hJ) X
    rw [homologyFunctor_map_singleUnit_app]
    infer_instance
  · have h₁ : IsZero ((homologyFunctor B n).obj
        ((DerivedCategory.singleFunctor B 0).obj (w.obj X))) :=
      DerivedCategory.isZero_of_isLE _ 0 n hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
    have h₂ : IsZero ((homologyFunctor B (m : ℤ)).obj
        (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X))) :=
      (hX m (by exact_mod_cast hn)).of_iso
        ((singleCompDerivedCompHomologyIsoRightDerived w Rw α hres m).app X)
    exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

end Stacks.DerivedFunctor

end
