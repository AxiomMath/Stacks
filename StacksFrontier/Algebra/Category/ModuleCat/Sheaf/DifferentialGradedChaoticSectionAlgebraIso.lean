module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRealization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseRingRestriction
public import StacksFrontier.Algebra.DifferentialGraded.AlgebraCategory

/-!
# The section algebras of an inverse system of differential graded algebras

Let `A : Cᵒᵖ ⥤ DGA(Λ)` be an inverse system of differential graded `Λ`-algebras and let
`𝒜 = Stacks.ChaoticSite.systemAlgebra A` be the sheaf of differential graded algebras on the
chaotic site `C` it defines. Over an object `U` the differential graded algebra of sections
`𝒜(U)` of the ambient library is formed over the lifted integers, as the external direct sum of
the sections of the homogeneous pieces; for `𝒜` those pieces are the homogeneous pieces of
`A(U)`. This file identifies `𝒜(U)` with `A(U)` regarded over the lifted integers, compatibly
with restriction.

## Main definitions

* `Stacks.ChaoticSite.sectionRingEquiv`: the ring isomorphism from the sections `𝒜(U)` to `A(U)`,
  summing the homogeneous components.
* `Stacks.ChaoticSite.sectionAlgebraIso`: the isomorphism of differential graded algebras over
  the lifted integers `𝒜(U) ≅ A(U)`.

## Main results

* `Stacks.ChaoticSite.sectionAlgebraIso_hom_naturality`: the isomorphism commutes with
  restriction along a morphism of `Cᵒᵖ`.

## References

* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
* [Stacks Project, Section 24.35 (Tag 0GZG)](https://stacks.math.columbia.edu/tag/0GZG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u u₁ v₁

attribute [local instance] SheafOfModules.GradedAlgebra.sectionsGOne
  SheafOfModules.GradedAlgebra.sectionsGMul SheafOfModules.GradedAlgebra.sectionsGRing

namespace Stacks.ChaoticSite

variable {C : Type u₁} [Category.{v₁} C] {Λ : Type u} [CommRing Λ]
  (A : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ) (U : Cᵒᵖ)

/-- The sections over `U` of the degree-`n` piece of `systemAlgebra A` are the degree-`n` piece of
`A(U)`. -/
theorem sectionsPiece_eq (n : ℤ) :
    (systemAlgebra A).toGradedAlgebra.sectionsPiece U n = ↥((A.obj U).grading n) :=
  rfl

/-- A homogeneous element of `A(U)`, read as a section of the corresponding piece of
`systemAlgebra A`. -/
def pieceMk (n : ℤ) (a : (A.obj U).A) (ha : a ∈ (A.obj U).grading n) :
    (systemAlgebra A).toGradedAlgebra.sectionsPiece U n :=
  (⟨a, ha⟩ : ↥((A.obj U).grading n))

/-- Summing the homogeneous components: the ring homomorphism from the sections of
`systemAlgebra A` over `U` to `A(U)`. -/
def sectionRingHom : (systemAlgebra A).toGradedAlgebra.totalSections U →+* (A.obj U).A :=
  DirectSum.toSemiring (fun n => ((A.obj U).grading n).subtype.toAddMonoidHom) rfl
    (fun _ _ => rfl)

/-- On the summand of degree `n`, `sectionRingHom A U` is the inclusion of the degree-`n` piece of
`A(U)`. -/
@[simp]
theorem sectionRingHom_of (n : ℤ) (x : (systemAlgebra A).toGradedAlgebra.sectionsPiece U n) :
    sectionRingHom A U (DirectSum.of _ n x) = (show ↥((A.obj U).grading n) from x).val :=
  DirectSum.toSemiring_of _ _ _ n x

/-- The ring isomorphism from the sections of `systemAlgebra A` over `U` to `A(U)`: its inverse is
the decomposition of `A(U)` into homogeneous components. -/
def sectionRingEquiv : (systemAlgebra A).toGradedAlgebra.totalSections U ≃+* (A.obj U).A where
  toFun := sectionRingHom A U
  invFun := DirectSum.decompose (A.obj U).grading
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
      rw [map_zero, DirectSum.decompose_zero]
      rfl
    | of n x =>
      rw [sectionRingHom_of]
      exact DirectSum.decompose_coe (A.obj U).grading x
    | add x y hx hy =>
      refine (congrArg _ (map_add (sectionRingHom A U) x y)).trans ?_
      rw [DirectSum.decompose_add, hx, hy]
      rfl
  right_inv a := by
    induction a using DirectSum.Decomposition.inductionOn (A.obj U).grading with
    | zero =>
      rw [DirectSum.decompose_zero]
      exact map_zero (sectionRingHom A U)
    | homogeneous a =>
      rw [DirectSum.decompose_coe]
      exact sectionRingHom_of A U _ a
    | add a b ha hb =>
      rw [DirectSum.decompose_add]
      exact (map_add (sectionRingHom A U) _ _).trans (by rw [ha, hb])
  map_mul' := map_mul _
  map_add' := map_add _

variable [Algebra (ULift.{u} ℤ) Λ]

omit [Algebra (ULift.{u} ℤ) Λ] in
/-- Any algebra structure over the lifted integers is the integer cast. -/
theorem algebraMap_uliftInt {T : Type u} [Ring T] [Algebra (ULift.{u} ℤ) T] (c : ULift.{u} ℤ) :
    algebraMap (ULift.{u} ℤ) T c = ((c.down : ℤ) : T) := by
  rw [← map_intCast (algebraMap (ULift.{u} ℤ) T) c.down]
  rfl

/-- The sections of `systemAlgebra A` over `U`, mapped to `A(U)`, as a homomorphism of
differential graded algebras over the lifted integers. -/
def sectionAlgebraHom :
    ((systemAlgebra A).sectionAlgebra U).Hom ((A.obj U).restrictBase (ULift.{u} ℤ)) where
  toAlgebraHom :=
    { toRingHom := (sectionRingEquiv A U).toRingHom
      commutes' := fun c => by
        change sectionRingHom A U ((c.down : ℤ) : (systemAlgebra A).toGradedAlgebra.totalSections U)
          = algebraMap Λ (A.obj U).A (algebraMap (ULift.{u} ℤ) Λ c)
        rw [algebraMap_uliftInt (T := Λ) c, map_intCast, map_intCast] }
  map_grading := by
    rintro n x ⟨p, rfl⟩
    change sectionRingHom A U (DirectSum.of _ n p) ∈ (A.obj U).grading n
    rw [sectionRingHom_of]
    exact (show ↥((A.obj U).grading n) from p).2
  map_d x := by
    change sectionRingHom A U ((systemAlgebra A).sectionD U x) = (A.obj U).d (sectionRingHom A U x)
    induction x using DirectSum.induction_on with
    | zero =>
      rw [map_zero, map_zero, map_zero]
    | of n p =>
      rw [SheafOfModules.DifferentialGradedAlgebra.sectionD_of, sectionRingHom_of,
        sectionRingHom_of]
      change (((systemComplex A).d n (n + 1)).val.app U p).val = _
      rw [systemComplex_d_val_app]
      rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The underlying algebra homomorphism of `sectionAlgebraHom A U` is `sectionRingHom A U`. -/
@[simp]
theorem sectionAlgebraHom_apply (x : (systemAlgebra A).toGradedAlgebra.totalSections U) :
    (sectionAlgebraHom A U).toAlgebraHom x = sectionRingHom A U x :=
  rfl

/-- `A(U)`, mapped to the sections of `systemAlgebra A` over `U` by decomposition into homogeneous
components, as a homomorphism of differential graded algebras over the lifted integers. -/
def sectionAlgebraInv :
    ((A.obj U).restrictBase (ULift.{u} ℤ)).Hom ((systemAlgebra A).sectionAlgebra U) where
  toAlgebraHom :=
    { toRingHom := (sectionRingEquiv A U).symm.toRingHom
      commutes' := fun c => by
        change (sectionRingEquiv A U).symm (algebraMap Λ (A.obj U).A (algebraMap (ULift.{u} ℤ) Λ c))
          = ((c.down : ℤ) : (systemAlgebra A).toGradedAlgebra.totalSections U)
        rw [algebraMap_uliftInt (T := Λ) c, map_intCast, map_intCast] }
  map_grading n a ha :=
    ⟨pieceMk A U n a ha, (sectionRingEquiv A U).injective <|
      (sectionRingHom_of A U n (pieceMk A U n a ha)).trans
        ((sectionRingEquiv A U).apply_symm_apply a).symm⟩
  map_d a := by
    change (sectionRingEquiv A U).symm ((A.obj U).d a) =
      (systemAlgebra A).sectionD U ((sectionRingEquiv A U).symm a)
    apply (sectionRingEquiv A U).injective
    rw [RingEquiv.apply_symm_apply]
    have h0 := (sectionAlgebraHom A U).map_d ((sectionRingEquiv A U).symm a)
    change sectionRingHom A U ((systemAlgebra A).sectionD U ((sectionRingEquiv A U).symm a)) =
      (A.obj U).d (sectionRingEquiv A U ((sectionRingEquiv A U).symm a)) at h0
    rw [RingEquiv.apply_symm_apply] at h0
    exact h0.symm

/-- **The sections of `systemAlgebra A` over `U` are `A(U)`**, as differential graded algebras
over the lifted integers. -/
def sectionAlgebraIso :
    (systemAlgebra A).sectionAlgebra U ≅ (A.obj U).restrictBase (ULift.{u} ℤ) where
  hom := sectionAlgebraHom A U
  inv := sectionAlgebraInv A U
  hom_inv_id := DifferentialGradedAlgebra.hom_eq_of_toAlgebraHom_eq
    (AlgHom.ext fun x => (sectionRingEquiv A U).symm_apply_apply x)
  inv_hom_id := DifferentialGradedAlgebra.hom_eq_of_toAlgebraHom_eq
    (AlgHom.ext fun a => (sectionRingEquiv A U).apply_symm_apply a)

/-- The forward map of `sectionAlgebraIso A U` is `sectionAlgebraHom A U`. -/
@[simp]
theorem sectionAlgebraIso_hom : (sectionAlgebraIso A U).hom = sectionAlgebraHom A U := rfl

/-- The inverse map of `sectionAlgebraIso A U` is `sectionAlgebraInv A U`. -/
@[simp]
theorem sectionAlgebraIso_inv : (sectionAlgebraIso A U).inv = sectionAlgebraInv A U := rfl

/-- **The identification of the section algebras commutes with restriction**: restricting
sections along `a : V ⟶ U` and then summing is summing and then applying `A(a)`. -/
theorem sectionAlgebraIso_hom_naturality {V : Cᵒᵖ} (a : V ⟶ U) :
    (systemAlgebra A).sectionRestriction a ≫ (sectionAlgebraIso A U).hom =
      (sectionAlgebraIso A V).hom ≫ (A.map a).restrictBase (ULift.{u} ℤ) :=
  DifferentialGradedAlgebra.hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun x => by
    show sectionRingHom A U ((systemAlgebra A).sectionRestrictRing a x) =
      (A.map a).toAlgebraHom (sectionRingHom A V x)
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | of n p =>
      rw [SheafOfModules.DifferentialGradedAlgebra.sectionRestrictRing_of, sectionRingHom_of,
        sectionRingHom_of]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add])

end Stacks.ChaoticSite
