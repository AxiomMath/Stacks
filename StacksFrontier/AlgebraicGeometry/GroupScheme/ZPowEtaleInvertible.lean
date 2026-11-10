module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowUnramifiedAtPoint
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowSurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.IsoInvariance
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange

/-!
# Multiplication by an invertible integer on an abelian variety is étale

Let `A` be an abelian variety over an algebraically closed field `k` and let `n` be a natural
number invertible in `k`. Then multiplication by `n` on `A` is étale, in particular flat.

## Main results

* `Stacks.Groupoids.etale_natCast_zpow_id_left_of_isUnit`: multiplication by `n` on an abelian
  variety over an algebraically closed field is étale when `n` is invertible in the field.
* `Stacks.Groupoids.flat_zpow_id_left_of_isUnit`: the same morphism is flat.

## Implementation notes

The source ([Stacks, Tag 0BFH]) derives this from [Stacks, Tag 0BFG], that `[n]` is finite
locally free, whose proof needs an ample invertible module with `[n]^* N ≅ N ^{⊗ n²}` and so the
theorem of the cube. None of that is used here. Instead:

* `[n]` is unramified at every point by
  `AlgebraicGeometry.unramifiedAt_zpow_id_left_of_isUnit`, the tangent-space computation of
  [Stacks, Tag 0BF5] carried out on dual-number points;
* at the unit `e`, which `[n]` fixes, the stalk map `𝒪_{A,e} ⟶ 𝒪_{A,e}` is a local homomorphism
  of the same regular local ring (Tag 056S) whose closed fibre is the residue field (being
  unramified), so it is flat by miracle flatness (Tag 00R4); flat and unramified is étale at `e`
  (Tag 02GU);
* translation by a rational point `a` is an automorphism with `t_a ≫ [n] = [n] ≫ t_{a^n}`,
  since `A` is commutative (Tag 0BFD), so `[n]` is étale at every rational point, i.e. at every
  closed point as `k` is algebraically closed;
* the étale locus is open, and a nonempty closed subset of the Jacobson space `A` contains a
  closed point, so the étale locus is everything.

## References

* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 02GU](https://stacks.math.columbia.edu/tag/02GU)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

end AlgebraicGeometry

open AlgebraicGeometry

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Translation by a rational point intertwines multiplication by `n` with translation by the
`n`-th power of the point, on a commutative group object. -/
theorem mulRight_hom_comp_zpow [IsCommMonObj A] (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) (n : ℤ) :
    (GrpObj.mulRight a).hom ≫ ((𝟙 A : A ⟶ A) ^ n) =
      ((𝟙 A : A ⟶ A) ^ n) ≫ (GrpObj.mulRight (a ^ n)).hom := by
  have h1 : (GrpObj.mulRight a).hom = 𝟙 A * (toUnit A ≫ a) := rfl
  have h2 : (GrpObj.mulRight (a ^ n)).hom = 𝟙 A * (toUnit A ≫ a ^ n) := rfl
  rw [h1, h2, GrpObj.comp_zpow, Category.comp_id, MonObj.comp_mul, Category.comp_id,
    ← Category.assoc, toUnit_unique (((𝟙 A : A ⟶ A) ^ n) ≫ toUnit A) (toUnit A), mul_zpow,
    GrpObj.comp_zpow]

/-- The unit of a group object is the identity element of its hom-group. -/
private theorem unit_eq_one : η[A] = (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

/-- Translation by a rational point sends the unit to that point. -/
theorem unit_comp_mulRight_hom (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    η[A] ≫ (GrpObj.mulRight a).hom = a := by
  have h1 : (GrpObj.mulRight a).hom = 𝟙 A * (toUnit A ≫ a) := rfl
  rw [h1, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]
  rw [unit_eq_one, one_mul]

/-- Multiplication by `n` fixes the unit. -/
theorem unit_comp_zpow (n : ℤ) : η[A] ≫ ((𝟙 A : A ⟶ A) ^ n) = η[A] := by
  rw [GrpObj.comp_zpow, Category.comp_id, unit_eq_one, one_zpow]

variable [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]

omit [GrpObj A] [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A] in
/-- `n` invertible in `k` is invertible in every residue field of a scheme over `k`. -/
lemma isUnit_natCast_residueField_of_isUnit_natCast (n : ℕ) (hn : IsUnit (n : k)) (x : A.left) :
    IsUnit ((n : ℕ) : A.left.residueField x) := by
  let φ : CommRingCat.of k ⟶ A.left.residueField x :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫ A.left.presheaf.germ ⊤ x trivial ≫
      A.left.residue x
  simpa using hn.map φ.hom

/-- **Multiplication by an invertible integer on an abelian variety over an algebraically closed
field is étale.** -/
theorem etale_natCast_zpow_id_left_of_isUnit (n : ℕ) (hn : IsUnit (n : k)) :
    Etale ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have : Smooth A.hom := smooth_hom A
  have := locallyOfFinitePresentation_zpow_id_left A (n : ℤ)
  set F := ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left with hFdef
  have hunr : ∀ x, UnramifiedAt F x := fun x =>
    unramifiedAt_zpow_id_left_of_isUnit A n x
      (isUnit_natCast_residueField_of_isUnit_natCast A n hn x)
  -- étale at the unit
  let p : (Spec (.of k) : Scheme) := IsLocalRing.closedPoint k
  let e : A.left := (η[A]).left p
  have hFe : F e = e := by
    change ((η[A]).left ≫ F) p = _
    rw [← Over.comp_left, unit_comp_zpow]
  have hEe : EtaleAt F e := by
    have hu := hunr e
    obtain ⟨hmap, -⟩ := ((unramifiedAt_tfae F e).out 1 7).mp hu
    have h14 := (etaleAt_tfae F e).out 1 4
    refine h14.mpr ⟨?_, ((unramifiedAt_tfae F e).out 1 3).mp hu⟩
    let : Algebra (A.left.presheaf.stalk (F e)) (A.left.presheaf.stalk e) :=
      (F.stalkMap e).hom.toAlgebra
    have : IsRegularLocalRing (A.left.presheaf.stalk (F e)) :=
      isRegularLocalRing_stalk_of_smooth_over_field A.hom (F e)
    have hRe : IsRegularLocalRing (A.left.presheaf.stalk e) :=
      isRegularLocalRing_stalk_of_smooth_over_field A.hom e
    have : IsLocalHom (algebraMap (A.left.presheaf.stalk (F e)) (A.left.presheaf.stalk e)) :=
      inferInstanceAs (IsLocalHom (F.stalkMap e).hom)
    have hCM :=
      (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
        (A.left.presheaf.stalk e)).2
    change Module.Flat _ _
    refine Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add hCM ?_
    have hmap' : (maximalIdeal (A.left.presheaf.stalk (F e))).map
        (algebraMap (A.left.presheaf.stalk (F e)) (A.left.presheaf.stalk e)) =
        maximalIdeal (A.left.presheaf.stalk e) := hmap
    rw [hmap', ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (maximalIdeal.isMaximal _)),
      add_zero]
    exact congrArg (fun y => ringKrullDim (A.left.presheaf.stalk y)) hFe.symm
  -- étale at every closed point
  have hclosed : ∀ x ∈ closedPoints A.left, EtaleAt F x := by
    intro x hx
    let a : 𝟙_ (Over (Spec (.of k))) ⟶ A :=
      Over.homMk (pointOfClosedPoint A.hom x hx) (pointOfClosedPoint_comp A.hom x hx)
    let t := GrpObj.mulRight a
    let t' := GrpObj.mulRight (a ^ (n : ℤ))
    have : IsIso t.hom.left := inferInstanceAs (IsIso ((Over.forget _).map t.hom))
    have : IsIso t'.hom.left := inferInstanceAs (IsIso ((Over.forget _).map t'.hom))
    have hcomm : F ≫ t'.hom.left = t.hom.left ≫ F := by
      rw [← Over.comp_left, ← Over.comp_left, mulRight_hom_comp_zpow]
    have hte : t.hom.left e = x := by
      change ((η[A]).left ≫ t.hom.left) p = x
      rw [← Over.comp_left, unit_comp_mulRight_hom]
      exact pointOfClosedPoint_apply A.hom x hx p
    exact hte ▸ etaleAt_of_isIso_square t.hom.left t'.hom.left hcomm hEe
  -- étale everywhere
  rw [etale_iff_forall_etaleAt]
  by_contra hne
  obtain ⟨y, hy⟩ := not_forall.mp hne
  have hjac : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hC : IsClosed {x | ¬ EtaleAt F x} := (isOpen_setOf_etaleAt F).isClosed_compl
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := {x | ¬ EtaleAt F x}) ⟨y, hy⟩
    hC.isLocallyClosed
  exact hz (hclosed z hzc)

/-- **Multiplication by an invertible integer on an abelian variety over an algebraically closed
field is flat.** This is the hypothesis `hflat` of clauses (3) and (4) of [Stacks, Tag 03RP] as
stated in `Stacks.Groupoids.surjective_zpow_id_left_of_flat` and
`Stacks.Groupoids.exists_zpow_eq_of_flat`, discharged for every `n` invertible in `k`. -/
theorem flat_zpow_id_left_of_isUnit (n : ℕ) (hn : IsUnit (n : k)) :
    Flat ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left :=
  (Etale.iff_flat_and_formallyUnramified.mp (etale_natCast_zpow_id_left_of_isUnit A n hn)).1

end Stacks.Groupoids

end
