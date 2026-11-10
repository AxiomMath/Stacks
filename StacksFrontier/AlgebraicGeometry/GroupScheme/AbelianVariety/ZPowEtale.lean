module

public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowEtaleOfIsUnit
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowRank0BFG
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Unibranch
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Multiplication by an integer on an abelian variety is étale exactly when it is invertible

Let `A` be an abelian variety over a field `k` and `d` an integer. Multiplication by `d`,
`[d] : A ⟶ A`, is the `d`-th power of the identity in the group `A ⟶ A` of morphisms into the
group object. [Stacks, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH) says that, for `A`
nonzero, `[d]` is étale if and only if `d` is invertible in `k`. This file proves it
unconditionally.

## Main results

* `Stacks.Groupoids.etaleAt_zpow_id_left_unit_of_isUnit`: for `d` invertible in `k`, `[d]` is
  étale at the identity.
* `Stacks.Groupoids.zpow_id_left_genericPoint_of_isUnit`: for `d` invertible in `k`, `[d]` fixes
  the generic point of `A`.
* `Stacks.Groupoids.etale_zpow_id_left_of_isUnit` (in `ZPowEtaleOfIsUnit`): for `d` invertible
  in `k`, `[d]` is étale.
* `Stacks.Groupoids.etale_zpow_id_left_iff_isUnit_intCast`: **Stacks Tag 0BFH.**

## Implementation notes

The source deduces flatness of `[d]` from [Stacks, Tag 0BFG], that `[d]` is finite locally free,
whose proof goes through the theorem of the cube. The argument here does not use Tag 0BFG.
Unramifiedness of `[d]` everywhere, for `d` invertible, is
`Stacks.Groupoids.unramified_zpow_id_left_of_isUnit`: the tangent map at the identity is
multiplication by `d` ([Stacks, Tag 0BF5] and [Stacks, Tag 0B2G]), and translations move every
point to the identity. Flatness is then obtained in three steps.

1. At the identity `e`, the stalk map `𝒪_{A, e} ⟶ 𝒪_{A, e}` of `[d]` is a local homomorphism of
   regular local rings ([Stacks, Tag 056S]) of the same dimension — the two rings are the same
   stalk — and its special fibre is the residue field, because `[d]` is unramified at `e`
   ([Stacks, Tag 02GF]). Miracle flatness ([Stacks, Tag 00R4]) makes it flat, so `[d]` is étale
   at `e` ([Stacks, Tag 02GU]).
2. An étale morphism is open on a neighbourhood of `e`; the image of that neighbourhood is a
   nonempty open subset of the integral scheme `A`, hence contains the generic point, so `[d]`
   maps the generic point to itself.
3. `A` is smooth, hence normal ([Stacks, Tag 033C]), hence geometrically unibranch
   ([Stacks, Tag 0BQ3]); a morphism unramified at a point `x` that is a specialization of a
   point over the generic point is étale at `x` ([Stacks, Tag 0GS8]).

The converse direction is the source's: if `[d]` is étale it is unramified at `e`, so its tangent
map, multiplication by `d`, is injective on the nonzero tangent space at `e`.

## References

* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 0GS8](https://stacks.math.columbia.edu/tag/0GS8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **Multiplication by an invertible integer on an abelian variety is unramified.** -/
theorem unramified_zpow_id_left_of_isUnit_of_isAbelianVariety
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hd : IsUnit (d : k)) : Unramified ((𝟙 A : A ⟶ A) ^ d).left := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  exact unramified_zpow_id_left_of_isUnit k A d hd

/-- **For `d` invertible in `k`, the stalk map of multiplication by `d` at the identity of an
abelian variety is flat.** It is a local homomorphism between regular local rings of the same
dimension whose special fibre is a field, so miracle flatness (Tag 00R4) applies. -/
theorem flat_stalkMap_zpow_id_left_unit [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hd : IsUnit (d : k)) :
    (((𝟙 A : A ⟶ A) ^ d).left.stalkMap ((η[A]).left (IsLocalRing.closedPoint k))).hom.Flat := by
  set f : A.left ⟶ A.left := ((𝟙 A : A ⟶ A) ^ d).left with hfdef
  set e : A.left := (η[A]).left (IsLocalRing.closedPoint k) with hedef
  have hfix : f e = e := zpow_id_left_apply_unit k A (IsLocalRing.closedPoint k) d
  have := smooth_hom A
  have := locallyOfFinitePresentation_zpow_id_left A d
  have hunram : UnramifiedAt f e :=
    (unramified_zpow_id_left_of_isUnit_of_isAbelianVariety A d hd).unramifiedAt e
  have hR : IsRegular A.left := isRegular_of_smooth_over_field A.hom
  have hreg : ∀ x : A.left, IsRegularLocalRing (A.left.presheaf.stalk x) :=
    have h2 : IsLocallyNoetherian A.left ∧
        ∀ x : A.left, IsRegularLocalRing (A.left.presheaf.stalk x) :=
      ((isRegular_tfae A.left).out 1 2).mp hR
    h2.2
  let : IsRegularLocalRing (A.left.presheaf.stalk (f e)) := hreg (f e)
  let : IsRegularLocalRing (A.left.presheaf.stalk e) := hreg e
  let : Algebra (A.left.presheaf.stalk (f e)) (A.left.presheaf.stalk e) :=
    (f.stalkMap e).hom.toAlgebra
  have : IsLocalHom (algebraMap (A.left.presheaf.stalk (f e)) (A.left.presheaf.stalk e)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap e).hom)
  have hmax : (IsLocalRing.maximalIdeal (A.left.presheaf.stalk (f e))).map
      (algebraMap (A.left.presheaf.stalk (f e)) (A.left.presheaf.stalk e)) =
      IsLocalRing.maximalIdeal (A.left.presheaf.stalk e) :=
    have h7 : Ideal.map (f.stalkMap e).hom
          (IsLocalRing.maximalIdeal (A.left.presheaf.stalk (f e))) =
        IsLocalRing.maximalIdeal (A.left.presheaf.stalk e) ∧ _ :=
      ((unramifiedAt_tfae f e).out 1 7).mp hunram
    h7.1
  have hdimeq : ringKrullDim (A.left.presheaf.stalk (f e)) =
      ringKrullDim (A.left.presheaf.stalk e) := by
    rw [hfix]
  change Module.Flat (A.left.presheaf.stalk (f e)) (A.left.presheaf.stalk e)
  apply Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      (A.left.presheaf.stalk e)).2
  have hq : ringKrullDim (A.left.presheaf.stalk e ⧸
      IsLocalRing.maximalIdeal (A.left.presheaf.stalk e)) = 0 :=
    ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient
      (IsLocalRing.maximalIdeal (A.left.presheaf.stalk e))).mp inferInstance)
  rw [hmax, hq, add_zero, hdimeq]

/-- **For `d` invertible in `k`, multiplication by `d` on an abelian variety is étale at the
identity**: its stalk map there is flat (`Stacks.Groupoids.flat_stalkMap_zpow_id_left_unit`) and
it is unramified there (Tag 02GU). -/
theorem etaleAt_zpow_id_left_unit_of_isUnit [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hd : IsUnit (d : k)) :
    EtaleAt ((𝟙 A : A ⟶ A) ^ d).left ((η[A]).left (IsLocalRing.closedPoint k)) := by
  have := locallyOfFinitePresentation_zpow_id_left A d
  have hunram := (unramified_zpow_id_left_of_isUnit_of_isAbelianVariety A d hd).unramifiedAt
    ((η[A]).left (IsLocalRing.closedPoint k))
  have h3 : Subsingleton (Stacks.SmoothAtJacobian.relativeDifferentialStalk
      ((𝟙 A : A ⟶ A) ^ d).left ((η[A]).left (IsLocalRing.closedPoint k))) :=
    ((unramifiedAt_tfae ((𝟙 A : A ⟶ A) ^ d).left
      ((η[A]).left (IsLocalRing.closedPoint k))).out 1 3).mp hunram
  have h4 := ((etaleAt_tfae ((𝟙 A : A ⟶ A) ^ d).left
    ((η[A]).left (IsLocalRing.closedPoint k))).out 1 4).mpr
  exact h4 (And.intro (flat_stalkMap_zpow_id_left_unit A d hd) h3)

/-- **For `d` invertible in `k`, multiplication by `d` on an abelian variety fixes the generic
point.** It is étale, hence open, on a neighbourhood of the identity; the image of that
neighbourhood contains the generic point, and a generization of the generic point is the generic
point. -/
theorem zpow_id_left_genericPoint_of_isUnit [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hd : IsUnit (d : k)) :
    ((𝟙 A : A ⟶ A) ^ d).left (genericPoint A.left) = genericPoint A.left := by
  set f : A.left ⟶ A.left := ((𝟙 A : A ⟶ A) ^ d).left with hfdef
  obtain ⟨U, -, heU, hEt⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt f _
    (etaleAt_zpow_id_left_unit_of_isUnit A d hd)
  have hopen : IsOpen (Set.range (U.ι ≫ f)) := (U.ι ≫ f).isOpenMap.isOpen_range
  have hmem : genericPoint A.left ∈ Set.range (U.ι ≫ f) :=
    ((genericPoint_spec A.left).mem_open_set_iff hopen).mpr
      ⟨_, Set.mem_univ _, Set.mem_range_self ⟨_, heU⟩⟩
  obtain ⟨u, hu⟩ := hmem
  have hsp : f (genericPoint A.left) ⤳ genericPoint A.left := by
    have h1 : genericPoint A.left ⤳ U.ι u := genericPoint_specializes _
    have h2 := h1.map f.continuous
    rwa [← Scheme.Hom.comp_apply, hu] at h2
  have hgen : IsGenericPoint (f (genericPoint A.left)) (⊤ : Set A.left) := by
    have h := specializes_iff_closure_subset.mp hsp
    rw [(genericPoint_spec A.left).def] at h
    exact isGenericPoint_def.mpr (top_le_iff.mp h)
  exact hgen.eq (genericPoint_spec A.left)

/-- **Stacks Project, Tag 0BFH.** Multiplication by an integer `d` on a nonzero abelian variety
`A` over a field `k` is étale if and only if `d` is invertible in `k`. Nonzero is expressed as
positivity of the dimension of the underlying scheme. -/
theorem etale_zpow_id_left_iff_isUnit_intCast [AlgebraicGeometry.IsAbelianVariety k A]
    (hA : 0 < topologicalKrullDim A.left) (d : ℤ) :
    Etale ((𝟙 A : A ⟶ A) ^ d).left ↔ IsUnit (d : k) := by
  refine ⟨fun h => ?_, etale_zpow_id_left_of_isUnit A d⟩
  have := locallyOfFinitePresentation_zpow_id_left A d
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have h4 := ((etaleAt_tfae ((𝟙 A : A ⟶ A) ^ d).left
    ((η[A]).left (IsLocalRing.closedPoint k))).out 1 4).mp
    ((etale_iff_forall_etaleAt _).mp h _)
  exact isUnit_of_unramifiedAt_zpow_id_left_unit k A hA (IsLocalRing.closedPoint k) d
    (((unramifiedAt_tfae _ _).out 1 3).mpr h4.2)

end Stacks.Groupoids

end
