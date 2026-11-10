module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldBase
public import StacksFrontier.Deformation.Predeformation.Basic

/-!
# Comparing the two residue-field objects of the base category

`Deformation.residueFieldObject` is the object of `𝒞_Λ` whose carrier is `ULift k`, which is
what a base category in two independent universes needs; `Deformation.Examples.residueFieldBase`
is the object whose carrier is `k` itself, which is what a deformation problem carrying a datum
over `k` needs. They are isomorphic in `𝒞_Λ`, by the universe-lifting algebra equivalence.

This isomorphism is what lets a statement about the fibre over `residueFieldObject` — which is
how predeformation and deformation categories are defined — be read off at the special-fibre
object of a deformation problem of chapter 93.

## Main definitions

* `Deformation.Examples.residueFieldBaseIso`: the isomorphism
  `residueFieldBase Λ k ≅ residueFieldObject Λ k` in `𝒞_Λ`.

## Main results

* `Deformation.Examples.residueFieldObject_residueEquiv_residue`: the residue-field
  identification of `residueFieldObject` on representatives.

## References

* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
* [Stacks Project, Tag 06GS](https://stacks.math.columbia.edu/tag/06GS)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples

universe u w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The residue-field identification of `residueFieldObject` sends the class of `a` to the
image of `a` under the universe-lowering equivalence. -/
public theorem residueFieldObject_residueEquiv_residue (a : ULift.{w} k) :
    (residueFieldObject.{u, w, w} Λ k).residueEquiv
      (IsLocalRing.residue (ULift.{w} k) a) = ULift.algEquiv (R := Λ) (A := k) a := by
  change ((Ideal.quotientEquivAlgOfEq Λ
      (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{w} k))).trans
      ((AlgEquiv.quotientBot Λ (ULift.{w} k)).trans
        (ULift.algEquiv (R := Λ) (A := k))))
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ULift.{w} k)) a) = _
  simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    AlgEquiv.quotientBot_mk]

/-- The residue field as an object of `𝒞_Λ` with carrier `k`, and the one with carrier
`ULift k`, are isomorphic. -/
public noncomputable def residueFieldBaseIso :
    residueFieldBase Λ k ≅ residueFieldObject.{u, w, w} Λ k :=
  let e := ULift.algEquiv (R := Λ) (A := k)
  { hom :=
      { hom := e.symm.toAlgHom
        isLocal := ⟨fun _ ha => (MulEquiv.isUnit_map e.symm).mp ha⟩
        residue_comm := fun a =>
          (residueFieldObject_residueEquiv_residue _).trans
            ((e.apply_symm_apply a).trans
              (residueFieldBase_residueEquiv_residue Λ k a).symm) }
    inv :=
      { hom := e.toAlgHom
        isLocal := ⟨fun _ ha => (MulEquiv.isUnit_map e).mp ha⟩
        residue_comm := fun a =>
          (residueFieldBase_residueEquiv_residue Λ k _).trans
            (residueFieldObject_residueEquiv_residue a).symm }
    hom_inv_id := ArtinianLocalAlgCat.hom_ext (AlgHom.ext e.apply_symm_apply)
    inv_hom_id := ArtinianLocalAlgCat.hom_ext (AlgHom.ext e.symm_apply_apply) }

end Deformation.Examples
