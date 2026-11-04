module

public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization

/-!
# The two identifications of the conormal sheaf with the pulled-back ideal sheaf

For an immersion `i : Z ⟶ X`, `Stacks.Immersion.conormalSheafSelfIso` and
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` both identify the conormal sheaf `𝒞_{Z/X}`
with `i^* ℐ_i`. This file proves that they are inverse to each other, and computes them on
sections.

## Main results

* `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq_eq_eqToIso_trans`: the comparison
  `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq` along an equation `k ≫ j = L` is the transport
  along that equation followed by `Stacks.Conormal.pullbackIdealSheafCompIso`.
* `Stacks.Immersion.conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf`: the two
  identifications of `𝒞_{Z/X}` with `i^* ℐ_i` are inverse to each other.
* `Stacks.Immersion.conormalSheafSelfIso_hom_unit`: `Stacks.Immersion.conormalSheafSelfIso`
  carries the unit generator of `i^* ℐ_i` named by a section of `ℐ_i` to the unit generator of
  `𝒞_{Z/X}` named by the corresponding section.
* `Stacks.Immersion.conormalSheafIsoPullbackSelf_hom_canonicalConormalQuotientMap`:
  `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` carries the canonical quotient generator
  named by a section of `ℐ_i` to the unit generator named by it.
* `Stacks.Immersion.conormalSheafIsoPullbackSelf_symm_trans_conormalSheafSelfIso_symm_trans`: the
  inverses of the two identifications cancel in a composite.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

/-! ### The comparison presented by an equation, as a transport -/

namespace Stacks.Conormal

/-- The comparison `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq k j L hL` is the transport
`CategoryTheory.eqToIso` along `hL : k ≫ j = L` followed by
`Stacks.Conormal.pullbackIdealSheafCompIso k j`. -/
theorem pullbackIdealSheafIsoOfCompEq_eq_eqToIso_trans {Z U V : Scheme.{u}} (k : Z ⟶ U)
    (j : U ⟶ V) [IsOpenImmersion j] (L : Z ⟶ V) (hL : k ≫ j = L) :
    pullbackIdealSheafIsoOfCompEq k j L hL =
      eqToIso (congrArg (fun f : Z ⟶ V => (modulePullback f.toLRSHom.toShHom).obj
            (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom)) hL).symm ≪≫
        pullbackIdealSheafCompIso k j := by
  subst hL
  exact Iso.ext (Category.id_comp _).symm

end Stacks.Conormal

/-! ### `conormalSheafSelfIso` is the inverse of `conormalSheafIsoPullbackSelf` -/

namespace Stacks.Immersion

open Stacks.ClosedImmersion

variable {Z X : Scheme.{u}}

/-- `Stacks.Immersion.conormalSheafSelfIso i` is the comparison
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq` of the factorization of `i` through
`i.coborderRange.ι`. -/
theorem conormalSheafSelfIso_eq_pullbackIdealSheafIsoOfCompEq (i : Z ⟶ X) [IsImmersion i] :
    conormalSheafSelfIso i =
      Stacks.Conormal.pullbackIdealSheafIsoOfCompEq i.liftCoborder i.coborderRange.ι i
        i.liftCoborder_ι :=
  (congrArg (fun e ↦ (eqToIso (congrArg (fun f : Z ⟶ X ↦ conormalSheaf f.toLRSHom.toShHom)
        i.liftCoborder_ι)).symm ≪≫ e)
      (conormalSheafFactorIso_eq_pullbackIdealSheafCompIso i.coborderRange i.liftCoborder)).trans
    (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq_eq_eqToIso_trans i.liftCoborder
      i.coborderRange.ι i i.liftCoborder_ι).symm

/-- The two identifications `Stacks.Immersion.conormalSheafSelfIso` and
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` of `𝒞_{Z/X}` with `i^* ℐ_i` are inverse to
each other. -/
theorem conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf (i : Z ⟶ X) [IsImmersion i] :
    conormalSheafSelfIso i = (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).symm :=
  conormalSheafSelfIso_eq_pullbackIdealSheafIsoOfCompEq i

/-- For an immersion `i : Z ⟶ X`, an open `O` of `X` and sections `y` of `ℐ_i` over `O` and `x`
of the ideal sheaf of `i.liftCoborder` over the preimage of `O` corresponding under
`Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq`, the identification
`Stacks.Immersion.conormalSheafSelfIso` carries the unit generator of `i^* ℐ_i` named by `y` to the
restriction along `ρ` of the unit generator of `𝒞_{Z/X}` named by `x`. -/
theorem conormalSheafSelfIso_hom_unit (i : Z ⟶ X) [IsImmersion i] (O : X.Opens)
    (ρ : i ⁻¹ᵁ O ⟶ i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ O))
    (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op O))
    (x : (idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
      (op (i.coborderRange.ι ⁻¹ᵁ O)))
    (hxy : (Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq i.liftCoborder
      i.coborderRange.ι i i.liftCoborder_ι).val.app (op O) y = x) :
    (conormalSheafSelfIso i).hom.val.app (op (i ⁻¹ᵁ O))
        (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (idealSheaf i.toLRSHom.toShHom)).val.app (op O) y) =
      (Stacks.Conormal.conormalSheaf i).val.map ρ.op
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (idealSheaf i.liftCoborder.toLRSHom.toShHom)).val.app
            (op (i.coborderRange.ι ⁻¹ᵁ O)) x) :=
  (congrArg (fun e : conormalSheaf i.toLRSHom.toShHom ≅ Stacks.Conormal.conormalSheaf i ↦
        e.hom.val.app (op (i ⁻¹ᵁ O))
          (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
            (idealSheaf i.toLRSHom.toShHom)).val.app (op O) y))
      (conormalSheafSelfIso_eq_pullbackIdealSheafIsoOfCompEq i)).trans
    (Stacks.Conormal.OpenFactorizations.pullbackIdealSheafIsoOfCompEq_hom_unit i.liftCoborder
      i.coborderRange.ι i i.liftCoborder_ι O ρ y x hxy)

/-- `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` carries the image of a section `y` of
`ℐ_i` under the canonical quotient map `Stacks.Immersion.canonicalConormalQuotientMap` to the unit
generator of `i^* ℐ_i` named by `y`. -/
theorem conormalSheafIsoPullbackSelf_hom_canonicalConormalQuotientMap (i : Z ⟶ X)
    [IsImmersion i] (O : X.Opens) (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op O)) :
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).hom.val.app (op (i ⁻¹ᵁ O))
        ((canonicalConormalQuotientMap i).val.app (op O) y) =
      ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (idealSheaf i.toLRSHom.toShHom)).val.app (op O) y :=
  have hinv : (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).hom =
      (conormalSheafSelfIso i).inv :=
    congrArg Iso.inv (conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf i).symm
  (congrArg (fun z : Stacks.Conormal.conormalSheaf i ⟶ conormalSheaf i.toLRSHom.toShHom ↦
        z.val.app (op (i ⁻¹ᵁ O)) ((canonicalConormalQuotientMap i).val.app (op O) y)) hinv).trans
    (congr($((conormalSheafSelfIso i).hom_inv_id).val.app (op (i ⁻¹ᵁ O))
      (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (idealSheaf i.toLRSHom.toShHom)).val.app (op O) y)))

/-- For an isomorphism `e` out of `𝒞_{Z/X}`, the inverse of
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` followed by the inverse of
`Stacks.Immersion.conormalSheafSelfIso` and then `e` is `e`. -/
theorem conormalSheafIsoPullbackSelf_symm_trans_conormalSheafSelfIso_symm_trans (i : Z ⟶ X)
    [IsImmersion i] {N : SheafOfModules.{u} (structureSheafRing
      Z.toLocallyRingedSpace.toRingedSpace)} (e : conormalSheaf i.toLRSHom.toShHom ≅ N) :
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).symm ≪≫
        ((conormalSheafSelfIso i).symm ≪≫ e) = e :=
  (congrArg (fun z : conormalSheaf i.toLRSHom.toShHom ≅ Stacks.Conormal.conormalSheaf i ↦
        z ≪≫ ((conormalSheafSelfIso i).symm ≪≫ e))
      (conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf i).symm).trans
    (Iso.ext ((conormalSheafSelfIso i).hom_inv_id_assoc e.hom))

end Stacks.Immersion

end
