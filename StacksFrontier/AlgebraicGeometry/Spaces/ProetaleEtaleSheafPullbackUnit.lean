module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullback
public import StacksFrontier.CategoryTheory.Adjunction.AdjunctionUnit
public import StacksCore.Tactic.StacksAttribute

/-!
# An étale sheaf is recovered from its pro-étale inverse image

Let `S` be a scheme and let `ε : S_proétale → S_étale` be the morphism of sites given by the
inclusion `u : S_étale → S_proétale` of the small étale category into the small pro-étale
category, so that `ε_*` is restriction along `u` and `ε⁻¹` is its left adjoint.  For every sheaf
`ℱ` on the small étale site the adjunction map `ℱ ⟶ ε_*ε⁻¹ℱ` is an isomorphism; equivalently
`ε⁻¹ℱ(U) = ℱ(U)` for every étale object `U`, and `ε⁻¹` is fully faithful.

## Main results

* `AlgebraicGeometry.Scheme.isIso_unit_of_etaleToProetale`: the unit `ℱ ⟶ ε_*ε⁻¹ℱ` is an
  isomorphism, for an arbitrary left adjoint `ε⁻¹` of `ε_*`.
* `AlgebraicGeometry.Scheme.isIso_proetaleInverseImageAdjunction_unit`: the same for the
  sheafified left Kan extension, which is the `ε⁻¹` of
  `AlgebraicGeometry.Scheme.etaleInverseImage`.
* `AlgebraicGeometry.Scheme.proetaleInverseImageEtaleSectionsIso`: the sections form
  `ε⁻¹ℱ(U) = ℱ(U)` at an étale object `U`.
* `AlgebraicGeometry.Scheme.proetaleInverseImageFullyFaithful`: `ε⁻¹` is fully faithful.

## Implementation notes

The conclusion is stated for an arbitrary left adjoint of `ε_*` rather than for one chosen model
of `ε⁻¹`, since the argument uses only the adjunction.

## References

* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 0GLZ](https://stacks.math.columbia.edu/tag/0GLZ)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

attribute [local instance] Scheme.Etale.forget_isContinuous Scheme.Etale.forget_isCocontinuous

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-- Restricting `ε⁻¹ℱ` back to the small étale site gives the restriction along the forgetful
functor of the small étale site of the inverse image of `ℱ` on all `S`-schemes. -/
public def Scheme.etaleSectionsSheafCompPushforwardIso :
    Scheme.etaleSectionsSheaf.{u, v} S ⋙
        S.etaleToProetale.sheafPushforwardContinuous (Type (max (u + 1) v))
          S.smallEtaleTopology (Scheme.ProEt.topology S) ≅
      Scheme.bigEtaleInverseImage.{u, v} S ⋙
        (Scheme.Etale.forget S).sheafPushforwardContinuous (Type (max (u + 1) v))
          S.smallEtaleTopology (Scheme.etaleTopology.over S) :=
  Functor.fullyFaithfulCancelRight
    (sheafToPresheaf S.smallEtaleTopology (Type (max (u + 1) v))) (Iso.refl _)

/-- The composite `ε⁻¹ ⋙ ε_*` is the identity functor on sheaves on the small étale site of
`S`. -/
public def Scheme.proetaleInverseImageCompPushforwardIsoId :
    Functor.sheafPullbackConstruction.sheafPullback S.etaleToProetale
          (Type (max (u + 1) v)) S.smallEtaleTopology (Scheme.ProEt.topology S) ⋙
        S.etaleToProetale.sheafPushforwardContinuous (Type (max (u + 1) v))
          S.smallEtaleTopology (Scheme.ProEt.topology S) ≅
      𝟭 (Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :=
  let adjB := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.Etale.forget S) (Type (max (u + 1) v)) S.smallEtaleTopology
    (Scheme.etaleTopology.over S)
  haveI : IsIso adjB.unit := Functor.isIso_unit_of_sheafPushforwardContinuous
    (Scheme.Etale.forget S) (Type (max (u + 1) v)) S.smallEtaleTopology
    (Scheme.etaleTopology.over S) adjB
  Functor.isoWhiskerRight (Scheme.proetaleInverseImageIsoEtaleSectionsSheaf.{u, v} S) _ ≪≫
    Scheme.etaleSectionsSheafCompPushforwardIso.{u, v} S ≪≫ (asIso adjB.unit).symm

/-- For every sheaf `ℱ` on the small étale site of a scheme `S`, the adjunction map
`ℱ ⟶ ε_*ε⁻¹ℱ` is an isomorphism, where `ε : S_proétale → S_étale` is the morphism of sites given
by the inclusion of the small étale category into the small pro-étale category and `ε⁻¹` is an
arbitrary left adjoint of `ε_*`. -/
@[stacks 099T "the adjunction map ℱ ⟶ ε_*ε⁻¹ℱ is an isomorphism, for an arbitrary left \
adjoint ε⁻¹ of ε_*"]
public theorem Scheme.isIso_unit_of_etaleToProetale
    {L : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.ProEt.topology S) (Type (max (u + 1) v))}
    (adj : L ⊣ S.etaleToProetale.sheafPushforwardContinuous (Type (max (u + 1) v))
      S.smallEtaleTopology (Scheme.ProEt.topology S)) :
    IsIso adj.unit :=
  Stacks.Adjunction.isIso_unit_of_comp_iso_id adj
    (Functor.isoWhiskerRight
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous S.etaleToProetale
          (Type (max (u + 1) v)) S.smallEtaleTopology
          (Scheme.ProEt.topology S)).leftAdjointUniq adj).symm _ ≪≫
      Scheme.proetaleInverseImageCompPushforwardIsoId.{u, v} S)

/-- The unit `ℱ ⟶ ε_*ε⁻¹ℱ` of the adjunction between the sheafified left Kan extension along the
inclusion of the small étale category and restriction along it is an isomorphism. -/
@[stacks 099T "the unit of the adjunction ε⁻¹ ⊣ ε_* is an isomorphism"]
public instance Scheme.isIso_proetaleInverseImageAdjunction_unit :
    IsIso (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous S.etaleToProetale
      (Type (max (u + 1) v)) S.smallEtaleTopology (Scheme.ProEt.topology S)).unit :=
  Scheme.isIso_unit_of_etaleToProetale.{u, v} S _

/-- At an étale object `U` of `S` the sections of `ε⁻¹ℱ` are the sections of `ℱ`, naturally in
`ℱ`. -/
@[stacks 099T "the sections form: ε⁻¹ℱ(U) = ℱ(U) for U in S_étale"]
public def Scheme.proetaleInverseImageEtaleSectionsIso (U : S.Etale) :
    Functor.sheafPullbackConstruction.sheafPullback S.etaleToProetale
          (Type (max (u + 1) v)) S.smallEtaleTopology (Scheme.ProEt.topology S) ⋙
        (sheafSections (Scheme.ProEt.topology S) (Type (max (u + 1) v))).obj
          (op (S.etaleToProetale.obj U)) ≅
      (sheafSections S.smallEtaleTopology (Type (max (u + 1) v))).obj (op U) :=
  Functor.isoWhiskerRight (Scheme.proetaleInverseImageCompPushforwardIsoId.{u, v} S)
      ((sheafSections S.smallEtaleTopology (Type (max (u + 1) v))).obj (op U)) ≪≫
    Functor.leftUnitor _

/-- The inverse image `ε⁻¹` along the inclusion of the small étale site of `S` into its small
pro-étale site is fully faithful. -/
@[stacks 099T "equivalently, ε⁻¹ is fully faithful"]
public def Scheme.proetaleInverseImageFullyFaithful :
    (Functor.sheafPullbackConstruction.sheafPullback S.etaleToProetale
      (Type (max (u + 1) v)) S.smallEtaleTopology (Scheme.ProEt.topology S)).FullyFaithful :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous S.etaleToProetale
    (Type (max (u + 1) v)) S.smallEtaleTopology
    (Scheme.ProEt.topology S)).fullyFaithfulLOfIsIsoUnit

end AlgebraicGeometry

end
