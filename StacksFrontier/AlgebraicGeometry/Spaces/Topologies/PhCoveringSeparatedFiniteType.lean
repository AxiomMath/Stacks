module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoverings

/-!
# Proper surjective scheme covers of separated algebraic spaces of finite type over an affine

A separated algebraic space of finite type over an affine scheme is covered by a proper
surjective morphism from a scheme.

## Main results

* `exists_properSurjective_schemeCover_of_isSeparated_isFiniteType_toAffine`: an algebraic
  space separated and of finite type over an affine object of the site is the target of a
  proper surjective morphism from a scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Chow's lemma over an affine object of the site, for a separated morphism of finite
type.** An algebraic space over `S` which is separated and of finite type over an affine
object `U` of the site is the target of a proper surjective morphism whose source is an object
of the site, that is a scheme. -/
theorem exists_properSurjective_schemeCover_of_isSeparated_isFiniteType_toAffine
    (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (q : Q ⟶ yoneda.obj U) (hsep : IsSeparated B S hS q) (hft : IsFiniteType B S hS q) :
    ∃ (V : BigFppfOver B S hS) (ρ : yoneda.obj V ⟶ Q),
      IsProper B S hS ρ ∧ IsSurjective B S hS ρ := by
  classical
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  let A : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let eT : Spec A ≅ (BigFppfOver.toScheme B S hS).obj U :=
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.symm
  have hA : B.Contains (Spec A) := (Scheme.size_congr eT).trans_lt U.left.property
  let εiso : B.obj hA ≅ U.left := B.inclusion.preimageIso eT
  let g₀ : B.obj hA ⟶ B.obj hS := εiso.hom ≫ U.hom
  let U' : BigFppfOver B S hS := Over.mk g₀
  let θ : U' ≅ U := Over.isoMk εiso rfl
  let yθ : yoneda.obj U ≅ yoneda.obj U' := yoneda.mapIso θ.symm
  let q' : Q ⟶ yoneda.obj U' := q ≫ yθ.hom
  have hsep' : IsSeparated B S hS q' :=
    (isSeparated_comp_isIso_iff B S hS q yθ.hom).mpr hsep
  have hft' : IsFiniteType B S hS q' :=
    (isFiniteType_comp_isIso_iff B S hS q yθ.hom).mpr hft
  let P₀ : ObjectProperty
      (Over (yoneda.obj U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    fun Z => IsAlgebraicSpace B S hS Z.left
  let Qobj : SpacesOverSmallerBase B (Spec A) S hA hS g₀ := ⟨Over.mk q', hQ⟩
  let eqv := spacesOverSmallerBaseEquivalence B (Spec A) S hA hS g₀
  let Qt : AlgebraicSpaces B (Spec A) hA := eqv.inverse.obj Qobj
  let cIso : (spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt ≅ Qobj :=
    eqv.counitIso.app Qobj
  let cOver : ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1 ≅ (Over.mk q' :
      Over (yoneda.obj U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    (ObjectProperty.ι P₀).mapIso cIso
  let cLeft : ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.left ≅ Q :=
    (Over.forget (yoneda.obj U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).mapIso cOver
  have hcw : cLeft.hom ≫ q' =
      ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.hom := Over.w cOver.hom
  let fIso : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ≅
      ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.left :=
    ((spacesOverSmallerBaseFunctorForgetIso B (Spec A) S hA hS g₀).app Qt).symm
  let lamIso : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ≅ Q := fIso ≪≫ cLeft
  let lam : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ⟶ Q := lamIso.hom
  have : IsIso lam := ⟨lamIso.inv, lamIso.hom_inv_id, lamIso.inv_hom_id⟩
  have hlam : lam ≫ q' = OverShriek.relocalizeToYoneda g₀ Qt.1 :=
    (Category.assoc fIso.hom cLeft.hom q').trans
      ((congrArg (fun z ↦ fIso.hom ≫ z) hcw).trans
        (relocalizeToYoneda_eq B (Spec A) S hA hS g₀ Qt))
  have hstructSepS : IsSeparated B S hS (OverShriek.relocalizeToYoneda g₀ Qt.1) :=
    hlam ▸ (isSeparated_isIso_comp_iff B S hS lam q').mpr hsep'
  have hstructFtS : IsFiniteType B S hS (OverShriek.relocalizeToYoneda g₀ Qt.1) :=
    hlam ▸ (isFiniteType_isIso_comp_iff B S hS lam q').mpr hft'
  have hstructSep : IsSeparated B (Spec A) hA (toYonedaId B (Spec A) hA Qt.1) :=
    (isSeparated_relocalizeToYoneda_iff B (Spec A) S hA hS g₀ Qt.1 Qt.2).mp hstructSepS
  have hstructFt : IsFiniteType B (Spec A) hA (toYonedaId B (Spec A) hA Qt.1) :=
    (isFiniteType_relocalizeToYoneda_iff B (Spec A) S hA hS g₀ Qt.1).mp hstructFtS
  obtain ⟨V', p, hpProper, hpSurj, -⟩ :=
    hasChowSchemeCover_of_isSeparated_isFiniteType B A hA Qt.1 Qt.2
      (toYonedaId B (Spec A) hA Qt.1) hstructSep hstructFt
  let yIso := relocalizedYonedaIso B (B.obj hA) (B.obj hS) g₀ V'
  refine ⟨(Over.map g₀).obj V',
    yIso.inv ≫ (OverShriek.relocalizePresheafFunctor g₀).map p ≫ lam, ?_, ?_⟩
  · exact (isProper_isIso_comp_iff B S hS yIso.inv _).mpr <|
      (isProper_comp_isIso_iff B S hS _ lam).mpr <|
        (isProper_relocalize_iff B (Spec A) hA S hS g₀
          (isAlgebraicSpace_yoneda B (Spec A) hA V') Qt.2 p).mpr hpProper
  · exact isSurjective_comp B S hS (isSurjective_of_isIso B S hS yIso.inv)
      (isSurjective_comp B S hS (isSurjective_relocalize B (Spec A) hA S hS g₀ p hpSurj)
        (isSurjective_of_isIso B S hS lam))

end AlgebraicGeometry.Space

end
