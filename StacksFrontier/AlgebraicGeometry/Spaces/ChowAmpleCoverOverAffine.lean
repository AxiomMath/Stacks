module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic

/-!
# Chow's lemma over an affine object of the site, with an ample module on the cover

An algebraic space `Q` over `S` which is proper over an affine object `U` of the big fppf site
admits a proper surjective morphism `h_V ⟶ Q` from an object `V` of the site whose underlying
scheme carries an ample invertible module.

This is `AlgebraicGeometry.Space.exists_properSurjective_schemeCover_of_isProper_toAffine` keeping
the last clause of Chow's lemma (**Stacks 089J**): the cover it produces is H-quasi-projective
over `Spec Γ(U, 𝒪_U)`, hence quasi-projective over an affine scheme, so the pullback of a twist
of the projective bundle is ample (`AlgebraicGeometry.exists_isAmple_of_isQuasiProjective`, the
unit module of an affine scheme being ample).  The proof repeats the change of base of that
statement, which discards the clause.

## Main results

* `AlgebraicGeometry.Space.exists_properSurjective_schemeCover_isAmple_of_isProper_toAffine`:
  the statement above.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Chow's lemma over an affine object of the site, with an ample module on the cover.**  An
algebraic space `Q` over `S` proper over an affine object `U` of the site admits a proper
surjective morphism `h_V ⟶ Q` from an object `V` of the site whose underlying scheme carries an
ample invertible module. -/
theorem exists_properSurjective_schemeCover_isAmple_of_isProper_toAffine
    (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (q : Q ⟶ yoneda.obj U) (hq : IsProper B S hS q) :
    ∃ (V : BigFppfOver B S hS) (ρ : yoneda.obj V ⟶ Q),
      IsProper B S hS ρ ∧ IsSurjective B S hS ρ ∧
        ∃ (L : ((BigFppfOver.toScheme B S hS).obj V).Modules)
          (hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj V) L),
          letI := hL
          Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj V) L := by
  classical
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  -- An isomorphic object of the site whose underlying scheme is literally a `Spec`.
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
  have hq' : IsProper B S hS q' := (isProper_comp_isIso_iff B S hS q yθ.hom).mpr hq
  -- Read `(Q, q')` as an algebraic space over the smaller base `Spec A`.
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
  -- The lower-shriek extension along `g₀`, and the comparison of `Λ Q̃` with `Q`.
  let fIso : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ≅
      ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.left :=
    ((spacesOverSmallerBaseFunctorForgetIso B (Spec A) S hA hS g₀).app Qt).symm
  let lamIso : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ≅ Q := fIso ≪≫ cLeft
  have hlam : lamIso.hom ≫ q' = OverShriek.relocalizeToYoneda g₀ Qt.1 :=
    (Category.assoc fIso.hom cLeft.hom q').trans
      ((congrArg (fun z ↦ fIso.hom ≫ z) hcw).trans
        (relocalizeToYoneda_eq B (Spec A) S hA hS g₀ Qt))
  -- Properness of the structural morphism of `Q̃` over the smaller base.
  have hstructS : IsProper B S hS (OverShriek.relocalizeToYoneda g₀ Qt.1) :=
    hlam ▸ (isProper_isIso_comp_iff B S hS lamIso.hom q').mpr hq'
  have : IsIso (OverShriek.relocalizeToYoneda g₀
      (yoneda.obj (Over.mk (𝟙 (B.obj hA))) : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u)) :=
    isIso_relocalizeToYoneda_yonedaId B (Spec A) S hA hS g₀
  have hstruct : IsProper B (Spec A) hA (toYonedaId B (Spec A) hA Qt.1) := by
    refine (isProper_relocalize_iff B (Spec A) hA S hS g₀ Qt.2
      (isAlgebraicSpace_yoneda B (Spec A) hA (Over.mk (𝟙 (B.obj hA))))
      (toYonedaId B (Spec A) hA Qt.1)).mp ?_
    refine (isProper_comp_isIso_iff B S hS
      ((OverShriek.relocalizePresheafFunctor g₀).map (toYonedaId B (Spec A) hA Qt.1))
      (OverShriek.relocalizeToYoneda g₀
        (yoneda.obj (Over.mk (𝟙 (B.obj hA))) : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u))).mp ?_
    rw [relocalizeToYoneda_eq_map_toYonedaId B (Spec A) S hA hS g₀ Qt.1]
    exact hstructS
  -- Chow's lemma over `Spec A`.
  obtain ⟨V', p, hpProper, hpSurj, hpQP⟩ :=
    hasChowSchemeCover_of_isSeparated_isFiniteType B A hA Qt.1 Qt.2
      (toYonedaId B (Spec A) hA Qt.1) hstruct.1 hstruct.2.1
  -- Carry the cover back to the base `S`.
  let yIso := relocalizedYonedaIso B (B.obj hA) (B.obj hS) g₀ V'
  refine ⟨(Over.map g₀).obj V',
    yIso.inv ≫ (OverShriek.relocalizePresheafFunctor g₀).map p ≫ lamIso.hom, ?_, ?_, ?_⟩
  · exact (isProper_isIso_comp_iff B S hS yIso.inv _).mpr
      ((isProper_comp_isIso_iff B S hS _ lamIso.hom).mpr
        ((isProper_relocalize_iff B (Spec A) hA S hS g₀
          (isAlgebraicSpace_yoneda B (Spec A) hA V') Qt.2 p).mpr hpProper))
  · exact isSurjective_comp B S hS (isSurjective_of_isIso B S hS yIso.inv)
      (isSurjective_comp B S hS (isSurjective_relocalize B (Spec A) hA S hS g₀ p hpSurj)
        (isSurjective_of_isIso B S hS lamIso.hom))
  · -- an ample invertible module on the quasi-projective scheme `V'₀` over `Spec A`
    have : IsAffine (B.inclusion.obj (B.obj hA)) := inferInstanceAs (IsAffine (Spec A))
    exact exists_isAmple_of_isQuasiProjective (B.inclusion.map V'.hom)
      (Stacks.Ample.unitModule (B.inclusion.obj (B.obj hA)))
      (Stacks.Ample.isAmple_unitModule_of_isAffine _)
      (isQuasiProjective_of_isHQuasiProjective (B.inclusion.map V'.hom) hpQP)

end AlgebraicGeometry.Space

end
