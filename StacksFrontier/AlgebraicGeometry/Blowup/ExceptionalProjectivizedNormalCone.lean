module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ProjectivizedNormalCone

/-!
# The exceptional divisor of a blowup is the projectivized normal cone of the centre

Let `X` be a scheme, `ℐ` a quasi-coherent sheaf of ideals on `X` with closed subscheme
`i : Z ⟶ X`, `b : X' ⟶ X` the blowup of `X` in `ℐ` and `E ⊆ X'` its exceptional divisor. Then

  `E ≅ P_ZX = Proj_Z(𝒞_{Z/X,*})`

over `Z`, where `𝒞_{Z/X,*}` is the conormal algebra of [Stacks, Tag 0630] and `P_ZX` its relative
`Proj` (`Stacks.Conormal.projectivizedNormalCone`). No hypothesis on `ℐ` is needed.

## The route

Both sides are fibre products of the cospan `X' ⟶ X ⟵ Z`:

* `E = X' ×_X Z` because the exceptional ideal is the inverse image of `ℐ`
  (`Stacks.AlgebraicGeometry.isPullback_exceptionalDivisor_toCentre`);
* `P_ZX = X' ×_X Z` by relative-`Proj` base change along `i`
  (`Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange`, [Stacks, Tag 01O3]), fed the
  degreewise invertible unital homomorphism `i^*(⨁ₙ ℐⁿ) ⟶ 𝒞_{Z/X,*}`. That homomorphism is
  `Stacks.Conormal.ConormalAlgebraData.unitalHom`: both algebras carry the local associated-graded
  presentations of Tag 0630 (`Stacks.Conormal.reesPullbackConormalAlgebra` and
  `Stacks.Conormal.conormalAlgebra`), and those presentations determine the algebra.

This is the argument of `StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveBundle` with
the conormal algebra itself in place of `Sym(ℐ/ℐ²)`; the quasi-regularity used there only serves
to identify the two.

## Main results

* `Stacks.AlgebraicGeometry.isPullback_exceptionalProjectivizedNormalCone`: `P_ZX = X' ×_X Z`.
* `Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectivizedNormalCone`: `E ≅ P_ZX`.
* `Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectivizedNormalCone_hom_toBase`: the
  isomorphism lies over `Z`.
* `Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectivizedNormalCone_hom_toBlowUp`: it is
  compatible with the two morphisms to `X'`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-- The unital homomorphism `i^*(⨁ₙ ℐⁿ) ⟶ 𝒞_{Z/X,*}` of graded algebras on the centre `Z = V(ℐ)`:
the comparison of the two sets of local associated-graded presentations of Tag 0630. -/
def exceptionalConormalHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.Conormal.gradedPullback ℐ.subschemeι (Stacks.Blowup.reesSituation ℐ).algebra)
      (Stacks.Conormal.conormalProjSituation ℐ.subschemeι).algebra :=
  Stacks.Conormal.ConormalAlgebraData.unitalHom
    (Stacks.Conormal.reesPullbackConormalAlgebra ℐ.subschemeι ℐ
      (Scheme.IdealSheafData.ker_subschemeι ℐ))
    (Stacks.Conormal.conormalAlgebra ℐ.subschemeι)

/-- The homomorphism `i^*(⨁ₙ ℐⁿ) ⟶ 𝒞_{Z/X,*}` is an isomorphism in every degree. -/
instance isIso_exceptionalConormalHom_app (n : ℤ) :
    IsIso ((exceptionalConormalHom ℐ).app n) :=
  Stacks.Conormal.ConormalAlgebraData.isIso_unitalHom_app _ _ n

/-- The base-change morphism `P_ZX ⟶ X'` of relative `Proj` along the closed immersion of the
centre, read into the blowup through the comparison of the two presentations of the blowup. -/
def projectivizedNormalConeToBlowUp :
    Stacks.Conormal.projectivizedNormalCone ℐ.subschemeι ⟶ blowUp ℐ :=
  Situation.relativeProjBaseChange (s := Stacks.Blowup.reesSituation ℐ)
      (s' := Stacks.Conormal.conormalProjSituation ℐ.subschemeι)
      ℐ.subschemeι (exceptionalConormalHom ℐ)
      (fun m => isIso_exceptionalConormalHom_app ℐ (m : ℤ)) ≫
    (Stacks.Blowup.reesSituationBlowUpIso ℐ).hom

/-- **The projectivized normal cone is the fibre product `X' ×_X Z`.** Relative `Proj` base
change along the closed immersion of the centre ([Stacks, Tag 01O3]), transported to
`AlgebraicGeometry.blowUp` along `Stacks.Blowup.reesSituationBlowUpIso`. -/
theorem isPullback_exceptionalProjectivizedNormalCone :
    IsPullback (projectivizedNormalConeToBlowUp ℐ)
      (Stacks.Conormal.projectivizedNormalConeToBase ℐ.subschemeι)
      (blowUpToBase ℐ) ℐ.subschemeι := by
  have h1 := Situation.isPullback_relativeProjBaseChange (s := Stacks.Blowup.reesSituation ℐ)
    (s' := Stacks.Conormal.conormalProjSituation ℐ.subschemeι)
    ℐ.subschemeι (exceptionalConormalHom ℐ) (fun m => isIso_exceptionalConormalHom_app ℐ (m : ℤ))
  exact h1.of_iso (Iso.refl _) (Stacks.Blowup.reesSituationBlowUpIso ℐ) (Iso.refl _)
    (Iso.refl X) (Category.id_comp _).symm (Category.comp_id _)
    ((Category.comp_id _).trans
      (Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase ℐ).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The exceptional divisor of the blowup of `X` in `ℐ` is the projectivized normal cone**
`P_ZX = Proj_Z(𝒞_{Z/X,*})` of the centre `Z = V(ℐ)`. -/
def exceptionalDivisorIsoProjectivizedNormalCone :
    exceptionalDivisor ℐ ≅ Stacks.Conormal.projectivizedNormalCone ℐ.subschemeι :=
  (isPullback_exceptionalDivisor_toCentre ℐ).isoIsPullback _ _
    (isPullback_exceptionalProjectivizedNormalCone ℐ)

/-- The isomorphism `E ≅ P_ZX` lies over the centre: it carries the structure morphism `E ⟶ Z`
to the projection `P_ZX ⟶ Z`. -/
@[reassoc]
theorem exceptionalDivisorIsoProjectivizedNormalCone_hom_toBase :
    (exceptionalDivisorIsoProjectivizedNormalCone ℐ).hom ≫
        Stacks.Conormal.projectivizedNormalConeToBase ℐ.subschemeι =
      Scheme.IdealSheafData.subschemeMap (exceptionalIdeal ℐ) ℐ (blowUpToBase ℐ)
        (ℐ.le_map_comap (blowUpToBase ℐ)) :=
  (isPullback_exceptionalDivisor_toCentre ℐ).isoIsPullback_hom_snd _ _
    (isPullback_exceptionalProjectivizedNormalCone ℐ)

/-- The isomorphism `E ≅ P_ZX` carries the closed immersion `E ⟶ X'` to the base-change
morphism `P_ZX ⟶ X'`. -/
@[reassoc]
theorem exceptionalDivisorIsoProjectivizedNormalCone_hom_toBlowUp :
    (exceptionalDivisorIsoProjectivizedNormalCone ℐ).hom ≫ projectivizedNormalConeToBlowUp ℐ =
      (exceptionalIdeal ℐ).subschemeι :=
  (isPullback_exceptionalDivisor_toCentre ℐ).isoIsPullback_hom_fst _ _
    (isPullback_exceptionalProjectivizedNormalCone ℐ)

end Stacks.AlgebraicGeometry

end
