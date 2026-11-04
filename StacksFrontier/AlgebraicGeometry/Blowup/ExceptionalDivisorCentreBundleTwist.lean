module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDivisorCentreBundle
public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumTwistComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `𝒪_E(1)` of the exceptional divisor read on the projective bundle over the centre

Let `i : Z ⟶ X` be a closed immersion of schemes smooth over `S`, `b : X' ⟶ X` the blowing up of
`X` along `Z` in the presentation `Stacks.Blowup.blowUp`, and `E ⊆ X'` its exceptional divisor.
`StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalDivisorCentreBundle.lean` identifies `E` with
the projective bundle `𝐏(𝒞)` of the conormal sheaf `𝒞` read on `Z`, over `Z`. This file carries
the last assertion of [Stacks, Tag 0FUT] across that identification: the tautological twist
`𝒪_{𝐏(𝒞)}(1)` of `Stacks.RelativeProj.tautologicalDatumTwist` restricts on `E` to
`𝒪_{X'}(-E)|_E`, the restriction of the ideal sheaf of `E`.

## Main definitions

* `Stacks.AlgebraicGeometry.negativeTwistComapIso`: the ideal sheaf of the inverse image of a
  closed subscheme along an isomorphism is the inverse image of its ideal sheaf.
* `Stacks.AlgebraicGeometry.exceptionalDivisorIsoCentreBundle_twistIso`:
  `φ^*𝒪_{𝐏(𝒞)}(1) ≅ 𝒪_{X'}(-E)|_E` for the identification `φ : E ≅ 𝐏(𝒞)`.

## References

* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry

/-- **The ideal sheaf of the inverse image of a closed subscheme along an isomorphism** is the
inverse image of its ideal sheaf: `𝒪_Y(-b⁻¹D) ≅ b^*𝒪_X(-D)` for `b : Y ≅ X`. -/
def negativeTwistComapIso {Y X : Scheme.{u}} (b : Y ≅ X) (D : X.IdealSheafData) :
    Stacks.Divisors.negativeTwist (D.comap b.hom) ≅
      (Scheme.Modules.pullback b.hom).obj (Stacks.Divisors.negativeTwist D) :=
  Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare
    (D.comap b.hom).subschemeι (D.comapIso b.hom ≪≫ asIso (pullback.snd b.hom D.subschemeι))
    D.subschemeι b (by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst D b.hom, Iso.trans_hom, asIso_hom,
        Category.assoc, Category.assoc, pullback.condition])

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- The exceptional ideal of `Stacks.Blowup.blowUp` is the inverse image of that of
`AlgebraicGeometry.blowUp` along the comparison of the two presentations. -/
theorem exceptionalIdeal_eq_comap_blowUpIso (ℐ : X.IdealSheafData) :
    Stacks.Blowup.exceptionalIdeal ℐ =
      (AlgebraicGeometry.exceptionalIdeal ℐ).comap (Stacks.Blowup.blowUpIso ℐ).hom := by
  rw [AlgebraicGeometry.exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp,
    Stacks.Blowup.blowUpIso_hom_comp]
  rfl

variable [Smooth f] [Smooth (i ≫ f)]

/-- The morphism `𝐏(𝒞) ⟶ X'` followed by the comparison of the two presentations of the blowup is
the comparison of `𝐏(𝒞)` with the projective bundle over `V(ℐ)` followed by the first leg of the
cartesian square of [Stacks, Tag 0FUT]. -/
theorem centreBundleToBlowUp_comp_blowUpIso_hom [Smooth (i.ker.subschemeι ≫ f)] :
    centreBundleToBlowUp f i ≫ (Stacks.Blowup.blowUpIso i.ker).hom =
      projectiveBundleBaseChange i.toImage
          (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) (centreConormal i)
          (Iso.refl _) ≫ exceptionalProjectiveBundleToBlowUp f i.ker := by
  simp [centreBundleToBlowUp]

/-- The identification of the exceptional divisor with `𝐏(𝒞)`, followed by the comparison of
`𝐏(𝒞)` with the projective bundle over `V(ℐ)` and the first leg of the cartesian square of
[Stacks, Tag 0FUT], is the inclusion of the exceptional divisor followed by the comparison of
the two presentations of the blowup. -/
theorem exceptionalDivisorIsoCentreBundle_hom_comp_baseChange [Smooth (i.ker.subschemeι ≫ f)] :
    (exceptionalDivisorIsoCentreBundle f i).hom ≫
        projectiveBundleBaseChange i.toImage
          (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) (centreConormal i)
          (Iso.refl _) ≫ exceptionalProjectiveBundleToBlowUp f i.ker =
      (Stacks.Blowup.exceptionalIdeal i.ker).subschemeι ≫ (Stacks.Blowup.blowUpIso i.ker).hom := by
  rw [← centreBundleToBlowUp_comp_blowUpIso_hom]
  exact exceptionalDivisorIsoCentreBundle_hom_toBlowUp_assoc f i _

/-- **`𝒪_{𝐏(𝒞)}(1)` restricts to `𝒪_{X'}(-E)|_E`** along the identification `φ : E ≅ 𝐏(𝒞)` of
the exceptional divisor with the projective bundle of the conormal sheaf of the centre, over `Z`
([Stacks, Tag 0FUT], fourth assertion, read on `Z` and for `Stacks.Blowup.blowUp`). -/
@[sga "6 VII 3.1" "(1), special case"]
def exceptionalDivisorIsoCentreBundle_twistIso :
    (Scheme.Modules.pullback (exceptionalDivisorIsoCentreBundle f i).hom).obj
        (tautologicalDatumTwist (centreConormal i)) ≅
      (Scheme.Modules.pullback (Stacks.Blowup.exceptionalIdeal i.ker).subschemeι).obj
        (Stacks.Divisors.negativeTwist (Stacks.Blowup.exceptionalIdeal i.ker)) :=
  haveI := smooth_subschemeι_comp f i
  (Scheme.Modules.pullback (exceptionalDivisorIsoCentreBundle f i).hom).mapIso
      ((tautologicalDatumTwistBaseChangeIso i.toImage
          (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) (centreConormal i)
          (Iso.refl _)).symm ≪≫
        (Scheme.Modules.pullback (projectiveBundleBaseChange i.toImage
          (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) (centreConormal i)
          (Iso.refl _))).mapIso
          ((twistSheafOneIsoTautologicalDatumTwist
              (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι)).symm ≪≫
            projectiveBundleTwistOneIso f i.ker) ≪≫
        (Scheme.Modules.pullbackComp _ _).app _) ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (exceptionalDivisorIsoCentreBundle_hom_comp_baseChange f i)).app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (twistOneIsoExceptionalIdealModule i.ker) ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback (Stacks.Blowup.exceptionalIdeal i.ker).subschemeι).mapIso
      ((negativeTwistComapIso (Stacks.Blowup.blowUpIso i.ker)
          (AlgebraicGeometry.exceptionalIdeal i.ker)).symm ≪≫
        eqToIso (congrArg Stacks.Divisors.negativeTwist
          (exceptionalIdeal_eq_comap_blowUpIso i.ker).symm))

end Stacks.AlgebraicGeometry

end
