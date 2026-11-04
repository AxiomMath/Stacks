module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exceptional divisor as a projective bundle over the centre itself

Let `i : Z ⟶ X` be a closed immersion of schemes smooth over a base `S`, with ideal sheaf
`ℐ = ker(i)`, let `b : X' ⟶ X` be the blowing up of `X` along `Z` in the presentation
`Stacks.Blowup.blowUp`, and let `p : E ⟶ Z` be its exceptional divisor over the centre. By
[Stacks, Tag 0FUT] the exceptional divisor is the projective bundle of the conormal sheaf
`ℐ/ℐ²`. The library proves this over the closed subscheme `V(ℐ)` cut out by `ℐ` and for the
presentation `AlgebraicGeometry.blowUp` of the blowup. This file reads it over `Z` itself and for
`Stacks.Blowup.blowUp`, which is the form the proof of [Stacks, Tag 0FUW] uses: the projective
bundle `𝐏(𝒞) ⟶ Z` of the pullback `𝒞` of `ℐ/ℐ²` along `Z ≅ V(ℐ)` is the fibre product `X' ×_X Z`,
as is `E`, so the two are identified over `Z`.

## Main definitions

* `Stacks.AlgebraicGeometry.centreConormal`: `𝒞 = ℐ/ℐ²` on `Z`.
* `Stacks.AlgebraicGeometry.centreBundleToBlowUp`: the morphism `𝐏(𝒞) ⟶ X'`.
* `Stacks.AlgebraicGeometry.exceptionalDivisorIsoCentreBundle`: the identification `E ≅ 𝐏(𝒞)`.

## Main results

* `Stacks.AlgebraicGeometry.isPullback_centreBundle`: `𝐏(𝒞) = X' ×_X Z`.
* `Stacks.AlgebraicGeometry.exceptionalDivisorIsoCentreBundle_hom_toBase`: the identification is
  one over `Z`.

## References

* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The conormal sheaf `𝒞 = ℐ/ℐ²` of the centre, on `Z`**: the conormal sheaf of the closed
subscheme `V(ℐ)` cut out by `ℐ = ker(i)`, read on `Z` through `Z ≅ V(ℐ)`. -/
abbrev centreConormal : Z.Modules :=
  (Scheme.Modules.pullback i.toImage).obj (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι)

/-- The conormal sheaf `𝒞` of the centre is quasi-coherent. -/
instance isQuasicoherent_centreConormal : (centreConormal i).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback i.toImage _ inferInstance

/-- The inverse of `Z ≅ V(ℐ)` followed by `i` is the inclusion of the closed subscheme `V(ℐ)`
into `X`. -/
lemma inv_toImage_comp : inv i.toImage ≫ i = i.ker.subschemeι :=
  (IsIso.inv_comp_eq _).mpr (Scheme.Hom.toImage_imageι i).symm

/-- If `Z` is smooth over `S`, then so is the closed subscheme `V(ℐ)` cut out by `ℐ = ker(i)`. -/
lemma smooth_subschemeι_comp [Smooth (i ≫ f)] : Smooth (i.ker.subschemeι ≫ f) := by
  rw [← inv_toImage_comp i, Category.assoc]
  infer_instance

variable [Smooth f] [Smooth (i ≫ f)]

/-- **The morphism `𝐏(𝒞) ⟶ X'`**: the comparison of `𝐏(𝒞)` with the projective bundle of `ℐ/ℐ²`
over `V(ℐ)`, followed by the first leg of the cartesian square of [Stacks, Tag 0FUT] and the
comparison of the two presentations of the blowup. -/
@[sga "5 VII 9.6" "partial"]
def centreBundleToBlowUp :
    projectiveBundle Z (centreConormal i) ⟶ Stacks.Blowup.blowUp i.ker :=
  haveI := smooth_subschemeι_comp f i
  projectiveBundleBaseChange i.toImage (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι)
      (centreConormal i) (Iso.refl _) ≫
    exceptionalProjectiveBundleToBlowUp f i.ker ≫ (Stacks.Blowup.blowUpIso i.ker).inv

/-- **The projective bundle of the conormal sheaf of the centre is the fibre product
`X' ×_X Z`**: the base change of the cartesian square of [Stacks, Tag 0FUT] along `Z ≅ V(ℐ)`. -/
@[sga "6 VII 3.1" "Y' = Y×_X X' is P(N)"]
theorem isPullback_centreBundle :
    IsPullback (centreBundleToBlowUp f i) (projectiveBundleToBase Z (centreConormal i))
      (Stacks.Blowup.blowUpToBase i.ker) i := by
  have := smooth_subschemeι_comp f i
  have h := (isPullback_projectiveBundleBaseChange i.toImage
    (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) (centreConormal i)
    (Iso.refl _)).paste_horiz (isPullback_exceptionalProjectiveBundle f i.ker)
  rw [Scheme.Hom.toImage_imageι] at h
  refine h.of_iso (Iso.refl _) (Stacks.Blowup.blowUpIso i.ker).symm (Iso.refl _) (Iso.refl X)
    ?_ (by simp) ?_ (by simp)
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, centreBundleToBlowUp,
      Category.assoc]
    rfl
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, eq_comm, Iso.inv_comp_eq,
      Stacks.Blowup.blowUpIso_hom_comp]

/-- **[Stacks, Tag 0FUT] over the centre**: the exceptional divisor is the projective bundle of
the conormal sheaf of the centre, read on `Z`. -/
@[sga "6 VII 3.1" "Y' ≅ P(J/J²)"]
def exceptionalDivisorIsoCentreBundle :
    Stacks.Blowup.exceptionalDivisor i.ker ≅ projectiveBundle Z (centreConormal i) :=
  (Stacks.Blowup.isPullback_exceptionalToCentre i).isoIsPullback _ _ (isPullback_centreBundle f i)

/-- The identification of the exceptional divisor with `𝐏(𝒞)` is one over `Z`. -/
@[reassoc]
theorem exceptionalDivisorIsoCentreBundle_hom_toBase :
    (exceptionalDivisorIsoCentreBundle f i).hom ≫ projectiveBundleToBase Z (centreConormal i) =
      Stacks.Blowup.exceptionalToCentre i :=
  (Stacks.Blowup.isPullback_exceptionalToCentre i).isoIsPullback_hom_snd _ _
    (isPullback_centreBundle f i)

/-- The identification of the exceptional divisor with `𝐏(𝒞)` carries the inclusion of the
exceptional divisor into the blowup to the morphism `𝐏(𝒞) ⟶ X'`. -/
@[reassoc]
theorem exceptionalDivisorIsoCentreBundle_hom_toBlowUp :
    (exceptionalDivisorIsoCentreBundle f i).hom ≫ centreBundleToBlowUp f i =
      (Stacks.Blowup.exceptionalIdeal i.ker).subschemeι :=
  (Stacks.Blowup.isPullback_exceptionalToCentre i).isoIsPullback_hom_fst _ _
    (isPullback_centreBundle f i)

end Stacks.AlgebraicGeometry

end
