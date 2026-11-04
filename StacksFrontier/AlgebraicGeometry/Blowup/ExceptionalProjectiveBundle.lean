module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationTwistComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentreExceptionalDivisor
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdeal
public import StacksFrontier.AlgebraicGeometry.Conormal.DataUniqueness
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.RegularToQuasiRegular
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalSymmetricIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjBundle.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exceptional divisor of a blowup with smooth centre is the projective bundle of `ℐ/ℐ²`

Let `S` be a scheme and let `i : Z ⟶ X` be a closed immersion of schemes smooth over `S`, with
ideal sheaf `ℐ = ker(i)`.  Let `b : X' ⟶ X` be the blowup of `X` in `ℐ` and `E ⊆ X'` its
exceptional divisor, with structure morphism `p : E ⟶ Z` over the centre.  This file proves the
last two assertions of [Stacks, Tag 0FUT]:

`p : E ⟶ Z` is canonically isomorphic to the projective space bundle `𝐏(ℐ/ℐ²) ⟶ Z`, and the
relative `𝒪_E(1)` of that bundle structure is the restriction of `𝒪_{X'}(-E)` to `E`;

and it carries the tag, on a single statement conjoining them with the two smoothness assertions
of `StacksFrontier/AlgebraicGeometry/Blowup/SmoothCentre.lean`.

## Main results

* `Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_smooth_of_smooth`: a closed immersion of
  schemes smooth over a base is a quasi-regular immersion.  This is [Stacks, Tag 067U] — the
  Divisors Lemma 31.23.11 that the proof of Tag 0FUT opens with — in the form the symmetric
  comparison needs.
* `Stacks.AlgebraicGeometry.isPullback_exceptionalProjectiveBundle`: the projective bundle of
  `ℐ/ℐ²` is the fibre product `X' ×_X Z`.
* `Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle` and
  `Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle_hom_toCentre`:
  **Tag 0FUT, third assertion** — the isomorphism `E ≅ 𝐏(ℐ/ℐ²)`, over `Z`.
* `Stacks.AlgebraicGeometry.exceptionalTwistOneIso`: **Tag 0FUT, fourth assertion** —
  `𝒪_E(1) ≅ 𝒪_{X'}(-E)|_E`.
* `Stacks.AlgebraicGeometry.smooth_exceptionalDivisor_isoProjectiveBundle_twistOne`:
  **[Stacks, Tag 0FUT]** — the four assertions together, for the ideal-sheaf presentation of the
  centre.
* `smooth_exceptionalDivisor_isoProjectiveBundle_twistOne_of_isClosedImmersion`, in the same
  namespace: **[Stacks, Tag 0FUT]** — the four assertions together, at the hypotheses the source
  states them under, a closed immersion `i : Z ⟶ X` of schemes smooth over `S`.

## The route

The identification is not constructed by hand; it is produced by exhibiting both sides as
fibre products of the *same* cospan `X' ⟶ X ⟵ Z` and invoking
`CategoryTheory.IsPullback.isoIsPullback`.

* `E = X' ×_X Z` is `AlgebraicGeometry.isPullback_of_isClosedImmersion` applied to the two
  closed immersions, whose one hypothesis is that the inverse image of `ℐ` along `b` is the
  exceptional ideal — true by definition.  The morphism `p : E ⟶ Z` it produces is
  `AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap`, so no new name is introduced for it;
  the centre is presented as `ℐ.subscheme`, which is what `p` lands in.
* `𝐏(ℐ/ℐ²) = X' ×_X Z` is relative-`Proj` base change along `i`,
  `Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange` ([Stacks, Tag 01O3]),
  applied to the Rees situation of `ℐ` over `X` and the symmetric situation of `ℐ/ℐ²` over `Z`.
  Its one datum is a degreewise invertible unital homomorphism
  `i^*(⨁ₙ ℐⁿ) ⟶ Sym(ℐ/ℐ²)`, which is `Stacks.AlgebraicGeometry.exceptionalSymmetricHom`, the
  composite of two isomorphisms:
  - `i^*(⨁ₙ ℐⁿ) ≅ 𝒞_{Z/X,*}`, because both carry the local associated-graded presentations of
    [Stacks, Tag 0630] — the first by `Stacks.Conormal.reesPullbackConormalAlgebra`, the second
    by `Stacks.Conormal.conormalAlgebra` — and those presentations determine the algebra, by
    `Stacks.Conormal.ConormalAlgebraData.unitalHom`;
  - `𝒞_{Z/X,*} ≅ Sym(𝒞_{Z/X})`, the inverse of the canonical map of [Stacks, Tag 0632], which is
    an isomorphism in every degree because `i` is quasi-regular — [Stacks, Tag 063M] condition
    (3), `Stacks.Conormal.isIso_conormalSymmetricHom_app`.

The blowup the geometry is proved for, `AlgebraicGeometry.blowUp`, is the relative `Proj` of a
`Classical.choice`-chosen Rees datum, while the base-change comparison has to be fed a situation
whose graded algebra one can compute with.  The two are identified over `X` by
`Stacks.Blowup.reesSituationBlowUpIso`, and the cartesian square is transported along that
isomorphism by pasting it as a horizontal square with invertible horizontal edges.

## Implementation notes

The centre is presented as the closed subscheme `ℐ.subscheme` cut out by `ℐ`, with its canonical
closed immersion `ℐ.subschemeι`, which is the presentation
`Stacks.AlgebraicGeometry.smooth_exceptionalDivisor_comp_of_idealSheafData` — the smoothness
clause of the same tag — is stated at.

`𝐏(ℐ/ℐ²)` is `Stacks.RelativeProj.projectiveBundle` of `Stacks.Conormal.conormalSheafDegreeOne`,
and `ℐ/ℐ²` is taken to be the degree-one piece of the conormal algebra — the identification the
source itself makes when it writes the canonical map as `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` in Tag 0632.
`Stacks.Conormal.conormalDegreeOneIso` compares it with the pullback of the ideal sheaf along the
closed factorization, so nothing is lost by that choice.

## The route to the fourth assertion

The relative `𝒪_E(1)` of the bundle structure is `𝒪_{𝐏(ℐ/ℐ²)}(1)` read on `E` through the
identification above, and the three isomorphisms carrying it to `𝒪_{X'}(-E)|_E` are each available:

* the twist half of Tag 01O3, `Stacks.RelativeProj.Situation.twistSheafPullbackIso`, applied to
  `Stacks.AlgebraicGeometry.exceptionalSymmetricHom`, gives
  `r^* 𝒪_{Proj(Stacks.Blowup.reesSituation ℐ)}(1) ≅ 𝒪_{𝐏(ℐ/ℐ²)}(1)` for the base-change
  morphism `r`;
* `Stacks.Blowup.reesSituationBlowUpTwistIso` carries the twisting sheaf across the comparison of
  the two presentations of the blowup, which is needed because that base change computes with the
  explicitly built Rees algebra while `AlgebraicGeometry.blowUpTwist` is the twisting sheaf of the
  `Classical.choice`-chosen one;
* `AlgebraicGeometry.twistOneIsoExceptionalIdealModule`, part (3) of [Stacks, Tag 02OS],
  identifies `𝒪_{X'}(1)` with the ideal sheaf of the exceptional divisor.

Their composite is read on `E` by pulling back along
`Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle`, whose compatibility with the
two morphisms to the blowup — the closed immersion of `E` and the first leg
`Stacks.AlgebraicGeometry.exceptionalProjectiveBundleToBlowUp` of the cartesian square — is the
other half of `CategoryTheory.IsPullback.isoIsPullback`,
`Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle_hom_toBlowUp`.

## What the tag is registered on

All four assertions are conjoined by
`Stacks.AlgebraicGeometry.smooth_exceptionalDivisor_isoProjectiveBundle_twistOne`, stated at the
ideal-sheaf presentation of the centre, which is the presentation the smoothness assertions of
`StacksFrontier/AlgebraicGeometry/Blowup/SmoothCentre.lean` use, so that all four speak of one `E`
and one `Z`.  They are conjoined again by
`smooth_exceptionalDivisor_isoProjectiveBundle_twistOne_of_isClosedImmersion`, in the same
namespace, at the hypotheses the source states them under — a closed immersion `i : Z ⟶ X` of
schemes smooth over `S` — with the two morphisms to the centre landing in `Z` itself; it is read
off the ideal-sheaf form along `AlgebraicGeometry.Scheme.Hom.toImage`.  The `@[stacks 0FUT]`
attribute is placed on that closed-immersion form only, as the one declaration stating the whole
tag at the source's hypotheses; the clause-qualified registration of the smoothness of the blowup
in `StacksFrontier/AlgebraicGeometry/Blowup/SmoothCentre.lean` predates it and is kept.

## References

* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 067U](https://stacks.math.columbia.edu/tag/067U)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry

variable {S X Z : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks Project, Tag 067U** (Divisors, Lemma 31.23.11), in the quasi-regular form.  An
immersion between two schemes smooth over a base is a regular immersion, hence a quasi-regular
one.  This is the input the proof of Tag 0FUT opens with. -/
theorem isQuasiRegularImmersion_of_smooth_of_smooth (i : Z ⟶ X) [IsImmersion i] [Smooth f]
    [Smooth (i ≫ f)] : IsQuasiRegularImmersion i :=
  isQuasiRegularImmersion_of_isRegularImmersion i
    (isRegularImmersion_of_smooth_of_smooth i f)

section Comparison

variable (ℐ : X.IdealSheafData) [Smooth f] [Smooth (ℐ.subschemeι ≫ f)]

/-- For a quasi-regular centre, the canonical map `Sym(ℐ/ℐ²) ⟶ 𝒞_{Z/X,*}` is invertible in
every degree. -/
private theorem isIso_conormalSymmetricHom_app_of_quasiRegular
    (h : IsQuasiRegularImmersion ℐ.subschemeι) :
    ∀ n : ℤ, IsIso ((Stacks.Conormal.conormalSymmetricHom ℐ.subschemeι).app n) :=
  Stacks.Conormal.isIso_conormalSymmetricHom_app ℐ.subschemeι h

/-- The degreewise invertible identification `i^*(⨁ₙ ℐⁿ) ⟶ Sym(ℐ/ℐ²)` of graded algebras on the
centre: the comparison of the two sets of local associated-graded presentations of Tag 0630,
followed by the inverse of the canonical map of Tag 0632. -/
def exceptionalSymmetricHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.Conormal.gradedPullback ℐ.subschemeι (Stacks.Blowup.reesSituation ℐ).algebra)
      (symmetricSituationOfQuasicoherent ℐ.subscheme
        (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι)).algebra :=
  haveI : ∀ n : ℤ, IsIso ((Stacks.Conormal.conormalSymmetricHom ℐ.subschemeι).app n) := fun n =>
    Stacks.Conormal.isIso_conormalSymmetricHom_app ℐ.subschemeι
      (isQuasiRegularImmersion_of_smooth_of_smooth f ℐ.subschemeι) n
  (Stacks.Conormal.ConormalAlgebraData.unitalHom
      (Stacks.Conormal.reesPullbackConormalAlgebra ℐ.subschemeι ℐ
        (Scheme.IdealSheafData.ker_subschemeι ℐ))
      (Stacks.Conormal.conormalAlgebra ℐ.subschemeι)).comp
    (Stacks.Conormal.conormalSymmetricHom ℐ.subschemeι).inverse

/-- The identification of graded algebras is an isomorphism in every degree. -/
theorem isIso_exceptionalSymmetricHom_app (n : ℤ) :
    IsIso ((exceptionalSymmetricHom f ℐ).app n) := by
  haveI := isIso_conormalSymmetricHom_app_of_quasiRegular ℐ
    (isQuasiRegularImmersion_of_smooth_of_smooth f ℐ.subschemeι)
  haveI := Stacks.Conormal.ConormalAlgebraData.isIso_unitalHom_app
    (Stacks.Conormal.reesPullbackConormalAlgebra ℐ.subschemeι ℐ
      (Scheme.IdealSheafData.ker_subschemeι ℐ))
    (Stacks.Conormal.conormalAlgebra ℐ.subschemeι) n
  haveI : IsIso ((Stacks.Conormal.conormalSymmetricHom ℐ.subschemeι).inverse.app n) := by
    rw [SheafOfModules.GradedAlgebra.UnitalHom.inverse_app]
    infer_instance
  unfold exceptionalSymmetricHom
  exact SheafOfModules.GradedAlgebra.UnitalHom.isIso_comp_app
    (Stacks.Conormal.ConormalAlgebraData.unitalHom
      (Stacks.Conormal.reesPullbackConormalAlgebra ℐ.subschemeι ℐ
        (Scheme.IdealSheafData.ker_subschemeι ℐ))
      (Stacks.Conormal.conormalAlgebra ℐ.subschemeι))
    (Stacks.Conormal.conormalSymmetricHom ℐ.subschemeι).inverse n

/-- **The projective bundle of `ℐ/ℐ²` is the fibre product `X' ×_X Z`.**  Relative `Proj` base
change along the closed immersion of the centre ([Stacks, Tag 01O3]), transported to
`AlgebraicGeometry.blowUp` along `Stacks.Blowup.reesSituationBlowUpIso`. -/
theorem isPullback_exceptionalProjectiveBundle :
    IsPullback
      (Situation.relativeProjBaseChange (s := Stacks.Blowup.reesSituation ℐ)
          (s' := symmetricSituationOfQuasicoherent ℐ.subscheme
            (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι))
          ℐ.subschemeι (exceptionalSymmetricHom f ℐ)
          (fun m => isIso_exceptionalSymmetricHom_app f ℐ (m : ℤ)) ≫
        (Stacks.Blowup.reesSituationBlowUpIso ℐ).hom)
      (projectiveBundleToBase ℐ.subscheme
        (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι))
      (blowUpToBase ℐ) ℐ.subschemeι := by
  have h1 := Situation.isPullback_relativeProjBaseChange (s := Stacks.Blowup.reesSituation ℐ)
    (s' := symmetricSituationOfQuasicoherent ℐ.subscheme
      (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι))
    ℐ.subschemeι (exceptionalSymmetricHom f ℐ)
    (fun m => isIso_exceptionalSymmetricHom_app f ℐ (m : ℤ))
  exact h1.of_iso (Iso.refl _) (Stacks.Blowup.reesSituationBlowUpIso ℐ) (Iso.refl _)
    (Iso.refl X) (by simp) (Category.comp_id _)
    ((Category.comp_id _).trans
      (Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase ℐ).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The exceptional divisor is the fibre product `X' ×_X Z`.**  The exceptional ideal is by
definition the inverse image of `ℐ` along the blowup morphism, which is the one hypothesis of
`AlgebraicGeometry.isPullback_of_isClosedImmersion`; the morphism to the centre it produces is
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap`. -/
@[sga "7 XVIII 2.1" "more general"]
theorem isPullback_exceptionalDivisor_toCentre :
    IsPullback (exceptionalIdeal ℐ).subschemeι
      (Scheme.IdealSheafData.subschemeMap (exceptionalIdeal ℐ) ℐ (blowUpToBase ℐ)
        (ℐ.le_map_comap (blowUpToBase ℐ)))
      (blowUpToBase ℐ) ℐ.subschemeι :=
  AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])

/-- **Stacks Project, Tag 0FUT**, third assertion.  Let `S` be a scheme and let `ℐ` be a
quasi-coherent ideal sheaf on a scheme `X` smooth over `S` whose closed subscheme `Z = V(ℐ)` is
also smooth over `S`.  Then the exceptional divisor of the blowup of `X` in `ℐ` is canonically
isomorphic to the projective space bundle of the conormal sheaf `ℐ/ℐ²` of the centre. -/
@[sga "6 VII 3.1" "Y' ≅ P(J/J²)"]
def exceptionalDivisorIsoProjectiveBundle :
    exceptionalDivisor ℐ ≅
      projectiveBundle ℐ.subscheme (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) :=
  (isPullback_exceptionalDivisor_toCentre ℐ).isoIsPullback _ _
    (isPullback_exceptionalProjectiveBundle f ℐ)

/-- **Stacks Project, Tag 0FUT**, third assertion.  The identification of the exceptional divisor
with the projective bundle of the conormal sheaf of the centre is an identification **over the
centre**: it carries the structure morphism `p : E ⟶ Z` of the exceptional divisor to the
projection of the projective bundle.  This is the assertion that `p : E ⟶ Z` is canonically
isomorphic to `𝐏(ℐ/ℐ²) ⟶ Z`. -/
@[sga "6 VII 3.1" "special case"]
theorem exceptionalDivisorIsoProjectiveBundle_hom_toCentre :
    (exceptionalDivisorIsoProjectiveBundle f ℐ).hom ≫
        projectiveBundleToBase ℐ.subscheme
          (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) =
      Scheme.IdealSheafData.subschemeMap (exceptionalIdeal ℐ) ℐ (blowUpToBase ℐ)
        (ℐ.le_map_comap (blowUpToBase ℐ)) :=
  (isPullback_exceptionalDivisor_toCentre ℐ).isoIsPullback_hom_snd _ _
    (isPullback_exceptionalProjectiveBundle f ℐ)

/-! ### The twisting sheaf of the bundle structure -/

/-- The base-change morphism `𝐏(ℐ/ℐ²) ⟶ Proj(⨁ₙ ℐⁿ)`: relative `Proj` base change along the
closed immersion of the centre, for the explicitly built Rees algebra. -/
def exceptionalProjectiveBundleToReesProj :
    projectiveBundle ℐ.subscheme (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) ⟶
      Situation.relativeProj (Stacks.Blowup.reesSituation ℐ) :=
  Situation.relativeProjBaseChange (s := Stacks.Blowup.reesSituation ℐ)
    (s' := symmetricSituationOfQuasicoherent ℐ.subscheme
      (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι))
    ℐ.subschemeι (exceptionalSymmetricHom f ℐ)
    (fun m => isIso_exceptionalSymmetricHom_app f ℐ (m : ℤ))

/-- The first leg `𝐏(ℐ/ℐ²) ⟶ X'` of the cartesian square exhibiting the projective bundle of the
conormal sheaf as the fibre product `X' ×_X Z`: relative `Proj` base change along the closed
immersion of the centre, followed by the comparison of the two Rees situations. -/
def exceptionalProjectiveBundleToBlowUp :
    projectiveBundle ℐ.subscheme (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) ⟶
      blowUp ℐ :=
  exceptionalProjectiveBundleToReesProj f ℐ ≫ (Stacks.Blowup.reesSituationBlowUpIso ℐ).hom

/-- The identification of the exceptional divisor with the projective bundle carries the closed
immersion of the exceptional divisor into the blowup to the first leg of the cartesian square.
This is the other half of `CategoryTheory.IsPullback.isoIsPullback`. -/
theorem exceptionalDivisorIsoProjectiveBundle_hom_toBlowUp :
    (exceptionalDivisorIsoProjectiveBundle f ℐ).hom ≫ exceptionalProjectiveBundleToBlowUp f ℐ =
      (exceptionalIdeal ℐ).subschemeι :=
  (isPullback_exceptionalDivisor_toCentre ℐ).isoIsPullback_hom_fst _ _
    (isPullback_exceptionalProjectiveBundle f ℐ)

/-- **`𝒪_{𝐏(ℐ/ℐ²)}(1)` is the inverse image of `𝒪_{X'}(1)` along the first leg of the cartesian
square.**  The twist half of [Stacks, Tag 01O3] for the base change along the closed immersion of
the centre identifies it with the inverse image of the degree-one twisting sheaf of the relative
`Proj` of the explicitly built Rees algebra, and
`Stacks.Blowup.reesSituationBlowUpTwistIso` carries that one to `𝒪_{X'}(1)`. -/
def projectiveBundleTwistOneIso :
    Situation.twistSheaf (symmetricSituationOfQuasicoherent ℐ.subscheme
        (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι)) 1
      ≅ (Scheme.Modules.pullback (exceptionalProjectiveBundleToBlowUp f ℐ)).obj
          (blowUpTwist ℐ 1) :=
  (Situation.twistSheafPullbackIso (s := Stacks.Blowup.reesSituation ℐ)
        (s' := symmetricSituationOfQuasicoherent ℐ.subscheme
          (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι))
        ℐ.subschemeι (exceptionalSymmetricHom f ℐ)
        (fun m => isIso_exceptionalSymmetricHom_app f ℐ (m : ℤ)) 1).symm
    ≪≫ (Scheme.Modules.pullback (exceptionalProjectiveBundleToReesProj f ℐ)).mapIso
        (Stacks.Blowup.reesSituationBlowUpTwistIso ℐ 1).symm
    ≪≫ (Scheme.Modules.pullbackComp (exceptionalProjectiveBundleToReesProj f ℐ)
        (Stacks.Blowup.reesSituationBlowUpIso ℐ).hom).app (blowUpTwist ℐ 1)

/-- **Stacks Project, Tag 0FUT**, fourth assertion.  The relative `𝒪_E(1)` of the
projective-bundle structure of the exceptional divisor — the degree-one twisting sheaf of
`𝐏(ℐ/ℐ²)`, read on `E` through the identification of the third assertion — is the restriction to
`E` of the ideal sheaf `𝒪_{X'}(-E)` of the exceptional divisor.

Three isomorphisms: the twist half of [Stacks, Tag 01O3] for the base change along the closed
immersion of the centre, the transport of the twisting sheaf across the comparison of the two
presentations of the blowup, and part (3) of [Stacks, Tag 02OS]; the composite is read on `E` by
pulling back along the identification, which carries the closed immersion of `E` to the first leg
of the cartesian square. -/
@[sga "6 VII 3.1" "(1), special case"]
def exceptionalTwistOneIso :
    (Scheme.Modules.pullback (exceptionalDivisorIsoProjectiveBundle f ℐ).hom).obj
        (Situation.twistSheaf (symmetricSituationOfQuasicoherent ℐ.subscheme
          (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι)) 1)
      ≅ (Scheme.Modules.pullback (exceptionalIdeal ℐ).subschemeι).obj
          (exceptionalIdealModule ℐ) :=
  (Scheme.Modules.pullback (exceptionalDivisorIsoProjectiveBundle f ℐ).hom).mapIso
      (projectiveBundleTwistOneIso f ℐ)
    ≪≫ (Scheme.Modules.pullbackComp (exceptionalDivisorIsoProjectiveBundle f ℐ).hom
        (exceptionalProjectiveBundleToBlowUp f ℐ)).app (blowUpTwist ℐ 1)
    ≪≫ (Scheme.Modules.pullbackCongr
        (exceptionalDivisorIsoProjectiveBundle_hom_toBlowUp f ℐ)).app (blowUpTwist ℐ 1)
    ≪≫ (Scheme.Modules.pullback (exceptionalIdeal ℐ).subschemeι).mapIso
        (twistOneIsoExceptionalIdealModule ℐ)

/-- **Stacks Project, Tag 0FUT.**  Let `S` be a scheme, let `X` be smooth over `S`, and let `ℐ` be
a quasi-coherent sheaf of ideals on `X` whose closed subscheme `Z = V(ℐ)` is smooth over `S`.  Let
`b : X' ⟶ X` be the blowup of `X` in `ℐ`, let `E ⊆ X'` be its exceptional divisor and
`p : E ⟶ Z` the induced morphism.  Then `X'` is smooth over `S`, `E` is smooth over `S`, there is
an isomorphism `E ≅ 𝐏(ℐ/ℐ²)` over `Z` — so `p` is canonically identified with the projection of
the projective space bundle of the conormal sheaf — and the relative `𝒪_E(1)` of that bundle
structure is the restriction of `𝒪_{X'}(-E)` to `E`.

The two smoothness assertions are
`Stacks.AlgebraicGeometry.smooth_blowUpToBase_comp_of_idealSheafData` and
`smooth_exceptionalDivisor_comp_of_idealSheafData`, the identification over the centre is
`Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle_hom_toCentre`, and the twisting
sheaf is `Stacks.AlgebraicGeometry.exceptionalTwistOneIso`. -/
@[ega "IV 19.4.8" "special case", sga "6 VII 3.1" "special case"]
theorem smooth_exceptionalDivisor_isoProjectiveBundle_twistOne :
    Smooth (blowUpToBase ℐ ≫ f) ∧
      Smooth ((exceptionalIdeal ℐ).subschemeι ≫ blowUpToBase ℐ ≫ f) ∧
      ∃ e : exceptionalDivisor ℐ ≅
          projectiveBundle ℐ.subscheme (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι),
        e.hom ≫ projectiveBundleToBase ℐ.subscheme
              (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) =
            Scheme.IdealSheafData.subschemeMap (exceptionalIdeal ℐ) ℐ (blowUpToBase ℐ)
              (ℐ.le_map_comap (blowUpToBase ℐ)) ∧
          Nonempty ((Scheme.Modules.pullback e.hom).obj
              (Situation.twistSheaf (symmetricSituationOfQuasicoherent ℐ.subscheme
                (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι)) 1)
            ≅ (Scheme.Modules.pullback (exceptionalIdeal ℐ).subschemeι).obj
                (exceptionalIdealModule ℐ)) :=
  ⟨smooth_blowUpToBase_comp_of_idealSheafData f ℐ,
    smooth_exceptionalDivisor_comp_of_idealSheafData f ℐ,
    exceptionalDivisorIsoProjectiveBundle f ℐ,
    exceptionalDivisorIsoProjectiveBundle_hom_toCentre f ℐ,
    ⟨exceptionalTwistOneIso f ℐ⟩⟩

end Comparison

section ClosedImmersionCentre

/-- **Stacks Project, Tag 0FUT.**  Let `S` be a scheme and let `i : Z ⟶ X` be a closed immersion
of schemes smooth over `S`, with ideal sheaf `ℐ = ker(i) ⊂ 𝒪_X`.  Let `b : X' ⟶ X` be the blowup
of `X` in `ℐ` and `E ⊆ X'` its exceptional divisor.  Then `X'` and `E` are smooth over `S`; the
morphism `p : E ⟶ Z` is canonically isomorphic to the projective space bundle
`𝐏(ℐ/ℐ²) ⟶ Z`; and the relative `𝒪_E(1)` of that bundle structure is the restriction of
`𝒪_{X'}(-E)` to `E`.

The morphisms to the centre are the two morphisms `p : E ⟶ Z` and `q : 𝐏(ℐ/ℐ²) ⟶ Z` over `X`,
each determined by its composite with the closed immersion `i`, and the third assertion is that
the identification `E ≅ 𝐏(ℐ/ℐ²)` carries `p` to `q`.

This is `Stacks.AlgebraicGeometry.smooth_exceptionalDivisor_isoProjectiveBundle_twistOne` read at
the ideal sheaf `i.ker` of the closed immersion, whose closed subscheme `V(i.ker)` receives `Z`
by the canonical isomorphism `AlgebraicGeometry.Scheme.Hom.toImage` onto the scheme-theoretic
image; smoothness transports along that isomorphism, and `p` and `q` are read on `Z` through its
inverse. -/
@[stacks 0FUT "all four assertions, for a closed immersion of schemes smooth over the base"]
theorem smooth_exceptionalDivisor_isoProjectiveBundle_twistOne_of_isClosedImmersion
    (i : Z ⟶ X) [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)] :
    Smooth (blowUpToBase i.ker ≫ f) ∧
      Smooth ((exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker ≫ f) ∧
      ∃ (p : exceptionalDivisor i.ker ⟶ Z)
        (q : projectiveBundle i.ker.subscheme
            (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) ⟶ Z)
        (e : exceptionalDivisor i.ker ≅
          projectiveBundle i.ker.subscheme
            (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι)),
        p ≫ i = (exceptionalIdeal i.ker).subschemeι ≫ blowUpToBase i.ker ∧
          q ≫ i = projectiveBundleToBase i.ker.subscheme
                (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) ≫ i.ker.subschemeι ∧
            e.hom ≫ q = p ∧
              Nonempty ((Scheme.Modules.pullback e.hom).obj
                  (Situation.twistSheaf (symmetricSituationOfQuasicoherent i.ker.subscheme
                    (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι)) 1)
                ≅ (Scheme.Modules.pullback (exceptionalIdeal i.ker).subschemeι).obj
                    (exceptionalIdealModule i.ker)) := by
  have hinv : inv i.toImage ≫ i = i.ker.subschemeι :=
    (IsIso.inv_comp_eq _).mpr (Scheme.Hom.toImage_imageι i).symm
  haveI : Smooth (i.ker.subschemeι ≫ f) := by
    rw [← hinv, Category.assoc]
    infer_instance
  obtain ⟨h1, h2, e, he, htwist⟩ :=
    smooth_exceptionalDivisor_isoProjectiveBundle_twistOne f i.ker
  refine ⟨h1, h2,
    Scheme.IdealSheafData.subschemeMap (exceptionalIdeal i.ker) i.ker (blowUpToBase i.ker)
        (i.ker.le_map_comap (blowUpToBase i.ker)) ≫ inv i.toImage,
    projectiveBundleToBase i.ker.subscheme
        (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) ≫ inv i.toImage,
    e, ?_, ?_, ?_, htwist⟩
  · rw [Category.assoc, hinv]
    exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  · rw [Category.assoc, hinv]
  · rw [← Category.assoc, he]

end ClosedImmersionCentre

end Stacks.AlgebraicGeometry

end
