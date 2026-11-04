module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.NonnegTruncationPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.AlgebraSheafComparison
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.Proper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagram clause of Stacks Tag 0EKI

Let `R` be a ring, `P` a proper scheme over `R` and `𝓛` an ample invertible `𝒪_P`-module, and set
`A = Γ_*(P, 𝓛) = ⨁_{m ≥ 0} Γ(P, 𝓛^{⊗ m})`. [Stacks, Tag 0EKI] asserts two things: that
`P = Proj A`, which is `Stacks.SectionRingProjIso.projIsoOfIsProper`, and that diagram
[Stacks, Tag 0EKG] takes the form in which the two left-hand entries are written with
`𝓛^{⊗ m}` in place of `𝒪_P(m)`:

`Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m}) ⟶ L = Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m}) ⟶^π P`.

**This file proves the second assertion.** Diagram [Stacks, Tag 0EKG] is formalized over `Proj A`,
with its two left-hand entries presented as the relative spectra of the twist algebras:
`Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecTwistAlgebraIso` is
`L = Spec_{Proj A}(⨁_{m ≥ 0} 𝒪(m))` and
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIso` is
`U = Spec_{Proj A}(⨁_{m ∈ ℤ} 𝒪(m))`. What is proved here is that both, read over `P` through the
canonical morphism `r : P ⟶ Proj A` of [Stacks, Tag 01PZ], are the relative spectra over `P` of
the Laurent algebras of `𝓛`.

## The route

Reading a relative spectrum over a new base is [Stacks, Tag 01LX] part (2),
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`: the fibre product
`Spec_{Proj A}(B) ×_{Proj A} P` is `Spec_P((algebraPullback r).obj B)`. So the whole clause is
the identification of the two algebra pullbacks:

* `(algebraPullback r).obj (⨁_{m ∈ ℤ} 𝒪(m)) ≅ ⨁_{m ∈ ℤ} 𝓛^{⊗ m}`, which is
  `Stacks.GradedRealizationPullback.comparisonIso` — the algebra pullback of an ungraded
  realisation is the realisation of the degreewise pullback — followed by
  `Stacks.SectionRingProjIso.pbTwistAlgebraSheafIsoLaurent`, Situation [Stacks, Tag 01QH]'s
  comparison read between the algebra sheaves;
* `(algebraPullback r).obj (⨁_{m ≥ 0} 𝒪(m)) ≅ ⨁_{m ≥ 0} 𝓛^{⊗ m}`, which is the same with the
  degreewise pullback commuted past the nonnegative truncation
  (`Stacks.GradedRealizationPullback.nonnegTruncationAlgebraSheafComparisonIso`) and
  `Stacks.SectionRingProjIso.pbNonnegTwistAlgebraSheafIsoNonnegLaurent`.

Neither identification uses properness: they hold for every ample invertible module, and that is
how they are stated. Properness enters only in the last step, where `r` is an isomorphism
(`Stacks.SectionRingProjIso.projIsoOfIsProper`) and the fibre product over it is the scheme
itself — `Stacks.AlgebraicGeometry.OverBaseChange.overPullbackIsoOfIsIso` — so that the two
entries are read over `P` as the source says, with the structure morphisms `π` and `π|_U`
composed with `r⁻¹`.

## Main definitions

* `Stacks.AlgebraicGeometry.OverBaseChange.overPullbackIsoOfIsIso`: base change along an
  isomorphism changes nothing — `Y ×_Z P` over `P` is `Y` over `P` through `r⁻¹`.
* `Stacks.SectionRingProjIso.nonnegLaurentRelativeSpecOver` and `laurentRelativeSpecOver`:
  `Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m})` and `Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m})` as schemes over `P`.
* `Stacks.SectionRingProjIso.coneBaseChangeIsoNonnegLaurent` and
  `puncturedConeBaseChangeIsoLaurent`: the two entries after base change to `P`, for an
  arbitrary ample invertible module.
* `Stacks.SectionRingProjIso.coneIsoNonnegLaurentOfIsProper` and
  `puncturedConeIsoLaurentOfIsProper`: **the two left-hand entries of [Stacks, Tag 0EKG]'s
  diagram, for `P` proper over `R`, read over `P` itself** — the diagram clause of
  [Stacks, Tag 0EKI].

## References

* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.RelativeSpec

universe u

namespace Stacks.AlgebraicGeometry.OverBaseChange

/-- **Base change along an isomorphism changes nothing.** For `r : P ⟶ Z` an isomorphism and
`h : Q ⟶ Z` arbitrary, the fibre product `Q ×_Z P`, viewed over `P` by its second projection, is
`Q` viewed over `P` by `h` followed by `r⁻¹`. The comparison is the first projection, which is an
isomorphism because isomorphisms are stable under base change
(`CategoryTheory.Limits.pullback_fst_iso_of_right_iso`). -/
def overPullbackIsoOfIsIso {Z P Q : Scheme.{u}} (h : Q ⟶ Z) (r : P ⟶ Z) [IsIso r] :
    (Over.pullback r).obj (Over.mk h) ≅ Over.mk (h ≫ inv r) :=
  Over.isoMk (asIso (pullback.fst h r))
    (show pullback.fst h r ≫ h ≫ inv r = pullback.snd h r from
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ inv r) (pullback.condition (f := h) (g := r))).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (pullback.snd h r ≫ ·) (IsIso.hom_inv_id r)).trans
              (Category.comp_id _)))))

end Stacks.AlgebraicGeometry.OverBaseChange

namespace Stacks.SectionRingProjIso

open Stacks.Ample (IsAmple IsInvertibleModule)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.ProjConeTwist
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)

/-! ### The algebra pullbacks of the two twist algebras -/

/-- **`r^*(⨁_{m ∈ ℤ} 𝒪_{Proj A}(m)) ≅ ⨁_{m ∈ ℤ} 𝓛^{⊗ m}` as algebra sheaves on `X`**, for the
*algebra* pullback along the canonical morphism `r` of [Stacks, Tag 01PZ].

`Stacks.GradedRealizationPullback.comparisonIso` identifies the algebra pullback of the ungraded
realisation with the ungraded realisation of the degreewise pullback, which is
`Stacks.SectionRingProjIso.pbTwistAlgebraSheaf`, and
`Stacks.SectionRingProjIso.pbTwistAlgebraSheafIsoLaurent` identifies that with the Laurent
algebra of `𝓛`. -/
def algebraPullbackTwistIsoLaurent :
    (algebraPullback (projHomOfIsAmple L hL)).obj (integerTwistAlgebraSheaf (grading L)) ≅
      laurentAlgebraSheaf L :=
  Stacks.GradedRealizationPullback.comparisonIso (projHomOfIsAmple L hL)
      (integerTwistAlgebra (grading L)) (heq_twistMul_comm (grading L)) ≪≫
    pbTwistAlgebraSheafIsoLaurent L hL

/-- **`r^*(⨁_{m ≥ 0} 𝒪_{Proj A}(m)) ≅ ⨁_{m ≥ 0} 𝓛^{⊗ m}` as algebra sheaves on `X`.** This is
`algebraPullbackTwistIsoLaurent` in nonnegative degrees: the nonnegative twist algebra is the
truncation of the integral one
(`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra_eq_nonnegTruncation`), the degreewise
pullback commutes with the truncation
(`Stacks.GradedRealizationPullback.nonnegTruncationAlgebraSheafComparisonIso`), and
`Stacks.SectionRingProjIso.pbNonnegTwistAlgebraSheafIsoNonnegLaurent` is the comparison with the
nonnegative Laurent algebra. -/
def algebraPullbackNonnegTwistIsoNonnegLaurent :
    (algebraPullback (projHomOfIsAmple L hL)).obj (nonnegTwistAlgebraSheaf (grading L)) ≅
      nonnegLaurentAlgebraSheaf L :=
  Stacks.GradedRealizationPullback.nonnegTruncationAlgebraSheafComparisonIso
      (projHomOfIsAmple L hL) (integerTwistAlgebra (grading L))
      (heq_twistMul_comm (grading L)) ≪≫
    pbNonnegTwistAlgebraSheafIsoNonnegLaurent L hL

/-- The Laurent algebra `⨁_{m ∈ ℤ} 𝓛^{⊗ m}` is a quasi-coherent sheaf of `𝒪_X`-algebras: it is
the algebra pullback of the quasi-coherent integral twist algebra. -/
theorem isQuasicoherent_laurentAlgebraSheaf {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) :
    AlgebraSheaf.IsQuasicoherent (laurentAlgebraSheaf L) :=
  AlgebraSheaf.isQuasicoherent_of_iso (algebraPullbackTwistIsoLaurent L hL) inferInstance

/-- The nonnegative Laurent algebra `⨁_{m ≥ 0} 𝓛^{⊗ m}` is a quasi-coherent sheaf of
`𝒪_X`-algebras. -/
theorem isQuasicoherent_nonnegLaurentAlgebraSheaf {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) :
    AlgebraSheaf.IsQuasicoherent (nonnegLaurentAlgebraSheaf L) :=
  AlgebraSheaf.isQuasicoherent_of_iso
    (algebraPullbackNonnegTwistIsoNonnegLaurent L hL) inferInstance

/-! ### The two relative spectra over `X` -/

/-- **`Spec_X(⨁_{m ≥ 0} 𝓛^{⊗ m})`, as a scheme over `X`**: the right-hand side of the
substitution the diagram clause of [Stacks, Tag 0EKI] makes in the nonnegatively graded left-hand
entry `L` of [Stacks, Tag 0EKG]'s diagram. Naming it keeps the quasi-coherence datum
`isQuasicoherent_nonnegLaurentAlgebraSheaf`, which depends on the ampleness hypothesis and so is
not an instance, out of the statements below. -/
@[ega "II 8.3.1" "special case"]
def nonnegLaurentRelativeSpecOver : Over X :=
  haveI := isQuasicoherent_nonnegLaurentAlgebraSheaf L hL
  Over.mk (relativeSpecToBase (nonnegLaurentAlgebraSheaf L))

/-- **`Spec_X(⨁_{m ∈ ℤ} 𝓛^{⊗ m})`, as a scheme over `X`**: the right-hand side of the
substitution the diagram clause of [Stacks, Tag 0EKI] makes in the integer-graded left-hand entry
`U` of [Stacks, Tag 0EKG]'s diagram. -/
def laurentRelativeSpecOver : Over X :=
  haveI := isQuasicoherent_laurentAlgebraSheaf L hL
  Over.mk (relativeSpecToBase (laurentAlgebraSheaf L))

/-! ### The two entries after base change to `X` -/

/-- **`L ×_{Proj A} X = Spec_X(⨁_{m ≥ 0} 𝓛^{⊗ m})`**: the nonnegatively graded left-hand entry of
[Stacks, Tag 0EKG]'s diagram, base changed along the canonical morphism `r` of
[Stacks, Tag 01PZ], is the relative spectrum over `X` of `⨁_{m ≥ 0} 𝓛^{⊗ m}`. No properness is
used; ampleness of `𝓛` is enough. -/
def coneBaseChangeIsoNonnegLaurent :
    (Over.pullback (projHomOfIsAmple L hL)).obj (Over.mk (pi (grading L))) ≅
      nonnegLaurentRelativeSpecOver L hL :=
  haveI := isQuasicoherent_nonnegLaurentAlgebraSheaf L hL
  (Over.pullback (projHomOfIsAmple L hL)).mapIso
      (coneRelativeSpecTwistAlgebraIso (grading L)) ≪≫
    relativeSpecBaseChangeIso (projHomOfIsAmple L hL) (nonnegTwistAlgebraSheaf (grading L)) ≪≫
    relativeSpecOverIso (algebraPullbackNonnegTwistIsoNonnegLaurent L hL)

/-- **`U ×_{Proj A} X = Spec_X(⨁_{m ∈ ℤ} 𝓛^{⊗ m})`**: the integer-graded left-hand entry of
[Stacks, Tag 0EKG]'s diagram, base changed along the canonical morphism `r` of
[Stacks, Tag 01PZ], is the relative spectrum over `X` of `⨁_{m ∈ ℤ} 𝓛^{⊗ m}`. No properness is
used; ampleness of `𝓛` is enough. -/
def puncturedConeBaseChangeIsoLaurent :
    (Over.pullback (projHomOfIsAmple L hL)).obj
        (Over.mk ((openUInL (grading L)).ι ≫ pi (grading L))) ≅
      laurentRelativeSpecOver L hL :=
  haveI := isQuasicoherent_laurentAlgebraSheaf L hL
  (Over.pullback (projHomOfIsAmple L hL)).mapIso
      (puncturedConeRelativeSpecTwistAlgebraIso (grading L)) ≪≫
    relativeSpecBaseChangeIso (projHomOfIsAmple L hL) (integerTwistAlgebraSheaf (grading L)) ≪≫
    relativeSpecOverIso (algebraPullbackTwistIsoLaurent L hL)

/-! ### The diagram clause of Tag 0EKI -/

variable {R : CommRingCat.{u}} (f : X ⟶ Spec R) [IsProper f]

/-- **The diagram clause of [Stacks, Tag 0EKI], nonnegatively graded entry.** For `P` proper over
a ring `R` and `𝓛` an ample invertible `𝒪_P`-module with section ring `A = Γ_*(P, 𝓛)`, the
nonnegatively graded left-hand entry `L` of [Stacks, Tag 0EKG]'s diagram, read over `P` through
the identification `P = Proj A`, is `Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m})`.

The structure morphism on the left is the cone projection `π` followed by the inverse of the
canonical morphism `r : P ⟶ Proj A` of [Stacks, Tag 01PZ], which is an isomorphism by
`Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper`; that is what makes the base
change in `coneBaseChangeIsoNonnegLaurent` the identity, by
`Stacks.AlgebraicGeometry.OverBaseChange.overPullbackIsoOfIsIso`. -/
@[stacks 0EKI "the diagram clause: the nonnegatively graded left-hand entry L of diagram 0EKG \
becomes Spec_P of the direct sum of the nonnegative tensor powers of the ample module"]
def coneIsoNonnegLaurentOfIsProper :
    Over.mk (pi (grading L) ≫ (projIsoOfIsProper L hL f).inv) ≅
      nonnegLaurentRelativeSpecOver L hL :=
  haveI := isIso_projHomOfIsAmple_of_isProper L hL f
  (Stacks.AlgebraicGeometry.OverBaseChange.overPullbackIsoOfIsIso
      (pi (grading L)) (projHomOfIsAmple L hL)).symm ≪≫
    coneBaseChangeIsoNonnegLaurent L hL

/-- **The diagram clause of [Stacks, Tag 0EKI], integer-graded entry.** For `P` proper over a ring
`R` and `𝓛` an ample invertible `𝒪_P`-module with section ring `A = Γ_*(P, 𝓛)`, the
integer-graded left-hand entry `U` of [Stacks, Tag 0EKG]'s diagram, read over `P` through the
identification `P = Proj A`, is `Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m})`. -/
@[stacks 0EKI "the diagram clause: the integer-graded left-hand entry U of diagram 0EKG becomes \
Spec_P of the direct sum of all integral tensor powers of the ample module"]
def puncturedConeIsoLaurentOfIsProper :
    Over.mk ((openUInL (grading L)).ι ≫ pi (grading L) ≫ (projIsoOfIsProper L hL f).inv) ≅
      laurentRelativeSpecOver L hL :=
  haveI := isIso_projHomOfIsAmple_of_isProper L hL f
  (Stacks.AlgebraicGeometry.OverBaseChange.overPullbackIsoOfIsIso
        ((openUInL (grading L)).ι ≫ pi (grading L)) (projHomOfIsAmple L hL)).symm ≪≫
      puncturedConeBaseChangeIsoLaurent L hL

end Monoidal

end Stacks.SectionRingProjIso

end
