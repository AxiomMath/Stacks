module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistRelativeSpecInclusion
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.NonnegTruncationInclusionPullback
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseChangeOverBase
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.DiagramClause
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The arrows of the diagram of Stacks Tag 0EKI

Let `R` be a ring, `P` a proper scheme over `R`, `𝓛` an ample invertible `𝒪_P`-module and
`A = Γ_*(P, 𝓛)`. [Stacks, Tag 0EKI] says that `P = Proj A` and that diagram [Stacks, Tag 0EKG]
*becomes* the diagram

`Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m}) ⟶ L = Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m}) ⟶^π P`

over `U ⟶ X ⟶ Z`. `StacksFrontier/AlgebraicGeometry/SectionRingProjIso/DiagramClause.lean`
identifies the entries one by one: `Stacks.SectionRingProjIso.coneIsoNonnegLaurentOfIsProper`
and `Stacks.SectionRingProjIso.puncturedConeIsoLaurentOfIsProper`. **This file proves that these
identifications are compatible with the arrows of the diagram**, so that the diagram is
identified arrow by arrow.

## The top arrow

The new top arrow is `Stacks.SectionRingProjIso.laurentToNonnegLaurentRelativeSpec`, the
morphism of relative spectra induced by the inclusion
`Stacks.SectionRingProjIso.nonnegLaurentToLaurentAlgebraSheafHom` of algebras. The old one is the
open immersion `U ⟶ L`, which [Stacks, Tag 0EKG] already identifies with the morphism induced by
`⨁_{m ≥ 0} 𝒪(m) ⊆ ⨁_{m ∈ ℤ} 𝒪(m)`
(`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedToConeRelativeSpecTwistAlgebra_comp`). The
identifications are built from the base change along `r : P ⟶ Proj A` ([Stacks, Tag 01LX]) and
the comparison of the algebra pullbacks of the twist algebras with the Laurent algebras; so the
compatibility is three naturalities:

* of the algebra comparison in the inclusion,
  `algebraPullback_map_comp_algebraPullbackTwistIsoLaurent_hom`, which is
  `Stacks.GradedRealizationPullback.algebraPullback_map_inclusion_comp_hom`;
* of the base change of relative spectra, `relativeSpecOverIso_inv_comp_baseChange`, checked on
  direct-image algebras with `Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom_naturality`;
* of the base change along an isomorphism,
  `Stacks.AlgebraicGeometry.OverBaseChange.overPullbackIsoOfIsIso_hom_comp`.

## Main results

* `Stacks.SectionRingProjIso.puncturedConeIsoLaurentOfIsProper_inv_comp`: **the open immersion
  `U ⟶ L` is the morphism induced by the inclusion of algebras**, under the identifications.
* `Stacks.SectionRingProjIso.projAndSpecDiagram_eq_laurentDiagram_of_isProper`: **[Stacks, Tag
  0EKI]**, the whole identification of diagrams: `P = Proj A`, the top arrow, the projections to
  `P`, the left identification with `U`, and the two squares.

## References

* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation
open Stacks.RelativeSpec

universe u

namespace Stacks.AlgebraicGeometry.OverBaseChange

/-- **Base change along an isomorphism is natural.** For `r : P ⟶ Z` an isomorphism and a
morphism `u : Q ⟶ Q'` of schemes over `Z`, the identification `Q ×_Z P ≅ Q` over `P` of
`overPullbackIsoOfIsIso` carries the base change of `u` to `u` itself. -/
theorem overPullbackIsoOfIsIso_hom_comp {Z P Q Q' : Scheme.{u}} (h : Q ⟶ Z) (h' : Q' ⟶ Z)
    (r : P ⟶ Z) [IsIso r] (v : Over.mk h ⟶ Over.mk h') :
    (overPullbackIsoOfIsIso h r).hom ≫
        Over.homMk (U := Over.mk (h ≫ inv r)) (V := Over.mk (h' ≫ inv r)) v.left
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ inv r) (Over.w v))) =
      (Over.pullback r).map v ≫ (overPullbackIsoOfIsIso h' r).hom := by
  ext
  exact (pullback.lift_fst _ _ _).symm

end Stacks.AlgebraicGeometry.OverBaseChange

namespace Stacks.SectionRingProjIso

open Stacks.Ample (IsAmple IsInvertibleModule)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.ProjConeTwist
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (laurent isSheafStruct)

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

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)

/-- **The inclusion `⨁_{m ≥ 0} 𝓛^{⊗ m} ⟶ ⨁_{m ∈ ℤ} 𝓛^{⊗ m}` of sheaves of commutative
`𝒪_P`-algebras**: the inclusion of the nonnegative truncation of the Laurent algebra
(`Stacks.AlgebraicGeometry.NonnegTruncation.inclusion`), realised. -/
def nonnegLaurentToLaurentAlgebraSheafHom :
    nonnegLaurentAlgebraSheaf L ⟶ laurentAlgebraSheaf L :=
  letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  gradedAlgebraSheafMap X (Stacks.AlgebraicGeometry.NonnegTruncation.inclusion (laurent L))
    (Stacks.AlgebraicGeometry.NonnegTruncation.isCommutative_nonnegTruncation (laurent L)
      (Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm X.toRingedSpace.presheaf
        (isSheafStruct X) L))
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm X.toRingedSpace.presheaf
      (isSheafStruct X) L)

omit [IsInvertibleModule X L] in
/-- The inclusion of the two twist algebras of [Stacks, Tag 0EKG] is the inclusion of the
nonnegative truncation of the integral one. -/
theorem nonnegToIntegerTwistUnitalHom_eq_inclusion {A : Type u} {σ : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    nonnegToIntegerTwistUnitalHom 𝒜 =
      Stacks.AlgebraicGeometry.NonnegTruncation.inclusion (integerTwistAlgebra 𝒜) := by
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
  rcases n with k | k
  · rfl
  · exact (isZero_nonnegTwistingSheaf 𝒜 (Int.negSucc_lt_zero k)).eq_of_src _ _

omit [IsInvertibleModule X L] in
/-- The inclusion of the two twist algebras, as algebra sheaves, is the realised inclusion of the
nonnegative truncation. -/
theorem nonnegToIntegerTwistAlgebraSheafHom_eq_inclusion {A : Type u} {σ : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    nonnegToIntegerTwistAlgebraSheafHom 𝒜 =
      gradedAlgebraSheafMap (AlgebraicGeometry.Proj 𝒜)
        (Stacks.AlgebraicGeometry.NonnegTruncation.inclusion (integerTwistAlgebra 𝒜))
        (Stacks.AlgebraicGeometry.NonnegTruncation.isCommutative_nonnegTruncation
          (integerTwistAlgebra 𝒜) (heq_twistMul_comm 𝒜)) (heq_twistMul_comm 𝒜) :=
  congrArg (fun (f : SheafOfModules.GradedAlgebra.UnitalHom (nonnegTwistAlgebra 𝒜)
      (integerTwistAlgebra 𝒜)) => gradedAlgebraSheafMap (AlgebraicGeometry.Proj 𝒜) f
    (heq_nonnegTwistMul_comm 𝒜) (heq_twistMul_comm 𝒜))
    (nonnegToIntegerTwistUnitalHom_eq_inclusion 𝒜)

/-- **The algebra comparisons are compatible with the inclusions**: the pullback along `r` of
`⨁_{m ≥ 0} 𝒪(m) ⊆ ⨁_{m ∈ ℤ} 𝒪(m)`, read through the two comparisons with the Laurent algebras,
is `⨁_{m ≥ 0} 𝓛^{⊗ m} ⊆ ⨁_{m ∈ ℤ} 𝓛^{⊗ m}`. -/
theorem algebraPullback_map_comp_algebraPullbackTwistIsoLaurent_hom :
    (algebraPullback (projHomOfIsAmple L hL)).map
        (nonnegToIntegerTwistAlgebraSheafHom (grading L)) ≫
        (algebraPullbackTwistIsoLaurent L hL).hom =
      (algebraPullbackNonnegTwistIsoNonnegLaurent L hL).hom ≫
        nonnegLaurentToLaurentAlgebraSheafHom L := by
  refine (congrArg (fun a => (algebraPullback (projHomOfIsAmple L hL)).map a ≫
      (algebraPullbackTwistIsoLaurent L hL).hom)
      (nonnegToIntegerTwistAlgebraSheafHom_eq_inclusion (grading L))).trans ?_
  unfold algebraPullbackNonnegTwistIsoNonnegLaurent pbNonnegTwistAlgebraSheafIsoNonnegLaurent
    algebraPullbackTwistIsoLaurent pbTwistAlgebraSheafIsoLaurent
    nonnegLaurentToLaurentAlgebraSheafHom
  exact Stacks.GradedRealizationPullback.algebraPullback_map_inclusion_comp_hom _ _ _ _ _ _
    (hψ := isIso_gradedTwistUnitalComparison_app L hL)

/-! ### The top arrow -/

/-- **The top arrow `Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m}) ⟶ Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m})` of the diagram of
[Stacks, Tag 0EKI]**, the morphism of relative spectra over `P` induced by the inclusion of
algebras `nonnegLaurentToLaurentAlgebraSheafHom`. -/
def laurentToNonnegLaurentRelativeSpec :
    laurentRelativeSpecOver L hL ⟶ nonnegLaurentRelativeSpecOver L hL :=
  haveI := isQuasicoherent_laurentAlgebraSheaf L hL
  haveI := isQuasicoherent_nonnegLaurentAlgebraSheaf L hL
  relativeSpecMapOfAlgebraHom (nonnegLaurentAlgebraSheaf L) (laurentAlgebraSheaf L)
    (nonnegLaurentToLaurentAlgebraSheafHom L)

/-- The base change along `r` of the top arrow of [Stacks, Tag 0EKG], read through the
identifications of [Stacks, Tag 01LX] and the algebra comparisons, is the top arrow of
[Stacks, Tag 0EKI]. Checked on direct-image algebras over `P`, after cancelling the base-change
isomorphism of algebras. -/
theorem relativeSpecOverIso_inv_comp_baseChange :
    haveI := isQuasicoherent_laurentAlgebraSheaf L hL
    haveI := isQuasicoherent_nonnegLaurentAlgebraSheaf L hL
    (relativeSpecOverIso (algebraPullbackTwistIsoLaurent L hL)).inv ≫
        (relativeSpecBaseChangeIso (projHomOfIsAmple L hL)
          (integerTwistAlgebraSheaf (grading L))).inv ≫
        (Over.pullback (projHomOfIsAmple L hL)).map
          (puncturedToConeRelativeSpecTwistAlgebra (grading L)) =
      relativeSpecMapOfAlgebraHom (nonnegLaurentAlgebraSheaf L) (laurentAlgebraSheaf L)
          (nonnegLaurentToLaurentAlgebraSheafHom L) ≫
        (relativeSpecOverIso (algebraPullbackNonnegTwistIsoNonnegLaurent L hL)).inv ≫
        (relativeSpecBaseChangeIso (projHomOfIsAmple L hL)
          (nonnegTwistAlgebraSheaf (grading L))).inv := by
  have := isQuasicoherent_laurentAlgebraSheaf L hL
  have := isQuasicoherent_nonnegLaurentAlgebraSheaf L hL
  have : IsAffineHom (Over.mk (relativeSpecToBase (nonnegTwistAlgebraSheaf (grading L)))).hom :=
    isAffineHom_relativeSpecToBase _
  have : IsAffineHom ((Over.pullback (projHomOfIsAmple L hL)).obj
      (Over.mk (relativeSpecToBase (nonnegTwistAlgebraSheaf (grading L))))).hom :=
    isAffineHom_overPullback_hom _ _
  have hiso := isIso_baseChangeAlgebraHom (projHomOfIsAmple L hL)
    (Over.mk (relativeSpecToBase (nonnegTwistAlgebraSheaf (grading L))))
  have hepi : Epi (baseChangeAlgebraHom (projHomOfIsAmple L hL)
      (Over.mk (relativeSpecToBase (nonnegTwistAlgebraSheaf (grading L))))) :=
    @IsIso.epi_of_iso _ _ _ _ _ hiso
  refine eq_of_pushforwardAlgebraMap_eq ?_
  refine hepi.left_cancellation _ _ ?_
  rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_comp, pushforwardAlgebraMap_comp,
    pushforwardAlgebraMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (baseChangeAlgebraHom _ _), ← baseChangeAlgebraHom_naturality,
    puncturedToConeRelativeSpecTwistAlgebra, pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom,
    pushforwardAlgebraMap_relativeSpecBaseChangeIso_inv,
    pushforwardAlgebraMap_relativeSpecBaseChangeIso_inv,
    pushforwardAlgebraMap_relativeSpecOverIso_inv, pushforwardAlgebraMap_relativeSpecOverIso_inv,
    pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (baseChangeAlgebraHom _ _) (pullbackAlgebraIso _ _).hom,
    baseChangeAlgebraHom_comp_pullbackAlgebraIso_hom,
    ← Category.assoc (baseChangeAlgebraHom _ _) (pullbackAlgebraIso _ _).hom,
    baseChangeAlgebraHom_comp_pullbackAlgebraIso_hom, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc (algebraPullback _) (pushforwardAlgebraIso _).inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  refine congrArg (_ ≫ ·) ?_
  rw [← Category.assoc, algebraPullback_map_comp_algebraPullbackTwistIsoLaurent_hom,
    Category.assoc]

/-- **The top arrows agree after base change to `P`**, for any ample invertible module: the base
change of the open immersion `U ⟶ L` along `r` is the morphism induced by the inclusion of Laurent
algebras, under `puncturedConeBaseChangeIsoLaurent` and `coneBaseChangeIsoNonnegLaurent`. -/
theorem puncturedConeBaseChangeIsoLaurent_inv_comp :
    (puncturedConeBaseChangeIsoLaurent L hL).inv ≫
        (Over.pullback (projHomOfIsAmple L hL)).map (openUInLOver (grading L)) =
      laurentToNonnegLaurentRelativeSpec L hL ≫ (coneBaseChangeIsoNonnegLaurent L hL).inv := by
  have := isQuasicoherent_laurentAlgebraSheaf L hL
  have := isQuasicoherent_nonnegLaurentAlgebraSheaf L hL
  have h1 := congrArg (Over.pullback (projHomOfIsAmple L hL)).map
    (puncturedToConeRelativeSpecTwistAlgebra_comp (grading L))
  have aux := relativeSpecOverIso_inv_comp_baseChange L hL
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)
  refine (congrArg (_ ≫ _ ≫ ·) ((Functor.map_comp _ _ _).symm.trans
    (h1.symm.trans (Functor.map_comp _ _ _)))).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) aux).trans ?_
  exact Category.assoc _ _ _

/-! ### The diagram clause over `P` -/

variable {R : CommRingCat.{u}} (f : X ⟶ Spec R) [IsProper f]

/-- The open immersion `U ⟶ L` of the punctured cone in the cone, as a morphism over `P` through
the identification `P = Proj A`. -/
def openUInLOverOfIsProper :
    Over.mk ((openUInL (grading L)).ι ≫ pi (grading L) ≫ (projIsoOfIsProper L hL f).inv) ⟶
      Over.mk (pi (grading L) ≫ (projIsoOfIsProper L hL f).inv) :=
  Over.homMk (openUInL (grading L)).ι rfl

/-- **The top square of [Stacks, Tag 0EKI]**: for `P` proper, the open immersion `U ⟶ L`, read
over `P` through `P = Proj A`, is the morphism `Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m}) ⟶
Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m})` induced by the inclusion of algebras, under the identifications
`puncturedConeIsoLaurentOfIsProper` and `coneIsoNonnegLaurentOfIsProper`. -/
theorem puncturedConeIsoLaurentOfIsProper_inv_comp :
    (puncturedConeIsoLaurentOfIsProper L hL f).inv ≫ openUInLOverOfIsProper L hL f =
      laurentToNonnegLaurentRelativeSpec L hL ≫ (coneIsoNonnegLaurentOfIsProper L hL f).inv := by
  have := isIso_projHomOfIsAmple_of_isProper L hL f
  have hnat := Stacks.AlgebraicGeometry.OverBaseChange.overPullbackIsoOfIsIso_hom_comp
    ((openUInL (grading L)).ι ≫ pi (grading L)) (pi (grading L)) (projHomOfIsAmple L hL)
    (openUInLOver (grading L))
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hnat).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (puncturedConeBaseChangeIsoLaurent_inv_comp L hL)).trans ?_
  exact Category.assoc _ _ _

/-- **The left square of the diagram of [Stacks, Tag 0EKI] commutes**: the top arrow followed by
`σ : L ⟶ X` is the identification of `Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m})` with `U` followed by `U ⊆ X`. -/
theorem laurentToNonnegLaurentRelativeSpec_left_comp_toSpecA :
    (laurentToNonnegLaurentRelativeSpec L hL).left ≫
        (coneIsoNonnegLaurentOfIsProper L hL f).inv.left ≫ toSpecA (grading L) =
      ((puncturedConeIsoLaurentOfIsProper L hL f).inv.left ≫
        (toSpecA (grading L) ∣_ Stacks.AlgebraicGeometry.ProjAndSpec.openU (grading L))) ≫
        (Stacks.AlgebraicGeometry.ProjAndSpec.openU (grading L)).ι := by
  have h := congrArg (fun φ => φ.left) (puncturedConeIsoLaurentOfIsProper_inv_comp L hL f)
  simp only [Over.comp_left] at h
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ toSpecA (grading L)) h.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (openUInL_ι_comp_toSpecA (grading L))).trans ?_
  exact (Category.assoc _ _ _).symm

/-- **The right square of the diagram of [Stacks, Tag 0EKI] commutes**: the projection of
`Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m})` to `P = Proj A` followed by `Proj A ⟶ Z` is `σ` followed by
`X ⟶ Z`. -/
theorem nonnegLaurentRelativeSpecOver_hom_comp_toSpecZero :
    (nonnegLaurentRelativeSpecOver L hL).hom ≫ (projIsoOfIsProper L hL f).hom ≫
        Proj.toSpecZero (grading L) =
      (coneIsoNonnegLaurentOfIsProper L hL f).inv.left ≫ toSpecA (grading L) ≫
        Stacks.AlgebraicGeometry.ProjAndSpec.xToZ (grading L) := by
  have hw := Over.w (coneIsoNonnegLaurentOfIsProper L hL f).inv
  refine (congrArg (· ≫ _) hw.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (pi (grading L) ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Proj.toSpecZero (grading L)) (Iso.inv_hom_id _)).trans
      (Category.id_comp _)))).trans ?_
  exact pi_comp_toSpecZero (grading L)

/-- The left component of an isomorphism of schemes over `X` is an isomorphism. -/
private theorem isIso_left_of_isIso {Y Z : Over X} (e : Y ⟶ Z) [IsIso e] : IsIso e.left :=
  inferInstanceAs (IsIso ((Over.forget X).map e))

include f in
/-- The top arrow of the diagram of [Stacks, Tag 0EKI] is an open immersion: it is the open
immersion `U ⟶ L` between two isomorphisms. -/
theorem isOpenImmersion_laurentToNonnegLaurentRelativeSpec_left :
    IsOpenImmersion (laurentToNonnegLaurentRelativeSpec L hL).left := by
  have h : laurentToNonnegLaurentRelativeSpec L hL =
      ((puncturedConeIsoLaurentOfIsProper L hL f).inv ≫ openUInLOverOfIsProper L hL f) ≫
        (coneIsoNonnegLaurentOfIsProper L hL f).hom :=
    (Iso.comp_inv_eq _).mp (puncturedConeIsoLaurentOfIsProper_inv_comp L hL f).symm
  rw [h, Over.comp_left, Over.comp_left]
  have := isIso_left_of_isIso (puncturedConeIsoLaurentOfIsProper L hL f).inv
  have := isIso_left_of_isIso (coneIsoNonnegLaurentOfIsProper L hL f).hom
  have : IsOpenImmersion (puncturedConeIsoLaurentOfIsProper L hL f).inv.left :=
    IsOpenImmersion.of_isIso _
  have : IsOpenImmersion (coneIsoNonnegLaurentOfIsProper L hL f).hom.left :=
    IsOpenImmersion.of_isIso _
  have : IsOpenImmersion (openUInLOverOfIsProper L hL f).left :=
    inferInstanceAs (IsOpenImmersion (openUInL (grading L)).ι)
  infer_instance

/-- **Stacks Project, Tag 0EKI: for `P` proper over `R` and `𝓛` ample, diagram 0EKG is the
diagram of `Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m}) ⟶ Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m}) ⟶ P`, arrow by arrow.**

Let `A = Γ_*(P, 𝓛)`, `r : P ⟶ Proj A` the canonical morphism, `π : L ⟶ Proj A` the cone of
[Stacks, Tag 0EKG] with its punctured cone `U ⊆ L`, `σ : L ⟶ X = Spec A`, and `ρ`, `Φ_L`, `Φ_U`
the identifications `P ≅ Proj A`, `L ≅ Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m})`, `U ≅ Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m})`
(the last two over `P`). Then:

1. `r` is an isomorphism (`P = Proj A`);
2. **the top arrow**: under `Φ_U` and `Φ_L` the open immersion `U ⟶ L` is the morphism
   `Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m}) ⟶ Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m})` induced by the inclusion of algebras
   `⨁_{m ≥ 0} 𝓛^{⊗ m} ⊆ ⨁_{m ∈ ℤ} 𝓛^{⊗ m}`, as morphisms over `P`;
3. **the projections**: under `Φ_L` and `ρ` the cone projection `π` is the structure morphism of
   `Spec_P(⨁_{m ≥ 0} 𝓛^{⊗ m})`, and under `Φ_U` and `ρ` its restriction `π|_U` is that of
   `Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m})`;
4. the top arrow is a morphism over `P` and an open immersion;
5. **the left vertical identification** `Spec_P(⨁_{m ∈ ℤ} 𝓛^{⊗ m}) ≅ U ⊆ X` (the `=` of the
   diagram) is `Φ_U⁻¹` followed by `σ|_U`, an isomorphism;
6. **the left square** of the new diagram commutes: the top arrow followed by `σ` (read through
   `Φ_L`) is the identification with `U` followed by `U ⊆ X`;
7. **the right square** of the new diagram commutes: the projection to `P` followed by
   `P = Proj A ⟶ Z = Spec A₀` is `σ` (read through `Φ_L`) followed by `X ⟶ Z`. -/
@[stacks 0EKI "the whole statement: P = Proj A and diagram 0EKG becomes, arrow by arrow, the \
diagram of the relative spectra over P of the Laurent algebras of the ample module: the open \
immersion U → L is the morphism induced by the inclusion of algebras, the projections to P are \
the structure morphisms, and the left and right squares commute",
  ega "II 8.7.4" "(ii), special case",
  ega "II 8.8.3" "special case"]
theorem projAndSpecDiagram_eq_laurentDiagram_of_isProper :
    IsIso (projHomOfIsAmple L hL) ∧
    (puncturedConeIsoLaurentOfIsProper L hL f).inv ≫ openUInLOverOfIsProper L hL f =
      laurentToNonnegLaurentRelativeSpec L hL ≫ (coneIsoNonnegLaurentOfIsProper L hL f).inv ∧
    (coneIsoNonnegLaurentOfIsProper L hL f).hom.left ≫ (nonnegLaurentRelativeSpecOver L hL).hom =
      pi (grading L) ≫ (projIsoOfIsProper L hL f).inv ∧
    (puncturedConeIsoLaurentOfIsProper L hL f).hom.left ≫ (laurentRelativeSpecOver L hL).hom =
      (openUInL (grading L)).ι ≫ pi (grading L) ≫ (projIsoOfIsProper L hL f).inv ∧
    (laurentToNonnegLaurentRelativeSpec L hL).left ≫ (nonnegLaurentRelativeSpecOver L hL).hom =
      (laurentRelativeSpecOver L hL).hom ∧
    IsOpenImmersion (laurentToNonnegLaurentRelativeSpec L hL).left ∧
    IsIso ((puncturedConeIsoLaurentOfIsProper L hL f).inv.left ≫
      (toSpecA (grading L) ∣_ Stacks.AlgebraicGeometry.ProjAndSpec.openU (grading L))) ∧
    (laurentToNonnegLaurentRelativeSpec L hL).left ≫
        (coneIsoNonnegLaurentOfIsProper L hL f).inv.left ≫ toSpecA (grading L) =
      ((puncturedConeIsoLaurentOfIsProper L hL f).inv.left ≫
        (toSpecA (grading L) ∣_ Stacks.AlgebraicGeometry.ProjAndSpec.openU (grading L))) ≫
        (Stacks.AlgebraicGeometry.ProjAndSpec.openU (grading L)).ι ∧
    (nonnegLaurentRelativeSpecOver L hL).hom ≫ (projIsoOfIsProper L hL f).hom ≫
        Proj.toSpecZero (grading L) =
      (coneIsoNonnegLaurentOfIsProper L hL f).inv.left ≫ toSpecA (grading L) ≫
        Stacks.AlgebraicGeometry.ProjAndSpec.xToZ (grading L) := by
  have := isIso_left_of_isIso (puncturedConeIsoLaurentOfIsProper L hL f).inv
  exact ⟨isIso_projHomOfIsAmple_of_isProper L hL f,
    puncturedConeIsoLaurentOfIsProper_inv_comp L hL f,
    Over.w (coneIsoNonnegLaurentOfIsProper L hL f).hom,
    Over.w (puncturedConeIsoLaurentOfIsProper L hL f).hom,
    Over.w (laurentToNonnegLaurentRelativeSpec L hL),
    isOpenImmersion_laurentToNonnegLaurentRelativeSpec_left L hL f,
    IsIso.comp_isIso' inferInstance (isIso_toSpecA_restrict (grading L)),
    laurentToNonnegLaurentRelativeSpec_left_comp_toSpecA L hL f,
    nonnegLaurentRelativeSpecOver_hom_comp_toSpecZero L hL f⟩

end Monoidal

end Stacks.SectionRingProjIso

end
