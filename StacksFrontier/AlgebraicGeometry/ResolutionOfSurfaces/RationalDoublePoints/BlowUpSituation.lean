module

public import StacksFrontier.AlgebraicGeometry.Models.Normalization
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpGorenstein
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowupStepSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpClosedPointDimension
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormalityExtra

/-!
# The rational double point situation at a closed point of the blowup

Let `S` be a Situation [Stacks, Tag 0BGC] with ring `A`, and let `x` be a closed point of the
blowup `X` of `Spec(A)` in the maximal ideal. Granted that the completion `A^` and the local ring
`𝒪_{X, x}` define rational singularities, that `𝒪_{X, x}` is not regular, and that a field maps
onto its residue field and three elements generate its maximal ideal, the local ring `𝒪_{X, x}` is
the ring of a Situation 0BGC. This is the field `AlgebraicGeometry.PointBlowupStep.next_prop` of
a rule for choosing the centres of a sequence of blowups at closed points, for the property
`AlgebraicGeometry.IsRationalDoublePointAt`.

## Main definitions

* `AlgebraicGeometry.RationalDoublePointSituation.blowUpSituation`: the Situation 0BGC at a
  closed point of the blowup.

## Main results

* `AlgebraicGeometry.vanishingIdeal_closedPoint_eq_maximalIdealSheaf`: the vanishing ideal sheaf
  of the closed point of the spectrum of a local ring is the ideal sheaf of the maximal ideal.
* `AlgebraicGeometry.RationalDoublePointSituation.isNormalDomain_stalk_blowUp`,
  `AlgebraicGeometry.RationalDoublePointSituation.isNagataRing_stalk_blowUp` and
  `AlgebraicGeometry.RationalDoublePointSituation.ringKrullDim_stalk_blowUp_eq_two`: the local
  ring at a point of the blowup is a normal domain and a Nagata ring, of dimension two at a closed
  point.
* `AlgebraicGeometry.RationalDoublePointSituation.isRationalDoublePointAt_blowUp`: the property
  `AlgebraicGeometry.IsRationalDoublePointAt` at a closed point of the blowup.
* `AlgebraicGeometry.RationalDoublePointSituation.centre_initialStage`: the centre of the initial
  stage of a sequence of blowups is the maximal ideal sheaf.
* `AlgebraicGeometry.RationalDoublePointSituation.isRationalDoublePointAt_blowUp_initialStage`:
  the property `AlgebraicGeometry.IsRationalDoublePointAt` at the closed points of the blowup of
  the initial stage.

## References

* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- **Blowing up the closed point of `Spec A` is blowing up the maximal ideal.** The vanishing
ideal sheaf of the closed point of the spectrum of a local ring is the ideal sheaf cut out by the
maximal ideal. -/
public theorem vanishingIdeal_closedPoint_eq_maximalIdealSheaf (A : Type u) [CommRing A]
    [IsLocalRing A] (hclosed : IsClosed ({closedPoint A} : Set (Spec (.of A)))) :
    Scheme.IdealSheafData.vanishingIdeal
        (⟨{closedPoint A}, hclosed⟩ : TopologicalSpace.Closeds (Spec (.of A))) =
      maximalIdealSheaf A := by
  have hU : IsAffineOpen (⊤ : (Spec (.of A)).Opens) := isAffineOpen_top _
  have hUimm : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hfs : hU.fromSpec = Spec.map (Scheme.ΓSpecIso (.of A)).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (.of A)).inv.hom :=
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.surjective
  let p : PrimeSpectrum ↑Γ(Spec (.of A), ⊤) := hU.primeIdealOf ⟨closedPoint A, trivial⟩
  have hfp : hU.fromSpec p = closedPoint A :=
    hU.fromSpec_primeIdealOf ⟨closedPoint A, trivial⟩
  have hcomap : p.asIdeal.comap (Scheme.ΓSpecIso (.of A)).inv.hom = maximalIdeal A := by
    have h : (Spec.map (Scheme.ΓSpecIso (.of A)).inv) p = closedPoint A := hfs ▸ hfp
    have h2 : PrimeSpectrum.comap (Scheme.ΓSpecIso (.of A)).inv.hom p = closedPoint A :=
      (Spec.map_apply (Scheme.ΓSpecIso (.of A)).inv p).symm.trans h
    exact (PrimeSpectrum.comap_asIdeal _ p).symm.trans (congrArg PrimeSpectrum.asIdeal h2)
  have hp : p.asIdeal = Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (maximalIdeal A) := by
    rw [← hcomap, Ideal.map_comap_of_surjective _ hsurj]
  have hpre : (hU.fromSpec.base ⁻¹'
      ((⟨{closedPoint A}, hclosed⟩ : TopologicalSpace.Closeds (Spec (.of A))) :
        Set (Spec (.of A))) : Set (PrimeSpectrum ↑Γ(Spec (.of A), ⊤))) = {p} := by
    ext z
    change hU.fromSpec.base z = closedPoint A ↔ z = p
    exact ⟨fun hz => hU.fromSpec.isOpenEmbedding.injective (hz.trans hfp.symm),
      fun hz => hz ▸ hfp⟩
  have hrhs : (Scheme.IdealSheafData.vanishingIdeal
        (⟨{closedPoint A}, hclosed⟩ :
          TopologicalSpace.Closeds (Spec (.of A)))).ideal ⟨⊤, hU⟩ =
      Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (maximalIdeal A) :=
    ((Scheme.IdealSheafData.vanishingIdeal_ideal _ ⟨⊤, hU⟩).trans
      ((congrArg PrimeSpectrum.vanishingIdeal hpre).trans
        (PrimeSpectrum.vanishingIdeal_singleton p))).trans hp
  have hlhs : (maximalIdealSheaf A).ideal ⟨⊤, hU⟩ =
      Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (maximalIdeal A) := by
    simp only [maximalIdealSheaf, Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl,
      CategoryTheory.op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  exact Scheme.IdealSheafData.ext_of_isAffine (hrhs.trans hlhs.symm)

namespace RationalDoublePointSituation

/-! ### The parts of the situation which need no hypothesis -/

/-- **Stacks Project, Tag 0B4Z at a rational double point.** The blowup of the spectrum of the
ring of a Situation [Stacks, Tag 0BGC] in its maximal ideal is a normal scheme. -/
public theorem isNormal_blowUp (S : RationalDoublePointSituation.{u}) :
    IsNormal (blowUp (maximalIdealSheaf S.A)) :=
  isNormal_blowUp_maximalIdeal_of_forall_isIntegrallyClosed_pow S.A fun n =>
    isIntegrallyClosed_maximalIdeal_pow_of_definesRationalSingularity S.A S.nagata
      S.dimension_two S.definesRationalSingularity n

/-- **The local ring at a point of the blowup of a rational double point is a normal domain.** -/
public theorem isNormalDomain_stalk_blowUp (S : RationalDoublePointSituation.{u})
    (x : blowUp (maximalIdealSheaf S.A)) :
    IsNormalDomain ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
  have h := (Stacks.Models.isNormalRing_stalk S.isNormal_blowUp x).of_isLocalRing
  ⟨h.1, h.2⟩

/-- **The local ring at a point of the blowup of a rational double point is a Nagata ring.** -/
public theorem isNagataRing_stalk_blowUp (S : RationalDoublePointSituation.{u})
    (x : blowUp (maximalIdealSheaf S.A)) :
    IsNagataRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
  Stacks.AlgebraicGeometry.NormalizationQuotient.stalk_isNagataRing _
    (isNagataScheme_of_isNagataRing (blowUpToBase (maximalIdealSheaf S.A)) S.nagata) x

/-- **The local ring at a closed point of the blowup of a rational double point has dimension
two.** -/
public theorem ringKrullDim_stalk_blowUp_eq_two (S : RationalDoublePointSituation.{u})
    (x : blowUp (maximalIdealSheaf S.A))
    (hx : IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A)))) :
    ringKrullDim ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) = 2 :=
  ringKrullDim_stalk_blowUp_maximalIdeal_eq_two_of_isClosed S.A S.dimension_two x hx

/-! ### The part of the situation which clause (1) of Tag 0BG7 supplies -/

/-- **Stacks Project, Tag 0BG7, clause (2) at a rational double point.** The completion of the
local ring at a closed point of the blowup of `Spec(A)` in the maximal ideal is a normal domain,
granted that the completion `A^` defines a rational singularity, which is clause (1) of
[Stacks, Tag 0BG7]. -/
public theorem isNormalDomain_adicCompletion_stalk_blowUp (S : RationalDoublePointSituation.{u})
    (hratc :
      letI : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) :=
        S.completion_normalDomain
      DefinesRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
    (x : blowUp (maximalIdealSheaf S.A))
    (hx : IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A)))) :
    IsNormalDomain (AdicCompletion
      (IsLocalRing.maximalIdeal ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))
      ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) := by
  have : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) :=
    AdicCompletion.isNoetherianRing (IsLocalRing.maximalIdeal S.A)
  have : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) :=
    S.completion_normalDomain
  exact isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal S.A
    (isNormal_blowUp_maximalIdeal_of_forall_isIntegrallyClosed_pow
      (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) fun n =>
        isIntegrallyClosed_maximalIdeal_pow_of_definesRationalSingularity
          (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)
          IsNagataRing.of_isPrecomplete_maximalIdeal
          ((_root_.ringKrullDim_adicCompletion_maximalIdeal (A := S.A)).symm.trans
            S.dimension_two) hratc n) x hx

/-! ### The situation at a closed point of the blowup -/

/-- **Situation [Stacks, Tag 0BGC] at a closed point of the blowup of a rational double point.**
Let `S` be a Situation 0BGC and let `x` be a closed point of the blowup of `Spec(A)` in the
maximal ideal. Then the local ring `𝒪_{X, x}` is the ring of a Situation 0BGC, granted

* `hratc`, that the completion `A^` defines a rational singularity, which is clause (1) of
  [Stacks, Tag 0BG7];
* `hrat`, that `𝒪_{X, x}` defines a rational singularity, which is [Stacks, Tag 0BG0] in its
  local-ring form;
* a field `K` mapping onto the residue field at `x`, and three generators `y` of the maximal
  ideal there;
* `hsing`, that `𝒪_{X, x}` is not regular. -/
public def blowUpSituation (S : RationalDoublePointSituation.{u})
    (hratc :
      letI : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) :=
        S.completion_normalDomain
      DefinesRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
    (x : blowUp (maximalIdealSheaf S.A))
    (hx : IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A))))
    (hrat :
      letI : IsNormalDomain ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
        S.isNormalDomain_stalk_blowUp x
      DefinesRationalSingularity ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))
    (K : Type v) [Field K] (f : K →+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)
    (hf : Function.Surjective ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal
        ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))).comp f))
    (y : Fin 3 → (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)
    (hy : Ideal.span (Set.range y) =
      IsLocalRing.maximalIdeal ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))
    (hsing : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) :
    RationalDoublePointSituation.{u} where
  A := (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x
  normalDomain := S.isNormalDomain_stalk_blowUp x
  nagata := S.isNagataRing_stalk_blowUp x
  dimension_two := S.ringKrullDim_stalk_blowUp_eq_two x hx
  definesRationalSingularity := hrat
  completion_normalDomain := S.isNormalDomain_adicCompletion_stalk_blowUp hratc x hx
  gorenstein := S.isGorensteinLocalRing_stalk_blowUp hratc x hx
    (S.ringKrullDim_stalk_blowUp_eq_two x hx) K f y hf hy
  not_isRegularLocalRing := hsing

/-- The ring of `blowUpSituation` is the local ring at the point. -/
@[simp]
public theorem blowUpSituation_A (S : RationalDoublePointSituation.{u}) {hratc x hx hrat}
    {K : Type v} [Field K] {f hf y hy hsing} :
    (S.blowUpSituation hratc x hx hrat K f hf y hy hsing).A =
      (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x :=
  rfl

/-- **`AlgebraicGeometry.PointBlowupStep.next_prop` at a closed point of the blowup of a rational
double point.** The property a rule carries along a sequence of blowups of a rational double
point holds at every closed point of the blowup of `Spec(A)` in the maximal ideal at which the
data of `AlgebraicGeometry.RationalDoublePointSituation.blowUpSituation` is available: the local
ring there is the ring of a Situation [Stacks, Tag 0BGC]. The element `z` of the local ring is
arbitrary. -/
public theorem isRationalDoublePointAt_blowUp (S : RationalDoublePointSituation.{u})
    (hratc :
      letI : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) :=
        S.completion_normalDomain
      DefinesRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
    (x : blowUp (maximalIdealSheaf S.A))
    (hx : IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A))))
    (hrat :
      letI : IsNormalDomain ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
        S.isNormalDomain_stalk_blowUp x
      DefinesRationalSingularity ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))
    (K : Type u) [Field K] (f : K →+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)
    (hf : Function.Surjective ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal
        ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))).comp f))
    (y : Fin 3 → (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)
    (hy : Ideal.span (Set.range y) =
      IsLocalRing.maximalIdeal ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))
    (hsing : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))
    (z : (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :
    IsRationalDoublePointAt (blowUp (maximalIdealSheaf S.A)) x z :=
  ⟨S.blowUpSituation hratc x hx hrat K f hf y hy hsing, ⟨RingEquiv.refl _⟩⟩

/-! ### The centre of a stage of a sequence of blowups -/

/-- **The centre of the initial stage is the maximal ideal sheaf.** The initial stage of a
sequence of blowups of a rational double point blows up the vanishing ideal of the closed point of
`Spec(A)`, and that is the ideal sheaf cut out by the maximal ideal. -/
public theorem centre_initialStage (S : RationalDoublePointSituation.{u})
    (e : S.base.presheaf.stalk S.closedPoint) :
    (S.initialStage e).centre = maximalIdealSheaf S.A :=
  vanishingIdeal_closedPoint_eq_maximalIdealSheaf S.A _

/-- **`AlgebraicGeometry.PointBlowupStep.next_prop` at the initial stage.** At every closed point
of the blowup of the initial stage of a sequence of blowups of a rational double point at which
the per-point data `hdata` is available, the property the rule carries holds. -/
public theorem isRationalDoublePointAt_blowUp_initialStage (S : RationalDoublePointSituation.{u})
    (e : S.base.presheaf.stalk S.closedPoint)
    (hratc :
      letI : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) :=
        S.completion_normalDomain
      DefinesRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
    (hdata : ∀ x : blowUp (maximalIdealSheaf S.A),
      IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A))) →
        letI : IsNormalDomain ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
          S.isNormalDomain_stalk_blowUp x
        DefinesRationalSingularity ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∧
          (∃ (K : Type u) (_ : Field K)
              (f : K →+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x),
              Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
                ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))).comp f)) ∧
          (∃ y : Fin 3 → (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x,
              Ideal.span (Set.range y) = IsLocalRing.maximalIdeal
                ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) ∧
          ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) :
    ∀ (q : blowUp (S.initialStage e).centre)
      (_ : IsClosed ({q} : Set (blowUp (S.initialStage e).centre)))
      (z : (blowUp (S.initialStage e).centre).presheaf.stalk q),
      IsRationalDoublePointAt (blowUp (S.initialStage e).centre) q z := by
  rw [S.centre_initialStage e]
  intro q hq z
  obtain ⟨hrat, ⟨K, _, f, hf⟩, ⟨y, hy⟩, hsing⟩ := hdata q hq
  exact S.isRationalDoublePointAt_blowUp hratc q hq hrat K f hf y hy hsing z

end RationalDoublePointSituation

end AlgebraicGeometry

end
