module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties

/-!
# The Noetherian valuative criterion for separatedness of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is quasi-separated
and locally of finite type, with `Y` locally Noetherian. Separatedness of `f` is then detected
by uniqueness of dotted arrows in valuative diagrams (Stacks 0H1V), and it is enough to test
discrete valuation rings, and even only those valuative diagrams whose generic arrow picks out
a point of codimension zero of the source.

## Main definitions

* `AlgebraicGeometry.Space.ValuativeSquare.genericFieldPoint` and
  `AlgebraicGeometry.Space.ValuativeSquare.genericPoint`: the point of the source of a
  valuative square picked out by its generic arrow, as a field-valued point and as a point.
* `AlgebraicGeometry.Space.ValuativeCriterion.DiscreteUniqueness`: at most one dotted arrow in
  every valuative diagram whose valuation ring is a discrete valuation ring; condition (3).
* `AlgebraicGeometry.Space.ValuativeCriterion.CodimensionZeroUniqueness`: the same, restricted
  further to the diagrams whose generic arrow picks out a point of codimension zero;
  condition (4).
* `AlgebraicGeometry.GenericDiscreteValuativeCriterion`: condition (4) of Stacks 0208 for a
  morphism of schemes, which is the one input of Stacks 0H1W the library does not yet have.

## Main results

* `AlgebraicGeometry.Space.isSeparated_iff_valuativeCriterion_uniqueness`: conditions (1) and
  (2) are equivalent for a quasi-separated morphism; this needs no extra hypothesis.
* `AlgebraicGeometry.Space.discreteUniqueness_of_uniqueness` and
  `AlgebraicGeometry.Space.codimensionZeroUniqueness_of_discreteUniqueness`: conditions (2)
  implies (3) implies (4).
* `AlgebraicGeometry.Space.isSeparated_of_codimensionZeroUniqueness`: condition (4) implies
  condition (1), taking the (4) implies (1) direction of Stacks 0208 for morphisms of schemes as
  a hypothesis.

The equivalence of all four conditions, Stacks 0H1W, is
`AlgebraicGeometry.Space.isSeparated_tfae_of_isLocallyOfFiniteType` in
`StacksFrontier/AlgebraicGeometry/Spaces/NoetherianValuativeSeparatednessTFAE.lean`.

## Implementation notes

The generic arrow of a valuative square is a morphism out of the presheaf represented by the
spectrum of the fraction field, so it corresponds under `CategoryTheory.yonedaEquiv` to a
section of the source over that spectrum, which is exactly the datum of a field-valued point
`AlgebraicGeometry.Space.FieldValuedPoint`; its class is the point of the source it picks out.
"Codimension zero" is vanishing of `AlgebraicGeometry.Space.localRingDimension`, the dimension
of the local ring at the point, which is the formulation of Stacks 0BAQ used in this
directory.

Conditions (1) and (2) are equivalent by Stacks 03KU and Stacks 03KV, and (2) implies (3)
implies (4) by restriction, so the whole content is the implication from (4) to (1). The
Stacks proof of that implication runs the argument of Stacks 0207 one level up: it bases the
relative diagonal of `f` change along an étale chart `U` of `X \times_Y X`, which is a
Noetherian scheme by Stacks 04ZK, obtaining a quasi-compact monomorphism of schemes `V \to U`
locally of finite type; condition (4) for `f` then says exactly that the valuative diagrams of
`V \to U` at the generic points of `V` have dotted arrows, because an étale chart of the
diagonal maps generic points to codimension-zero points (Stacks 0BAQ). The step from there to
properness of `V \to U` is the Noetherian valuative criterion for properness, Stacks 0208
(Limits, Lemma 32.15.3), whose proof needs Chow's lemma; the library has neither Stacks 0208
nor Chow's lemma over a Noetherian base (Stacks 0200), so that implication is stated here with
Stacks 0208 as an explicit hypothesis, `AlgebraicGeometry.GenericDiscreteValuativeCriterion`
being its condition (4). Only the case of a monomorphism is assumed, which is all the proof
uses. Everything else is unconditional: the descent of the closed immersion from the chart
back to the diagonal is Stacks 02L6 and Stacks 02WZ.

## References

* [Stacks Project, Tag 0H1W](https://stacks.math.columbia.edu/tag/0H1W)
* [Stacks Project, Tag 0H1V](https://stacks.math.columbia.edu/tag/0H1V)
* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The generic arrow of a valuative square, read as a field-valued point of the source: its
field is the fraction field of the valuation ring and its section is the generic arrow under
the Yoneda correspondence. -/
noncomputable def ValuativeSquare.genericFieldPoint {f : X ⟶ Y} (q : ValuativeSquare f) :
    FieldValuedPoint B S hS X where
  carrier := q.K
  contained := q.field_mem
  toBase := Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base
  value := yonedaEquiv q.generic

/-- The point of the source of a valuative square picked out by its generic arrow. -/
noncomputable abbrev ValuativeSquare.genericPoint {f : X ⟶ Y} (q : ValuativeSquare f) :
    points B S hS X :=
  q.genericFieldPoint.class B S hS X

namespace ValuativeCriterion

/-- There is at most one dotted arrow in every valuative diagram whose valuation ring is a
discrete valuation ring. This is condition (3) of Stacks 0H1W. -/
def DiscreteUniqueness (f : X ⟶ Y) : Prop :=
  ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R → Subsingleton q.Lift

/-- There is at most one dotted arrow in every valuative diagram whose valuation ring is a
discrete valuation ring and whose generic arrow picks out a point of codimension zero of the
source. This is condition (4) of Stacks 0H1W. -/
def CodimensionZeroUniqueness (f : X ⟶ Y) : Prop :=
  ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
    localRingDimension B S hS q.genericPoint = 0 → Subsingleton q.Lift

end ValuativeCriterion

/-- **Stacks 0H1W, (2) implies (3).** Testing uniqueness of dotted arrows on all valuation
rings is stronger than testing it on the discrete ones. -/
@[stacks 0H1W "(2) implies (3)"]
theorem discreteUniqueness_of_uniqueness {f : X ⟶ Y}
    (hu : ValuativeCriterion.Uniqueness f) : ValuativeCriterion.DiscreteUniqueness f :=
  fun q _ => hu q

/-- **Stacks 0H1W, (3) implies (4).** Testing uniqueness of dotted arrows on all discrete
valuation rings is stronger than testing it only on the diagrams whose generic arrow picks out
a point of codimension zero. -/
@[stacks 0H1W "(3) implies (4)"]
theorem codimensionZeroUniqueness_of_discreteUniqueness {f : X ⟶ Y}
    (hu : ValuativeCriterion.DiscreteUniqueness f) :
    ValuativeCriterion.CodimensionZeroUniqueness f :=
  fun q hq _ => hu q hq

/-- **Stacks 0H1W, (1) implies (3).** A separated morphism of algebraic spaces has at most one
dotted arrow in every valuative diagram with a discrete valuation ring. -/
@[stacks 0H1W "(1) implies (3)"]
theorem discreteUniqueness_of_isSeparated (f : X ⟶ Y) (hf : IsSeparated B S hS f) :
    ValuativeCriterion.DiscreteUniqueness f :=
  discreteUniqueness_of_uniqueness (valuativeCriterion_uniqueness_of_isSeparated f hf)

/-- **Stacks 0H1W, (1) implies (4).** A separated morphism of algebraic spaces has at most one
dotted arrow in every valuative diagram with a discrete valuation ring whose generic arrow
picks out a point of codimension zero. -/
@[stacks 0H1W "(1) implies (4)"]
theorem codimensionZeroUniqueness_of_isSeparated (f : X ⟶ Y) (hf : IsSeparated B S hS f) :
    ValuativeCriterion.CodimensionZeroUniqueness f :=
  codimensionZeroUniqueness_of_discreteUniqueness (discreteUniqueness_of_isSeparated f hf)

/-- **Stacks 0H1W, (1) is equivalent to (2).** A quasi-separated morphism of algebraic spaces
is separated exactly when it satisfies the uniqueness part of the valuative criterion. -/
@[stacks 0H1W "(1) is equivalent to (2)"]
theorem isSeparated_iff_valuativeCriterion_uniqueness
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) :
    IsSeparated B S hS f ↔ ValuativeCriterion.Uniqueness f :=
  ⟨valuativeCriterion_uniqueness_of_isSeparated f,
    isSeparated_of_isQuasiSeparated_of_valuativeCriterion_uniqueness hX hY f hqs⟩

end AlgebraicGeometry.Space

/-! ### The missing scheme-level input -/

namespace AlgebraicGeometry

open TopologicalSpace

/-- Condition (4) of **Stacks 0208** for a morphism of schemes `p : V ⟶ U`: in every valuative
diagram whose valuation ring is a discrete valuation subring `A` of the residue field at a
generic point `η` of `V` having that residue field as its fraction field, and whose generic
arrow is the canonical morphism `Spec κ(η) ⟶ V`, there is exactly one dotted arrow. -/
def GenericDiscreteValuativeCriterion {V U : Scheme.{u}} (p : V ⟶ U) : Prop :=
  ∀ η : V, η ∈ genericPoints V → ∀ A : Subring (V.residueField η),
    IsDiscreteValuationRing A → IsFractionRing A (V.residueField η) →
      ∀ (i₂ : Spec (.of A) ⟶ U)
        (sq : CommSq (V.fromSpecResidueField η)
          (Spec.map (CommRingCat.ofHom A.subtype)) p i₂),
        Nonempty sq.LiftStruct ∧ Subsingleton sq.LiftStruct

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_NoetherianValuativeSeparatedness :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut instance for pullbacks of presheaves on the big fppf site. -/
local instance (priority := high) hasPullback_presheaf_NoetherianValuativeSeparatedness
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

open TopologicalSpace in
/-- The codimension-zero criterion for `f` produces the dotted arrows asked for by condition
(4) of Stacks 0208 in the base change of the relative diagonal of `f` along an étale chart of
`X ×_Y X`: a discrete valuation ring over that chart is a pair of morphisms to `X` which agree
over `Y` and agree at the generic point of the chart of the diagonal, and that generic point
has codimension zero in `X` because the chart is étale over `X`. -/
private theorem nonempty_liftStruct_of_codimensionZeroUniqueness
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (h : ValuativeCriterion.CodimensionZeroUniqueness f)
    {U W : BigFppfOver B S hS} (atlas : yoneda.obj U ⟶ pullback f f)
    (c : yoneda.obj W ⟶ X) (s : W ⟶ U)
    (hdiagPB : IsPullback c (yoneda.map s) (pullback.diagonal f) atlas)
    (hcEtale : IsEtale B S hS c)
    (hsMono : Mono ((BigFppfOver.toScheme B S hS).map s))
    (η : (BigFppfOver.toScheme B S hS).obj W)
    (hη : η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj W))
    (A : Subring (((BigFppfOver.toScheme B S hS).obj W).residueField η))
    [IsDiscreteValuationRing A]
    [IsFractionRing A (((BigFppfOver.toScheme B S hS).obj W).residueField η)]
    (i₂ : Spec (.of A) ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (sq : CommSq (((BigFppfOver.toScheme B S hS).obj W).fromSpecResidueField η)
      (Spec.map (CommRingCat.ofHom A.subtype)) ((BigFppfOver.toScheme B S hS).map s) i₂) :
    Nonempty sq.LiftStruct ∧ Subsingleton sq.LiftStruct := by
  classical
  have hKmem : B.Contains
      (Spec (.of (((BigFppfOver.toScheme B S hS).obj W).residueField η : Type u))) :=
    B.residueField_spec_contains W.left.property η
  have hAmem : B.Contains (Spec (.of (A : Type u))) :=
    Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A hKmem
  have hsubtype : A.subtype =
      algebraMap A (((BigFppfOver.toScheme B S hS).obj W).residueField η) := rfl
  set baseA : Spec (.of (A : Type u)) ⟶ S := i₂ ≫ B.inclusion.map U.hom with hbaseA
  set iK := ((BigFppfOver.toScheme B S hS).obj W).fromSpecResidueField η with hiKdef
  -- the two site objects of the valuative square and the morphisms out of them
  set uA : siteObject B S hS hAmem baseA ⟶ U :=
    Over.homMk (B.inclusion.preimage (X := B.obj hAmem) (Y := U.left) i₂) (by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_preimage]
      show i₂ ≫ B.inclusion.map U.hom = baseA
      rw [hbaseA]) with huAdef
  have hWbase : (BigFppfOver.toScheme B S hS).map s ≫ B.inclusion.map U.hom =
      B.inclusion.map W.hom := by
    show B.inclusion.map s.left ≫ B.inclusion.map U.hom = _
    rw [← B.inclusion.map_comp, s.w]
  set uK : siteObject B S hS hKmem
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (((BigFppfOver.toScheme B S hS).obj W).residueField η))) ≫ baseA) ⟶ W :=
    Over.homMk (B.inclusion.preimage (X := B.obj hKmem) (Y := W.left) iK) (by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_preimage]
      show iK ≫ B.inclusion.map W.hom =
        Spec.map (CommRingCat.ofHom
          (algebraMap A (((BigFppfOver.toScheme B S hS).obj W).residueField η))) ≫ baseA
      rw [← hWbase, ← Category.assoc, hiKdef, sq.w, hbaseA, ← hsubtype, Category.assoc]
      rfl)
      with huKdef
  set uFrac : siteObject B S hS hKmem
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (((BigFppfOver.toScheme B S hS).obj W).residueField η))) ≫ baseA) ⟶
      siteObject B S hS hAmem baseA :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
      (algebraMap A (((BigFppfOver.toScheme B S hS).obj W).residueField η)))) :
      B.obj hKmem ⟶ B.obj hAmem) with huFracdef
  have huKs : uK ≫ s = uFrac ≫ uA := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    rw [Over.comp_left, Over.comp_left, B.inclusion.map_comp, B.inclusion.map_comp, huKdef,
      huAdef, huFracdef]
    show B.inclusion.map (B.inclusion.preimage (X := B.obj hKmem) (Y := W.left) iK) ≫
        B.inclusion.map s.left =
      Spec.map (CommRingCat.ofHom
          (algebraMap A (((BigFppfOver.toScheme B S hS).obj W).residueField η))) ≫
        B.inclusion.map (B.inclusion.preimage (X := B.obj hAmem) (Y := U.left) i₂)
    rw [B.inclusion.map_preimage, B.inclusion.map_preimage, ← hsubtype]
    exact sq.w
  have hmap : yoneda.map uK ≫ yoneda.map s = yoneda.map uFrac ≫ yoneda.map uA := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, huKs]
  have hcproj : ∀ g : pullback f f ⟶ X, pullback.diagonal f ≫ g = 𝟙 X →
      c = yoneda.map s ≫ atlas ≫ g := fun g hg => by
    calc c = c ≫ pullback.diagonal f ≫ g := by rw [hg, Category.comp_id]
      _ = yoneda.map s ≫ atlas ≫ g := by rw [← Category.assoc, hdiagPB.w, Category.assoc]
  have hcf := hcproj _ (pullback.diagonal_fst f)
  have hcf₂ := hcproj _ (pullback.diagonal_snd f)
  have hgenproj : ∀ g : pullback f f ⟶ X, c = yoneda.map s ≫ atlas ≫ g →
      yoneda.map uFrac ≫ yoneda.map uA ≫ atlas ≫ g = yoneda.map uK ≫ c := fun g hg => by
    calc _ = (yoneda.map uFrac ≫ yoneda.map uA) ≫ atlas ≫ g := (Category.assoc _ _ _).symm
      _ = (yoneda.map uK ≫ yoneda.map s) ≫ atlas ≫ g := by rw [hmap]
      _ = yoneda.map uK ≫ c := by rw [Category.assoc, ← hg]
  set q : ValuativeSquare f :=
    { R := A
      K := (((BigFppfOver.toScheme B S hS).obj W).residueField η : Type u)
      ring_mem := hAmem
      field_mem := hKmem
      base := baseA
      generic := yoneda.map uK ≫ c
      special := yoneda.map uA ≫ atlas ≫ pullback.fst f f ≫ f
      comm := by
        show (yoneda.map uK ≫ c) ≫ f =
          yoneda.map uFrac ≫ yoneda.map uA ≫ atlas ≫ pullback.fst f f ≫ f
        rw [← hgenproj _ hcf]
        simp only [Category.assoc] } with hqdef
  -- the generic arrow picks out a generic point of the chart, hence a codimension-zero point
  set pW : FieldValuedPoint B S hS (yoneda.obj W) :=
    { carrier := (((BigFppfOver.toScheme B S hS).obj W).residueField η : Type u)
      contained := hKmem
      toBase := Spec.map (CommRingCat.ofHom
        (algebraMap A (((BigFppfOver.toScheme B S hS).obj W).residueField η))) ≫ baseA
      value := yonedaEquiv (yoneda.map uK) } with hpWdef
  have hschemePoint : schemePoint B S hS W pW = η := by
    show (BigFppfOver.toScheme B S hS).map (yonedaEquiv (yoneda.map uK))
      (IsLocalRing.closedPoint _) = η
    rw [yonedaEquiv_yoneda_map, huKdef]
    show B.inclusion.map (B.inclusion.preimage (X := B.obj hKmem) (Y := W.left) iK)
      (IsLocalRing.closedPoint _) = η
    rw [B.inclusion.map_preimage, hiKdef]
    exact Scheme.fromSpecResidueField_apply _ _
  have hchart : ChartPoint B S hS W c η q.genericPoint := ⟨pW, hschemePoint, rfl⟩
  have hcodim : localRingDimension B S hS q.genericPoint = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX q.genericPoint).2
      ⟨W, c, η, hcEtale, hchart, hη⟩
  have huniq : Subsingleton q.Lift :=
    h q (inferInstanceAs (IsDiscreteValuationRing (A : Type u))) hcodim
  -- the two projections of the valuation-ring point of the chart of the diagonal
  set m₁ : yoneda.obj (siteObject B S hS hAmem baseA) ⟶ X :=
    yoneda.map uA ≫ atlas ≫ pullback.fst f f with hm₁def
  set m₂ : yoneda.obj (siteObject B S hS hAmem baseA) ⟶ X :=
    yoneda.map uA ≫ atlas ≫ pullback.snd f f with hm₂def
  have hgen₁ : yoneda.map uFrac ≫ m₁ = q.generic := hgenproj _ hcf
  have hgen₂ : yoneda.map uFrac ≫ m₂ = q.generic := hgenproj _ hcf₂
  set l₁ : q.Lift :=
    { map := m₁
      generic_comm := hgen₁
      special_comm := by
        rw [hm₁def]
        show _ = q.special
        simp only [Category.assoc]
        rfl }
    with hl₁def
  set l₂ : q.Lift :=
    { map := m₂
      generic_comm := hgen₂
      special_comm := by
        rw [hm₂def]
        show _ = q.special
        simp only [Category.assoc, ← pullback.condition]
        rfl }
    with hl₂def
  have hmEq : m₁ = m₂ :=
    congrArg ValuativeSquare.Lift.map (@Subsingleton.elim _ huniq l₁ l₂)
  -- the two projections agree, so the valuation-ring point factors through the diagonal
  have hdiagSq : m₁ ≫ pullback.diagonal f = yoneda.map uA ≫ atlas := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, hm₁def]
      simp only [Category.assoc]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hmEq, hm₂def]
      simp only [Category.assoc]
  set lA : siteObject B S hS hAmem baseA ⟶ W :=
    yoneda.preimage (hdiagPB.lift m₁ (yoneda.map uA) hdiagSq)
  have hlAmap : yoneda.map lA = hdiagPB.lift m₁ (yoneda.map uA) hdiagSq :=
    yoneda.map_preimage _
  have hlAc : yoneda.map lA ≫ c = m₁ := by
    rw [hlAmap]; exact hdiagPB.lift_fst m₁ (yoneda.map uA) hdiagSq
  have hlAs : lA ≫ s = uA := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hlAmap]
    exact hdiagPB.lift_snd m₁ (yoneda.map uA) hdiagSq
  have hgenericSite : uFrac ≫ lA = uK := by
    apply yoneda.map_injective
    rw [yoneda.map_comp]
    refine hdiagPB.hom_ext ?_ ?_
    · rw [Category.assoc, hlAc, hgen₁]
    · rw [Category.assoc, ← yoneda.map_comp, hlAs, ← yoneda.map_comp]
      exact (congrArg yoneda.map huKs).symm
  have huKScheme : (BigFppfOver.toScheme B S hS).map uK = iK := by
    rw [huKdef]
    show B.inclusion.map (B.inclusion.preimage (X := B.obj hKmem) (Y := W.left) iK) = iK
    rw [B.inclusion.map_preimage]
  have hschemeLeft : Spec.map (CommRingCat.ofHom A.subtype) ≫
      (BigFppfOver.toScheme B S hS).map lA = iK := by
    have huFracScheme : (BigFppfOver.toScheme B S hS).map uFrac =
        Spec.map (CommRingCat.ofHom (algebraMap A
          (((BigFppfOver.toScheme B S hS).obj W).residueField η))) := by
      rw [huFracdef]
      rfl
    rw [hsubtype, ← huFracScheme, ← Functor.map_comp, hgenericSite, huKScheme]
  have hschemeRight : (BigFppfOver.toScheme B S hS).map lA ≫
      (BigFppfOver.toScheme B S hS).map s = i₂ := by
    rw [← (BigFppfOver.toScheme B S hS).map_comp, hlAs, huAdef]
    show B.inclusion.map (B.inclusion.preimage (X := B.obj hAmem) (Y := U.left) i₂) = i₂
    rw [B.inclusion.map_preimage]
  refine ⟨⟨{ l := (BigFppfOver.toScheme B S hS).map lA
             fac_left := hschemeLeft
             fac_right := hschemeRight }⟩, ⟨fun a b => ?_⟩⟩
  apply CommSq.LiftStruct.ext
  apply (cancel_mono ((BigFppfOver.toScheme B S hS).map s)).1
  rw [a.fac_right, b.fac_right]

/-- **Stacks 0H1W, (4) implies (1)**, assuming Stacks 0208 for monomorphisms of schemes.

The relative diagonal of `f` is representable, separated, a monomorphism and locally of finite
type (Stacks 03HK), and quasi-compact because `f` is quasi-separated. The algebraic space
`X \times_Y X` is locally Noetherian (Stacks 04ZK), so an étale chart `U` of it is a locally
Noetherian scheme and the base change `V ⟶ U` of the diagonal along it is a quasi-compact
monomorphism of schemes locally of finite type. The codimension-zero criterion supplies the
dotted arrows asked for by condition (4) of Stacks 0208 for `V ⟶ U`, hence `V ⟶ U` is proper,
hence a closed immersion; being a closed immersion is fpqc local on the base (Stacks 02L6,
02WZ), so the diagonal of `f` is a closed immersion. -/
theorem isSeparated_of_codimensionZeroUniqueness
    (h0208 : ∀ {V U : Scheme.{u}} (p : V ⟶ U), IsLocallyNoetherian U →
      AlgebraicGeometry.LocallyOfFiniteType p → AlgebraicGeometry.QuasiCompact p →
      Mono p → AlgebraicGeometry.GenericDiscreteValuativeCriterion p →
      AlgebraicGeometry.IsProper p)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) (hlft : IsLocallyOfFiniteType B S hS f)
    (hnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (h : ValuativeCriterion.CodimensionZeroUniqueness f) :
    IsSeparated B S hS f := by
  classical
  have hZ : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS f f hX hX hY
  have hRep : yoneda.relativelyRepresentable (pullback.diagonal f) :=
    relativelyRepresentable_pullbackDiagonal B S hS f hX
  have hfstFT : IsLocallyOfFiniteType B S hS (pullback.fst f f) :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).flip hlft
  have hcompFT : IsLocallyOfFiniteType B S hS (pullback.fst f f ≫ f) :=
    isLocallyOfFiniteType_comp' B S hS _ _ hX hY hfstFT hlft
  obtain ⟨U, atlas, hatlasSurj, hatlasEtale, hU⟩ :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hZ hY _ hcompFT hnoeth
  set W := hRep.pullback atlas with hWdef
  set c := hRep.fst atlas with hcdef
  set s := hRep.snd atlas with hsdef
  have hdiagPB : IsPullback c (yoneda.map s) (pullback.diagonal f) atlas := hRep.isPullback atlas
  have hsSep : AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map s) :=
    (presheaf_isSeparated_pullbackDiagonal B S hS f hX).property atlas c s hdiagPB
  have hsLFT : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map s) :=
    (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS f hX).property atlas c s hdiagPB
  have hsMono : Mono ((BigFppfOver.toScheme B S hS).map s) :=
    (presheaf_monomorphisms_pullbackDiagonal B S hS f hX).property atlas c s hdiagPB
  have hsQC : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map s) :=
    (presheaf_quasiCompact_of_isQuasiCompact B S hS hRep hqs).property atlas c s hdiagPB
  have hUnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hcEtale : IsEtale B S hS c :=
    isEtale_of_isPullback_yoneda B S hS hdiagPB.flip
      ((isEtale_iff_presheaf_of_yoneda B S hS atlas).2 hatlasEtale)
  have hsCrit : AlgebraicGeometry.GenericDiscreteValuativeCriterion
      ((BigFppfOver.toScheme B S hS).map s) := by
    intro η hη A hA hfrac i₂ sq
    exact nonempty_liftStruct_of_codimensionZeroUniqueness hX h atlas c s hdiagPB hcEtale
      hsMono η hη A i₂ sq
  have hsCI : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s) :=
    (AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono _).2
      ⟨h0208 _ hUnoeth hsLFT hsQC hsMono hsCrit, hsMono⟩
  have _ : (show MorphismProperty Scheme.{u} from
      @AlgebraicGeometry.IsClosedImmersion).IsLocalAtTarget Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact (presheaf_inverseImage_iff_atlas_snd B S hS
    (@AlgebraicGeometry.IsClosedImmersion.{u}) (pullback.diagonal f) hRep U atlas
    hatlasSurj hatlasEtale).2 hsCI

end AlgebraicGeometry.Space

end
