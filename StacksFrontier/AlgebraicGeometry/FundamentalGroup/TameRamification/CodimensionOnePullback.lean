module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified

/-!
# Pulling back a cover with codimension-one ramification conditions

A finite étale cover of a dense open subscheme is considered together with a morphism of
locally Noetherian schemes whose inverse-image open is dense. The boundary codimension-one points
have discrete valuation local rings, and the morphism carries each such point in the source to
one in the target. In this situation the pulled-back cover is again finite and étale over the
inverse-image open subscheme.

## Main definitions

* `Stacks.FundamentalGroup.CodimensionOnePullbackSetup` bundles the standing data and
  assumptions.
* `Stacks.FundamentalGroup.IsFieldFactorAt` identifies a field factor of the generic fibre of
  the cover at a boundary discrete valuation ring.
* `Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne` and
  `Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne` impose the corresponding
  valuation-theoretic condition on every factor.

## Main results

* `Stacks.FundamentalGroup.pulledBackCover_isFinite` gives finiteness of the canonical
  morphism from the pulled-back cover to the inverse-image open subscheme.
* `Stacks.FundamentalGroup.pulledBackCover_etale` gives its étaleness.
* `Stacks.FundamentalGroup.isIso_of_specMap_comp_eq_fromSpecResidueField` recognizes a field
  factor presented as above as the whole residue field.

## References

* [Stacks Project, Tag 0EYD](https://stacks.math.columbia.edu/tag/0EYD)
* [Stacks Project, Tag 09E9](https://stacks.math.columbia.edu/tag/09E9)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace Stacks.FundamentalGroup

/-- The data and boundary hypotheses for codimension-one pullback of a finite
étale cover. -/
public structure CodimensionOnePullbackSetup where
  /-- The ambient scheme carrying the cover. -/
  X : Scheme.{u}
  /-- The scheme mapping to the ambient scheme. -/
  X' : Scheme.{u}
  /-- The ambient scheme is locally Noetherian. -/
  locallyNoetherian_X : IsLocallyNoetherian X
  /-- The source of the morphism is locally Noetherian. -/
  locallyNoetherian_X' : IsLocallyNoetherian X'
  /-- The morphism along which the cover is pulled back. -/
  g : X' ⟶ X
  /-- The open subscheme over which the cover is given. -/
  U : X.Opens
  /-- That open subscheme is dense. -/
  dense_U : DenseRange U.ι.base
  /-- The covering scheme. -/
  Y : Scheme.{u}
  /-- The covering morphism. -/
  f : Y ⟶ U
  /-- The covering morphism is finite. -/
  finite_f : IsFinite f
  /-- The covering morphism is étale. -/
  etale_f : Etale f
  /-- The inverse image of the open subscheme is dense. -/
  dense_U' : DenseRange (pullback.fst g U.ι).base
  /-- Every boundary prime divisor of the ambient scheme has a discrete valuation local ring. -/
  dvr_X : ∀ Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor X,
    Z.genericPoint ∉ U →
    ∃ _ : IsDomain (X.presheaf.stalk Z.genericPoint),
      IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint)
  /-- Every boundary prime divisor of the source has a discrete valuation local ring. -/
  dvr_X' : ∀ Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor X',
    Z.genericPoint ∉ Set.range (pullback.fst g U.ι).base →
    ∃ _ : IsDomain (X'.presheaf.stalk Z.genericPoint),
      IsDiscreteValuationRing (X'.presheaf.stalk Z.genericPoint)
  /-- The morphism carries boundary prime divisors to boundary prime divisors. -/
  maps_boundary : ∀ Z' : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor
    X',
    Z'.genericPoint ∉ Set.range (pullback.fst g U.ι).base →
    ∃ Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor X,
      Z.genericPoint ∉ U ∧ g Z'.genericPoint = Z.genericPoint

/-- The inverse-image open scheme. -/
public abbrev CodimensionOnePullbackSetup.U' (D : CodimensionOnePullbackSetup.{u}) :
    Scheme.{u} := pullback D.g D.U.ι

/-- The pullback of the cover over the ambient scheme. -/
public abbrev CodimensionOnePullbackSetup.Y' (D : CodimensionOnePullbackSetup.{u}) :
    Scheme.{u} := pullback (D.f ≫ D.U.ι) D.g

/-- The canonical morphism from the pulled-back cover to the inverse-image
open subscheme. -/
public def CodimensionOnePullbackSetup.pulledBackCover
    (D : CodimensionOnePullbackSetup.{u}) : D.Y' ⟶ D.U' :=
  pullback.lift (pullback.snd (D.f ≫ D.U.ι) D.g)
    (pullback.fst (D.f ≫ D.U.ι) D.g ≫ D.f) (by
      simp only [Category.assoc, pullback.condition])

/-- A field factor of the generic fibre at `x`. The isomorphism with a
residue field excludes proper field extensions of a factor. -/
public def IsFieldFactorAt {X U Y : Scheme.{u}} (j : U ⟶ X) (f : Y ⟶ U)
    (x : X) (K L : Type u) [Field K] [Field L]
    [Algebra (X.presheaf.stalk x) K] [Algebra K L] : Prop :=
  ∃ (w : Spec (.of K) ⟶ U) (v : Spec (.of L) ⟶ Y),
    w ≫ j =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫
        X.fromSpecStalk x ∧
    v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ w ∧
    ∃ e : Y.residueField (v (IsLocalRing.closedPoint L)) ≃+* L,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Y.fromSpecResidueField (v (IsLocalRing.closedPoint L)) = v

/-- Every field factor above a boundary prime divisor is unramified over
its discrete valuation local ring. -/
public def IsUnramifiedInCodimensionOne {X U Y : Scheme.{u}}
    (j : U ⟶ X) (f : Y ⟶ U) : Prop :=
  ∀ (Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor X),
    Z.genericPoint ∉ Set.range j.base →
    ∀ (hD : IsDomain (X.presheaf.stalk Z.genericPoint))
      (hV : IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint)),
      letI := hD
      letI := hV
      ∀ (K L : Type u) [Field K] [Field L]
        [Algebra (X.presheaf.stalk Z.genericPoint) K]
        [IsFractionRing (X.presheaf.stalk Z.genericPoint) K]
        [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
        [Algebra (X.presheaf.stalk Z.genericPoint) L]
        [IsScalarTower (X.presheaf.stalk Z.genericPoint) K L],
        IsFieldFactorAt j f Z.genericPoint K L →
          IsDiscreteValuationRing.IsUnramifiedWithRespectTo
            (X.presheaf.stalk Z.genericPoint) K L

/-- Every field factor above a boundary prime divisor is tamely ramified over
its discrete valuation local ring. -/
public def IsTamelyRamifiedInCodimensionOne {X U Y : Scheme.{u}}
    (j : U ⟶ X) (f : Y ⟶ U) : Prop :=
  ∀ (Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor X),
    Z.genericPoint ∉ Set.range j.base →
    ∀ (hD : IsDomain (X.presheaf.stalk Z.genericPoint))
      (hV : IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint)),
      letI := hD
      letI := hV
      ∀ (K L : Type u) [Field K] [Field L]
        [Algebra (X.presheaf.stalk Z.genericPoint) K]
        [IsFractionRing (X.presheaf.stalk Z.genericPoint) K]
        [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
        [Algebra (X.presheaf.stalk Z.genericPoint) L]
        [IsScalarTower (X.presheaf.stalk Z.genericPoint) K L],
        IsFieldFactorAt j f Z.genericPoint K L →
          IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo
            (X.presheaf.stalk Z.genericPoint) K L

/-- A map of fields into a residue field whose `Spec` factors the canonical map from that
residue field is an isomorphism. -/
public lemma isIso_of_specMap_comp_eq_fromSpecResidueField
    {Z : Scheme.{u}} (z : Z) {K : Type u} [Field K]
    (c : CommRingCat.of K ⟶ Z.residueField z) (a : Spec (.of K) ⟶ Z)
    (h : Spec.map c ≫ a = Z.fromSpecResidueField z) : IsIso c := by
  obtain ⟨⟨y, k⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective a
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  have hy := congrArg (fun m : Spec (Z.residueField z) ⟶ Z ↦ m default) h
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at hy
  subst y
  have : Mono c := ConcreteCategory.mono_of_injective c c.hom.injective
  have : IsSplitEpi c := ⟨⟨k, by
    simpa only [← Spec.map_inj, Spec.map_comp, Spec.map_id,
      ← cancel_mono (Z.fromSpecResidueField z), Category.assoc, Category.id_comp] using h⟩⟩
  exact isIso_of_mono_of_isSplitEpi c

/-- The pulled-back cover is a base change of the cover along the given morphism. -/
private noncomputable def pulledBackCoverBaseChangeIso
    (D : CodimensionOnePullbackSetup.{u}) :
    pullback D.f (pullback.snd D.g D.U.ι) ≅ D.Y' :=
  (pullbackSymmetry D.f (pullback.snd D.g D.U.ι)).trans
    ((pullbackLeftPullbackSndIso D.g D.U.ι D.f).trans
      (pullbackSymmetry D.g (D.f ≫ D.U.ι)))

/-- The canonical morphism from the pulled-back cover is, up to that isomorphism, the base
change of the cover. -/
private lemma pulledBackCover_eq_baseChange
    (D : CodimensionOnePullbackSetup.{u}) :
    D.pulledBackCover = (pulledBackCoverBaseChangeIso D).inv ≫
      pullback.snd D.f (pullback.snd D.g D.U.ι) := by
  rw [Iso.eq_inv_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, CodimensionOnePullbackSetup.pulledBackCover, pullback.lift_fst]
    simp [pulledBackCoverBaseChangeIso]
  · rw [Category.assoc, CodimensionOnePullbackSetup.pulledBackCover, pullback.lift_snd]
    simp [pulledBackCoverBaseChangeIso, pullback.condition]

/-- The canonical pullback of the cover is finite. -/
@[stacks 0EYD "finite_etale_pullback"]
public instance pulledBackCover_isFinite
    (D : CodimensionOnePullbackSetup.{u}) :
    IsFinite D.pulledBackCover := by
  have := D.finite_f
  rw [pulledBackCover_eq_baseChange]
  infer_instance

/-- The canonical pullback of the cover is étale. -/
@[stacks 0EYD "finite_etale_pullback"]
public instance pulledBackCover_etale
    (D : CodimensionOnePullbackSetup.{u}) :
    Etale D.pulledBackCover := by
  have := D.etale_f
  rw [pulledBackCover_eq_baseChange]
  infer_instance

end Stacks.FundamentalGroup
