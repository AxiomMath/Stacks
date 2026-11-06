module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.OpenImmersionCriterion
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence

/-!
# The valuative criterion for separatedness using discrete valuation rings

For a morphism locally of finite type to a locally Noetherian scheme, separatedness can be
tested either on all valuation rings, on discrete valuation rings, or only on discrete valuation
subrings of the residue fields at the generic points of the irreducible components of the
source.

## Main results

* `AlgebraicGeometry.isSeparated_tfae_of_locallyOfFiniteType`: the four forms of the valuative
  criterion for separatedness are equivalent.
* `AlgebraicGeometry.isIso_residueFieldMap_of_isClosedImmersion` and
  `AlgebraicGeometry.isIso_residueFieldMap_of_isImmersion`: a closed immersion, and more generally
  an immersion, induces an isomorphism on residue fields.
* `AlgebraicGeometry.hom_ext_of_closedPoint_eq_of_specMap_comp_eq`: a morphism out of the
  spectrum of a local domain is determined by its value at the closed point together with its
  restriction to the fraction field.

## Implementation notes

Valuative diagrams are expressed using `AlgebraicGeometry.ValuativeCommSq`, and "at most one
dotted arrow" by `Subsingleton` on the square's `CategoryTheory.CommSq.LiftStruct`.  A generic
point of an irreducible component is represented by membership in `genericPoints X`.  In the last
condition, a valuation subring `A` of `X.residueField η` together with
`IsFractionRing A (X.residueField η)` expresses that this residue field is the fraction field of
`A`.

The implication from the restricted criterion back to separatedness is the substance of the
proof, and it is assembled from three geometric inputs, each isolated as a private lemma: a
non-generic point of an integral locally Noetherian scheme has a non-field local ring, so the
local ring is dominated by a discrete valuation ring inside the function field
(`exists_isDiscreteValuationRing_subalgebra_of_ne_genericPoint`); a specialization in a locally
Noetherian scheme is realized inside an integral closed subscheme whose generic point is the
specializing point (`exists_integral_closedImmersion_of_specializes`); and a morphism out of the
spectrum of a local domain is determined by its value at the closed point together with its
restriction to the fraction field (`eq_of_closedPoint_eq_of_specMap_comp_eq`).

The transport from the function field of that closed subscheme to the residue field of the
source, together with the compatibility of the two spectra over the ambient scheme, is split off
into `functionFieldEquivOfGenericImmersion` and
`specMap_functionFieldEquivOfGenericImmersion_comp`; the latter is proved from three
`fromSpecResidueField` identities, one per factor of the equivalence, so that no single
elaboration has to see all of them at once.

## References

* [Stacks Project, Tag 0207](https://stacks.math.columbia.edu/tag/0207)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- At a point of an integral scheme other than the generic point the local ring is not a
field: otherwise the canonical map from the local ring to the function field would carry the
closed point of the function field to that point as well as to the generic point. -/
private theorem not_isField_stalk_of_ne_genericPoint
    {Z : Scheme.{u}} [IsIntegral Z] (y : Z) (hy : y ≠ genericPoint Z) :
    ¬ IsField (Z.presheaf.stalk y) := by
  intro hfield
  let R := Z.presheaf.stalk y
  let K := Z.functionField
  let : Field R := hfield.toField
  have hspec := Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    (X := Z) ((genericPoint_spec Z).specializes (Set.mem_univ y))
  have heval := congrArg
    (fun g : Spec (.of K) ⟶ Z => g (IsLocalRing.closedPoint K)) hspec
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R K))
      (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint R := by
    apply PrimeSpectrum.ext
    change (IsLocalRing.maximalIdeal K).comap (algebraMap R K) =
      IsLocalRing.maximalIdeal R
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField K),
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield]
    simp
  change Z.fromSpecStalk y
    (Spec.map (CommRingCat.ofHom (algebraMap R K)) (IsLocalRing.closedPoint K)) =
      Z.fromSpecStalk (genericPoint Z) (IsLocalRing.closedPoint K) at heval
  rw [hmap, Scheme.fromSpecStalk_closedPoint, Scheme.fromSpecStalk_closedPoint] at heval
  exact hy heval

/-- The local ring at a non-generic point of an integral locally Noetherian scheme is dominated
by a discrete valuation subring of the function field, and the spectrum of that subring maps to
the scheme compatibly with the canonical map out of the spectrum of the local ring. -/
private theorem exists_isDiscreteValuationRing_subalgebra_of_ne_genericPoint
    {Z : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z] (y : Z)
    (hy : y ≠ genericPoint Z) :
    ∃ (A : Subalgebra (Z.presheaf.stalk y) Z.functionField),
      ∃ (hA : IsDiscreteValuationRing A),
        IsFractionRing A Z.functionField ∧
          IsLocalHom (algebraMap (Z.presheaf.stalk y) A) ∧
          ∃ (i : Spec (.of A) ⟶ Z),
            i (@IsLocalRing.closedPoint A _
                (@IsDiscreteValuationRing.toIsLocalRing A _ _ hA)) = y ∧
            Spec.map (CommRingCat.ofHom A.subtype) ≫ i =
              Spec.map (CommRingCat.ofHom (algebraMap
                (Z.presheaf.stalk y) Z.functionField)) ≫ Z.fromSpecStalk y := by
  obtain ⟨A, hA, hAK, hlocal⟩ : ∃ A : Subalgebra (Z.presheaf.stalk y) Z.functionField,
      IsDiscreteValuationRing A ∧ IsFractionRing A Z.functionField ∧
        IsLocalHom (algebraMap (Z.presheaf.stalk y) A) :=
    exists_isDiscreteValuationRing_isFractionRing_of_not_isField Z.functionField
      (not_isField_stalk_of_ne_genericPoint y hy)
  have : IsDiscreteValuationRing A := hA
  have : IsLocalHom (algebraMap (Z.presheaf.stalk y) A) := hlocal
  let i : Spec (.of A) ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.presheaf.stalk y) A)) ≫
      Z.fromSpecStalk y
  let : IsLocalRing A := @IsDiscreteValuationRing.toIsLocalRing A _ _ hA
  have hclosed : i (IsLocalRing.closedPoint A) = y := by
    change Z.fromSpecStalk y
      (PrimeSpectrum.comap (algebraMap (Z.presheaf.stalk y) A)
        (IsLocalRing.closedPoint A)) = y
    rw [IsLocalRing.comap_closedPoint (algebraMap (Z.presheaf.stalk y) A),
      Scheme.fromSpecStalk_closedPoint]
  refine ⟨A, hA, hAK, hlocal, i, hclosed, ?_⟩
  dsimp [i]
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1

/-- A nontrivial specialization in a locally Noetherian scheme is realized by an integral closed
subscheme whose generic point lies over the specializing point. -/
private theorem exists_integral_closedImmersion_of_specializes
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] {t y : Y} (hty : t ⤳ y)
    (hne : t ≠ y) :
    ∃ (Z : Scheme) (j : Z ⟶ Y), IsClosedImmersion j ∧ IsIntegral Z ∧
      IsLocallyNoetherian Z ∧ ∃ (zt zy : Z), j zt = t ∧ j zy = y ∧
        IsGenericPoint zt Set.univ ∧ zy ≠ zt := by
  classical
  let T : Closeds Y := .closure ({t} : Set Y)
  have hT : IsIrreducible (T : Set Y) := isIrreducible_singleton.closure
  have htT : t ∈ (T : Set Y) := subset_closure (Set.mem_singleton t)
  have hyT : y ∈ (T : Set Y) := specializes_iff_mem_closure.mp hty
  let I : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T
  let Z : Scheme := I.subscheme
  let j : Z ⟶ Y := I.subschemeι
  have hrange : Set.range j = (T : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  obtain ⟨zt, hzt⟩ : t ∈ Set.range j := hrange ▸ htT
  obtain ⟨zy, hzy⟩ : y ∈ Set.range j := hrange ▸ hyT
  let e : Z ≃ₜ T :=
    ((Homeomorph.Set.univ Z).symm.trans
      (j.isClosedEmbedding.isEmbedding.homeomorphImage Set.univ)).trans
      (Homeomorph.setCongr (by simpa only [Set.image_univ] using hrange))
  have : IrreducibleSpace Z := e.irreducibleSpace_iff.mpr (Subtype.irreducibleSpace hT)
  have : IsReduced Z := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal T
  have : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian j
  have hztI : IsGenericPoint zt Set.univ := by
    rw [isGenericPoint_def]
    refine Set.eq_univ_iff_forall.mpr fun w => ?_
    have hwT : j w ∈ (T : Set Y) := hrange ▸ Set.mem_range_self w
    have hwclosure : j w ∈ closure ({j zt} : Set Y) := by rwa [hzt]
    rw [j.isClosedEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    simpa only [Set.mem_preimage, Set.image_singleton] using hwclosure
  exact ⟨Z, j, inferInstance, inferInstance, inferInstance, zt, zy,
    hzt, hzy, hztI, fun hyz => hne (by rw [← hzt, ← hzy, hyz])⟩

/-- Two morphisms from the spectrum of a ring to an affine scheme which agree after restriction to
the fraction field are equal. -/
private theorem eq_of_isAffine_of_specMap_comp_eq
    {A K : Type u} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    {U : Scheme.{u}} [IsAffine U] (f g : Spec (.of A) ⟶ U)
    (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g) : f = g := by
  let fS := f ≫ U.isoSpec.hom
  let gS := g ≫ U.isoSpec.hom
  let φ := Spec.preimage fS
  let ψ := Spec.preimage gS
  have hfS : Spec.map φ = fS := Spec.map_preimage fS
  have hgS : Spec.map ψ = gS := Spec.map_preimage gS
  have hφψ : φ = ψ := by
    ext r
    have hcomp : φ ≫ CommRingCat.ofHom (algebraMap A K) =
        ψ ≫ CommRingCat.ofHom (algebraMap A K) := by
      apply Spec.map_injective
      calc
        Spec.map (φ ≫ CommRingCat.ofHom (algebraMap A K)) =
            Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ fS := by
              rw [Spec.map_comp, hfS]
        _ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ gS := by
              simpa only [Category.assoc] using congrArg (· ≫ U.isoSpec.hom) hgeneric
        _ = Spec.map (ψ ≫ CommRingCat.ofHom (algebraMap A K)) := by
              rw [Spec.map_comp, hgS]
    exact IsFractionRing.injective A K
      (congrArg (fun h => h r) (CommRingCat.hom_ext_iff.mp hcomp))
  exact (cancel_mono U.isoSpec.hom).mp (hfS.symm.trans ((congrArg Spec.map hφψ).trans hgS))

/-- Two morphisms out of the spectrum of a local domain which agree at the closed point and
agree after restriction to the fraction field are equal: both factor through one affine open
containing the common image of the closed point, where they are determined by the induced ring
maps, and those agree because the fraction field embedding is injective. -/
private theorem eq_of_closedPoint_eq_of_specMap_comp_eq
    {A K : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {X : Scheme.{u}} (f g : Spec (.of A) ⟶ X)
    (hclosed : f (IsLocalRing.closedPoint A) = g (IsLocalRing.closedPoint A))
    (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g) : f = g := by
  classical
  let x := f (IsLocalRing.closedPoint A)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hrange (k : Spec (.of A) ⟶ X) (hk : k (IsLocalRing.closedPoint A) = x) :
      Set.range k ⊆ Set.range (Scheme.Opens.ι U) := by
    rintro z ⟨p, rfl⟩
    have hs := (IsLocalRing.specializes_closedPoint p).map k.continuous
    rw [hk] at hs
    rw [Scheme.Opens.range_ι]
    exact hs.mem_open U.2 hxU
  let fU : Spec (.of A) ⟶ Scheme.Opens.toScheme U :=
    IsOpenImmersion.lift (Scheme.Opens.ι U) f (hrange f rfl)
  let gU : Spec (.of A) ⟶ Scheme.Opens.toScheme U :=
    IsOpenImmersion.lift (Scheme.Opens.ι U) g (hrange g hclosed.symm)
  have : IsAffine (Scheme.Opens.toScheme U) := hU
  have hUeq : fU = gU := by
    refine eq_of_isAffine_of_specMap_comp_eq (K := K) fU gU ?_
    apply (cancel_mono (Scheme.Opens.ι U)).mp
    calc
      _ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ f := by
        simp [fU]
      _ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g := hgeneric
      _ = _ := by simp [gU]
  calc
    f = fU ≫ Scheme.Opens.ι U := by simp [fU]
    _ = gU ≫ Scheme.Opens.ι U := by rw [hUeq]
    _ = g := by simp [gU]

/-- Two morphisms out of the spectrum of a local domain which agree at the closed point and
agree after restriction to the fraction field are equal.

This is the statement of the private `eq_of_closedPoint_eq_of_specMap_comp_eq` above, which is
one of the three geometric inputs of the proof of Stacks 0207 in this file. It is stated again
under a public name because the refined criteria of Stacks 0CM3–0CM5 need the same uniqueness
argument, in
`AlgebraicGeometry.isSeparated_of_denseRange_of_subsingleton_discreteLift`; the private lemma
has to keep its visibility, so the export is a separate declaration. -/
alias hom_ext_of_closedPoint_eq_of_specMap_comp_eq := eq_of_closedPoint_eq_of_specMap_comp_eq

section ResidueFieldMap

/-- A closed immersion induces an isomorphism on residue fields: the map is injective because
residue fields are fields, and surjective because a closed immersion is surjective on stalks. -/
alias isIso_residueFieldMap_of_isClosedImmersion := residueFieldMap_isIso_of_isClosedImmersion

/-- An open immersion induces an isomorphism on residue fields, because it induces one on
stalks. -/
private theorem isIso_residueFieldMap_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) : IsIso (f.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

/-- An immersion induces an isomorphism on residue fields: it factors as a closed immersion into
its coborder followed by the open immersion of the coborder. -/
theorem isIso_residueFieldMap_of_isImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsImmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  have : IsIso (f.liftCoborder.residueFieldMap x) :=
    AlgebraicGeometry.residueFieldMap_isIso_of_isClosedImmersion _ x
  have : IsIso (f.coborderRange.ι.residueFieldMap (f.liftCoborder x)) :=
    isIso_residueFieldMap_of_isOpenImmersion _ _
  rw [← f.liftCoborder_ι, Scheme.residueFieldMap_comp]
  exact CategoryTheory.IsIso.comp_isIso' ‹_› ‹_›

end ResidueFieldMap

section FunctionFieldEquiv

variable {Z X Y : Scheme.{u}}

/-- The residue field map of a closed immersion, as a ring equivalence. -/
private noncomputable def residueFieldEquivOfIsClosedImmersion (j : Z ⟶ Y)
    [IsClosedImmersion j] (z : Z) :
    Y.residueField (j z) ≃+* Z.residueField z :=
  have : IsIso (j.residueFieldMap z) :=
    AlgebraicGeometry.residueFieldMap_isIso_of_isClosedImmersion j z
  (asIso (j.residueFieldMap z)).commRingCatIsoToRingEquiv

private lemma residueFieldEquivOfIsClosedImmersion_toRingHom (j : Z ⟶ Y)
    [IsClosedImmersion j] (z : Z) :
    (residueFieldEquivOfIsClosedImmersion j z).toRingHom =
      (j.residueFieldMap z).hom := rfl

/-- The residue field map of an immersion, as a ring equivalence. -/
private noncomputable def residueFieldEquivOfIsImmersion (g : X ⟶ Y) [IsImmersion g] (x : X) :
    Y.residueField (g x) ≃+* X.residueField x :=
  have : IsIso (g.residueFieldMap x) := isIso_residueFieldMap_of_isImmersion g x
  (asIso (g.residueFieldMap x)).commRingCatIsoToRingEquiv

variable [IsIntegral Z]

/-- The function field of an integral scheme is its residue field at the generic point: the
local ring there is already a field, so the residue map is bijective. -/
private noncomputable def functionFieldEquivResidueField :
    Z.functionField ≃+* Z.residueField (genericPoint Z) := by
  change Z.presheaf.stalk (genericPoint Z) ≃+*
    IsLocalRing.ResidueField (Z.presheaf.stalk (genericPoint Z))
  exact RingEquiv.ofBijective (IsLocalRing.residue _)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.maximalIdeal_eq_bot] at hx,
      IsLocalRing.residue_surjective⟩

private lemma specMap_functionFieldEquivResidueField :
    Spec.map (CommRingCat.ofHom (functionFieldEquivResidueField (Z := Z)).toRingHom) ≫
        Z.fromSpecStalk (genericPoint Z) =
      Z.fromSpecResidueField (genericPoint Z) := rfl

variable (j : Z ⟶ Y) [IsClosedImmersion j] (g : X ⟶ Y) (η : X)
variable (hz : j (genericPoint Z) = g η)

/-- The residue field of the ambient scheme at the common image point, identified with the
residue field of `Z` at its generic point along the closed immersion `j`. -/
private noncomputable def ambientEquivGenericResidueField :
    Y.residueField (g η) ≃+* Z.residueField (genericPoint Z) :=
  ((Y.residueFieldCongr hz).commRingCatIsoToRingEquiv.symm).trans
    (residueFieldEquivOfIsClosedImmersion j (genericPoint Z))

/-- The ambient scheme's canonical map out of the residue field at the common image point,
pulled back along `j`. -/
private lemma specMap_ambientEquivGenericResidueField_symm :
    Spec.map (CommRingCat.ofHom (ambientEquivGenericResidueField j g η hz).symm.toRingHom) ≫
        Z.fromSpecResidueField (genericPoint Z) ≫ j =
      Y.fromSpecResidueField (g η) := by
  have hJraw : Spec.map (CommRingCat.ofHom
        (residueFieldEquivOfIsClosedImmersion j (genericPoint Z)).toRingHom) ≫
      Y.fromSpecResidueField (j (genericPoint Z)) =
        Z.fromSpecResidueField (genericPoint Z) ≫ j := by
    rw [residueFieldEquivOfIsClosedImmersion_toRingHom]
    exact j.SpecMap_residueFieldMap_fromSpecResidueField (genericPoint Z)
  have hring : CommRingCat.ofHom
        (residueFieldEquivOfIsClosedImmersion j (genericPoint Z)).toRingHom ≫
      CommRingCat.ofHom (ambientEquivGenericResidueField j g η hz).symm.toRingHom =
        CommRingCat.ofHom (Y.residueFieldCongr hz).commRingCatIsoToRingEquiv.toRingHom := by
    ext x
    change (((Y.residueFieldCongr hz).commRingCatIsoToRingEquiv.symm).trans
          (residueFieldEquivOfIsClosedImmersion j (genericPoint Z))).symm
        (residueFieldEquivOfIsClosedImmersion j (genericPoint Z) x) =
      (Y.residueFieldCongr hz).commRingCatIsoToRingEquiv x
    simp only [RingEquiv.symm_trans_apply, RingEquiv.symm_apply_apply, RingEquiv.symm_symm]
  calc
    Spec.map (CommRingCat.ofHom (ambientEquivGenericResidueField j g η hz).symm.toRingHom) ≫
        Z.fromSpecResidueField (genericPoint Z) ≫ j =
        Spec.map (CommRingCat.ofHom
            (ambientEquivGenericResidueField j g η hz).symm.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom
              (residueFieldEquivOfIsClosedImmersion j (genericPoint Z)).toRingHom) ≫
            Y.fromSpecResidueField (j (genericPoint Z))) := by rw [← hJraw]
    _ = Spec.map (CommRingCat.ofHom
          (Y.residueFieldCongr hz).commRingCatIsoToRingEquiv.toRingHom) ≫
        Y.fromSpecResidueField (j (genericPoint Z)) := by
          rw [← Category.assoc, ← Spec.map_comp]
          exact congrArg (fun k => Spec.map k ≫ Y.fromSpecResidueField _) hring
    _ = Y.fromSpecResidueField (g η) := Y.residueFieldCongr_fromSpecResidueField hz

variable [IsImmersion g]

/-- The function field of `Z` is the residue field of `X` at `η`, when the generic point of `Z`
and `η` have the same image in `Y`.  Both are identified with the residue field of `Y` at that
common image, through the closed immersion `j` and the immersion `g` respectively. -/
private noncomputable def functionFieldEquivOfGenericImmersion :
    Z.functionField ≃+* X.residueField η :=
  functionFieldEquivResidueField.trans
    ((ambientEquivGenericResidueField j g η hz).symm.trans
      (residueFieldEquivOfIsImmersion g η))

/-- The identification `functionFieldEquivOfGenericImmersion` is compatible with the two
canonical maps into `Y`: the one out of the spectrum of the local ring at the generic point of
`Z`, composed with `j`, and the one out of the spectrum of the residue field at `η`, composed
with `g`. -/
private theorem specMap_functionFieldEquivOfGenericImmersion_comp :
    Spec.map (CommRingCat.ofHom
      (functionFieldEquivOfGenericImmersion j g η hz).toRingHom) ≫
        Z.fromSpecStalk (genericPoint Z) ≫ j =
      X.fromSpecResidueField η ≫ g := by
  have hD : Spec.map (CommRingCat.ofHom
        (residueFieldEquivOfIsImmersion g η).toRingHom) ≫
      Y.fromSpecResidueField (g η) = X.fromSpecResidueField η ≫ g :=
    g.SpecMap_residueFieldMap_fromSpecResidueField η
  simp only [functionFieldEquivOfGenericImmersion, RingEquiv.toRingHom_trans',
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [reassoc_of% specMap_functionFieldEquivResidueField,
    specMap_ambientEquivGenericResidueField_symm, hD]

end FunctionFieldEquiv

section DiscreteValuationSubring

/-- **A nontrivial specialization of a point in the image of an immersion is realized by a
discrete valuation subring of the residue field at that point.**

Let `g : Xs ⟶ Yamb` be an immersion into a locally Noetherian scheme and let `g η` specialize to
a point `y` distinct from it.  Then any field `L` identified with the residue field of `Xs` at
`η` is the fraction field of a discrete valuation subring `B`, and `Spec B` maps to `Yamb`
restricting on the fraction field to the canonical morphism `Spec κ(η) ⟶ Xs ⟶ Yamb` read through
that identification, and carrying the closed point to `y`.

The identification `τ` is carried along because the criterion for properness applies the
construction at a generic point of the source of a Chow modification while the subring it needs
lives in the residue field of the scheme being tested.

The specialization is realized by an integral closed subscheme `Z` of `Yamb` whose generic point
is `g η`; the local ring of `Z` at `y` is then not a field, so it is dominated by a discrete
valuation subring of the function field of `Z`; and that function field is the residue field of
`Xs` at `η`.  Those three steps are the geometric inputs of
`AlgebraicGeometry.isSeparated_tfae_of_locallyOfFiniteType`, and this statement packages them
for the criterion for properness, which needs the same construction. -/
@[ega "II 7.1.4" "special case",
  ega "II 7.1.9" "special case",
  ega "IV 15.5.2.2" "1°",
  sga "3 XV 3.3" "partial"]
theorem exists_isDiscreteValuationRing_subring_of_specializes_of_isImmersion
    {Xs Yamb : Scheme.{u}} [IsLocallyNoetherian Yamb] (gi : Xs ⟶ Yamb) [IsImmersion gi]
    (η : Xs) {y : Yamb} (hspec : gi η ⤳ y) (hne : gi η ≠ y)
    {L : Type u} [Field L] (τ : (Xs.residueField η : Type u) ≃+* L) :
    ∃ (B : Subring L) (hB : IsDiscreteValuationRing B),
      IsFractionRing B L ∧
        ∃ m : Spec (.of B) ⟶ Yamb,
          Spec.map (CommRingCat.ofHom B.subtype) ≫ m =
              Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Xs.fromSpecResidueField η ≫ gi ∧
            m (@IsLocalRing.closedPoint B _
                (@IsDiscreteValuationRing.toIsLocalRing B _ _ hB)) = y := by
  classical
  obtain ⟨Z, j, _, _, _, zt, zy, hzt, hzy, hztI, hzyNe⟩ :=
    exists_integral_closedImmersion_of_specializes hspec hne
  obtain rfl : zt = genericPoint Z := ((genericPoint_spec Z).eq hztI).symm
  let e₀ := functionFieldEquivOfGenericImmersion j gi η hzt
  let e := e₀.trans τ
  obtain ⟨A, _, _, _, iz, hzyA, hgeneric⟩ :=
    exists_isDiscreteValuationRing_subalgebra_of_ne_genericPoint zy hzyNe
  let K₀ := Z.functionField
  let _ : Algebra A L := (e.toRingHom.comp (algebraMap A K₀)).toAlgebra
  have _ : IsFractionRing A L :=
    IsFractionRing.of_algEquiv (AlgEquiv.ofRingEquiv (f := e) fun _ => rfl : K₀ ≃ₐ[A] L)
  let B : Subring L := A.toSubring.map e.toRingHom
  let eAB : A ≃+* B := Subring.equivMapOfInjective A.toSubring e.toRingHom e.injective
  have hBdvr : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eAB
  let _ : Algebra B L := B.subtype.toAlgebra
  have hBfrac : IsFractionRing B L :=
    IsFractionRing.of_ringEquiv_left eAB.symm (by
      intro b
      change (b : L) = e ((eAB.symm b : A) : K₀)
      exact congrArg (fun x : B => (x : L)) (eAB.apply_symm_apply b).symm)
  let vB : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom eAB.toRingHom)
  have hv : Spec.map (CommRingCat.ofHom B.subtype) ≫ vB =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map (CommRingCat.ofHom A.subtype) := by
    dsimp only [vB]
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hAtoZ : Spec.map (CommRingCat.ofHom A.subtype) ≫ iz =
      Z.fromSpecStalk (genericPoint Z) := by
    rw [hgeneric]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      ((genericPoint_spec Z).specializes (Set.mem_univ zy))
  have hmap : Spec.map (CommRingCat.ofHom e.toRingHom) =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom e₀.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  refine ⟨B, hBdvr, hBfrac, vB ≫ iz ≫ j, ?_, ?_⟩
  · rw [reassoc_of% hv, reassoc_of% hAtoZ, hmap]
    simp only [Category.assoc]
    rw [specMap_functionFieldEquivOfGenericImmersion_comp j gi η hzt]
  · have _ : IsLocalHom eAB.toRingHom := IsLocalHom.of_surjective _ eAB.surjective
    have hvcp : vB (@IsLocalRing.closedPoint B _
        (@IsDiscreteValuationRing.toIsLocalRing B _ _ hBdvr)) = IsLocalRing.closedPoint A := by
      change PrimeSpectrum.comap eAB.toRingHom _ = _
      exact IsLocalRing.comap_closedPoint _
    change j (iz (vB _)) = y
    rw [hvcp, hzyA, hzy]

end DiscreteValuationSubring

section Tfae

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The restricted criterion of
`AlgebraicGeometry.isSeparated_tfae_of_locallyOfFiniteType`, written out so that the
implications it takes part in can be stated separately. -/
private def RestrictedValuativeUniqueness : Prop :=
  ∀ (η : X), η ∈ genericPoints X →
    ∀ (A : Subring (X.residueField η)),
      IsDiscreteValuationRing A →
        IsFractionRing A (X.residueField η) →
          ∀ (i₂ : Spec (.of A) ⟶ S)
            (sq : CommSq (X.fromSpecResidueField η)
              (Spec.map (CommRingCat.ofHom A.subtype)) f i₂),
            Subsingleton sq.LiftStruct

/-- Given two dotted arrows of a valuative square, the image of the closed point under the
induced morphism to `X ×_S X` is a specialization of the image under the diagonal of the
image of the generic point. -/
private theorem diagonal_specializes_pullbackLift_closedPoint (D : ValuativeCommSq f)
    (l₁ l₂ : Spec (.of D.R) ⟶ X)
    (hl₁ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ l₁ = D.i₁)
    (hl₂ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ l₂ = D.i₁)
    (hw : l₁ ≫ f = l₂ ≫ f) :
    Limits.pullback.diagonal f (D.i₁ (IsLocalRing.closedPoint D.K)) ⤳
      Limits.pullback.lift l₁ l₂ hw (IsLocalRing.closedPoint D.R) := by
  let Y : Scheme := Limits.pullback f f
  let d : X ⟶ Y := Limits.pullback.diagonal f
  let q : Spec (.of D.R) ⟶ Y := Limits.pullback.lift l₁ l₂ hw
  let qK : Spec (.of D.K) ⟶ Y := D.i₁ ≫ d
  have hqgen : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ q = qK := by
    refine Limits.pullback.hom_ext ?_ ?_
    · simp only [q, qK, d, Category.assoc, Limits.pullback.lift_fst,
        Limits.pullback.diagonal_fst, Category.comp_id, hl₁]
    · simp only [q, qK, d, Category.assoc, Limits.pullback.lift_snd,
        Limits.pullback.diagonal_snd, Category.comp_id, hl₂]
  have hmapcp : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))
      (IsLocalRing.closedPoint D.K) = genericPoint (Spec (.of D.R)) := by
    apply PrimeSpectrum.ext
    rw [genericPoint_eq_bot_of_affine]
    change (IsLocalRing.maximalIdeal D.K).comap (algebraMap D.R D.K) = ⊥
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField D.K)]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective D.R D.K)
  let p : X := D.i₁ (IsLocalRing.closedPoint D.K)
  let t : Y := qK (IsLocalRing.closedPoint D.K)
  let y : Y := q (IsLocalRing.closedPoint D.R)
  have hqPoint : q (genericPoint (Spec (.of D.R))) = t := by
    rw [← hmapcp]
    change (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ q)
      (IsLocalRing.closedPoint D.K) = _
    rw [hqgen]
  have hspec : t ⤳ y := by
    have hgen := (genericPoint_spec (Spec (.of D.R))).specializes
      (Set.mem_univ (IsLocalRing.closedPoint D.R))
    have h := hgen.map q.continuous
    change q (genericPoint (Spec (.of D.R))) ⤳ q (IsLocalRing.closedPoint D.R) at h
    simpa only [hqPoint, y] using h
  have htp : d p = t := by
    rfl
  exact htp ▸ hspec

/-- The two dotted arrows of a valuative square agree at the closed point.  This is the
geometric heart of the implication from the restricted criterion to uniqueness: unless the two
arrows already agree there, the two images of the closed point in `X ×_S X` are a nontrivial
specialization of the image of the diagonal, so an integral closed subscheme of `X ×_S X`
realizes it, and the discrete valuation ring produced inside the residue field of a generic
point of `X` yields two lifts of one square in the restricted criterion. -/
private theorem closedPoint_eq_of_restrictedValuativeUniqueness
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (h4 : RestrictedValuativeUniqueness f) (D : ValuativeCommSq f)
    (l₁ l₂ : Spec (.of D.R) ⟶ X)
    (hl₁ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ l₁ = D.i₁)
    (hl₁' : l₁ ≫ f = D.i₂)
    (hl₂ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ l₂ = D.i₁)
    (hl₂' : l₂ ≫ f = D.i₂) :
    l₁ (IsLocalRing.closedPoint D.R) = l₂ (IsLocalRing.closedPoint D.R) := by
  classical
  let Y : Scheme := Limits.pullback f f
  let d : X ⟶ Y := Limits.pullback.diagonal f
  let q : Spec (.of D.R) ⟶ Y := Limits.pullback.lift l₁ l₂ (hl₁'.trans hl₂'.symm)
  have hqfst : q ≫ Limits.pullback.fst f f = l₁ := Limits.pullback.lift_fst _ _ _
  have hqsnd : q ≫ Limits.pullback.snd f f = l₂ := Limits.pullback.lift_snd _ _ _
  let y : Y := q (IsLocalRing.closedPoint D.R)
  obtain ⟨η, hη, hηp⟩ := exists_genericPoint_specializes (D.i₁ (IsLocalRing.closedPoint D.K))
  have hty : d η ⤳ y := (hηp.map d.continuous).trans
    (diagonal_specializes_pullbackLift_closedPoint f D l₁ l₂ hl₁ hl₂ _)
  rw [← hqfst, ← hqsnd]
  change Limits.pullback.fst f f y = Limits.pullback.snd f f y
  by_cases hne : d η = y
  · rw [← hne]
    change (d ≫ Limits.pullback.fst f f) η = (d ≫ Limits.pullback.snd f f) η
    rw [Limits.pullback.diagonal_fst, Limits.pullback.diagonal_snd]
  · have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst f f ≫ f)
    obtain ⟨B, hB, hBfrac, m, hm, hmcp⟩ :=
      exists_isDiscreteValuationRing_subring_of_specializes_of_isImmersion d η hty hne
        (RingEquiv.refl _)
    have hfield₁ : Spec.map (CommRingCat.ofHom B.subtype) ≫ m ≫ Limits.pullback.fst f f =
        X.fromSpecResidueField η := by
      simp [reassoc_of% hm, d, CommRingCat.ofHom_id, Spec.map_id]
    have hfield₂ : Spec.map (CommRingCat.ofHom B.subtype) ≫ m ≫ Limits.pullback.snd f f =
        X.fromSpecResidueField η := by
      simp [reassoc_of% hm, d, CommRingCat.ofHom_id, Spec.map_id]
    let sq : CommSq (X.fromSpecResidueField η) (Spec.map (CommRingCat.ofHom B.subtype)) f
        ((m ≫ Limits.pullback.fst f f) ≫ f) := ⟨by
          rw [← hfield₁]
          rfl⟩
    let L₁ : sq.LiftStruct := ⟨_, hfield₁, rfl⟩
    let L₂ : sq.LiftStruct :=
      ⟨_, hfield₂, by simp only [Category.assoc, Limits.pullback.condition]⟩
    have := h4 η hη B hB hBfrac _ sq
    rw [← hmcp]
    exact congrArg (fun L => L.l (@IsLocalRing.closedPoint B _
      (@IsDiscreteValuationRing.toIsLocalRing B _ _ hB))) (Subsingleton.elim L₁ L₂)

/-- The restricted criterion implies separatedness.  This is the only nontrivial implication of
`AlgebraicGeometry.isSeparated_tfae_of_locallyOfFiniteType`. -/
private theorem isSeparated_of_restrictedValuativeUniqueness
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (h4 : RestrictedValuativeUniqueness f) : IsSeparated f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine IsSeparated.of_valuativeCriterion f fun D => ⟨?_⟩
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  exact CommSq.LiftStruct.ext (eq_of_closedPoint_eq_of_specMap_comp_eq l₁ l₂
    (closedPoint_eq_of_restrictedValuativeUniqueness f h4 D l₁ l₂ hl₁ hl₁' hl₂ hl₂')
    (hl₁.trans hl₂.symm))

/-- **Stacks Project, Tag 0207.** For a morphism locally of finite type over a locally
Noetherian scheme, separatedness is equivalent to uniqueness in the valuative criterion; it
suffices to use discrete valuation rings, and even the discrete valuation subrings of the
function fields of the irreducible components of the source. -/
@[stacks 0207, ega "II 7.2.3" "Noetherian/DVR case"]
theorem isSeparated_tfae_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    List.TFAE
      [ IsSeparated f,
        ValuativeCriterion.Uniqueness f,
        ∀ (D : ValuativeCommSq f),
          IsDiscreteValuationRing D.R → Subsingleton D.commSq.LiftStruct,
        ∀ (η : X), η ∈ genericPoints X →
          ∀ (A : Subring (X.residueField η)),
            IsDiscreteValuationRing A →
              IsFractionRing A (X.residueField η) →
                ∀ (i₂ : Spec (.of A) ⟶ S)
                  (sq : CommSq (X.fromSpecResidueField η)
                    (Spec.map (CommRingCat.ofHom A.subtype)) f i₂),
                  Subsingleton sq.LiftStruct ] := by
  tfae_have 1 → 2 := fun _ D => IsSeparated.valuativeCriterion f D
  tfae_have 2 → 3 := fun hf D _ => hf D
  tfae_have 3 → 4 := fun hf η _ A hA _ i₂ sq =>
    hf { R := A, K := X.residueField η, i₁ := X.fromSpecResidueField η, i₂, commSq := sq } hA
  tfae_have 4 → 1 := isSeparated_of_restrictedValuativeUniqueness f
  tfae_finish

end Tfae

end AlgebraicGeometry

end
