module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.LerayVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.NoetherNormalization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.StrictHenselizationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalLocalExactSequence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomological dimension of affine curves

Let `K` be a field and `X` an affine scheme of finite type over `K` of dimension at most one.
Then `cd(X) ≤ 1 + cd(K)` (Stacks 0F0S). Over a separably closed field this is `cd(X) ≤ 1`, which
is part (2) of Stacks 03SC after passing to an algebraic closure, an extension along which étale
cohomology does not change (Stacks 03SI).

## Main results

* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_one_of_isSepClosed`: `cd(X) ≤ 1` for
  an affine scheme of finite type and dimension at most one over a separably closed field.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_one_add`: **Stacks 0F0S**,
  `cd(X) ≤ 1 + cd(K)` for an affine scheme of finite type and dimension at most one over a field
  `K`.
* `Scheme.etaleCohomologicalDimension_le_unbotD_add_of_topologicalKrullDim_le_one`: the same bound
  written `cd(X) ≤ dim(X) + cd(K)`, the dimension of the empty scheme read as `0`.

## Implementation notes

The vanishing of `H^q` above degree one for a torsion sheaf on an affine curve over an
algebraically closed field is statement (2) of Situation 0A52,
`Stacks.EtaleCohomology.TorsionSheafSituation.isAffineVanishingAboveDegreeOne` (Tag 0A54, part of
Theorem 03SC).

The stalk of a higher direct image at a geometric point (Stacks 03Q9) enters as a vanishing
criterion, `AlgebraicGeometry.isZero_stalk_rightDerived_iff_subsingleton_sheafH`.

## References

* [Stacks Project, Tag 0F0S](https://stacks.math.columbia.edu/tag/0F0S)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **An affine curve over a separably closed field has cohomological dimension at most one.**
Let `Ω` be separably closed and `Y` an affine scheme of finite type over `Ω` of dimension at most
one. Then `cd(Y) ≤ 1`.

Over an algebraic closure `Ω̄` of `Ω`, statement (2) of Situation 0A52 (Tag 0A54, part of Theorem
03SC) kills the cohomology of the torsion sheaf `p⁻¹F` on the affine curve `Y_{Ω̄}` above degree
one; as `Ω̄/Ω` is purely inseparable, `p : Y_{Ω̄} ⟶ Y` is a universal homeomorphism, so restriction
along it is bijective on étale cohomology (Stacks 03SI (3)), and the inverse image of a torsion
sheaf is torsion. -/
@[sga "4 IX 5.7" "more general", sga "4 X 5.2" "special case", sga "4½ Arcata 3.3.6" "more general"]
public theorem etaleCohomologicalDimension_le_one_of_isSepClosed
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {Y : Scheme.{u}} [IsAffine Y]
    (π : Y ⟶ Spec (.of Ω)) [LocallyOfFiniteType π] (hY : topologicalKrullDim Y ≤ 1) :
    etaleCohomologicalDimension Y ≤ 1 := by
  refine etaleCohomologicalDimension_le Y 1 fun F hF q hq => ?_
  have hq' : 1 < q := by exact_mod_cast hq
  let Ω' := AlgebraicClosure Ω
  let p := Stacks.EtaleCohomology.scalarExtensionFst Ω Ω' π
  have hp : UniversalHomeomorphism p :=
    Stacks.EtaleCohomology.scalarExtensionFst_universalHomeomorphism_of_isPurelyInseparable Ω Ω' π
  have : IsIntegralHom p :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective p).1 hp).1
  let π' : Stacks.EtaleCohomology.scalarExtension Ω Ω' π ⟶ Spec (.of Ω') :=
    pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap Ω Ω')))
  have hdim : topologicalKrullDim (Stacks.EtaleCohomology.scalarExtension Ω Ω' π) ≤ 1 :=
    (topologicalKrullDim_le_of_isIntegralHom p).trans hY
  have hT := Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage.{u, 0} p F hF
  let S : Stacks.EtaleCohomology.TorsionSheafSituation.{u, 0} :=
    { k := Ω'
      X := Stacks.EtaleCohomology.scalarExtension Ω Ω' π
      structureMorphism := π'
      dimension_le_one := hdim
      F := (Stacks.EtaleCohomology.etaleAbelianInverseImage.{u, 0} p).obj F
      isTorsion := hT }
  have h₀ : Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((Stacks.EtaleCohomology.etaleAbelianInverseImage.{u, 0} p).obj F) q) :=
    S.isAffineVanishingAboveDegreeOne.subsingleton (X := S.X) hq'
  exact
    (Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{u,
      0, u + 1} p F q).1.subsingleton

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open IsLocalRing

section FieldPoint

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- If the ordinary local ring at the image of a geometric point is a field, its strict
henselization in the chosen tower is integral over it: a strict henselization is ind-étale, hence
algebraic, over a local domain. -/
theorem isIntegral_strictHenselization_of_isField
    (hR : IsField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))) :
    Algebra.IsIntegral ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (geometricHenselizationTower S s).strictHenselization := by
  have : IsDomain ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))) := hR.isDomain
  have := isAlgebraic_of_isHenselization ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
    (geometricHenselizationTower S s).strictHenselization
    (separableClosure (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
      s.residueField)
    (FractionRing ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
  let := hR.toField
  exact Algebra.IsAlgebraic.isIntegral

/-- **The étale local ring at a geometric point is a field when the ordinary local ring is.** Its
strict henselization is a domain (Stacks 06DI, a field being a normal domain) which is integral
over the field, hence a field. -/
theorem isField_etaleLocalRing_of_isField_stalk
    (hR : IsField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))) :
    IsField ↥(etaleLocalRing B S hS s) := by
  have : IsDomain ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))) := hR.isDomain
  have : IsIntegrallyClosed ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))) := by
    let := hR.toField
    infer_instance
  obtain ⟨hdom, -⟩ := isDomain_and_isIntegrallyClosed_of_isHenselization
    ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
    (geometricHenselizationTower S s).strictHenselization
    (separableClosure (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
      s.residueField)
  have := isIntegral_strictHenselization_of_isField S s hR
  exact (etaleLocalRingEquivStrictHenselization B S hS s).symm.toMulEquiv.isField
    (isField_of_isIntegral_of_isField' hR)

/-- **The étale local ring at a geometric point is separably closed when it is a field**: it is
then its own residue field, which is a separable closure of the residue field of the ordinary
local ring. -/
theorem isSepClosed_etaleLocalRing_of_isField (h : IsField ↥(etaleLocalRing B S hS s)) :
    letI := h.toField
    IsSepClosed ↥(etaleLocalRing B S hS s) := by
  have hm : IsLocalRing.maximalIdeal ↥(etaleLocalRing B S hS s) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.1 h
  have : IsSepClosed (ResidueField ↥(etaleLocalRing B S hS s)) :=
    IsSepClosure.sep_closed (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
  let e : ↥(etaleLocalRing B S hS s) ≃+* ResidueField ↥(etaleLocalRing B S hS s) :=
    RingEquiv.ofBijective (IsLocalRing.residue _)
      ⟨(injective_iff_map_eq_zero _).2 fun x hx => by
          have hx' : x ∈ IsLocalRing.maximalIdeal ↥(etaleLocalRing B S hS s) :=
            (IsLocalRing.residue_eq_zero_iff x).1 hx
          rwa [hm, Ideal.mem_bot] at hx',
        Ideal.Quotient.mk_surjective⟩
  let := h.toField
  exact IsSepClosed.of_ringEquiv e

/-- **Over a field, the strict henselization at a geometric point is integral over the base.**
The point of `Spec K` is the closed point of the local ring `K`, where the canonical morphism from
the spectrum of the local ring is an isomorphism, and the étale local ring is integral over the
ordinary one. -/
theorem isIntegralHom_strictHenselizationToBase_of_field {K : Type u} [Field K]
    (hS : B.Contains (Spec (.of K))) (s : GeometricPoint (Spec (.of K))) :
    IsIntegralHom (strictHenselizationToBase B (Spec (.of K)) hS s) := by
  have hR : IsField ↥((Spec (.of K)).presheaf.stalk (s.hom (closedPoint s.residueField))) := by
    obtain ⟨x, hx⟩ : ∃ x, x = s.hom (closedPoint s.residueField) := ⟨_, rfl⟩
    rw [← hx]
    obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  have h₁ : IsIntegralHom (Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing B
      (Spec (.of K)) hS s))) := by
    rw [IsIntegralHom.SpecMap_iff]
    have := isIntegral_strictHenselization_of_isField (Spec (.of K)) s hR
    have hfac : structureSheafStalkFromLocalRing B (Spec (.of K)) hS s =
        (etaleLocalRingEquivStrictHenselization B (Spec (.of K)) hS s).toRingHom.comp
          (algebraMap _ (geometricHenselizationTower (Spec (.of K)) s).strictHenselization) :=
      RingHom.ext fun r => ((etaleLocalRing_strictHenselization_canonical B (Spec (.of K)) hS s
        (geometricHenselizationTower (Spec (.of K)) s)).property.1 r).symm
    rw [hfac]
    exact RingHom.IsIntegral.trans _ _ (algebraMap_isIntegral_iff.2 this)
      (RingHom.isIntegral_of_surjective _
        (etaleLocalRingEquivStrictHenselization B (Spec (.of K)) hS s).surjective)
  have h₂ : ∀ x : Spec (.of K), IsIntegralHom ((Spec (.of K)).fromSpecStalk x) := by
    intro x
    obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [← Spec_stalkClosedPointIso]
    infer_instance
  have := h₂ (s.hom (closedPoint s.residueField))
  exact inferInstanceAs (IsIntegralHom (Spec.map _ ≫ _))

end FieldPoint

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

/-- **Stacks Project, Tag 0F0S.** Let `K` be a field and `X` an affine scheme of finite type over
`K` of dimension at most one. Then `cd(X) ≤ 1 + cd(K)`.

The source's statement is for `X` of dimension one; dimension at most one is no harder, and
contains it.

The proof is the source's. Let `𝓕` be a torsion sheaf on `X_étale`. By the Leray spectral
sequence for `g : X ⟶ Spec K` (`Stacks.EtaleCohomology.LerayVanishing`) it suffices that
`H^p(Spec K, R^qg_*𝓕) = 0` for `p + q > 1 + cd(K)`. For `q ≤ 1` this is the definition of
`cd(K)`, `R^qg_*𝓕` being torsion (Stacks 0DDD). For `q ≥ 2` the sheaf `R^qg_*𝓕` vanishes: its
stalk at a geometric point is the cohomology of the base change of `X` to the strict
henselization, which is a separable closure `Ω` of `K` (Stacks 03Q9), and `X_Ω` is an affine curve
over a separably closed field, of cohomological dimension at most one by
`etaleCohomologicalDimension_le_one_of_isSepClosed`. -/
@[stacks 0F0S "for `X` of dimension at most one, which contains the source's dimension one",
  sga "4 X 5.2" "special case",
  sga "4 XIV 3.2" "special case",
  sga "4½ Arcata 4.6.4" "special case",
  sga "5 I 1.5.2" "special case"]
public theorem etaleCohomologicalDimension_le_one_add
    {K : Type u} [Field K] {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (.of K))
    [LocallyOfFiniteType g] (hX : topologicalKrullDim X ≤ 1) :
    etaleCohomologicalDimension X ≤ 1 + etaleCohomologicalDimension (Spec (.of K)) := by
  let B := BigEtaleSite.containing (Spec (.of K))
  have hS : B.Contains (Spec (.of K)) := BigEtaleSite.contains_containing _
  -- the higher direct images in degrees `≥ 2` vanish
  have hvan : ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F → ∀ q : ℕ, 2 ≤ q →
        IsZero (((Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} g).rightDerived q).obj
          F) := by
    intro F hF q hq
    let G := ((Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} g).rightDerived q).obj F
    have hiso : IsIso (0 : G ⟶ G) := by
      refine (Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun s => ?_
      have hsrc : IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s.hom).obj G) := by
        refine (isZero_stalk_rightDerived_iff_subsingleton_sheafH B hS g s F q).2 ?_
        have hfield := isField_etaleLocalRing_of_isField_stalk B (Spec (.of K)) hS s (by
          obtain ⟨x, hx⟩ : ∃ x, x = s.hom (IsLocalRing.closedPoint s.residueField) := ⟨_, rfl⟩
          rw [← hx]
          obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
          exact (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
            (Field.toIsField K))
        let := hfield.toField
        have := isSepClosed_etaleLocalRing_of_isField B (Spec (.of K)) hS s hfield
        have := isIntegralHom_strictHenselizationToBase_of_field B hS s
        have hdim : topologicalKrullDim (strictHenselizationBaseChange B hS g s) ≤ 1 :=
          (topologicalKrullDim_le_of_isIntegralHom
            (strictHenselizationBaseChangeToSource B hS g s)).trans hX
        have hcd := etaleCohomologicalDimension_le_one_of_isSepClosed
          (Ω := ↥(etaleLocalRing B (Spec (.of K)) hS s))
          (strictHenselizationBaseChangeToStrictHenselization B hS g s) hdim
        exact isEtaleCohomologyBound_etaleCohomologicalDimension _ _
          (Stacks.Torsion.torsionSheafProperty_of_iso _
            ((Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleAbelianInverseImage
              (strictHenselizationBaseChangeToSource B hS g s)).app F).symm
            (Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage.{u, 0} _ F hF)) q
          (lt_of_le_of_lt hcd (by exact_mod_cast hq))
      exact ⟨⟨0, hsrc.eq_of_src _ _, hsrc.eq_of_src _ _⟩⟩
    refine (IsZero.iff_id_eq_zero G).2 ?_
    rw [← IsIso.hom_inv_id (0 : G ⟶ G), zero_comp]
  -- the Leray spectral sequence
  induction hK : etaleCohomologicalDimension (Spec (.of K)) using ENat.recTopCoe with
  | top => simp
  | coe c =>
    refine etaleCohomologicalDimension_le X _ fun F hF n hn => ?_
    have hn' : 1 + c < n := by exact_mod_cast hn
    open Stacks.EtaleCohomology.LerayVanishing in
    refine subsingleton_sheafH_of_forall_subsingleton_sheafH_rightDerived g F n fun q hq => ?_
    rcases lt_or_ge q 2 with hq2 | hq2
    · have hT :=
        Stacks.EtaleCohomology.torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{0}
          g q F hF
      refine isEtaleCohomologyBound_etaleCohomologicalDimension _ _ hT (n - q) ?_
      rw [hK]
      exact_mod_cast (by omega : c < n - q)
    · exact Sheaf.subsingleton_H_of_isZero (hvan F hF q hq2) _

/-- **The bound `cd(Y) ≤ dim(Y) + cd(K)` in dimension at most one.** For an affine scheme `Y` of
finite type over a field `K` with `dim Y ≤ 1`, `cd(Y) ≤ dim(Y) + cd(K)`, the dimension of the empty
scheme being read as `0`.

The empty scheme and dimension zero are integral over `Spec K` (a finite morphism to
`𝔸^0_K = Spec K` by Noether normalization, Stacks 0CBI); dimension one is
`etaleCohomologicalDimension_le_one_add`. These are the cases
`dim(X) = 0` and `dim(X) = 1` of the source's induction. -/
@[sga "4 X 5.2" "special case", sga "4 XIV 3.2" "special case"]
public theorem etaleCohomologicalDimension_le_unbotD_add_of_topologicalKrullDim_le_one
    {K : Type u} [Field K] {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType g] (hY : topologicalKrullDim Y ≤ 1) :
    etaleCohomologicalDimension Y ≤
      (topologicalKrullDim Y).unbotD 0 + etaleCohomologicalDimension (Spec (.of K)) := by
  induction hd : topologicalKrullDim Y using WithBot.recBotCoe with
  | bot =>
    have : IsEmpty Y := by
      rw [topologicalKrullDim, Order.krullDim_eq_bot_iff] at hd
      exact ⟨fun y => hd.false ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    simpa using etaleCohomologicalDimension_le_of_isEmpty g
  | coe a =>
    rw [hd] at hY
    have ha : a ≤ 1 := by exact_mod_cast hY
    rcases (show a = 0 ∨ a = 1 by
      induction a using ENat.recTopCoe with
      | top => simp at ha
      | coe b =>
        have : b ≤ 1 := by exact_mod_cast ha
        interval_cases b <;> simp) with rfl | rfl
    · have h₀ := etaleCohomologicalDimension_le_affineSpace g 0 (by rw [hd]; rfl)
      have h₁ := etaleCohomologicalDimension_le_of_isIntegralHom
        (𝔸(ULift (Fin 0); Spec (.of K)) ↘ Spec (.of K))
      simpa using h₀.trans h₁
    · simpa using etaleCohomologicalDimension_le_one_add g (by rw [hd]; rfl)

end AlgebraicGeometry.Scheme

end
