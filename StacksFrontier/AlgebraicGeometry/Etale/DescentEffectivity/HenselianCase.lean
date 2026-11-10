module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.BaseGluing
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.EssSurjHenselianReduction
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.HenselianFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.InvariantOpenOverEffectiveOpen
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.InvariantSplitDescended
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale descent along surjective integral morphisms

This file proves [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP): for a surjective
integral morphism `f : X ⟶ S`, the functor of Tag 0BTI taking a scheme étale over `S` to its
canonical descent datum relative to `X/S` restricts to an equivalence between schemes
quasi-compact, separated and étale over `S` and descent data `(V, φ)` relative to `X/S` with `V`
quasi-compact, separated and étale over `X`.

Full faithfulness is
`AlgebraicGeometry.fullyFaithful_quasiCompactSeparatedEtaleDescentFunctor_of_isIntegralHom`, and
`AlgebraicGeometry.isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_isHenselianCase`
reduces essential surjectivity to the henselian case `AlgebraicGeometry.IsHenselianCase`.

## Main results

* `AlgebraicGeometry.exists_iso_spec_comp_specMap_eq`: an affine scheme over `Spec R` is
  `Spec B` over `Spec R` for a ring map `R →+* B`.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_preimage_changeDatum`: étale
  effectivity over an open of the base passes to its preimage under any base change.
* `AlgebraicGeometry.DescentDatum.Descended.changeOfComp`: a scheme descending the base change
  of a datum along `ι` descends its iterated base change along `j` and then `c`, whenever
  `c ≫ j` factors through `ι`.
* `AlgebraicGeometry.DescentDatum.Descended.isFinite_over_hom`: a datum descended by a scheme
  finite over the base is finite over `X`.
* `AlgebraicGeometry.DescentDatum.isFinite_pullbackSnd_specMap_quotientMk_of_descended`: the
  closed fibre of a datum over `Spec B` is finite when a finite scheme descends the closed fibre
  over the base.
* `AlgebraicGeometry.isHenselianCase`: **the henselian case of Tag 0BTP.**
* `AlgebraicGeometry.isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_isIntegralHom`:
  **[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP).**

## Implementation notes

The source writes `Z^h = V(IAʰ) ≅ Z` and transports `U_Z` along the isomorphism. Here `U_Z` lives
over the reduced induced scheme on the part of an affine chart outside `U₀`, and is pulled back
along the factorization of `Spec (Aʰ ⧸ IAʰ) ⟶ T` through that scheme
(`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedLift`). That factorization
exists because `Aʰ ⧸ IAʰ ≅ A ⧸ I` is reduced, `I` being radical, and it is all that is needed of
the isomorphism.

## References

* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
* [Stacks Project, Tag 0BTN](https://stacks.math.columbia.edu/tag/0BTN)
* [Stacks Project, Tag 09ZS](https://stacks.math.columbia.edu/tag/09ZS)
* [Stacks Project, Tag 09XK](https://stacks.math.columbia.edu/tag/09XK)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

/-- **An affine scheme over `Spec R` is the spectrum of an `R`-algebra, over `Spec R`.** The
algebra is the ring of global sections, with the ring map induced by the structure morphism. -/
theorem exists_iso_spec_comp_specMap_eq {R : Type u} [CommRing R] {Y : Scheme.{u}} [IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of R)) :
    ∃ (B : Type u) (_ : CommRing B) (b : R →+* B) (e : Y ≅ Spec (CommRingCat.of B)),
      e.hom ≫ Spec.map (CommRingCat.ofHom b) = p := by
  refine ⟨Γ(Y, ⊤), inferInstance, ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop).hom,
    Y.isoSpec, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality]
  simp

namespace DescentDatum

/-- **Étale effectivity over an open of the base passes to its preimage under any base change.** If
a datum relative to `X/S` is étale effective over `U₀ ⊆ S`, its base change along `w : T ⟶ S` is
étale effective over `w⁻¹(U₀)`. -/
theorem isEtaleEffective_baseDatum_preimage_changeDatum {S X T : Scheme.{u}} {f : X ⟶ S}
    (D : DescentDatum f) [Etale D.over.hom] (w : T ⟶ S) {U₀ : S.Opens}
    (heff : (D.baseDatum U₀).IsEtaleEffective) :
    ((D.changeDatum w).baseDatum (w ⁻¹ᵁ U₀)).IsEtaleEffective := by
  have h₁ : ((D.changeDatum U₀.ι).changeDatum (w ∣_ U₀)).IsEtaleEffective :=
    isEtaleEffective_pullbackSquare (changePullbackFunctor _ _) heff
  have h₂ := (isEtaleEffective_changeDatum_comp_iff D).mp h₁
  rw [morphismRestrict_ι] at h₂
  have h₃ := (isEtaleEffective_changeDatum_opensRange_comp D w (w ⁻¹ᵁ U₀).ι).mpr h₂
  rwa [Scheme.Opens.opensRange_ι] at h₃

namespace Descended

variable {S X : Scheme.{u}} {f : X ⟶ S} {D : DescentDatum f}

/-- **A datum descended by a scheme finite over the base is finite over `X`.** -/
theorem isFinite_over_hom (Q : D.Descended) [IsFinite Q.base.hom] : IsFinite D.over.hom :=
  MorphismProperty.of_isPullback Q.isPullback.flip ‹_›

variable {Z T T' : Scheme.{u}} {ι : Z ⟶ S} {j : T ⟶ S} {c : T' ⟶ T} {k : T' ⟶ Z}

/-- **Base change of a descended scheme along a factorization.** A scheme descending the base
change of `D` along `ι : Z ⟶ S` descends, after pulling it back along `k : T' ⟶ Z`, the base change
of `D` along `j : T ⟶ S` followed by `c : T' ⟶ T`, as soon as `k ≫ ι = c ≫ j`. -/
def changeOfComp (hk : k ≫ ι = c ≫ j) (Q : (D.changeDatum ι).Descended) :
    ((D.changeDatum j).changeDatum c).Descended :=
  (pullbackSquare (changeCompFunctor f j c) (changeCongr hk (Q.changeComp k))).ofDatumIso
    (changeCompDatumIso j c D).symm

/-- The descended scheme of `changeOfComp hk Q` is the pullback of `Q.base` along `k`, pulled back
further along the identity of `T'`. -/
@[simp]
lemma changeOfComp_base (hk : k ≫ ι = c ≫ j) (Q : (D.changeDatum ι).Descended) :
    (changeOfComp hk Q).base = (Over.pullback (𝟙 T')).obj ((Over.pullback k).obj Q.base) :=
  rfl

/-- The descended scheme of `changeOfComp hk Q` is étale over `T'` when `Q.base` is étale over
`Z`. -/
instance etale_changeOfComp_base_hom (hk : k ≫ ι = c ≫ j) (Q : (D.changeDatum ι).Descended)
    [Etale Q.base.hom] : Etale (changeOfComp hk Q).base.hom := by
  rw [changeOfComp_base]
  infer_instance

/-- The descended scheme of `changeOfComp hk Q` is finite over `T'` when `Q.base` is finite over
`Z`. -/
instance isFinite_changeOfComp_base_hom (hk : k ≫ ι = c ≫ j) (Q : (D.changeDatum ι).Descended)
    [IsFinite Q.base.hom] : IsFinite (changeOfComp hk Q).base.hom := by
  rw [changeOfComp_base]
  change IsFinite (pullback.snd (pullback.snd Q.base.hom k) (𝟙 T'))
  infer_instance

end Descended

/-- **A datum whose base change along `c : Z ⟶ S` is descended by a finite scheme is finite over
every `Z' ⟶ X` lying over `Z`.** If `q : Z' ⟶ X` and `r : Z' ⟶ Z` satisfy `q ≫ f = r ≫ c`, then
`V ×_X Z' ⟶ Z'` is finite. -/
theorem isFinite_pullbackSnd_of_descended_changeDatum {S X Z Z' : Scheme.{u}} {f : X ⟶ S}
    (D : DescentDatum f) {c : Z ⟶ S} (QZ : (D.changeDatum c).Descended) [IsFinite QZ.base.hom]
    (q : Z' ⟶ X) (r : Z' ⟶ Z) (hq : q ≫ f = r ≫ c) :
    IsFinite (pullback.snd D.over.hom q) := by
  have h₁ : IsFinite (D.changeDatum c).over.hom := QZ.isFinite_over_hom
  have h₂ : IsFinite (pullback.snd D.over.hom (pullback.fst f c)) := by
    let P := changePullbackFunctor f c
    have hcomm : (P.objIso D).hom.left ≫ ((Over.pullback (pullback.fst f c)).obj D.over).hom =
        (D.changeDatum c).over.hom := (P.objIso D).hom.w
    have : IsIso (P.objIso D).hom.left := by
      change IsIso ((Over.forget _).map (P.objIso D).hom)
      infer_instance
    have heq : ((Over.pullback (pullback.fst f c)).obj D.over).hom =
        inv (P.objIso D).hom.left ≫ (D.changeDatum c).over.hom := by
      rw [← hcomm, IsIso.inv_hom_id_assoc]
    change IsFinite ((Over.pullback (pullback.fst f c)).obj D.over).hom
    rw [heq]
    infer_instance
  have hu : pullback.lift q r hq ≫ pullback.fst f c = q := pullback.lift_fst _ _ _
  have heq : pullback.snd D.over.hom (pullback.lift q r hq ≫ pullback.fst f c) =
      (pullbackLeftPullbackSndIso D.over.hom (pullback.fst f c) (pullback.lift q r hq)).inv ≫
        pullback.snd (pullback.snd D.over.hom (pullback.fst f c)) (pullback.lift q r hq) := by
    rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
  rw [← hu, heq]
  infer_instance

/-- **The closed fibre of a datum over `Spec B` is finite as soon as a finite scheme descends the
closed fibre over the base.** Let `f : X ⟶ Spec A` with `X = Spec B` through `e`, and let `(V, φ)`
be a datum relative to `f` whose base change to `Spec (A ⧸ I)` is descended by a scheme finite over
`Spec (A ⧸ I)`. Then `V ×_{Spec B} Spec (B ⧸ IB)` is finite over `Spec (B ⧸ IB)`. -/
theorem isFinite_pullbackSnd_specMap_quotientMk_of_descended {A : Type u} [CommRing A]
    (I : Ideal A) {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} (D : DescentDatum f)
    {B : Type u} [CommRing B] (b : A →+* B) (e : X ≅ Spec (CommRingCat.of B))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom b) = f)
    (QZ : (D.changeDatum (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Descended)
    [IsFinite QZ.base.hom] :
    IsFinite (pullback.snd (D.over.hom ≫ e.hom)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map b))))) := by
  have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map b))) ≫
      Spec.map (CommRingCat.ofHom b) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map b) b Ideal.le_comap_map)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk Ideal.le_comap_map]
  have h₃ := D.isFinite_pullbackSnd_of_descended_changeDatum QZ
    (pullback.fst e.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map b)))))
    (pullback.snd e.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map b)))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map b) b Ideal.le_comap_map)))
    (by rw [← he, ← Category.assoc, pullback.condition, Category.assoc, hq, Category.assoc])
  have heq : pullback.snd (D.over.hom ≫ e.hom)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map b)))) =
      (pullbackRightPullbackFstIso e.hom _ D.over.hom).inv ≫
        pullback.snd D.over.hom (pullback.fst e.hom _) ≫ pullback.snd e.hom _ := by
    rw [Iso.eq_inv_comp, pullbackRightPullbackFstIso_hom_snd]
  rw [heq]
  infer_instance

end DescentDatum

/-- **The henselian case of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP).** Over
the henselization `Aʰ` of an affine chart `A = Γ(T, W')` at the ideal `I` cutting out the part of
the chart outside `U₀`, a quasi-compact separated étale datum relative to a finite surjective
`Y ⟶ T` is étale effective, given effectivity over `U₀` and a finite étale scheme descending the
datum over the reduced induced scheme on `W' ∖ U₀`. -/
theorem isHenselianCase : IsHenselianCase.{u} := by
  intro T Y g hT hTN hg hgs D hD hqc hsep U₀ W' hW' I hIrad hIfg hU Ah _ _ hh hun Q hQe hQf heff
  set j : Spec (CommRingCat.of Ah) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W') Ah)) ≫ hW'.fromSpec with hj
  set I' : Ideal Ah := I.map (algebraMap Γ(T, W') Ah) with hI'
  set D₁ := D.changeDatum j
  have hqc₁ : QuasiCompact D₁.over.hom := D.quasiCompact_changeDatum_over_hom j hqc
  have hsep₁ : IsSeparated D₁.over.hom := D.isSeparated_changeDatum_over_hom j hsep
  have : IsAffine (pullback g j) := isAffine_of_isAffineHom (pullback.snd g j)
  obtain ⟨B, _, b, e, he⟩ := exists_iso_spec_comp_specMap_eq (pullback.snd g j)
  have hbfin : (b : Ah →+* B).Finite := by
    rw [← CommRingCat.hom_ofHom b, ← IsFinite.SpecMap_iff,
      show Spec.map (CommRingCat.ofHom b) = e.inv ≫ pullback.snd g j by
        rw [← he, Iso.inv_hom_id_assoc]]
    infer_instance
  let : Algebra Ah B := b.toAlgebra
  have : Algebra.IsIntegral Ah B := ⟨hbfin.to_isIntegral⟩
  have hB : HenselianPair B (I'.map b) := henselianPair_map_of_isIntegral I' hh
  have hpair := flat_henselization_and_bijective_quotientMap Γ(T, W') I Ah hh hun
  have hbij := bijective_quotientMap_congr (algebraMap Γ(T, W') Ah) (pow_one I) (hpair.2 1)
  have : _root_.IsReduced (Γ(T, W') ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hIrad
  have : _root_.IsReduced (Ah ⧸ I') :=
    isReduced_of_injective (RingEquiv.ofBijective _ hbij).symm
      (RingEquiv.ofBijective _ hbij).symm.injective
  set c := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I'))
  have hzl : ∀ x : PrimeSpectrum Ah, PrimeSpectrum.comap (algebraMap Γ(T, W') Ah) x ∈
      ((hW'.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W')).Opens) : Set (Spec Γ(T, W'))) ↔
      x ∉ PrimeSpectrum.zeroLocus (I' : Set Ah) := fun x ↦ by
    rw [hU]
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
      Ideal.map_le_iff_le_comap, hI']
    rfl
  have hrange : Set.range (c ≫ j) ⊆ (W' : Set T) ∩ (U₀ : Set T)ᶜ := by
    rintro _ ⟨x, rfl⟩
    have hx : c x ∈ PrimeSpectrum.zeroLocus (I' : Set Ah) := by
      rw [← range_spec_map_quotient_mk]; exact ⟨x, rfl⟩
    exact ⟨by rw [← hW'.range_fromSpec]; exact ⟨_, rfl⟩, fun hmem ↦ (hzl _).mp hmem hx⟩
  have hk := reducedInducedLift_inclusion ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
    (isLocallyClosed_inter_compl W' U₀) (c ≫ j) hrange
  let QZ : (D₁.changeDatum c).Descended := DescentDatum.Descended.changeOfComp hk Q
  have hjac : I' ≤ Ring.jacobson Ah := Ideal.jacobson_bot (R := Ah) ▸ hh.le_jacobson
  obtain ⟨V, V', hVV', hV, hV', hfin, hempty⟩ :=
    DescentDatum.exists_isCompl_isTransitionInvariant_of_henselianPair hjac inferInstance D₁
      inferInstance hqc₁ hsep₁ b hB e he
      (D₁.isFinite_pullbackSnd_specMap_quotientMk_of_descended I' b e he QZ)
  obtain ⟨QF, -, hQFe⟩ :=
    DescentDatum.exists_descended_restrictOpen_isFinite_etale_of_henselianPair hh D₁ V V' hVV' hV
      hfin hempty QZ
  have hsub : (PrimeSpectrum.zeroLocus (I' : Set Ah))ᶜ ⊆
      ((j ⁻¹ᵁ U₀ : (Spec (CommRingCat.of Ah)).Opens) : Set (Spec (CommRingCat.of Ah))) :=
    fun x hx ↦ (hzl x).mpr hx
  have hheff : (D₁.baseDatum (j ⁻¹ᵁ U₀)).IsEtaleEffective :=
    D.isEtaleEffective_baseDatum_preimage_changeDatum j heff
  have hA : (D₁.restrictOpen V' hV').IsEtaleEffective :=
    D₁.isEtaleEffective_restrictOpen_of_isEmpty_closedFiber I' hsub hheff V' hV' hempty
  exact D₁.isEtaleEffective_of_isCompl V V' hVV' hV hV' QF.isEtaleEffective hA

/-- **[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP).** Let `f : X ⟶ S` be a
surjective integral morphism. The functor of Tag 0BTI induces an equivalence between the category
of schemes quasi-compact, separated and étale over `S` and the category of descent data `(V, φ)`
relative to `X/S` with `V` quasi-compact, separated and étale over `X`. -/
@[stacks 0BTP, sga "1 IX 4.11" "more general", sga "1 IX 4.7"]
theorem isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_isIntegralHom
    {S X : Scheme.{u}} (f : X ⟶ S) [Surjective f] [IsIntegralHom f] :
    (quasiCompactSeparatedEtaleDescentFunctor f).IsEquivalence :=
  isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_isHenselianCase isHenselianCase f

end AlgebraicGeometry

end
