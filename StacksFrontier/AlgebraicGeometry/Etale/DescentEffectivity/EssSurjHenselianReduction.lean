module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.CoprodBaseEffective
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.EssSurjChart
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.EssSurjInduction
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.HenselizationCovering
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.ReducedInducedAffine

/-!
# The affine chart step of Tag 0BTP, reduced to the henselian case

`AlgebraicGeometry.exists_isEtaleEffective_baseDatum_not_le_of_affineChart` reduces [Stacks, Tag
0BTP](https://stacks.math.columbia.edu/tag/0BTP) to one geometric statement: over an affine
Noetherian base `T` on which the complement of an already-effective open `U₀` is irreducible
with generic point `ξ` inside an affine chart, the datum is effective over some open containing
`ξ`. This file reduces that statement in turn to the *henselian case*, which is the remaining
mathematical content of the source's proof.

The reduction is the source's covering argument. Over an affine chart `W'` with ring of sections
`A = Γ(T, W')`, the part of the chart outside `U₀` is the zero locus of a radical finitely
generated ideal `I ⊆ A`, and `{Spec Aʰ ⟶ Spec A, Spec A ∖ V(I) ⟶ Spec A}` is an fpqc covering of
the chart for `Aʰ` the henselization of the pair `(A, I)`
(`AlgebraicGeometry.singleton_coprod_desc_specMap_henselization_mem_fpqcPrecoverage`). Étale
effectivity is local for that covering
(`AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isEtaleEffective_changeDatum_coprod_desc`),
so effectivity over the chart follows from effectivity over its two members. Over
`Spec A ∖ V(I)`, which lies inside `U₀`, effectivity is the hypothesis `heff` restricted; over
`Spec Aʰ` it is the henselian case, and that is what is left.

What the henselian case may use is everything the geometric half has already produced at that
point: `AlgebraicGeometry.exists_isAffineOpen_descended_isFinite_etale_reducedInducedInclusion`
(step 4) supplies a scheme finite and étale over the reduced induced scheme on the part of the
chart outside `U₀`, descending the datum base changed there. That reduced induced scheme is
`Spec (A ⧸ I)` over `Spec A`, by
`AlgebraicGeometry.exists_isIso_reducedInducedScheme_specQuotient` composed with the chart
transport `AlgebraicGeometry.exists_isRadical_fg_isIso_reducedInducedScheme_fromSpec`, and
`Spec (A ⧸ I)` is the closed fibre of `Spec Aʰ ⟶ Spec A`, the henselization of a pair being an
isomorphism modulo the ideal. So the henselian case is handed its own closed fibre already
descended, which is the input the splitting of Tag 0BTN and the lifting of Tag 09ZS consume.

The henselian case in the form `AlgebraicGeometry.IsHenselianCase` is proved as
`AlgebraicGeometry.isHenselianCase`, and Tag 0BTP itself is
`AlgebraicGeometry.isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_isIntegralHom`.

## Main results

* `AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_ι_fromSpec_of_baseDatum`: **the
  open member of the covering.** The datum base changed to the part of an affine chart lying over
  `U₀` is effective as soon as the datum is effective over `U₀`.
* `DescentDatum.isEtaleEffective_baseDatum_of_isEtaleEffective_changeDatum_specMap_henselization`:
  **effectivity over an affine chart from effectivity over the henselization of the chart at the
  complement of `U₀`.**
* `AlgebraicGeometry.exists_isEtaleEffective_baseDatum_of_henselianCase`: **the affine chart step
  of Tag 0BTP from the henselian case**, in exactly the form
  `AlgebraicGeometry.exists_isEtaleEffective_baseDatum_not_le_of_affineChart` consumes.
* `AlgebraicGeometry.isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_henselianCase`:
  **Tag 0BTP from the henselian case**, in the form without effectivity over `U₀`.
* `AlgebraicGeometry.isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_isHenselianCase`:
  **Tag 0BTP from the henselian case as the source states it**,
  `AlgebraicGeometry.IsHenselianCase`.

## Implementation notes

The chart is used through `AlgebraicGeometry.IsAffineOpen.fromSpec` rather than through
`AlgebraicGeometry.Scheme.Opens.ι` followed by `AlgebraicGeometry.IsAffineOpen.isoSpec`: the
henselization covering is a covering of `Spec A`, so the datum has to be base changed all the way
to `Spec A` in one morphism, and `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι` turns the result
back into effectivity over the open `W'` at the end.

The open member of the covering is handled by factoring `Spec A ∖ V(I) ⟶ Spec A ⟶ T` through
`U₀.ι`. The factorisation is built from
`AlgebraicGeometry.Scheme.Hom.isoOpensRange` and `AlgebraicGeometry.Scheme.homOfLE` rather than
from `AlgebraicGeometry.IsOpenImmersion.lift`, so that the factor is an open immersion by
instance resolution — which is what
`AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_opensRange_comp` requires.

The henselization is quantified over rather than named: `exists_henselization` (Tag 0A02)
produces it inside an existential, and the hypothesis of
`AlgebraicGeometry.exists_isEtaleEffective_baseDatum_of_henselianCase` is therefore stated for
every henselian pair under `(A, I)` with the universal property, which is the form a proof of the
henselian case would take anyway.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
* [Stacks Project, Tag 0BTN](https://stacks.math.columbia.edu/tag/0BTN)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

namespace DescentDatum

/-! ### The open member of the covering -/

/-- **The datum base changed to the part of an affine chart lying over `U₀` is étale effective**,
as soon as the datum is étale effective over `U₀`.

This is the open member `Spec A ∖ V(I) ⟶ Spec A` of the covering the reduction uses: that open
of the chart lies inside `U₀`, so the morphism `Spec A ∖ V(I) ⟶ Spec A ⟶ T` factors through
`U₀.ι`, and étale effectivity over `U₀` passes to it. -/
theorem isEtaleEffective_changeDatum_ι_fromSpec_of_baseDatum {T X : Scheme.{u}} {g : X ⟶ T}
    [Surjective g] [IsIntegralHom g] (D : DescentDatum g) [Etale D.over.hom] {W : T.Opens}
    (hW : IsAffineOpen W) (U₀ : T.Opens) (heff : (D.baseDatum U₀).IsEtaleEffective) :
    ((D.changeDatum hW.fromSpec).changeDatum
      (hW.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W)).Opens).ι).IsEtaleEffective := by
  set k : (hW.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W)).Opens).toScheme ⟶ T :=
    (hW.fromSpec ⁻¹ᵁ U₀).ι ≫ hW.fromSpec with hk
  have hle : k.opensRange ≤ U₀ := by
    rintro x ⟨y, rfl⟩
    exact y.2
  set j : (hW.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W)).Opens).toScheme ⟶ U₀.toScheme :=
    k.isoOpensRange.hom ≫ T.homOfLE hle with hjdef
  have hj : j ≫ U₀.ι = k := by
    rw [hjdef, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]
  have hle₂ : U₀.ι ''ᵁ j.opensRange ≤ U₀ :=
    (U₀.ι.image_le_opensRange _).trans_eq U₀.opensRange_ι
  have hrestrict :
      ((D.baseDatum U₀).baseDatum (U₀.ι ⁻¹ᵁ (U₀.ι ''ᵁ j.opensRange))).IsEtaleEffective :=
    (D.isEtaleEffective_baseDatum_of_le_iff hle₂).mpr
      (D.isEtaleEffective_baseDatum_of_le hle₂ heff)
  rw [U₀.ι.preimage_image_eq] at hrestrict
  have hfactor : (D.changeDatum (j ≫ U₀.ι)).IsEtaleEffective :=
    (isEtaleEffective_changeDatum_opensRange_comp D U₀.ι j).mp hrestrict
  rw [hj] at hfactor
  exact (isEtaleEffective_changeDatum_comp_iff D).mpr hfactor

/-! ### Effectivity over an affine chart from the henselian member -/

/-- **Étale effectivity over an affine chart `W` of the base, from étale effectivity over the
henselization of the chart at the part of it outside `U₀`.** The ideal `I` of `Γ(T, W)` cuts that
part out, `Aʰ` is a henselization of the pair `(Γ(T, W), I)`, and the two hypotheses are
effectivity over `U₀` and effectivity along `Spec Aʰ ⟶ Spec Γ(T, W) ⟶ T`.

`AlgebraicGeometry.singleton_coprod_desc_specMap_henselization_mem_fpqcPrecoverage` is the
covering this uses; here its three constituent properties are produced directly, because
`AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isEtaleEffective_changeDatum_coprod_desc`
takes them as instances rather than taking membership in the fpqc precoverage. -/
theorem isEtaleEffective_baseDatum_of_isEtaleEffective_changeDatum_specMap_henselization
    {T X : Scheme.{u}} {g : X ⟶ T} [Surjective g] [IsIntegralHom g] (D : DescentDatum g)
    [Etale D.over.hom] (hqc : QuasiCompact D.over.hom) (hsep : IsSeparated D.over.hom)
    {W : T.Opens} (hW : IsAffineOpen W) (U₀ : T.Opens) (I : Ideal Γ(T, W)) (hIfg : I.FG)
    (hU : ((hW.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W)).Opens) : Set (Spec Γ(T, W))) =
      (PrimeSpectrum.zeroLocus (I : Set Γ(T, W)))ᶜ)
    (Ah : Type u) [CommRing Ah] [Algebra Γ(T, W) Ah]
    (hh : HenselianPair Ah (I.map (algebraMap Γ(T, W) Ah)))
    (hι : ∀ (B : Type u) (_ : CommRing B) (J : Ideal B), HenselianPair B J →
      ∀ q : Γ(T, W) →+* B, I ≤ J.comap q →
        ∃! r : Ah →+* B, r.comp (algebraMap Γ(T, W) Ah) = q ∧
          I.map (algebraMap Γ(T, W) Ah) ≤ J.comap r)
    (heff : (D.baseDatum U₀).IsEtaleEffective)
    (hhens : (D.changeDatum (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W) Ah)) ≫
      hW.fromSpec)).IsEtaleEffective) :
    (D.baseDatum W).IsEtaleEffective := by
  have hpair := flat_henselization_and_bijective_quotientMap Γ(T, W) I Ah hh hι
  have _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W) Ah))) :=
    flat_specMap_algebraMap_henselization Γ(T, W) I Ah hh hι
  have hcpt : IsCompact ((hW.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W)).Opens) : Set (Spec Γ(T, W))) := by
    rw [hU]
    exact (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨I, hIfg, rfl⟩).1
  have _ : CompactSpace (hW.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W)).Opens).toScheme :=
    isCompact_iff_compactSpace.mp hcpt
  have _ : Surjective (coprod.desc (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W) Ah)))
      (hW.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W)).Opens).ι) :=
    surjective_coprod_desc_specMap _ I
      (bijective_quotientMap_congr (algebraMap Γ(T, W) Ah) (pow_one I) (hpair.2 1)) _ hU
  have hchart : (D.changeDatum hW.fromSpec).IsEtaleEffective :=
    isEtaleEffective_of_isEtaleEffective_changeDatum_coprod_desc _
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W) Ah)))
      (hW.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W)).Opens).ι (D.changeDatum hW.fromSpec)
      (D.quasiCompact_changeDatum_over_hom hW.fromSpec hqc)
      (D.isSeparated_changeDatum_over_hom hW.fromSpec hsep)
      ((isEtaleEffective_changeDatum_comp_iff D).mpr hhens)
      (D.isEtaleEffective_changeDatum_ι_fromSpec_of_baseDatum hW U₀ heff)
  exact (isEtaleEffective_changeDatum_iso_comp_iff D W.ι hW.isoSpec.symm).mp
    ((isEtaleEffective_changeDatum_of_eq D hW.isoSpec_inv_ι).mpr hchart)

end DescentDatum

/-! ### The affine chart step from the henselian case -/

/-- **The affine chart step of [Stacks, Tag
0BTP](https://stacks.math.columbia.edu/tag/0BTP) from the henselian case.** The conclusion is
exactly the hypothesis `Hchart` of
`AlgebraicGeometry.exists_isEtaleEffective_baseDatum_not_le_of_affineChart`, so the henselian
case is all that Tag 0BTP still needs.

The henselian case, the hypothesis `Hhens`, is: over an affine Noetherian base `T` with a
quasi-compact separated étale descent datum along a finite surjective `g`, given an affine chart
`W'`, a radical finitely generated ideal `I` of `Γ(T, W')` cutting out the part of the chart
outside `U₀`, a henselization `Aʰ` of the pair `(Γ(T, W'), I)`, and a scheme finite and étale
over the reduced induced scheme on that part which descends the datum base changed there, the
datum base changed along `Spec Aʰ ⟶ Spec Γ(T, W') ⟶ T` is étale effective.

Given that, the step is the covering argument:
`AlgebraicGeometry.exists_isAffineOpen_descended_isFinite_etale_reducedInducedInclusion`
shrinks the chart until the datum over the reduced complement is descended by a finite étale
scheme, `AlgebraicGeometry.exists_isRadical_fg_zeroLocus_eq_compl_opens` names the ideal,
`exists_henselization` names the henselization, and
`DescentDatum.isEtaleEffective_baseDatum_of_isEtaleEffective_changeDatum_specMap_henselization`
assembles effectivity over the shrunk chart, which contains `ξ`. -/
theorem exists_isEtaleEffective_baseDatum_of_henselianCase
    (Hhens : ∀ (T Y : Scheme.{u}) (g : Y ⟶ T), IsAffine T → IsNoetherian T → IsFinite g →
      Surjective g → ∀ (D : DescentDatum g) (_ : Etale D.over.hom), QuasiCompact D.over.hom →
        IsSeparated D.over.hom → ∀ (U₀ W' : T.Opens) (hW' : IsAffineOpen W')
          (I : Ideal Γ(T, W')), I.IsRadical → I.FG →
            ((hW'.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W')).Opens) : Set (Spec Γ(T, W'))) =
                (PrimeSpectrum.zeroLocus (I : Set Γ(T, W')))ᶜ →
              ∀ (Ah : Type u) (_ : CommRing Ah) (_ : Algebra Γ(T, W') Ah),
                HenselianPair Ah (I.map (algebraMap Γ(T, W') Ah)) →
                  (∀ (B : Type u) (_ : CommRing B) (J : Ideal B), HenselianPair B J →
                    ∀ q : Γ(T, W') →+* B, I ≤ J.comap q →
                      ∃! r : Ah →+* B, r.comp (algebraMap Γ(T, W') Ah) = q ∧
                        I.map (algebraMap Γ(T, W') Ah) ≤ J.comap r) →
                    ∀ Q : (D.changeDatum (reducedInducedInclusion
                        ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
                        (isLocallyClosed_inter_compl W' U₀))).Descended,
                      Etale Q.base.hom → IsFinite Q.base.hom →
                        (D.changeDatum (Spec.map (CommRingCat.ofHom
                          (algebraMap Γ(T, W') Ah)) ≫ hW'.fromSpec)).IsEtaleEffective)
    (T Y : Scheme.{u}) (g : Y ⟶ T) (hT : IsAffine T) (hTN : IsNoetherian T) (hg : IsFinite g)
    (hgs : Surjective g) (D : DescentDatum g) (hD : Etale D.over.hom)
    (hqc : QuasiCompact D.over.hom) (hsep : IsSeparated D.over.hom) (U₀ W : T.Opens) (ξ : T)
    (heff : (D.baseDatum U₀).IsEtaleEffective) (_hWaff : IsAffineOpen W) (hξW : ξ ∈ W)
    (hξU₀ : ξ ∉ U₀) (hirr : IsIrreducible ((W : Set T) ∩ (U₀ : Set T)ᶜ))
    (hclos : (W : Set T) ∩ (U₀ : Set T)ᶜ ⊆ closure {ξ}) :
    ∃ V : T.Opens, ξ ∈ V ∧ (D.baseDatum V).IsEtaleEffective := by
  have := hD
  have := hg
  have := hgs
  have := hTN
  have _ : IsIntegralHom g := inferInstance
  obtain ⟨W', -, hξW', hW'aff, Q, hQe, hQf⟩ :=
    exists_isAffineOpen_descended_isFinite_etale_reducedInducedInclusion g D hqc hsep U₀ W ξ
      hξW hξU₀ hirr hclos
  have _ : IsNoetherianRing Γ(T, W') :=
    IsLocallyNoetherian.component_noetherian ⟨W', hW'aff⟩
  obtain ⟨I, hIrad, hIfg, -, hU⟩ :=
    exists_isRadical_fg_zeroLocus_eq_compl_opens (A := Γ(T, W')) (hW'aff.fromSpec ⁻¹ᵁ U₀)
  obtain ⟨Ah, instAh, ι, hh, hun⟩ := exists_henselization.{u, u} Γ(T, W') I
  let : CommRing Ah := instAh
  let : Algebra Γ(T, W') Ah := ι.toAlgebra
  exact ⟨W', hξW',
    D.isEtaleEffective_baseDatum_of_isEtaleEffective_changeDatum_specMap_henselization hqc hsep
      hW'aff U₀ I hIfg hU Ah hh hun heff
      (Hhens T Y g hT hTN hg hgs D hD hqc hsep U₀ W' hW'aff I hIrad hIfg hU Ah _ _ hh hun Q hQe
        hQf)⟩

/-- **[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) from the henselian case.**
The henselian case, described at
`AlgebraicGeometry.exists_isEtaleEffective_baseDatum_of_henselianCase`, is the hypothesis: the
descent functor for quasi-compact separated étale schemes along a surjective integral morphism is
an equivalence as soon as it holds.

No Stacks tag is claimed, the statement being conditional. -/
theorem isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_henselianCase
    (Hhens : ∀ (T Y : Scheme.{u}) (g : Y ⟶ T), IsAffine T → IsNoetherian T → IsFinite g →
      Surjective g → ∀ (D : DescentDatum g) (_ : Etale D.over.hom), QuasiCompact D.over.hom →
        IsSeparated D.over.hom → ∀ (U₀ W' : T.Opens) (hW' : IsAffineOpen W')
          (I : Ideal Γ(T, W')), I.IsRadical → I.FG →
            ((hW'.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W')).Opens) : Set (Spec Γ(T, W'))) =
                (PrimeSpectrum.zeroLocus (I : Set Γ(T, W')))ᶜ →
              ∀ (Ah : Type u) (_ : CommRing Ah) (_ : Algebra Γ(T, W') Ah),
                HenselianPair Ah (I.map (algebraMap Γ(T, W') Ah)) →
                  (∀ (B : Type u) (_ : CommRing B) (J : Ideal B), HenselianPair B J →
                    ∀ q : Γ(T, W') →+* B, I ≤ J.comap q →
                      ∃! r : Ah →+* B, r.comp (algebraMap Γ(T, W') Ah) = q ∧
                        I.map (algebraMap Γ(T, W') Ah) ≤ J.comap r) →
                    ∀ Q : (D.changeDatum (reducedInducedInclusion
                        ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
                        (isLocallyClosed_inter_compl W' U₀))).Descended,
                      Etale Q.base.hom → IsFinite Q.base.hom →
                        (D.changeDatum (Spec.map (CommRingCat.ofHom
                          (algebraMap Γ(T, W') Ah)) ≫ hW'.fromSpec)).IsEtaleEffective)
    {S X : Scheme.{u}} (f : X ⟶ S) [Surjective f] [IsIntegralHom f] :
    (quasiCompactSeparatedEtaleDescentFunctor f).IsEquivalence :=
  isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_exists_not_le
    (exists_isEtaleEffective_baseDatum_not_le_of_affineChart
      (exists_isEtaleEffective_baseDatum_of_henselianCase Hhens)) f

/-! ### The henselian case as the source states it -/

/-- **The henselian case of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP), as the
source states it.** This is the hypothesis `Hhens` of
`AlgebraicGeometry.exists_isEtaleEffective_baseDatum_of_henselianCase` with one further
hypothesis: that the datum is already étale effective over `U₀`.

The source's reduced situation is *"here `S = Spec A`, `Z = V(I)`, `S' = S ∖ Z` where `(A, I)` is
a henselian pair, **we have `U' → S'` corresponding to the descent datum `(V', φ')`** and we have
a finite étale morphism `U_Z → Z` corresponding to the descent datum `(V_Z, φ_Z)`"*. The scheme
`U'` over the open part of the base is an input of the henselian case, not an output of it: the
splitting of Tag 0BTN cuts `V` into a part finite over the base and a part `V_away` carrying no
point over `Z`, and the second part is algebraized by nothing in the henselian situation — it is
algebraized by `U'`, through the open and closed immersion `U'_fin ⟶ U'`. Effectivity over `U₀`
is what supplies `U'`: the open member `Spec Aʰ ∖ V(IAʰ)` of the base lies over
`Spec Γ(T, W') ∖ V(I)`, which by the hypothesis naming `I` lies inside `U₀`.

Without it the statement is still true — Tag 0BTP is a theorem, so every quasi-compact separated
étale datum along a surjective integral morphism is effective — but it is then as strong as Tag
0BTP itself, and the source's argument does not prove it: the Noetherian induction of
`AlgebraicGeometry.exists_isEtaleEffective_baseDatum_not_le_of_affineChart` is exactly what
produces `U'`, and the henselian case is a step inside that induction. -/
def IsHenselianCase : Prop :=
  ∀ (T Y : Scheme.{u}) (g : Y ⟶ T), IsAffine T → IsNoetherian T → IsFinite g →
    Surjective g → ∀ (D : DescentDatum g) (_ : Etale D.over.hom), QuasiCompact D.over.hom →
      IsSeparated D.over.hom → ∀ (U₀ W' : T.Opens) (hW' : IsAffineOpen W')
        (I : Ideal Γ(T, W')), I.IsRadical → I.FG →
          ((hW'.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W')).Opens) : Set (Spec Γ(T, W'))) =
              (PrimeSpectrum.zeroLocus (I : Set Γ(T, W')))ᶜ →
            ∀ (Ah : Type u) (_ : CommRing Ah) (_ : Algebra Γ(T, W') Ah),
              HenselianPair Ah (I.map (algebraMap Γ(T, W') Ah)) →
                (∀ (B : Type u) (_ : CommRing B) (J : Ideal B), HenselianPair B J →
                  ∀ q : Γ(T, W') →+* B, I ≤ J.comap q →
                    ∃! r : Ah →+* B, r.comp (algebraMap Γ(T, W') Ah) = q ∧
                      I.map (algebraMap Γ(T, W') Ah) ≤ J.comap r) →
                  ∀ Q : (D.changeDatum (reducedInducedInclusion
                      ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
                      (isLocallyClosed_inter_compl W' U₀))).Descended,
                    Etale Q.base.hom → IsFinite Q.base.hom →
                      (D.baseDatum U₀).IsEtaleEffective →
                        (D.changeDatum (Spec.map (CommRingCat.ofHom
                          (algebraMap Γ(T, W') Ah)) ≫ hW'.fromSpec)).IsEtaleEffective

/-- **The affine chart step of [Stacks, Tag
0BTP](https://stacks.math.columbia.edu/tag/0BTP) from the henselian case as the source states
it.** This is `AlgebraicGeometry.exists_isEtaleEffective_baseDatum_of_henselianCase` with
`AlgebraicGeometry.IsHenselianCase` in place of its hypothesis: the induction step has
effectivity over `U₀` in hand, so it can pass it on. -/
theorem exists_isEtaleEffective_baseDatum_of_isHenselianCase (Hhens : IsHenselianCase.{u})
    (T Y : Scheme.{u}) (g : Y ⟶ T) (hT : IsAffine T) (hTN : IsNoetherian T) (hg : IsFinite g)
    (hgs : Surjective g) (D : DescentDatum g) (hD : Etale D.over.hom)
    (hqc : QuasiCompact D.over.hom) (hsep : IsSeparated D.over.hom) (U₀ W : T.Opens) (ξ : T)
    (heff : (D.baseDatum U₀).IsEtaleEffective) (_hWaff : IsAffineOpen W) (hξW : ξ ∈ W)
    (hξU₀ : ξ ∉ U₀) (hirr : IsIrreducible ((W : Set T) ∩ (U₀ : Set T)ᶜ))
    (hclos : (W : Set T) ∩ (U₀ : Set T)ᶜ ⊆ closure {ξ}) :
    ∃ V : T.Opens, ξ ∈ V ∧ (D.baseDatum V).IsEtaleEffective := by
  have := hD
  have := hg
  have := hgs
  have := hTN
  have _ : IsIntegralHom g := inferInstance
  obtain ⟨W', -, hξW', hW'aff, Q, hQe, hQf⟩ :=
    exists_isAffineOpen_descended_isFinite_etale_reducedInducedInclusion g D hqc hsep U₀ W ξ
      hξW hξU₀ hirr hclos
  have _ : IsNoetherianRing Γ(T, W') :=
    IsLocallyNoetherian.component_noetherian ⟨W', hW'aff⟩
  obtain ⟨I, hIrad, hIfg, -, hU⟩ :=
    exists_isRadical_fg_zeroLocus_eq_compl_opens (A := Γ(T, W')) (hW'aff.fromSpec ⁻¹ᵁ U₀)
  obtain ⟨Ah, instAh, ι, hh, hun⟩ := exists_henselization.{u, u} Γ(T, W') I
  let : CommRing Ah := instAh
  let : Algebra Γ(T, W') Ah := ι.toAlgebra
  exact ⟨W', hξW',
    D.isEtaleEffective_baseDatum_of_isEtaleEffective_changeDatum_specMap_henselization hqc hsep
      hW'aff U₀ I hIfg hU Ah hh hun heff
      (Hhens T Y g hT hTN hg hgs D hD hqc hsep U₀ W' hW'aff I hIrad hIfg hU Ah _ _ hh hun Q hQe
        hQf heff)⟩

/-- **[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) from the henselian case as
the source states it.** The descent functor is an equivalence as soon as
`AlgebraicGeometry.IsHenselianCase` holds. That hypothesis is
`AlgebraicGeometry.isHenselianCase`, and the unconditional statement is
`AlgebraicGeometry.isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_isIntegralHom`. -/
theorem isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_isHenselianCase
    (Hhens : IsHenselianCase.{u}) {S X : Scheme.{u}} (f : X ⟶ S) [Surjective f]
    [IsIntegralHom f] :
    (quasiCompactSeparatedEtaleDescentFunctor f).IsEquivalence :=
  isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_exists_not_le
    (exists_isEtaleEffective_baseDatum_not_le_of_affineChart
      (exists_isEtaleEffective_baseDatum_of_isHenselianCase Hhens)) f

end AlgebraicGeometry

end
