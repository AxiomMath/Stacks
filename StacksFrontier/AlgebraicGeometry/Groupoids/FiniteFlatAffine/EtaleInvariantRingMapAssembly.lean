module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleInvariantRingMap

/-!
# The first conclusion of [Stacks Project, Tag 0DT9]: the map on invariant rings is étale

Let `F : (U', R', s', t', c') ⟶ (U, R, s, t, c)` be a morphism of groupoid schemes with all four of
`U`, `R`, `U'`, `R'` affine, with `s`, `t`, `s'`, `t'` finite locally free, with the source, target
and stabilizer squares cartesian, and with `f : U' ⟶ U` étale. Writing `C` and `C'` for the two
rings of invariant functions, this file proves that `C ⟶ C'` is **étale**, and deduces the second
conclusion of the tag from it: `U' = Spec C' ×_{Spec C} U`.

## The argument

Étaleness is checked at one point `p'` of `Spec C'` at a time, through the source-cover criterion
`AlgebraicGeometry.etale_of_forall_exists_etale_comp`: it suffices to produce, for each `p'`, an
étale morphism `gg` onto a neighbourhood of `p'` in `Spec C'` whose composite with
`Spec C' ⟶ Spec C` is again étale. No finite presentation hypothesis is needed for that criterion,
which matters because local finite presentation of `Spec C' ⟶ Spec C` is part of the conclusion
being proved.

The morphism `gg` is produced at a finite étale stage of the strict henselization. Write `p` for
the image of `p'` in `Spec C` and `Λ = C^{sh}_p`, which is flat, strictly henselian local and a
filtered colimit of étale `C`-algebras. Over `Λ` the "Claim" of the source text is available, in
the form `AlgebraicGeometry.GroupoidScheme.exists_section_tensorBaseRing_of_strictlyHenselian`: the
base-changed map on object schemes `U'_Λ ⟶ U_Λ` admits a section whose sheet is an invariant clopen
containing a point above a chosen point of `Spec (C' ⊗[C] Λ)` over `p'`. That datum is an
idempotent of `A' ⊗[C] Λ` together with one invariance equation, and both descend to a single étale
stage `D`: the attached `A`-algebra map `A' ⟶ A ⊗[C] Λ` factors through `A ⊗[C] D` because `A'` is
of finite presentation over `A`, and the invariance equation then holds at a possibly later stage.
At that stage the datum is turned back into a section of `U'_D ⟶ U_D` with invariant clopen sheet,
and the geometry of a sheet makes `Spec (C' ⊗[C] D) ⟶ Spec D` étale at the point of the sheet above
`p'`. An affine neighbourhood of that point, followed by the projection to `Spec C'`, is `gg`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.etale_invariantRingMap`: **the first conclusion of
  [Stacks Project, Tag 0DT9]** — the map `C ⟶ C'` on rings of invariant functions is étale.
* `AlgebraicGeometry.GroupoidScheme.isPullback_mapObjects`: **the second conclusion** —
  `U' = Spec C' ×_{Spec C} U`, now with no hypothesis on the map on invariant rings.
* `AlgebraicGeometry.GroupoidScheme.exists_etale_comp_invariantRingMap`: the étale cover of a
  neighbourhood of one point of `Spec C'` along which `Spec C' ⟶ Spec C` becomes étale, which is
  what the source-cover criterion consumes.
* `AlgebraicGeometry.GroupoidScheme.exists_etale_comp_of_indEtale`: the whole descent, from an
  ind-étale flat strictly henselian local extension of the invariant ring and a point above its
  closed point.
* `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_of_section_of_bijective` and
  `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_tensorBaseRingMap_of_section`: the geometry at
  a stage — the base-changed map on invariant rings is étale at the image of a point of the sheet
  of an invariant section.

## Implementation notes

Every step is taken against a *small* goal. The chaining theorem
`AlgebraicGeometry.GroupoidScheme.exists_etale_comp_of_indEtale` states only the existence of the
étale cover, so the many `obtain`s in its proof never destructure against a conclusion mentioning a
coordinate ring of a base change; the commuting square of four spectra that finishes it is a
separate lemma over abstract rings (`AlgebraicGeometry.exists_etale_comp_specMap_of_etaleAt`), and
the transport of the point along the two canonical identifications of Tag 03BK is a separate lemma
about one stage. A monolithic proof over those terms exhausts the heartbeat budget.

The chosen point of `Spec (C' ⊗[C] Λ)` exists because `Spec (C' ⊗[C] Λ)` is the fibre product
`Spec C' ×_{Spec C} Spec Λ`
(`AlgebraicGeometry.GroupoidScheme.isPullback_invariantSpectrumMap_tensorBaseRing`) and the closed
point of `Spec Λ` lies over `p` by
`StacksDraft.under_maximalIdeal_strictHenselizationAtPrime`.

## References

* [Stacks Project, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
* [Stacks Project, Tag 02KL](https://stacks.math.columbia.edu/tag/02KL)
* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)

## Tags

groupoid scheme, invariant ring, étale, strict henselization, ind-étale descent, source cover
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

/-! ### The commuting square of four spectra -/

/-- The spectrum of an étale algebra map is an étale morphism. -/
private theorem etale_specMap_algebraMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

/-- Equal morphisms of schemes agree on points. -/
private theorem base_apply_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (x : X) :
    f.base x = g.base x := by rw [h]

/-- **An étale cover of a neighbourhood of a point of `Spec C'` along which `Spec C' ⟶ Spec C`
becomes étale, produced from an étale stage.** Given a commuting square of ring maps

```
C --a--> D
|φ       |b
v        v
C' --c-> E
```

with `C ⟶ D` and `C' ⟶ E` étale and `Spec E ⟶ Spec D` étale at a point `x` lying over `p'`, the
morphism `Spec C' ⟶ Spec C` has an étale morphism through `p'` whose composite with it is étale.

This is `AlgebraicGeometry.GroupoidScheme.exists_etale_comp_of_etaleAt_of_square` read on the four
spectra; it is stated over abstract rings so that the unifier never has to match a point of a
spectrum of a tensor product against an implicit argument. -/
theorem exists_etale_comp_specMap_of_etaleAt {C C' D E : Type u} [CommRing C] [CommRing C']
    [CommRing D] [CommRing E] (φ : C →+* C') (a : C →+* D) (b : D →+* E) (c : C' →+* E)
    (hcomm : b.comp a = c.comp φ)
    (ha : Etale (Spec.map (CommRingCat.ofHom a)))
    (hc : Etale (Spec.map (CommRingCat.ofHom c)))
    {x : Spec (.of E)} (hx : EtaleAt (Spec.map (CommRingCat.ofHom b)) x)
    {p' : Spec (.of C')} (hp : (Spec.map (CommRingCat.ofHom c)).base x = p') :
    ∃ (W : Scheme.{u}) (gg : W ⟶ Spec (.of C')), Etale gg ∧
      Etale (gg ≫ Spec.map (CommRingCat.ofHom φ)) ∧ p' ∈ Set.range gg.base := by
  have := ha
  have := hc
  have hsq : Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hcomm]
  exact GroupoidScheme.exists_etale_comp_of_etaleAt_of_square
    (Spec.map (CommRingCat.ofHom b)) (Spec.map (CommRingCat.ofHom c))
    (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom a)) hsq hx hp

/-- **The closed point of the strict henselization of `C` at a prime lies over that prime.** This
is `StacksDraft.under_maximalIdeal_strictHenselizationAtPrime` read on spectra. -/
theorem specMap_base_closedPoint_strictHenselizationAtPrime (C : Type u) [CommRing C]
    (q : PrimeSpectrum C) :
    (Spec.map (CommRingCat.ofHom
          (algebraMap C (StacksDraft.strictHenselizationAtPrime C q.asIdeal)))).base
        (IsLocalRing.closedPoint
          (StacksDraft.strictHenselizationAtPrime C q.asIdeal)) = q :=
  PrimeSpectrum.ext (StacksDraft.under_maximalIdeal_strictHenselizationAtPrime C q.asIdeal)

namespace GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-- Membership of a prime of the target, from membership of the pullback of the element: the
pointwise form of `AlgebraicGeometry.GroupoidScheme.mem_comap_iff` in which the pullback is
presented by an equation. Stated for abstract schemes so that the rewrite is carried out on small
terms. -/
private theorem mem_asIdeal_of_appTop_eq {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (x : X) {a : Γ(Y, ⊤)} {b : Γ(X, ⊤)} (hab : f.appTop.hom a = b)
    (hb : b ∈ (X.carrierEquivPrimeSpectrum x).asIdeal) :
    a ∈ (Y.carrierEquivPrimeSpectrum (f.base x)).asIdeal :=
  (mem_comap_iff f x a).mpr (hab ▸ hb)

/-! ### The geometry at a stage -/

section Induced

variable {C₁ C'₁ : Type u} [CommRing C₁] [CommRing C'₁] [Algebra (invariantRing G) C₁]
  [Algebra (invariantRing G') C'₁] (ψ : C₁ →+* C'₁)
  (hψ : ψ.comp (algebraMap (invariantRing G) C₁) =
    (algebraMap (invariantRing G') C'₁).comp (invariantRingMap F))
  (bc : AffineInvariantBaseChange G C₁) (bc' : AffineInvariantBaseChange G' C'₁)

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsAffine G'.objects.left]
  [IsAffine G'.arrows.left] in
include hψ in
/-- **The map of new base rings is étale at the image of a point of the sheet of an invariant
section**, read on a compatible pair of extensions. Let `C ⟶ C₁` and `C' ⟶ C'₁` be extensions of
the two invariant rings compatible through `ψ`, let the two canonical maps of Tag 03BK be
bijective, and let the map on object schemes of the induced morphism of base changes admit a
section which is an open immersion with closed invariant range. Then `Spec ψ` is étale at the
image of any point of that range.

Étaleness at a point travels the square of Tag 03BK by
`AlgebraicGeometry.etaleAt_specMap_of_ringEquiv_square`, exactly as in
`AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_of_strictlyHenselian_of_bijective`; stating it
for an abstract compatible pair keeps the identification of the invariant ring of a pushforward
with the invariant ring itself off a term as large as `C' ⊗[C] D`. -/
theorem etaleAt_specMap_of_section_of_bijective
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hbc : Function.Bijective bc.canonicalMapToInvariantFunctions)
    (hbc' : Function.Bijective bc'.canonicalMapToInvariantFunctions)
    {σ : bc.groupoid.objects.left ⟶ bc'.groupoid.objects.left} (hoi : IsOpenImmersion σ)
    (hσ : σ ≫ (baseChangeHom F ψ hψ bc bc').mapObjects.left = 𝟙 bc.groupoid.objects.left)
    (hcl : IsClosed (Set.range σ.base))
    (hV : IsInvariantSet bc'.groupoid (Set.range σ.base))
    (v : bc.groupoid.objects.left) :
    EtaleAt (Spec.map (CommRingCat.ofHom ψ))
      (bc'.groupoid.objects.hom.base (σ.base v)) := by
  have : IsAffine (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).objects.left :=
    inferInstanceAs (IsAffine bc'.groupoid.objects.left)
  have : IsAffine (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).arrows.left :=
    inferInstanceAs (IsAffine bc'.groupoid.arrows.left)
  have hkey := etaleAt_specMap_invariantRingMap_section_point (baseChangeHom F ψ hψ bc bc')
    (source_isPullback_mapArrows_baseChangeHom F ψ hψ bc bc' hsource) hoi hσ hcl hV v
  have hstep := base_apply_eq_of_eq
    (objectsToInvariantSpectrum_comp_specMap_canonicalMapToInvariantFunctions bc') (σ.base v)
  exact etaleAt_specMap_of_ringEquiv_square ψ (invariantRingMap (baseChangeHom F ψ hψ bc bc'))
    (RingEquiv.ofBijective _ hbc) (RingEquiv.ofBijective _ hbc')
    (invariantRingMap_baseChangeHom_comp_ofBijective F ψ hψ bc bc' hbc hbc') hstep hkey

end Induced

/-- **The base-changed map on invariant rings is étale at the image of a point of the sheet of an
invariant section.** Let `C ⟶ D` be a flat extension of the invariant ring of `G` and let the
base-changed map on object schemes `U'_D ⟶ U_D` admit a section which is an open immersion with
closed invariant range. Then `Spec (C' ⊗[C] D) ⟶ Spec D` is étale at the image of any point of
the range of that section.

This is `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_of_section_of_bijective` at the tensor
product presentation, where the two bijectivity hypotheses are Tag 03BK for the two
extensions. -/
theorem etaleAt_specMap_tensorBaseRingMap_of_section
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (D : Type u) [CommRing D] [Algebra (invariantRing G) D] [Module.Flat (invariantRing G) D]
    (bcD : AffineInvariantBaseChange G D)
    (bcD' : AffineInvariantBaseChange G' (tensorBaseRing F D))
    {σ : bcD.groupoid.objects.left ⟶ bcD'.groupoid.objects.left} (hoi : IsOpenImmersion σ)
    (hσ : σ ≫ tensorMapObjects F bcD bcD' = 𝟙 bcD.groupoid.objects.left)
    (hcl : IsClosed (Set.range σ.base))
    (hV : IsInvariantSet bcD'.groupoid (Set.range σ.base))
    (v : bcD.groupoid.objects.left) :
    EtaleAt (Spec.map (CommRingCat.ofHom (tensorBaseRingMap F D)))
      (bcD'.groupoid.objects.hom.base (σ.base v)) :=
  etaleAt_specMap_of_section_of_bijective F (tensorBaseRingMap F D)
    (tensorBaseRing_compatible F D) bcD bcD' hsource
    (canonicalMapToInvariantFunctions_bijective_of_flat bcD)
    (canonicalMapToInvariantFunctions_bijective_of_flat bcD') hoi hσ hcl hV v

/-! ### The étale cover of a neighbourhood of one point of `Spec C'` -/

section Chaining

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
  [Etale F.mapObjects.left]

/-- **The étale cover of a neighbourhood of one point of `Spec C'` along which `Spec C' ⟶ Spec C`
becomes étale**, from an ind-étale, flat, strictly henselian local extension `Λ` of the invariant
ring and a point of `Spec (C' ⊗[C] Λ)` above the closed point of `Spec Λ` and above the given
point of `Spec C'`.

This is the whole descent of the first conclusion of [Stacks Project, Tag 0DT9]. Over `Λ` the
"Claim" of the source text gives a section of `U'_Λ ⟶ U_Λ` whose sheet is an invariant clopen
containing a point above the chosen point; the sheet is an idempotent of `A' ⊗[C] Λ` with one
invariance equation; the attached `A`-algebra map `A' ⟶ A ⊗[C] Λ` factors through a single étale
stage, the invariance equation holds at a possibly later stage, and at that stage the datum is a
section of `U'_D ⟶ U_D` again. The comparison morphism of the two base changes carries the chosen
point of the sheet over `Λ` into the sheet over `D`, and the geometry of a sheet makes
`Spec (C' ⊗[C] D) ⟶ Spec D` étale there. -/
theorem exists_etale_comp_of_indEtale
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (Λ : Type u) [CommRing Λ] [Algebra (invariantRing G) Λ]
    [Module.Flat (invariantRing G) Λ] [StrictlyHenselianLocalRing Λ]
    (hΛ : StacksDraft.IndEtale (invariantRing G) Λ)
    (p' : Spec (.of (invariantRing G')))
    (x : Spec (.of (tensorBaseRing F Λ)))
    (hx : (Spec.map (CommRingCat.ofHom (tensorBaseRingMap F Λ))).base x =
      (IsLocalRing.closedPoint Λ : Spec (.of Λ)))
    (hp : (invariantSpectrumMap G' (tensorBaseRing F Λ)).base x = p') :
    ∃ (W : Scheme.{u}) (gg : W ⟶ Spec (.of (invariantRing G'))), Etale gg ∧
      Etale (gg ≫ Spec.map (CommRingCat.ofHom (invariantRingMap F))) ∧
      p' ∈ Set.range gg.base := by
  let := objectRingAlgebraOfHom F
  let := arrowRingAlgebraOfHom F
  obtain ⟨bc⟩ := exists_affineInvariantBaseChange G Λ
  obtain ⟨bc'⟩ := exists_affineInvariantBaseChange G' (tensorBaseRing F Λ)
  obtain ⟨σ, hoi, hσ, hcl, hinv, u', hu'mem, hu'x⟩ :=
    exists_section_tensorBaseRing_of_strictlyHenselian F hsource htarget hstab Λ bc bc' x hx
  obtain ⟨e, he, hker, hinve, hmem⟩ :=
    exists_isIdempotentElem_ker_tensorRetraction_of_section F bc bc' hσ hinv
  obtain ⟨D₀, hCR₀, hAlg₀, hEt₀, h₀, g₀, hg₀, hcompat₀⟩ :=
    exists_etale_stage_map F hΛ
      (bc'.objectsProjection.appTop ≫ σ.appTop ≫ (objectsBaseChangeIso bc).inv)
      (appTop_comp_section_comp_objectsBaseChangeIso_inv F bc bc' hσ)
  obtain ⟨e₀, he₀, hker₀⟩ := exists_isIdempotentElem_ker_tensorRetraction F g₀ hg₀
  have heΛ := eq_map_of_ker_eq_span_singleton F g₀ hg₀ h₀
    (bc'.objectsProjection.appTop ≫ σ.appTop ≫ (objectsBaseChangeIso bc).inv)
    (appTop_comp_section_comp_objectsBaseChangeIso_inv F bc bc' hσ) hcompat₀ e₀ e he₀ he
    hker₀ hker
  have hEqΛ := (map_push (sourceAlgHomOfHom F) h₀ heΛ).trans
    (hinve.trans (map_push (targetAlgHomOfHom F) h₀ heΛ).symm)
  obtain ⟨D, hCRD, hAlgD, hEtD, h', φ, hφ, heqφ⟩ :=
    StacksDraft.exists_etale_stage_eq_of_indEtale hΛ inferInstance h₀ _ _ hEqΛ
  obtain ⟨gD, hgD, hcompatD⟩ := exists_map_of_algHom F φ g₀ hg₀
  obtain ⟨eD, heD, hkerD⟩ := exists_isIdempotentElem_ker_tensorRetraction F gD hgD
  have hεeq := eq_map_of_ker_eq_span_singleton F g₀ hg₀ φ gD hgD hcompatD e₀ eD he₀ heD
    hker₀ hkerD
  have hinvD := map_eq_of_map_eq (sourceAlgHomOfHom F) (targetAlgHomOfHom F) φ hεeq heqφ
  have heD' := eq_map_of_eq_map_comp h' φ hφ heΛ hεeq
  obtain ⟨bcD⟩ := exists_affineInvariantBaseChange G D
  obtain ⟨bcD'⟩ := exists_affineInvariantBaseChange G' (tensorBaseRing F D)
  obtain ⟨σD, hoiD, hσD, hclD, hinvDset, hmemD⟩ :=
    exists_section_of_isIdempotentElem_ker_tensorRetraction F bcD bcD' gD hgD eD hkerD hinvD
  have hbridge : (tensorBaseRingComparison F h' bcD' bc').appTop.hom
        ((objectsTensorBaseRingIso F D bcD').hom eD) =
      (objectsTensorBaseRingIso F Λ bc').hom e :=
    (appTop_tensorBaseRingComparison F h' bcD' bc' eD).trans
      (congrArg (objectsTensorBaseRingIso F Λ bc').hom.hom heD'.symm)
  obtain ⟨vD, hvD⟩ : (tensorBaseRingComparison F h' bcD' bc').base u' ∈ Set.range σD.base :=
    (hmemD _).mpr (mem_asIdeal_of_appTop_eq (tensorBaseRingComparison F h' bcD' bc') u'
      hbridge ((hmem u').mp hu'mem))
  have := hEtD
  have hEtAt := etaleAt_specMap_tensorBaseRingMap_of_section F hsource D bcD bcD' hoiD hσD
    hclD hinvDset vD
  have h1 := base_apply_eq_of_eq bcD'.objects_isPullback.w (σD.base vD)
  have h2 := base_apply_eq_of_eq (tensorBaseRingComparison_comp_objectsProjection F h' bcD' bc') u'
  have h3 := base_apply_eq_of_eq bc'.objects_isPullback.w u'
  have hB : bcD'.objectsProjection.base (σD.base vD) = bc'.objectsProjection.base u' :=
    (congrArg (fun z : bcD'.groupoid.objects.left => bcD'.objectsProjection.base z) hvD).trans h2
  have hpt : (invariantSpectrumMap G' (tensorBaseRing F D)).base
      (bcD'.groupoid.objects.hom.base (σD.base vD)) = p' :=
    h1.symm.trans
      ((congrArg (fun z : G'.objects.left => (objectsToInvariantSpectrum G').base z) hB).trans
        (h3.trans ((congrArg (fun z : Spec (.of (tensorBaseRing F Λ)) =>
          (invariantSpectrumMap G' (tensorBaseRing F Λ)).base z) hu'x).trans hp)))
  refine exists_etale_comp_specMap_of_etaleAt (invariantRingMap F)
    (algebraMap (invariantRing G) D) (tensorBaseRingMap F D)
    (algebraMap (invariantRing G') (tensorBaseRing F D))
    (tensorBaseRing_compatible F D) etale_specMap_algebraMap etale_specMap_algebraMap hEtAt hpt

/-- **The étale cover of a neighbourhood of one point of `Spec C'`.** For each point `p'` of
`Spec C'` there is an étale morphism onto a neighbourhood of `p'` whose composite with
`Spec C' ⟶ Spec C` is étale.

The extension used is the strict henselization of `C` at the image `p` of `p'`, which is flat,
strictly henselian local and ind-étale over `C`; the chosen point of `Spec (C' ⊗[C] C^{sh}_p)`
exists because that spectrum is the fibre product `Spec C' ×_{Spec C} Spec C^{sh}_p` and the
closed point of `Spec C^{sh}_p` lies over `p`. -/
theorem exists_etale_comp_invariantRingMap
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (p' : Spec (.of (invariantRing G'))) :
    ∃ (W : Scheme.{u}) (gg : W ⟶ Spec (.of (invariantRing G'))), Etale gg ∧
      Etale (gg ≫ Spec.map (CommRingCat.ofHom (invariantRingMap F))) ∧
      p' ∈ Set.range gg.base := by
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum (invariantRing G),
      (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p' = q := ⟨_, rfl⟩
  have := q.isPrime
  obtain ⟨x, hx1, hx2⟩ := exists_point_of_isPullback
    (isPullback_invariantSpectrumMap_tensorBaseRing F
      (StacksDraft.strictHenselizationAtPrime (invariantRing G) q.asIdeal))
    p' (IsLocalRing.closedPoint _)
    (hq.trans (specMap_base_closedPoint_strictHenselizationAtPrime (invariantRing G) q).symm)
  exact exists_etale_comp_of_indEtale F hsource htarget hstab _
    (StacksDraft.indEtale_strictHenselizationAtPrime _ _) p' x hx2 hx1

/-- **The first conclusion of [Stacks Project, Tag 0DT9]: the map `C ⟶ C'` from the `R`-invariant
functions on `U` to the `R'`-invariant functions on `U'` is étale.**

The four hypotheses of the source are all present: that `U`, `R`, `U'`, `R'` are affine is the four
`IsAffine` instances; that `s`, `t`, `s'`, `t'` are finite locally free is the four
`IsFiniteLocallyFree` instances; the three cartesian squares are `hsource`, `htarget` and `hstab`;
and that `f : U' → U` is étale is `[Etale F.mapObjects.left]`.

Étaleness is checked point by point with the source-cover criterion
`AlgebraicGeometry.etale_of_forall_exists_etale_comp`, whose covering family is supplied by
`AlgebraicGeometry.GroupoidScheme.exists_etale_comp_invariantRingMap`. No finite presentation
hypothesis on `Spec C' ⟶ Spec C` is needed, which matters because local finite presentation is
itself part of the conclusion. -/
@[stacks 0DT9 "the FIRST conclusion: the map C -> C' from the R-invariant functions on U to the \
R'-invariant functions on U' is etale. Together with isPullback_mapObjects, which is the second \
conclusion, this is the whole statement of the tag"]
theorem etale_invariantRingMap
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left) :
    (invariantRingMap F).Etale :=
  HasRingHomProperty.Spec_iff.mp
    (etale_of_forall_exists_etale_comp (Spec.map (CommRingCat.ofHom (invariantRingMap F)))
      fun p' => exists_etale_comp_invariantRingMap F hsource htarget hstab p')

/-- **The second conclusion of [Stacks Project, Tag 0DT9]: `U' = Spec C' ×_{Spec C} U`.**

This is `AlgebraicGeometry.GroupoidScheme.isPullback_mapObjects_of_etale_invariantRingMap` with its
hypothesis `hC` discharged by
`AlgebraicGeometry.GroupoidScheme.etale_invariantRingMap`, the first conclusion of the tag. The
cartesian `s'/s` square is not needed for the implication from the first conclusion to the second,
but it is a hypothesis of the first, so it appears here too. -/
@[stacks 0DT9 "the SECOND conclusion: U' is the fibre product of Spec C' and U over Spec C. \
Unconditional: the premise that C -> C' is etale is supplied by etale_invariantRingMap, the tag's \
first conclusion"]
theorem isPullback_mapObjects
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left) :
    IsPullback F.mapObjects.left (objectsToInvariantSpectrum G')
      (objectsToInvariantSpectrum G) (Spec.map (CommRingCat.ofHom (invariantRingMap F))) :=
  isPullback_mapObjects_of_etale_invariantRingMap F htarget hstab
    (etale_invariantRingMap F hsource htarget hstab)

end Chaining

end GroupoidScheme

end AlgebraicGeometry

end

end
