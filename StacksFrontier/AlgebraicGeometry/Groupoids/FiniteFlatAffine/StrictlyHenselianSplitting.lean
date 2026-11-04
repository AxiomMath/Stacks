module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantFibreFinite
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.StrictlyHenselianFibre
public import StacksFrontier.AlgebraicGeometry.Scheme.GlobalEvaluation
public import StacksFrontier.RingTheory.Henselian.Pair.EtaleSplittingFibre

/-!
# The splitting of the object ring over a strictly henselian invariant ring

This file is the **"Claim" of [Stacks Project, Tag 0DT9]** at the level of rings: if `C` is
strictly henselian and `p'` is a point of `Spec C'` over the closed point of `Spec C`, then
`A' = Γ(U', ⊤)` splits as a product `A × A''` of `A = Γ(U, ⊤)`-algebras, with the first
projection a retraction of `A → A'`.

The three inputs are the ones the preceding files supply: the bijection of fibres
`U'_{p'} ⟶ U_p` (`bijective_invariantFibreMap_of_strictlyHenselian`), the finiteness of the fibre
(`finite_fibre_objectsToInvariantSpectrum`), and the bijectivity of the residue field maps along
it (`bijective_residueFieldMap_mapObjects_of_strictlyHenselian`). The splitting itself is the
henselian-pair criterion `exists_algEquiv_prod_of_etale_of_henselianPair_of_le`, whose hypothesis
`A ⧸ J → A' ⧸ J'` is recognised from the fibre data by
`RingHom.bijective_quotientMap_of_bijective_comapRestrict`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isMaximal_toSpecΓ_base_of_isMaximal`: a point of `U` over a
  closed point of `Spec C` cuts out a maximal ideal of `A`.
* `AlgebraicGeometry.GroupoidScheme.surjective_globalEvaluation_objects`: at such a point, global
  functions on `U` surject onto the residue field.
* `AlgebraicGeometry.GroupoidScheme.isMaximal_toSpecΓ_base_mapObjects`: a point of `U'` over the
  closed point of `Spec C` cuts out a maximal ideal of `A'`.
* `AlgebraicGeometry.GroupoidScheme.isMaximal_asIdeal_of_comap_eq_closedPoint`: **a point of
  `Spec C'` over the closed point of `Spec C` is a closed point**, which is the fact that lets the
  fibre `U'_{p'}` be cut out by `invariantFibreIdeal G' p'`.
* `AlgebraicGeometry.GroupoidScheme.exists_algEquiv_prod_appTop_of_strictlyHenselian`: **the
  splitting `A' ≃ A × A''`**, which is the "Claim" of [Stacks Project, Tag 0DT9] at the level of
  rings, together with the containment of the kernel of the retraction in the ideal cutting out
  the fibre `U'_{p'}`.

## Implementation notes

Maximality upstairs is obtained from the *evaluation map* rather than from quasi-finiteness of an
étale algebra: `AlgebraicGeometry.surjective_globalEvaluation_comp` makes `A' ⟶ κ(u')` surjective
out of surjectivity of `A ⟶ κ(u)` and of the residue field map, and a point whose evaluation map
is surjective cuts out a maximal ideal. Maximality of `p'` in `C'` then follows by contracting
along the integral extension `C' ⊆ A'` (Tag 03BJ for `G'`).

## References

* [Stacks Project, Tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-! ### Closed points of the object scheme -/

/-- **A point of `U` lying over a closed point of `Spec C` cuts out a maximal ideal of
`Γ(U, ⊤)`.** The ring of global functions is integral over the invariant ring (Tag 03BJ), and a
prime of an integral extension over a maximal ideal is maximal. -/
theorem isMaximal_toSpecΓ_base_of_isMaximal (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] (u : G.objects.left)
    (hu : ((objectsToInvariantSpectrum G).base u).asIdeal.IsMaximal) :
    (G.objects.left.toSpecΓ.base u).asIdeal.IsMaximal := by
  let _ : (G.objects.left.toSpecΓ.base u).asIdeal.IsPrime :=
    (G.objects.left.toSpecΓ.base u).isPrime
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'
    (CommRingCat.ofHom (invariantRing G).subtype).hom (isIntegral_invariantRing G) _ hu

/-- **At a point of `U` over a closed point of `Spec C`, global functions on `U` surject onto the
residue field.** -/
theorem surjective_globalEvaluation_objects (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] (u : G.objects.left)
    (hu : ((objectsToInvariantSpectrum G).base u).asIdeal.IsMaximal) :
    Function.Surjective (G.objects.left.globalEvaluation u).hom :=
  G.objects.left.surjective_globalEvaluation u (isMaximal_toSpecΓ_base_of_isMaximal G u hu)

/-! ### Closed points of the object scheme upstairs -/

/-- A point of `U'` over a point of `Spec C'` above the closed point of `Spec C` lies over the
closed point of `Spec C`. -/
private theorem base_objectsToInvariantSpectrum_mapObjects_eq_closedPoint
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsAffine G'.objects.left]
    [IsAffine G'.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsFiniteLocallyFree G'.source.left]
    [IsFiniteLocallyFree G'.target.left] [IsLocalRing (invariantRing G)] {u' : G'.objects.left}
    {p' : Spec (.of (invariantRing G'))} (hu' : (objectsToInvariantSpectrum G').base u' = p')
    (hp' : (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p' =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    (objectsToInvariantSpectrum G).base (F.mapObjects.left.base u') =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G))) := by
  rw [base_objectsToInvariantSpectrum_mapObjects, hu', hp']

section StrictlyHenselian

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
  [StrictlyHenselianLocalRing (invariantRing G)] [Etale F.mapObjects.left]

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- The closed point of `Spec C` is a maximal ideal of `C`. -/
theorem isMaximal_asIdeal_closedPoint :
    ((IsLocalRing.closedPoint (invariantRing G) :
      Spec (.of (invariantRing G)))).asIdeal.IsMaximal :=
  IsLocalRing.maximalIdeal.isMaximal _

omit [IsAffine G'.objects.left] [IsAffine G'.arrows.left] [IsFiniteLocallyFree G'.source.left]
  [IsFiniteLocallyFree G'.target.left] [Etale F.mapObjects.left] in
/-- At a point of `U'` over the closed point of `Spec C`, global functions on `U` surject onto
the residue field of its image. -/
theorem surjective_globalEvaluation_base_mapObjects (u' : G'.objects.left)
    (hu' : (objectsToInvariantSpectrum G).base (F.mapObjects.left.base u') =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    Function.Surjective (G.objects.left.globalEvaluation (F.mapObjects.left.base u')).hom :=
  surjective_globalEvaluation_objects G _ (by
    rw [hu']
    exact isMaximal_asIdeal_closedPoint)

omit [IsAffine G'.objects.left] [IsAffine G'.arrows.left] [IsFiniteLocallyFree G'.source.left]
  [IsFiniteLocallyFree G'.target.left] in
/-- **Global functions on `U'` surject onto the residue field at a point of the closed fibre.**
The composite `A ⟶ κ(u) ⟶ κ(u')` is surjective: the first map because `u` is a closed point of
`U` and the second because `U' ⟶ U` is étale and `κ(u)` is separably closed. -/
theorem surjective_globalEvaluation_mapObjects (u' : G'.objects.left)
    (hu' : (objectsToInvariantSpectrum G).base (F.mapObjects.left.base u') =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    Function.Surjective (G'.objects.left.globalEvaluation u').hom :=
  surjective_globalEvaluation_comp F.mapObjects.left u'
    (surjective_globalEvaluation_base_mapObjects F u' hu')
    (bijective_residueFieldMap_mapObjects_of_strictlyHenselian F u' hu').surjective

omit [IsAffine G'.objects.left] [IsAffine G'.arrows.left] [IsFiniteLocallyFree G'.source.left]
  [IsFiniteLocallyFree G'.target.left] in
/-- **A point of `U'` over the closed point of `Spec C` cuts out a maximal ideal of
`Γ(U', ⊤)`.** -/
theorem isMaximal_toSpecΓ_base_mapObjects (u' : G'.objects.left)
    (hu' : (objectsToInvariantSpectrum G).base (F.mapObjects.left.base u') =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    (G'.objects.left.toSpecΓ.base u').asIdeal.IsMaximal :=
  isMaximal_asIdeal_toSpecΓ_base u' (surjective_globalEvaluation_mapObjects F u' hu')

/-- **A point of `Spec C'` lying over the closed point of `Spec C` is a closed point.**

Pick a point `u'` of `U'` above it, which exists because `U' ⟶ Spec C'` is surjective. Then `u'`
cuts out a maximal ideal of `Γ(U', ⊤)`, and `Γ(U', ⊤)` is integral over `C'` (Tag 03BJ), so the
contraction is maximal. -/
theorem isMaximal_asIdeal_of_comap_eq_closedPoint (p' : Spec (.of (invariantRing G')))
    (hp' : (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p' =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    p'.asIdeal.IsMaximal := by
  obtain ⟨u', hu'⟩ := surjective_objectsToInvariantSpectrum G' p'
  have := isMaximal_toSpecΓ_base_mapObjects F u'
    (base_objectsToInvariantSpectrum_mapObjects_eq_closedPoint F hu' hp')
  have hcomp : p'.asIdeal =
      (G'.objects.left.toSpecΓ.base u').asIdeal.comap
        (CommRingCat.ofHom (invariantRing G').subtype).hom := by
    rw [← hu']
    rfl
  rw [hcomp]
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    (CommRingCat.ofHom (invariantRing G').subtype).hom (isIntegral_invariantRing G') _

/-! ### The splitting -/

omit [IsAffine G'.arrows.left] [IsFiniteLocallyFree G'.source.left]
  [IsFiniteLocallyFree G'.target.left] in
/-- The fibre of `U'` over a point of `Spec C'` above the closed point of `Spec C`, read as a
point of `U'`. -/
private theorem comap_subtype_toSpecΓ_base_symm (p' : Spec (.of (invariantRing G')))
    (q : PrimeSpectrum Γ(G'.objects.left, ⊤))
    (hq : PrimeSpectrum.comap (invariantRing G').subtype q = p') :
    (objectsToInvariantSpectrum G').base
      (G'.objects.left.carrierEquivPrimeSpectrum.symm q) = p' := by
  rwa [objectsToInvariantSpectrum_base, show G'.objects.left.isoSpec.hom.base
      (G'.objects.left.carrierEquivPrimeSpectrum.symm q) = q from
    G'.objects.left.carrierEquivPrimeSpectrum.apply_symm_apply q]

/-- **The "Claim" of [Stacks Project, Tag 0DT9], at the level of rings.** If the invariant ring
`C` is strictly henselian and `p'` is a point of `Spec C'` over the closed point of `Spec C`,
then `A' = Γ(U', ⊤)` splits as a product `A × A''` of `A = Γ(U, ⊤)`-algebras, the first
projection being a retraction of `A ⟶ A'`.

The radical ideal along which the splitting is taken is `invariantFibreIdeal G' p'`, the one
cutting out the fibre `U'_{p'}`; the henselian pair is `(A, √(m A))`, which is a henselian pair
because `A` is integral over the henselian local ring `C` (Tags 09XK and 09XJ); and the
bijectivity of `A ⧸ √(m A) → A' ⧸ J'` is read off the fibre, from the bijection
`U'_{p'} ⟶ U_p`, its finiteness, and the identification of the residue fields along it.

The kernel of the retraction is moreover contained in `J'`, which geometrically says that the
fibre `U'_{p'}` lies in the sheet of `Spec A'` cut out by the retraction. That is the reduction
statement of the splitting criterion: `τ` reduces modulo `J'` to the inverse of
`A ⧸ J → A' ⧸ J'`, so an element killed by `τ` is already zero in `A' ⧸ J'`. -/
theorem exists_algEquiv_prod_appTop_of_strictlyHenselian
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (p' : Spec (.of (invariantRing G')))
    (hp' : (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p' =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    letI : Algebra Γ(G.objects.left, ⊤) Γ(G'.objects.left, ⊤) :=
      F.mapObjects.left.appTop.hom.toAlgebra
    ∃ (A'' : Type u) (_ : CommRing A'') (_ : Algebra Γ(G.objects.left, ⊤) A'')
      (τ : Γ(G'.objects.left, ⊤) →ₐ[Γ(G.objects.left, ⊤)] Γ(G.objects.left, ⊤))
      (e : Γ(G'.objects.left, ⊤) ≃ₐ[Γ(G.objects.left, ⊤)] Γ(G.objects.left, ⊤) × A''),
      (∀ x : Γ(G'.objects.left, ⊤), (e x).1 = τ x) ∧
        RingHom.ker τ ≤ invariantFibreIdeal G' p' := by
  let : Algebra Γ(G.objects.left, ⊤) Γ(G'.objects.left, ⊤) :=
    F.mapObjects.left.appTop.hom.toAlgebra
  let : Algebra (invariantRing G) Γ(G.objects.left, ⊤) := (invariantRing G).subtype.toAlgebra
  have : Algebra.IsIntegral (invariantRing G) Γ(G.objects.left, ⊤) :=
    ⟨isIntegral_invariantRing G⟩
  have : Algebra.Etale Γ(G.objects.left, ⊤) Γ(G'.objects.left, ⊤) :=
    RingHom.etale_algebraMap.mp
      (HasRingHomProperty.appTop (P := @Etale) F.mapObjects.left inferInstance)
  have hcp : PrimeSpectrum.comap (invariantRingMap F) p' =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G))) := hp'
  have hp'max : p'.asIdeal.IsMaximal := isMaximal_asIdeal_of_comap_eq_closedPoint F p' hp'
  have hpmax : (PrimeSpectrum.comap (invariantRingMap F) p').asIdeal.IsMaximal := by
    rw [hcp]
    exact isMaximal_asIdeal_closedPoint
  have hJ' := invariantFibreIdeal_le_comap F p'
  have hI : HenselianPair Γ(G.objects.left, ⊤)
      (invariantFibreIdeal G (PrimeSpectrum.comap (invariantRingMap F) p')) := by
    rw [hcp]
    exact henselianPair_radical_map_maximalIdeal_of_isIntegral (C := invariantRing G) _
  have hbij : Function.Bijective (Ideal.quotientMapₐ (invariantFibreIdeal G' p')
      (Algebra.ofId Γ(G.objects.left, ⊤) Γ(G'.objects.left, ⊤)) hJ') := by
    refine RingHom.bijective_quotientMap_of_bijective_comapRestrict
      F.mapObjects.left.appTop.hom hJ' (Ideal.radical_isRadical _)
      (invariantFibreIdeal_isRadical G' p')
      (finite_primes_invariantFibreIdeal G _ hpmax) (fun q hq => ?_)
      (bijective_comapRestrict_invariantFibreIdeal F p' hp'max hpmax
        (bijective_invariantFibreMap_of_strictlyHenselian F hsource htarget hstab p' hp'))
      (fun q hq y => ?_)
    · rw [hcp] at hq
      exact Ideal.isMaximal_of_radical_map_isMaximal_le
        (IsLocalRing.maximalIdeal.isMaximal (invariantRing G)) q.asIdeal hq
    · set u' := G'.objects.left.carrierEquivPrimeSpectrum.symm q
      have hbase : G'.objects.left.toSpecΓ.base u' = q :=
        G'.objects.left.carrierEquivPrimeSpectrum.apply_symm_apply q
      have hfib : (objectsToInvariantSpectrum G').base u' = p' :=
        comap_subtype_toSpecΓ_base_symm p' q
          ((PrimeSpectrum.comap_eq_iff_radical_map_le _ hp'max q).mpr hq)
      have himg := base_objectsToInvariantSpectrum_mapObjects_eq_closedPoint F hfib hp'
      obtain ⟨a, ha⟩ := exists_sub_mem_asIdeal_of_surjective_residueFieldMap F.mapObjects.left u'
        (surjective_globalEvaluation_base_mapObjects F u' himg)
        (bijective_residueFieldMap_mapObjects_of_strictlyHenselian F u' himg).surjective y
      exact ⟨a, hbase ▸ ha⟩
  obtain ⟨A'', _, _, τ, e, he, hred⟩ :=
    exists_algEquiv_prod_of_etale_of_henselianPair_of_le hI Γ(G'.objects.left, ⊤) hJ' hbij
  refine ⟨A'', inferInstance, inferInstance, τ, e, he, fun x hx => ?_⟩
  have hq := hred x
  rw [RingHom.mem_ker.mp hx, map_zero, map_zero] at hq
  exact Ideal.Quotient.eq_zero_iff_mem.mp hq.symm

end StrictlyHenselian

end AlgebraicGeometry.GroupoidScheme

end

end
