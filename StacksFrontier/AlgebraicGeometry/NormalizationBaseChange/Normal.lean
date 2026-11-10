module

public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Separable
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE

/-!
# Normality of the normalization of a scheme

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components. Its
normalization `X.normalizationScheme hX` is a normal scheme, the normalization morphism carries
generic points of irreducible components to generic points of irreducible components, and for a
normal `X` the normalization morphism is an isomorphism. Separately, a normal scheme over a field
stays normal after base change along a separable extension of the ground field.

## Main results

* `AlgebraicGeometry.Scheme.isNormal_normalizationScheme`: the normalization of `X` is normal.
* `AlgebraicGeometry.Scheme.normalization_mem_genericPoints`: the normalization morphism carries
  generic points of irreducible components to generic points of irreducible components.  This is
  the hypothesis under which the universal property of the normalization (Tag 035Q part (4))
  applies to the normalization morphism itself.
* `AlgebraicGeometry.Scheme.isIso_normalization_of_isNormal`: the normalization morphism of a
  normal scheme is an isomorphism.
* `AlgebraicGeometry.Scheme.isIso_normalization_iff_isNormal` is Tag 0H7D: the normalization
  morphism is an isomorphism exactly when the scheme is normal.
* `AlgebraicGeometry.isNormal_pullback_of_isSeparableExtension` is Tag 0C3M.

Two statements of independent interest are proved along the way:
`AlgebraicGeometry.mem_genericPoints_of_forall_comap_minimalPrimes` reduces the generic-point
condition on a morphism to a condition on minimal primes of affine charts, and
`AlgebraicGeometry.comap_mem_minimalPrimes_of_map_nonZeroDivisors` is the ring-level statement it
is applied to.

## Implementation notes

Everything is checked on the open cover of the normalization by the preimages of the affine opens
of `X`. Over an affine open `U = Spec A` the normalization is `Spec` of the integral closure `A'`
of `A` in its total ring of fractions
(`AlgebraicGeometry.preimageNormalizationIsoSpecIntegralClosure`), and that integral closure is a
normal ring whenever `A` is reduced with finitely many minimal primes
(`isNormalRing_integralClosure_fractionRing_of_finite_minimalPrimes`). The reduction to a reduced
`X` is `AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_reduction`.

For the generic points the point is that `A → A'` carries non-zerodivisors to non-zerodivisors:
a non-zerodivisor of `A` becomes a unit in the total ring of fractions, hence a non-zerodivisor in
the subring `A'`. In a reduced ring the non-zerodivisors are exactly the elements lying in no
minimal prime, so a minimal prime of `A'` meets no non-zerodivisor of `A`, and prime avoidance
over the finitely many minimal primes of `A` then puts its contraction inside — hence equal to —
one of them. The statement for a general `X` is transported from the reduced case along the
reduction isomorphism, using that the closed immersion of the reduction is a homeomorphism.

For a normal `X` the map `A → A'` is bijective, because a normal ring is integrally closed in its
total ring of fractions (Tag 034M, in the form
`IsNormalRing.exists_algebraMap_eq_of_isIntegral`), so the normalization morphism is an
isomorphism locally on the target.

## References

* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
* [Stacks Project, Tag 0C3M](https://stacks.math.columbia.edu/tag/0C3M)
* [Stacks Project, Tag 0H7D](https://stacks.math.columbia.edu/tag/0H7D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Transport of normality -/

/-- The spectrum of a normal ring is a normal scheme. -/
theorem isNormal_spec_of_isNormalRing {R : Type u} [CommRing R] (hR : IsNormalRing R) :
    IsNormal (Spec (.of R)) := by
  have h : IsNormal (Spec (CommRingCat.of R)) ↔
      ∃ (I : Type u) (U : I → (Spec (CommRingCat.of R)).affineOpens),
        IsOpenCover (fun i ↦ (U i : (Spec (CommRingCat.of R)).Opens)) ∧
          ∀ i, IsNormalRing Γ(Spec (CommRingCat.of R), U i) :=
    (isNormal_tfae _).out 1 3
  refine h.mpr ⟨PUnit, fun _ ↦ ⟨⊤, isAffineOpen_top _⟩, IsOpenCover.mk (by simp), fun _ ↦ ?_⟩
  exact IsNormalRing.congr
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv hR

namespace Scheme

/-! ### Normality of the normalization -/

/-- The normalization of a reduced scheme whose quasi-compact opens have finitely many
irreducible components is normal. -/
@[ega "II 6.3.8" "partial"]
theorem isNormal_normalizationScheme_of_isReduced (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsNormal (X.normalizationScheme hX) := by
  have h : IsNormal (X.normalizationScheme hX) ↔
      ∃ (I : Type u) (U : I → (X.normalizationScheme hX).Opens),
        IsOpenCover U ∧ ∀ i, IsNormal (U i).toScheme :=
    (isNormal_tfae _).out 1 4
  refine h.mpr
    ⟨X.affineOpens, fun V ↦ X.normalization hX ⁻¹ᵁ V.1, IsOpenCover.mk ?_, fun V ↦ ?_⟩
  · refine top_unique fun z _ ↦ ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (X.normalization hX z)) isOpen_univ
    exact Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩
  · have hV : IsAffineOpen V.1 := V.2
    let : _root_.IsReduced Γ(X, V.1) := IsReduced.component_reduced V.1
    let := isNormal_spec_of_isNormalRing
      (isNormalRing_integralClosure_fractionRing_of_finite_minimalPrimes
        (A := Γ(X, V.1)) (finite_minimalPrimes_of_affine_open hX V.1 hV.isoSpec.symm))
    exact AlgebraicGeometry.isNormal_of_iso
      (preimageNormalizationIsoSpecIntegralClosure hX V.1 hV.isoSpec.symm)

/-- The normalization of a scheme whose quasi-compact opens have finitely many irreducible
components is a normal scheme.  This is half of **Stacks Project, Tag 035Q** part (1); the tag
is withheld because the disjoint-union statement of part (1) is not proved here. -/
@[ega "II 6.3.6" "special case"]
theorem isNormal_normalizationScheme (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsNormal (X.normalizationScheme hX) := by
  obtain ⟨e, -⟩ := X.exists_normalizationScheme_iso_reduction hX
  have : IsReduced X.nilradical.subscheme := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := X) ⊤
  have := X.nilradical.subscheme.isNormal_normalizationScheme_of_isReduced
    (X.finite_irreducibleComponents_reduction hX)
  exact AlgebraicGeometry.isNormal_of_iso e

end Scheme

/-! ### Generic points of the normalization -/

/-- A morphism of schemes carries generic points to generic points as soon as it does so, at the
level of minimal primes, on affine charts around every point of the source.  This is the converse
of the chart-level reading of the generic-point hypothesis used for Tag 035Q part (4). -/
theorem mem_genericPoints_of_forall_comap_minimalPrimes {X Z : Scheme.{u}} (f : Z ⟶ X)
    (h : ∀ z : Z, ∃ (U : X.Opens) (V : Z.Opens) (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ U), z ∈ V ∧
        ∀ q ∈ minimalPrimes Γ(Z, V),
          Ideal.comap (f.appLE U V hVU).hom q ∈ minimalPrimes Γ(X, U))
    {z : Z} (hz : z ∈ genericPoints Z) : f z ∈ genericPoints X := by
  obtain ⟨U, V, hU, hV, hVU, hzV, hmin⟩ := h z
  have hfzU : f z ∈ U := hVU hzV
  have hq : (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ∈ minimalPrimes Γ(Z, V) := by
    have hmem := (genericPointsInOpenEquivMinimalPrimes hV ⟨⟨z, hz⟩, hzV⟩).2
    rwa [genericPointsInOpenEquivMinimalPrimes_asIdeal hV ⟨⟨z, hz⟩, hzV⟩] at hmem
  have hcomap : Ideal.comap (f.appLE U V hVU).hom (hV.primeIdealOf ⟨z, hzV⟩).asIdeal =
      (hU.primeIdealOf ⟨f z, hfzU⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hzV)
  have hpmin : (hU.primeIdealOf ⟨f z, hfzU⟩).asIdeal ∈ minimalPrimes Γ(X, U) :=
    hcomap ▸ hmin _ hq
  set ξ := (genericPointsInOpenEquivMinimalPrimes hU).symm
    ⟨(hU.primeIdealOf ⟨f z, hfzU⟩).asIdeal, hpmin⟩ with hξdef
  have hξ : (hU.primeIdealOf ⟨ξ.1.1, ξ.2⟩).asIdeal =
      (hU.primeIdealOf ⟨f z, hfzU⟩).asIdeal := by
    rw [← genericPointsInOpenEquivMinimalPrimes_asIdeal hU ξ, hξdef]
    exact congrArg (fun p : minimalPrimes Γ(X, U) ↦ (p : Ideal Γ(X, U)))
      ((genericPointsInOpenEquivMinimalPrimes hU).apply_symm_apply _)
  have hpt : (⟨ξ.1.1, ξ.2⟩ : U.toScheme) = ⟨f z, hfzU⟩ :=
    hU.isoSpec.hom.homeomorph.injective (PrimeSpectrum.ext hξ)
  have hval : (ξ.1.1 : X) = f z := congrArg (fun x : U.toScheme ↦ (x.1 : X)) hpt
  rw [← hval]
  exact ξ.1.2

/-- A ring map between reduced rings carrying non-zerodivisors to non-zerodivisors pulls minimal
primes back to minimal primes, provided the source has only finitely many minimal primes.

This is what makes the normalization morphism carry generic points to generic points: on an affine
chart it is the inclusion of a ring into its integral closure inside the total ring of fractions,
and a non-zerodivisor becomes a unit there. -/
theorem comap_mem_minimalPrimes_of_map_nonZeroDivisors {A C : Type u} [CommRing A] [CommRing C]
    [_root_.IsReduced A] [_root_.IsReduced C] (φ : A →+* C) (hA : (minimalPrimes A).Finite)
    (hreg : ∀ s ∈ nonZeroDivisors A, φ s ∈ nonZeroDivisors C)
    {q : Ideal C} (hq : q ∈ minimalPrimes C) :
    q.comap φ ∈ minimalPrimes A := by
  classical
  have hqp : q.IsPrime := hq.1.1
  have hp : (q.comap φ).IsPrime := hqp.comap φ
  have hsub : ((q.comap φ : Ideal A) : Set A) ⊆ ⋃ p ∈ (↑hA.toFinset : Set (Ideal A)), p := by
    intro a ha
    by_contra hnot
    refine hreg a ?_ |> fun hreg' ↦
      (mem_nonZeroDivisors_iff_forall_notMem_minimalPrimes (φ a)).mp hreg' q hq ha
    rw [mem_nonZeroDivisors_iff_forall_notMem_minimalPrimes]
    intro p hpmin hap
    exact hnot (Set.mem_biUnion (hA.mem_toFinset.mpr hpmin) hap)
  obtain ⟨p, hpmem, hle⟩ :=
    (Ideal.subset_union_prime (⊥ : Ideal A) ⊥
      (fun i hi _ _ ↦ (hA.mem_toFinset.mp hi).1.1)).mp hsub
  have hpmin : p ∈ minimalPrimes A := hA.mem_toFinset.mp hpmem
  have hge : p ≤ q.comap φ := hpmin.2 ⟨hp, bot_le⟩ hle
  exact le_antisymm hle hge ▸ hpmin

/-- If, over an affine open `U`, every non-zerodivisor of `Γ(X, U)` becomes a unit in
`Γ(Y, g ⁻¹ᵁ U)`, then the relative normalization of `X` in `Y` carries non-zerodivisors to
non-zerodivisors over `U`: on that chart the normalization is the inclusion of `Γ(X, U)` into its
integral closure inside `Γ(Y, g ⁻¹ᵁ U)`. -/
theorem fromNormalization_app_mem_nonZeroDivisors {Y X : Scheme.{u}} (g : Y ⟶ X)
    [QuasiCompact g] [QuasiSeparated g] (U : X.Opens) (hU : IsAffineOpen U)
    (hunit : ∀ t ∈ nonZeroDivisors Γ(X, U), IsUnit ((g.app U).hom t))
    {s : Γ(X, U)} (hs : s ∈ nonZeroDivisors Γ(X, U)) :
    (g.fromNormalization.app U).hom s ∈
      nonZeroDivisors Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U) := by
  let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  set C := integralClosure Γ(X, U) Γ(Y, g ⁻¹ᵁ U) with hC
  have hunitS : IsUnit (algebraMap Γ(X, U) Γ(Y, g ⁻¹ᵁ U) s) := hunit s hs
  have h0 : (algebraMap Γ(X, U) Γ(Y, g ⁻¹ᵁ U) s) ∈ nonZeroDivisors Γ(Y, g ⁻¹ᵁ U) :=
    IsUnit.mem_nonZeroDivisors hunitS
  have hregC : algebraMap Γ(X, U) C s ∈ nonZeroDivisors C := by
    refine mem_nonZeroDivisors_of_injective (f := (Subalgebra.val C).toRingHom)
      (fun a b hab ↦ Subtype.ext hab) ?_
    simpa using h0
  have happ := Scheme.Hom.fromNormalization_app g hU
  have hval : (g.fromNormalization.app U).hom s =
      (g.normalizationObjIso hU).inv.hom (algebraMap Γ(X, U) C s) :=
    congrArg (fun φ : Γ(X, U) ⟶ Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U) ↦ φ.hom s) happ
  rw [hval]
  refine mem_nonZeroDivisors_of_injective
    (f := (g.normalizationObjIso hU).hom.hom) ?_ ?_
  · exact ((ConcreteCategory.isIso_iff_bijective
      (g.normalizationObjIso hU).hom).mp inferInstance).1
  · have hcomp : (g.normalizationObjIso hU).hom.hom
        ((g.normalizationObjIso hU).inv.hom (algebraMap Γ(X, U) C s)) =
        algebraMap Γ(X, U) C s := by
      have := (g.normalizationObjIso hU).inv_hom_id
      exact congrArg (fun φ : CommRingCat.of C ⟶ CommRingCat.of C ↦ φ.hom
        (algebraMap Γ(X, U) C s)) this
    rw [hcomp]
    exact hregC

/-- Over an affine open of a reduced scheme, every non-zerodivisor of the ring of sections becomes
a unit in the sections of the generic-point residue spectrum: those sections are the total ring of
fractions. -/
theorem isUnit_app_fromGenericPointResidueFields {X : Scheme.{u}} [IsReduced X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) {s : Γ(X, U)} (hs : s ∈ nonZeroDivisors Γ(X, U)) :
    IsUnit (((Scheme.fromGenericPointResidueFields X).app U).hom s) := by
  classical
  have : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hX U hU.isCompact)).to_subtype
  let : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_injective (Scheme.genericPointsInOpenEquiv X U)
      (Scheme.genericPointsInOpenEquiv X U).injective
  let : Algebra Γ(X, U) Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) :=
    ((Scheme.fromGenericPointResidueFields X).app U).hom.toAlgebra
  let e := genericPreimageSectionsAlgEquivFractionRing U hU
  have h1 : IsUnit (algebraMap Γ(X, U) (FractionRing Γ(X, U)) s) :=
    IsLocalization.map_units (FractionRing Γ(X, U)) ⟨s, hs⟩
  have h2 := h1.map e.symm.toRingEquiv.toRingHom
  change IsUnit (e.symm (algebraMap Γ(X, U) (FractionRing Γ(X, U)) s)) at h2
  rwa [e.symm.commutes] at h2

namespace Scheme

/-- For a reduced scheme, the normalization morphism carries generic points of irreducible
components to generic points of irreducible components. -/
theorem normalization_mem_genericPoints_of_isReduced {X : Scheme.{u}} [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {z : X.normalizationScheme hX} (hz : z ∈ genericPoints (X.normalizationScheme hX)) :
    X.normalization hX z ∈ genericPoints X := by
  classical
  let := quasiCompactFromGenericPointResidueFields X hX
  let := quasiSeparatedFromGenericPointResidueFields X
  have : IsReduced (X.normalizationScheme hX) := isReduced_normalizationScheme X hX
  refine mem_genericPoints_of_forall_comap_minimalPrimes (X.normalization hX) ?_ hz
  intro w
  obtain ⟨_, ⟨U, hU, rfl⟩, hwU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (X.normalization hX w)) isOpen_univ
  refine ⟨U, X.normalization hX ⁻¹ᵁ U, hU, hU.preimage (X.normalization hX), le_rfl, hwU, ?_⟩
  have hredU : _root_.IsReduced Γ(X, U) := IsReduced.component_reduced U
  have hredV : _root_.IsReduced Γ(X.normalizationScheme hX, X.normalization hX ⁻¹ᵁ U) :=
    IsReduced.component_reduced _
  intro q hq
  refine comap_mem_minimalPrimes_of_map_nonZeroDivisors
    ((X.normalization hX).appLE U (X.normalization hX ⁻¹ᵁ U) le_rfl).hom
    (finite_minimalPrimes_of_affine_open hX U hU.isoSpec.symm) ?_ hq
  intro s hs
  rw [Scheme.Hom.appLE_eq_app]
  exact fromNormalization_app_mem_nonZeroDivisors (Scheme.fromGenericPointResidueFields X) U hU
    (fun t ht ↦ isUnit_app_fromGenericPointResidueFields hX U hU ht) hs

end Scheme

/-- Generic points of irreducible components transfer along an isomorphism of schemes. -/
theorem mem_genericPoints_of_iso {A B : Scheme.{u}} (e : A ≅ B) {a : A}
    (ha : a ∈ genericPoints A) : e.hom a ∈ genericPoints B :=
  mem_genericPoints_of_generalizingMap e.hom.isOpenEmbedding.generalizingMap ha

/-- The closed immersion of the reduction is a homeomorphism, so it carries generic points of
irreducible components to generic points of irreducible components. -/
theorem mem_genericPoints_subschemeι_nilradical (X : Scheme.{u})
    {x : X.nilradical.subscheme} (hx : x ∈ genericPoints X.nilradical.subscheme) :
    X.nilradical.subschemeι x ∈ genericPoints X := by
  have hsurj : Function.Surjective X.nilradical.subschemeι := fun y ↦
    Set.mem_range.mp
      (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
  let eX : X.nilradical.subscheme ≃ₜ X :=
    X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hsurj
  exact mem_genericPoints_of_generalizingMap eX.isOpenEmbedding.generalizingMap hx

namespace Scheme

/-- The normalization morphism carries generic points of irreducible components to generic points
of irreducible components.  This is the hypothesis under which Tag 035Q part (4) applies to the
normalization morphism itself. -/
theorem normalization_mem_genericPoints (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {z : X.normalizationScheme hX} (hz : z ∈ genericPoints (X.normalizationScheme hX)) :
    X.normalization hX z ∈ genericPoints X := by
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
  have : IsReduced X.nilradical.subscheme := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := X) ⊤
  have h1 := normalization_mem_genericPoints_of_isReduced
    (X.finite_irreducibleComponents_reduction hX) (mem_genericPoints_of_iso e hz)
  have h2 := mem_genericPoints_subschemeι_nilradical X h1
  have hval : X.normalization hX z = X.nilradical.subschemeι
      (X.nilradical.subscheme.normalization
        (X.finite_irreducibleComponents_reduction hX) (e.hom z)) := by
    rw [← he]
    simp
  rw [hval]
  exact h2

/-- The normalization morphism of a normal scheme is an isomorphism: on an affine chart it is the
inclusion of a normal ring into its integral closure in its total ring of fractions, which is the
identity by Tag 034M. -/
theorem isIso_normalization_of_isNormal (X : Scheme.{u}) [IsNormal X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsIso (X.normalization hX) := by
  have hnormalAffines : IsNormal X ↔ ∀ J : X.affineOpens, IsNormalRing Γ(X, J) :=
    (isNormal_tfae X).out 1 2
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme) (f := X.normalization hX) fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨U, hxU, ?_⟩
  have hredU : _root_.IsReduced Γ(X, U) := IsReduced.component_reduced U
  have hnormU : IsNormalRing Γ(X, U) := hnormalAffines.mp inferInstance ⟨U, hU⟩
  have hbij : Function.Bijective
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U)))) := by
    refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
    · exact IsLocalization.injective (M := nonZeroDivisors Γ(X, U))
        (FractionRing Γ(X, U)) le_rfl (congrArg Subtype.val hab)
    · obtain ⟨a, ha⟩ := hnormU.exists_algebraMap_eq_of_isIntegral b.2
      exact ⟨a, Subtype.ext ha⟩
  have hiso : IsIso (CommRingCat.ofHom
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U))))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hchart := preimageNormalizationIsoSpecIntegralClosure_hom_comp hX U hU.isoSpec.symm
  have heq : (X.normalization hX ∣_ U) =
      ((preimageNormalizationIsoSpecIntegralClosure hX U hU.isoSpec.symm).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U)))))) ≫
        hU.isoSpec.inv := by
    rw [hchart]
    simp
  change IsIso (X.normalization hX ∣_ U)
  rw [heq]
  infer_instance

/-- **Stacks Project, Tag 0H7D.** The normalization morphism of a scheme whose quasi-compact
opens have finitely many irreducible components is an isomorphism if and only if the scheme is
normal. -/
@[stacks 0H7D]
theorem isIso_normalization_iff_isNormal (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsIso (X.normalization hX) ↔ IsNormal X := by
  refine ⟨fun h ↦ ?_, fun h ↦ have := h; X.isIso_normalization_of_isNormal hX⟩
  have := X.isNormal_normalizationScheme hX
  exact AlgebraicGeometry.isNormal_of_iso (asIso (X.normalization hX)).symm

end Scheme

/-! ### Base change of a normal scheme along a separable extension -/

/-- **Stacks Project, Tag 0C3M.** A normal scheme over a field stays normal after base change
along a separable extension of the ground field.

Affine-locally the base change is `Spec (Γ(N, U) ⊗[k] K)`, and the ring-level statement
`IsNormalRing.tensorProduct_of_isSeparableExtension` applies. -/
@[stacks 0C3M,
  ega "IV 6.14.2",
  ega "IV 6.14.3" "Y = Spec K",
  ega "IV 4.6.4" "Case where X is normal",
  ega "IV 6.7.4" "c), special case"]
theorem isNormal_pullback_of_isSeparableExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparableExtension k K]
    {N : Scheme.{u}} (p : N ⟶ Spec (.of k)) [IsNormal N] :
    IsNormal (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  classical
  have hnormalAffines : IsNormal N ↔ ∀ J : N.affineOpens, IsNormalRing Γ(N, J) :=
    (isNormal_tfae N).out 1 2
  set σ := Spec.map (CommRingCat.ofHom (algebraMap k K)) with hσ
  set π := pullback.fst p σ with hπ
  have hAff : ∀ z : (pullback p σ : Scheme.{u}), ∃ U : N.Opens, IsAffineOpen U ∧ π z ∈ U := by
    intro z
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π z)) isOpen_univ
    exact ⟨U, hU, hzU⟩
  have h : IsNormal (pullback p σ : Scheme.{u}) ↔
      ∃ (I : Type u) (U : I → (pullback p σ : Scheme.{u}).Opens),
        IsOpenCover U ∧ ∀ i, IsNormal (U i).toScheme :=
    (isNormal_tfae _).out 1 4
  refine h.mpr ⟨(pullback p σ : Scheme.{u}), fun z ↦ π ⁻¹ᵁ (hAff z).choose,
    IsOpenCover.mk ?_, fun z ↦ ?_⟩
  · exact top_unique fun z _ ↦ Opens.mem_iSup.2 ⟨z, (hAff z).choose_spec.2⟩
  · let : Algebra k Γ(N, (hAff z).choose) :=
      (CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom ≫
        p.appLE ⊤ (hAff z).choose (by simp)).hom.toAlgebra
    obtain ⟨hV, e, -, -⟩ := affineBaseChangeLocalModel k K N p z (hAff z).choose
      (hAff z).choose_spec.1 (hAff z).choose_spec.2
    have hring : IsNormalRing (Γ(N, (hAff z).choose) ⊗[k] K) :=
      IsNormalRing.congr (Algebra.TensorProduct.comm k K Γ(N, (hAff z).choose)).toRingEquiv
        (IsNormalRing.tensorProduct_of_isSeparableExtension k K Γ(N, (hAff z).choose)
          (hnormalAffines.mp inferInstance ⟨(hAff z).choose, (hAff z).choose_spec.1⟩))
    have := isNormal_spec_of_isNormalRing hring
    exact AlgebraicGeometry.isNormal_of_iso e

end AlgebraicGeometry

end
