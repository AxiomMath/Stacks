module

public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.OpenModel

/-!
# Chart data for a subalgebra, and the image of one standard open

Let `A ⊆ R` be a subalgebra over the integers and let `r ∈ A`.  This file records the condition
that makes the two localizations `A_r` and `R_r` agree — finitely many generators of `R_r` whose
numerators already lie in `A` — and draws from it the *geometric* consequence that the
one-affine-open step of Tag 07RN needs: the standard open `D(r) ⊆ Spec R`, mapped into `Spec A`
by the spectrum of the inclusion, has image exactly the standard open `D(r) ⊆ Spec A`.

That image computation is what the existing descent of an open immersion to a finite-type
subalgebra (`Stacks.FiniteTypeOpenModel.IsOpenModel`) does **not** record: that predicate is
existential
in the factorizing morphism and says nothing about its image, and the image is not a consequence
of it.  The counterexample is `A = ℤ[x] ⊆ R = ℤ[x, 1/x]` with `f` the identity of `Spec R` and
the one-element family `r = 1`: the factorization `Spec R ⟶ Spec A` is an open immersion, `1`
lies in `A`, the standard opens of the family cover, and yet the image is `D(x)` rather than all
of `Spec A`.  Chart data at `r` is exactly what rules this out.

## What is proved, and the route

* `AlgebraicGeometry.HasAwayNumerators` is the chart condition at one element: a finite
  generating set of `R_r` over the integers, each of whose members has a numerator in `A`.  It is
  monotone in `A` (`AlgebraicGeometry.HasAwayNumerators.mono`), which is what lets a chart be
  enlarged to absorb a prescribed finitely generated subalgebra.

* `AlgebraicGeometry.HasAwayNumerators.bijective_awayMap`: chart data makes `A_r ⟶ R_r`
  bijective.  Surjectivity is the content — the generators are hit, because a numerator in `A`
  divided by a power of `r` is in the image — and injectivity is free, the inclusion of `A` in
  `R` being injective.

* `AlgebraicGeometry.basicOpen_ι_comp_SpecMap_eq` factors the composite
  `D(φ q) ⟶ Spec R' ⟶ Spec B'`, for an **arbitrary** ring map `φ : B' ⟶ R'` and an element
  `q : B'` at which the two localizations are identified: it is the isomorphism
  `D(φ q) ≅ Spec R'_{φ q}` of Mathlib's `AlgebraicGeometry.basicOpenIsoSpecAway`, then that
  identification read backwards, then the spectrum of the localization map of `B'`.  From the
  factorization both consequences are read off, since the first two factors are isomorphisms:
  `AlgebraicGeometry.isOpenImmersion_basicOpen_ι_comp_SpecMap` and
  `AlgebraicGeometry.opensRange_basicOpen_ι_comp_SpecMap`, the latter being the image
  computation, by Mathlib's `AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway`.  Both
  take bijectivity of the away map as their hypothesis and build the identification themselves,
  by `AlgebraicGeometry.awayAlgEquivOfBijective`.

  The generality is not idle: the *same* image computation is what Tag 01Z9 needs at the
  fibre-product rings, where the ring map is a projection of a fibre product and not the
  inclusion of a subalgebra — see
  `AlgebraicGeometry.opensRange_iSup_basicOpen_comp_SpecMap_snd`.

* `AlgebraicGeometry.HasAwayNumerators.isOpenImmersion_basicOpen_ι_comp_SpecMap_val` and
  `AlgebraicGeometry.HasAwayNumerators.opensRange_basicOpen_ι_comp_SpecMap_val` are those two at
  the inclusion of a subalgebra, which is the case the finite-type open models of Tag 01Z7 need.

## Universe situation

The ring and the schemes live in the single universe `u`, as in the file this builds on.
Nothing here forms a limit or a colimit, so no index universe enters and none is tied to
another.

## Transparency gotchas

* The chart isomorphism is built by `AlgEquiv.ofBijective` on `IsLocalization.Away.mapₐ`, whose
  `IsLocalization.Away` instance is at `φ q` read through the integer-algebra form of `φ` and not
  at `φ q` itself; the two are the same element definitionally but instance search does not see
  that, so the instance is introduced by `inferInstanceAs` at the spelling the statement wants.

* The image is stated through `AlgebraicGeometry.Scheme.Hom.opensRange` under a `haveI`
  introducing the open-immersion instance proved just above it.  Stating it with a coercion to a
  `Set` of the carrier of `Spec B'` is **not** possible: a standard open ascribed to the opens of
  `Spec B'` type-checks, the two carriers being definitionally equal, but no coercion from it to a
  `Set` of that carrier is found at all.  Rewriting a morphism underneath an `opensRange` needs
  `simp only`, which transports the instance, and not `rewrite`, which dies with a motive error.

* `AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway` is stated for the localization map
  of an object of `CommRingCat`, so the subalgebra has to appear as `CommRingCat.of ↥A`; the
  identification is definitional but the statement has to be written at that spelling.

## What is NOT done here

Nothing here mentions a diagram of schemes, an inverse limit, or
`AlgebraicGeometry.Scheme.FiniteTypeApproximation`.  The chart data is a hypothesis in this
file and is not produced from finite type of the ambient scheme; that is the sibling
`AlgebraicGeometry.IsChartedSubalgebra`.  Tag 07RN is not proved and no tag attribute is
attached to anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- **Chart data for a subalgebra at one element.**  The localization `R_r` is generated over
the integers by finitely many elements each of which has a numerator in `A`.  This is what makes
`A_r ⟶ R_r` bijective, and hence what makes the standard open `D(r)` of `Spec R` map onto the
standard open `D(r)` of `Spec A`. -/
def HasAwayNumerators (A : Subalgebra ℤ R) (r : R) : Prop :=
  ∃ s : Finset (Localization.Away r),
    Algebra.adjoin ℤ (s : Set (Localization.Away r)) = ⊤ ∧
      ∀ x ∈ s, ∃ (a : A) (m : ℕ),
        x * algebraMap R (Localization.Away r) r ^ m =
          algebraMap R (Localization.Away r) a.1

/-- Chart data survives enlarging the subalgebra. -/
lemma HasAwayNumerators.mono {A B : Subalgebra ℤ R} (hAB : A ≤ B) {r : R}
    (h : HasAwayNumerators A r) : HasAwayNumerators B r := by
  obtain ⟨s, hs, hnum⟩ := h
  refine ⟨s, hs, fun x hx ↦ ?_⟩
  obtain ⟨a, m, ham⟩ := hnum x hx
  exact ⟨⟨a.1, hAB a.2⟩, m, ham⟩

/-- **Chart data makes the map of localizations surjective.** -/
lemma HasAwayNumerators.surjective_awayMap {A : Subalgebra ℤ R} {r : R} (hr : r ∈ A)
    (h : HasAwayNumerators A r) :
    Function.Surjective (Localization.awayMap (A.val : A →+* R) (⟨r, hr⟩ : A)) := by
  obtain ⟨s, hs, hnum⟩ := h
  let rA : A := ⟨r, hr⟩
  let f : A →ₐ[ℤ] R := { toRingHom := A.val, commutes' := fun _ ↦ rfl }
  have : IsLocalization.Away (f rA) (Localization.Away r) := by
    show IsLocalization.Away r (Localization.Away r)
    infer_instance
  let g : Localization.Away rA →ₐ[ℤ] Localization.Away r :=
    IsLocalization.Away.mapₐ (Localization.Away rA) (Localization.Away r) f rA
  have hg : g.range = ⊤ := by
    apply le_antisymm le_top
    rw [← hs]
    apply Algebra.adjoin_le
    intro x hx
    obtain ⟨a, n, hax⟩ := hnum x hx
    show x ∈ g.range
    refine ⟨algebraMap A (Localization.Away rA) a * IsLocalization.Away.invSelf rA ^ n, ?_⟩
    have hmap : g.toRingHom (algebraMap A (Localization.Away rA) a *
        IsLocalization.Away.invSelf rA ^ n) =
        algebraMap R (Localization.Away r) a.1 * IsLocalization.Away.invSelf r ^ n := by
      simp [g, f, rA, IsLocalization.Away.mapₐ, IsLocalization.Away.invSelf,
        IsLocalization.Away.map, IsLocalization.map_mk']
    rw [hmap]
    calc
      algebraMap R (Localization.Away r) a.1 * IsLocalization.Away.invSelf r ^ n =
          (x * algebraMap R (Localization.Away r) r ^ n) *
            IsLocalization.Away.invSelf r ^ n := by rw [hax]
      _ = x := by
        rw [mul_assoc, ← mul_pow]
        simp [IsLocalization.Away.mul_invSelf]
  exact (AlgHom.range_eq_top g).mp hg

/-- **Chart data makes the map of localizations bijective.**  Injectivity needs no hypothesis:
the inclusion of a subalgebra is injective. -/
lemma HasAwayNumerators.bijective_awayMap {A : Subalgebra ℤ R} {r : R} (hr : r ∈ A)
    (h : HasAwayNumerators A r) :
    Function.Bijective (Localization.awayMap (A.val : A →+* R) (⟨r, hr⟩ : A)) := by
  refine ⟨?_, h.surjective_awayMap hr⟩
  rw [Localization.awayMap_injective_iff]
  intro a ha
  exact ⟨0, by simpa using ha⟩

/-! ### The image of one standard open, for an arbitrary ring map -/

section General

variable {B' R' : Type u} [CommRing B'] [CommRing R'] (φ : B' →+* R') (q : B')

/-- **The factorization of a standard open through an isomorphism of localizations.**  Let
`φ : B' ⟶ R'` be a ring map and `q : B'` an element at which the two localizations are
identified by `e`.  Then the composite `D(φ q) ⟶ Spec R' ⟶ Spec B'` is the isomorphism
`D(φ q) ≅ Spec R'_{φ q}` of Mathlib's `AlgebraicGeometry.basicOpenIsoSpecAway`, then `e` read
backwards, then the spectrum of the localization map of `B'`. -/
lemma basicOpen_ι_comp_SpecMap_eq (e : Localization.Away q ≃ₐ[ℤ] Localization.Away (φ q))
    (he : ∀ b : B', e (algebraMap B' (Localization.Away q) b) =
      algebraMap R' (Localization.Away (φ q)) (φ b)) :
    Scheme.Opens.ι (X := Spec (.of R')) (PrimeSpectrum.basicOpen (φ q)) ≫
        Spec.map (CommRingCat.ofHom φ) =
      (basicOpenIsoSpecAway (R := CommRingCat.of R') (φ q)).hom ≫
        Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap B' (Localization.Away q))) := by
  let eR := basicOpenIsoSpecAway (R := CommRingCat.of R') (φ q)
  let kR : R' →+* Localization.Away (φ q) := algebraMap R' (Localization.Away (φ q))
  let kB : B' →+* Localization.Away q := algebraMap B' (Localization.Away q)
  rw [← basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R')]
  show eR.hom ≫ (Spec.map (CommRingCat.ofHom kR) ≫ Spec.map (CommRingCat.ofHom φ)) =
    eR.hom ≫ (Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom kB))
  rw [cancel_epi, ← Spec.map_comp, ← Spec.map_comp, Spec.map_injective.eq_iff]
  ext x
  exact (he x).symm

/-- The isomorphism of localizations determined by bijectivity of the away map. -/
noncomputable def awayAlgEquivOfBijective
    (hbij : Function.Bijective (Localization.awayMap φ q)) :
    Localization.Away q ≃ₐ[ℤ] Localization.Away (φ q) :=
  have : IsLocalization.Away (φ.toIntAlgHom q) (Localization.Away (φ q)) :=
    inferInstanceAs (IsLocalization.Away (φ q) (Localization.Away (φ q)))
  AlgEquiv.ofBijective (IsLocalization.Away.mapₐ (Localization.Away q)
    (Localization.Away (φ q)) φ.toIntAlgHom q) hbij

/-- `awayAlgEquivOfBijective φ q hbij` sends the image of `b : B'` in `Localization.Away q` to
the image of `φ b` in `Localization.Away (φ q)`. -/
lemma awayAlgEquivOfBijective_algebraMap
    (hbij : Function.Bijective (Localization.awayMap φ q)) (b : B') :
    awayAlgEquivOfBijective φ q hbij (algebraMap B' (Localization.Away q) b) =
      algebraMap R' (Localization.Away (φ q)) (φ b) := by
  simp [awayAlgEquivOfBijective, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- The factorization of `basicOpen_ι_comp_SpecMap_eq` at the isomorphism of localizations given
by bijectivity of the away map. -/
private lemma basicOpen_ι_comp_SpecMap_eq_of_bijective
    (hbij : Function.Bijective (Localization.awayMap φ q)) :
    Scheme.Opens.ι (X := Spec (.of R')) (PrimeSpectrum.basicOpen (φ q)) ≫
        Spec.map (CommRingCat.ofHom φ) =
      (basicOpenIsoSpecAway (R := CommRingCat.of R') (φ q)).hom ≫
        Spec.map (awayAlgEquivOfBijective φ q hbij).toRingEquiv.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap B' (Localization.Away q))) :=
  basicOpen_ι_comp_SpecMap_eq φ q _ (awayAlgEquivOfBijective_algebraMap φ q hbij)

/-- **A standard open on which the away map is bijective is carried by an open immersion into
the spectrum of the source.** -/
lemma isOpenImmersion_basicOpen_ι_comp_SpecMap
    (hbij : Function.Bijective (Localization.awayMap φ q)) :
    IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of R')) (PrimeSpectrum.basicOpen (φ q)) ≫
      Spec.map (CommRingCat.ofHom φ)) := by
  rw [basicOpen_ι_comp_SpecMap_eq_of_bijective φ q hbij]
  infer_instance

/-- **The image of a standard open on which the away map is bijective.**  It is the standard
open of the element itself, read inside the spectrum of the source. -/
lemma opensRange_basicOpen_ι_comp_SpecMap
    (hbij : Function.Bijective (Localization.awayMap φ q)) :
    haveI := isOpenImmersion_basicOpen_ι_comp_SpecMap φ q hbij
    (Scheme.Opens.ι (X := Spec (.of R')) (PrimeSpectrum.basicOpen (φ q)) ≫
        Spec.map (CommRingCat.ofHom φ)).opensRange = PrimeSpectrum.basicOpen q := by
  have := isOpenImmersion_basicOpen_ι_comp_SpecMap φ q hbij
  simp only [basicOpen_ι_comp_SpecMap_eq_of_bijective φ q hbij]
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B')]

end General

/-- **A standard open on which the localizations agree is carried by an open immersion into the
spectrum of the subalgebra.** -/
lemma HasAwayNumerators.isOpenImmersion_basicOpen_ι_comp_SpecMap_val {A : Subalgebra ℤ R}
    {r : R} (hr : r ∈ A) (h : HasAwayNumerators A r) :
    IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
      Spec.map (CommRingCat.ofHom (A.val : A →+* R))) :=
  isOpenImmersion_basicOpen_ι_comp_SpecMap (A.val : A →+* R) (⟨r, hr⟩ : A)
    (h.bijective_awayMap hr)

/-- **The image of a standard open on which the localizations agree.**  It is the standard open
of the same element, read inside the spectrum of the subalgebra.  This is the image computation
that the gluing step of Tag 07RN needs and that
`Stacks.FiniteTypeOpenModel.IsOpenModel` does not record. -/
lemma HasAwayNumerators.opensRange_basicOpen_ι_comp_SpecMap_val {A : Subalgebra ℤ R} {r : R}
    (hr : r ∈ A) (h : HasAwayNumerators A r) :
    haveI := h.isOpenImmersion_basicOpen_ι_comp_SpecMap_val hr
    (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
        Spec.map (CommRingCat.ofHom (A.val : A →+* R))).opensRange =
      PrimeSpectrum.basicOpen (⟨r, hr⟩ : A) :=
  opensRange_basicOpen_ι_comp_SpecMap (A.val : A →+* R) (⟨r, hr⟩ : A) (h.bijective_awayMap hr)

end AlgebraicGeometry
