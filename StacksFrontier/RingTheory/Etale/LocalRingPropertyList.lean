module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.GorensteinPermanence
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Permanence
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.Permanence
public import StacksFrontier.RingTheory.Depth.Defs
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
public import StacksFrontier.RingTheory.Etale.PermanenceOfProperties
public import StacksFrontier.RingTheory.Etale.ReducedLocalization
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.FaithfullyFlatDescent

/-!
# Properties of local rings which are insensitive to étale extension

A property `P` of local rings is insensitive to étale extension when, for every étale ring map
`A → B` and every prime `q` of `B` lying over a prime `p` of `A`, the local ring `A_p` has `P`
exactly when `B_q` does. Such a `P` defines a property of germs of schemes by evaluation on the
local ring at the marked point, and that property of germs is étale local; this is
`AlgebraicGeometry.GermOfScheme.isEtaleLocal_stalk_property`.

This file registers the properties the source lists as insensitive to étale extension, each in
the shape that criterion consumes.

## Main results

* `isNoetherianRing_localizationAtPrime_iff_of_etale`: being Noetherian.
* `ringKrullDim_eq_localizationAtPrime_iff_of_etale`: having dimension `d`.
* `isRegularLocalRing_localizationAtPrime_iff_of_etale`: being regular.
* `isDiscreteValuationRing_localizationAtPrime_iff_of_etale`: being a discrete valuation ring.
* `isNormalDomain_localizationAtPrime_iff_of_etale`: being normal.
* `isNoetherianRing_and_ringDepth_eq_localizationAtPrime_iff_of_etale`: being Noetherian of
  depth `k`.
* `isCohenMacaulayLocalRing_localizationAtPrime_iff_of_etale`: being Noetherian and
  Cohen-Macaulay.
* `isGorensteinLocalRing_localizationAtPrime_iff_of_etale`: being Noetherian and Gorenstein.
* `ringDepth_eq_of_ringEquiv`: the depth of a local ring is an isomorphism invariant, which is
  the other hypothesis the germ criterion asks of a property of local rings.

Reducedness, the remaining item of the list, is `isReduced_localizationAtPrime_iff_of_etale`.

## Implementation notes

The two primes are related by the equation `q.comap (algebraMap A B) = p` rather than by an
`Ideal.LiesOver` instance, so that the statements are literally the hypothesis of the germ
criterion; the étale ring map itself is an `Algebra A B` instance together with
`Algebra.Etale A B`.

The common engine is `flat_formallyUnramified_essFiniteType_localRingHom_of_etale`, which says
that the induced homomorphism of local rings `A_p → B_q` is flat, formally unramified and
essentially of finite type. On Noetherian local rings that triple is exactly
`RingHom.IsEtaleLocalHom`, so the permanence results for étale local homomorphisms apply: Tag
025N for regularity, Tag 039T for depth, Tag 025Q for Cohen-Macaulayness and Tag 0BJL for
Gorensteinness. Noetherianity itself is Tag 0AGZ and dimension is Tag 07QP, both already
available directly for an étale algebra, and regularity is likewise available as Tag 0AH0.
Being a discrete valuation ring is regularity together with dimension one, by item (3) of the
characterisation of Tag 00PD.

Normality is the one item proved without a Noetherian hypothesis, following the route of Tag
033G rather than Tag 025P: `B_q` is a localization of `M⁻¹B` for `M` the image of
`A \ p`, and `M⁻¹B` is the base change `A_p ⊗_A B`, hence étale over `A_p`, so normality
ascends; in the other direction `A_p → B_q` is a faithfully flat local homomorphism, along
which normality descends. For a local ring `IsNormalRing` — all localizations at primes are
integrally closed domains — is the same as `IsNormalDomain`, so the statement is about the
local ring itself.

The properties which include a numerical invariant are stated with that invariant as a
parameter: `ringKrullDim` for the dimension and `ringDepth` for the depth. The properties which
presuppose Noetherianity to be stated at all — Cohen-Macaulayness and Gorensteinness — carry it
as a bound existential, which is how a caller supplies the instance those predicates need.

## References

* [Stacks Project, Tag 0BBL](https://stacks.math.columbia.edu/tag/0BBL)
* [Stacks Project, Tag 0AGZ](https://stacks.math.columbia.edu/tag/0AGZ)
* [Stacks Project, Tag 07QP](https://stacks.math.columbia.edu/tag/07QP)
* [Stacks Project, Tag 0AH0](https://stacks.math.columbia.edu/tag/0AH0)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
* [Stacks Project, Tag 033G](https://stacks.math.columbia.edu/tag/033G)
* [Stacks Project, Tag 039T](https://stacks.math.columbia.edu/tag/039T)
* [Stacks Project, Tag 025Q](https://stacks.math.columbia.edu/tag/025Q)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
-/

@[expose] public section

universe u v

/-- A local ring is a normal domain exactly when it is a normal ring: localizing at the maximal
ideal changes nothing, and a normal domain has all of its prime localizations normal. -/
private theorem isNormalDomain_iff_isNormalRing (R : Type*) [CommRing R] [IsLocalRing R] :
    IsNormalDomain R ↔ IsNormalRing R := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.isDomain
    have := h.isIntegrallyClosed
    exact IsNormalRing.of_isIntegrallyClosed R
  · obtain ⟨hd, hc⟩ := h.of_isLocalRing
    exact ⟨hd, hc⟩

/-- The depth of a local ring depends only on its isomorphism class. -/
theorem ringDepth_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) : ringDepth R = ringDepth S := by
  rw [ringDepth_eq_depth_maximalIdeal, ringDepth_eq_depth_maximalIdeal,
    Module.depth_self_eq_of_ringEquiv e]

/-- The homomorphism of local rings induced by an étale ring map at corresponding primes is
flat, formally unramified and essentially of finite type. On Noetherian local rings this triple
is `RingHom.IsEtaleLocalHom`, and no Noetherian hypothesis is needed to establish it. -/
theorem flat_formallyUnramified_essFiniteType_localRingHom_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap A B) = p) :
    (Localization.localRingHom p q (algebraMap A B) hq.symm).Flat ∧
      (Localization.localRingHom p q (algebraMap A B) hq.symm).FormallyUnramified ∧
      (Localization.localRingHom p q (algebraMap A B) hq.symm).EssFiniteType := by
  have : q.LiesOver p := ⟨hq.symm⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have hft : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp A (Localization.AtPrime p) (Localization.AtPrime q)
  have hflat : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime q)).2 inferInstance
  have hfu : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.localization_base p.primeCompl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq] using
      RingHom.flat_algebraMap_iff.mpr hflat
  · simpa only [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq] using
      RingHom.formallyUnramified_algebraMap.mpr hfu
  · simpa only [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq] using
      RingHom.essFiniteType_algebraMap.mpr hft

/-- Existential statements over propositions `α ↔ β` are equivalent when the predicates are. -/
private theorem exists_iff_exists_of_iff {α β : Prop} {P : α → Prop} {Q : β → Prop}
    (h : α ↔ β) (hPQ : ∀ a b, P a ↔ Q b) : (∃ a, P a) ↔ ∃ b, Q b :=
  ⟨fun ⟨a, ha⟩ => ⟨h.mp a, (hPQ _ _).mp ha⟩, fun ⟨b, hb⟩ => ⟨h.mpr b, (hPQ _ _).mpr hb⟩⟩

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
  (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]

/-- **Stacks 0BBL, Noetherian.** For prime ideals `p` and `q` corresponding under an étale map
`A → B`, the local ring of `A` at `p` is Noetherian if and only if the local ring of `B` at `q`
is Noetherian. -/
@[stacks 0BBL "Noetherian"]
theorem isNoetherianRing_localizationAtPrime_iff_of_etale
    (hq : q.comap (algebraMap A B) = p) :
    IsNoetherianRing (Localization.AtPrime p) ↔ IsNoetherianRing (Localization.AtPrime q) :=
  have : q.LiesOver p := ⟨hq.symm⟩
  isNoetherianRing_localization_iff_of_etale p q

/-- For prime ideals `p` and `q` corresponding under an étale map `A → B`, the local rings of
`A` at `p` and of `B` at `q` have the same Krull dimension. -/
theorem ringKrullDim_localizationAtPrime_eq_of_etale (hq : q.comap (algebraMap A B) = p) :
    ringKrullDim (Localization.AtPrime p) = ringKrullDim (Localization.AtPrime q) :=
  RingHom.Etale.ringKrullDim_localization_atPrime_eq
    (RingHom.etale_algebraMap.mpr inferInstance) p q hq.symm

/-- **Stacks 0BBL, dimension `d`.** For prime ideals `p` and `q` corresponding under an étale
map `A → B`, the local ring of `A` at `p` has dimension `d` if and only if the local ring of `B`
at `q` has dimension `d`. -/
@[stacks 0BBL "dimension d"]
theorem ringKrullDim_eq_localizationAtPrime_iff_of_etale (d : WithBot ℕ∞)
    (hq : q.comap (algebraMap A B) = p) :
    ringKrullDim (Localization.AtPrime p) = d ↔ ringKrullDim (Localization.AtPrime q) = d := by
  rw [ringKrullDim_localizationAtPrime_eq_of_etale p q hq]

/-- **Stacks 0BBL, regular.** For prime ideals `p` and `q` corresponding under an étale map
`A → B`, the local ring of `A` at `p` is regular if and only if the local ring of `B` at `q` is
regular. -/
@[stacks 0BBL "regular"]
theorem isRegularLocalRing_localizationAtPrime_iff_of_etale
    (hq : q.comap (algebraMap A B) = p) :
    IsRegularLocalRing (Localization.AtPrime p) ↔
      IsRegularLocalRing (Localization.AtPrime q) :=
  have : q.LiesOver p := ⟨hq.symm⟩
  isRegularLocalRing_localization_iff_of_etale p q

/-- **Stacks 0BBL, discrete valuation ring.** For prime ideals `p` and `q` corresponding under
an étale map `A → B`, the local ring of `A` at `p` is a discrete valuation ring if and only if
the local ring of `B` at `q` is one. This is regularity together with dimension one, through
item (3) of the characterisation of Tag 00PD. -/
@[stacks 0BBL "discrete valuation ring"]
theorem isDiscreteValuationRing_localizationAtPrime_iff_of_etale
    (hq : q.comap (algebraMap A B) = p) :
    (∃ _ : IsDomain (Localization.AtPrime p),
        IsDiscreteValuationRing (Localization.AtPrime p)) ↔
      (∃ _ : IsDomain (Localization.AtPrime q),
        IsDiscreteValuationRing (Localization.AtPrime q)) := by
  have hP := (isDiscreteValuationRing_tfae (Localization.AtPrime p)).out 1 3
  have hQ := (isDiscreteValuationRing_tfae (Localization.AtPrime q)).out 1 3
  rw [hP, hQ, isRegularLocalRing_localizationAtPrime_iff_of_etale p q hq,
    ringKrullDim_localizationAtPrime_eq_of_etale p q hq]

/-- **Stacks 0BBL, normal.** For prime ideals `p` and `q` corresponding under an étale map
`A → B`, the local ring of `A` at `p` is a normal domain if and only if the local ring of `B` at
`q` is one. Neither ring is assumed Noetherian. -/
@[stacks 0BBL "normal"]
theorem isNormalDomain_localizationAtPrime_iff_of_etale
    (hq : q.comap (algebraMap A B) = p) :
    IsNormalDomain (Localization.AtPrime p) ↔ IsNormalDomain (Localization.AtPrime q) := by
  rw [isNormalDomain_iff_isNormalRing, isNormalDomain_iff_isNormalRing]
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q
  let f := Localization.localRingHom p q (algebraMap A B) hq.symm
  let : Algebra R S := f.toAlgebra
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom f)
  have : Module.Flat R S :=
    (flat_formallyUnramified_essFiniteType_localRingHom_of_etale p q hq).1
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let M := p.primeCompl
  let N := q.primeCompl
  let M' := M.map (algebraMap A B)
  let B' := Localization M'
  have hMN : M' ≤ N := by
    rintro x ⟨a, ha, rfl⟩
    exact fun h => ha (hq ▸ h)
  let g : R →+* B' := IsLocalization.map B' (algebraMap A B) (Submonoid.le_comap_map M)
  let : Algebra R B' := g.toAlgebra
  have : Algebra.Etale R B' := Algebra.Etale.of_equiv (Localization.tensorRightAlgEquiv M B)
  have hunit : ∀ x : M', IsUnit (algebraMap B S x) :=
    fun x => IsLocalization.map_units S (⟨(x : B), hMN x.property⟩ : N)
  let j : B' →+* S := IsLocalization.lift (M := M') (S := B') (g := algebraMap B S) hunit
  let : Algebra B' S := j.toAlgebra
  have : IsScalarTower B B' S :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
  have : IsLocalization (N.map (algebraMap B B')) S :=
    IsLocalization.isLocalization_of_submonoid_le (S := B') (T := S) M' N hMN
  exact ⟨fun hR =>
      (IsNormalRing.of_etale (R := R) hR).isLocalization (N.map (algebraMap B B')) S,
    fun hS => isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat (R := R) (S := S) hS⟩

/-- For prime ideals `p` and `q` corresponding under an étale map `A → B` with Noetherian local
rings, the local ring of `A` at `p` and the local ring of `B` at `q` have the same depth. -/
theorem ringDepth_localizationAtPrime_eq_of_etale (hq : q.comap (algebraMap A B) = p)
    [IsNoetherianRing (Localization.AtPrime p)] [IsNoetherianRing (Localization.AtPrime q)] :
    ringDepth (Localization.AtPrime p) = ringDepth (Localization.AtPrime q) := by
  rw [ringDepth_eq_depth_maximalIdeal, ringDepth_eq_depth_maximalIdeal]
  exact RingHom.depth_eq_of_isEtaleLocalHom _
    (flat_formallyUnramified_essFiniteType_localRingHom_of_etale p q hq)

/-- **Stacks 0BBL, Noetherian and depth `k`.** For prime ideals `p` and `q` corresponding under
an étale map `A → B`, the local ring of `A` at `p` is Noetherian of depth `k` if and only if the
local ring of `B` at `q` is. -/
@[stacks 0BBL "Noetherian and depth k"]
theorem isNoetherianRing_and_ringDepth_eq_localizationAtPrime_iff_of_etale (k : ℕ∞)
    (hq : q.comap (algebraMap A B) = p) :
    (IsNoetherianRing (Localization.AtPrime p) ∧ ringDepth (Localization.AtPrime p) = k) ↔
      (IsNoetherianRing (Localization.AtPrime q) ∧ ringDepth (Localization.AtPrime q) = k) := by
  rw [← exists_prop, ← exists_prop]
  exact exists_iff_exists_of_iff (isNoetherianRing_localizationAtPrime_iff_of_etale p q hq)
    fun _ _ => by
      rw [ringDepth_localizationAtPrime_eq_of_etale p q hq]

/-- **Stacks 0BBL, Noetherian and Cohen-Macaulay.** For prime ideals `p` and `q` corresponding
under an étale map `A → B`, the local ring of `A` at `p` is Noetherian and Cohen-Macaulay if and
only if the local ring of `B` at `q` is. -/
@[stacks 0BBL "Noetherian and Cohen-Macaulay"]
theorem isCohenMacaulayLocalRing_localizationAtPrime_iff_of_etale
    (hq : q.comap (algebraMap A B) = p) :
    (∃ h : IsNoetherianRing (Localization.AtPrime p),
        @IsCohenMacaulayLocalRing (Localization.AtPrime p) _ h _) ↔
      (∃ h : IsNoetherianRing (Localization.AtPrime q),
        @IsCohenMacaulayLocalRing (Localization.AtPrime q) _ h _) := by
  exact exists_iff_exists_of_iff (isNoetherianRing_localizationAtPrime_iff_of_etale p q hq)
    fun _ _ => RingHom.isCohenMacaulayLocalRing_iff_of_isEtaleLocalHom _
      (flat_formallyUnramified_essFiniteType_localRingHom_of_etale p q hq)

/-- **Stacks 0BBL, Noetherian and Gorenstein.** For prime ideals `p` and `q` corresponding
under an étale map `A → B`, the local ring of `A` at `p` is Noetherian and Gorenstein if and
only if the local ring of `B` at `q` is. -/
@[stacks 0BBL "Noetherian and Gorenstein"]
theorem isGorensteinLocalRing_localizationAtPrime_iff_of_etale
    (hq : q.comap (algebraMap A B) = p) :
    (∃ h : IsNoetherianRing (Localization.AtPrime p),
        @Dualizing.IsGorensteinLocalRing (Localization.AtPrime p) _ h _) ↔
      (∃ h : IsNoetherianRing (Localization.AtPrime q),
        @Dualizing.IsGorensteinLocalRing (Localization.AtPrime q) _ h _) := by
  exact exists_iff_exists_of_iff (isNoetherianRing_localizationAtPrime_iff_of_etale p q hq)
    fun _ _ => RingHom.isGorensteinLocalRing_iff_of_isEtaleLocalHom _
      (flat_formallyUnramified_essFiniteType_localRingHom_of_etale p q hq)

end

end
