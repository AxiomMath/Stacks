module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Compatibilities
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GenericFibres
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationBaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# h descent for relative cycles

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type, let `r ≥ 0` and
let `α` be a family of `r`-cycles on the fibres of `X/S`. If `{g i : S' i ⟶ S}` is an h covering,
then `α` is a relative `r`-cycle if and only if each base change `(g i)^*α` is a relative
`r`-cycle.

Being a relative `r`-cycle is a valuative condition: it says that for every morphism
`c : Spec R ⟶ S` out of the spectrum of a discrete valuation ring the specialization of the generic
member of `c^*α` is its closed member. So the lemma is a statement about which discrete valuations
of the base have to be tested, and its content is that testing them on the members of an h covering
suffices. That is what this file proves:
`AlgebraicGeometry.exists_isDiscreteValuationRing_lift_of_isHCovering` says that every morphism
from the spectrum of a discrete valuation ring to `S` factors, after an extension of discrete
valuation rings, through a member of the covering.

## Main results

* `AlgebraicGeometry.isHCovering_pullback_of_isLocalRing` — the base change of an h covering along
  a morphism out of the spectrum of a local ring is an h covering. This is the case of Stacks
  0ETY part (3) the argument needs, and it is unconditional.
* `AlgebraicGeometry.exists_valuationRing_lift_of_isVCovering` — the family form of the
  implication part (1) ⟹ part (2) of Stacks 0ETN: a V covering of an affine scheme lifts every
  morphism out of the spectrum of a valuation ring to one of its members, after an extension of
  valuation rings.
* `AlgebraicGeometry.exists_isDiscreteValuationRing_lift_of_isHCovering` — the geometric content of
  the proof of Stacks 0H52.
* `Stacks.Chow.isRelativeCycle_iff_forall_baseChangeFamily` — the argument of Lemma 0H52, with its
  two inputs as hypotheses, and `Stacks.Chow.mem_relativeCycles_iff_forall_baseChangeFamily`, the
  same phrased as membership in `z(X/S, r)`.
* `Stacks.Chow.specializationCycle_baseChangeFamily_baseChangeFamily_iff` and
  `Stacks.Chow.specializationCycle_baseChangeFamily_of_isExtension` — the two inputs.
* `Stacks.Chow.isRelativeCycle_iff_forall_isRelativeCycle_baseChangeFamily` — **Stacks Project,
  Lemma 0H52**.
* `Stacks.Chow.isRelativeCycle_of_isRelativeCycle_baseChangeFamily_of_isProper` — the case of a
  single proper surjective morphism, which is an h covering by Tag 0ETW.

## Implementation notes

The source reduces to the case of a base which is the spectrum of a discrete valuation ring by base
changing the covering, then uses that an h covering is a V covering to lift a specialization of the
base to one of the members, then Stacks 054F to realize that lifted specialization by a discrete
valuation ring. The route here follows the same three steps but keeps them over the original base
rather than restating the lemma over the reduced one: the base change of the covering along
`Spec R ⟶ S` is formed, the valuative criterion is applied to the *identity* of `Spec R`, which
produces a lift out of the spectrum of some valuation ring, and the specialization of points of the
base changed member that this lift carries is realized by a discrete valuation ring. The structure
morphism of that realization is then read off as the morphism of spectra induced by an injective
local homomorphism of discrete valuation rings.

Base changing the covering is legitimate with no refinement hypothesis because a morphism out of
the spectrum of a local ring is confined over its target: the only open of the spectrum of a local
ring containing the closed point is the whole spectrum, so the morphism factors through any affine
open of the target containing the image of the closed point. The general base change statement
`AlgebraicGeometry.isHCovering_pullback` would serve as well, but it passes through Stacks 0DBF
part (2) and so through Chow's lemma; the confinement here makes that detour unnecessary.

## Implementation notes on the two inputs

The argument is first written, as `Stacks.Chow.isRelativeCycle_iff_forall_baseChangeFamily`, with
two statements of the source as hypotheses, each about one operation and upstream of Lemma 0H52;
they are then proved, and Lemma 0H52 is the instance.

* `htrans` is the two-step base change compatibility of Section 0H4N, read on the valuative
  identity. The two families of cycles it compares live on the two schemes
  `(X ×_S S' i) ×_{S' i} Spec R` and `X ×_S Spec R`; Tag 0H4P part (1),
  `Stacks.Chow.baseChangeFamily_baseChangeFamily_comp`, identifies them through the canonical
  isomorphism, and reading a family through an isomorphism commutes with specialization
  (Tag 0H4L for open immersions) and is injective. This is
  `Stacks.Chow.specializationCycle_baseChangeFamily_baseChangeFamily_iff`.
* `hdvr` is Lemma 0H4K, that specialization commutes with base change along an extension of
  discrete valuation rings, together with the injectivity of the base change map
  `Z_r(X_0) → Z_r(X'_{0'})` of Section 0H4E. The morphism of bases is an arbitrary injective
  local homomorphism `e : R ⟶ R'`, which is turned into the algebra structure `e.toAlgebra` so
  that `Stacks.Chow.baseChangeFiberCycleOfEq_comp_specializationCycleHom` applies. This is
  `Stacks.Chow.specializationCycle_baseChangeFamily_of_isExtension`.

## References

* [Stacks Project, Tag 0H52](https://stacks.math.columbia.edu/tag/0H52)
* [Stacks Project, Tag 0ETS](https://stacks.math.columbia.edu/tag/0ETS)
* [Stacks Project, Tag 0ETN](https://stacks.math.columbia.edu/tag/0ETN)
* [Stacks Project, Tag 0ETY](https://stacks.math.columbia.edu/tag/0ETY)
* [Stacks Project, Tag 054F](https://stacks.math.columbia.edu/tag/054F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-! ### Morphisms out of the spectrum of a local ring are confined over the target -/

/-- A morphism `c : Spec R ⟶ S` with `R` a local ring maps every affine open of `Spec R` into an
affine open of `S`: the whole of `Spec R` already lands in any affine open of `S` containing the
image of the closed point, because the only open of `Spec R` containing the closed point is
`Spec R` itself. -/
theorem exists_isAffineOpen_range_comp_subset {S : Scheme.{u}} {R : Type u} [CommRing R]
    [IsLocalRing R] (c : Spec (.of R) ⟶ S) (U' : (Spec (.of R)).Opens) :
    ∃ U : S.Opens, IsAffineOpen U ∧ Set.range (U'.ι ≫ c).base ⊆ (U : Set S) := by
  obtain ⟨U, hU, hmem, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
      (Opens.mem_top (c (IsLocalRing.closedPoint R)))
  refine ⟨U, hU, ?_⟩
  rintro x ⟨y, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact (Scheme.preimage_eq_top_of_closedPoint_mem c hmem).ge (Opens.mem_top (U'.ι y))

/-- The base change of an h covering along a morphism from the spectrum of a local ring is an
h covering.

This is the case of Stacks 0ETY part (3) that the proof of Stacks 0H52 uses, and unlike the
general statement it needs neither Stacks 0DBF part (2) nor Chow's lemma: by
`AlgebraicGeometry.exists_isAffineOpen_range_comp_subset` the morphism is confined over the base,
so `AlgebraicGeometry.isHCovering_pullback_of_forall_exists_isAffineOpen` applies. -/
theorem isHCovering_pullback_of_isLocalRing {S : Scheme.{u}} {I : Type v} {S' : I → Scheme.{u}}
    {g : ∀ i, S' i ⟶ S} (hg : IsHCovering S' g) {R : Type u} [CommRing R] [IsLocalRing R]
    (c : Spec (.of R) ⟶ S) :
    IsHCovering (fun i ↦ pullback (g i) c) (fun i ↦ pullback.snd (g i) c) :=
  isHCovering_pullback_of_forall_exists_isAffineOpen hg c fun U' _ ↦
    exists_isAffineOpen_range_comp_subset c U'

/-! ### Valuation-ring lifting for a V covering of an affine scheme -/

/-- A V covering of an affine scheme lifts every morphism out of the spectrum of a valuation ring
to one of its members, after an extension of valuation rings.

This is the family form of the implication part (1) ⟹ part (2) of Stacks 0ETN: over the affine
open `⊤` the covering is refined by a standard V covering, whose defining lifting property
provides the extension and the lift, and the refinement carries the lift into a member of the
original family. -/
theorem exists_valuationRing_lift_of_isVCovering {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hV : IsVCovering X f)
    (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] (c : Spec (.of V) ⟶ T) :
    ∃ (i : I) (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W) (e : V →+* W),
      IsExtensionOfValuationRings e ∧
        ∃ q : Spec (.of W) ⟶ X i, Spec.map (CommRingCat.ofHom e) ≫ c = q ≫ f i := by
  classical
  obtain ⟨𝒰, hfinite, haffine, hstd, href⟩ := hV ⊤ (isAffineOpen_top T)
  have : Finite 𝒰.I₀ := hfinite
  have : ∀ j, IsAffine (𝒰.X j) := haffine
  let cU : Spec (.of V) ⟶ (⊤ : T.Opens).toScheme :=
    IsOpenImmersion.lift (⊤ : T.Opens).ι c (by
      rintro x ⟨y, rfl⟩
      exact ⟨⟨c y, trivial⟩, rfl⟩)
  have hcU : cU ≫ (⊤ : T.Opens).ι = c := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨W, iW, iWd, iWv, e, hext, j, l, hcomm⟩ := hstd V cU
  let _ : CommRing W := iW
  let _ : IsDomain W := iWd
  let _ : ValuationRing W := iWv
  let φ := Classical.choice href
  obtain ⟨i, p, hfac⟩ : ∃ (i : I) (p : 𝒰.X j ⟶ pullback (f i) (⊤ : T.Opens).ι),
      p ≫ pullback.snd (f i) (⊤ : T.Opens).ι = 𝒰.f j :=
    ⟨φ.s₀ j, φ.h₀ j, φ.w₀ j⟩
  refine ⟨i, W, inferInstance, inferInstance, inferInstance, e, hext,
    l ≫ p ≫ pullback.fst (f i) (⊤ : T.Opens).ι, ?_⟩
  have hsq : p ≫ pullback.fst (f i) (⊤ : T.Opens).ι ≫ f i = 𝒰.f j ≫ (⊤ : T.Opens).ι := by
    rw [pullback.condition, ← Category.assoc, hfac]
  rw [← hcU, ← Category.assoc, hcomm]
  simp only [Category.assoc, hsq]

/-! ### Generic and closed points under a morphism of spectra of local domains -/

private theorem specMap_genericPoint_of_injective {A B : Type u} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (e : A →+* B) (he : Function.Injective e) :
    Spec.map (CommRingCat.ofHom e) (genericPoint (Spec (.of B))) =
      genericPoint (Spec (.of A)) := by
  change PrimeSpectrum.comap e (genericPoint (Spec (.of B))) = genericPoint (Spec (.of A))
  rw [genericPoint_eq_bot_of_affine (CommRingCat.of B),
    genericPoint_eq_bot_of_affine (CommRingCat.of A)]
  refine PrimeSpectrum.ext ?_
  change Ideal.comap e (⊥ : Ideal B) = (⊥ : Ideal A)
  exact (RingHom.injective_iff_ker_eq_bot e).mp he

private theorem injective_of_specMap_genericPoint {A B : Type u} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (e : A →+* B)
    (he : Spec.map (CommRingCat.ofHom e) (genericPoint (Spec (.of B))) =
      genericPoint (Spec (.of A))) : Function.Injective e := by
  rw [RingHom.injective_iff_ker_eq_bot e]
  change PrimeSpectrum.comap e (genericPoint (Spec (.of B))) = genericPoint (Spec (.of A)) at he
  rw [genericPoint_eq_bot_of_affine (CommRingCat.of B),
    genericPoint_eq_bot_of_affine (CommRingCat.of A)] at he
  exact congrArg PrimeSpectrum.asIdeal he

private theorem specMap_closedPoint_of_isLocalHom {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (e : A →+* B) [IsLocalHom e] :
    Spec.map (CommRingCat.ofHom e) (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A := by
  change PrimeSpectrum.comap e (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A
  exact IsLocalRing.comap_closedPoint e

private theorem isLocalHom_of_specMap_closedPoint {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (e : A →+* B)
    (he : Spec.map (CommRingCat.ofHom e) (IsLocalRing.closedPoint B) =
      IsLocalRing.closedPoint A) : IsLocalHom e := by
  refine ((IsLocalRing.local_hom_TFAE e).out 5 1 rfl rfl).mp ?_
  change PrimeSpectrum.comap e (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A at he
  exact congrArg PrimeSpectrum.asIdeal he

/-! ### Lifting a discrete valuation of the base along an h covering -/

/-- **The geometric content of the proof of Stacks Project, Lemma 0H52.** Let
`{g i : S' i ⟶ S}` be an h covering and let `c : Spec R ⟶ S` be a morphism out of the spectrum
of a discrete valuation ring. Then some member of the covering receives a morphism
`c' : Spec R' ⟶ S' i` out of the spectrum of a discrete valuation ring `R'`, over an extension
`e : R →+* R'` of discrete valuation rings, in the sense that `e` is injective and local and that
`e` sends the generic and the closed point of `Spec R'` to the generic and the closed point of
`Spec R`.

The argument is the one of the source. The covering is base changed to `Spec R`, which is
legitimate with no refinement hypothesis because a morphism out of the spectrum of a local ring is
confined over its target. An h covering is a ph covering and hence a V covering, so the valuative
criterion provides a lift of the identity of `Spec R` to one member `T = (S' i) ×_S Spec R` of the
base changed covering, out of the spectrum of some valuation ring. That lift carries the
generic-to-closed specialization of that spectrum to a specialization of points of `T`, and `T` is
locally Noetherian because it is locally of finite type over the spectrum of a discrete valuation
ring, so Stacks 054F realizes that specialization by the spectrum of a *discrete* valuation ring
`R'`. The structure morphism `Spec R' ⟶ Spec R` of that realization is the one induced by `e`. -/
theorem exists_isDiscreteValuationRing_lift_of_isHCovering {S : Scheme.{u}} {I : Type v}
    {S' : I → Scheme.{u}} {g : ∀ i, S' i ⟶ S} (hg : IsHCovering S' g) (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (c : Spec (.of R) ⟶ S) :
    ∃ (i : I) (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (e : R →+* R') (_ : Function.Injective e) (_ : IsLocalHom e) (c' : Spec (.of R') ⟶ S' i),
      Spec.map (CommRingCat.ofHom e) ≫ c = c' ≫ g i ∧
        Spec.map (CommRingCat.ofHom e) (genericPoint (Spec (.of R'))) =
            genericPoint (Spec (.of R)) ∧
          Spec.map (CommRingCat.ofHom e) (IsLocalRing.closedPoint R') =
            IsLocalRing.closedPoint R := by
  classical
  have hV : IsVCovering (fun i ↦ pullback (g i) c) (fun i ↦ pullback.snd (g i) c) :=
    isVCovering_of_isPHCovering _ _ (isHCovering_pullback_of_isLocalRing hg c).2
  obtain ⟨i, W, iW, iWd, iWv, e₀, hext, q, hq⟩ :=
    exists_valuationRing_lift_of_isVCovering hV R (𝟙 _)
  let _ : CommRing W := iW
  let _ : IsDomain W := iWd
  let _ : ValuationRing W := iWv
  have _ : IsLocalHom e₀ := hext.2
  have hq' : Spec.map (CommRingCat.ofHom e₀) = q ≫ pullback.snd (g i) c := by
    rw [← hq, Category.comp_id]
  have _ : LocallyOfFinitePresentation (pullback.snd (g i) c) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (g i) c) (hg.1 i)
  have _ : IsLocallyNoetherian (pullback (g i) c : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (g i) c)
  have hspec : q (genericPoint (Spec (.of W))) ⤳ q (IsLocalRing.closedPoint W) :=
    (genericPoint_specializes (IsLocalRing.closedPoint W)).map q.continuous
  obtain ⟨R', iR', iR'd, iR'dvr, d, hdη, hd0⟩ :=
    exists_dvr_morphism_of_specializes (pullback (g i) c : Scheme.{u}) hspec
  let _ : CommRing R' := iR'
  let _ : IsDomain R' := iR'd
  let _ : IsDiscreteValuationRing R' := iR'dvr
  obtain ⟨e, he⟩ : ∃ e : R →+* R', Spec.map (CommRingCat.ofHom e) = d ≫ pullback.snd (g i) c :=
    ⟨(Spec.preimage (d ≫ pullback.snd (g i) c)).hom, by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have hgen : Spec.map (CommRingCat.ofHom e) (genericPoint (Spec (.of R'))) =
      genericPoint (Spec (.of R)) := by
    rw [he, Scheme.Hom.comp_apply, hdη, ← Scheme.Hom.comp_apply, ← hq']
    exact specMap_genericPoint_of_injective e₀ hext.1
  have hcl : Spec.map (CommRingCat.ofHom e) (IsLocalRing.closedPoint R') =
      IsLocalRing.closedPoint R := by
    rw [he]
    change pullback.snd (g i) c (d (IsLocalRing.closedPoint R')) = _
    rw [hd0]
    change (q ≫ pullback.snd (g i) c) (IsLocalRing.closedPoint W) = _
    rw [← hq']
    exact specMap_closedPoint_of_isLocalHom e₀
  refine ⟨i, R', inferInstance, inferInstance, inferInstance, e,
    injective_of_specMap_genericPoint e hgen, isLocalHom_of_specMap_closedPoint e hcl,
    d ≫ pullback.fst (g i) c, ?_, hgen, hcl⟩
  rw [he, Category.assoc, ← pullback.condition, Category.assoc]

/-- The members of an h covering of a locally Noetherian scheme are locally Noetherian: each is
locally of finite presentation, hence locally of finite type, over the base. -/
theorem IsHCovering.isLocallyNoetherian {S : Scheme.{u}} [IsLocallyNoetherian S] {I : Type v}
    {S' : I → Scheme.{u}} {g : ∀ i, S' i ⟶ S} (hg : IsHCovering S' g) (i : I) :
    IsLocallyNoetherian (S' i) :=
  have : LocallyOfFinitePresentation (g i) := hg.1 i
  LocallyOfFiniteType.isLocallyNoetherian (g i)

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### h descent for relative cycles -/

/-- **The argument of Lemma 0H52, with its two inputs as hypotheses.** Let `S` be locally
Noetherian, let `f : X ⟶ S` be locally of finite type, let `r ≥ 0` and let `α` be a family of
`r`-cycles on the fibres of `X/S`. Let `{g i : S' i ⟶ S}` be an h covering. Granted the two
statements below, `α` is a relative `r`-cycle if and only if each base change `(g i)^*α` is one.
Both are proved further down, and Lemma 0H52 itself is
`Stacks.Chow.isRelativeCycle_iff_forall_isRelativeCycle_baseChangeFamily`.

* `htrans` is the two-step base change compatibility of Section 0H4N: base changing `α` along
  `g i` and then along `c : Spec R ⟶ S' i` gives the same family of cycles on the fibres over
  `Spec R` as base changing `α` along the composite `c ≫ g i`. The two families live on the two
  schemes `(X ×_S S' i) ×_{S' i} Spec R` and `X ×_S Spec R`, which are canonically isomorphic,
  so the compatibility is stated as the equivalence of the two valuative identities; it is
  `Stacks.Chow.specializationCycle_baseChangeFamily_baseChangeFamily_iff`. Granted it, the
  forward implication is the base change case of Lemma 0H51.
* `hdvr` is the descent of the valuative identity along an extension of discrete valuation rings:
  if the identity holds after base change along an injective local homomorphism `e : R ⟶ R'` of
  discrete valuation rings, then it holds over `R`. This is Lemma 0H4K, that specialization
  commutes with base change along such an extension, together with the injectivity of the base
  change map `Z_r(X_0) → Z_r(X'_{0'})` of Section 0H4E; it is
  `Stacks.Chow.specializationCycle_baseChangeFamily_of_isExtension`.

What the proof does with its own hypotheses is the reverse implication, and the work there is
`AlgebraicGeometry.exists_isDiscreteValuationRing_lift_of_isHCovering`: every morphism from the
spectrum of a discrete valuation ring to `S` is, after an extension of discrete valuation rings,
factored through a member of the covering. The h-covering hypothesis is used there and only
there. -/
theorem isRelativeCycle_iff_forall_baseChangeFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r)
    {I : Type v} (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S) (hg : IsHCovering S' g)
    (htrans : ∀ (i : I) (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (c : Spec (.of R) ⟶ S' i),
      (specializationCycle (pullback.snd (pullback.snd f (g i)) c) r
            (baseChangeFamily (pullback.snd f (g i)) c r (baseChangeFamily f (g i) r α)
              (genericPoint (Spec (.of R)))) =
          baseChangeFamily (pullback.snd f (g i)) c r (baseChangeFamily f (g i) r α)
            (IsLocalRing.closedPoint R)) ↔
        specializationCycle (pullback.snd f (c ≫ g i)) r
            (baseChangeFamily f (c ≫ g i) r α (genericPoint (Spec (.of R)))) =
          baseChangeFamily f (c ≫ g i) r α (IsLocalRing.closedPoint R))
    (hdvr : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (c : Spec (.of R) ⟶ S) (R' : Type u) [CommRing R'] [IsDomain R']
      [IsDiscreteValuationRing R'] (e : R →+* R'), Function.Injective e → IsLocalHom e →
      (specializationCycle (pullback.snd f (Spec.map (CommRingCat.ofHom e) ≫ c)) r
            (baseChangeFamily f (Spec.map (CommRingCat.ofHom e) ≫ c) r α
              (genericPoint (Spec (.of R')))) =
          baseChangeFamily f (Spec.map (CommRingCat.ofHom e) ≫ c) r α
            (IsLocalRing.closedPoint R')) →
        specializationCycle (pullback.snd f c) r
            (baseChangeFamily f c r α (genericPoint (Spec (.of R)))) =
          baseChangeFamily f c r α (IsLocalRing.closedPoint R)) :
    IsRelativeCycle f r α ↔
      ∀ i, @IsRelativeCycle _ _ (pullback.snd f (g i)) _ (hg.isLocallyNoetherian i) r
        (baseChangeFamily f (g i) r α) := by
  refine ⟨fun hα i R _ _ _ c ↦ (htrans i R c).2 (hα R (c ≫ g i)), fun hall R _ _ _ c ↦ ?_⟩
  obtain ⟨i, R', iR', iR'd, iR'dvr, e, hinje, hloce, c', hsq, -, -⟩ :=
    exists_isDiscreteValuationRing_lift_of_isHCovering hg R c
  let _ : CommRing R' := iR'
  let _ : IsDomain R' := iR'd
  let _ : IsDiscreteValuationRing R' := iR'dvr
  refine hdvr R c R' e hinje hloce ?_
  rw [hsq]
  exact (htrans i R' c').1 (hall i R' c')

/-- **The argument of Lemma 0H52, membership form.** Under the hypotheses of
`Stacks.Chow.isRelativeCycle_iff_forall_baseChangeFamily`, a family of `r`-cycles on the fibres of
`X/S` lies in `z(X/S, r)` if and only if each of its base changes along the members of the h
covering lies in `z(X ×_S S' i / S' i, r)`. -/
theorem mem_relativeCycles_iff_forall_baseChangeFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r)
    {I : Type v} (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S) (hg : IsHCovering S' g)
    (htrans : ∀ (i : I) (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (c : Spec (.of R) ⟶ S' i),
      (specializationCycle (pullback.snd (pullback.snd f (g i)) c) r
            (baseChangeFamily (pullback.snd f (g i)) c r (baseChangeFamily f (g i) r α)
              (genericPoint (Spec (.of R)))) =
          baseChangeFamily (pullback.snd f (g i)) c r (baseChangeFamily f (g i) r α)
            (IsLocalRing.closedPoint R)) ↔
        specializationCycle (pullback.snd f (c ≫ g i)) r
            (baseChangeFamily f (c ≫ g i) r α (genericPoint (Spec (.of R)))) =
          baseChangeFamily f (c ≫ g i) r α (IsLocalRing.closedPoint R))
    (hdvr : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (c : Spec (.of R) ⟶ S) (R' : Type u) [CommRing R'] [IsDomain R']
      [IsDiscreteValuationRing R'] (e : R →+* R'), Function.Injective e → IsLocalHom e →
      (specializationCycle (pullback.snd f (Spec.map (CommRingCat.ofHom e) ≫ c)) r
            (baseChangeFamily f (Spec.map (CommRingCat.ofHom e) ≫ c) r α
              (genericPoint (Spec (.of R')))) =
          baseChangeFamily f (Spec.map (CommRingCat.ofHom e) ≫ c) r α
            (IsLocalRing.closedPoint R')) →
        specializationCycle (pullback.snd f c) r
            (baseChangeFamily f c r α (genericPoint (Spec (.of R)))) =
          baseChangeFamily f c r α (IsLocalRing.closedPoint R)) :
    α ∈ relativeCycles f r ↔
      ∀ i, baseChangeFamily f (g i) r α ∈
        @relativeCycles _ _ (pullback.snd f (g i)) _ (hg.isLocallyNoetherian i) r :=
  isRelativeCycle_iff_forall_baseChangeFamily f r α S' g hg htrans hdvr

/-! ### The two inputs of Lemma 0H52 -/

/-- **The two-step base change compatibility of Section 0H4N, read on the valuative identity.**
Base changing a family `α` of `r`-cycles on the fibres of `X/S` along `g : S' ⟶ S` and then along
`c : Spec R ⟶ S'` gives the family `(c ≫ g)^*α`, read through the canonical isomorphism
`(X ×_S S') ×_{S'} Spec R ≅ X ×_S Spec R` (Tag 0H4P, part (1)). Reading through that isomorphism
commutes with specialization (Tag 0H4L for open immersions) and is injective, so the valuative
identity holds for one family exactly when it holds for the other. -/
theorem specializationCycle_baseChangeFamily_baseChangeFamily_iff {X S S' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (c : Spec (.of R) ⟶ S') :
    specializationCycle (pullback.snd (pullback.snd f g) c) r
          (baseChangeFamily (pullback.snd f g) c r (baseChangeFamily f g r α)
            (genericPoint (Spec (.of R)))) =
        baseChangeFamily (pullback.snd f g) c r (baseChangeFamily f g r α)
          (IsLocalRing.closedPoint R) ↔
      specializationCycle (pullback.snd f (c ≫ g)) r
          (baseChangeFamily f (c ≫ g) r α (genericPoint (Spec (.of R)))) =
        baseChangeFamily f (c ≫ g) r α (IsLocalRing.closedPoint R) := by
  rw [baseChangeFamily_baseChangeFamily_comp f g c r α,
    specializationCycle_fiberCycleRestrict (pullback.snd f (c ≫ g))
      (pullback.snd (pullback.snd f g) c) (pullbackLeftPullbackSndIso f g c).hom
      (pullbackLeftPullbackSndIso_hom_snd f g c) r
      (baseChangeFamily f (c ≫ g) r α (genericPoint (Spec (.of R))))]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  exact fiberCycleRestrict_injective_of_isIso (pullback.snd f (c ≫ g))
    (pullback.snd (pullback.snd f g) c) (pullbackLeftPullbackSndIso f g c).hom
    (pullbackLeftPullbackSndIso_hom_snd f g c) (IsLocalRing.closedPoint R) r h

/-- The base change map on the cycles of a fibre over a prescribed point is injective
(Section 0H4E): it is `Stacks.Chow.baseChangeFiberCycle` after substituting the equality of
points, and that map is injective by `Stacks.Chow.injective_baseChangeFiberCycle`. -/
theorem injective_baseChangeFiberCycleOfEq {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) {t : S'} {s : S} (hst : g t = s) (r : ℕ) :
    Function.Injective (baseChangeFiberCycleOfEq f g hst r) := by
  subst hst
  exact injective_baseChangeFiberCycle f g t r

/-- **Descent of the valuative identity along an extension of discrete valuation rings.** Let
`c : Spec R ⟶ S` be a morphism out of the spectrum of a discrete valuation ring and let
`e : R ⟶ R'` be an injective local homomorphism of discrete valuation rings. If the
specialization of the generic member of the base change of `α` along `Spec R' ⟶ Spec R ⟶ S` is
its closed member, then the same holds for the base change along `c`.

By the two-step compatibility the hypothesis is the valuative identity for the base change along
`Spec R' ⟶ Spec R` of `c^*α`; by Tag 0H4K specialization commutes with that base change, and the
base change map on the cycles of the special fibre is injective (Section 0H4E). -/
theorem specializationCycle_baseChangeFamily_of_isExtension {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : FamilyOfCycles f r) (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (c : Spec (.of R) ⟶ S) (R' : Type u)
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] (e : R →+* R')
    (he : Function.Injective e) (hloc : IsLocalHom e)
    (h : specializationCycle (pullback.snd f (Spec.map (CommRingCat.ofHom e) ≫ c)) r
          (baseChangeFamily f (Spec.map (CommRingCat.ofHom e) ≫ c) r α
            (genericPoint (Spec (.of R')))) =
        baseChangeFamily f (Spec.map (CommRingCat.ofHom e) ≫ c) r α
          (IsLocalRing.closedPoint R')) :
    specializationCycle (pullback.snd f c) r
        (baseChangeFamily f c r α (genericPoint (Spec (.of R)))) =
      baseChangeFamily f c r α (IsLocalRing.closedPoint R) := by
  let : Algebra R R' := e.toAlgebra
  have : IsDiscreteValuationRing.IsExtension R R' :=
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective R R').mpr he
      toIsLocalHom := hloc }
  let β := baseChangeFamily f c r α
  have h' := (specializationCycle_baseChangeFamily_baseChangeFamily_iff f c r α R'
    (specMapAlgebraMap R R')).mpr h
  have hK := congrArg (fun F => F (β (genericPoint (Spec (.of R)))))
    (baseChangeFiberCycleOfEq_comp_specializationCycleHom R' (pullback.snd f c) r)
  simp only [AddMonoidHom.comp_apply] at hK
  change baseChangeSpecialFibreCycle R' (pullback.snd f c) r
      (specializationCycle (pullback.snd f c) r (β (genericPoint (Spec (.of R))))) =
    specializationCycle (pullback.snd (pullback.snd f c) (specMapAlgebraMap R R')) r
      (baseChangeGenericFibreCycle R' (pullback.snd f c) r (β (genericPoint (Spec (.of R)))))
    at hK
  rw [baseChangeFiberCycleOfEq_family] at hK
  have hcl : baseChangeSpecialFibreCycle R' (pullback.snd f c) r (β (IsLocalRing.closedPoint R)) =
      baseChangeFamily (pullback.snd f c) (specMapAlgebraMap R R') r β
        (IsLocalRing.closedPoint R') :=
    baseChangeFiberCycleOfEq_family _ _ _ _ _
  refine injective_baseChangeFiberCycleOfEq (pullback.snd f c) (specMapAlgebraMap R R')
    (specMapAlgebraMap_closedPoint R R') r ?_
  change baseChangeSpecialFibreCycle R' (pullback.snd f c) r
      (specializationCycle (pullback.snd f c) r (β (genericPoint (Spec (.of R))))) =
    baseChangeSpecialFibreCycle R' (pullback.snd f c) r (β (IsLocalRing.closedPoint R))
  rw [hK, hcl]
  exact h'

/-! ### Lemma 0H52 -/

/-- **Stacks Project, Lemma 0H52.** Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of
finite type, let `r ≥ 0` and let `α` be a family of `r`-cycles on the fibres of `X/S`. Let
`{g i : S' i ⟶ S}` be an h covering. Then `α` is a relative `r`-cycle if and only if each base
change `(g i)^*α` is a relative `r`-cycle.

This is `Stacks.Chow.isRelativeCycle_iff_forall_baseChangeFamily` with its two inputs supplied:
the two-step base change compatibility by
`Stacks.Chow.specializationCycle_baseChangeFamily_baseChangeFamily_iff` and the descent along an
extension of discrete valuation rings by
`Stacks.Chow.specializationCycle_baseChangeFamily_of_isExtension`. -/
@[stacks 0H52]
theorem isRelativeCycle_iff_forall_isRelativeCycle_baseChangeFamily {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r)
    {I : Type v} (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S) (hg : IsHCovering S' g) :
    IsRelativeCycle f r α ↔
      ∀ i, @IsRelativeCycle _ _ (pullback.snd f (g i)) _ (hg.isLocallyNoetherian i) r
        (baseChangeFamily f (g i) r α) :=
  isRelativeCycle_iff_forall_baseChangeFamily f r α S' g hg
    (fun i R _ _ _ c ↦ specializationCycle_baseChangeFamily_baseChangeFamily_iff f (g i) r α R c)
    (fun R _ _ _ c R' _ _ _ e he hloc h ↦
      specializationCycle_baseChangeFamily_of_isExtension f r α R c R' e he hloc h)

/-- **Lemma 0H52 for a single proper surjective morphism.** Let `S` be locally Noetherian, let
`f : X ⟶ S` be locally of finite type and let `g : S' ⟶ S` be proper, surjective and locally of
finite presentation. A family `α` of `r`-cycles on the fibres of `X/S` whose base change along `g`
is a relative `r`-cycle is itself a relative `r`-cycle: `g` alone is an h covering, by
Tag 0ETW. -/
theorem isRelativeCycle_of_isRelativeCycle_baseChangeFamily_of_isProper {X S S' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (g : S' ⟶ S) [IsProper g]
    [Surjective g] [LocallyOfFinitePresentation g] (r : ℕ) (α : FamilyOfCycles f r)
    (h : @IsRelativeCycle _ _ (pullback.snd f g) _
      (LocallyOfFiniteType.isLocallyNoetherian g) r (baseChangeFamily f g r α)) :
    IsRelativeCycle f r α := by
  have hg : IsHCovering (fun _ : Unit ↦ S') (fun _ ↦ g) :=
    surjective_proper_isHCovering g ⟨inferInstance, inferInstance, inferInstance⟩
  exact (isRelativeCycle_iff_forall_isRelativeCycle_baseChangeFamily f r α _ _ hg).mpr
    fun _ ↦ h

end Stacks.Chow

end
