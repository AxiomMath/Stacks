module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.ProperOverDvr

/-!
# Reducedness of a proper flat algebraic space over a discrete valuation ring

Let `R` be a discrete valuation ring and let `X` be an algebraic space over `Spec R` whose
structure morphism is proper and flat. If the special fibre of `X` is reduced, then `X` itself
is reduced, and so is its generic fibre.

Reducedness of an algebraic space is the étale-local property of admitting a reduced scheme
atlas. The argument takes an arbitrary étale chart `U ⟶ X`, passes to the open subscheme of
`U` on which `U` is reduced, and shows that this open subscheme still covers `X`: a point of
`X` specializes to a point above the closed point of `Spec R`, and the local ring of `U` at a
point above the closed point is reduced because a uniformizer is a nonzerodivisor there (by
flatness) and the quotient by it is a local ring of the special fibre.

## Main results

* `AlgebraicGeometry.Space.isReduced_of_isReduced_specialFiber`: the total space is reduced.
* `AlgebraicGeometry.Space.isReduced_genericFiber_of_isReduced_specialFiber`: the generic
  fibre is reduced.

## Implementation notes

The special and generic fibres are the restrictions of `X` along the morphisms of the chosen
big fppf site induced by `R ⟶ κ` and `R ⟶ Frac R`; the hypotheses record that the site
contains the spectra of all three rings. Restriction of presheaves is
`CategoryTheory.OverShriek.relocalizeRestrict`.

Restriction carries a representable sheaf to a representable sheaf, by
`AlgebraicGeometry.Space.restrict_representable`, and the private section on restricted
charts below packages that existence statement as data — the representing object together
with its projection and the cartesian square — and transports a base-change stable property
of an étale chart across it. That transport is what identifies the restricted chart as an
atlas of the restricted space.

## References

* [Stacks Project, Tag 0E0B](https://stacks.math.columbia.edu/tag/0E0B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Reducedness of a local ring from reducedness of a quotient -/

/-- A Noetherian local ring is reduced as soon as it is reduced modulo a nonzerodivisor lying
in the maximal ideal: a nilpotent is then infinitely divisible by that element, so Krull's
intersection theorem makes it zero. -/
private theorem isReduced_of_isReduced_quotient_by_regular_element
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A)
    (hregular : ∀ a : A, π * a = 0 → a = 0)
    (hquot : _root_.IsReduced (A ⧸ Ideal.span ({π} : Set A))) : _root_.IsReduced A := by
  let I : Ideal A := Ideal.span ({π} : Set A)
  have hI : I ≠ ⊤ := by
    intro h
    have hle : I ≤ IsLocalRing.maximalIdeal A :=
      Ideal.span_le.mpr fun x hx => by simpa using hx ▸ hπ
    have htop : (⊤ : Ideal A) ≤ IsLocalRing.maximalIdeal A := by simpa [h] using hle
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp htop)
  have hK := I.iInf_pow_smul_eq_bot_of_isLocalRing (M := A) hI
  have hregular_pow : ∀ n : ℕ, ∀ a : A, π ^ n * a = 0 → a = 0 := by
    intro n
    induction n with
    | zero =>
      intro a ha
      simpa using ha
    | succ n ih => exact fun a ha => ih a (hregular _ (by rwa [← mul_assoc, ← pow_succ']))
  refine ⟨fun a ha => ?_⟩
  have factor : ∀ n : ℕ, ∃ b : A, a = π ^ n * b ∧ IsNilpotent b := by
    intro n
    induction n with
    | zero => exact ⟨a, by simp, ha⟩
    | succ n ih =>
      obtain ⟨b, rfl, hb⟩ := ih
      have hmap : IsNilpotent (Ideal.Quotient.mk I b) := by
        obtain ⟨m, hm⟩ := hb
        exact ⟨m, by simpa using congrArg (Ideal.Quotient.mk I) hm⟩
      have hzero : Ideal.Quotient.mk I b = 0 :=
        hquot.eq_zero (Ideal.Quotient.mk I b) hmap
      have hbI : b ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp hzero
      obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton').mp hbI
      have hcnil : IsNilpotent c := by
        obtain ⟨m, hm⟩ := hb
        exact ⟨m, hregular_pow m _ (by rwa [← mul_pow, mul_comm, hc])⟩
      refine ⟨c, ?_, hcnil⟩
      rw [← hc]
      ring
  have hall : ∀ n : ℕ, a ∈ (I ^ n) • (⊤ : Submodule A A) := by
    intro n
    obtain ⟨b, hab, _⟩ := factor n
    rw [hab, Ideal.smul_top_eq_map]
    simpa using Ideal.mul_mem_right b (I ^ n)
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) n)
  have hmem : a ∈ ⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A A) := Submodule.mem_iInf _ |>.mpr hall
  rw [hK] at hmem
  simpa using hmem

/-- If a Noetherian ring is reduced after localizing at a prime, then it is already reduced
after inverting a single element outside that prime: one element kills the finitely many
generators of the nilradical. -/
private theorem exists_reduced_away_neighborhood_of_reduced_localization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] [_root_.IsReduced (Localization.AtPrime p)] :
    ∃ s : A, s ∉ p ∧ _root_.IsReduced (Localization.Away s) := by
  classical
  let N : Ideal A := nilradical A
  obtain ⟨F, hFspan⟩ := IsNoetherian.noetherian N
  have hkill : ∀ F' : Finset A, (∀ a ∈ F', a ∈ F) →
      ∃ s : A, s ∉ p ∧ ∀ a ∈ F', s * a = 0 := by
    intro F'
    induction F' using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, p.one_notMem, by simp⟩
    | @insert a F' ha ih =>
      intro hmem
      obtain ⟨s, hs, hsF⟩ := ih fun b hb => hmem b (Finset.mem_insert_of_mem hb)
      have haN : a ∈ N := by
        rw [← hFspan]
        exact Submodule.subset_span (hmem a (Finset.mem_insert_self ..))
      have haNil : IsNilpotent a := (mem_nilradical).mp haN
      have haZero : algebraMap A (Localization.AtPrime p) a = 0 :=
        IsReduced.eq_zero _ (haNil.map (algebraMap A (Localization.AtPrime p)))
      obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl
        (Localization.AtPrime p) a).mp haZero
      refine ⟨s * c, Ideal.IsPrime.mul_notMem (I := p) inferInstance hs c.property, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rw [mul_assoc, hc, mul_zero]
      · rw [mul_right_comm, hsF b hb, zero_mul]
  obtain ⟨s, hs, hkillF⟩ := hkill F fun _ h => h
  have hkillN : ∀ a ∈ N, s * a = 0 := by
    intro a ha
    rw [← hFspan] at ha
    refine Submodule.span_induction (s := (F : Set A)) ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact hkillF x hx
    · simp
    · intro x y hx hy hxs hys
      simp [mul_add, hxs, hys]
    · intro r x hx hxs
      rw [smul_eq_mul, mul_left_comm, hxs, mul_zero]
  let Aₛ := Localization.Away s
  have hred : _root_.IsReduced Aₛ := by
    constructor
    intro x hx
    obtain ⟨⟨a, d⟩, hrepr⟩ := IsLocalization.surj (Submonoid.powers s) x
    obtain ⟨n, hn⟩ := hx
    have hpow : algebraMap A Aₛ (a ^ n) = 0 := by
      rw [map_pow, show algebraMap A Aₛ a = x * algebraMap A Aₛ d from hrepr.symm, mul_pow,
        hn, zero_mul]
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) Aₛ
      (a ^ n)).mp hpow
    have htnil : IsNilpotent ((t : A) * a) := by
      refine ⟨n + 1, ?_⟩
      rw [pow_succ, mul_pow]
      calc
        (t : A) ^ n * a ^ n * ((t : A) * a) =
            (t : A) ^ n * ((t : A) * a ^ n) * a := by ring
        _ = 0 := by simp [ht]
    have hz := hkillN ((t : A) * a) ((mem_nilradical).mpr htnil)
    have hmap : algebraMap A Aₛ s *
        (algebraMap A Aₛ (t : A) * algebraMap A Aₛ a) = 0 := by
      simpa only [map_mul, map_zero] using congrArg (algebraMap A Aₛ) hz
    have hsunit : IsUnit (algebraMap A Aₛ s) :=
      IsLocalization.map_units Aₛ ⟨s, show s ∈ Submonoid.powers s from ⟨1, by simp⟩⟩
    have htunit : IsUnit (algebraMap A Aₛ (t : A)) :=
      IsLocalization.map_units Aₛ t
    have ha0 : algebraMap A Aₛ a = 0 := by
      have hcancel : algebraMap A Aₛ a *
          (algebraMap A Aₛ s * algebraMap A Aₛ (t : A)) =
          0 * (algebraMap A Aₛ s * algebraMap A Aₛ (t : A)) := by
        calc
          algebraMap A Aₛ a *
              (algebraMap A Aₛ s * algebraMap A Aₛ (t : A)) =
              algebraMap A Aₛ s *
                (algebraMap A Aₛ (t : A) * algebraMap A Aₛ a) := by ring
          _ = 0 *
              (algebraMap A Aₛ s * algebraMap A Aₛ (t : A)) := by
                simpa using hmap
      apply (hsunit.mul htunit).mul_left_inj.mp
      simpa [map_mul] using hcancel
    have hrepr0 : x * algebraMap A Aₛ (d : A) = 0 := by
      calc
        x * algebraMap A Aₛ (d : A) = algebraMap A Aₛ a := hrepr
        _ = 0 := ha0
    exact (IsLocalization.map_units Aₛ d).mul_left_inj.mp (by simpa using hrepr0)
  exact ⟨s, hs, by simpa [Aₛ] using hred⟩

/-! ### The reduced open locus of a locally Noetherian scheme -/

/-- The stalk of a scheme at a point of an affine open is reduced iff the corresponding
localization of the ring of sections is. -/
private theorem isReduced_stalk_iff_isReduced_localization {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : X) (hxU : x ∈ U) :
    _root_.IsReduced (X.presheaf.stalk x) ↔
      _root_.IsReduced (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  let _ : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let e : X.presheaf.stalk x ≃ₐ[Γ(X, U)]
      Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _ _
  exact ⟨fun _ => isReduced_of_injective e.symm.toRingHom e.symm.injective,
    fun _ => isReduced_of_injective e.toRingHom e.injective⟩

/-- A point of a locally Noetherian scheme with reduced local ring has a reduced open
neighbourhood: shrink an affine neighbourhood to a basic open on which the ring is reduced. -/
@[ega "I 6.1.13"]
private theorem exists_reduced_open_neighborhood_of_reduced_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X)
    (hx : _root_.IsReduced (X.presheaf.stalk x)) :
    ∃ V : X.Opens, x ∈ V ∧ IsReduced V.toScheme := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let A := Γ(X, U)
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : _root_.IsReduced (Localization.AtPrime p.asIdeal) :=
    (isReduced_stalk_iff_isReduced_localization hU x hxU).mp hx
  obtain ⟨s, hs, haway⟩ :=
    exists_reduced_away_neighborhood_of_reduced_localization p.asIdeal
  let W := X.basicOpen s
  have hW : IsAffineOpen W := hU.basicOpen s
  let _ : IsLocalization.Away s Γ(X, W) := hU.isLocalization_basicOpen s
  let es : Localization.Away s ≃ₐ[A] Γ(X, W) :=
    IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) Γ(X, W)
  have hredRing : _root_.IsReduced Γ(X, W) :=
    isReduced_of_injective es.symm.toRingHom es.symm.injective
  have hredW : IsReduced W.toScheme := by
    have : IsReduced (Spec (.of Γ(X, W))) :=
      (affine_isReduced_iff (CommRingCat.of Γ(X, W))).2 hredRing
    exact isReduced_of_isOpenImmersion hW.isoSpec.hom
  have hxSpec : p ∈ PrimeSpectrum.basicOpen s := by
    rw [PrimeSpectrum.mem_basicOpen]
    exact hs
  have hxW : x ∈ W := by
    have hx' : hU.fromSpec p ∈ W := by
      show p ∈ hU.fromSpec ⁻¹ᵁ W
      rw [hU.fromSpec_preimage_basicOpen s]
      exact hxSpec
    simpa [W, p, hU.fromSpec_primeIdealOf] using hx'
  exact ⟨W, hxW, hredW⟩

/-- The largest open subscheme of a scheme that is reduced: the union of all reduced open
subschemes. -/
private noncomputable def reducedOpenLocus (X : Scheme.{u}) : X.Opens :=
  ⨆ V : {V : X.Opens // IsReduced V.toScheme}, V.1

/-- A point with reduced local ring lies in the reduced open locus. -/
private theorem mem_reducedOpenLocus_of_reduced_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X)
    (hx : _root_.IsReduced (X.presheaf.stalk x)) : x ∈ reducedOpenLocus X := by
  obtain ⟨V, hxV, hV⟩ := exists_reduced_open_neighborhood_of_reduced_stalk x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩

/-- The reduced open locus is reduced: the reduced open subschemes cover it. -/
private theorem isReduced_reducedOpenLocus (X : Scheme.{u}) :
    IsReduced (reducedOpenLocus X).toScheme := by
  let W := reducedOpenLocus X
  let J := {V : X.Opens // IsReduced V.toScheme}
  let coverOpen : J → W.toScheme.Opens := fun i => W.ι ⁻¹ᵁ i.1
  have hcover : TopologicalSpace.IsOpenCover coverOpen := by
    apply TopologicalSpace.IsOpenCover.mk
    apply le_antisymm
    · exact le_top
    · intro x hx
      have hxW : (x.1 : X) ∈ reducedOpenLocus X := x.2
      rw [reducedOpenLocus, TopologicalSpace.Opens.mem_iSup] at hxW
      obtain ⟨i, hi⟩ := hxW
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
      show (x.1 : X) ∈ i.1
      exact hi
  let 𝒰 := Scheme.openCoverOfIsOpenCover W.toScheme coverOpen hcover
  have hred : ∀ i : 𝒰.I₀, IsReduced (𝒰.X i) := by
    intro i
    show IsReduced (coverOpen i).toScheme
    let e := Scheme.Opens.isoOfLE (le_iSup (fun V : J => V.1) i)
    have hOpen : AlgebraicGeometry.IsOpenImmersion e.hom := by
      let _ : IsIso e.hom := e.isIso_hom
      exact IsOpenImmersion.of_isIso e.hom
    exact @isReduced_of_isOpenImmersion _ _ e.hom hOpen i.2
  exact IsReduced.of_openCover W.toScheme 𝒰

/-! ### Stalks of a flat scheme over a discrete valuation ring -/

/-- Reducedness of a fibre passes to an open subscheme of the source. -/
private theorem isReduced_fiber_of_isOpenImmersion
    {X Y Z : Scheme.{u}} (e : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion e]
    (f : X ⟶ Z) (g : Y ⟶ Z) (he : e ≫ f = g) (y : Z)
    [IsReduced (f.fiber y)] : IsReduced (g.fiber y) := by
  let i : g.fiber y ≅ pullback e (f.fiberι y) :=
    (pullback.congrHom he rfl).symm ≪≫
      (pullbackRightPullbackFstIso f (Z.fromSpecResidueField y) e).symm
  let j : g.fiber y ⟶ f.fiber y := i.hom ≫ pullback.snd e (f.fiberι y)
  have : AlgebraicGeometry.IsOpenImmersion (pullback.snd e (f.fiberι y)) :=
    MorphismProperty.pullback_snd e (f.fiberι y) inferInstance
  have : AlgebraicGeometry.IsOpenImmersion i.hom := inferInstance
  have : AlgebraicGeometry.IsOpenImmersion j := inferInstance
  exact isReduced_of_isOpenImmersion j

/-- Over a local ring, the fibre over the closed point is the base change along the residue
map. -/
private theorem isReduced_fiber_closedPoint_of_isReduced_pullback_residue
    (R : Type u) [CommRing R] [IsLocalRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))] :
    IsReduced (f.fiber (IsLocalRing.closedPoint (CommRingCat.of R))) := by
  let y : Spec (.of R) := IsLocalRing.closedPoint (CommRingCat.of R)
  let m := IsLocalRing.maximalIdeal R
  let ek : CommRingCat.of (IsLocalRing.ResidueField R) ≅ .of m.ResidueField :=
    (RingEquiv.ofBijective (algebraMap (R ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField).toCommRingCatIso
  let s := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let e := ek ≪≫ (Scheme.Spec.residueFieldIso (.of R) y).symm
  let i : Spec ((Spec (.of R)).residueField y) ⟶
      Spec (.of (IsLocalRing.ResidueField R)) :=
    Spec.map e.hom
  have hkcomp : CommRingCat.ofHom (IsLocalRing.residue R) ≫ ek.hom =
      CommRingCat.ofHom (algebraMap R m.ResidueField) := by
    ext r
    exact (IsScalarTower.algebraMap_apply R (R ⧸ m) m.ResidueField r).symm
  have hi : i ≫ s = (Spec (.of R)).fromSpecResidueField y := by
    show Spec.map (ek.hom ≫ (Scheme.Spec.residueFieldIso (.of R) y).inv) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) = _
    calc
      _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R) ≫
          (ek.hom ≫ (Scheme.Spec.residueFieldIso (.of R) y).inv)) :=
        (Spec.map_comp _ _).symm
      _ = Spec.map ((CommRingCat.ofHom (IsLocalRing.residue R) ≫ ek.hom) ≫
          (Scheme.Spec.residueFieldIso (.of R) y).inv) :=
        congrArg Spec.map (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom (algebraMap R m.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of R) y).inv) :=
        congrArg (fun t => Spec.map (t ≫ (Scheme.Spec.residueFieldIso (.of R) y).inv)) hkcomp
      _ = _ := (Spec.map_comp _ _).trans
        (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) y)
  have : IsIso i := by
    dsimp only [i]
    infer_instance
  let j : f.fiber y ⟶ pullback f s :=
    pullback.map f ((Spec (.of R)).fromSpecResidueField y) f s (𝟙 X) i (𝟙 _)
      (by simp) (by simpa using hi.symm)
  have : IsIso j := by
    dsimp only [j]
    exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact isReduced_of_isOpenImmersion j

/-- A flat, locally Noetherian scheme over a discrete valuation ring with reduced special
fibre has reduced local rings at the points of that fibre: a uniformizer is a nonzerodivisor
in the local ring by flatness, and the quotient by it is a local ring of the fibre. -/
@[ega "IV 11.3.13" "(ii), special case"]
private theorem isReduced_stalk_of_closedPoint_of_flat
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f]
    [IsLocallyNoetherian X]
    [IsReduced (f.fiber (IsLocalRing.closedPoint (CommRingCat.of R)))]
    (x : X) (hfx : f x = IsLocalRing.closedPoint (CommRingCat.of R)) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let A := Γ(X, U)
  let q := hU.primeIdealOf ⟨x, hxU⟩
  let φ : R →+* A := (Spec.preimage (hU.fromSpec ≫ f)).hom
  have he : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom φ) := by simp [φ]
  have hqx : hU.fromSpec q = x := by
    simpa [q] using hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have heval : f x = PrimeSpectrum.comap φ q := by
    have hcomp : f x = (hU.fromSpec ≫ f) q := by
      rw [← hqx]
      rfl
    have hmap : (hU.fromSpec ≫ f) q = (Spec.map (CommRingCat.ofHom φ)) q :=
      congrArg (fun g => g q) he
    exact hcomp.trans (hmap.trans rfl)
  let y : PrimeSpectrum R := f x
  have hq : PrimeSpectrum.comap φ q = y :=
    PrimeSpectrum.ext (congrArg (fun z : Spec (.of R) => z.asIdeal) heval).symm
  have hy : y = IsLocalRing.closedPoint (CommRingCat.of R) :=
    congrArg (fun z : Spec (.of R) => (z : PrimeSpectrum R)) hfx
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsReduced (f.fiber y) := by
    rw [hy]
    infer_instance
  have : IsReduced ((Spec.map (CommRingCat.ofHom φ)).fiber y) :=
    isReduced_fiber_of_isOpenImmersion hU.fromSpec f _ he y
  have hredQuot := isReduced_quotient_localization_of_isReduced_fiber
    φ y q hq hy ϖ hϖ
  let _ : Algebra R A := RingHom.toAlgebra φ
  have hflatSpec : Flat (Spec.map (CommRingCat.ofHom φ)) := by
    rw [← he]
    infer_instance
  have hflatRing : (CommRingCat.ofHom φ).hom.Flat := Flat.SpecMap_iff.mp hflatSpec
  have : Module.Flat R A := RingHom.flat_algebraMap_iff.mpr hflatRing
  let Aq := Localization.AtPrime q.asIdeal
  let _ : IsLocalization.AtPrime Aq q.asIdeal := Localization.isLocalization
  have : Module.Flat A Aq := IsLocalization.flat Aq q.asIdeal.primeCompl
  have : Module.Flat R Aq := Module.Flat.trans R A Aq
  have hπchart : φ ϖ ∈ q.asIdeal := by
    have hπR : ϖ ∈ y.asIdeal := by
      have hIdeal : y.asIdeal = IsLocalRing.maximalIdeal R :=
        congrArg (fun z : Spec (.of R) => z.asIdeal) hy
      rw [hIdeal, hϖ.maximalIdeal_eq]
      exact Ideal.subset_span (by simp)
    have hπq : ϖ ∈ (PrimeSpectrum.comap φ q).asIdeal := by
      rw [hq]
      exact hπR
    change ϖ ∈ q.asIdeal.comap φ at hπq
    exact (Ideal.mem_comap.mp hπq)
  have hπmax : algebraMap A Aq (φ ϖ) ∈ IsLocalRing.maximalIdeal Aq := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem (algebraMap A Aq) hπchart
  have hregular : ∀ a : Aq, algebraMap A Aq (φ ϖ) * a = 0 → a = 0 := by
    intro a ha
    have hregR : ϖ ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hϖ.ne_zero
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors hregR (M := Aq)
    rw [IsSMulRegular] at hreg
    have ha' : ϖ • a = 0 := by
      rw [Algebra.smul_def]
      show algebraMap R Aq ϖ * a = 0
      rw [IsScalarTower.algebraMap_apply R A Aq]
      have hφ : algebraMap R A = φ := rfl
      simpa [hφ] using ha
    apply hreg
    simpa using ha'
  have hredLoc : _root_.IsReduced Aq :=
    isReduced_of_isReduced_quotient_by_regular_element
      (algebraMap A Aq (φ ϖ)) hπmax hregular hredQuot
  exact (isReduced_stalk_iff_isReduced_localization hU x hxU).mpr hredLoc

/-- Over the spectrum of a local ring, every point of a space mapping by a closed map
specializes to a point above the closed point. -/
private theorem exists_specializes_closedPoint_of_closedMap
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Type*} [TopologicalSpace X] (f : X → Spec (.of R))
    (hf : IsClosedMap f) (x : X) :
    ∃ y : X, f y = IsLocalRing.closedPoint (CommRingCat.of R) ∧ x ⤳ y := by
  have hspec : f x ⤳ IsLocalRing.closedPoint (CommRingCat.of R) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal (f x).2.1)
  obtain ⟨y, hyC, hyf⟩ := hspec.mem_closed (hf _ isClosed_closure)
    ⟨x, subset_closure (Set.mem_singleton x), rfl⟩
  exact ⟨y, hyf, specializes_iff_mem_closure.mpr hyC⟩

/-- An open map onto a space that is closed over the spectrum of a local ring is surjective as
soon as its image contains the fibre over the closed point. -/
private theorem surjective_of_closedMap_and_openMap
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Spec (.of R)) (hf : IsClosedMap f) (g : Y → X) (hg : IsOpenMap g)
    (hclosed : ∀ x : X, f x = IsLocalRing.closedPoint (CommRingCat.of R) →
      x ∈ Set.range g) : Function.Surjective g := by
  intro x
  obtain ⟨y, hyf, hxy⟩ := exists_specializes_closedPoint_of_closedMap f hf x
  exact hxy.mem_open hg.isOpen_range (hclosed y hyf)

/-- The spectrum of the fraction field of a discrete valuation ring is an open subscheme of
the spectrum of the ring: the fraction field is the localization away from a uniformizer. -/
private theorem isOpenImmersion_specFractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    AlgebraicGeometry.IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ : algebraMap R (FractionRing R) ϖ ≠ 0 := by
    simpa using (IsFractionRing.injective R (FractionRing R)).ne hϖ.ne_zero
  have : IsLocalization.Away ϖ (FractionRing R) := by
    apply IsLocalization.Away.mk
    · exact isUnit_iff_ne_zero.mpr hπ
    · intro x
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
      obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (show b ≠ 0 by simpa using hb) hϖ
      refine ⟨n, a * ↑v⁻¹, ?_⟩
      have hv : algebraMap R (FractionRing R) (v : R) ≠ 0 :=
        (v.isUnit.map _).ne_zero
      simp only [map_mul, map_pow]
      field_simp
      simp
    · intro a b hab
      exact ⟨0, by simpa using (IsFractionRing.injective R (FractionRing R)) hab⟩
  exact IsOpenImmersion.of_isLocalization ϖ

/-- **The local rings along the special fibre of a flat scheme over a discrete valuation
ring.** If `f : X ⟶ Spec R` is flat, `X` is locally Noetherian and the fibre of `f` over the
closed point is reduced, then the local ring of `X` at every point of that fibre is reduced: a
uniformizer is a nonzerodivisor in it by flatness, and the quotient by it is a local ring of
the fibre, so Krull's intersection theorem applies. -/
@[ega "IV 11.3.13" "(ii), special case"]
public alias _root_.AlgebraicGeometry.isReduced_stalk_of_flat_of_isReduced_closedFiber :=
  isReduced_stalk_of_closedPoint_of_flat

/-! ### Restriction of a representable sheaf to a smaller base -/

section Restriction

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- A representing object for the restriction of a representable sheaf along `g`, together
with the projection to the original object and the cartesian square exhibiting it as a fibre
product over the two bases. -/
private structure RestrictedChart (X' : BigFppfOver B S' hS') where
  /-- The representing object over the smaller base. -/
  base : BigFppfOver B S hS
  /-- Its projection to the original object. -/
  projection : base.left ⟶ X'.left
  /-- The projection and the two structure morphisms form a cartesian square of schemes. -/
  isPullback : IsPullback (B.inclusion.map projection) (B.inclusion.map base.hom)
    (B.inclusion.map X'.hom) (B.inclusion.map g)

/-- Every representable sheaf has a restricted chart: restriction along `g` carries the sheaf
represented by `X'` to the one represented by the fibre product with the smaller base. -/
private noncomputable def restrictedChart (X' : BigFppfOver B S' hS') :
    RestrictedChart B S S' hS hS' g X' := by
  classical
  have h := restrict_representable B S S' hS hS' g X'
    ⟨yoneda.obj X', (isAlgebraicSpace_yoneda B S' hS' X').isSheaf⟩ ⟨Iso.refl _⟩
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    (Classical.choose_spec (Classical.choose_spec h)).1⟩

end Restriction

section RestrictedChartApi

variable {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
  {g : B.obj hS ⟶ B.obj hS'} {X' X'' : BigFppfOver B S' hS'}

namespace RestrictedChart

/-- The cartesian square of a restricted chart, read in the site rather than in schemes. -/
private theorem square (D : RestrictedChart B S S' hS hS' g X') :
    IsPullback D.projection D.base.hom X'.hom g :=
  IsPullback.of_map_of_faithful B.inclusion D.isPullback

/-- The universal property of a restricted chart: morphisms to it from an object `T` over the
smaller base are morphisms to `X'` from `T` viewed over the larger base. -/
private noncomputable def equiv (D : RestrictedChart B S S' hS hS' g X')
    (T : BigFppfOver B S hS) : (T ⟶ D.base) ≃ ((Over.map g).obj T ⟶ X') := by
  have h := D.square
  refine
    { toFun := fun f => Over.homMk (f.left ≫ D.projection) ?_
      invFun := fun q =>
        Over.homMk (h.lift q.left T.hom (Over.w q)) (h.lift_snd _ _ _)
      left_inv := ?_
      right_inv := ?_ }
  · change _ = T.hom ≫ g
    rw [Category.assoc, h.w, ← Category.assoc, Over.w f]
  · intro f
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (h.lift (f.left ≫ D.projection) T.hom _) =
      B.inclusion.map f.left
    apply D.isPullback.hom_ext
    · calc
        B.inclusion.map (h.lift (f.left ≫ D.projection) T.hom _ ≫ D.projection) =
            B.inclusion.map (f.left ≫ D.projection) :=
          congrArg B.inclusion.map (h.lift_fst _ _ _)
        _ = B.inclusion.map f.left ≫ B.inclusion.map D.projection :=
          B.inclusion.map_comp _ _
    · calc
        B.inclusion.map (h.lift (f.left ≫ D.projection) T.hom _ ≫ D.base.hom) =
            B.inclusion.map T.hom := congrArg B.inclusion.map (h.lift_snd _ _ _)
        _ = B.inclusion.map (f.left ≫ D.base.hom) := by rw [Over.w f]
        _ = B.inclusion.map f.left ≫ B.inclusion.map D.base.hom := B.inclusion.map_comp _ _
  · intro q
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (h.lift q.left T.hom (Over.w q) ≫ D.projection) =
      B.inclusion.map q.left
    rw [B.inclusion.map_comp]
    exact congrArg B.inclusion.map (h.lift_fst _ _ _)

/-- A restricted chart does represent the restriction of the represented sheaf. -/
private noncomputable def iso (D : RestrictedChart B S S' hS hS' g X') :
    yoneda.obj D.base ≅ (OverShriek.relocalizeRestrict g).obj (yoneda.obj X') := by
  refine NatIso.ofComponents (fun T => Equiv.toIso (D.equiv T.unop)) ?_
  intro T T' m
  ext f
  apply Over.OverMorphism.ext
  simp [equiv, Category.assoc]

/-- The functoriality of restricted charts: a morphism of the originals induces one of the
restrictions. -/
private noncomputable def map (D : RestrictedChart B S S' hS hS' g X')
    (E : RestrictedChart B S S' hS hS' g X'') (f : X' ⟶ X'') : D.base ⟶ E.base := by
  have hcomm :
      (B.inclusion.map (D.projection ≫ f.left)) ≫ B.inclusion.map X''.hom =
        B.inclusion.map D.base.hom ≫ B.inclusion.map g := by
    rw [B.inclusion.map_comp, Category.assoc, ← B.inclusion.map_comp f.left, Over.w f,
      D.isPullback.w]
  refine Over.homMk (B.inclusion.preimage (E.isPullback.lift
    (B.inclusion.map (D.projection ≫ f.left)) (B.inclusion.map D.base.hom) hcomm)) ?_
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp, B.inclusion.map_preimage]
  exact E.isPullback.lift_snd _ _ _

/-- The induced morphism of restricted charts commutes with the projections. -/
private theorem map_projection (D : RestrictedChart B S S' hS hS' g X')
    (E : RestrictedChart B S S' hS hS' g X'') (f : X' ⟶ X'') :
    (D.map E f).left ≫ E.projection = D.projection ≫ f.left := by
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp]
  show B.inclusion.map (B.inclusion.preimage _) ≫ B.inclusion.map E.projection =
    B.inclusion.map (D.projection ≫ f.left)
  rw [B.inclusion.map_preimage]
  exact E.isPullback.lift_fst _ _ _

/-- The identification of a restricted chart with the restricted sheaf is natural. -/
private theorem iso_naturality (D : RestrictedChart B S S' hS hS' g X')
    (E : RestrictedChart B S S' hS hS' g X'') (f : X' ⟶ X'') :
    D.iso.hom ≫ (OverShriek.relocalizeRestrict g).map (yoneda.map f) =
      yoneda.map (D.map E f) ≫ E.iso.hom := by
  ext T x
  apply Over.OverMorphism.ext
  show (x.left ≫ D.projection) ≫ f.left =
    (x.left ≫ (D.map E f).left) ≫ E.projection
  simp only [Category.assoc, map_projection]

end RestrictedChart

/-- Two cartesian squares over the same morphism make the square comparing their left-hand
legs cartesian as well. -/
private theorem isPullback_of_pullback_squares
    {V U V' U' T T' : Scheme.{u}}
    {pV : V ⟶ V'} {pU : U ⟶ U'} {v : V ⟶ T} {u : U ⟶ T}
    {v' : V' ⟶ T'} {u' : U' ⟶ T'} {f : V ⟶ U} {f' : V' ⟶ U'}
    {e : T ⟶ T'}
    (hV : IsPullback pV v v' e) (hU : IsPullback pU u u' e)
    (hsq : f ≫ pU = pV ≫ f') (hf' : f' ≫ u' = v') (hf : f ≫ u = v) :
    IsPullback f pV pU f' :=
  ((by simpa only [hf, hf'] using hV : IsPullback pV (f ≫ u) (f' ≫ u') e).of_bot
    hsq.symm hU).flip

/-- The square relating a morphism of restricted charts to the morphism it restricts is
cartesian. -/
private theorem RestrictedChart.map_isPullback (D : RestrictedChart B S S' hS hS' g X')
    (E : RestrictedChart B S S' hS hS' g X'') (f : X' ⟶ X'') :
    IsPullback (B.inclusion.map (D.map E f).left) (B.inclusion.map D.projection)
      (B.inclusion.map E.projection) (B.inclusion.map f.left) := by
  apply isPullback_of_pullback_squares D.isPullback E.isPullback
  · simpa only [B.inclusion.map_comp] using
      congrArg B.inclusion.map (D.map_projection E f)
  · simpa only [B.inclusion.map_comp] using congrArg B.inclusion.map (Over.w f)
  · simpa only [B.inclusion.map_comp] using
      congrArg B.inclusion.map (Over.w (D.map E f))

/-- A base-change stable property of an étale chart of a sheaf over the larger base is
inherited by the induced chart of the restricted sheaf. -/
private theorem RestrictedChart.presheaf_property
    (P : MorphismProperty Scheme.{u}) [hPbc : P.IsStableUnderBaseChange]
    {F' : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (D : RestrictedChart B S S' hS hS' g X') (f : yoneda.obj X' ⟶ F')
    (hf : (P.inverseImage (BigFppfOver.toScheme B S' hS')).presheaf f) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (D.iso.hom ≫ (OverShriek.relocalizeRestrict g).map f) := by
  classical
  have _ : (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS hPbc
  have _ : (P.inverseImage (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply MorphismProperty.relative.of_exists
  intro T t
  let Res := OverShriek.relocalizeRestrict g
  let T' : BigFppfOver B S' hS' := (Over.map g).obj T
  let Tdata := restrictedChart B S S' hS hS' g T'
  let ξ : F'.obj (Opposite.op T') := by
    show (Res.obj F').obj (Opposite.op T)
    exact yonedaEquiv t
  let t' : yoneda.obj T' ⟶ F' := yonedaEquiv.symm ξ
  let delta : T ⟶ Tdata.base := by
    have hcomm : (𝟙 T.left) ≫ T'.hom = T.hom ≫ g := by simp [T']
    exact Over.homMk (Tdata.square.lift (𝟙 T.left) T.hom hcomm)
      (Tdata.square.lift_snd _ _ _)
  have hdelta : delta.left ≫ Tdata.projection = 𝟙 T.left := by
    dsimp only [delta, Over.homMk_left]
    exact Tdata.square.lift_fst _ _ _
  have hsection : Tdata.iso.hom.app (Opposite.op T) delta = 𝟙 T' := by
    apply Over.OverMorphism.ext
    simp [RestrictedChart.iso, RestrictedChart.equiv, hdelta, T']
  have ht : yoneda.map delta ≫ Tdata.iso.hom ≫ Res.map t' = t := by
    apply yonedaEquiv.injective
    show (Res.map t').app (Opposite.op T) (Tdata.iso.hom.app (Opposite.op T) delta) =
      yonedaEquiv t
    rw [hsection]
    show F'.map (𝟙 T').op ξ = ξ
    simp
  obtain ⟨V', snd, fst, hpb⟩ := hf.1 t'
  let Vdata := restrictedChart B S S' hS hS' g V'
  let fVU := yoneda.preimage fst
  have hfVU : yoneda.map fVU = fst := yoneda.map_preimage fst
  have hres : IsPullback (Res.map fst) (Res.map (yoneda.map snd))
      (Res.map f) (Res.map t') := IsPullback.map Res hpb
  have hnew : IsPullback (yoneda.map (Vdata.map D fVU)) (yoneda.map (Vdata.map Tdata snd))
      (D.iso.hom ≫ Res.map f) (Tdata.iso.hom ≫ Res.map t') := by
    refine hres.of_iso' Vdata.iso D.iso Tdata.iso (Iso.refl _) ?_ ?_ ?_ ?_
    · simpa only [← hfVU] using Vdata.iso_naturality D fVU
    · exact Vdata.iso_naturality Tdata snd
    · rfl
    · rfl
  have hW : IsPullback (yoneda.map (pullback.fst (Vdata.map Tdata snd) delta))
      (yoneda.map (pullback.snd (Vdata.map Tdata snd) delta))
      (yoneda.map (Vdata.map Tdata snd)) (yoneda.map delta) :=
    (IsPullback.of_hasPullback (Vdata.map Tdata snd) delta).map yoneda
  have hfinal : IsPullback
      (yoneda.map (pullback.fst (Vdata.map Tdata snd) delta ≫ Vdata.map D fVU))
      (yoneda.map (pullback.snd (Vdata.map Tdata snd) delta))
      (D.iso.hom ≫ Res.map f) t := by
    have h := hW.paste_horiz hnew
    simpa [Category.assoc, ht] using h
  refine ⟨pullback (Vdata.map Tdata snd) delta,
    yoneda.map (pullback.fst (Vdata.map Tdata snd) delta ≫ Vdata.map D fVU),
    pullback.snd (Vdata.map Tdata snd) delta, hfinal, ?_⟩
  have hq' := hf.2 t' fst snd hpb
  change P (B.inclusion.map snd.left) at hq'
  exact MorphismProperty.pullback_snd (Vdata.map Tdata snd) delta
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
      (Vdata.map_isPullback Tdata snd).flip hq')

end RestrictedChartApi

/-! ### Points of an algebraic space above the closed point -/

/-- The map from the points of a representable sheaf to the points of the representing scheme
is closed. -/
private theorem isClosedMap_pointsToScheme (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS) :
    IsClosedMap (pointsToScheme B S hS U) :=
  (schemePointsHomeomorph B S hS U).isClosedMap

/-- A field-valued point of a representable sheaf whose scheme point lies in an open
subobject comes from a field-valued point of that subobject. -/
private theorem fieldPoint_factors_through_open
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (j : V ⟶ U)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : schemePoint B S hS U p ∈
      Set.range ((BigFppfOver.toScheme B S hS).map j)) :
    ∃ q : FieldValuedPoint B S hS (yoneda.obj V),
      pointsMap B S hS (yoneda.obj V) (yoneda.map j)
        (q.class B S hS (yoneda.obj V)) = p.class B S hS (yoneda.obj U) := by
  classical
  let G := BigFppfOver.toScheme B S hS
  let A := FieldValuedPoint.siteObject B S hS (yoneda.obj U) p
  have hrange : Set.range (G.map p.value) ⊆ Set.range (G.map j) := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    have hz : z = IsLocalRing.closedPoint p.carrier :=
      (inferInstance : Subsingleton (PrimeSpectrum p.carrier)).elim _ _
    subst z
    simpa [schemePoint, G] using hp
  let ψ : Spec (.of p.carrier) ⟶ G.obj V :=
    IsOpenImmersion.lift (G.map j) (G.map p.value) hrange
  have hψ : ψ ≫ G.map j = G.map p.value := IsOpenImmersion.lift_fac _ _ _
  let k : A.left ⟶ V.left :=
    B.inclusion.preimage (show B.inclusion.obj A.left ⟶ B.inclusion.obj V.left from ψ)
  have hk : B.inclusion.map k = ψ := by
    show B.inclusion.map
      (B.inclusion.preimage
        (show B.inclusion.obj A.left ⟶ B.inclusion.obj V.left from ψ)) = ψ
    rw [B.inclusion.map_preimage]
  let a : A ⟶ V := Over.homMk k (by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp]
    have hj : G.map j ≫ B.inclusion.map U.hom = B.inclusion.map V.hom := by
      show B.inclusion.map j.left ≫ B.inclusion.map U.hom = B.inclusion.map V.hom
      rw [← B.inclusion.map_comp, j.w]
    have hpv : G.map p.value ≫ B.inclusion.map U.hom = B.inclusion.map A.hom := by
      show B.inclusion.map p.value.left ≫ B.inclusion.map U.hom = B.inclusion.map A.hom
      rw [← B.inclusion.map_comp, p.value.w]
      rfl
    rw [hk, ← hj, ← Category.assoc, hψ]
    exact hpv)
  have ha : a ≫ j = p.value := by
    apply Over.OverMorphism.ext
    have hleft : k ≫ j.left = p.value.left := by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, hk]
      show ψ ≫ G.map j = G.map p.value
      exact hψ
    exact hleft
  let q : FieldValuedPoint B S hS (yoneda.obj V) := ⟨p.carrier, p.contained, p.toBase, a⟩
  refine ⟨q, ?_⟩
  rw [pointsMap_class]
  have hmap : FieldValuedPoint.map B S hS (yoneda.obj V) (yoneda.map j) q = p := by
    cases p
    simp [q, FieldValuedPoint.map, ha]
  exact congrArg (FieldValuedPoint.class B S hS (yoneda.obj U)) hmap

/-! ### Reducedness of the total space and of the generic fibre -/

/-- **Stacks 0E0B.** A proper flat algebraic space over a discrete valuation ring is reduced
when its special fibre is reduced. -/
@[stacks 0E0B "total space"]
public theorem isReduced_of_isReduced_specialFiber
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (B : BigFppfSite.{u})
    (hR : B.Contains (Spec (.of R)))
    (hk : B.Contains (Spec (.of (IsLocalRing.ResidueField R))))
    (X : (BigFppfOver B (Spec (.of R)) hR)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of R)) hR X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hR))))
    (hproper : IsProper B (Spec (.of R)) hR f)
    (hflat : IsFlat B (Spec (.of R)) hR f)
    (hspecial :
      let g : B.obj hk ⟶ B.obj hR :=
        B.inclusion.preimage
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
      HasEtaleLocalProperty B
        (Spec (.of (IsLocalRing.ResidueField R))) hk
        ((OverShriek.relocalizeRestrict g).obj X)
        (fun T : Scheme.{u} => IsReduced T)) :
    HasEtaleLocalProperty B (Spec (.of R)) hR X
      (fun T : Scheme.{u} => IsReduced T) := by
  classical
  rcases hX.exists_atlas with ⟨U, a, haSurj, haEtale⟩
  let g : B.obj hk ⟶ B.obj hR :=
    B.inclusion.preimage (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  let Udata := restrictedChart B (Spec (.of (IsLocalRing.ResidueField R)))
    (Spec (.of R)) hk hR g U
  let Uₖ : BigFppfOver B (Spec (.of (IsLocalRing.ResidueField R))) hk := Udata.base
  let Xₖ := (OverShriek.relocalizeRestrict g).obj X
  let aₖ : yoneda.obj Uₖ ⟶ Xₖ :=
    Udata.iso.hom ≫ (OverShriek.relocalizeRestrict g).map a
  let hXₖ := isAlgebraicSpace_relocalizeRestrict B
    (Spec (.of (IsLocalRing.ResidueField R))) (Spec (.of R)) hk hR g X hX
  have haₖEtale : MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of (IsLocalRing.ResidueField R))) hk))
      aₖ :=
    Udata.presheaf_property (@Etale.{u} : MorphismProperty Scheme.{u}) a haEtale
  have hredUₖ : IsReduced
      ((BigFppfOver.toScheme B
        (Spec (.of (IsLocalRing.ResidueField R))) hk).obj Uₖ) :=
    (exists_atlas_iff_forall_etale B (Spec (.of (IsLocalRing.ResidueField R))) hk Xₖ
      (fun T : Scheme.{u} => IsReduced T) hXₖ).mp hspecial Uₖ aₖ haₖEtale
  let T := BigFppfOver.toScheme B (Spec (.of R)) hR
  let Uₛ := T.obj U
  let fU := B.inclusion.map U.hom
  have hredFiber : IsReduced (fU.fiber
      (IsLocalRing.closedPoint (CommRingCat.of R))) := by
    have hpb : IsPullback (B.inclusion.map Udata.projection)
        (B.inclusion.map Udata.base.hom) fU
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := by
      simpa only [g, B.inclusion.map_preimage] using Udata.isPullback
    have : IsReduced (B.inclusion.obj Udata.base.left) := hredUₖ
    have : IsReduced (pullback fU
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :=
      isReduced_of_isOpenImmersion hpb.isoPullback.inv
    exact isReduced_fiber_closedPoint_of_isReduced_pullback_residue R Uₛ fU
  let base : BigFppfOver B (Spec (.of R)) hR := Over.mk (𝟙 (B.obj hR))
  let uToBase : U ⟶ base := Over.homMk U.hom
  have hbaseEtale : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T))
      (𝟙 (yoneda.obj base)) := by
    let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
    show (MorphismProperty.relative yoneda Q) _
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda (𝟙 _), ?_⟩
    intro A C q fst snd hpb
    have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
    let _ : IsIso (T.map snd) := Functor.map_isIso T snd
    exact (inferInstance : Etale (T.map snd))
  have hbaseTerminal : IsTerminal (yoneda.obj base) :=
    (Over.mkIdTerminal : IsTerminal base).isTerminalObj yoneda base
  have hchartMap : yoneda.map uToBase ≫ 𝟙 (yoneda.obj base) = a ≫ f :=
    hbaseTerminal.hom_ext _ _
  have hflatU : Flat fU :=
    hflat U base a (𝟙 _) uToBase haEtale hbaseEtale hchartMap
  have hlocalFTU : LocallyOfFiniteType fU :=
    hproper.2.1.1 U base a (𝟙 _) uToBase haEtale hbaseEtale hchartMap
  let _ : IsLocallyNoetherian (B.inclusion.obj (B.obj hR)) := by
    show IsLocallyNoetherian (Spec (.of R))
    infer_instance
  let _ : LocallyOfFiniteType fU := hlocalFTU
  let _ : IsLocallyNoetherian (B.inclusion.obj U.left) :=
    LocallyOfFiniteType.isLocallyNoetherian fU
  let _ : IsLocallyNoetherian Uₛ :=
    (inferInstance : IsLocallyNoetherian (B.inclusion.obj U.left))
  let _ : Flat fU := hflatU
  let _ : IsReduced (fU.fiber (IsLocalRing.closedPoint (CommRingCat.of R))) := hredFiber
  let W := reducedOpenLocus Uₛ
  let Wsite : B.Schemes :=
    ⟨W.toScheme, (Scheme.size_coe_opens_le _ W).trans_lt U.left.property⟩
  let j₀ : Wsite ⟶ U.left := ObjectProperty.homMk W.ι
  let V : BigFppfOver B (Spec (.of R)) hR := Over.mk (j₀ ≫ U.hom)
  let j : V ⟶ U := Over.homMk j₀
  have hVEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf (yoneda.map j ≫ a) :=
    etale_comp_of_scheme B (Spec (.of R)) hR j a (inferInstanceAs (Etale W.ι)) haEtale
  refine ⟨V, yoneda.map j ≫ a, ?_, hVEtale, isReduced_reducedOpenLocus Uₛ⟩
  apply (surjective_iff_surjective_pointsMap B (Spec (.of R)) hR X hX
    V (yoneda.map j ≫ a)).2
  let fpoints : points B (Spec (.of R)) hR X → Spec (.of R) :=
    pointsToScheme B (Spec (.of R)) hR base ∘
      pointsMap B (Spec (.of R)) hR X f
  apply surjective_of_closedMap_and_openMap fpoints
  · exact (isClosedMap_pointsToScheme B (Spec (.of R)) hR base).comp
      (isClosed_of_universallyClosed B (Spec (.of R)) hR
        (isAlgebraicSpace_yoneda B (Spec (.of R)) hR base) f hproper.2.2)
  · exact (pointTopologyFamily B (Spec (.of R)) hR).etale_isOpenMap
      hX V (yoneda.map j ≫ a) hVEtale
  · intro x hx
    obtain ⟨p, rfl⟩ :=
      (surjective_iff_surjective_pointsMap B (Spec (.of R)) hR X hX U a).1 haSurj x
    induction p using Quot.inductionOn with
    | h p =>
      have hpoint : fU (schemePoint B (Spec (.of R)) hR U p) =
          IsLocalRing.closedPoint (CommRingCat.of R) := by
        change pointsToScheme B (Spec (.of R)) hR base
          (pointsMap B (Spec (.of R)) hR X f
            (pointsMap B (Spec (.of R)) hR (yoneda.obj U) a
              (p.class B (Spec (.of R)) hR (yoneda.obj U)))) = _ at hx
        have hx' : pointsToScheme B (Spec (.of R)) hR base
            (pointsMap B (Spec (.of R)) hR (yoneda.obj U) (a ≫ f)
              (p.class B (Spec (.of R)) hR (yoneda.obj U))) =
            IsLocalRing.closedPoint (CommRingCat.of R) := by
          simpa only [pointsMap_comp, Function.comp_apply] using hx
        rw [← hchartMap, Category.comp_id] at hx'
        change (B.inclusion.map (p.value.left ≫ U.hom))
          (IsLocalRing.closedPoint p.carrier) = _ at hx'
        show (B.inclusion.map U.hom)
          ((B.inclusion.map p.value.left) (IsLocalRing.closedPoint p.carrier)) = _
        rw [B.inclusion.map_comp] at hx'
        exact hx'
      have hpW : schemePoint B (Spec (.of R)) hR U p ∈ W :=
        mem_reducedOpenLocus_of_reduced_stalk _
          (isReduced_stalk_of_closedPoint_of_flat fU _ hpoint)
      have : AlgebraicGeometry.IsOpenImmersion (T.map j) :=
        inferInstanceAs (AlgebraicGeometry.IsOpenImmersion W.ι)
      obtain ⟨q, hq⟩ := fieldPoint_factors_through_open B (Spec (.of R)) hR j p
        ⟨⟨_, hpW⟩, rfl⟩
      refine ⟨q.class B (Spec (.of R)) hR (yoneda.obj V), ?_⟩
      rw [pointsMap_comp, Function.comp_apply, hq]

/-- **Stacks 0E0B.** The generic fibre of a proper flat algebraic space over a discrete
valuation ring with reduced special fibre is reduced. -/
@[stacks 0E0B "generic fibre"]
public theorem isReduced_genericFiber_of_isReduced_specialFiber
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (B : BigFppfSite.{u})
    (hR : B.Contains (Spec (.of R)))
    (hk : B.Contains (Spec (.of (IsLocalRing.ResidueField R))))
    (hK : B.Contains (Spec (.of (FractionRing R))))
    (X : (BigFppfOver B (Spec (.of R)) hR)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of R)) hR X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hR))))
    (hproper : IsProper B (Spec (.of R)) hR f)
    (hflat : IsFlat B (Spec (.of R)) hR f)
    (hspecial :
      let g : B.obj hk ⟶ B.obj hR :=
        B.inclusion.preimage
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
      HasEtaleLocalProperty B
        (Spec (.of (IsLocalRing.ResidueField R))) hk
        ((OverShriek.relocalizeRestrict g).obj X)
        (fun T : Scheme.{u} => IsReduced T)) :
    let g : B.obj hK ⟶ B.obj hR :=
      B.inclusion.preimage
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    HasEtaleLocalProperty B (Spec (.of (FractionRing R))) hK
      ((OverShriek.relocalizeRestrict g).obj X)
      (fun T : Scheme.{u} => IsReduced T) := by
  classical
  intro g
  obtain ⟨U, a, haSurj, haEtale, hredU⟩ :=
    isReduced_of_isReduced_specialFiber R B hR hk X hX f hproper hflat hspecial
  let D := restrictedChart B (Spec (.of (FractionRing R))) (Spec (.of R)) hK hR g U
  let aK := D.iso.hom ≫ (OverShriek.relocalizeRestrict g).map a
  refine ⟨D.base, aK, ?_, ?_, ?_⟩
  · exact D.presheaf_property (@Surjective.{u}) a haSurj
  · exact D.presheaf_property (@Etale.{u}) a haEtale
  · have : IsReduced (B.inclusion.obj U.left) := hredU
    have hgen : AlgebraicGeometry.IsOpenImmersion (B.inclusion.map g) := by
      rw [show B.inclusion.map g = Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R))) from B.inclusion.map_preimage _]
      exact isOpenImmersion_specFractionRing R
    have : AlgebraicGeometry.IsOpenImmersion (B.inclusion.map D.projection) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback D.isPullback.flip hgen
    exact isReduced_of_isOpenImmersion (B.inclusion.map D.projection)

end AlgebraicGeometry.Space

end
