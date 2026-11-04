module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.OpenPieceDimension
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalCapRegularFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.ChowGroups
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.OpenImmersionRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.LocalEquation
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Triviality
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.DedekindBase
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
import all StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exterior product over a Dedekind base respects rational equivalence

Let `(S, δ)` be as in section 42.63 of the Stacks Project: `S` is locally Noetherian with an open
covering by spectra of Dedekind domains, and `δ(s) = 0` for `s` closed and `δ(s) = 1`
otherwise. For `X`, `Y` locally of finite type over `S` the exterior product of an `n`-cycle on
`X` and an `m`-cycle on `Y` is the `(n + m - 1)`-cycle on `X ×_S Y` given on integral closed
subschemes by `[X'] × [Y'] = [X' ×_S Y']_{n+m-1}` if `X'` or `Y'` dominates an irreducible
component of `S`, and by `0` otherwise (`Stacks.Chow.exteriorProductDedekindCycles`). Stacks 0FC4
asserts that it descends to a map

  `× : CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`.

This file proves that descent with no hypothesis beyond the shape of the base, and so obtains
the map.

## The argument

By the symmetry of the exterior product under `X ×_S Y ≅ Y ×_S X` it suffices to treat the second
variable. Fix `α` and let `β` be rationally equivalent to zero. The product `α × β` is the locally
finite sum over the points `x` of the support of `α` of its part `∑_y α(x) β(y) [x] × [y]`, and
each part is the pushforward from `closure {x} ×_S Y` of a cycle there; by Stacks 02RZ it is
enough that this cycle be rationally equivalent to zero on `closure {x} ×_S Y`.

* If `x` lies over the generic point of an irreducible component of `S`, then `closure {x}` is flat
  over `S` (Stacks 0AUW), of relative dimension `δ(x) - δ(f x)`: over a closed point every generic
  point of the fibre has codimension one in `closure {x}`, by the dimension formula for the flat
  local homomorphism to its local ring. The part at `x` is the flat pullback of `α(x) · β` along
  the projection `closure {x} ×_S Y ⟶ Y`, which preserves rational equivalence (Stacks 02S1).
* Otherwise `x` lies over a closed point `s` with a proper generalization. Near `s` there is a
  function `π` whose zero scheme is the reduced point `s`: a nonzero prime of a Dedekind domain
  becomes principal after inverting an element outside it. Over the open `Y_U` of `Y` where `π`
  is defined, the pulled-back function cuts out the fibre `D = Y_s`, an effective Cartier divisor
  with trivial normal bundle, and the Gysin map on cycles of Stacks 0B6Z sends the restriction of
  `β` to the cycle `∑_{Y' ⊄ D} β(Y') [Y' ∩ D]_{m-1}` on `D`; it preserves rational equivalence
  because it represents the Gysin map of Stacks 02TO. Finally `closure {x} ×_S Y` is the product
  `closure {x} ×_s D`, so its projection to `D` is flat of relative dimension `δ(x)`, and the flat
  pullback of that cycle along it is the part of `α × β` at `x`.

## Main definitions

* `Stacks.Chow.IsDedekindChowBase.exteriorProductChow` — **Stacks 0FC4**: the exterior product
  `CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)` over a Dedekind base.

## Main results

* `Stacks.Chow.IsDedekindChowBase.exteriorProductFactorsThroughRationalEquivalence` — **Stacks
  0FC4**: the exterior product of cycles is compatible with rational equivalence in each variable.
* `Stacks.Chow.IsDedekindChowBase.exteriorProductDedekindCycles_mem_rationalEquivalences_right`,
  `Stacks.Chow.IsDedekindChowBase.exteriorProductDedekindCycles_mem_rationalEquivalences_left` —
  the two variables separately.
* `Stacks.Chow.IsDedekindChowBase.flat_of_mem_genericPoints` — Stacks 0AUW over a Dedekind base:
  an integral scheme whose generic point lies over a generic point of the base is flat over it.
* `Stacks.Chow.IsDedekindChowBase.relativeDimension_integralComponentAt_comp` — such a point
  closure has relative dimension `δ(x) - δ(f x)` over the base.
* `Stacks.Chow.IsDedekindChowBase.exists_zeroScheme_unit_eq` — a closed point of a Dedekind base
  with a proper generalization is, near itself, the zero scheme of a function.
* `Stacks.Chow.exists_gysinCycle_mem_rationalEquivalences` — the Gysin map on cycles of a divisor
  with trivial normal bundle preserves rational equivalence, with its component formula.
* `Stacks.Chow.exteriorProductDedekindCycles_pullbackSymmetry` — the symmetry of the exterior
  product of cycles.

## Implementation notes

The source writes the cap products of the bivariant classes `c' = i_* ∘ (p')^*` and
`c' = i_* ∘ (p')^* ∘ c` and observes that capping with a bivariant class preserves rational
equivalence. Here those cap products are computed on cycles instead: for each point `x` of the
support of `α` the cycle on `closure {x} ×_S Y` is written down explicitly, as a flat pullback in
the first case and as a flat pullback of the Gysin map on cycles of Stacks 0B6Z in the second, and
the infinitely many points `x` are assembled by Stacks 02RZ. The Gysin class of the closed point
is taken locally, where the closed point is the zero scheme of a function, since that is where its
normal bundle is visibly trivial; this changes nothing, because the part of `α × β` at `x` only
involves `Y` over a neighbourhood of `s`.

A field is a Dedekind domain, so the base may have zero-dimensional irreducible components. A
point `x` over such a component dominates it and falls under the first case; the relative
dimension of `closure {x}` is then `δ(x)`, one more than the degree `n + m - 1` requires, and the
part of `α × β` at `x` vanishes for dimension reasons.

## References

* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)

/-! ### Points of a base of dimension one -/

section Base

variable {C}

/-- Specialization of points of an affine open gives the inclusion of their prime ideals. -/
private theorem primeIdealOf_le_of_specializes {S : Scheme.{u}} {U : S.Opens}
    (hU : IsAffineOpen U) {p q : S} (hp : p ∈ (U : Set S)) (hq : q ∈ (U : Set S)) (hpq : p ⤳ q) :
    hU.primeIdealOf ⟨p, hp⟩ ≤ hU.primeIdealOf ⟨q, hq⟩ := by
  have h' : (⟨p, hp⟩ : U) ⤳ ⟨q, hq⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hpq
  exact (PrimeSpectrum.le_iff_specializes _ _).mpr (h'.map hU.isoSpec.hom.continuous)

/-- Points of an affine open with the same prime ideal are equal. -/
private theorem eq_of_primeIdealOf_eq {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)
    {p q : S} (hp : p ∈ (U : Set S)) (hq : q ∈ (U : Set S))
    (h : hU.primeIdealOf ⟨p, hp⟩ = hU.primeIdealOf ⟨q, hq⟩) : p = q := by
  have h1 := hU.fromSpec_primeIdealOf ⟨p, hp⟩
  have h2 := hU.fromSpec_primeIdealOf ⟨q, hq⟩
  rw [h] at h1
  exact h1.symm.trans h2

/-- **A Dedekind base has no chains of specializations of length two.** If `a ⤳ b ⤳ c` with
`a ≠ b`, then `b = c`: in an affine open around `c` whose ring of sections is a Dedekind domain,
the prime of `b` contains the prime of `a` properly, so it is nonzero and hence maximal. -/
theorem IsDedekindChowBase.eq_of_specializes (hS : IsDedekindChowBase C) {a b c : C.S}
    (hab : a ⤳ b) (hbc : b ⤳ c) (hne : a ≠ b) : b = c := by
  obtain ⟨U, hcU, hU, hded⟩ := hS.1 c
  have hbU : b ∈ (U : Set C.S) := hbc.mem_open U.isOpen hcU
  have haU : a ∈ (U : Set C.S) := hab.mem_open U.isOpen hbU
  have hab' := primeIdealOf_le_of_specializes hU haU hbU hab
  have hbc' := primeIdealOf_le_of_specializes hU hbU hcU hbc
  have hlt : (hU.primeIdealOf ⟨a, haU⟩).asIdeal < (hU.primeIdealOf ⟨b, hbU⟩).asIdeal :=
    lt_of_le_of_ne hab' fun h ↦ hne (eq_of_primeIdealOf_eq hU haU hbU (PrimeSpectrum.ext h))
  have hbot : (hU.primeIdealOf ⟨b, hbU⟩).asIdeal ≠ ⊥ := ne_bot_of_gt hlt
  have hmax : (hU.primeIdealOf ⟨b, hbU⟩).asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hbot (hU.primeIdealOf ⟨b, hbU⟩).isPrime
  exact eq_of_primeIdealOf_eq hU hbU hcU (PrimeSpectrum.ext
    (hmax.eq_of_le (hU.primeIdealOf ⟨c, hcU⟩).isPrime.ne_top hbc'))

/-- A point of a Dedekind base with a proper generalization is closed. -/
theorem IsDedekindChowBase.isClosed_singleton_of_specializes (hS : IsDedekindChowBase C)
    {t s : C.S} (hts : t ⤳ s) (hne : t ≠ s) : IsClosed ({s} : Set C.S) :=
  closure_subset_iff_isClosed.mp fun _ hc ↦
    (hS.eq_of_specializes hts (specializes_iff_mem_closure.mpr hc) hne).symm

/-- A proper generalization of a point of a Dedekind base is the generic point of an irreducible
component. -/
theorem IsDedekindChowBase.mem_genericPoints_of_specializes (hS : IsDedekindChowBase C)
    {t s : C.S} (hts : t ⤳ s) (hne : t ≠ s) : t ∈ genericPoints C.S := by
  rw [mem_genericPoints_iff_forall_specializes_eq]
  intro y hyt
  by_contra hyne
  exact hne (hS.eq_of_specializes hyt hts hyne)

/-- A point of a Dedekind base which is not the generic point of an irreducible component is a
closed point with a proper generalization, namely the generic point of a component through it. -/
theorem IsDedekindChowBase.exists_specializes_of_notMem_genericPoints (hS : IsDedekindChowBase C)
    {s : C.S} (hs : s ∉ genericPoints C.S) :
    IsClosed ({s} : Set C.S) ∧ ∃ t : C.S, t ⤳ s ∧ t ≠ s := by
  rw [mem_genericPoints_iff_forall_specializes_eq] at hs
  push Not at hs
  obtain ⟨t, hts, hne⟩ := hs
  exact ⟨hS.isClosed_singleton_of_specializes hts hne, t, hts, hne⟩

/-- A point of a Dedekind base with a proper generalization has coheight one. -/
theorem IsDedekindChowBase.coheight_eq_one_of_specializes (hS : IsDedekindChowBase C)
    {t s : C.S} (hts : t ⤳ s) (hne : t ≠ s) : Order.coheight s = 1 := by
  refine le_antisymm ?_ ?_
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Order.coheight_le_coe_iff]
    intro y hy
    have hys : y ⤳ s := Scheme.le_iff_specializes.mp hy.le
    have hne' : y ≠ s := fun h ↦ hy.ne h.symm
    rw [Order.coheight_eq_zero.mpr
      (isMax_of_mem_genericPoints ⟨y, hS.mem_genericPoints_of_specializes hys hne'⟩)]
    exact zero_lt_one
  · refine Order.one_le_iff_ne_zero.mpr (Order.coheight_ne_zero.mpr fun hmax ↦ hne ?_)
    have := hmax (Scheme.le_iff_specializes.mpr hts)
    exact ((Scheme.le_iff_specializes.mp this).antisymm hts).eq.symm

end Base

/-! ### A local equation of a closed point of a Dedekind base -/

/-- **A nonzero prime of a Dedekind domain is principal away from a suitable element outside
it.** For `π ∈ P \ P²` the principal ideal `(π)` factors as `P · J` with `J ⊄ P`, and inverting an
element `τ ∈ J \ P` makes `J` the unit ideal, so that `(π) = P` after inverting `τ`. -/
theorem _root_.Ideal.exists_span_singleton_eq_map_of_isDedekindDomain {A : Type u} [CommRing A]
    [IsDedekindDomain A] (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ π τ : A, π ∈ P ∧ τ ∉ P ∧ ∀ (R : Type u) [CommRing R] [Algebra A R]
      [IsLocalization.Away τ R], Ideal.span {algebraMap A R π} = P.map (algebraMap A R) := by
  have hlt : P ^ 2 < P := by
    refine lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) fun h ↦ ?_
    have h1 : P * P = P * 1 := by rw [← pow_two, h, mul_one]
    have h2 := mul_left_cancel₀ hP h1
    exact (Ideal.IsPrime.ne_top ‹_›) (by rw [h2, Ideal.one_eq_top])
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  obtain ⟨J, hJ⟩ : P ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hπP)
  have hJP : ¬ J ≤ P := by
    intro hJP
    refine hπ2 ?_
    rw [pow_two]
    exact (Ideal.span_singleton_le_iff_mem _).mp (hJ ▸ Ideal.mul_mono_right hJP)
  obtain ⟨τ, hτJ, hτP⟩ := SetLike.not_le_iff_exists.mp hJP
  refine ⟨π, τ, hπP, hτP, fun R _ _ _ ↦ ?_⟩
  have hJR : J.map (algebraMap A R) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hτJ)
      (IsLocalization.Away.algebraMap_isUnit τ)
  have hspan : Ideal.span {algebraMap A R π} = (Ideal.span {π}).map (algebraMap A R) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan, hJ, Ideal.map_mul, hJR, Ideal.mul_top]

/-- A closed point of a scheme stays closed in any open neighbourhood. -/
private theorem isClosed_singleton_opens_mk {S : Scheme.{u}} (U : S.Opens) {s : S} (hsU : s ∈ U)
    (h : IsClosed ({s} : Set S)) :
    IsClosed ({(⟨s, hsU⟩ : (U : Scheme.{u}))} : Set (U : Scheme.{u})) := by
  have h1 : (U.ι.base ⁻¹' {s} : Set (U : Scheme.{u})) = {⟨s, hsU⟩} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ U.ι.isOpenEmbedding.injective h, fun h ↦ h ▸ rfl⟩
  exact h1 ▸ h.preimage U.ι.continuous

variable {C} in
/-- **A closed point of a Dedekind base is locally the zero scheme of a function.** If `s` is a
closed point of a Dedekind base with a proper generalization, there is an open neighbourhood `U`
of `s` and a function `π` on `U` whose zero scheme is the reduced point `s`: in an affine chart
whose ring is a Dedekind domain `A`, `s` is a nonzero prime `P`, and
`Ideal.exists_span_singleton_eq_map_of_isDedekindDomain` makes `P` principal on a basic open. -/
theorem IsDedekindChowBase.exists_zeroScheme_unit_eq (hS : IsDedekindChowBase C) {t s : C.S}
    (hts : t ⤳ s) (hne : t ≠ s) :
    ∃ (U : C.S.Opens) (hsU : s ∈ U) (π : Γ((U : Scheme.{u}), ⊤)),
      Stacks.Divisors.zeroScheme (U : Scheme.{u})
          (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π =
        integralComponentAt (⟨s, hsU⟩ : (U : Scheme.{u})) := by
  obtain ⟨U₀, hsU₀, hU₀, hded⟩ := hS.1 s
  have htU₀ : t ∈ (U₀ : Set C.S) := hts.mem_open U₀.isOpen hsU₀
  set P := hU₀.primeIdealOf ⟨s, hsU₀⟩ with hPdef
  have hP : P.asIdeal ≠ ⊥ := by
    have hle := primeIdealOf_le_of_specializes hU₀ htU₀ hsU₀ hts
    exact ne_bot_of_gt (lt_of_le_of_ne hle fun h ↦
      hne (eq_of_primeIdealOf_eq hU₀ htU₀ hsU₀ (PrimeSpectrum.ext h)))
  obtain ⟨π₀, τ, hπ₀, hτ, hloc⟩ := Ideal.exists_span_singleton_eq_map_of_isDedekindDomain
    P.asIdeal hP
  set U : C.S.Opens := C.S.basicOpen τ with hUdef
  have hsU : s ∈ U := by
    have h1 : P ∈ (PrimeSpectrum.basicOpen τ : Set (PrimeSpectrum Γ(C.S, U₀))) := hτ
    rw [← hU₀.fromSpec_preimage_basicOpen] at h1
    have h2 : hU₀.fromSpec P = s := hU₀.fromSpec_primeIdealOf ⟨s, hsU₀⟩
    rw [← h2]
    exact h1
  set s' : (U : Scheme.{u}) := ⟨s, hsU⟩ with hs'
  have _ : IsAffine (U : Scheme.{u}) := hU₀.basicOpen τ
  have hUU₀ : U.ι ''ᵁ ⊤ ≤ U₀ := by
    rw [Scheme.Opens.ι_image_top]
    exact C.S.basicOpen_le τ
  let : Algebra Γ(C.S, U₀) Γ((U : Scheme.{u}), ⊤) :=
    (C.S.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  have hlocU : IsLocalization.Away τ Γ((U : Scheme.{u}), ⊤) :=
    hU₀.isLocalization_of_eq_basicOpen τ (homOfLE hUU₀) (Scheme.Opens.ι_image_top U)
  set Ptop := (isAffineOpen_top (U : Scheme.{u})).primeIdealOf ⟨s', trivial⟩ with hPtop
  have hcomap : Ptop.asIdeal.comap (algebraMap Γ(C.S, U₀) Γ((U : Scheme.{u}), ⊤)) = P.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := U.ι) U₀ hU₀ ⊤ (isAffineOpen_top _)
      (fun z _ ↦ C.S.basicOpen_le τ z.2) (x := s') trivial
    have happ : U.ι.appLE U₀ ⊤ (fun z _ ↦ C.S.basicOpen_le τ z.2) =
        C.S.presheaf.map (homOfLE hUU₀).op := Scheme.Opens.ι_appLE U _ _ _
    rw [happ] at h
    exact congrArg PrimeSpectrum.asIdeal h
  have hspan : Ideal.span {algebraMap Γ(C.S, U₀) Γ((U : Scheme.{u}), ⊤) π₀} = Ptop.asIdeal := by
    rw [hloc, ← hcomap]
    exact IsLocalization.map_under (Submonoid.powers τ) _ Ptop.asIdeal
  refine ⟨U, hsU, algebraMap Γ(C.S, U₀) Γ((U : Scheme.{u}), ⊤) π₀, ?_⟩
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  have hclosed : IsClosed ({s'} : Set (U : Scheme.{u})) :=
    isClosed_singleton_opens_mk U hsU (hS.isClosed_singleton_of_specializes hts hne)
  have hpre : (isAffineOpen_top (U : Scheme.{u})).fromSpec ⁻¹'
      (Closeds.closure ({s'} : Set (U : Scheme.{u})) : Set (U : Scheme.{u})) = {Ptop} := by
    rw [Closeds.coe_closure, hclosed.closure_eq]
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun h ↦ (isAffineOpen_top (U : Scheme.{u})).fromSpec.isOpenEmbedding.injective ?_,
      fun h ↦ h ▸ (isAffineOpen_top (U : Scheme.{u})).fromSpec_primeIdealOf ⟨s', trivial⟩⟩
    rw [h, hPtop, (isAffineOpen_top (U : Scheme.{u})).fromSpec_primeIdealOf ⟨s', trivial⟩]
  have hmem : (⊤ : (U : Scheme.{u}).Opens) ∈ (U : Scheme.{u}).affineOpens :=
    isAffineOpen_top (U : Scheme.{u})
  let : Module Γ((U : Scheme.{u}), (⟨⊤, hmem⟩ : (U : Scheme.{u}).affineOpens).1)
      Γ(SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf,
        (⟨⊤, hmem⟩ : (U : Scheme.{u}).affineOpens).1) :=
    ((SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).val.obj (.op ⊤)).isModule
  have key := Stacks.Divisors.zeroScheme_ideal_of_trivialization (U : Scheme.{u})
    (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)
    (algebraMap Γ(C.S, U₀) Γ((U : Scheme.{u}), ⊤) π₀) ⟨⊤, hmem⟩
    { toFun := fun a ↦ a, invFun := fun a ↦ a, map_add' := fun _ _ ↦ rfl,
      map_smul' := fun _ _ ↦ rfl, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
    (algebraMap Γ(C.S, U₀) Γ((U : Scheme.{u}), ⊤) π₀) (by simp; rfl)
  refine key.trans ?_
  rw [show integralComponentAt s' = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({s'} : Set (U : Scheme.{u}))) from rfl,
    Scheme.IdealSheafData.vanishingIdeal_ideal]
  have hpre' : ((isAffineOpen_top (U : Scheme.{u})).fromSpec.base ⁻¹'
      (Closeds.closure ({s'} : Set (U : Scheme.{u})) : Set (U : Scheme.{u})) :
        Set (PrimeSpectrum Γ((U : Scheme.{u}), ⊤))) = {Ptop} := hpre
  show _ = PrimeSpectrum.vanishingIdeal ((isAffineOpen_top (U : Scheme.{u})).fromSpec.base ⁻¹'
    (Closeds.closure ({s'} : Set (U : Scheme.{u})) : Set (U : Scheme.{u})))
  rw [hpre', PrimeSpectrum.vanishingIdeal_singleton, hspan]

/-! ### Relative dimension of a flat morphism out of an integral scheme -/

/-- **The relative dimension of a flat morphism out of an integral scheme.** Let `q : X' ⟶ B` be
flat and locally of finite type over the base, with `X'` integral, and suppose that at every
point `w` of `X'` the coheight of `q w` in `B` plus `r` is the drop of the delta-dimension from the
generic point of `X'` to `q w`. Then every nonempty fibre of `q` is equidimensional of
dimension `r`.

At `w` the dimension formula for the flat local homomorphism `𝒪_{B, q w} ⟶ 𝒪_{X', w}` computes
the dimension of the local ring of the fibre as `codim(w) - codim(q w)`, the codimension of `w` in
the integral scheme `X'` is the drop of the delta-dimension, and that drop is the drop at `q w`
plus the transcendence degree of `κ(w)` over `κ(q w)`; the dimension of the fibre at `w` is the
dimension of its local ring plus that transcendence degree (Stacks 02FX), which is therefore
`r`. -/
theorem relativeDimension_of_flat_of_coheight {X' B : Scheme.{u}} [IsIntegral X'] (q : X' ⟶ B)
    [LocallyOfFiniteType q] [Flat q] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (r : ℕ)
    (h : ∀ w : X', Order.coheight (q.base w) + r =
      ((relativeDimension C.dimensionFunction (q ≫ sB) (genericPoint X') -
        relativeDimension C.dimensionFunction sB (q.base w)).toNat : ℕ∞)) :
    AlgebraicGeometry.RelativeDimension q r := by
  have _ : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian sB
  have _ : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sB)
  have hgen : ∀ W : irreducibleComponents X', relativeDimension C.dimensionFunction (q ≫ sB)
      W.2.1.genericPoint = relativeDimension C.dimensionFunction (q ≫ sB) (genericPoint X') := by
    intro W
    have hW : (W : Set X') = Set.univ := by
      obtain ⟨W, hW⟩ := W
      exact (irreducibleComponents_eq_singleton (X := X') ▸ hW : W ∈ ({Set.univ} : Set (Set X')))
    have hη : IsGenericPoint W.2.1.genericPoint (Set.univ : Set X') := by
      rw [← hW]
      exact W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)
    rw [hη.eq (genericPoint_spec X')]
  have hloc : ∀ w : X', topologicalKrullDimAt (q.fiber (q.base w)) (q.asFiber w) =
      ((r : ℕ) : WithBot ℕ∞) := by
    intro w
    have hcoh := coheight_eq_toNat_sub_relativeDimension C (q ≫ sB) hgen w
    have hle := relativeDimension_le_of_forall_genericPoint C (q ≫ sB) hgen w
    have hδw := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sB q w
    have hflat := ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat q w
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at hflat
    have hfx := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg q w
    change topologicalKrullDimAt (q.fiber (q.base w)) (q.asFiber w) =
      ringKrullDim ((q.fiber (q.base w)).presheaf.stalk (q.asFiber w)) +
        (Cardinal.toENat (residueTrdeg q w) : WithBot ℕ∞) at hfx
    have htr : Cardinal.toENat (residueTrdeg q w) =
        ((Cardinal.toNat (residueTrdeg q w) : ℕ) : ℕ∞) :=
      Cardinal.toENat_eq_natCast.mpr (Cardinal.cast_toNat_of_lt_aleph0
        (residueTrdeg_lt_aleph0 q w)).symm
    have hw := h w
    obtain ⟨b, hb⟩ : ∃ b : ℕ, Order.coheight (q.base w) = (b : ℕ∞) := by
      refine ⟨(Order.coheight (q.base w)).toNat, (ENat.natCast_toNat fun htop ↦ ?_).symm⟩
      rw [htop, top_add] at hw
      exact ENat.top_ne_natCast _ hw
    rw [hb] at hw hflat
    have hbr : b + r = (relativeDimension C.dimensionFunction (q ≫ sB) (genericPoint X') -
        relativeDimension C.dimensionFunction sB (q.base w)).toNat := by exact_mod_cast hw
    rw [hcoh] at hflat
    rw [hfx, htr]
    generalize ringKrullDim ((q.fiber (q.base w)).presheaf.stalk (q.asFiber w)) = c at hflat ⊢
    induction c using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.add_bot] at hflat
      exact absurd hflat (WithBot.coe_ne_bot)
    | coe c₀ =>
      induction c₀ using ENat.recTopCoe with
      | top =>
        rw [← WithBot.coe_add, add_top] at hflat
        exact absurd (WithBot.coe_injective hflat) (ENat.natCast_ne_top _)
      | coe c' =>
        have h2 : (((relativeDimension C.dimensionFunction (q ≫ sB) (genericPoint X') -
            relativeDimension C.dimensionFunction (q ≫ sB) w).toNat : ℕ) : ℕ∞) =
            (b : ℕ∞) + (c' : ℕ∞) :=
          WithBot.coe_injective (by rwa [WithBot.coe_add])
        have h3 : (relativeDimension C.dimensionFunction (q ≫ sB) (genericPoint X') -
            relativeDimension C.dimensionFunction (q ≫ sB) w).toNat = b + c' := by
          exact_mod_cast h2
        have hca : c' + Cardinal.toNat (residueTrdeg q w) = r := by omega
        rw [← WithBot.coe_add, ← hca]
        push_cast
        rfl
  intro t ht
  have hFT : LocallyOfFiniteType (q.fiberToSpecResidueField t) := by
    show LocallyOfFiniteType (pullback.snd q (B.fromSpecResidueField t))
    infer_instance
  have hlocal : ∀ w : q.fiber t,
      topologicalKrullDimAt (q.fiber t) w = ((r : ℕ) : WithBot ℕ∞) := by
    intro w
    rw [← Scheme.Hom.topologicalKrullDimAt_fiber_fiberι q t w]
    exact hloc _
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (B.residueField t) (q.fiber t)
    (q.fiberToSpecResidueField t) hlocal, ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  have hloc' : ∀ w : q.fiber t, localKrullDim (q.fiber t) w = ((r : ℕ) : WithBot ℕ∞) := by
    intro w
    rw [← topologicalKrullDimAt_eq_localKrullDim]
    exact hlocal w
  simp_rw [hloc']
  have : Nonempty (q.fiber t) := ht
  exact iSup_const

/-- A point of the reduced closure of `x`, viewed in `X`, lies in the closure of `x`. -/
private theorem subschemeι_base_mem_closure_integralComponentAt {X : Scheme.{u}} (x : X)
    (w : (integralComponentAt x).subscheme) :
    (integralComponentAt x).subschemeι.base w ∈ closure ({x} : Set X) := by
  rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨w, rfl⟩

/-! ### Integral schemes dominating a component of a Dedekind base -/

section Dominating

variable {C}

/-- **Stacks 0AUW, globalized.** An integral scheme over a Dedekind base whose generic point lies
over the generic point of an irreducible component of the base is flat over the base: over an
affine open whose ring of sections is a Dedekind domain the generic point lies over the generic
point, which is `AlgebraicGeometry.flat_of_genericPoint_map_eq`. -/
theorem IsDedekindChowBase.flat_of_mem_genericPoints (hS : IsDedekindChowBase C) {Z : Scheme.{u}}
    [IsIntegral Z] (p : Z ⟶ C.S) (hp : p.base (genericPoint Z) ∈ genericPoints C.S) :
    Flat p := by
  let : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @Flat (Q := RingHom.Flat)
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @Flat) (f := p) fun t ↦ ?_
  obtain ⟨U, htU, hU, hded⟩ := hS.1 t
  refine ⟨U, htU, ?_⟩
  by_cases hne : Nonempty (p ⁻¹ᵁ U)
  · have _ : Nonempty U := ⟨⟨t, htU⟩⟩
    have _ : IsIntegral (U : Scheme.{u}) := isIntegral_of_isOpenImmersion hU.isoSpec.hom
    have hU' : U.ι.base ((p ∣_ U).base (genericPoint (p ⁻¹ᵁ U))) = p.base (genericPoint Z) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
        genericPoint_eq_of_isOpenImmersion (p ⁻¹ᵁ U).ι]
    have hgenU : (p ∣_ U).base (genericPoint (p ⁻¹ᵁ U)) = genericPoint (U : Scheme.{u}) := by
      have hspec : genericPoint (U : Scheme.{u}) ⤳ (p ∣_ U).base (genericPoint (p ⁻¹ᵁ U)) :=
        (genericPoint_spec (U : Scheme.{u})).specializes (Set.mem_univ _)
      have h2 := hspec.map U.ι.continuous
      rw [hU'] at h2
      rw [mem_genericPoints_iff_forall_specializes_eq] at hp
      have h3 := hp _ h2
      rw [← hU'] at h3
      exact (U.ι.isOpenEmbedding.injective h3).symm
    let q : (p ⁻¹ᵁ U : Scheme.{u}) ⟶ Spec (.of Γ(C.S, U)) := (p ∣_ U) ≫ hU.isoSpec.hom
    have hq : Flat q := by
      refine flat_of_genericPoint_map_eq (A := Γ(C.S, U)) q ?_
      show hU.isoSpec.hom.base ((p ∣_ U).base (genericPoint (p ⁻¹ᵁ U))) = _
      rw [hgenU]
      exact genericPoint_eq_of_isOpenImmersion hU.isoSpec.hom
    rw [show p ∣_ U = q ≫ hU.isoSpec.inv by simp [q]]
    infer_instance
  · rw [Flat.iff_flat_stalkMap]
    exact fun w ↦ absurd ⟨w⟩ hne

/-- **The relative dimension of a point closure dominating a component of a Dedekind base.** If
the generic point of the reduced closure of `x : X` lies over the generic point of an irreducible
component of the base, then `closure {x} ⟶ S` is flat of relative dimension `δ(x) - δ(f x)`: over
the generic point the fibre is irreducible with generic point `x`, and over a closed point every
generic point of the fibre has codimension one in `closure {x}`, by the dimension formula for the
flat local homomorphism to its local ring. -/
@[ega "IV 12.2.1.1" "partial"]
theorem IsDedekindChowBase.relativeDimension_integralComponentAt_comp (hS : IsDedekindChowBase C)
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (x : X)
    (hx : f.base x ∈ genericPoints C.S) [Flat ((integralComponentAt x).subschemeι ≫ f)] :
    AlgebraicGeometry.RelativeDimension ((integralComponentAt x).subschemeι ≫ f)
      (relativeDimension C.dimensionFunction f x - C.dimensionFunction (f.base x)).toNat := by
  have _ := isIntegral_integralComponentAt x
  have hδx : C.dimensionFunction (f.base x) ≤ relativeDimension C.dimensionFunction f x := by
    show _ ≤ C.dimensionFunction (f.base x) + (Cardinal.toNat (residueTrdeg f x) : ℤ)
    omega
  refine relativeDimension_of_flat_of_coheight C ((integralComponentAt x).subschemeι ≫ f)
    (𝟙 C.S) _ fun w ↦ ?_
  rw [Category.comp_id, relativeDimension_comp_closedImmersion,
    subschemeι_genericPoint_integralComponentAt x, relativeDimension_id]
  have hspec : f.base x ⤳ ((integralComponentAt x).subschemeι ≫ f).base w := by
    rw [Scheme.Hom.comp_apply]
    exact (specializes_iff_mem_closure.mpr
      (subschemeι_base_mem_closure_integralComponentAt x w)).map f.continuous
  by_cases heq : f.base x = ((integralComponentAt x).subschemeι ≫ f).base w
  · rw [← heq, Order.coheight_eq_zero.mpr (isMax_of_mem_genericPoints ⟨_, hx⟩), zero_add]
  · rw [hS.coheight_eq_one_of_specializes hspec heq,
      hS.2.1 _ (hS.isClosed_singleton_of_specializes hspec heq)]
    have hnc : ¬ IsClosed ({f.base x} : Set C.S) := fun hc ↦ heq (hspec.mem_closed hc rfl).symm
    rw [hS.2.2 _ hnc] at hδx ⊢
    have h1 : (relativeDimension C.dimensionFunction f x - 1).toNat + 1 =
        (relativeDimension C.dimensionFunction f x - 0).toNat := by omega
    rw [add_comm]
    exact_mod_cast h1

end Dominating

/-! ### Multiplicities of inverse images of point closures -/

section Multiplicity

variable {E F : Scheme.{u}} (sE : E ⟶ C.S) [LocallyOfFiniteType sE] (sF : F ⟶ C.S)
  [LocallyOfFiniteType sF] (v : E ⟶ F) [LocallyOfFiniteType v] [Flat v]

include sF in
/-- Along a flat morphism `v : E ⟶ F`, the inverse image of the reduced closure of a point `y`
of `F` has multiplicity zero at every point of `E` not lying over `y`: a generic point of that
inverse image lies over `y`, generalizations lifting along a flat morphism. -/
theorem closedSubschemeCycleCoeff_comap_integralComponentAt_eq_zero_of_ne (y : F) (j : ℤ) {w : E}
    (hw : v.base w ≠ y) :
    closedSubschemeCycleCoeff C sE ((integralComponentAt y).comap v).subschemeι j w = 0 := by
  have _ := isIntegral_integralComponentAt y
  rw [closedSubschemeCycleCoeff_eq_of_iso C sE ((integralComponentAt y).comap v).subschemeι
    (pullback.fst v (integralComponentAt y).subschemeι) ((integralComponentAt y).comapIso v)
    ((integralComponentAt y).comapIso_hom_fst v) j w]
  refine closedSubschemeCycleCoeff_pullbackFst_eq_zero C sE sF v _ j w ?_
  rwa [subschemeι_genericPoint_integralComponentAt]

/-- Along a flat morphism `v : E ⟶ F` of relative dimension `r` over the base, the inverse image
of the reduced closure of a point `y` of `F` has nonzero multiplicity only in delta-dimension
`δ(y) + r`: every irreducible component of the inverse image lies over the closure of `y` with
fibres of dimension `r` (Stacks 02R8). -/
theorem eq_of_closedSubschemeCycleCoeff_comap_integralComponentAt_ne_zero
    (hbase : v ≫ sF = sE) (r : ℕ) (hv : AlgebraicGeometry.RelativeDimension v r) (y : F)
    (j : ℤ) {w : E}
    (hw : closedSubschemeCycleCoeff C sE ((integralComponentAt y).comap v).subschemeι j w ≠ 0) :
    j = relativeDimension C.dimensionFunction sF y + (r : ℤ) := by
  classical
  have _ := isIntegral_integralComponentAt y
  set I := integralComponentAt y with hI
  unfold closedSubschemeCycleCoeff at hw
  split at hw
  · rename_i h
    obtain ⟨ξ, hξ, hj⟩ := h
    have _ := locallyOfFiniteType_comapRestrict I v
    have _ := flat_comapRestrict I v
    have hrel := relativeDimension_comapRestrict I v hv
    set W := genericPoints.component ξ with hW
    have hgen : W.2.1.genericPoint = ξ.1 :=
      (W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)).eq
        (genericPoints.isGenericPoint ξ)
    have hδ := relativeDimension_comp_eq_add_trdeg C.dimensionFunction (I.subschemeι ≫ sF)
      (comapRestrict I v) W.2.1.genericPoint
    rw [show comapRestrict I v ≫ I.subschemeι ≫ sF = (I.comap v).subschemeι ≫ sE by
        rw [← Category.assoc, comapRestrict_subschemeι, Category.assoc, hbase],
      toNat_residueTrdeg_genericPoint (comapRestrict I v) W r hrel,
      map_genericPoint_irreducibleComponent_eq_genericPoint (comapRestrict I v) W,
      relativeDimension_comp_closedImmersion, relativeDimension_comp_closedImmersion,
      subschemeι_genericPoint_integralComponentAt, hgen, hξ] at hδ
    rw [← hj, hδ]
  · exact absurd rfl hw

end Multiplicity

/-! ### The product of a point closure with the second factor -/

/-- The multiplicity of the product `closure {x} ×_S closure {y}` at a point of
`closure {x} ×_S Y`, read inside `closure {x} ×_S Y`, is the multiplicity there of the inverse
image of the reduced closure of `y` under the projection `closure {x} ×_S Y ⟶ Y`: the first of
the two ideal sheaves cutting out the product already vanishes on `closure {x} ×_S Y`. -/
theorem closedSubschemeCycleCoeff_exteriorProductIdeal_comap (x : X) (y : Y) (j : ℤ)
    (w : ((integralComponentAt x).comap (pullback.fst f g)).subscheme) :
    closedSubschemeCycleCoeff C (pullback.fst f g ≫ f) (exteriorProductIdeal f g x y).subschemeι j
        (((integralComponentAt x).comap (pullback.fst f g)).subschemeι.base w) =
      closedSubschemeCycleCoeff C
        (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫ (pullback.fst f g ≫ f))
        ((integralComponentAt y).comap
          (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
            pullback.snd f g)).subschemeι j w := by
  have hker : ((integralComponentAt x).comap (pullback.fst f g)).subschemeι.ker ≤
      exteriorProductIdeal f g x y := by
    rw [Scheme.IdealSheafData.ker_subschemeι, exteriorProductIdeal]
    exact le_sup_left
  have hkill : ((integralComponentAt x).comap (pullback.fst f g)).comap
      ((integralComponentAt x).comap (pullback.fst f g)).subschemeι = ⊥ := by
    have h := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
      ((integralComponentAt x).comap (pullback.fst f g)).subschemeι
      ((integralComponentAt x).comap (pullback.fst f g)).subschemeι
    rw [Scheme.IdealSheafData.ker_subschemeι] at h
    rw [← h, Scheme.Hom.ker_eq_bot_of_isIso]
  have hcomap : (exteriorProductIdeal f g x y).comap
      ((integralComponentAt x).comap (pullback.fst f g)).subschemeι =
      (integralComponentAt y).comap
        (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) := by
    rw [exteriorProductIdeal, Scheme.IdealSheafData.comap_sup]
    show ((integralComponentAt x).comap (pullback.fst f g)).comap
      ((integralComponentAt x).comap (pullback.fst f g)).subschemeι ⊔ _ = _
    rw [hkill, bot_sup_eq, ← Scheme.IdealSheafData.comap_comp]
    rfl
  rw [closedSubschemeCycleCoeff_comap_of_isClosedImmersion C (pullback.fst f g ≫ f)
    ((integralComponentAt x).comap (pullback.fst f g)).subschemeι _ hker j w, hcomap]

/-- **One summand of the exterior product.** Let `x` be a point of `X` and let
`v : closure {x} ×_S Y ⟶ E` be flat of relative dimension `r` over the base. If the part
`∑_y [x] × [y]` of `α × β` at `x`, read on `closure {x} ×_S Y`, is the flat pullback along `v`
of a cycle `γ` rationally equivalent to zero on `E`, then it is the pushforward of a cycle
rationally equivalent to zero on `closure {x} ×_S Y`. -/
theorem exists_exteriorProductDedekindSummand_of_flat (α : CycleGroup C f n)
    (β : CycleGroup C g m) (x : X) {E : Scheme.{u}} (sE : E ⟶ C.S) [LocallyOfFiniteType sE]
    (v : ((integralComponentAt x).comap (pullback.fst f g)).subscheme ⟶ E)
    [LocallyOfFiniteType v] [Flat v]
    (hbase : v ≫ sE =
      ((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫ (pullback.fst f g ≫ f))
    (r : ℕ) (hv : AlgebraicGeometry.RelativeDimension v r) (k : ℤ) (hk : k + r = n + m - 1)
    (γ : CycleGroup C sE k) (hγ : γ ∈ rationalEquivalences C sE k)
    (hcoeff : ∀ w : ((integralComponentAt x).comap (pullback.fst f g)).subscheme,
      ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β
          (((integralComponentAt x).comap (pullback.fst f g)).subschemeι.base w) (x, y) =
        γ.1 (v.base w) * flatPullbackWeight C
          (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
            (pullback.fst f g ≫ f)) v (k + r) w) :
    ∃ a : CycleGroup C
        (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫ (pullback.fst f g ≫ f))
        (n + m - 1),
      a ∈ rationalEquivalences C
          (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
            (pullback.fst f g ≫ f)) (n + m - 1) ∧
        ∀ z : (pullback f g : Scheme.{u}),
          (properPushforward C
            (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
              (pullback.fst f g ≫ f)) (pullback.fst f g ≫ f)
            ((integralComponentAt x).comap (pullback.fst f g)).subschemeι rfl (n + m - 1) a).1 z =
            ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y) := by
  refine ⟨hk ▸ flatPullback C _ sE v hbase r hv k γ,
    mem_rationalEquivalences_cast C _ hk
      (flatPullbackFactorsThroughRationalEquivalence_general C _ sE v hbase r hv k γ hγ),
    fun z ↦ ?_⟩
  by_cases hz : z ∈ Set.range ((integralComponentAt x).comap (pullback.fst f g)).subschemeι.base
  · obtain ⟨w, rfl⟩ := hz
    rw [properPushforward_apply_image_of_isClosedImmersion, val_cycleGroup_cast,
      flatPullback_apply, hcoeff]
  · rw [properPushforward_apply_of_notMem_range C _ (pullback.fst f g ≫ f)
      ((integralComponentAt x).comap (pullback.fst f g)).subschemeι rfl (n + m - 1) _ hz]
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun y ↦ ?_
    by_contra hne
    obtain ⟨h1, -⟩ := mem_closure_of_exteriorProductDedekindTerm_ne_zero C f g n m α β z (x, y) hne
    refine hz ?_
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    show (pullback.fst f g).base z ∈ ((integralComponentAt x).support : Set X)
    rw [coe_support_integralComponentAt]
    exact h1

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The product `closure {x} ×_S Y`, presented as the inverse image of the reduced closure of `x`
under the first projection, is a fibre product of the structure morphism of `closure {x}` with
`g`. -/
theorem isPullback_comap_integralComponentAt_fst (x : X) :
    IsPullback (comapRestrict (integralComponentAt x) (pullback.fst f g))
      (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt x).subschemeι ≫ f) g :=
  (isPullback_comapRestrict (integralComponentAt x) (pullback.fst f g)).flip.paste_vert
    (IsPullback.of_hasPullback f g)

/-- **The summand at a point whose closure is flat over the base.** Let `x` be a point of `X`
whose reduced closure dominates an irreducible component of the base and is flat of relative
dimension `r` over it. Then the part `∑_y [x] × [y]` of `α × β` at `x` is the pushforward of a
cycle on `closure {x} ×_S Y` which is rationally equivalent to zero whenever `β` is: the flat
pullback of `α(x) · β` along the flat projection `closure {x} ×_S Y ⟶ Y` when `m + r` is the
degree `n + m - 1`, and zero otherwise, every multiplicity of the product then vanishing for
dimension reasons. -/
theorem exists_exteriorProductDedekindSummand_of_dominates (α : CycleGroup C f n)
    {β : CycleGroup C g m} (hβ : β ∈ rationalEquivalences C g m) (x : X)
    (hdom : DominatesBaseComponent C f x) [Flat ((integralComponentAt x).subschemeι ≫ f)] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension ((integralComponentAt x).subschemeι ≫ f) r) :
    ∃ a : CycleGroup C
        (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫ (pullback.fst f g ≫ f))
        (n + m - 1),
      a ∈ rationalEquivalences C
          (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
            (pullback.fst f g ≫ f)) (n + m - 1) ∧
        ∀ z : (pullback f g : Scheme.{u}),
          (properPushforward C
            (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
              (pullback.fst f g ≫ f)) (pullback.fst f g ≫ f)
            ((integralComponentAt x).comap (pullback.fst f g)).subschemeι rfl (n + m - 1) a).1 z =
            ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y) := by
  classical
  set K : (pullback f g : Scheme.{u}).IdealSheafData :=
    (integralComponentAt x).comap (pullback.fst f g) with hK
  set v : K.subscheme ⟶ Y := K.subschemeι ≫ pullback.snd f g with hvdef
  have hpb := isPullback_comap_integralComponentAt_fst C f g x
  have _ : Flat v := MorphismProperty.of_isPullback hpb inferInstance
  have _ : LocallyOfFiniteType v := MorphismProperty.of_isPullback hpb inferInstance
  have hv : AlgebraicGeometry.RelativeDimension v r := RelativeDimension.of_isPullback hpb hr
  have hbase : v ≫ g = K.subschemeι ≫ (pullback.fst f g ≫ f) := by
    rw [hvdef, Category.assoc, ← pullback.condition]
  -- the part of `α × β` at `x`, read on `closure {x} ×_S Y`
  have hsum : ∀ w : K.subscheme,
      ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β (K.subschemeι.base w) (x, y) =
        α.1 x * β.1 (v.base w) * closedSubschemeCycleCoeff C (K.subschemeι ≫ (pullback.fst f g ≫ f))
          ((integralComponentAt (v.base w)).comap v).subschemeι (n + m - 1) w := by
    intro w
    have hterm : ∀ y : Y,
        exteriorProductDedekindTerm C f g n m α β (K.subschemeι.base w) (x, y) =
          α.1 x * β.1 y * closedSubschemeCycleCoeff C (K.subschemeι ≫ (pullback.fst f g ≫ f))
            ((integralComponentAt y).comap v).subschemeι (n + m - 1) w := by
      intro y
      rw [exteriorProductDedekindTerm, ite_eq_left (Or.inl hdom)]
      exact congrArg _ (closedSubschemeCycleCoeff_exteriorProductIdeal_comap C f g x y _ w)
    rw [finsum_eq_single _ (v.base w) fun y hy ↦ ?_, hterm]
    rw [hterm, closedSubschemeCycleCoeff_comap_integralComponentAt_eq_zero_of_ne C _ g v y _
      (Ne.symm hy), mul_zero]
  by_cases hk : m + r = n + m - 1
  · refine exists_exteriorProductDedekindSummand_of_flat C f g n m α β x g v hbase r hv m hk
      (α.1 x • β) ((rationalEquivalences C g m).zsmul_mem hβ (α.1 x)) fun w ↦ ?_
    rw [hsum, hk,
      show (α.1 x • β : CycleGroup C g m).1 (v.base w) = α.1 x * β.1 (v.base w) by simp]
    rfl
  · refine exists_exteriorProductDedekindSummand_of_flat C f g n m α β x g v hbase r hv
      (n + m - 1 - r) (by ring) 0 (rationalEquivalences C g _).zero_mem fun w ↦ ?_
    rw [hsum]
    by_cases hβw : β.1 (v.base w) = 0
    · simp [hβw]
    · have hcoeff : closedSubschemeCycleCoeff C (K.subschemeι ≫ (pullback.fst f g ≫ f))
          ((integralComponentAt (v.base w)).comap v).subschemeι (n + m - 1) w = 0 := by
        by_contra hne
        have hj := eq_of_closedSubschemeCycleCoeff_comap_integralComponentAt_ne_zero C _ g v
          hbase r hv _ _ hne
        rw [(mem_cyclesOfDimension_iff_forall_point C g m β.1).1 β.2 _ hβw] at hj
        exact hk hj.symm
      simp [hcoeff]

/-! ### The Gysin map of a divisor with trivial normal bundle -/

/-- **The Gysin map on cycles of a divisor with trivial normal bundle preserves rational
equivalence.** Let `D = Z(σ)` be the zero scheme of a section of an invertible module whose
restriction to `D` is trivial. For a `(k+1)`-cycle `δ` rationally equivalent to zero, the cycle
on `D` which on each component of `δ` not contained in `D` is the fundamental cycle of its
intersection with `D`, and on each component contained in `D` is zero, is rationally equivalent
to zero: it is the Gysin map on cycles of Stacks 0B6Z, which represents the Gysin map of
Stacks 02TO on Chow groups (`Stacks.Chow.gysinSystemOfInvertible_onChowEqGysinCycleMap`). -/
theorem exists_gysinCycle_mem_rationalEquivalences {T : Scheme.{u}} (p : T ⟶ C.S)
    [LocallyOfFiniteType p] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) {D : T.IdealSheafData} (hD : Stacks.Divisors.zeroScheme T L σ = D)
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L σ).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L σ).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L σ).subschemeι).obj L))
    (k : ℤ) (δ : CycleGroup C p (k + 1)) (hδ : δ ∈ rationalEquivalences C p (k + 1)) :
    ∃ γ : CycleGroup C (D.subschemeι ≫ p) k, γ ∈ rationalEquivalences C (D.subschemeι ≫ p) k ∧
      ∀ d : D.subscheme, γ.1 d = ∑ᶠ i : cycleSupportIndex δ, δ.1 i.1 *
        (open Classical in if D ≤ integralComponentAt i.1 then 0 else
          closedSubschemeCycleCoeff C (D.subschemeι ≫ p)
            ((integralComponentAt i.1).comap D.subschemeι).subschemeι k d) := by
  classical
  subst hD
  refine ⟨gysinCycleMap C p k L σ htriv δ, ?_, fun d ↦ ?_⟩
  · have h := gysinSystemOfInvertible_onChowEqGysinCycleMap C p L σ htriv k δ
    have h0 : QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) δ = 0 :=
      (QuotientAddGroup.eq_zero_iff δ).mpr hδ
    rw [h0, map_zero] at h
    exact (QuotientAddGroup.eq_zero_iff _).mp h.symm
  · show ((gysinCycleMapRule C p k L σ).extendCycleGroup δ).1 d = _
    rw [GysinChernCap.extendCycleGroup_eq_finsum_cycle]
    refine finsum_congr fun i ↦ ?_
    show (δ.1 i.1 • gysinCycleMapComponent C p k L σ _ (isIntegral_integralComponentAt i.1)
      (schemeDeltaDimension_cycleSupportIndex δ i)).1 d = _
    split_ifs with h
    · rw [gysinCycleMapComponent_of_le C p k L σ _ _ _ h]
      simp
    · rw [gysinCycleMapComponent_of_not_le C p k L σ _ _ _ h]
      rfl

/-! ### The summand at a point over a closed point of the base -/

variable {C} in
/-- **The summand at a point lying over a closed point of the base.** Let `x` be a point of `X`
whose image `s` in the base is not the generic point of an irreducible component, so that `s` is
a closed point with a proper generalization. Then the part `∑_y [x] × [y]` of `α × β` at `x` is
the pushforward of a cycle on `closure {x} ×_S Y` which is rationally equivalent to zero whenever
`β` is.

Near `s` the base has a function `π` whose zero scheme is the reduced point `s`
(`Stacks.Chow.IsDedekindChowBase.exists_zeroScheme_unit_eq`). On the open `Y_U` of `Y` over the
neighbourhood `U` of `s` where `π` is defined, the pulled-back function cuts out the fibre `D`
of `Y` over `s`, an effective Cartier divisor with trivial normal bundle; the Gysin map on cycles
sends the restriction of `β` to the cycle on `D` which is `[Y' ∩ D]` on the components `Y'` of
`β` not lying over `s` and zero on the others, and it preserves rational equivalence
(`Stacks.Chow.exists_gysinCycle_mem_rationalEquivalences`). Finally `closure {x} ×_S Y` is the
product `closure {x} ×_s D` over the residue field of `s`, so its projection to `D` is flat of
relative dimension `δ(x)`, and the flat pullback of that cycle along it is the part of `α × β`
at `x`: a component `Y'` of `β` dominating a component of the base contributes
`[closure {x} ×_S Y']`, and the other components contribute nothing, which is the defining rule
of the exterior product. -/
theorem IsDedekindChowBase.exists_exteriorProductDedekindSummand_of_notMem_genericPoints
    (hS : IsDedekindChowBase C) (α : CycleGroup C f n) {β : CycleGroup C g m}
    (hβ : β ∈ rationalEquivalences C g m) (x : X) (hx : α.1 x ≠ 0)
    (hgen : f.base x ∉ genericPoints C.S) :
    ∃ a : CycleGroup C
        (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫ (pullback.fst f g ≫ f))
        (n + m - 1),
      a ∈ rationalEquivalences C
          (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
            (pullback.fst f g ≫ f)) (n + m - 1) ∧
        ∀ z : (pullback f g : Scheme.{u}),
          (properPushforward C
            (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
              (pullback.fst f g ≫ f)) (pullback.fst f g ≫ f)
            ((integralComponentAt x).comap (pullback.fst f g)).subschemeι rfl (n + m - 1) a).1 z =
            ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y) := by
  classical
  obtain ⟨hclosed, t, hts, hne⟩ := hS.exists_specializes_of_notMem_genericPoints hgen
  obtain ⟨U, hsU, π, hπ⟩ := hS.exists_zeroScheme_unit_eq hts hne
  set s' : (U : Scheme.{u}) := ⟨f.base x, hsU⟩ with hs'
  have hs's : U.ι.base s' = f.base x := rfl
  set I : X.IdealSheafData := integralComponentAt x with hI
  set K : (pullback f g : Scheme.{u}).IdealSheafData := I.comap (pullback.fst f g) with hK
  set Dpt : (U : Scheme.{u}).IdealSheafData := integralComponentAt s' with hDpt
  have _ : IsIntegral I.subscheme := isIntegral_integralComponentAt x
  have _ : IsIntegral Dpt.subscheme := isIntegral_integralComponentAt s'
  -- the dimension of `x`
  have hδx : relativeDimension C.dimensionFunction f x = n :=
    (mem_cyclesOfDimension_iff_forall_point C f n α.1).1 α.2 x hx
  have hδs : C.dimensionFunction (f.base x) = 0 := hS.2.1 _ hclosed
  have hn : 0 ≤ n := by
    rw [← hδx]
    show 0 ≤ C.dimensionFunction (f.base x) + (Cardinal.toNat (residueTrdeg f x) : ℤ)
    omega
  -- the closure of `x` lies over the reduced point `s`
  have hrange : ∀ w : I.subscheme, (I.subschemeι ≫ f).base w = f.base x := by
    intro w
    have h1 := (specializes_iff_mem_closure.mpr
      (subschemeι_base_mem_closure_integralComponentAt x w)).map f.continuous
    rw [Scheme.Hom.comp_apply]
    exact h1.mem_closed hclosed rfl
  have hsub : Set.range (I.subschemeι ≫ f).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨w, rfl⟩
    exact ⟨s', hs's.trans (hrange w).symm⟩
  set c₀ : I.subscheme ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι (I.subschemeι ≫ f) hsub
    with hc₀
  have hc₀fac : c₀ ≫ U.ι = I.subschemeι ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hc₀pt : ∀ w, c₀.base w = s' := by
    intro w
    refine U.ι.isOpenEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, hc₀fac, hrange, hs's]
  have hker : Dpt.subschemeι.ker ≤ c₀.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    rw [← SetLike.coe_subset_coe, Closeds.coe_closure, Closeds.coe_closure]
    refine closure_mono ?_
    rintro _ ⟨w, rfl⟩
    exact hc₀pt w
  set c : I.subscheme ⟶ Dpt.subscheme := IsClosedImmersion.lift Dpt.subschemeι c₀ hker with hc
  have hcfac : c ≫ Dpt.subschemeι ≫ U.ι = I.subschemeι ≫ f := by
    rw [← Category.assoc, IsClosedImmersion.lift_fac, hc₀fac]
  have hcpt : ∀ w, Dpt.subschemeι.base (c.base w) = s' := by
    intro w
    rw [← Scheme.Hom.comp_apply, IsClosedImmersion.lift_fac, hc₀pt]
  -- the reduced point `s` is a single point
  have hs'closed : IsClosed ({s'} : Set (U : Scheme.{u})) :=
    isClosed_singleton_opens_mk U hsU hclosed
  have _ : Subsingleton Dpt.subscheme := by
    refine ⟨fun a b ↦ Dpt.subschemeι.isClosedEmbedding.injective ?_⟩
    have hmem : ∀ z : Dpt.subscheme, Dpt.subschemeι.base z = s' := by
      intro z
      have hz := subschemeι_base_mem_closure_integralComponentAt s' z
      rwa [hs'closed.closure_eq, Set.mem_singleton_iff] at hz
    rw [hmem a, hmem b]
  have _ : Flat c := inferInstance
  have _ : LocallyOfFiniteType (c ≫ Dpt.subschemeι ≫ U.ι) := by
    rw [hcfac]
    infer_instance
  have _ : LocallyOfFiniteType c := locallyOfFiniteType_of_comp c (Dpt.subschemeι ≫ U.ι)
  have hcrel : AlgebraicGeometry.RelativeDimension c n.toNat := by
    refine relativeDimension_of_flat_of_coheight C c (Dpt.subschemeι ≫ U.ι) n.toNat fun w ↦ ?_
    have hmax : Order.coheight (c.base w) = 0 :=
      Order.coheight_eq_zero.mpr fun b _ ↦ le_of_eq (Subsingleton.elim _ _)
    rw [hmax, zero_add, hcfac, relativeDimension_comp_closedImmersion,
      subschemeι_genericPoint_integralComponentAt, hδx, relativeDimension_comp_closedImmersion,
      ← Category.comp_id U.ι, relativeDimension_opensι_comp, relativeDimension_id, hcpt,
      hs's, hδs, sub_zero]
  -- the open `Y_U` of `Y` over `U`, the fibre `D` of `Y` over `s`, and the projection to `D`
  set T : Y.Opens := g ⁻¹ᵁ U with hT
  set Dbig : (T : Scheme.{u}).IdealSheafData := Dpt.comap (g ∣_ U) with hDbig
  have sq2 := isPullback_morphismRestrict g U
  have sq3 := isPullback_comapRestrict Dpt (g ∣_ U)
  have sq23 : IsPullback (comapRestrict Dpt (g ∣_ U)) (Dbig.subschemeι ≫ T.ι)
      (Dpt.subschemeι ≫ U.ι) g := sq3.flip.paste_vert sq2
  set r := comapRestrict I (pullback.fst f g) with hr
  set v : K.subscheme ⟶ Y := K.subschemeι ≫ pullback.snd f g with hv
  have hw : (r ≫ c) ≫ (Dpt.subschemeι ≫ U.ι) = v ≫ g := by
    rw [Category.assoc, hcfac, hr, comapRestrict_subschemeι_assoc, hv, Category.assoc,
      pullback.condition]
  set u : K.subscheme ⟶ Dbig.subscheme := sq23.lift (r ≫ c) v hw with hu
  have hu1 : u ≫ comapRestrict Dpt (g ∣_ U) = r ≫ c := sq23.lift_fst _ _ _
  have hu2 : u ≫ (Dbig.subschemeι ≫ T.ι) = v := sq23.lift_snd _ _ _
  have sq1 := isPullback_comap_integralComponentAt_fst C f g x
  have sq1' : IsPullback r u c (comapRestrict Dpt (g ∣_ U)) := by
    refine IsPullback.of_bot ?_ hu1.symm sq23
    rw [hu2, hcfac]
    exact sq1
  have _ : Flat u := MorphismProperty.of_isPullback sq1' inferInstance
  have _ : LocallyOfFiniteType u := MorphismProperty.of_isPullback sq1' inferInstance
  have hurel : AlgebraicGeometry.RelativeDimension u n.toNat :=
    RelativeDimension.of_isPullback sq1' hcrel
  have hbase : u ≫ (Dbig.subschemeι ≫ (T.ι ≫ g)) =
      K.subschemeι ≫ (pullback.fst f g ≫ f) := by
    rw [← Category.assoc Dbig.subschemeι, ← Category.assoc, hu2, hv, Category.assoc,
      ← pullback.condition]
  -- the Gysin map of the pulled-back function
  set LT : (T : Scheme.{u}).Modules :=
    (Scheme.Modules.pullback (g ∣_ U)).obj (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)
    with hLT
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible (T : Scheme.{u}).sheaf.obj
      (T : Scheme.{u}).ringCatSheaf.property LT :=
    Stacks.Divisors.pullback_isInvertible _ _
  set σ : Γ(LT, ⊤) := pullbackGlobalSections (g ∣_ U)
    (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π with hσ
  have hE : Stacks.Divisors.zeroScheme (T : Scheme.{u}) LT σ = Dbig :=
    (Stacks.Divisors.zeroScheme_pullback (g ∣_ U)
      (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π).trans
      (congrArg (fun J ↦ J.comap (g ∣_ U)) hπ)
  have htrivU : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme (U : Scheme.{u})
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (U : Scheme.{u})
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme (U : Scheme.{u})
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π).subschemeι).obj
          (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) :=
    ⟨Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso _⟩
  have htriv := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections (g ∣_ U)
    (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π htrivU
  have hdeg : m + ((0 : ℕ) : ℤ) = m - 1 + 1 := by push_cast; ring
  set δ₀ : CycleGroup C (T.ι ≫ g) (m - 1 + 1) :=
    hdeg ▸ flatPullback C (T.ι ≫ g) g T.ι rfl 0 (relativeDimension_opensι T) m β with hδ₀
  have hδ₀mem : δ₀ ∈ rationalEquivalences C (T.ι ≫ g) (m - 1 + 1) :=
    mem_rationalEquivalences_cast C _ hdeg
      (flatPullbackFactorsThroughRationalEquivalence_of_opensι C g T m β hβ)
  have hδ₀val : ∀ i : (T : Scheme.{u}), δ₀.1 i = β.1 (T.ι.base i) := by
    intro i
    rw [hδ₀, val_cycleGroup_cast, flatPullback_opensι, opensRestrictCycle_apply]
  obtain ⟨γ, hγ, hγval⟩ := exists_gysinCycle_mem_rationalEquivalences C (T.ι ≫ g) LT σ hE
    htriv (m - 1) δ₀ hδ₀mem
  refine exists_exteriorProductDedekindSummand_of_flat C f g n m α β x
    (Dbig.subschemeι ≫ (T.ι ≫ g)) u hbase n.toNat hurel (m - 1) (by omega) (α.1 x • γ)
    ((rationalEquivalences C _ _).zsmul_mem hγ (α.1 x)) fun w ↦ ?_
  -- the points of `D` are the points of `Y_U` over `s`
  have hDsupp : ∀ z : (T : Scheme.{u}),
      z ∈ (Dbig.support : Set (T : Scheme.{u})) ↔ g.base (T.ι.base z) = f.base x := by
    intro z
    rw [hDbig, coe_support_comap, Set.mem_preimage, coe_support_integralComponentAt,
      hs'closed.closure_eq, Set.mem_singleton_iff]
    have h1 : U.ι.base ((g ∣_ U).base z) = g.base (T.ι.base z) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    exact ⟨fun h ↦ by rw [← h1, h, hs's],
      fun h ↦ U.ι.isOpenEmbedding.injective (h1.trans (h.trans hs's.symm))⟩
  have huw : g.base (T.ι.base (Dbig.subschemeι.base (u.base w))) = f.base x := by
    rw [← hDsupp, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩
  have hvw : v.base w = T.ι.base (Dbig.subschemeι.base (u.base w)) := by
    rw [← hu2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  -- a component not lying over `s` meets `D` in delta-dimension at most `m - 1`
  have hZdim : ∀ i : cycleSupportIndex δ₀, ¬ Dbig ≤ integralComponentAt i.1 →
      schemeDeltaDimension C (((integralComponentAt i.1).comap Dbig.subschemeι).subschemeι ≫
        (Dbig.subschemeι ≫ (T.ι ≫ g))) ≤ ((m - 1 : ℤ) : EInt) := by
    intro i hi
    rw [le_integralComponentAt_iff_mem_support] at hi
    have hδi : relativeDimension C.dimensionFunction (T.ι ≫ g) i.1 = m - 1 + 1 :=
      (mem_cyclesOfDimension_iff_forall_point C _ _ δ₀.1).1 δ₀.2 i.1 i.2
    obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
      C.dimensionFunction (T.ι ≫ g)
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le C _ _ fun z ↦ ?_
    rw [relativeDimension_comp_closedImmersion]
    set q := Dbig.subschemeι.base
      (((integralComponentAt i.1).comap Dbig.subschemeι).subschemeι.base z) with hq
    have hqcl : q ∈ closure ({i.1} : Set (T : Scheme.{u})) := by
      have hz : ((integralComponentAt i.1).comap Dbig.subschemeι).subschemeι.base z ∈
          (((integralComponentAt i.1).comap Dbig.subschemeι).support : Set _) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨z, rfl⟩
      rwa [coe_support_comap, Set.mem_preimage, coe_support_integralComponentAt] at hz
    have hqD : q ∈ (Dbig.support : Set (T : Scheme.{u})) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩
    have hne' : i.1 ≠ q := fun h ↦ hi (h ▸ hqD)
    have hlt := d.strictAnti_specializes (specializes_iff_mem_closure.mpr hqcl) hne'
    rw [hd, hd, hδi] at hlt
    exact Int.le_sub_one_of_lt (by omega)
  -- the right-hand side as a sum over the components of the restriction of `β`
  set W := flatPullbackWeight C (K.subschemeι ≫ (pullback.fst f g ≫ f)) u (m - 1 + n.toNat) w
    with hW
  have hrhs : (α.1 x • γ).1 (u.base w) * W = ∑ᶠ i : cycleSupportIndex δ₀,
      α.1 x * δ₀.1 i.1 * (if Dbig ≤ integralComponentAt i.1 then 0 else
        closedSubschemeCycleCoeff C (K.subschemeι ≫ (pullback.fst f g ≫ f))
          (((integralComponentAt i.1).comap Dbig.subschemeι).comap u).subschemeι
          (m - 1 + n.toNat) w) := by
    rw [show (α.1 x • γ).1 (u.base w) = α.1 x * γ.1 (u.base w) by simp, hγval, mul_assoc,
      finsum_mul, mul_finsum]
    refine finsum_congr fun i ↦ ?_
    split_ifs with hle
    · ring
    · rw [closedSubschemeCycleCoeff_comap C _ _ u hbase n.toNat hurel _ (m - 1) (hZdim i hle) w]
      ring
  rw [hrhs]
  -- the left-hand side is a sum over the same components, read in `Y`
  set φ : cycleSupportIndex δ₀ → Y := fun i ↦ T.ι.base i.1 with hφ
  have hφinj : Function.Injective φ := fun a b h ↦ Subtype.ext (T.ι.isOpenEmbedding.injective h)
  have hsupp : Function.support (fun y : Y ↦
      exteriorProductDedekindTerm C f g n m α β (K.subschemeι.base w) (x, y)) ⊆ Set.range φ := by
    intro y hy
    have hy' : exteriorProductDedekindTerm C f g n m α β (K.subschemeι.base w) (x, y) ≠ 0 := hy
    obtain ⟨-, h2⟩ := mem_closure_of_exteriorProductDedekindTerm_ne_zero C f g n m α β _ (x, y) hy'
    have hβy : β.1 y ≠ 0 := by
      unfold exteriorProductDedekindTerm at hy'
      split_ifs at hy' with hdom
      · exact (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 hy').1).2
      · exact absurd rfl hy'
    have h3 : y ⤳ v.base w := by
      rw [hv, Scheme.Hom.comp_apply]
      exact specializes_iff_mem_closure.mpr h2
    have hyT : y ∈ (T : Set Y) := by
      refine h3.mem_open T.isOpen ?_
      rw [hvw]
      exact (Dbig.subschemeι.base (u.base w)).2
    obtain ⟨i₀, hi₀⟩ : y ∈ Set.range T.ι.base := by rwa [Scheme.Opens.range_ι]
    refine ⟨⟨i₀, ?_⟩, hi₀⟩
    rwa [hδ₀val, hi₀]
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq _ Set.univ (Set.range φ)
    (by rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp]), finsum_mem_range hφinj]
  refine finsum_congr fun i ↦ ?_
  show exteriorProductDedekindTerm C f g n m α β (K.subschemeι.base w) (x, T.ι.base i.1) = _
  unfold exteriorProductDedekindTerm
  dsimp only
  rw [← hδ₀val]
  by_cases hdg : DominatesBaseComponent C g (T.ι.base i.1)
  · have hle : ¬ Dbig ≤ integralComponentAt i.1 := by
      rw [le_integralComponentAt_iff_mem_support, hDsupp]
      exact fun h ↦ hgen (h ▸ hdg)
    have hideal : (integralComponentAt (T.ι.base i.1)).comap (K.subschemeι ≫ pullback.snd f g) =
        ((integralComponentAt i.1).comap Dbig.subschemeι).comap u := by
      rw [← Scheme.IdealSheafData.comap_comp,
        show K.subschemeι ≫ pullback.snd f g = (u ≫ Dbig.subschemeι) ≫ T.ι by
          rw [Category.assoc, hu2],
        Scheme.IdealSheafData.comap_comp, comap_integralComponentAt_of_isOpenImmersion]
    rw [ite_eq_left (Or.inr hdg), ite_eq_right hle,
      closedSubschemeCycleCoeff_exteriorProductIdeal_comap,
      show n + m - 1 = m - 1 + (n.toNat : ℤ) by omega, hideal]
  · have hgen' : ¬ DominatesBaseComponent C f x := hgen
    rw [ite_eq_right (not_or.mpr ⟨hgen', hdg⟩)]
    split_ifs with hle
    · simp
    · suffices h0 : closedSubschemeCycleCoeff C (K.subschemeι ≫ (pullback.fst f g ≫ f))
          (((integralComponentAt i.1).comap Dbig.subschemeι).comap u).subschemeι
          (m - 1 + n.toNat) w = 0 by rw [h0, mul_zero]
      by_contra hne'
      have hmem : w ∈ Set.range
          (((integralComponentAt i.1).comap Dbig.subschemeι).comap u).subschemeι.base :=
        support_cycleAssociatedToClosedSubscheme_subset C _ _ _ hne'
      rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap, Set.mem_preimage,
        coe_support_comap, Set.mem_preimage, coe_support_integralComponentAt] at hmem
      have h1 := (specializes_iff_mem_closure.mpr hmem).map (T.ι ≫ g).continuous
      simp only [Scheme.Hom.comp_apply] at h1
      rw [huw] at h1
      rw [le_integralComponentAt_iff_mem_support, hDsupp] at hle
      exact hdg (hS.mem_genericPoints_of_specializes h1 hle)

/-! ### Decomposing the exterior product along the first factor -/

omit [LocallyOfFiniteType g] in
/-- The inverse images, under the first projection of `X ×_S Y`, of the reduced closures of the
points in the support of a cycle on `X` form a locally finite family. -/
theorem locallyFinite_support_comap_integralComponentAt {k : ℤ} (α : CycleGroup C f k) :
    LocallyFinite fun x : cycleSupportIndex α ↦
      (((integralComponentAt x.1).comap (pullback.fst f g)).support :
        Set (pullback f g : Scheme.{u})) := by
  refine ((locallyFinite_support_integralComponentAt α).preimage_continuous
    (pullback.fst f g).continuous).subset fun x ↦ ?_
  rw [Scheme.IdealSheafData.support_comap]
  exact subset_rfl

/-- **The exterior product of cycles is a locally finite sum over the first factor.** If, for
every point `x` in the support of `α`, the part `∑_y [x] × [y]` of `α × β` coming from the
components of `α` at `x` is the pushforward of a cycle on `closure {x} ×_S Y` which is rationally
equivalent to zero there, then `α × β` is rationally equivalent to zero. This is Stacks 02RZ for
the locally finite family `closure {x} ×_S Y`. -/
theorem exteriorProductDedekindCycles_mem_rationalEquivalences_of_summands
    (α : CycleGroup C f n) (β : CycleGroup C g m)
    (h : ∀ x : X, α.1 x ≠ 0 → ∃ a : CycleGroup C
        (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫ (pullback.fst f g ≫ f))
        (n + m - 1),
      a ∈ rationalEquivalences C
          (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
            (pullback.fst f g ≫ f)) (n + m - 1) ∧
        ∀ z : (pullback f g : Scheme.{u}),
          (properPushforward C
            (((integralComponentAt x).comap (pullback.fst f g)).subschemeι ≫
              (pullback.fst f g ≫ f)) (pullback.fst f g ≫ f)
            ((integralComponentAt x).comap (pullback.fst f g)).subschemeι rfl (n + m - 1) a).1 z =
            ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y)) :
    exteriorProductDedekindCycles C f g n m α β ∈
      rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1) := by
  classical
  choose a ha hpush using fun x : cycleSupportIndex α ↦ h x.1 x.2
  refine rationallyEquivalentToZero_finsum_of_closedSupports C (pullback.fst f g ≫ f) (n + m - 1)
    (fun x : cycleSupportIndex α ↦ (integralComponentAt x.1).comap (pullback.fst f g))
    (locallyFinite_support_comap_integralComponentAt C f g α) a ha fun z ↦ ?_
  simp_rw [hpush]
  rw [exteriorProductDedekindCycles_apply,
    finsum_curry _ (exteriorProductDedekindTerm_support_finite C f g n m α β z)]
  have hzero : ∀ x : X, α.1 x = 0 → ∀ y : Y,
      exteriorProductDedekindTerm C f g n m α β z (x, y) = 0 := by
    intro x hx y
    unfold exteriorProductDedekindTerm
    split_ifs
    · simp [hx]
    · rfl
  refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond
    (f := fun x : X ↦ ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y))
    (fun x : X ↦ α.1 x ≠ 0)).symm
  refine finsum_congr fun x ↦ ?_
  rw [finsum_eq_if]
  split_ifs with hx
  · rfl
  · push Not at hx
    exact finsum_eq_zero_of_forall_eq_zero (hzero x hx)

/-! ### Stacks 0FC4: compatibility with rational equivalence -/

variable {C} in
/-- **Stacks 0FC4, the second variable.** Over a Dedekind base, the exterior product of an
`n`-cycle on `X` with an `m`-cycle on `Y` rationally equivalent to zero is rationally equivalent to
zero on `X ×_S Y`.

The product is the locally finite sum over the support of the first cycle of its parts at the
points `x` (`Stacks.Chow.exteriorProductDedekindCycles_mem_rationalEquivalences_of_summands`).
If `x` lies over the generic point of an irreducible component of the base, its closure is flat
over the base (Stacks 0AUW) and its part is a flat pullback
(`Stacks.Chow.exists_exteriorProductDedekindSummand_of_dominates`); otherwise `x` lies over a
closed point and its part is a flat pullback of a Gysin map
(`Stacks.Chow.IsDedekindChowBase.exists_exteriorProductDedekindSummand_of_notMem_genericPoints`).
These are the two bivariant classes `i_* ∘ (p')^*` and `i_* ∘ (p')^* ∘ c` of the source, read on
cycles. -/
theorem IsDedekindChowBase.exteriorProductDedekindCycles_mem_rationalEquivalences_right
    (hS : IsDedekindChowBase C) (α : CycleGroup C f n) {β : CycleGroup C g m}
    (hβ : β ∈ rationalEquivalences C g m) :
    exteriorProductDedekindCycles C f g n m α β ∈
      rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1) := by
  refine exteriorProductDedekindCycles_mem_rationalEquivalences_of_summands C f g n m α β
    fun x hx ↦ ?_
  by_cases hgen : f.base x ∈ genericPoints C.S
  · have _ := isIntegral_integralComponentAt x
    have _ : Flat ((integralComponentAt x).subschemeι ≫ f) :=
      hS.flat_of_mem_genericPoints _ (by
        rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_integralComponentAt]
        exact hgen)
    exact exists_exteriorProductDedekindSummand_of_dominates C f g n m α hβ x hgen _
      (hS.relativeDimension_integralComponentAt_comp f x hgen)
  · exact hS.exists_exteriorProductDedekindSummand_of_notMem_genericPoints f g n m α hβ x hx
      hgen

variable {C} in
/-- **Stacks 0FC4, the first variable.** Over a Dedekind base, the exterior product of an
`n`-cycle on `X` rationally equivalent to zero with an `m`-cycle on `Y` is rationally equivalent to
zero on `X ×_S Y`. This is the second variable for the product taken in the opposite order,
pushed forward along the isomorphism `Y ×_S X ≅ X ×_S Y`, which is a closed immersion; this is
the source's "by symmetry". -/
theorem IsDedekindChowBase.exteriorProductDedekindCycles_mem_rationalEquivalences_left
    (hS : IsDedekindChowBase C) {α : CycleGroup C f n} (hα : α ∈ rationalEquivalences C f n)
    (β : CycleGroup C g m) :
    exteriorProductDedekindCycles C f g n m α β ∈
      rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1) := by
  set e : (pullback f g : Scheme.{u}) ≅ (pullback g f : Scheme.{u}) := pullbackSymmetry f g
    with he
  have hbase : e.inv ≫ (pullback.fst f g ≫ f) = pullback.fst g f ≫ g := by
    rw [← Category.assoc, he, pullbackSymmetry_inv_comp_fst, pullback.condition]
  have hdeg : m + n - 1 = n + m - 1 := by ring
  have hcast := mem_rationalEquivalences_cast C (pullback.fst g f ≫ g) hdeg
    (hS.exteriorProductDedekindCycles_mem_rationalEquivalences_right g f m n β hα)
  have hpf := properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion e.inv C
    (pullback.fst g f ≫ g) (pullback.fst f g ≫ f) hbase (n + m - 1) _ hcast
  have hval : properPushforward C (pullback.fst g f ≫ g) (pullback.fst f g ≫ f) e.inv hbase
        (n + m - 1) (hdeg ▸ exteriorProductDedekindCycles C g f m n β α) =
      exteriorProductDedekindCycles C f g n m α β := by
    refine Subtype.ext (DFunLike.ext _ _ fun z ↦ ?_)
    obtain ⟨w, rfl⟩ := (Scheme.homeoOfIso e.symm).surjective z
    rw [show (Scheme.homeoOfIso e.symm) w = e.inv.base w from rfl,
      properPushforward_apply_image_of_isClosedImmersion C (pullback.fst g f ≫ g)
        (pullback.fst f g ≫ f) e.inv hbase (n + m - 1) _ w,
      val_cycleGroup_cast C (pullback.fst g f ≫ g) hdeg]
    exact (exteriorProductDedekindCycles_pullbackSymmetry C f g n m α β w).symm
  rwa [hval] at hpf

variable {C} in
/-- **Stacks 0FC4.** Over a Dedekind base the exterior product of cycles carries rational
equivalences to rational equivalences in each variable, for all `X`, `Y` locally of finite type
over the base and all `n`, `m`. This discharges the hypothesis of
`Stacks.Chow.exteriorProductDedekindTensor`. -/
@[stacks 0FC4 "the exterior product of cycles over a Dedekind base is compatible with rational \
equivalence in each variable; the source's bivariant classes `i_* ∘ (p')^*` and \
`i_* ∘ (p')^* ∘ c` are read on cycles as a flat pullback and a flat pullback of the Gysin map of \
a principal divisor with trivial normal bundle"]
theorem IsDedekindChowBase.exteriorProductFactorsThroughRationalEquivalence
    (hS : IsDedekindChowBase C) : ExteriorProductFactorsThroughRationalEquivalence C f g n m :=
  ⟨fun α _ hβ ↦ hS.exteriorProductDedekindCycles_mem_rationalEquivalences_right f g n m α hβ,
    fun β _ hα ↦ hS.exteriorProductDedekindCycles_mem_rationalEquivalences_left f g n m hα β⟩

variable {C} in
/-- **Stacks 0FC4.** The exterior product on Chow groups over a Dedekind base,

  `× : CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`,

well defined with no hypothesis beyond the base being as in Stacks section 42.63. It is
`Stacks.Chow.exteriorProductDedekindTensor` with its compatibility with rational equivalence
supplied by `Stacks.Chow.IsDedekindChowBase.exteriorProductFactorsThroughRationalEquivalence`; on
a pure tensor of the classes of integral closed subschemes `X'` and `Y'` of delta-dimensions `n`
and `m` it is the class of `[X' ×_S Y']_{n+m-1}` when one of them dominates an irreducible
component of the base and zero otherwise. -/
@[stacks 0FC4 "the map CH_n(X) ⊗_ℤ CH_m(Y) → CH_{n+m-1}(X ×_S Y) is well defined, \
unconditionally"]
def IsDedekindChowBase.exteriorProductChow (hS : IsDedekindChowBase C) :
    TensorProduct ℤ (chowGroup C f n) (chowGroup C g m) →+
      chowGroup C (pullback.fst f g ≫ f) (n + m - 1) :=
  exteriorProductDedekindTensor C f g n m
    (hS.exteriorProductFactorsThroughRationalEquivalence f g n m)

variable {C} in
/-- On the pure tensor of the classes of two cycles the exterior product over a Dedekind base is
the class of their cycle-level exterior product. -/
@[simp]
theorem IsDedekindChowBase.exteriorProductChow_tmul_mk (hS : IsDedekindChowBase C)
    (α : CycleGroup C f n) (β : CycleGroup C g m) :
    hS.exteriorProductChow f g n m
        (TensorProduct.tmul ℤ (QuotientAddGroup.mk' (rationalEquivalences C f n) α)
          (QuotientAddGroup.mk' (rationalEquivalences C g m) β)) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1))
        (exteriorProductDedekindCycles C f g n m α β) :=
  rfl

end Stacks.Chow

end
