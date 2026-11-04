module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsBound
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsEmbedding
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PuncturedSpectrumIsomorphism
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.SpecialFibreSections
public import StacksFrontier.RingTheory.LocalRing.TotalFractionsAway

/-!
# A uniform bound on the sections of the divisor cut out by an element

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two and `a ∈ A` nonzero. There is
an integer `N` such that for every modification `f : X ⟶ Spec A` with `X` normal the `A`-module

  `M_{X,a} = Coker(A ⟶ H⁰(Z, 𝒪_Z))`,

for `Z ⊆ X` cut out by `a`, has length at most `N` ([Stacks, Tag 0AXJ]).

## Main results

* `length_quotient_le_length_normalizationCokernel`: a ring integral over `A ⧸ cA` and embedded
  in its total ring of fractions has its cokernel over `A` bounded by `normalizationCokernel`.
* `AlgebraicGeometry.VanishingSituation.length_quotient_baseToZeroSchemeSections_le`: for `c ∈ 𝔪`
  nonzero with `A ⧸ cA` reduced, the length of `M_{X,c}` is at most that of the cokernel of
  `A ⧸ cA` in its integral closure in its total ring of fractions, for every normal modification
  `X`.
This is the subquotient step of [Stacks, Tag 0AXJ]; the tag itself is
`AlgebraicGeometry.exists_uniform_bound_length_quotient_baseToZeroSchemeSections`.

## Implementation notes

This follows the source. `H⁰(Z, 𝒪_Z)`, for `Z` the zero scheme of `c`, is a ring integral over
`R = A ⧸ cA` because `Z` is proper over `Spec A`. Choose `d ∈ 𝔪` in no minimal prime of `R`.
Then the localization of `R` away from `d` is its total ring of fractions, and `D(c) ∪ D(d)` is
the punctured spectrum `U`. Since `f` is an isomorphism over `U`, the preimage `X_d` of `D(d)` is
affine with ring `A_d`, so restriction to `Z ∩ X_d` maps `H⁰(Z, 𝒪_Z)` to `A_d ⧸ cA_d = R_d`. On
the image of `H⁰(X, 𝒪_X/c𝒪_X)` this map is injective: a section killed there vanishes on
`f⁻¹(D(d))`, it vanishes on `f⁻¹(D(c))` because `Z` does not meet it, and a section of
`𝒪_X/c𝒪_X` vanishing on `f⁻¹(U)` is zero
(`VanishingSituation.eq_zero_of_res_preimagePuncturedSpectrum_eq_zero`, the step of the source's
proof that rests on [Stacks, Tag 0AXB]). So `M_{X,c}` embeds into the cokernel of `A` in a ring
between `R` and its integral closure in its total ring of fractions, and
`length_quotient_le_length_normalizationCokernel` bounds its length.

The reduction from `a` to such a `c` is that of
`AlgebraicGeometry.exists_bound_length_quotient_baseToZeroSchemeSections`, whose hypothesis
`hsub` is exactly the bound proved here.

## References

* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

/-- If an injective `A`-linear map `L : M ⟶ T` to an `A`-algebra carries `b : A ⟶ M` to the
structure map of `T`, then the cokernel of `b` is no longer than the cokernel of `A ⟶ T`. -/
private theorem length_quotient_range_le_of_injective_aux {A M T : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [CommRing T] [Algebra A T] (b : A →ₗ[A] M) (L : M →ₗ[A] T)
    (hL : Function.Injective L) (hb : ∀ a, L (b a) = algebraMap A T a) :
    Module.length A (M ⧸ LinearMap.range b) ≤
      Module.length A (T ⧸ LinearMap.range (Algebra.linearMap A T)) := by
  have hle : LinearMap.range b ≤ (LinearMap.range (Algebra.linearMap A T)).comap L := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (hb a).symm⟩
  refine Module.length_le_of_injective (Submodule.mapQ _ _ L hle) ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with | _ σ =>
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨a, ha⟩ := hx
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨a, hL (by rwa [hb])⟩

/-- **The algebraic half of the subquotient step in the proof of [Stacks, Tag 0AXJ].** Let
`A ⟶ R` be a surjection of commutative rings, and let `T` be an `R`-algebra which is integral
over `R` and admits an injective `R`-algebra map to the total ring of fractions of `R`. Then the
cokernel of `A ⟶ T` has length at most the length of `normalizationCokernel R` over `R`.

In the source's proof of [Stacks, Tag 0AXJ] this is applied with `R = A ⧸ cA` and
`T = H⁰(Z', 𝒪_{Z'})`, for `Z'` the scheme theoretic closure of `Z ∩ f⁻¹(U)`; the sentence "the
length of `M_{X,a}` is bounded by the length of `B/A`" is this inequality.

Integrality over `R` together with the injection into `Frac R` says exactly that `T` is carried
isomorphically onto an `R`-subalgebra of the integral closure `B`, so the cokernel of `R ⟶ T`
injects into the cokernel of `R ⟶ B`. The passage between the two base rings costs nothing
because `A ⟶ R` is surjective, which makes the `A`-submodules of a quotient of `T` exactly its
`R`-submodules ([Stacks, Tag 00IX]). -/
theorem length_quotient_le_length_normalizationCokernel {A R T : Type u} [CommRing A]
    [CommRing R] [CommRing T] [Algebra A R] [Algebra A T] [Algebra R T] [IsScalarTower A R T]
    [Algebra.IsIntegral R T] (hq : Function.Surjective (algebraMap A R))
    (θ : T →ₐ[R] FractionRing R) (hθ : Function.Injective θ) :
    Module.length A (T ⧸ LinearMap.range (Algebra.linearMap A T)) ≤
      Module.length R (normalizationCokernel R) := by
  let C := integralClosure R (FractionRing R)
  let g : T →ₐ[R] ↥C := θ.codRestrict C fun t => (Algebra.IsIntegral.isIntegral t).map θ
  let Q : Submodule R T := LinearMap.range (Algebra.linearMap R T)
  have hrange : LinearMap.range (Algebra.linearMap A T) = Q.restrictScalars A := by
    refine SetLike.ext fun t => ⟨?_, ?_⟩
    · rintro ⟨a, rfl⟩
      exact ⟨algebraMap A R a, by
        simp [Algebra.linearMap_apply, IsScalarTower.algebraMap_apply A R T]⟩
    · rintro ⟨r, hr⟩
      obtain ⟨a, rfl⟩ := hq r
      exact ⟨a, by
        simpa [Algebra.linearMap_apply, IsScalarTower.algebraMap_apply A R T] using hr⟩
  rw [hrange]
  calc Module.length A (T ⧸ Q.restrictScalars A)
      = Module.length A (T ⧸ Q) := (Submodule.Quotient.restrictScalarsEquiv A Q).length_eq
    _ = Module.length R (T ⧸ Q) := Module.length_eq_of_surjective hq
    _ ≤ Module.length R (normalizationCokernel R) :=
        length_quotient_range_le_of_injective_aux (Algebra.linearMap R T) g.toLinearMap
          (fun s t h => hθ (congrArg Subtype.val h)) fun r => g.commutes r

/-- If `S` is the localization of an `A`-algebra away from `d` and `g : S ⟶ S'` is surjective with
kernel generated by `c`, then `S'` is the localization of `A ⧸ cA` away from the image of `d`. -/
theorem isLocalization_away_mk_of_surjective {A S S' : Type*} [CommRing A] [CommRing S]
    [CommRing S'] [Algebra A S] {c d : A} [Algebra (A ⧸ Ideal.span {c}) S']
    [IsLocalization.Away d S] (g : S →+* S') (hg : Function.Surjective g)
    (hker : RingHom.ker g = (Ideal.span {c}).map (algebraMap A S))
    (H : ∀ a, g (algebraMap A S a) = algebraMap _ S' (Ideal.Quotient.mk (Ideal.span {c}) a)) :
    IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {c}) d) S' := by
  have h := IsLocalization.of_surjective (Submonoid.powers d) S (Ideal.Quotient.mk (Ideal.span {c}))
    Ideal.Quotient.mk_surjective g hg (RingHom.ext H) (by rw [hker, Ideal.mk_ker])
  rwa [Submonoid.map_powers] at h

/-- If an injective `A`-linear map `L : M ⟶ T` to an `A`-algebra carries `b : A ⟶ M` to the
structure map of `T`, then the cokernel of `b` is no longer than the cokernel of `A ⟶ T`. -/
theorem Module.length_quotient_range_le_of_injective {A M T : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [CommRing T] [Algebra A T] (b : A →ₗ[A] M) (L : M →ₗ[A] T)
    (hL : Function.Injective L) (hb : ∀ a, L (b a) = algebraMap A T a) :
    Module.length A (M ⧸ LinearMap.range b) ≤
      Module.length A (T ⧸ LinearMap.range (Algebra.linearMap A T)) := by
  exact length_quotient_range_le_of_injective_aux b L hL hb

namespace AlgebraicGeometry

attribute [local instance] Scheme.commRingRingCatSheafObj

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))

/-- The zero scheme of an element of the base ring. -/
abbrev zeroSchemeSubscheme (a : A) : Scheme.{u} := (zeroSchemeIdeal X f a).subscheme

/-- The ring map from the base ring to the global functions on the zero scheme of `a`. -/
def zeroSchemeAlgebraMap (a : A) : A →+* Γ(zeroSchemeSubscheme X f a, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ (zeroSchemeIdeal X f a).subschemeι.appTop).hom

/-- The element `a` vanishes on its own zero scheme. -/
theorem zeroSchemeAlgebraMap_self (a : A) : zeroSchemeAlgebraMap X f a a = 0 := by
  have h := subschemeι_app_baseSection_eq_zero X f a ⊤
  rwa [show X.presheaf.map (homOfLE (le_refl (⊤ : X.Opens))).op = 𝟙 _ from
    X.presheaf.map_id _] at h

/-- **The global functions on the zero scheme are integral over the base**: the zero scheme is
proper over `Spec A`. -/
theorem isIntegral_zeroSchemeAlgebraMap [IsProper f] (a : A) :
    (zeroSchemeAlgebraMap X f a).IsIntegral := by
  have h := isIntegral_appTop_of_universallyClosed ((zeroSchemeIdeal X f a).subschemeι ≫ f)
  rw [Scheme.Hom.comp_appTop] at h
  exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2) h

/-- The global sections of `𝒪_X / a𝒪_X` as global functions on the zero scheme of `a`. -/
def toZeroSchemeSections (a : A) :
    (zeroSchemeStructureSheaf X f a).val.obj (op ⊤) →+ Γ(zeroSchemeSubscheme X f a, ⊤) :=
  ((toZeroSchemeSubscheme X f a).val.app (op ⊤)).hom.toAddMonoidHom

/-- The map `toZeroSchemeSections X f a` is injective. -/
theorem toZeroSchemeSections_injective (a : A) :
    Function.Injective (toZeroSchemeSections X f a) :=
  toZeroSchemeSubscheme_app_injective X f a ⊤

/-- The image of `r ∈ A` in the global sections of `𝒪_X / a𝒪_X` is sent by
`toZeroSchemeSections` to `zeroSchemeAlgebraMap X f a r`. -/
theorem toZeroSchemeSections_baseToZeroSchemeSections (a r : A) :
    toZeroSchemeSections X f a (baseToZeroSchemeSections X f a r) =
      zeroSchemeAlgebraMap X f a r :=
  ConcreteCategory.congr_hom
    (congrArg (fun g => g.val.app (op ⊤))
      (toZeroSchemeStructureSheaf_comp_toZeroSchemeSubscheme X f a))
    (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom r)

/-- `toZeroSchemeSections` is `A`-linear: it sends `r • σ` to the product of
`zeroSchemeAlgebraMap X f a r` with the image of `σ`. -/
theorem toZeroSchemeSections_smul (a r : A)
    (σ : globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f a)) :
    toZeroSchemeSections X f a (r • σ) =
      zeroSchemeAlgebraMap X f a r * toZeroSchemeSections X f a σ :=
  ((toZeroSchemeSubscheme X f a).val.app (op ⊤)).hom.map_smul
    (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom r) σ

/-! ### The quotient `A ⧸ cA` -/

section Quotient

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B]

omit [IsNoetherianRing B] [IsDomain B] in
/-- For `c` a nonzero element of the maximal ideal of a two-dimensional Noetherian local domain,
`B ⧸ cB` is a Noetherian local ring of dimension one. -/
theorem isLocalRing_quotient_span_singleton {c : B} (hcm : c ∈ IsLocalRing.maximalIdeal B) :
    IsLocalRing (B ⧸ Ideal.span {c}) := by
  have : Nontrivial (B ⧸ Ideal.span {c}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hcm))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {c})) Ideal.Quotient.mk_surjective

/-- For `c` a nonzero element of the maximal ideal of a two-dimensional Noetherian local domain
`B`, the ring `B ⧸ cB` has Krull dimension one. -/
theorem ringKrullDim_quotient_span_singleton_eq_one (hdim : ringKrullDim B = 2) {c : B}
    (hc : c ≠ 0) (hcm : c ∈ IsLocalRing.maximalIdeal B) :
    ringKrullDim (B ⧸ Ideal.span {c}) = 1 := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hc) hcm
  rw [hdim, show (2 : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) by
    norm_num] at h
  exact (ENat.WithBot.add_natCast_cancel (c := 1)).mp (by simpa using h)

/-- **An element `d` with `(c, d)` primary to the maximal ideal and `d` regular modulo `c`.** For
`B ⧸ cB` reduced there is `d ∈ 𝔪` lying in no minimal prime of `B ⧸ cB`; every prime of `B`
containing `c` and `d` is then the maximal ideal, and the localization of `B ⧸ cB` away from `d`
is its total ring of fractions. -/
theorem exists_mem_maximalIdeal_forall_isPrime_eq (hdim : ringKrullDim B = 2) {c : B}
    (hc : c ≠ 0) (hcm : c ∈ IsLocalRing.maximalIdeal B)
    (hred : _root_.IsReduced (B ⧸ Ideal.span {c})) :
    ∃ d ∈ IsLocalRing.maximalIdeal B,
      (∀ q : Ideal B, q.IsPrime → c ∈ q → d ∈ q → q = IsLocalRing.maximalIdeal B) ∧
      ∀ (L : Type u) [CommRing L] [Algebra (B ⧸ Ideal.span {c}) L]
        [IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {c}) d) L],
        IsLocalization (nonZeroDivisors (B ⧸ Ideal.span {c})) L := by
  let R := B ⧸ Ideal.span {c}
  have : IsLocalRing R := isLocalRing_quotient_span_singleton hcm
  have : _root_.IsReduced R := hred
  obtain ⟨d₀, hd₀m, hd₀prime, hloc⟩ :=
    IsLocalRing.exists_mem_maximalIdeal_isLocalization_nonZeroDivisors (R := R)
      (ringKrullDim_quotient_span_singleton_eq_one hdim hc hcm)
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d₀
  have hmk : Function.Surjective (Ideal.Quotient.mk (Ideal.span {c})) :=
    Ideal.Quotient.mk_surjective
  have hcomap : (IsLocalRing.maximalIdeal R).comap (Ideal.Quotient.mk (Ideal.span {c})) =
      IsLocalRing.maximalIdeal B := by
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {c})) :=
      IsLocalHom.of_surjective _ hmk
    exact IsLocalRing.maximalIdeal_comap _
  refine ⟨d, ?_, ?_, fun L _ _ _ => hloc L⟩
  · rwa [← hcomap]
  · intro q hq hcq hdq
    have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {c})) ≤ q := by
      rwa [Ideal.mk_ker, Ideal.span_singleton_le_iff_mem]
    have h := hd₀prime _ (Ideal.map_isPrime_of_surjective hmk hker) (Ideal.mem_map_of_mem _ hdq)
    rw [← hcomap, ← h, Ideal.comap_map_of_surjective' _ hmk, sup_eq_left.mpr hker]

end Quotient

/-! ### Embedding the sections into the total ring of fractions -/

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-- A point of the base lies in the basic open of the image of `a` exactly when `a` is not in
the corresponding prime. -/
theorem mem_basicOpen_ΓSpecIso_inv_iff (y : V.base) (a : V.A) :
    y ∈ V.base.basicOpen ((Scheme.ΓSpecIso (.of V.A)).inv.hom a) ↔ a ∉ y.asIdeal := by
  refine Iff.trans ?_ (PrimeSpectrum.mem_basicOpen _ _)
  simp only [basicOpen_eq_of_affine', Iso.inv_hom_id_apply]
  exact Iff.rfl

/-- The basic open of an element of the maximal ideal lies in the punctured spectrum. -/
theorem basicOpen_le_puncturedSpectrumOpen {a : V.A} (ha : a ∈ V.maximalIdeal) :
    V.base.basicOpen ((Scheme.ΓSpecIso (.of V.A)).inv.hom a) ≤ V.puncturedSpectrumOpen := by
  intro y hy hys
  rw [V.mem_basicOpen_ΓSpecIso_inv_iff] at hy
  obtain rfl : y = V.closedPoint := hys
  exact hy ha

/-- A point of the zero scheme of `c` lies over a prime containing `c`. -/
theorem mem_asIdeal_of_mem_zeroSchemeSubscheme (c : V.A) (z : zeroSchemeSubscheme V.X V.f c) :
    c ∈ (V.f ((zeroSchemeIdeal V.X V.f c).subschemeι z)).asIdeal := by
  have hz : (zeroSchemeIdeal V.X V.f c).subschemeι z ∈
      ((zeroSchemeIdeal V.X V.f c).support : Set V.X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hz' : (zeroSchemeIdeal V.X V.f c).subschemeι z ∈ V.X.zeroLocus (U := ⊤)
      (Ideal.span {((Scheme.ΓSpecIso (.of V.A)).inv ≫ V.f.appTop).hom c} : Set Γ(V.X, ⊤)) := by
    simpa [zeroSchemeIdeal] using hz
  have hb := (Scheme.mem_zeroLocus_iff _ _ _).mp hz' _ (Ideal.subset_span (Set.mem_singleton _))
  by_contra hc
  apply hb
  rw [show V.X.basicOpen (((Scheme.ΓSpecIso (.of V.A)).inv ≫ V.f.appTop).hom c) =
      V.f ⁻¹ᵁ V.base.basicOpen ((Scheme.ΓSpecIso (.of V.A)).inv.hom c) from
    (Scheme.preimage_basicOpen_top V.f _).symm]
  exact (V.mem_basicOpen_ΓSpecIso_inv_iff _ c).mpr hc

/-- **The points of the zero scheme of `c` over the punctured spectrum lie over `D(d)`**, when
every prime containing `c` and `d` is the maximal ideal. -/
theorem preimage_preimagePuncturedSpectrum_le {c d : V.A}
    (hcd : ∀ q : Ideal V.A, q.IsPrime → c ∈ q → d ∈ q → q = V.maximalIdeal) :
    (zeroSchemeIdeal V.X V.f c).subschemeι ⁻¹ᵁ V.preimagePuncturedSpectrum ≤
      (zeroSchemeIdeal V.X V.f c).subschemeι ⁻¹ᵁ
        (V.f ⁻¹ᵁ V.base.basicOpen ((Scheme.ΓSpecIso (.of V.A)).inv.hom d)) := by
  intro z hz
  change V.f ((zeroSchemeIdeal V.X V.f c).subschemeι z) ∈
    V.base.basicOpen ((Scheme.ΓSpecIso (.of V.A)).inv.hom d)
  rw [V.mem_basicOpen_ΓSpecIso_inv_iff]
  intro hd
  have hq := hcd _ (V.f ((zeroSchemeIdeal V.X V.f c).subschemeι z)).isPrime
    (V.mem_asIdeal_of_mem_zeroSchemeSubscheme c z) hd
  exact hz (show V.f ((zeroSchemeIdeal V.X V.f c).subschemeι z) = V.closedPoint from
    PrimeSpectrum.ext hq)

/-- **A section of `𝒪_X / c𝒪_X` whose image on the zero scheme vanishes on an open containing
the part of the zero scheme over the punctured spectrum is zero.** The section then vanishes on
`f⁻¹(U)`, and a section of `𝒪_X / c𝒪_X` vanishing on `f⁻¹(U)` is zero
(`VanishingSituation.eq_zero_of_res_preimagePuncturedSpectrum_eq_zero`). -/
theorem eq_zero_of_restrict_toZeroSchemeSections_eq_zero [IsNormal V.X] {c : V.A} (hc : c ≠ 0)
    (O : (zeroSchemeSubscheme V.X V.f c).Opens)
    (hO : (zeroSchemeIdeal V.X V.f c).subschemeι ⁻¹ᵁ V.preimagePuncturedSpectrum ≤ O)
    (σ : (zeroSchemeStructureSheaf V.X V.f c).val.obj (op ⊤))
    (h : (zeroSchemeSubscheme V.X V.f c).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op
        (toZeroSchemeSections V.X V.f c σ) = 0) : σ = 0 := by
  refine V.eq_zero_of_res_preimagePuncturedSpectrum_eq_zero c hc σ ?_
  apply toZeroSchemeSubscheme_app_injective V.X V.f c V.preimagePuncturedSpectrum
  refine Eq.trans ?_ (map_zero ((toZeroSchemeSubscheme V.X V.f c).val.app
    (op V.preimagePuncturedSpectrum)).hom).symm
  refine (ConcreteCategory.congr_hom ((toZeroSchemeSubscheme V.X V.f c).val.naturality
    (homOfLE (le_top : V.preimagePuncturedSpectrum ≤ ⊤)).op) σ).trans ?_
  change (zeroSchemeSubscheme V.X V.f c).presheaf.map
    ((homOfLE le_top).op ≫ (homOfLE hO).op) (toZeroSchemeSections V.X V.f c σ) = 0
  rw [Functor.map_comp, ConcreteCategory.comp_apply, h, map_zero]

/-- For `d ∈ 𝔪`, the preimage in `X` of the basic open `D(d)` is affine, as `f` is an isomorphism
over it. -/
theorem isAffineOpen_basicOpen_of_mem_maximalIdeal {d : V.A} (hdm : d ∈ V.maximalIdeal) :
    IsAffineOpen (V.X.basicOpen (V.f.appTop.hom ((Scheme.ΓSpecIso (.of V.A)).inv.hom d))) := by
  have : IsIso (V.f ∣_ V.base.basicOpen ((Scheme.ΓSpecIso (.of V.A)).inv.hom d)) :=
    V.isIso_morphismRestrict_of_le_puncturedSpectrumOpen (V.basicOpen_le_puncturedSpectrumOpen hdm)
  have : IsAffine (V.base.basicOpen ((Scheme.ΓSpecIso (.of V.A)).inv.hom d)) :=
    (isAffineOpen_top V.base).basicOpen _
  have : IsAffineOpen (V.f ⁻¹ᵁ V.base.basicOpen ((Scheme.ΓSpecIso (.of V.A)).inv.hom d)) :=
    IsAffine.of_isIso (V.f ∣_ _)
  rwa [Scheme.preimage_basicOpen_top] at this

/-- The functions on the preimage in `X` of the basic open `D(d)` are the localization of `A` away
from `d`. -/
theorem isLocalization_away_basicOpen (d : V.A) :
    letI : Algebra V.A Γ(V.X, V.X.basicOpen
        (V.f.appTop.hom ((Scheme.ΓSpecIso (.of V.A)).inv.hom d))) :=
      ((algebraMap Γ(V.X, ⊤) _).comp ((Scheme.ΓSpecIso (.of V.A)).inv ≫ V.f.appTop).hom).toAlgebra
    IsLocalization.Away d
      Γ(V.X, V.X.basicOpen (V.f.appTop.hom ((Scheme.ΓSpecIso (.of V.A)).inv.hom d))) := by
  let r : Γ(V.X, ⊤) := V.f.appTop.hom ((Scheme.ΓSpecIso (.of V.A)).inv.hom d)
  have : CompactSpace V.X := QuasiCompact.compactSpace_of_compactSpace V.f
  have : QuasiSeparatedSpace V.X := quasiSeparatedSpace_of_quasiSeparated V.f
  have : IsLocalization.Away r Γ(V.X, V.X.basicOpen r) :=
    isLocalization_basicOpen_of_qcqs (U := ⊤) isCompact_univ isQuasiSeparated_univ r
  have : IsIso ((Scheme.ΓSpecIso (.of V.A)).inv ≫ V.f.appTop) := by
    have := V.modification.isIso_appTop
    infer_instance
  let eA : V.A ≃+* Γ(V.X, ⊤) :=
    (asIso ((Scheme.ΓSpecIso (.of V.A)).inv ≫ V.f.appTop)).commRingCatIsoToRingEquiv
  have h := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers r)
    Γ(V.X, V.X.basicOpen r) eA.symm
  have hM : (Submonoid.powers r).map eA.symm = Submonoid.powers d := by
    rw [Submonoid.map_powers]
    congr 1
    exact eA.symm_apply_apply d
  rwa [hM] at h

/-- **The global functions on the zero scheme of `c` map to the total ring of fractions of
`A ⧸ cA`, compatibly with `A`, injectively on the sections of `𝒪_X / c𝒪_X`.** The map is
restriction to the part of the zero scheme over `D(d)`, for `d` as in
`exists_mem_maximalIdeal_forall_isPrime_eq`: there `f` is an isomorphism onto the affine `D(d)`,
so these are the functions on `Spec (A_d ⧸ c A_d)`, the total ring of fractions of `A ⧸ cA`. -/
theorem exists_ringHom_fractionRing [IsNormal V.X] {c : V.A} (hc : c ≠ 0)
    (hcm : c ∈ V.maximalIdeal) (hred : _root_.IsReduced (V.A ⧸ Ideal.span {c})) :
    ∃ θ : Γ(zeroSchemeSubscheme V.X V.f c, ⊤) →+* FractionRing (V.A ⧸ Ideal.span {c}),
      (∀ r : V.A, θ (zeroSchemeAlgebraMap V.X V.f c r) =
        algebraMap (V.A ⧸ Ideal.span {c}) _ (Ideal.Quotient.mk _ r)) ∧
      ∀ σ, θ (toZeroSchemeSections V.X V.f c σ) = 0 → σ = 0 := by
  classical
  obtain ⟨d, hdm, hcd, hloc⟩ :=
    exists_mem_maximalIdeal_forall_isPrime_eq V.dimension_two hc hcm hred
  let R := V.A ⧸ Ideal.span {c}
  let I := zeroSchemeIdeal V.X V.f c
  let Z := zeroSchemeSubscheme V.X V.f c
  let Xd : V.X.Opens := V.X.basicOpen (V.f.appTop.hom ((Scheme.ΓSpecIso (.of V.A)).inv.hom d))
  let Zd : Z.Opens := I.subschemeι ⁻¹ᵁ Xd
  have hXdaff : IsAffineOpen Xd := V.isAffineOpen_basicOpen_of_mem_maximalIdeal hdm
  let : Algebra V.A Γ(V.X, Xd) :=
    ((algebraMap Γ(V.X, ⊤) _).comp ((Scheme.ΓSpecIso (.of V.A)).inv ≫ V.f.appTop).hom).toAlgebra
  have : IsLocalization.Away d Γ(V.X, Xd) := V.isLocalization_away_basicOpen d
  let g : Γ(V.X, Xd) →+* Γ(Z, Zd) := (I.subschemeι.app Xd).hom
  have hg : Function.Surjective g := I.subschemeι_app_surjective ⟨Xd, hXdaff⟩
  have hker : RingHom.ker g = (Ideal.span {c}).map (algebraMap V.A Γ(V.X, Xd)) := by
    rw [show RingHom.ker g = I.ideal ⟨Xd, hXdaff⟩ from I.ker_subschemeι_app ⟨Xd, hXdaff⟩]
    simp only [I, zeroSchemeIdeal, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
      Set.image_singleton]
    rfl
  let φ : V.A →+* Γ(Z, Zd) := g.comp (algebraMap V.A Γ(V.X, Xd))
  have hφ : Ideal.span {c} ≤ RingHom.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem]
    change algebraMap V.A Γ(V.X, Xd) c ∈ RingHom.ker g
    rw [hker]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self c)
  let : Algebra R Γ(Z, Zd) := (Ideal.Quotient.lift _ φ hφ).toAlgebra
  have : IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {c}) d) Γ(Z, Zd) :=
    isLocalization_away_mk_of_surjective g hg hker fun _ =>
      (Ideal.Quotient.lift_mk (Ideal.span {c}) φ hφ).symm
  have hfrac : IsLocalization (nonZeroDivisors R) Γ(Z, Zd) := hloc Γ(Z, Zd)
  let eθ := IsLocalization.algEquiv (nonZeroDivisors R) Γ(Z, Zd) (FractionRing R)
  let res : Γ(Z, ⊤) →+* Γ(Z, Zd) := (Z.presheaf.map (homOfLE (le_top : Zd ≤ ⊤)).op).hom
  refine ⟨eθ.toRingHom.comp res, fun a => ?_, fun σ hσ => ?_⟩
  · have hres : res (zeroSchemeAlgebraMap V.X V.f c a) = algebraMap R Γ(Z, Zd)
        (Ideal.Quotient.mk _ a) :=
      (ConcreteCategory.congr_hom (I.subschemeι.naturality (homOfLE (le_top : Xd ≤ ⊤)).op)
        (((Scheme.ΓSpecIso (.of V.A)).inv ≫ V.f.appTop).hom a)).symm
    exact (congrArg eθ hres).trans (eθ.commutes _)
  · have hO : I.subschemeι ⁻¹ᵁ V.preimagePuncturedSpectrum ≤ Zd := by
      have h := V.preimage_preimagePuncturedSpectrum_le hcd
      rwa [Scheme.preimage_basicOpen_top] at h
    exact V.eq_zero_of_restrict_toZeroSchemeSections_eq_zero hc Zd hO σ
      (eθ.injective (by simpa using hσ))

/-- **The length bound of the source's proof of [Stacks, Tag 0AXJ].** For `c ∈ 𝔪` nonzero with
`A ⧸ cA` reduced and `X` normal, the cokernel of `A ⟶ H⁰(Z, 𝒪_Z)`, for `Z` cut out by `c`, has
length at most that of the cokernel of `A ⧸ cA` in its integral closure in its total ring of
fractions. The sections embed, compatibly with `A`, into a ring between `A ⧸ cA` and that
integral closure (`exists_ringHom_fractionRing`), the functions on `Z` being integral over `A`
because `Z` is proper over `Spec A`. -/
theorem length_quotient_baseToZeroSchemeSections_le [IsNormal V.X] {c : V.A} (hc : c ≠ 0)
    (hcm : c ∈ V.maximalIdeal) (hred : _root_.IsReduced (V.A ⧸ Ideal.span {c})) :
    Module.length V.A (globalSectionsAsBaseModule V.X V.f (zeroSchemeStructureSheaf V.X V.f c) ⧸
        LinearMap.range (baseToZeroSchemeSections V.X V.f c)) ≤
      Module.length (V.A ⧸ Ideal.span {c}) (normalizationCokernel (V.A ⧸ Ideal.span {c})) := by
  classical
  obtain ⟨θ, hθA, hθinj⟩ := V.exists_ringHom_fractionRing hc hcm hred
  let R := V.A ⧸ Ideal.span {c}
  let K := FractionRing R
  let Z := zeroSchemeSubscheme V.X V.f c
  let φA := zeroSchemeAlgebraMap V.X V.f c
  have hφ : Ideal.span {c} ≤ RingHom.ker φA :=
    (Ideal.span_singleton_le_iff_mem _).mpr (zeroSchemeAlgebraMap_self V.X V.f c)
  let : Algebra R Γ(Z, ⊤) := (Ideal.Quotient.lift _ φA hφ).toAlgebra
  have hint : Algebra.IsIntegral R Γ(Z, ⊤) :=
    ⟨RingHom.IsIntegral.tower_top (Ideal.Quotient.mk _) (Ideal.Quotient.lift _ φA hφ) (by
      convert isIntegral_zeroSchemeAlgebraMap V.X V.f c
      exact Ideal.Quotient.lift_comp_mk _ φA hφ)⟩
  let θR : Γ(Z, ⊤) →ₐ[R] K :=
    { toRingHom := θ
      commutes' := fun r => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact (congrArg θ (Ideal.Quotient.lift_mk _ φA hφ)).trans (hθA a) }
  let T : Subalgebra R K := θR.range
  have hTint : Algebra.IsIntegral R T :=
    Algebra.IsIntegral.of_surjective θR.rangeRestrict θR.rangeRestrict_surjective
  let : Algebra V.A T := ((algebraMap R T).comp (Ideal.Quotient.mk _)).toAlgebra
  have : IsScalarTower V.A R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hθT : ∀ a : V.A, θR.rangeRestrict (φA a) = algebraMap V.A T a := fun a =>
    Subtype.ext (hθA a)
  let L : globalSectionsAsBaseModule V.X V.f (zeroSchemeStructureSheaf V.X V.f c) →ₗ[V.A] T :=
    { toFun := fun σ => θR.rangeRestrict (toZeroSchemeSections V.X V.f c σ)
      map_add' := fun σ τ => by
        change θR.rangeRestrict (toZeroSchemeSections V.X V.f c (σ + τ)) = _
        exact (congrArg θR.rangeRestrict ((toZeroSchemeSections V.X V.f c).map_add σ τ)).trans
          (map_add _ _ _)
      map_smul' := fun a σ => by
        change θR.rangeRestrict (toZeroSchemeSections V.X V.f c (a • σ)) = _
        rw [toZeroSchemeSections_smul, map_mul, hθT, RingHom.id_apply, Algebra.smul_def] }
  have hLbase : ∀ a, L (baseToZeroSchemeSections V.X V.f c a) = algebraMap V.A T a := fun a =>
    (congrArg θR.rangeRestrict (toZeroSchemeSections_baseToZeroSchemeSections V.X V.f c a)).trans
      (hθT a)
  have hLinj : Function.Injective L := (injective_iff_map_eq_zero L).mpr fun σ hσ =>
    hθinj σ (congrArg Subtype.val hσ)
  exact (Module.length_quotient_range_le_of_injective _ L hLinj hLbase).trans
    (length_quotient_le_length_normalizationCokernel (A := V.A) (R := R) (T := T)
      Ideal.Quotient.mk_surjective T.val Subtype.val_injective)

end VanishingSituation

end AlgebraicGeometry

end
