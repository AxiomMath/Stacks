module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionTaylorInvariance
public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelSite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalNonempty
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomology
public import StacksFrontier.RingTheory.DividedPowers.PadicIntegersAtPrime

/-!
# The global section of `𝒪_{X/S}` defined by `τ`, for the example of [Stacks, Tag 07LJ]

Keep the situation of `StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero`: the
base `(A, I, γ) = (ℤ_[p], (p), γ)`, the presentation `C = P/J = ℤ_[p][x, y]/(p, x², xy, y²)` of
`C = 𝐅_p[x, y]/(x², xy, y²)`, the divided power envelope `E = D_{P, γ}(J)` and the element
`τ = γ_p(x²) γ_p(y²) − γ_p(xy)²` of `E`.  Set `X = Spec(C)` and `S = Spec(A)`.

This module builds the global crystalline situation `X/S` and the global section of the structure
sheaf of `Cris(X/S)` that `τ` defines.  Its value on an object `(U, T, δ)` is the image of `τ`
under any divided power morphism `E → Γ(T, 𝒪_T)` over `A` lifting the coordinates `x, y` of
`Γ(U, 𝒪_U)`; such a morphism exists because `U`, and hence `T`, is affine and `Γ(T) → Γ(U)` is
surjective with kernel the divided power ideal, and the image of `τ` does not depend on it by
`Crystalline.TorsionExample.envelopeTau_eq_of_sub_mem`.  That `U` is affine holds for every
object: `X` has exactly one point, so an open subscheme of `X` is empty or all of `X`.

The construction is made on the **big** crystalline site, for every object `(U, T, δ)` of
`CRIS(X/S)` with `U` affine (`Crystalline.TorsionExample.tauAt`), and is compatible with every
morphism of `CRIS(X/S)` (`Crystalline.TorsionExample.tauAt_map`).

## Main definitions

* `Crystalline.TorsionExample.situation` — the global crystalline situation `X/S`.
* `Crystalline.TorsionExample.envelopeLift` — a divided power morphism `E → Γ(T, 𝒪_T)` over `A`
  lifting the coordinates, for an object of `CRIS(X/S)` with affine thickened scheme.
* `Crystalline.TorsionExample.tauAt` — the image of `τ` in `Γ(T, 𝒪_T)`.
* `Crystalline.TorsionExample.tauSection` — the global section of the structure sheaf of
  `Cris(X/S)` defined by `τ`.

## Main results

* `Crystalline.TorsionExample.subsingleton_sourceScheme` — `X` has at most one point.
* `Crystalline.TorsionExample.tauAt_eq` — any lift computes `tauAt`.
* `Crystalline.TorsionExample.tauAt_map` — `tauAt` is compatible with the morphisms of
  `CRIS(X/S)`.
* `Crystalline.TorsionExample.prime_mul_tauSection` — `p τ = 0` as a global section.

## References

* [Stacks Project, Tag 07LJ](https://stacks.math.columbia.edu/tag/07LJ)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DividedPowers Opposite
open Crystalline.DividedPowerScheme Crystalline.GlobalCrystallineSituation

namespace Crystalline

namespace TorsionExample

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] DividedPowers.padicIntAlgebraAtPrime

/-! ### The schemes of the example -/

/-- **`X = Spec(C)`**, for `C = 𝐅_p[x, y]/(x², xy, y²)` in its presentation `P/J`. -/
abbrev sourceScheme : Scheme := Spec (CommRingCat.of (quotientRing p))

/-- The map `A/I = 𝐅_p → C` of the presentation: the composite `A → P → P/J` kills `I = (p)`,
because `p ∈ J`. -/
def residueToQuotient : ℤ_[p] ⧸ (base p).ideal →+* quotientRing p :=
  Ideal.Quotient.lift (base p).ideal
    ((Ideal.Quotient.mk (relations p)).comp (algebraMap ℤ_[p] (polynomial p)))
    (by
      have hp : algebraMap ℤ_[p] (polynomial p) (p : ℤ_[p]) ∈ relations p := by
        rw [map_natCast]
        exact Ideal.subset_span (by simp)
      intro a ha
      change a ∈ Ideal.span {(p : ℤ_[p])} at ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [RingHom.comp_apply, map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right (algebraMap ℤ_[p] (polynomial p) c) (relations p) hp)

/-- **The structure morphism `X ⟶ S₀`** of the example, `Spec` of the map `𝐅_p → C` read in the
closed fibre `S₀ = Spec(A/I)` of `S = Spec(A, I, γ)`. -/
def toClosedFibre :
    sourceScheme p ⟶ closedFiber (specBase (base p).ideal (base p).dividedPowers) :=
  Spec.map (CommRingCat.ofHom (residueToQuotient p)) ≫ (specClosedFiberIso (base p)).inv

/-- `p = 0` in `C = P/J`, the ideal `J` containing `p`. -/
theorem prime_eq_zero_quotientRing : (p : quotientRing p) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (relations p)) p, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

/-- `p = 0` in the global functions of `X = Spec(C)`. -/
theorem prime_eq_zero_sections : (p : Γ(sourceScheme p, ⊤)) = 0 := by
  refine (Scheme.ΓSpecIso
    (CommRingCat.of (quotientRing p))).commRingCatIsoToRingEquiv.injective ?_
  rw [map_natCast, map_zero]
  exact prime_eq_zero_quotientRing p

/-- `p` is nilpotent — indeed zero — in every local ring of `X = Spec(C)`. -/
theorem prime_locallyNilpotent (x : sourceScheme p) :
    IsNilpotent (p : (sourceScheme p).presheaf.stalk x) := by
  have hx : x ∈ (⊤ : (sourceScheme p).Opens) := trivial
  have h := map_natCast ((sourceScheme p).presheaf.germ ⊤ x hx).hom p
  exact ⟨1, by rw [pow_one, ← h, prime_eq_zero_sections, map_zero]⟩

/-- **The global crystalline situation `X/S` of [Stacks, Tag 07LJ]**: `S = Spec(ℤ_p)` with the
divided power ideal `(p)` and its divided powers `γ`, and `X = Spec(C)` over the closed fibre
`Spec(𝐅_p)`.  It indexes the small crystalline site `Cris(X/S)` of [Stacks, Tag 07IG]. -/
def situation : GlobalCrystallineSituation.{0} :=
  specSituation (base p).ideal (base p).dividedPowers p (sourceScheme p) (toClosedFibre p)
    (prime_locallyNilpotent p)

/-- `S` is affine. -/
instance isAffine_situation_S : IsAffine (situation p).S.scheme :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of ℤ_[p])))

/-- `X` is affine. -/
instance isAffine_situation_X : IsAffine (situation p).X :=
  inferInstanceAs (IsAffine (sourceScheme p))

/-- `p` vanishes, hence is nilpotent, in `Γ(X, 𝒪_X)`. -/
theorem prime_isNilpotent_sections : IsNilpotent ((situation p).p : Γ((situation p).X, ⊤)) :=
  ⟨1, by rw [pow_one]; exact prime_eq_zero_sections p⟩

/-! ### `X` has one point -/

/-- The polynomials without constant term lie in the ideal generated by the variables. -/
theorem sub_C_constantCoeff_mem_span_X (f : polynomial p) :
    f - MvPolynomial.C (MvPolynomial.constantCoeff f) ∈
      Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 2))) := by
  classical
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C,
      ite_eq_left rfl, ← MvPolynomial.constantCoeff_eq, sub_self] at hm
    exact hm rfl
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
  exact ⟨i, Set.mem_univ _, Finsupp.mem_support_iff.mp hi⟩

/-- The square of an element of the ideal generated by the variables lies in `J`. -/
theorem sq_mem_relations_of_mem_span_X {g : polynomial p}
    (hg : g ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 2)))) :
    g ^ 2 ∈ relations p := by
  have h2 := Ideal.pow_mem_pow hg 2
  rw [pow_two (Ideal.span _), Ideal.span_mul_span] at h2
  refine (Ideal.span_le.mpr ?_) h2
  rintro _ ⟨a, ⟨i, -, rfl⟩, b, ⟨j, -, rfl⟩, rfl⟩
  have hX : ∀ k : Fin 2, k = 0 ∨ k = 1 := fun k => by fin_cases k <;> simp
  rcases hX i with rfl | rfl <;> rcases hX j with rfl | rfl
  · exact Ideal.subset_span (by simp [polynomialX, pow_two])
  · exact Ideal.subset_span (by simp [polynomialX, polynomialY])
  · change MvPolynomial.X 1 * MvPolynomial.X 0 ∈ relations p
    rw [mul_comm]; exact Ideal.subset_span (by simp [polynomialX, polynomialY])
  · exact Ideal.subset_span (by simp [polynomialY, pow_two])

/-- **Every element of `C = 𝐅_p[x, y]/(x², xy, y²)` is a unit or nilpotent.** -/
theorem isUnit_or_isNilpotent (c : quotientRing p) : IsUnit c ∨ IsNilpotent c := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  set a := MvPolynomial.constantCoeff f
  have hg := sub_C_constantCoeff_mem_span_X p f
  have hnil : IsNilpotent (Ideal.Quotient.mk (relations p)
      (f - MvPolynomial.C (MvPolynomial.constantCoeff f))) :=
    ⟨2, by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact sq_mem_relations_of_mem_span_X p hg⟩
  have hsplit : Ideal.Quotient.mk (relations p) f =
      Ideal.Quotient.mk (relations p) (MvPolynomial.C a) +
        Ideal.Quotient.mk (relations p) (f - MvPolynomial.C (MvPolynomial.constantCoeff f)) := by
    rw [← map_add, add_sub_cancel]
  by_cases ha : IsUnit a
  · left
    rw [hsplit]
    exact hnil.isUnit_add_left_of_commute ((ha.map MvPolynomial.C).map _) (Commute.all _ _)
  · right
    have hmem : a ∈ Ideal.span {(p : ℤ_[p])} := by
      rw [← PadicInt.maximalIdeal_eq_span_p]
      exact (IsLocalRing.mem_maximalIdeal a).mpr ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
    have hzero : Ideal.Quotient.mk (relations p) (MvPolynomial.C a) = 0 := by
      rw [hb, map_mul, map_mul, map_natCast, map_natCast, prime_eq_zero_quotientRing, zero_mul]
    rw [hsplit, hzero, zero_add]
    exact hnil

/-- **`C = 𝐅_p[x, y]/(x², xy, y²)` has exactly one prime ideal** at most: a prime contains the
nilpotents and no unit, and every element is one or the other. -/
instance subsingleton_primeSpectrum : Subsingleton (PrimeSpectrum (quotientRing p)) := by
  refine ⟨fun q₁ q₂ => PrimeSpectrum.ext (Ideal.ext fun c => ?_)⟩
  have key (q : PrimeSpectrum (quotientRing p)) : c ∈ q.asIdeal ↔ IsNilpotent c :=
    ⟨fun hc => (isUnit_or_isNilpotent p c).resolve_left fun hu =>
        q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem hc hu),
      fun ⟨n, hn⟩ => q.isPrime.mem_of_pow_mem n (hn ▸ q.asIdeal.zero_mem)⟩
  rw [key q₁, key q₂]

/-- **`X = Spec(C)` has at most one point.** -/
instance subsingleton_sourceScheme : Subsingleton (sourceScheme p) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum (quotientRing p)))

/-- **The thickened scheme `U` of every object `(U, T, δ)` of `Cris(X/S)` is affine**: `U ⟶ X`
is an open immersion into a space with at most one point, so `U` is empty or `U ⟶ X` is
surjective, hence an isomorphism. -/
instance isAffine_source (A : GlobalCrystallineSituation.CrystallineThickening (situation p)) :
    IsAffine A.obj.thickening.source := by
  have : IsOpenImmersion A.obj.toX := A.property
  by_cases h : IsEmpty A.obj.thickening.source
  · infer_instance
  · obtain ⟨u⟩ := not_isEmpty_iff.mp h
    have : IsIso A.obj.toX := (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, ⟨fun _ => ⟨u, Subsingleton.elim (α := sourceScheme p) _ _⟩⟩⟩
    exact IsAffine.of_isIso A.obj.toX

/-! ### Lifting the coordinates to an object of `CRIS(X/S)` -/

/-- The coordinate `x` (for `i = 0`) or `y` (for `i = 1`) of `C`, read in `Γ(X, 𝒪_X)`. -/
def coordinate (i : Fin 2) : Γ((situation p).X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (quotientRing p))).inv.hom
    (Ideal.Quotient.mk (relations p) (MvPolynomial.X i))

/-- The image in `Γ(X, 𝒪_X)` of an element of `J` vanishes. -/
theorem sections_eq_zero_of_mem_relations {f : polynomial p} (hf : f ∈ relations p) :
    ((Scheme.ΓSpecIso (CommRingCat.of (quotientRing p))).inv.hom
      (Ideal.Quotient.mk (relations p) f) : Γ((situation p).X, ⊤)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

/-- The map `P → Γ(X, 𝒪_X)`. -/
def polynomialToSections : polynomial p →+* Γ((situation p).X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (quotientRing p))).inv.hom.comp (Ideal.Quotient.mk (relations p))

/-- The map `P → Γ(X, 𝒪_X)` sends the variables to the coordinates. -/
theorem polynomialToSections_X (i : Fin 2) :
    polynomialToSections p (MvPolynomial.X i) = coordinate p i := rfl

/-- `p`, `x²`, `xy` and `y²` vanish in `C`. -/
theorem coordinate_relations :
    (p : Γ((situation p).X, ⊤)) = 0 ∧ coordinate p 0 ^ 2 = 0 ∧
      coordinate p 0 * coordinate p 1 = 0 ∧ coordinate p 1 ^ 2 = 0 := by
  have key : ∀ f ∈ relations p, polynomialToSections p f = 0 := fun f hf =>
    sections_eq_zero_of_mem_relations p hf
  refine ⟨prime_eq_zero_sections p, ?_, ?_, ?_⟩
  · rw [← polynomialToSections_X, ← map_pow]
    exact key _ (Ideal.subset_span (by simp [polynomialX]))
  · rw [← polynomialToSections_X, ← polynomialToSections_X, ← map_mul]
    exact key _ (Ideal.subset_span (by simp [polynomialX, polynomialY]))
  · rw [← polynomialToSections_X, ← map_pow]
    exact key _ (Ideal.subset_span (by simp [polynomialY]))

/-- The divided power morphism `A → Γ(T, 𝒪_T)` of an object `(U, T, δ)` of `CRIS(X/S)`: the
identification `A = Γ(S, 𝒪_S)` followed by the structure morphism `T ⟶ S`. -/
def baseToSections (B : Thickening (situation p)) : base p ⟶ B.thickening.sectionsRing :=
  specDividedPowerSchemeUnit (base p) ≫ globalSectionsDPMorphism B.toBase

variable {p}

/-- A divided power morphism into `Γ(T, 𝒪_T)` read as a ring map into `Γ(T, 𝒪_T)`. -/
abbrev toSections {R : DividedPowerRing.{0}} {B : Thickening (situation p)}
    (F : R ⟶ B.thickening.sectionsRing) : ↥R →+* Γ(B.thickening.target.scheme, ⊤) :=
  F.toRingHom

/-- The identification `A = Γ(S, 𝒪_S)`, as a ring map. -/
abbrev baseUnit : ↥(base p) →+* Γ((situation p).S.scheme, ⊤) :=
  (specDividedPowerSchemeUnit (base p)).toRingHom

/-- `baseToSections` on elements. -/
theorem toSections_baseToSections (B : Thickening (situation p)) (a : base p) :
    toSections (baseToSections p B) a = B.toBase.hom.appTop.hom (baseUnit a) := rfl

/-- The chosen lifts to `Γ(T, 𝒪_T)` of the coordinates of `Γ(U, 𝒪_U)`, for an object
`(U, T, δ)` of `CRIS(X/S)` with `U` affine. -/
def liftValues (B : Thickening (situation p)) [IsAffine B.thickening.source] (i : Fin 2) :
    Γ(B.thickening.target.scheme, ⊤) :=
  (B.thickening.surjective_immersion_appTop (B.toX.appTop.hom (coordinate p i))).choose

/-- The chosen lifts restrict to the coordinates of `Γ(U, 𝒪_U)`. -/
theorem immersion_liftValues (B : Thickening (situation p)) [IsAffine B.thickening.source]
    (i : Fin 2) :
    B.thickening.immersion.appTop.hom (liftValues B i) = B.toX.appTop.hom (coordinate p i) :=
  (B.thickening.surjective_immersion_appTop (B.toX.appTop.hom (coordinate p i))).choose_spec

/-- **The criterion for a polynomial map `P → Γ(T, 𝒪_T)` to carry `J` into the divided power
ideal**: the images of the variables restrict to the coordinates of `Γ(U, 𝒪_U)`. -/
theorem map_relations_le (B : Thickening (situation p)) [IsAffine B.thickening.source]
    (a : ↥(base p) →+* Γ(B.thickening.target.scheme, ⊤))
    (v : Fin 2 → Γ(B.thickening.target.scheme, ⊤))
    (hv : ∀ i, B.thickening.immersion.appTop.hom (v i) = B.toX.appTop.hom (coordinate p i)) :
    (relations p).map (MvPolynomial.eval₂Hom a v) ≤
      SchemeThickening.sectionsIdeal B.thickening := by
  obtain ⟨h0, hx, hz, hy⟩ := coordinate_relations (p := p)
  refine Ideal.map_le_iff_le_comap.mpr ?_
  change Ideal.span ({(p : polynomial p), polynomialX p ^ 2,
    polynomialX p * polynomialY p, polynomialY p ^ 2} : Set (polynomial p)) ≤ _
  rw [Ideal.span_le]
  rintro z hz'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
  rw [SetLike.mem_coe, Ideal.mem_comap, SchemeThickening.mem_sectionsIdeal_iff]
  rcases hz' with rfl | rfl | rfl | rfl
  · rw [map_natCast, map_natCast]
    have := congrArg B.toX.appTop.hom h0
    rwa [map_natCast, map_zero] at this
  · rw [map_pow, MvPolynomial.eval₂Hom_X', map_pow, hv, ← map_pow, hx, map_zero]
  · rw [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', map_mul, hv, hv, ← map_mul,
      hz, map_zero]
  · rw [map_pow, MvPolynomial.eval₂Hom_X', map_pow, hv, ← map_pow, hy, map_zero]

/-- A divided power morphism `E → Γ(T, 𝒪_T)` over `A` with the chosen values on the coordinates
exists, by the universal property of the envelope. -/
theorem exists_envelopeLift (B : Thickening (situation p)) [IsAffine B.thickening.source] :
    ∃ q : (envelope p).object ⟶ B.thickening.sectionsRing,
      q.comp (envelope p).structureMap = baseToSections p B ∧
        ∀ i, toSections q (envelopeCoord (envelope p) i) = liftValues B i :=
  exists_envelope_dpMorphism (envelope p) B.thickening.sectionsRing (baseToSections p B)
    (liftValues B) (map_relations_le B (toSections (baseToSections p B)) _ (immersion_liftValues B))

/-- **A divided power morphism `E → Γ(T, 𝒪_T)` over `A` lifting the coordinates**, for an object
`(U, T, δ)` of `CRIS(X/S)` with `U` affine. -/
def envelopeLift (B : Thickening (situation p)) [IsAffine B.thickening.source] :
    (envelope p).object ⟶ B.thickening.sectionsRing :=
  (exists_envelopeLift B).choose

/-- The lift is a morphism over `A`. -/
theorem envelopeLift_comp_structureMap (B : Thickening (situation p))
    [IsAffine B.thickening.source] :
    (envelopeLift B).comp (envelope p).structureMap = baseToSections p B :=
  (exists_envelopeLift B).choose_spec.1

/-- The lift sends the coordinates of `E` to the chosen lifts. -/
theorem envelopeLift_coord (B : Thickening (situation p)) [IsAffine B.thickening.source]
    (i : Fin 2) : toSections (envelopeLift B) (envelopeCoord (envelope p) i) = liftValues B i :=
  (exists_envelopeLift B).choose_spec.2 i

/-! ### The image of `τ` -/

/-- **The image of `τ` in `Γ(T, 𝒪_T)`** for an object `(U, T, δ)` of `CRIS(X/S)` with `U` affine:
`γ_p(x²) γ_p(y²) − γ_p(xy)²` for any lifts `x, y ∈ Γ(T, 𝒪_T)` of the coordinates, computed with
the divided powers of `T`. -/
def tauAt (B : Thickening (situation p)) [IsAffine B.thickening.source] :
    Γ(B.thickening.target.scheme, ⊤) :=
  toSections (envelopeLift B) (envelopeTau p)

/-- **Any lift computes `tauAt`**: a divided power morphism `E → Γ(T, 𝒪_T)` over `A` sending the
coordinates of `E` to lifts of the coordinates of `Γ(U, 𝒪_U)` sends `τ` to `tauAt`. -/
theorem tauAt_eq (B : Thickening (situation p)) [IsAffine B.thickening.source]
    (F : (envelope p).object ⟶ B.thickening.sectionsRing)
    (hF : F.comp (envelope p).structureMap = baseToSections p B)
    (hFv : ∀ i, B.thickening.immersion.appTop.hom (toSections F (envelopeCoord (envelope p) i)) =
      B.toX.appTop.hom (coordinate p i)) :
    toSections F (envelopeTau p) = tauAt B := by
  refine envelopeTau_eq_of_sub_mem p B.thickening.sectionsRing F (envelopeLift B)
    (hF.trans (envelopeLift_comp_structureMap B).symm) fun i => ?_
  have hmem : toSections F (envelopeCoord (envelope p) i) -
      toSections (envelopeLift B) (envelopeCoord (envelope p) i) ∈
        SchemeThickening.sectionsIdeal B.thickening := by
    rw [SchemeThickening.mem_sectionsIdeal_iff, map_sub, hFv, envelopeLift_coord,
      immersion_liftValues, sub_self]
  exact hmem

/-- **`tauAt` is compatible with the morphisms of `CRIS(X/S)`**: the restriction along a
morphism `(U, T, δ) ⟶ (U', T', δ')` carries the image of `τ` in `Γ(T', 𝒪_{T'})` to its image in
`Γ(T, 𝒪_T)`, because composing a lift for `T'` with the restriction gives a lift for `T`. -/
theorem tauAt_map {B B' : Thickening (situation p)} [IsAffine B.thickening.source]
    [IsAffine B'.thickening.source] (f : B ⟶ B') :
    f.targetHom.hom.appTop.hom (tauAt B') = tauAt B := by
  refine tauAt_eq B (envelopeLift B' ≫ globalSectionsDPMorphism f.targetHom) ?_ ?_
  · refine DFunLike.ext _ _ fun r => ?_
    have h := DFunLike.congr_fun (envelopeLift_comp_structureMap B') r
    change toSections (envelopeLift B') ((envelope p).structureMap r) =
      toSections (baseToSections p B') r at h
    change f.targetHom.hom.appTop.hom
        (toSections (envelopeLift B') ((envelope p).structureMap r)) =
      toSections (baseToSections p B) r
    rw [h, toSections_baseToSections, toSections_baseToSections,
      Stacks.Thickenings.appTop_comp_apply]
    change ((f.targetHom ≫ B'.toBase).hom).appTop.hom _ = _
    rw [f.base_naturality]
  · intro i
    change B.thickening.immersion.appTop.hom
        (f.targetHom.hom.appTop.hom (toSections (envelopeLift B') (envelopeCoord (envelope p) i)))
      = _
    rw [envelopeLift_coord, Stacks.Thickenings.appTop_comm_of_comm f.immersion_naturality,
      immersion_liftValues, Stacks.Thickenings.appTop_comp_apply, f.toX_naturality]

/-- `p` kills the image of `τ`, by `p τ = 0` in `E`. -/
theorem prime_mul_tauAt (B : Thickening (situation p)) [IsAffine B.thickening.source] :
    (p : Γ(B.thickening.target.scheme, ⊤)) * tauAt B = 0 := by
  have h := congrArg (toSections (envelopeLift B)) (prime_mul_envelopeTau p)
  rwa [map_mul, map_natCast, map_zero] at h

/-! ### The global section -/

/-- **The global section of the structure sheaf of `Cris(X/S)` defined by `τ`**: its value on an
object `(U, T, δ)` is `tauAt`, the image of `τ` under any lift `E → Γ(T, 𝒪_T)` of the
coordinates. -/
def tauSection :
    ↥(GlobalCrystallineSituation.SmallSite.crystallineSectionRing (situation p)) :=
  ⟨fun A => tauAt A.unop.obj, fun {_ _} f => tauAt_map f.unop.hom⟩

/-- The value of `tauSection` on an object is `tauAt`. -/
@[simp]
theorem tauSection_val (A : (GlobalCrystallineSituation.CrystallineThickening (situation p))ᵒᵖ) :
    (tauSection (p := p)).val A = tauAt A.unop.obj := rfl

/-- **`p τ = 0` as a global section of `𝒪_{X/S}`.** -/
theorem prime_mul_tauSection :
    (p : ↥(GlobalCrystallineSituation.SmallSite.crystallineSectionRing (situation p))) *
      tauSection = 0 :=
  Subtype.ext <| funext fun A => prime_mul_tauAt A.unop.obj

end TorsionExample

end Crystalline

end
