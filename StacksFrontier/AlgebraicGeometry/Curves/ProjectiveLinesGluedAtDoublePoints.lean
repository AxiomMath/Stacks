module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineFiniteType

/-!
# Two projective lines glued along three double points

Let `k` be a field and let `a₀, a₁, a₂ ∈ k` be pairwise distinct. The three double points
`Spec(k[t]/(t - aᵢ)²)` form a closed subscheme `T` of the affine chart `A¹_k ⊂ P¹_k`, and
gluing two copies of `P¹_k` along `T` — the pushout of `T ⟶ P¹_k` with itself — produces a
curve `X`. On the affine open part of `X`, the image of `A¹_k ⨿ A¹_k`, the functions are the
pairs of polynomials agreeing to first order at the three points: the equalizer of the two
reduction maps `k[t] × k[t] ⟶ ∏ᵢ k[t]/(t - aᵢ)²`.

Over a ring in which `2 = 0` this equalizer has infinitesimal automorphisms. If `c` satisfies
`c² = 0` then the substitution `t ↦ t + c` fixes each generator `(t - aᵢ)²`, since
`(t - aᵢ + c)² = (t - aᵢ)² + 2c(t - aᵢ) + c²`, so it preserves each ideal `((t - aᵢ)²)` and
hence acts on the equalizer. Taking `k` of characteristic `2` and `c = ε` in the dual numbers
`k[ε]` gives an automorphism of the equalizer diagram over `k[ε]` which sends `t` to `t + ε`,
is not the identity, and becomes the identity modulo `ε`.

## Main definitions

* `AlgebraicGeometry.doublePointIdeal`: the ideal `((t - a)²)` of `R[t]`.
* `AlgebraicGeometry.doublePointsMk`: the reduction `R[t] ⟶ ∏ᵢ R[t]/(t - aᵢ)²` at three
  points, and `AlgebraicGeometry.reduceFst`, `AlgebraicGeometry.reduceSnd` its two composites
  with the projections of `R[t] × R[t]`.
* `AlgebraicGeometry.gluingSubring`: the equalizer of those two reduction maps, with
  `AlgebraicGeometry.gluingSubringFst` and `AlgebraicGeometry.gluingSubringSnd` its two
  coordinates and `AlgebraicGeometry.gluingScheme` its spectrum.
* `AlgebraicGeometry.doublePointsScheme`, `AlgebraicGeometry.doublePointsToAffineLine` and
  `AlgebraicGeometry.doublePointsToProjectiveLine`: the scheme `T` of the three double points
  and its maps to `A¹_k` and to `P¹_k`.
* `AlgebraicGeometry.gluedCurve`: the curve `X`, the pushout of `T ⟶ P¹_k` with itself,
  together with `AlgebraicGeometry.gluedCurveInl`, `AlgebraicGeometry.gluedCurveInr` the two
  copies of `P¹_k` inside it and `AlgebraicGeometry.gluedCurveToBase` its structure morphism
  over `k`.
* `AlgebraicGeometry.translate`: the substitution `t ↦ t + c` on `R[t]`, with
  `AlgebraicGeometry.gluingSubringTranslate` the automorphism it induces on the equalizer and
  `AlgebraicGeometry.epsTranslate` the case `c = ε` over the dual numbers.

## Main results

* `AlgebraicGeometry.isClosedImmersion_doublePointsToProjectiveLine`: for three pairwise
  distinct points the three double points form a closed subscheme of `P¹_k`.
* `AlgebraicGeometry.isPushout_gluedCurve`: `X` is the pushout of two copies of `P¹_k`
  along `T`, and `AlgebraicGeometry.isClosedImmersion_gluedCurveInl`,
  `AlgebraicGeometry.isClosedImmersion_gluedCurveInr` say that the two copies are closed
  subschemes of `X`.
* `AlgebraicGeometry.isPushout_gluingScheme`: the two affine lines glue along `T` to the
  spectrum of the equalizer, so the functions on the affine part of `X` are the pairs of
  polynomials agreeing to first order at the three points.
* `AlgebraicGeometry.gluingSubringTranslate_ne_one` and
  `AlgebraicGeometry.epsTranslate_ne_one`: the substitution `t ↦ t + ε` is not the identity
  on the equalizer over the dual numbers of a field of characteristic `2`.
* `AlgebraicGeometry.map_translate_of_map_eq_zero` and
  `AlgebraicGeometry.map_fst_epsTranslate`: that automorphism becomes the identity modulo `ε`.

## Implementation notes

`T` is realized as `Spec` of the product ring `∏ᵢ k[t]/(t - aᵢ)²`, which is the disjoint union
of the three double points, and the reduction out of `k[t]` is surjective by the Chinese
remainder theorem, so `T ⟶ A¹_k` is a closed immersion. That `T ⟶ P¹_k` is again a closed
immersion is read off from finiteness: `T` is finite over `k` because each `k[t]/(t - aᵢ)²` is
a free module of rank two, and `P¹_k` is separated over `k`, so `T ⟶ P¹_k` is finite; it is a
monomorphism as a composite of a closed and an open immersion, and a finite monomorphism is a
closed immersion. The equalizer is the fibre product of the reduction map with itself, so the
affine gluing is an instance of the cocartesian square of a surjection of rings.

The equalizer is identified with the functions on the pushout of the two affine lines, not with
the sections of `X` over an open subscheme: that the affine gluing is an open subscheme of `X`
is not proved here. Neither is the extension of the automorphism `t ↦ t + ε` from the equalizer
to the whole of `X`, nor the finiteness of the group of automorphisms of `X` over `k`, nor the
resulting non-reducedness of the automorphism group scheme of `X`. For the last of these the
obstruction is one of expressibility: the automorphism group of an object of an algebraic stack
is available only as a group object in presheaves on a big fppf site, whose carrier is not a
scheme, so reducedness cannot be asked of it.

## References

* [Stacks Project, Tag 0DSU](https://stacks.math.columbia.edu/tag/0DSU)
* [Stacks Project, Tag 0B7M](https://stacks.math.columbia.edu/tag/0B7M)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

universe u

section DoublePoints

variable {R : Type u} [CommRing R]

/-- The ideal `((t - a)²)` of `R[t]`, cutting out the double point at `a` on the affine
line. -/
def doublePointIdeal (a : R) : Ideal R[X] := Ideal.span {(X - C a) ^ 2}

/-- The ring `R[t]/(t - a)²` of functions on the double point at `a`. -/
abbrev DoublePoint (a : R) : Type u := R[X] ⧸ doublePointIdeal a

/-- The reduction `R[t] ⟶ R[t]/(t - a)²` of a polynomial to first order at `a`. -/
abbrev doublePointMk (a : R) : R[X] →+* DoublePoint a := Ideal.Quotient.mk _

variable (pts : Fin 3 → R)

/-- The ring `∏ᵢ R[t]/(t - aᵢ)²` of functions on the three double points `a₀, a₁, a₂`. -/
abbrev DoublePoints : Type u := ∀ i, DoublePoint (pts i)

/-- The reduction `R[t] ⟶ ∏ᵢ R[t]/(t - aᵢ)²` of a polynomial to first order at the three
points. -/
def doublePointsMk : R[X] →+* DoublePoints pts := RingHom.pi fun i ↦ doublePointMk (pts i)

@[simp]
theorem doublePointsMk_apply (f : R[X]) (i : Fin 3) :
    doublePointsMk pts f i = doublePointMk (pts i) f := rfl

/-- Reduction of the first coordinate: `(f, g) ↦ f mod (t - aᵢ)²`. -/
def reduceFst : R[X] × R[X] →+* DoublePoints pts :=
  (doublePointsMk pts).comp (RingHom.fst _ _)

/-- Reduction of the second coordinate: `(f, g) ↦ g mod (t - aᵢ)²`. -/
def reduceSnd : R[X] × R[X] →+* DoublePoints pts :=
  (doublePointsMk pts).comp (RingHom.snd _ _)

/-- The equalizer of the two reduction maps `R[t] × R[t] ⟶ ∏ᵢ R[t]/(t - aᵢ)²`: the pairs of
polynomials whose values agree to first order at each of the three points. -/
def gluingSubring : Subring (R[X] × R[X]) :=
  RingHom.eqLocus (reduceFst pts) (reduceSnd pts)

theorem mem_gluingSubring_iff {fg : R[X] × R[X]} :
    fg ∈ gluingSubring pts ↔ ∀ i, doublePointMk (pts i) fg.1 = doublePointMk (pts i) fg.2 := by
  constructor
  · intro h i; exact congrFun h i
  · intro h; exact funext h

theorem diag_mem_gluingSubring (f : R[X]) : (f, f) ∈ gluingSubring pts :=
  (mem_gluingSubring_iff pts).2 fun _ ↦ rfl

/-- The equalizer of the two reduction maps is the fibre product of the reduction
`R[t] ⟶ ∏ᵢ R[t]/(t - aᵢ)²` with itself. -/
theorem gluingSubring_eq_pullback :
    gluingSubring pts = (doublePointsMk pts).pullback (doublePointsMk pts) := rfl

/-- The first coordinate `(f, g) ↦ f` of the equalizer. -/
abbrev gluingSubringFst : gluingSubring pts →+* R[X] :=
  RingHom.pullbackFst (doublePointsMk pts) (doublePointsMk pts)

/-- The second coordinate `(f, g) ↦ g` of the equalizer. -/
abbrev gluingSubringSnd : gluingSubring pts →+* R[X] :=
  RingHom.pullbackSnd (doublePointsMk pts) (doublePointsMk pts)

end DoublePoints

section Curve

variable (k : Type u) [Field k] (pts : Fin 3 → k)

/-- The ideals `((t - aᵢ)²)` of distinct points are pairwise coprime: `(t - aᵢ)` and
`(t - aⱼ)` differ by the unit `aⱼ - aᵢ`. -/
theorem pairwise_isCoprime_doublePointIdeal (hpts : Function.Injective pts) :
    Pairwise (Function.onFun IsCoprime fun i ↦ doublePointIdeal (pts i)) := by
  intro i j hij
  have hne : pts j - pts i ≠ 0 := sub_ne_zero.2 fun h ↦ hij (hpts h).symm
  refine Ideal.isCoprime_span_singleton_iff _ _ |>.2 (IsCoprime.pow ?_)
  refine ⟨C (pts j - pts i)⁻¹, -C (pts j - pts i)⁻¹, ?_⟩
  have : (C (pts j - pts i)⁻¹ : k[X]) * (X - C (pts i)) +
      -C (pts j - pts i)⁻¹ * (X - C (pts j)) = C ((pts j - pts i)⁻¹ * (pts j - pts i)) := by
    rw [map_mul, map_sub]; ring
  rw [this, inv_mul_cancel₀ hne, map_one]

/-- The reduction `k[t] ⟶ ∏ᵢ k[t]/(t - aᵢ)²` at three distinct points is surjective, by the
Chinese remainder theorem. -/
theorem doublePointsMk_surjective (hpts : Function.Injective pts) :
    Function.Surjective (doublePointsMk pts) := by
  intro g
  obtain ⟨y, hy⟩ :=
    Ideal.quotientInfToPiQuotient_surj (pairwise_isCoprime_doublePointIdeal k pts hpts) g
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨x, by rw [← hy, ← hx]; rfl⟩

/-- Each `k[t]/(t - a)²` is a free `k`-module of rank two, so the three double points are
finite over `k`. -/
instance module_finite_doublePoints : Module.Finite k (DoublePoints pts) := by
  have : ∀ i : Fin 3, Module.Finite k (DoublePoint (pts i)) := fun i ↦
    ((monic_X_sub_C (pts i)).pow 2).finite_quotient
  infer_instance

/-- The scheme `T` of the three double points `a₀, a₁, a₂`, the disjoint union of the three
spectra `Spec(k[t]/(t - aᵢ)²)`. -/
abbrev doublePointsScheme : Scheme.{u} := Spec (.of (DoublePoints pts))

/-- The map `T ⟶ A¹_k` of the three double points into the affine line. -/
def doublePointsToAffineLine : doublePointsScheme k pts ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (doublePointsMk pts))

/-- The map `T ⟶ P¹_k` of the three double points into the projective line, through the
affine chart. -/
def doublePointsToProjectiveLine : doublePointsScheme k pts ⟶ projectiveLine k :=
  doublePointsToAffineLine k pts ≫ projectiveLineXChart k

theorem isClosedImmersion_doublePointsToAffineLine (hpts : Function.Injective pts) :
    IsClosedImmersion (doublePointsToAffineLine k pts) :=
  IsClosedImmersion.spec_of_surjective _ (doublePointsMk_surjective k pts hpts)

theorem isPreimmersion_doublePointsToProjectiveLine (hpts : Function.Injective pts) :
    IsPreimmersion (doublePointsToProjectiveLine k pts) := by
  have := isClosedImmersion_doublePointsToAffineLine k pts hpts
  exact IsPreimmersion.comp _ _

/-- The three double points are finite over `k` through the projective line. -/
theorem isFinite_doublePointsToProjectiveLine_comp :
    IsFinite (doublePointsToProjectiveLine k pts ≫ (projectiveLine k ↘ Spec (.of k))) := by
  have hcomp : doublePointsToProjectiveLine k pts ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom ((doublePointsMk pts).comp (C : k →+* k[X]))) := by
    rw [doublePointsToProjectiveLine, Category.assoc,
      projectiveLineXChart_comp_structureMorphism, doublePointsToAffineLine,
      ← Spec.map_comp]
    rfl
  rw [hcomp, IsFinite.SpecMap_iff]
  change RingHom.Finite ((doublePointsMk pts).comp (C : k →+* k[X]))
  rw [show (doublePointsMk pts).comp (C : k →+* k[X]) = algebraMap k (DoublePoints pts) from rfl,
    RingHom.finite_algebraMap]
  infer_instance

/-- **Stacks 0DSU.** For three pairwise distinct points of the affine line, the three double
points `Spec(k[t]/(t - aᵢ)²)` form a closed subscheme of `P¹_k`. -/
@[stacks 0DSU "the three double points form a closed subscheme of the projective line"]
theorem isClosedImmersion_doublePointsToProjectiveLine (hpts : Function.Injective pts) :
    IsClosedImmersion (doublePointsToProjectiveLine k pts) := by
  have := isPreimmersion_doublePointsToProjectiveLine k pts hpts
  have : IsFinite (doublePointsToProjectiveLine k pts) :=
    have := isFinite_doublePointsToProjectiveLine_comp k pts
    IsFinite.of_comp _ (projectiveLine k ↘ Spec (.of k))
  rw [IsClosedImmersion.iff_isFinite_and_mono]
  exact ⟨inferInstance, inferInstance⟩

/-- The affine scheme `Spec(O)` of the equalizer `O` of the two reduction maps
`k[t] × k[t] ⇉ ∏ᵢ k[t]/(t - aᵢ)²`. -/
abbrev gluingScheme : Scheme.{u} := Spec (.of (gluingSubring pts))

/-- **Stacks 0DSU.** Gluing two copies of `A¹_k` along the three double points gives the
spectrum of the equalizer of the two reduction maps `k[t] × k[t] ⇉ ∏ᵢ k[t]/(t - aᵢ)²`: the
functions on the affine part of the glued curve are the pairs of polynomials agreeing to first
order at the three points. -/
@[stacks 0DSU "the two affine lines glue to the spectrum of the equalizer of the two reductions"]
theorem isPushout_gluingScheme (hpts : Function.Injective pts) :
    IsPushout (doublePointsToAffineLine k pts) (doublePointsToAffineLine k pts)
      (Spec.map (CommRingCat.ofHom (gluingSubringSnd pts)))
      (Spec.map (CommRingCat.ofHom (gluingSubringFst pts))) :=
  Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _
    (Stacks.Pushout.isPullback_ofHom_pullback (doublePointsMk pts) (doublePointsMk pts))
    (doublePointsMk_surjective k pts hpts)

variable (hpts : Function.Injective pts)

/-- **Stacks 0DSU.** The curve `X` of the example: two copies of `P¹_k` glued along the closed
subscheme of the three double points `Spec(k[t]/(t - aᵢ)²)`, that is, the pushout of
`T ⟶ P¹_k` with itself. -/
@[stacks 0DSU "the curve obtained by gluing two projective lines along three double points"]
def gluedCurve : Scheme.{u} :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  pushout (doublePointsToProjectiveLine k pts) (doublePointsToProjectiveLine k pts)

/-- The first copy `Y = P¹_k` inside the glued curve. -/
def gluedCurveInl : projectiveLine k ⟶ gluedCurve k pts hpts :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  pushout.inl (doublePointsToProjectiveLine k pts) (doublePointsToProjectiveLine k pts)

/-- The second copy `Z = P¹_k` inside the glued curve. -/
def gluedCurveInr : projectiveLine k ⟶ gluedCurve k pts hpts :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  pushout.inr (doublePointsToProjectiveLine k pts) (doublePointsToProjectiveLine k pts)

/-- **Stacks 0DSU.** The glued curve is the pushout of the two copies of `P¹_k` along the
three double points. -/
@[stacks 0DSU "the glued curve is the pushout of the two projective lines"]
theorem isPushout_gluedCurve :
    IsPushout (doublePointsToProjectiveLine k pts) (doublePointsToProjectiveLine k pts)
      (gluedCurveInl k pts hpts) (gluedCurveInr k pts hpts) :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  IsPushout.of_hasPushout _ _

/-- Both copies of `P¹_k` are closed subschemes of the glued curve. -/
theorem isClosedImmersion_gluedCurveInl :
    IsClosedImmersion (gluedCurveInl k pts hpts) :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  pushout_inl_isClosedImmersion _ _

theorem isClosedImmersion_gluedCurveInr :
    IsClosedImmersion (gluedCurveInr k pts hpts) :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  pushout_inr_isClosedImmersion _ _

/-- The structure morphism of the glued curve over `k`, obtained from the structure morphisms
of the two copies of `P¹_k`. -/
def gluedCurveToBase : gluedCurve k pts hpts ⟶ Spec (.of k) :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  pushout.desc (projectiveLine k ↘ Spec (.of k)) (projectiveLine k ↘ Spec (.of k)) rfl

@[simp]
theorem gluedCurveInl_comp_toBase :
    gluedCurveInl k pts hpts ≫ gluedCurveToBase k pts hpts =
      projectiveLine k ↘ Spec (.of k) :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  pushout.inl_desc _ _ _

@[simp]
theorem gluedCurveInr_comp_toBase :
    gluedCurveInr k pts hpts ≫ gluedCurveToBase k pts hpts =
      projectiveLine k ↘ Spec (.of k) :=
  haveI := isClosedImmersion_doublePointsToProjectiveLine k pts hpts
  pushout.inr_desc _ _ _

end Curve

section Translate

variable {R : Type u} [CommRing R]

/-- The substitution `t ↦ t + c` on `R[t]`. -/
def translate (c : R) : R[X] →ₐ[R] R[X] := aeval (X + C c)

@[simp]
theorem translate_X (c : R) : translate c X = X + C c := by simp [translate]

@[simp]
theorem translate_C (c a : R) : translate c (C a) = C a := by simp [translate]

/-- Translating twice by `c` is translating by `c + c`; in particular it is the identity
when `c + c = 0`. -/
theorem translate_comp_translate {c : R} (hc : c + c = 0) :
    (translate c).comp (translate c) = AlgHom.id R R[X] := by
  refine Polynomial.algHom_ext ?_
  simp only [AlgHom.coe_comp, Function.comp_apply, translate_X, map_add, translate_C,
    AlgHom.coe_id, id_eq]
  rw [add_assoc, ← C_add, hc, map_zero, add_zero]

@[simp]
theorem translate_translate {c : R} (hc : c + c = 0) (f : R[X]) :
    translate c (translate c f) = f :=
  congrFun (congrArg (fun g : R[X] →ₐ[R] R[X] ↦ (g : R[X] → R[X]))
    (translate_comp_translate hc)) f

/-- Over a ring in which `2 = 0`, a translation by a square-zero element fixes the square
`(t - a)²`: expanding gives `(t - a)² + 2c(t - a) + c²`, and the last two terms vanish. -/
theorem translate_sq_X_sub_C {c : R} (h2 : (2 : R) = 0) (hc : c * c = 0) (a : R) :
    translate c ((X - C a) ^ 2) = (X - C a) ^ 2 := by
  have h2' : (2 : R[X]) = 0 := by
    rw [show (2 : R[X]) = C (2 : R) from (map_ofNat C 2).symm, h2, map_zero]
  have hu : translate c (X - C a) = (X - C a) + C c := by
    rw [map_sub, translate_X, translate_C]; ring
  have hcc : (C c : R[X]) ^ 2 = 0 := by rw [← C_pow, sq, hc, map_zero]
  rw [map_pow, hu, add_sq, hcc, h2']
  ring

/-- A translation by a square-zero element maps the ideal `((t - a)²)` into itself. -/
theorem translate_mem_doublePointIdeal {c : R} (h2 : (2 : R) = 0) (hc : c * c = 0) {a : R}
    {f : R[X]} (hf : f ∈ doublePointIdeal a) : translate c f ∈ doublePointIdeal a := by
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  refine Ideal.mem_span_singleton'.2 ⟨translate c g, ?_⟩
  rw [map_mul, translate_sq_X_sub_C h2 hc]

variable (pts : Fin 3 → R)

/-- Translating both coordinates preserves the equalizer of the two reduction maps: the
substitution respects each ideal `((t - aᵢ)²)`, hence each of the three conditions. -/
theorem translate_pair_mem_gluingSubring {c : R} (h2 : (2 : R) = 0) (hc : c * c = 0)
    {fg : R[X] × R[X]} (hfg : fg ∈ gluingSubring pts) :
    (translate c fg.1, translate c fg.2) ∈ gluingSubring pts := by
  refine (mem_gluingSubring_iff pts).2 fun i ↦ ?_
  have h := (mem_gluingSubring_iff pts).1 hfg i
  rw [Ideal.Quotient.eq] at h ⊢
  rw [← map_sub]
  exact translate_mem_doublePointIdeal h2 hc h

/-- The automorphism of the equalizer of the two reduction maps given by the substitution
`t ↦ t + c` on both coordinates, for `c` with `c + c = 0` and `c² = 0`. -/
def gluingSubringTranslate {c : R} (h2 : (2 : R) = 0) (hc : c * c = 0) :
    gluingSubring pts ≃+* gluingSubring pts where
  toFun x := ⟨(translate c x.1.1, translate c x.1.2),
    translate_pair_mem_gluingSubring pts h2 hc x.2⟩
  invFun x := ⟨(translate c x.1.1, translate c x.1.2),
    translate_pair_mem_gluingSubring pts h2 hc x.2⟩
  left_inv x := by
    have h2' : c + c = 0 := by rw [← two_mul, h2, zero_mul]
    ext <;> simp [translate_translate h2']
  right_inv x := by
    have h2' : c + c = 0 := by rw [← two_mul, h2, zero_mul]
    ext <;> simp [translate_translate h2']
  map_mul' x y := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp]
theorem gluingSubringTranslate_apply_coe {c : R} (h2 : (2 : R) = 0) (hc : c * c = 0)
    (x : gluingSubring pts) :
    ((gluingSubringTranslate pts h2 hc x : R[X] × R[X])) =
      (translate c x.1.1, translate c x.1.2) := rfl

/-- The substitution `t ↦ t + c` on the equalizer is not the identity as soon as `c ≠ 0`:
it moves the pair `(t, t)`. -/
theorem gluingSubringTranslate_ne_one {c : R} (h2 : (2 : R) = 0) (hc : c * c = 0)
    (hc0 : c ≠ 0) : gluingSubringTranslate pts h2 hc ≠ RingEquiv.refl _ := by
  intro h
  have hx := congrArg (fun e : gluingSubring pts ≃+* gluingSubring pts ↦
    ((e ⟨(X, X), diag_mem_gluingSubring pts X⟩ : gluingSubring pts) : R[X] × R[X])) h
  rw [gluingSubringTranslate_apply_coe] at hx
  exact hc0 (by simpa using hx)

/-- Killing `c` kills the substitution `t ↦ t + c`: for a ring map `φ` with `φ c = 0`, the
translation by `c` becomes the identity after applying `φ` coefficientwise. -/
theorem map_translate_of_map_eq_zero {S : Type u} [CommRing S] (φ : R →+* S) {c : R}
    (hc : φ c = 0) (f : R[X]) :
    (Polynomial.mapRingHom φ) (translate c f) = (Polynomial.mapRingHom φ) f := by
  have key : (Polynomial.mapRingHom φ).comp (translate c).toRingHom =
      Polynomial.mapRingHom φ := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp [hc]
  exact DFunLike.congr_fun key f

end Translate

section DualNumbers

variable (k : Type u) [Field k] [CharP k 2]

open DualNumber TrivSqZeroExt in
/-- In characteristic `2` the dual numbers satisfy `2 = 0`. -/
theorem two_eq_zero_dualNumber : (2 : DualNumber k) = 0 := by
  have h : ((2 : ℕ) : k) = 0 := CharP.cast_eq_zero k 2
  have : ((2 : ℕ) : DualNumber k) = 0 := by
    rw [← inl_natCast, show ((2 : ℕ) : k) = 0 from h, inl_zero]
  simpa using this

variable (pts : Fin 3 → DualNumber k)

/-- **Stacks 0DSU.** The automorphism of the equalizer diagram
`k[ε][t] × k[ε][t] ⇉ ∏ᵢ k[ε][t]/(t - aᵢ)²` over the dual numbers of a field of characteristic
`2` given by the substitution `t ↦ t + ε` on both coordinates. -/
@[stacks 0DSU "the automorphism of the equalizer diagram sending t to t + epsilon"]
def epsTranslate : gluingSubring pts ≃+* gluingSubring pts :=
  gluingSubringTranslate pts (two_eq_zero_dualNumber k) DualNumber.eps_mul_eps

/-- **Stacks 0DSU.** The substitution `t ↦ t + ε` on the equalizer diagram is not the
identity. -/
@[stacks 0DSU "non-triviality of the automorphism sending t to t + epsilon"]
theorem epsTranslate_ne_one : epsTranslate k pts ≠ RingEquiv.refl _ := by
  refine gluingSubringTranslate_ne_one pts (two_eq_zero_dualNumber k) DualNumber.eps_mul_eps
    (fun h ↦ one_ne_zero (α := k) ?_)
  have h' := congrArg TrivSqZeroExt.snd h
  rwa [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] at h'

/-- **Stacks 0DSU.** The substitution `t ↦ t + ε` becomes the identity modulo `ε`. -/
@[stacks 0DSU "the automorphism sending t to t + epsilon is the identity modulo epsilon"]
theorem map_fst_epsTranslate (x : gluingSubring pts) :
    ((Polynomial.mapRingHom (TrivSqZeroExt.fstHom k k k).toRingHom) (epsTranslate k pts x).1.1,
        (Polynomial.mapRingHom (TrivSqZeroExt.fstHom k k k).toRingHom)
          (epsTranslate k pts x).1.2) =
      ((Polynomial.mapRingHom (TrivSqZeroExt.fstHom k k k).toRingHom) x.1.1,
        (Polynomial.mapRingHom (TrivSqZeroExt.fstHom k k k).toRingHom) x.1.2) := by
  have hc : (TrivSqZeroExt.fstHom k k k).toRingHom (DualNumber.eps : DualNumber k) = 0 :=
    DualNumber.fst_eps
  exact Prod.ext (map_translate_of_map_eq_zero _ hc _) (map_translate_of_map_eq_zero _ hc _)

end DualNumbers

end AlgebraicGeometry
