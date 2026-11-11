module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Localization.NumDen
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace

/-!
# The divisor of zeros of a rational function on a locally factorial integral scheme

Let `X` be an integral scheme with function field `K` and let `h ∈ K`. On an affine open `U`
with ring of sections `A = Γ(X, U) ⊆ K`, the elements of `A` which are multiples of `h` in `K`
form the ideal `A ∩ h A`. These ideals are compatible with localization at basic opens, so
they define a closed subscheme of `X`, the *divisor of zeros* of `h`.

When `A` is a unique factorization domain and `h ≠ 0`, write `h = a / b` in lowest terms; then
`A ∩ h A = (a)` with `a ≠ 0`. So on a locally factorial integral scheme the divisor of zeros of a
nonzero rational function is locally cut out by a nonzerodivisor, hence an effective Cartier
divisor. Where `h` is regular, with representative `r ∈ Γ(X, U)`, the divisor is `V(r)`.

For an arbitrary effective Cartier divisor `D` on a scheme `X`, the invertible module `𝒪_X(D)`
carries its canonical section `1_D`, which vanishes exactly on `D`. Pulled back along any
morphism `g : Z ⟶ X`, it gives a global section of `g^* 𝒪_X(D)` vanishing exactly over `D`.

## Main definitions

* `Stacks.Divisors.zeroDivisorIdeal`: the ideal `Γ(X, U) ∩ h · Γ(X, U)`.
* `Stacks.Divisors.zeroDivisor`: the divisor of zeros of a rational function, as a closed
  subscheme.
* `Stacks.Divisors.canonicalGlobalSection`: the canonical section `1_D` of `𝒪_X(D)`, as an
  element of `Γ(𝒪_X(D), ⊤)`.

## Main results

* `Stacks.Divisors.isEffectiveCartierDivisor_zeroDivisor`: on a locally factorial integral
  scheme the divisor of zeros of a nonzero rational function is an effective Cartier divisor.
* `Stacks.Divisors.mem_supportSet_zeroDivisor_iff`: where `h` is the image of a section `r`,
  the divisor of zeros of `h` is the zero locus of `r`.
* `Stacks.Divisors.isInvertible_modulesInvertibleSheaf` and
  `Stacks.Divisors.isInvertible_pullback_modulesInvertibleSheaf`: `𝒪_X(D)` and its pullbacks
  are invertible.
* `Stacks.Divisors.exists_section_pullback_modulesInvertibleSheaf`: the pullback of `𝒪_X(D)`
  along `g` has a global section vanishing exactly over `D`.

## Implementation notes

The ideal on an open `U` is defined for every open; over the empty open, where there is no map
to the function field, it is the unit ideal. The ring of sections there is the zero ring, so this
is no choice.

## References

* [Stacks Project, Tag 08KF](https://stacks.math.columbia.edu/tag/08KF)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

section ZeroDivisor

variable {X : Scheme.{u}}

/-- On a reduced scheme the ring of sections over an empty open is the zero ring. -/
theorem subsingleton_sections_of_not_nonempty [IsReduced X] (U : X.Opens) (hU : ¬ Nonempty U) :
    Subsingleton Γ(X, U) := by
  have hbot : X.basicOpen (1 : Γ(X, U)) = ⊥ := by
    rw [Scheme.basicOpen_one]
    exact eq_bot_iff.2 fun x hx => (hU ⟨⟨x, hx⟩⟩).elim
  exact subsingleton_of_zero_eq_one ((AlgebraicGeometry.basicOpen_eq_bot_iff _).1 hbot).symm

variable [IsIntegral X]

/-- The image of a section in the function field does not change under restriction. -/
theorem germToFunctionField_map {U V : X.Opens} (i : V ⟶ U) [Nonempty U] [Nonempty V]
    (r : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map i.op r) = X.germToFunctionField U r :=
  X.presheaf.germ_res_apply i _ _ r

/-- On a nonempty open `U`, the ideal `Γ(X, U) ∩ h · Γ(X, U)` of the sections whose image in the
function field is a multiple of `h` by a section over `U`. -/
def zeroDivisorIdealOfNonempty (h : X.functionField) (U : X.Opens) [Nonempty U] :
    Ideal Γ(X, U) :=
  (Submodule.span Γ(X, U) {h}).comap (Algebra.linearMap Γ(X, U) X.functionField)

/-- Membership in `Γ(X, U) ∩ h · Γ(X, U)`, through the algebra map to the function field. -/
theorem mem_zeroDivisorIdealOfNonempty_iff' (h : X.functionField) (U : X.Opens) [Nonempty U]
    (r : Γ(X, U)) :
    r ∈ zeroDivisorIdealOfNonempty h U ↔
      ∃ s : Γ(X, U), algebraMap Γ(X, U) X.functionField s * h =
        algebraMap Γ(X, U) X.functionField r := by
  simp only [zeroDivisorIdealOfNonempty, Submodule.mem_comap, Algebra.linearMap_apply,
    Submodule.mem_span_singleton, Algebra.smul_def]

/-- A section lies in `Γ(X, U) ∩ h · Γ(X, U)` exactly when its image in the function field is
`s · h` for some section `s` over `U`. -/
theorem mem_zeroDivisorIdealOfNonempty_iff (h : X.functionField) (U : X.Opens) [Nonempty U]
    (r : Γ(X, U)) :
    r ∈ zeroDivisorIdealOfNonempty h U ↔
      ∃ s : Γ(X, U), X.germToFunctionField U r = X.germToFunctionField U s * h :=
  (mem_zeroDivisorIdealOfNonempty_iff' h U r).trans (exists_congr fun _ => eq_comm)

/-- If `h` is the image of a section `r` over a nonempty open `U`, then
`Γ(X, U) ∩ h · Γ(X, U)` is the principal ideal generated by `r`. -/
theorem zeroDivisorIdealOfNonempty_eq_span {h : X.functionField} {U : X.Opens} [Nonempty U]
    (r : Γ(X, U)) (hr : X.germToFunctionField U r = h) :
    zeroDivisorIdealOfNonempty h U = Ideal.span {r} := by
  ext t
  rw [mem_zeroDivisorIdealOfNonempty_iff, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, X.germToFunctionField_injective U (by rw [map_mul, hr, hs])⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, by rw [map_mul, hr]⟩

/-- If `Γ(X, U)` is a unique factorization domain, `U` is affine and `h = a / b` in lowest terms
with `a = IsFractionRing.num Γ(X, U) h`, then `Γ(X, U) ∩ h · Γ(X, U)` is the principal ideal
generated by `a`. -/
theorem zeroDivisorIdealOfNonempty_eq_span_num (h : X.functionField) {U : X.Opens}
    [Nonempty U] (hU : IsAffineOpen U) [UniqueFactorizationMonoid Γ(X, U)] :
    letI := functionField_isFractionRing_of_isAffineOpen X U hU
    zeroDivisorIdealOfNonempty h U = Ideal.span {IsFractionRing.num Γ(X, U) h} := by
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  have hb : algebraMap Γ(X, U) X.functionField (IsFractionRing.den Γ(X, U) h : Γ(X, U)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (IsFractionRing.den Γ(X, U) h).2
  have hab : algebraMap Γ(X, U) X.functionField (IsFractionRing.num Γ(X, U) h) =
      h * algebraMap Γ(X, U) X.functionField (IsFractionRing.den Γ(X, U) h : Γ(X, U)) := by
    rw [eq_comm, ← eq_div_iff hb]
    exact (IsFractionRing.mk'_num_den' Γ(X, U) h).symm
  have hrel := IsFractionRing.num_den_reduced Γ(X, U) h
  set a := IsFractionRing.num Γ(X, U) h
  set b : Γ(X, U) := (IsFractionRing.den Γ(X, U) h : Γ(X, U))
  ext r
  rw [mem_zeroDivisorIdealOfNonempty_iff', Ideal.mem_span_singleton]
  constructor
  · rintro ⟨s, hs⟩
    have hrb : r * b = s * a := by
      apply IsFractionRing.injective Γ(X, U) X.functionField
      rw [map_mul, map_mul, ← hs, hab]
      ring
    exact hrel.dvd_of_dvd_mul_right ⟨s, by rw [hrb, mul_comm]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c * b, ?_⟩
    rw [map_mul, map_mul, hab]
    ring

open Classical in
/-- The ideal `Γ(X, U) ∩ h · Γ(X, U)` of the divisor of zeros of `h` on an open `U`; on the
empty open, where the ring of sections is the zero ring, it is the unit ideal. -/
def zeroDivisorIdeal (h : X.functionField) (U : X.Opens) : Ideal Γ(X, U) :=
  if hU : Nonempty U then @zeroDivisorIdealOfNonempty _ _ h U hU else ⊤

/-- On a nonempty open the ideal of the divisor of zeros is `Γ(X, U) ∩ h · Γ(X, U)`. -/
theorem zeroDivisorIdeal_of_nonempty (h : X.functionField) (U : X.Opens) [hU : Nonempty U] :
    zeroDivisorIdeal h U = zeroDivisorIdealOfNonempty h U :=
  by rw [zeroDivisorIdeal, dite_eq_left hU]

/-- The ideals `Γ(X, U) ∩ h · Γ(X, U)` are compatible with localization at basic opens. -/
theorem map_zeroDivisorIdeal_basicOpen (h : X.functionField) (U : X.affineOpens)
    (f : Γ(X, U)) :
    (zeroDivisorIdeal h U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
      zeroDivisorIdeal h (X.affineBasicOpen f) := by
  by_cases hD : Nonempty (X.basicOpen f)
  · have hU : Nonempty (U : X.Opens) := ⟨⟨hD.some.1, X.basicOpen_le f hD.some.2⟩⟩
    change _ = zeroDivisorIdeal h (X.basicOpen f)
    rw [zeroDivisorIdeal_of_nonempty h (U : X.Opens),
      zeroDivisorIdeal_of_nonempty h (X.basicOpen f)]
    let := U.2.isLocalization_basicOpen f
    have halg : algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
        (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom := rfl
    have hgerm : ∀ t : Γ(X, U), X.germToFunctionField (X.basicOpen f)
        (algebraMap Γ(X, U) Γ(X, X.basicOpen f) t) = X.germToFunctionField U t :=
      fun t => germToFunctionField_map (homOfLE <| X.basicOpen_le f) t
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      obtain ⟨s, hs⟩ := (mem_zeroDivisorIdealOfNonempty_iff h _ r).1 hr
      rw [Ideal.mem_comap, ← halg]
      refine (mem_zeroDivisorIdealOfNonempty_iff h _ _).2
        ⟨algebraMap Γ(X, U) Γ(X, X.basicOpen f) s, ?_⟩
      rw [hgerm, hgerm, hs]
    · intro x hx
      obtain ⟨y, hy⟩ := (mem_zeroDivisorIdealOfNonempty_iff h _ x).1 hx
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers f) x
      obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers f) y
      change x * algebraMap _ _ (f ^ n) = algebraMap _ _ a at ha
      change y * algebraMap _ _ (f ^ m) = algebraMap _ _ b at hb
      have ha' := congrArg (X.germToFunctionField (X.basicOpen f)) ha
      have hb' := congrArg (X.germToFunctionField (X.basicOpen f)) hb
      rw [map_mul, hgerm, hgerm] at ha' hb'
      have hmem : a * f ^ m ∈ zeroDivisorIdealOfNonempty h U := by
        refine (mem_zeroDivisorIdealOfNonempty_iff h _ _).2 ⟨b * f ^ n, ?_⟩
        rw [map_mul, map_mul, ← ha', ← hb', hy]
        ring
      have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ n * f ^ m)) :=
        IsLocalization.map_units (S := Γ(X, X.basicOpen f))
          (⟨f ^ n * f ^ m, Submonoid.mul_mem _ ⟨n, rfl⟩ ⟨m, rfl⟩⟩ : Submonoid.powers f)
      refine (Ideal.mul_unit_mem_iff_mem _ hu).1 ?_
      have hm := Ideal.mem_map_of_mem (algebraMap Γ(X, U) Γ(X, X.basicOpen f)) hmem
      rw [← halg]
      convert hm using 1
      simp only [map_mul]
      rw [← ha]
      ring
  · change _ = zeroDivisorIdeal h (X.basicOpen f)
    have := subsingleton_sections_of_not_nonempty (X.basicOpen f) hD
    ext t
    rw [Subsingleton.elim t 0]
    exact iff_of_true (zero_mem _) (zero_mem _)

/-- **The divisor of zeros of a rational function.** For `h` in the function field of an
integral scheme `X`, the closed subscheme whose ideal on an affine open `U` is
`Γ(X, U) ∩ h · Γ(X, U)`. -/
def zeroDivisor (h : X.functionField) : X.IdealSheafData where
  ideal U := zeroDivisorIdeal h U
  map_ideal_basicOpen U f := map_zeroDivisorIdeal_basicOpen h U f

/-- The ideal of the divisor of zeros on an affine open. -/
@[simp] theorem zeroDivisor_ideal (h : X.functionField) (U : X.affineOpens) :
    (zeroDivisor h).ideal U = zeroDivisorIdeal h U :=
  rfl

/-- **The divisor of zeros of a nonzero rational function is an effective Cartier divisor** on
an integral scheme which is locally factorial, in the sense that every point has an affine open
neighbourhood whose ring of sections is a unique factorization domain. Near such a point, with
`h = a / b` in lowest terms, the divisor is cut out by the nonzero element `a`. -/
theorem isEffectiveCartierDivisor_zeroDivisor
    (hufd : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : Set X) ∧ UniqueFactorizationMonoid Γ(X, U))
    {h : X.functionField} (hh : h ≠ 0) :
    IsEffectiveCartierDivisor (zeroDivisor h) := by
  refine isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  obtain ⟨U, hxU, hU⟩ := hufd x
  have : Nonempty (U : X.Opens) := ⟨⟨x, hxU⟩⟩
  let := functionField_isFractionRing_of_isAffineOpen X U U.2
  refine ⟨U, U.2, hxU, IsFractionRing.num Γ(X, U) h, IsRegular.of_ne_zero ?_, ?_⟩
  · intro h0
    apply hh
    rw [← IsFractionRing.mk'_num_den' Γ(X, U) h, h0, map_zero, zero_div]
  · rw [zeroDivisor_ideal]
    change zeroDivisorIdeal h (U : X.Opens) = _
    rw [zeroDivisorIdeal_of_nonempty]
    exact zeroDivisorIdealOfNonempty_eq_span_num h U.2

/-- **Where `h` is regular, its divisor of zeros is the zero locus of a representative.** If `h`
is the image of a section `r` over a nonempty open `U`, then a point of `U` lies on the divisor
of zeros of `h` exactly when `r` vanishes there. -/
theorem mem_supportSet_zeroDivisor_iff {h : X.functionField} {U : X.Opens} [Nonempty U]
    (r : Γ(X, U)) (hr : X.germToFunctionField U r = h) {x : X} (hx : x ∈ U) :
    x ∈ (zeroDivisor h).supportSet ↔ x ∉ X.basicOpen r := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  let i : V ⟶ U := homOfLE hVU
  have hideal : (zeroDivisor h).ideal ⟨V, hV⟩ = Ideal.span {X.presheaf.map i.op r} := by
    rw [zeroDivisor_ideal]
    change zeroDivisorIdeal h V = _
    rw [zeroDivisorIdeal_of_nonempty]
    exact zeroDivisorIdealOfNonempty_eq_span _ ((germToFunctionField_map i r).trans hr)
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨V, hV⟩) hxV, hideal,
    Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, Scheme.basicOpen_res]
  simp [hxV]

end ZeroDivisor

section CanonicalSectionPullback

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The canonical section `1_D` of `𝒪_X(D)`, as a global section. -/
def canonicalGlobalSection : Γ(modulesInvertibleSheaf D, ⊤) :=
  (canonicalSections D).eval (op ⊤)

variable [IsEffectiveCartierDivisor D]

/-- **`𝒪_X(D)` is invertible**, at the index `X.presheaf`, `X.ringCatSheaf.2`. -/
instance isInvertible_modulesInvertibleSheaf :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (modulesInvertibleSheaf D) :=
  stacksIsInvertible_invertibleSheaf D

/-- **The pullback of `𝒪_X(D)` along any morphism is invertible.** -/
theorem isInvertible_pullback_modulesInvertibleSheaf {Z : Scheme.{u}} (g : Z ⟶ X) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property
      ((Scheme.Modules.pullback g).obj (modulesInvertibleSheaf D)) :=
  @Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback Z.toRingedSpace
    X.toRingedSpace g.toLRSHom.toShHom (modulesInvertibleSheaf D)
    (isInvertible_modulesInvertibleSheaf D)

/-- The canonical section `1_D` vanishes exactly on `D`, in the spelling
`Stacks.Ample.nonvanishingLocus` of the nonvanishing locus of a global section. -/
theorem nonvanishingLocus_canonicalGlobalSection :
    Stacks.Ample.nonvanishingLocus (modulesInvertibleSheaf D)
        (canonicalGlobalSection D) = (D.supportSet)ᶜ := by
  ext x
  rw [← nonvanishingLocus_canonicalSections D, Stacks.Ample.mem_nonvanishingLocus_iff,
    Stacks.NonvanishingPullback.mem_maximalSmul_iff]
  exact Iff.rfl

/-- **The pullback of the canonical section vanishes exactly over `D`.** For `g : Z ⟶ X`, the
pullback of `1_D` to `g^* 𝒪_X(D)` does not vanish at `z` exactly when `g z ∉ D`. -/
theorem nonvanishingLocus_pullbackGlobalSections_canonicalSections {Z : Scheme.{u}}
    (g : Z ⟶ X) :
    Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback g).obj (modulesInvertibleSheaf D))
        (pullbackGlobalSections g (modulesInvertibleSheaf D) (canonicalGlobalSection D)) =
      g.base ⁻¹' (D.supportSet)ᶜ := by
  rw [← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections,
    nonvanishingLocus_canonicalGlobalSection]

/-- **The pullback of `𝒪_X(D)` has a global section vanishing exactly over `D`.** -/
theorem exists_section_pullback_modulesInvertibleSheaf {Z : Scheme.{u}} (g : Z ⟶ X) :
    ∃ s : Γ((Scheme.Modules.pullback g).obj (modulesInvertibleSheaf D), ⊤), ∀ z : Z,
      z ∈ Stacks.Ample.nonvanishingLocus
          ((Scheme.Modules.pullback g).obj (modulesInvertibleSheaf D)) s ↔
        g z ∉ D.supportSet :=
  ⟨pullbackGlobalSections g (modulesInvertibleSheaf D) (canonicalGlobalSection D),
    fun z => by
    rw [nonvanishingLocus_pullbackGlobalSections_canonicalSections]
    exact Iff.rfl⟩

end CanonicalSectionPullback

end Stacks.Divisors

end
