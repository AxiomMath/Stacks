module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeExample
public import StacksFrontier.AlgebraicGeometry.HomogeneousAwayMapCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.IdealOfClosedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The curve of [Stacks, Tag 0CD1] exists: `Z`, `i` and `I(Z) = (F)` are constructed

Every statement of [Stacks, Tag 0CD1] in this repository takes the curve as *input*: a scheme `Z`,
a closed immersion `i : Z ⟶ 𝐏²_k`, and the hypothesis
`I(Z) = (F)` for `F = T₁²T₀ - T₂³ + aT₀³`. This file produces that data, so those three
hypotheses stop being hypotheses.

## What is constructed

`Z` is `Proj` of the graded quotient `k[T₀, T₁, T₂] ⧸ (F)` and `i` is the canonical morphism to
`Proj k[T₀, T₁, T₂]`:

* `Stacks.Curves.InseparableGenus.planeCubicIdeal`: `(F)` as a homogeneous ideal;
* `Stacks.Curves.InseparableGenus.planeCubicCurve`: `Z = Proj (k[T₀, T₁, T₂] ⧸ (F))`;
* `Stacks.Curves.InseparableGenus.planeCubicEmbedding`: `i : Z ⟶ 𝐏²_k`, a closed immersion;
* `Stacks.Curves.InseparableGenus.idealOfClosedSubscheme_planeCubicEmbedding`: **`I(Z) = (F)`**;
* `Stacks.Curves.InseparableGenus.nonempty_planeCubicCurve`: `Z` is nonempty;
* `Stacks.Curves.InseparableGenus.isRegular_planeCubicCurve`: `Z` is nonsingular.

## The identification `I(Z) = (F)`, which is the content

The ideal of Tag 0BXK is defined by the vanishing of twisted global sections *pulled back* to
`Z`, so identifying it with the ideal one quotiented by is not a formality — it is the direction
of Tag 0BXK that `StacksFrontier/AlgebraicGeometry/ProjSaturation/Quotient.lean` records as not
computed, because in general it asks for the comparison map
`(Proj.map ψ)^* 𝒪(n) ⟶ 𝒪(n)` of [Stacks, Tag 01N0] part (3).

What replaces that comparison map here is the **chart kernel**. On the standard open `D₊(f)` of a
homogeneous `f` of positive degree, the map on sections induced by `Proj.map ψ` is
`HomogeneousLocalization.Away.map ψ f`
(`Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff`), whose kernel is computed
elementwise by `Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff`: the
fraction `a / f ^ n` dies exactly when some `f ^ k · a` lies in the kernel of `ψ`, which for a
graded quotient map is the ideal itself. That is
`Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projQuotientHom_iff`, the only general
statement proved here, and the two inclusions come out of it:

* `(F) ⊆ I(Z)` is the chartwise criterion
  `mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker`
  with `k = 0`: `F` itself lies in `(F)`. This is
  `Stacks.ProjQuotientChartIdeal.mem_idealOfClosedSubscheme_projQuotientHom`, and it holds for
  every homogeneous element of every homogeneous ideal.
* `I(Z) ⊆ (F)` is where irreducibility of `F` enters. A homogeneous equation `b` for `Z` has
  `F ∣ T₀ ^ p · b` and `F ∣ T₁ ^ q · b` by the chart kernel on `D₊(T₀)` and `D₊(T₁)`, and the two
  coordinates are coprime, so `F ∣ b`. This is the same coprimality step as in
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.projectivePlane_isCurve_iff_irreducible`.

Irreducibility is not needed for the inclusion `(F) ⊆ I(Z)`; it is needed for the reverse one,
and that is as it should be — for `F = G ^ 2` the quotient `Proj (k[T] ⧸ (G ^ 2))` has `G` as an
equation, so `I(Z)` is strictly larger than `(F)`.

## The other two inputs

The remaining two inputs of the Tag 0CD1 statements,

* `HasNoEmbeddedPoints Z`;
* `∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1`,

are proved for this curve in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeCurveDimension.lean`, by computing
the dimension on the two charts `Z ∩ D₊(T₀)` and `Z ∩ D₊(T₁)` and deducing the absence of embedded
points from the Cohen–Macaulayness of a regular scheme.

## References

* [Stacks Project, Tag 0CD1](https://stacks.math.columbia.edu/tag/0CD1)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj (idealOfClosedSubscheme chartFraction
  mem_idealOfClosedSubscheme chartFraction_mem_ker_app_of_mem_idealOfClosedSubscheme
  mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker)
open Stacks.RingTheory.HomogeneousQuotient (quotientGrading quotientMk)

universe u

namespace Stacks.ProjQuotientChartIdeal

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (𝒮 : ℕ → Submodule R S)
  [_root_.GradedAlgebra 𝒮] (I : HomogeneousIdeal 𝒮)

/-! ### `Proj` of a graded quotient as a closed subscheme, for an arbitrary homogeneous ideal -/

/-- **The canonical morphism `Proj (𝒮 ⧸ I) ⟶ Proj 𝒮`**, for `I` an arbitrary homogeneous
ideal.
This is `Stacks.ClosedSubschemeProjQuotient.ambientHom` with the ideal of a closed subscheme
replaced by a prescribed one; the two agree by
`Stacks.ProjQuotientChartIdeal.ambientHom_eq_projMap`. -/
@[ega "II 2.9.2"]
def projQuotientHom : AlgebraicGeometry.Proj (quotientGrading 𝒮 I) ⟶ AlgebraicGeometry.Proj 𝒮 :=
  AlgebraicGeometry.Proj.map (quotientMk 𝒮 I) (irrelevant_le_map_quotientMk 𝒮 I)

/-- `Proj` of the quotient by a homogeneous ideal is a closed subscheme of `Proj 𝒮`: the quotient
map is surjective. -/
@[ega "II 2.9.2" "(i), special case"]
instance isClosedImmersion_projQuotientHom : IsClosedImmersion (projQuotientHom 𝒮 I) :=
  AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective _
    fun y => Ideal.Quotient.mk_surjective y

/-- **The chart kernel of `Proj (𝒮 ⧸ I) ⟶ Proj 𝒮`.** On the standard open of a homogeneous
`f` of positive degree, the degree-zero fraction `a / f ^ n` is carried to zero exactly when some
`f ^ k · a` lies in `I`.

This is `Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_ambientHom_iff` for a prescribed
ideal instead of the ideal of a closed subscheme, and unlike that statement it needs no
hypothesis beyond homogeneity: the kernel of a graded quotient map *is* the ideal, with no
saturation step. -/
theorem awayToSection_mem_ker_app_projQuotientHom_iff {m : ℕ} {f : S} (hf : f ∈ 𝒮 m) (hm : 0 < m)
    (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • m)) :
    (AlgebraicGeometry.Proj.awayToSection 𝒮 f).hom (Away.mk 𝒮 hf n a ha) ∈
        RingHom.ker ((projQuotientHom 𝒮 I).app (AlgebraicGeometry.Proj.basicOpen 𝒮 f)).hom ↔
      ∃ k : ℕ, f ^ k * a ∈ I.toIdeal := by
  rw [projQuotientHom, awayToSection_mem_ker_app_projMap_iff _ _ hf hm,
    Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff]
  exact exists_congr fun k => Ideal.Quotient.eq_zero_iff_mem

/-- **A homogeneous element of `I` is an equation for `Proj (𝒮 ⧸ I)`.** Over a graded algebra
generated in degree one, `I` is contained in the Tag 0BXK ideal of equations of the closed
subscheme it cuts out.

This is the chartwise criterion
`mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker`
fed with the chart kernel at `k = 0`. The reverse inclusion is false in general — the ideal of
equations is the saturation of `I`, which for `I = (G ^ 2)` already contains `G`. -/
theorem mem_idealOfClosedSubscheme_projQuotientHom
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) {m : ℕ} (z : 𝒮 m)
    (hz : (z : S) ∈ I.toIdeal) :
    (z : S) ∈ idealOfClosedSubscheme 𝒮 (projQuotientHom 𝒮 I) := by
  have hz1 : (z : S) ∈ 𝒮 (m • 1) := by simp
  refine mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker 𝒮 Nat.one_pos
    (fun g : 𝒮 1 => (g : S)) (fun g => g.2)
    (Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top 𝒮 hgen)
    (projQuotientHom 𝒮 I) (m := m) ⟨(z : S), hz1⟩ fun g => ?_
  exact (awayToSection_mem_ker_app_projQuotientHom_iff 𝒮 I g.2 Nat.one_pos m (z : S) hz1).mpr
    ⟨0, by simpa using hz⟩

/-- **The equations of `Proj (𝒮 ⧸ I)` are the elements of `I` up to a power of a coordinate.**
A homogeneous equation `b` for the closed subscheme cut out by `I` has `f ^ k · b ∈ I` for some
`k`, for every homogeneous `f` of positive degree. The power of `f` cannot be removed: it is the
saturation that separates `I` from the ideal of equations. -/
theorem exists_pow_mul_mem_of_mem_idealOfClosedSubscheme_projQuotientHom
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) {f : S} (hf : f ∈ 𝒮 1) {m : ℕ} (b : 𝒮 m)
    (hb : (b : S) ∈ idealOfClosedSubscheme 𝒮 (projQuotientHom 𝒮 I)) :
    ∃ k : ℕ, f ^ k * (b : S) ∈ I.toIdeal := by
  have inst : ∀ j : ℤ, SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒮).sheaf.obj
      (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.property
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒮 j) :=
    AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf 𝒮 hgen
  have hb1 : (b : S) ∈ 𝒮 (m • 1) := by simp
  exact (awayToSection_mem_ker_app_projQuotientHom_iff 𝒮 I hf Nat.one_pos m (b : S) hb1).mp
    (chartFraction_mem_ker_app_of_mem_idealOfClosedSubscheme 𝒮 hf Nat.one_pos
      (projQuotientHom 𝒮 I) m ⟨(b : S), hb1⟩ hb)

end Stacks.ProjQuotientChartIdeal

namespace Stacks.Curves.InseparableGenus

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.ProjQuotientChartIdeal (projQuotientHom
  awayToSection_mem_ker_app_projQuotientHom_iff mem_idealOfClosedSubscheme_projQuotientHom
  exists_pow_mul_mem_of_mem_idealOfClosedSubscheme_projQuotientHom)

/-! ### Divisibility from two coprime coordinates -/

/-- A polynomial dividing both `T₀ ^ n · b` and `T₁ ^ m · b` divides `b`: the two coordinates are
coprime. -/
theorem dvd_of_dvd_X_zero_pow_mul_of_dvd_X_one_pow_mul (k : Type u) [Field k]
    {b F : MvPolynomial (Fin 3) k} {n m : ℕ} (h0 : F ∣ MvPolynomial.X 0 ^ n * b)
    (h1 : F ∣ MvPolynomial.X 1 ^ m * b) : F ∣ b := by
  let _ := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial (Fin 3) k)
  have h : IsRelPrime (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) k)
      (MvPolynomial.X 1) :=
    MvPolynomial.X_prime.irreducible.isRelPrime_iff_not_dvd.mpr (by simp [MvPolynomial.X_dvd_X])
  exact ((h.pow (m := n) (n := m)) (gcd_dvd_left _ _) (gcd_dvd_right _ _)).dvd_mul_left.mp
    ((gcd_mul_right' b (MvPolynomial.X (0 : Fin 3) ^ n) (MvPolynomial.X 1 ^ m)).dvd_iff_dvd_right.mp
      (dvd_gcd h0 h1))

/-! ### The homogeneous ideal of the cubic -/

/-- **The equation of [Stacks, Tag 0CD1] as a homogeneous ideal.** `F = T₁²T₀ - T₂³ + aT₀³` is
homogeneous of degree three, so the principal ideal it generates is a homogeneous ideal of
`k[T₀, T₁, T₂]`; that is the shape `Proj` of a graded quotient takes. -/
def planeCubicIdeal (k : Type u) [Field k] (a : k) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) k) :=
  ⟨Ideal.span {planeCubic k a},
    Ideal.homogeneous_span _ _ fun _ hx => ⟨3, (Set.mem_singleton_iff.mp hx) ▸
      (MvPolynomial.mem_homogeneousSubmodule 3 _).2 (planeCubic_isHomogeneous k a)⟩⟩

/-- The underlying ideal of `planeCubicIdeal k a` is the principal ideal generated by
`planeCubic k a`. -/
@[simp] theorem toIdeal_planeCubicIdeal (k : Type u) [Field k] (a : k) :
    (planeCubicIdeal k a).toIdeal = Ideal.span {planeCubic k a} := rfl

/-- The homogeneous ideal `planeCubicIdeal k a` is prime. -/
theorem isPrime_planeCubicIdeal (k : Type u) [Field k] (a : k) :
    (planeCubicIdeal k a).toIdeal.IsPrime := by
  rw [toIdeal_planeCubicIdeal, Ideal.span_singleton_prime (planeCubic_ne_zero k a)]
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp (planeCubic_irreducible k a)

/-- The cubic divides no coordinate: it is irreducible of degree three, so if it divided a
coordinate the two would be associated, and `T₀` and `T₁` both divide `F` only if `F` vanishes at
`(0 : 0 : 1)`, where it takes the value `-1`. -/
theorem planeCubic_notDvd_X (k : Type u) [Field k] (a : k) {j : Fin 3} (hj : j = 0 ∨ j = 1) :
    ¬ planeCubic k a ∣ MvPolynomial.X j := by
  intro hdvd
  obtain ⟨q, hq⟩ := ((planeCubic_irreducible k a).associated_of_dvd
    (MvPolynomial.X_prime (R := k) (i := j)).irreducible hdvd).symm.dvd
  have hev := congrArg
    (MvPolynomial.eval (fun i : Fin 3 => if i = 2 then (1 : k) else 0)) hq
  rcases hj with rfl | rfl <;> simp [planeCubic] at hev

/-! ### The curve, the embedding, and the ideal of equations -/

/-- **The curve of [Stacks, Tag 0CD1]**: `Z = AlgebraicGeometry.Proj (k[T₀, T₁, T₂] ⧸ (F))` for
`F = T₁²T₀ - T₂³ + aT₀³`. -/
abbrev planeCubicCurve (k : Type u) [Field k] (a : k) : Scheme.{u} :=
  AlgebraicGeometry.Proj
    (quotientGrading (MvPolynomial.homogeneousSubmodule (Fin 3) k) (planeCubicIdeal k a))

/-- **The embedding of the curve of [Stacks, Tag 0CD1] in `𝐏²_k`**, the canonical morphism out of
`Proj` of the graded quotient. It is a closed immersion, by
`Stacks.ProjQuotientChartIdeal.isClosedImmersion_projQuotientHom`. -/
abbrev planeCubicEmbedding (k : Type u) [Field k] (a : k) :
    planeCubicCurve k a ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k) :=
  projQuotientHom (MvPolynomial.homogeneousSubmodule (Fin 3) k) (planeCubicIdeal k a)

/-- **The curve of [Stacks, Tag 0CD1] is nonempty.** The quotient by `(F)` is a domain, since `F`
is irreducible, so the zero ideal is a point of its projective spectrum; it is a *relevant* point
because `T₀` survives in the quotient, `F` being of degree three and irreducible. -/
theorem nonempty_planeCubicCurve (k : Type u) [Field k] (a : k) :
    Nonempty (planeCubicCurve k a) := by
  have := isPrime_planeCubicIdeal k a
  have : IsDomain (MvPolynomial (Fin 3) k ⧸ (planeCubicIdeal k a).toIdeal) :=
    Ideal.Quotient.isDomain _
  refine ⟨⟨⊥, by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot, fun hle => ?_⟩⟩
  have hmem : Ideal.Quotient.mk (planeCubicIdeal k a).toIdeal (MvPolynomial.X 0) ∈
      (⊥ : HomogeneousIdeal
        (quotientGrading (MvPolynomial.homogeneousSubmodule (Fin 3) k) (planeCubicIdeal k a))) :=
    hle (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
      (Stacks.RingTheory.HomogeneousQuotient.quotientGrading_mk_mem _ _
        (MvPolynomial.isHomogeneous_X k 0)))
  exact planeCubic_notDvd_X k a (Or.inl rfl) (Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_bot.mp (HomogeneousIdeal.mem_iff.mpr hmem))))

/-- **The homogeneous ideal of equations of the curve of [Stacks, Tag 0CD1] is `(F)`.**

This is the hypothesis `hI` of every statement of the example in this repository, discharged for
the explicit curve `Proj (k[T₀, T₁, T₂] ⧸ (F))`.

The inclusion `(F) ⊆ I(Z)` is
`Stacks.ProjQuotientChartIdeal.mem_idealOfClosedSubscheme_projQuotientHom`, which holds for every
homogeneous ideal. The inclusion `I(Z) ⊆ (F)` is where irreducibility enters: a homogeneous
equation `b` has `F ∣ T₀ ^ p · b` and `F ∣ T₁ ^ q · b` on the two charts, and `T₀` and `T₁` are
coprime, so `F ∣ b`. -/
theorem idealOfClosedSubscheme_planeCubicEmbedding (k : Type u) [Field k] (a : k) :
    idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k)
        (planeCubicEmbedding k a) =
      Ideal.span {planeCubic k a} := by
  have hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin 3) k
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
  · rintro - ⟨n, b, rfl, hzero⟩
    have hb : (b : MvPolynomial (Fin 3) k) ∈
        idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k)
          (planeCubicEmbedding k a) :=
      mem_idealOfClosedSubscheme _ _ n b hzero
    have hdvd := fun j : Fin 3 => (exists_pow_mul_mem_of_mem_idealOfClosedSubscheme_projQuotientHom
      _ (planeCubicIdeal k a) hgen (MvPolynomial.isHomogeneous_X k j) b hb).imp
      fun _ => Ideal.mem_span_singleton.mp
    obtain ⟨p, hp⟩ := hdvd 0
    obtain ⟨q, hq⟩ := hdvd 1
    exact Ideal.mem_span_singleton.mpr
      (dvd_of_dvd_X_zero_pow_mul_of_dvd_X_one_pow_mul k hp hq)
  · exact mem_idealOfClosedSubscheme_projQuotientHom _ (planeCubicIdeal k a) hgen
      (⟨planeCubic k a, (MvPolynomial.mem_homogeneousSubmodule 3 _).2
        (planeCubic_isHomogeneous k a)⟩ : MvPolynomial.homogeneousSubmodule (Fin 3) k 3)
      (Ideal.mem_span_singleton_self _)

/-- **The curve of [Stacks, Tag 0CD1] is nonsingular**, with no hypothesis left over:
`Stacks.Curves.InseparableGenus.isRegular_of_idealOfClosedSubscheme_eq_span` at the explicit
curve, whose ideal of equations is `(F)` by
`Stacks.Curves.InseparableGenus.idealOfClosedSubscheme_planeCubicEmbedding`. -/
theorem isRegular_planeCubicCurve (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) :
    IsRegular (planeCubicCurve k a) :=
  isRegular_of_idealOfClosedSubscheme_eq_span a ha (planeCubicEmbedding k a)
    (idealOfClosedSubscheme_planeCubicEmbedding k a)

end Stacks.Curves.InseparableGenus

end
