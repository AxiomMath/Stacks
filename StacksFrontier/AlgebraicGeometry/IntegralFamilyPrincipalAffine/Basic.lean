module

public import StacksFrontier.AlgebraicGeometry.IntegralFamilyFiniteRange.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAffineNonvanishing.Basic

/-!
# An integral family of points factors through an affine principal open

[Stacks, Tag 0E21] asserts: let `X` be a scheme carrying an ample invertible module `L`, let
`W ⊆ X` be open, let `k` be a field and `A` a `k`-algebra integral over `k`; then for every
morphism `Spec A ⟶ W` there are an `n > 0` and a global section `s` of `L ^⊗ n` such that `X_s`
is affine, `X_s ⊆ W`, and `Spec A ⟶ W` **factors through** `X_s`.

The source proves this by absolute Noetherian approximation: replace `X` by a stage of a
finite-type approximation, where the image of `Spec A` is a finite set, and apply
[Stacks, Tag 09NV]. This file proves the part of that argument which does **not** go through the
approximation, namely the passage from a *finite* image to the conclusion of Tag 0E21, including
the factorization of the morphism, which Tag 09NV does not provide. It rests on

* `Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite`, an
  affine principal open containing a finite set and contained in `W`, which is Tag 09NV stated over
  `sections` as
  `Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite_sections`,
  and
* `Stacks.IntegralFamilyFiniteRange.finite_range_of_integral_of_locallyOfFinitePresentation`: the
  image of `Spec A ⟶ T` is finite when `A` is integral over a field and `T` is locally of finite
  presentation over the terminal scheme.

## Main results

* `Stacks.IntegralFamilyPrincipalAffine.exists_affine_powNonvanishingOpen_lift_of_finite_range`:
  the reduction with no integrality hypothesis at all. For *any* scheme `Y` and morphism
  `g : Y ⟶ X` with finite image contained in `W`, there are `n ≥ 1` and `s` with `X_s` affine,
  `X_s ⊆ W`, and `g` factoring through `X_s`.
* `Stacks.IntegralFamilyPrincipalAffine.exists_affine_powNonvanishingOpen_factors_of_finite_range`:
  the same with the morphism given into `W`, and the factorization stated as a morphism to `X_s`
  over `W`. This is the shape of the conclusion of Tag 0E21.
* `Stacks.IntegralFamilyPrincipalAffine.exists_affine_powNonvanishingOpen_factors_of_integral`:
  **Tag 0E21 for an `X` locally of finite presentation over the terminal scheme.** The
  finite-presentation hypothesis is the one the approximation is there to supply and is the only
  hypothesis here that Tag 0E21 does not have.
* `exists_affine_powNonvanishingOpen_factors_of_integral_of_finiteType`, in the same namespace:
  the same with "of finite type over the terminal scheme" in place of "locally of finite
  presentation", which is the form the stages of a finite-type approximation satisfy — they are
  of finite type over `Spec ℤ` by construction, and `ℤ` is Noetherian, so Tag 01TX upgrades this.

## Implementation notes

Tag 0E21 is stated for an **arbitrary** scheme `X`. Every result here carries a hypothesis the tag
does not have — a finiteness hypothesis on the image, or a finite-presentation hypothesis on `X` —
so none of them carries the tag.

## References

* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Ample Stacks.AmpleTheory

universe v u

namespace Stacks.IntegralFamilyPrincipalAffine

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **The reduction of [Stacks, Tag 0E21] to a finite image, with the factorization.**

Let `L` be an ample invertible module on `X` and `W` an open of `X`. A morphism `g : Y ⟶ X` whose
set-theoretic image is finite and contained in `W` factors through an affine nonvanishing open
`X_s ⊆ W` of a global section of a positive tensor power of `L`. -/
theorem exists_affine_powNonvanishingOpen_lift_of_finite_range (hL : IsAmple X L) (W : X.Opens)
    {Y : Scheme.{u}} (g : Y ⟶ X) (hfin : (Set.range g.base).Finite)
    (hgW : Set.range g.base ⊆ (W : Set X)) :
    ∃ (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)),
      1 ≤ n ∧ IsAffineOpen (powNonvanishingOpen X L n s) ∧
        (powNonvanishingOpen X L n s : Set X) ⊆ (W : Set X) ∧
          ∃ b : Y ⟶ (powNonvanishingOpen X L n s).toScheme,
            b ≫ (powNonvanishingOpen X L n s).ι = g := by
  obtain ⟨n, hn, s, haff, hEs, hsW⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite
      L hL hfin W hgW
  refine ⟨n, s, hn, haff, hsW, ?_⟩
  have hr : Set.range g ⊆ Set.range (powNonvanishingOpen X L n s).ι := by
    rw [Scheme.Opens.range_ι]
    exact hEs
  exact ⟨IsOpenImmersion.lift _ g hr, IsOpenImmersion.lift_fac _ g hr⟩

/-- **[Stacks, Tag 0E21] for a morphism with finite image.**

The conclusion is the tag's own: an `n ≥ 1`, a global section `s` of `L ^⊗ n` with `X_s` affine
and `X_s ≤ W`, and a factorization of the given `Y ⟶ W` through `X_s` *as a morphism over `W`*.
The hypothesis the tag does not have is the finiteness of the image. -/
theorem exists_affine_powNonvanishingOpen_factors_of_finite_range (hL : IsAmple X L) (W : X.Opens)
    {Y : Scheme.{u}} (a : Y ⟶ W.toScheme) (hfin : (Set.range (a ≫ W.ι).base).Finite) :
    ∃ (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤))
        (hle : powNonvanishingOpen X L n s ≤ W),
      1 ≤ n ∧ IsAffineOpen (powNonvanishingOpen X L n s) ∧
        ∃ b : Y ⟶ (powNonvanishingOpen X L n s).toScheme, b ≫ X.homOfLE hle = a := by
  have hgW : Set.range (a ≫ W.ι).base ⊆ (W : Set X) := by
    have h : Set.range (a ≫ W.ι) ⊆ Set.range W.ι := by
      rintro x ⟨y, rfl⟩
      exact ⟨a y, (Scheme.Hom.comp_apply a W.ι y).symm⟩
    rw [Scheme.Opens.range_ι] at h
    exact h
  obtain ⟨n, s, hn, haff, hsW, b, hb⟩ :=
    exists_affine_powNonvanishingOpen_lift_of_finite_range L hL W (a ≫ W.ι) hfin hgW
  refine ⟨n, s, SetLike.coe_subset_coe.mp hsW, hn, haff, b, ?_⟩
  rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι]
  exact hb

/-- **[Stacks, Tag 0E21] for an `X` locally of finite presentation over the terminal scheme.**

Let `k` be a field, `A` a `k`-algebra integral over `k`, `L` an ample invertible module on `X`
and `W` an open of `X`. Then every `Spec A ⟶ W` factors through an affine nonvanishing open
`X_s ⊆ W` of a global section of a positive tensor power of `L`.

The finite-presentation hypothesis on `X` is the only hypothesis here that Tag 0E21 does not have;
in the source it is supplied by the absolute Noetherian approximation of [Stacks, Tag 01ZA]. -/
theorem exists_affine_powNonvanishingOpen_factors_of_integral (k : Type v) (A : Type u) [Field k]
    [CommRing A] [Algebra k A] [Algebra.IsIntegral k A] (hL : IsAmple X L)
    [LocallyOfFinitePresentation (terminal.from X)] (W : X.Opens)
    (a : Spec (CommRingCat.of A) ⟶ W.toScheme) :
    ∃ (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤))
        (hle : powNonvanishingOpen X L n s ≤ W),
      1 ≤ n ∧ IsAffineOpen (powNonvanishingOpen X L n s) ∧
        ∃ b : Spec (CommRingCat.of A) ⟶ (powNonvanishingOpen X L n s).toScheme,
          b ≫ X.homOfLE hle = a :=
  exists_affine_powNonvanishingOpen_factors_of_finite_range L hL W a
    (Stacks.IntegralFamilyFiniteRange.finite_range_of_integral_of_locallyOfFinitePresentation
      k A X (a ≫ W.ι))

/-- **[Stacks, Tag 0E21] for an `X` of finite type over the terminal scheme**, which is the shape
the stages of an absolute Noetherian approximation have: they are of finite type over `Spec ℤ` by
construction, and `ℤ` being Noetherian they are then locally of finite presentation over it by
[Stacks, Tag 01TX]. -/
theorem exists_affine_powNonvanishingOpen_factors_of_integral_of_finiteType (k : Type v)
    (A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.IsIntegral k A] (hL : IsAmple X L)
    [LocallyOfFiniteType (terminal.from X)] [QuasiCompact (terminal.from X)] (W : X.Opens)
    (a : Spec (CommRingCat.of A) ⟶ W.toScheme) :
    ∃ (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤))
        (hle : powNonvanishingOpen X L n s ≤ W),
      1 ≤ n ∧ IsAffineOpen (powNonvanishingOpen X L n s) ∧
        ∃ b : Spec (CommRingCat.of A) ⟶ (powNonvanishingOpen X L n s).toScheme,
          b ≫ X.homOfLE hle = a :=
  let _ := Stacks.IntegralFamilyFiniteRange.locallyOfFinitePresentation_of_finiteType X
  exists_affine_powNonvanishingOpen_factors_of_integral L k A hL W a

end Stacks.IntegralFamilyPrincipalAffine

end
