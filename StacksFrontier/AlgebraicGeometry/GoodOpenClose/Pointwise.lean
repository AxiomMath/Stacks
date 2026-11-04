module

public import StacksFrontier.AlgebraicGeometry.ProjShared.InvertibleLocus
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist

/-!
# A unit value of a product of twisted sections puts the point in the ratio locus

Let `S` be a graded ring, `X = Proj(S)` and `d` a natural number, and let

`ratioLocus 𝒮 d = ⋃ D₊(f g)`,  `f`, `g` homogeneous,  `deg f = deg g + d`.

A section of `𝒪(a)` over an open containing `x` has, near `x`, the form `f / g` with `g`
homogeneous of some degree `n`, not vanishing at `x`, and `f` homogeneous of degree `n + a`. If
the product of the value at `x` of a section of `𝒪(d)` with the value at `x` of a section of
`𝒪(b)`, for any `b`, is a unit of the local ring at `x`, then `x ∈ ratioLocus 𝒮 d`.

## Main results

* `Stacks.AlgebraicGeometry.GoodOpenClose.exists_localization_mk_of_mem`: the local fraction of
  a section of an associated module sheaf at a point of its domain, with the numerator read in
  the integer-extended grading.
* `Stacks.AlgebraicGeometry.GoodOpenClose.mem_ratioLocus_of_isUnit_mul`: one product with a unit
  value puts `x` in the ratio locus.
* `Stacks.AlgebraicGeometry.GoodOpenClose.mem_ratioLocus_of_isUnit_sum` and
  `Stacks.AlgebraicGeometry.GoodOpenClose.mem_ratioLocus_of_sum_eq_one`: a finite sum of such
  products with a unit value, or with value `1`, puts `x` in the ratio locus.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.GoodOpenClose

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The underlying ideal of the homogeneous prime ideal of a point of `Proj` is prime. -/
local instance instIsPrime (x : ProjectiveSpectrum.top 𝒮) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- The local fraction of a section of the sheaf associated to a twist of the regular module, at
a point of its domain: numerator homogeneous of integer degree `n + a`, denominator homogeneous
of degree `n` and not vanishing at the point. -/
theorem exists_localization_mk_of_mem {a : ℤ} {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (ς : moduleSections 𝒮 (twistGrading (S := S) 𝒮 a) W)
    {x : ProjectiveSpectrum.top 𝒮} (hx : x ∈ W) :
    ∃ (n : ℕ) (f : S) (g : x.asHomogeneousIdeal.toIdeal.primeCompl),
      f ∈ integerGrading (S := S) 𝒮 ((n : ℤ) + a) ∧ (g : S) ∈ 𝒮 n ∧
        ς.1 ⟨x, hx⟩ = Localization.mk f g := by
  obtain ⟨V, hxV, i, n, m, s, hm, hs, hn, heq⟩ := ς.2 ⟨x, hx⟩
  exact ⟨n, m, ⟨s, hn ⟨x, hxV⟩⟩, hm, hs, heq ⟨x, hxV⟩⟩

/-- A homogeneous element whose image in the local ring at `x` is a unit does not vanish
at `x`. -/
theorem notMem_of_isUnit_mk {x : ProjectiveSpectrum.top 𝒮} (f : S)
    (g : x.asHomogeneousIdeal.toIdeal.primeCompl)
    (h : IsUnit (Localization.mk f g : Localization.AtPrime x.asHomogeneousIdeal.toIdeal)) :
    f ∉ x.asHomogeneousIdeal := by
  have hmap : IsUnit (algebraMap S (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) f) := by
    rw [Localization.mk_eq_mk'] at h
    have hmul := h.mul
      (IsLocalization.map_units (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) g)
    rwa [IsLocalization.mk'_spec] at hmul
  exact (IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) x.asHomogeneousIdeal.toIdeal f).mp hmap

/-- **One product with a unit value suffices.** If the value at `x` of a section of `𝒪(d)` times
the value at `x` of a section of `𝒪(b)` is a unit of the local ring at `x`, then `x` lies in the
ratio locus for `d`. Nothing is assumed about `b`. -/
theorem mem_ratioLocus_of_isUnit_mul {d : ℕ} {a b : ℤ} (ha : a = (d : ℤ))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} {x : ProjectiveSpectrum.top 𝒮} (hx : x ∈ W)
    (ς : moduleSections 𝒮 (twistGrading (S := S) 𝒮 a) W)
    (τ : moduleSections 𝒮 (twistGrading (S := S) 𝒮 b) W)
    (h : IsUnit (ς.1 ⟨x, hx⟩ * τ.1 ⟨x, hx⟩)) :
    x ∈ ProjShared.ratioLocus 𝒮 d := by
  obtain ⟨n, f, g, hf, hg, hς⟩ := exists_localization_mk_of_mem 𝒮 ς hx
  obtain ⟨n', f', g', hf', -, hτ⟩ := exists_localization_mk_of_mem 𝒮 τ hx
  have hpair : IsUnit ((Localization.mk f g * Localization.mk f' g' :
      Localization.AtPrime x.asHomogeneousIdeal.toIdeal)) := by
    rw [← hς, ← hτ]; exact h
  rw [Localization.mk_mul] at hpair
  have hprod : IsUnit (Localization.mk (f * f') (g * g') :
      Localization.AtPrime x.asHomogeneousIdeal.toIdeal) := hpair
  have hffx : f * f' ∉ x.asHomogeneousIdeal := notMem_of_isUnit_mk 𝒮 _ _ hprod
  have hfx : f ∉ x.asHomogeneousIdeal := fun hmem =>
    hffx (Ideal.mul_mem_right _ _ hmem)
  have hfdeg : f ∈ 𝒮 (n + d) := by
    rw [ha, show (n : ℤ) + (d : ℤ) = ((n + d : ℕ) : ℤ) by push_cast; ring,
      integerGrading_natCast] at hf
    exact hf
  exact (ProjShared.mem_ratioLocus_iff 𝒮 d x).mpr ⟨n, f, g, hfdeg, hg, hfx, g.2⟩

/-- A finite sum of products of values of sections of `𝒪(d)` and `𝒪(b)` at `x` which is a unit
of the local ring at `x` puts `x` in the ratio locus. -/
theorem mem_ratioLocus_of_isUnit_sum {d : ℕ} {a b : ℤ} (ha : a = (d : ℤ))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} {x : ProjectiveSpectrum.top 𝒮} (hx : x ∈ W)
    {ι : Type*} (t : Finset ι)
    (ς : ι → moduleSections 𝒮 (twistGrading (S := S) 𝒮 a) W)
    (τ : ι → moduleSections 𝒮 (twistGrading (S := S) 𝒮 b) W)
    (h : IsUnit (∑ i ∈ t, (ς i).1 ⟨x, hx⟩ * (τ i).1 ⟨x, hx⟩)) :
    x ∈ ProjShared.ratioLocus 𝒮 d := by
  have h' : IsUnit (∑ i ∈ t, ((ς i).1 ⟨x, hx⟩ * (τ i).1 ⟨x, hx⟩ :
      Localization.AtPrime x.asHomogeneousIdeal.toIdeal)) := h
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum h'
  exact mem_ratioLocus_of_isUnit_mul 𝒮 ha hx (ς i) (τ i) hi

/-- A finite sum of products of values of sections of `𝒪(d)` and `𝒪(b)` at `x` which equals `1`
puts `x` in the ratio locus. -/
theorem mem_ratioLocus_of_sum_eq_one {d : ℕ} {a b : ℤ} (ha : a = (d : ℤ))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} {x : ProjectiveSpectrum.top 𝒮} (hx : x ∈ W)
    {ι : Type*} (t : Finset ι)
    (ς : ι → moduleSections 𝒮 (twistGrading (S := S) 𝒮 a) W)
    (τ : ι → moduleSections 𝒮 (twistGrading (S := S) 𝒮 b) W)
    (h : (∑ i ∈ t, (ς i).1 ⟨x, hx⟩ * (τ i).1 ⟨x, hx⟩) = 1) :
    x ∈ ProjShared.ratioLocus 𝒮 d := by
  refine mem_ratioLocus_of_isUnit_sum 𝒮 ha hx t ς τ ?_
  rw [h]
  exact isUnit_one

end Stacks.AlgebraicGeometry.GoodOpenClose

end
