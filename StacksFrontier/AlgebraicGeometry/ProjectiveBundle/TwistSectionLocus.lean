module

public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.AffineSectionBasis
public import StacksFrontier.AlgebraicGeometry.ProjChartKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.IdealOfClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Clause
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.AffineTwistSections

/-!
# Where a degree-one twisted section vanishes, on a `Proj` generated in degree one

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring generated in degree one over `𝒮 0`, so
that `𝒪(1)` is invertible on the whole of `Proj 𝒮`. For `a ∈ 𝒮 1` the canonical global section
`degreeSection 𝒮 1 a` of `𝒪(1)` is then nonvanishing exactly on the standard open `D₊(a)`:

`X_{s(a)} = D₊(a)`,

with no intersection against an invertible locus left over, and its zero scheme is cut out on
each standard affine chart `D₊(f)` of a degree-one `f` by the single fraction `a / f`.

Specialised to `𝒮 = Sym_A(M)` this is the vanishing statement for the sections of `𝒪(1)` on the
projective bundle `𝐏(M̃) = Proj(Sym_A(M))` over an affine base that
`StacksFrontier.AlgebraicGeometry.ProjectiveBundle.AffineTwistSections` constructs, and it is the
input a Chow-group argument on the bundle needs about them: the common vanishing locus of a
family of such sections is the complement of the union of the corresponding standard opens.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.nonvanishingLocus_degreeSection_one`: **the
  nonvanishing locus of the section of `𝒪(1)` attached to a degree-one element is `D₊(a)`**, on
  the whole of `Proj 𝒮`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.vanishingSet_degreeSection_one`: the complementary
  form — the section vanishes exactly at the homogeneous primes containing `a`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.iInter_vanishingSet_degreeSection_one`: **the
  common vanishing locus of a family** of such sections is the complement of the union of the
  standard opens.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.zeroScheme_degreeSection_one_ideal_basicOpen`: the
  zero scheme of the section is cut out on the chart `D₊(f)` of a degree-one `f` by `a / f`.
* `SymmetricAlgebra.vanishingSet_toTwistSections` and
  `SymmetricAlgebra.iInter_vanishingSet_toTwistSections`: the last two statements for
  `Stacks.SymmetricAlgebra.toTwistSections`, the canonical map
  `M → Γ(Proj(Sym_A(M)), 𝒪(1))` of Stacks 01OB over an affine base. The first, that the section
  attached to `m ∈ M` is nonvanishing exactly on `D₊(m)`, is
  `SymmetricAlgebra.nonvanishingLocus_toTwistSections` of
  `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BasicOpenSection`.

## Implementation notes

The degree bookkeeping is the only subtlety. Stacks 01MV is stated in the library for an element
of degree `n * d` on the invertible locus `W_d`
(`Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'`), and the
statements below are its instance `n = d = 1`: `1 * 1` and `1` are the same natural number, so no
transport along an equality of degrees is needed, and
`Stacks.AlgebraicGeometry.ProjTwistPowers.whereInvertible_one_eq_top` turns `W_1` into `⊤`, which
is what removes the intersection from the conclusion of Stacks 01MV.

The nonvanishing locus is taken in the `Stacks.Ample.nonvanishingLocus` spelling — a global
section of a module on a scheme — because that is the spelling in which the ambient scheme is an
explicit argument, and the scheme here is `AlgebraicGeometry.Proj 𝒮`, which no higher-order
unification recovers from the type of `twistingSheaf`. The other spellings are identified with it
by `Stacks.AlgebraicGeometry.NonvanishingSpelling` and
`Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_sectionsOfTop_iff'`.

Nothing here assumes `S` Noetherian: the Noetherian hypothesis in
`StacksFrontier/AlgebraicGeometry/ProjSaturation/Basic.lean` is needed only for the converse
direction of the vanishing criterion for a *section*, not for the identification of the
nonvanishing *locus*.

## References

* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### The nonvanishing locus in degree one -/

/-- **The section of `𝒪(1)` attached to a degree-one element is nonvanishing exactly on
`D₊(a)`.** This is Stacks 01MV in degree one, with the invertible locus `W_1` identified with the
whole of `Proj 𝒮` because `S` is generated in degree one over `𝒮 0`. -/
theorem nonvanishingLocus_degreeSection_one
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (a : 𝒮 1) :
    Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒮)
        (twistingSheaf 𝒮 ((1 : ℕ) : ℤ)) (degreeSection 𝒮 1 a) =
      (AlgebraicGeometry.Proj.basicOpen 𝒮 (a : S) :
        Set (AlgebraicGeometry.Proj 𝒮)) := by
  ext x
  refine Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    𝒮 1 1 a ?_
  rw [Stacks.AlgebraicGeometry.ProjTwistPowers.whereInvertible_one_eq_top 𝒮 hgen]
  trivial

/-- **The section of `𝒪(1)` attached to a degree-one element vanishes exactly at the homogeneous
primes containing it**, the complementary form of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.nonvanishingLocus_degreeSection_one`. -/
theorem vanishingSet_degreeSection_one
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (a : 𝒮 1) :
    (Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒮)
          (twistingSheaf 𝒮 ((1 : ℕ) : ℤ)) (degreeSection 𝒮 1 a))ᶜ =
      {x : AlgebraicGeometry.Proj 𝒮 |
        (a : S) ∈ x.asHomogeneousIdeal.toIdeal} := by
  rw [nonvanishingLocus_degreeSection_one 𝒮 hgen a]
  ext x
  simp

/-- **The common vanishing locus of a family of degree-one twisted sections** is the complement
of the union of the corresponding standard opens. This is the form in which a Chow-group argument
on `Proj 𝒮` meets the zero loci of several sections of `𝒪(1)` at once. -/
theorem iInter_vanishingSet_degreeSection_one {ι : Type*}
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (v : ι → 𝒮 1) :
    (⋂ i, (Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒮)
          (twistingSheaf 𝒮 ((1 : ℕ) : ℤ)) (degreeSection 𝒮 1 (v i)))ᶜ) =
      (⋃ i, (AlgebraicGeometry.Proj.basicOpen 𝒮 ((v i : S)) :
        Set (AlgebraicGeometry.Proj 𝒮)))ᶜ := by
  rw [Set.compl_iUnion]
  exact Set.iInter_congr fun i => congrArg _ (nonvanishingLocus_degreeSection_one 𝒮 hgen (v i))

/-! ### The zero scheme in degree one -/

/-- **`𝒪(1)` is invertible on `Proj 𝒮` when `S` is generated in degree one**, in the spelling the
zero-scheme API of Chapter 31 asks for. -/
theorem isInvertible_twistingSheafModule_one
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒮).sheaf.obj
      (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.property
      (twistingSheafModule 𝒮 ((1 : ℕ) : ℤ)) :=
  algebraicGeometry_isInvertible_twistingSheaf 𝒮 hgen _

/-- **The zero scheme of the section of `𝒪(1)` attached to `a ∈ 𝒮 1` is cut out on the standard
chart `D₊(f)` of a degree-one `f` by the single fraction `a / f`.** This is Stacks 02OQ's
assertion that the zero scheme of a section of an invertible module is locally principal, made
explicit for the sections of the first twist. -/
theorem zeroScheme_degreeSection_one_ideal_basicOpen
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) {f : S} (hf : f ∈ 𝒮 1) (a : 𝒮 1) :
    letI := isInvertible_twistingSheafModule_one 𝒮 hgen
    (AlgebraicGeometry.zeroScheme (AlgebraicGeometry.Proj 𝒮)
          (twistingSheafModule 𝒮 ((1 : ℕ) : ℤ)) (degreeSection 𝒮 1 a)).ideal
        ⟨AlgebraicGeometry.Proj.basicOpen 𝒮 f,
          AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒮 f hf Nat.one_pos⟩ =
      Ideal.span {chartFraction 𝒮 hf 1 ⟨(a : S), by simp⟩} := by
  let := isInvertible_twistingSheafModule_one 𝒮 hgen
  exact zeroScheme_degreeSection_ideal_basicOpen_of_degree_eq 𝒮 hf Nat.one_pos 1
    (by simp) a (by simp)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

/-! ### The sections of `𝒪(1)` on the projective bundle over an affine base -/

namespace SymmetricAlgebra

universe u

variable (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]

/-- **The section of `𝒪(1)` attached to `m ∈ M` vanishes exactly at the homogeneous primes of
`Sym_A(M)` containing the image of `m`.** -/
theorem vanishingSet_toTwistSections (m : M) :
    (Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj (grading A M))
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (grading A M) ((1 : ℕ) : ℤ))
          (toTwistSections A M m))ᶜ =
      {x : AlgebraicGeometry.Proj (grading A M) |
        ι A M m ∈ x.asHomogeneousIdeal.toIdeal} :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.vanishingSet_degreeSection_one
    (grading A M) (adjoin_grading_one_eq_top A M) (toGradingOne A M m)

/-- **The common vanishing locus on `𝐏(M̃)` of the sections of `𝒪(1)` attached to a family of
elements of `M`** is the complement of the union of their standard opens. For `M` free with basis
`e_1, …, e_r` and the family `e_1, …, e_{r-1}` this is the locus the proof of Stacks 02TW cuts
out at the generic point of an integral subscheme of the base. -/
theorem iInter_vanishingSet_toTwistSections {ι' : Type*} (v : ι' → M) :
    (⋂ i, (Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj (grading A M))
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (grading A M) ((1 : ℕ) : ℤ))
          (toTwistSections A M (v i)))ᶜ) =
      (⋃ i, (AlgebraicGeometry.Proj.basicOpen (grading A M) (ι A M (v i)) :
        Set (AlgebraicGeometry.Proj (grading A M))))ᶜ :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.iInter_vanishingSet_degreeSection_one
    (grading A M) (adjoin_grading_one_eq_top A M) (fun i => toGradingOne A M (v i))

end SymmetricAlgebra

end
