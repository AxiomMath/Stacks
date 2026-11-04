module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.OrderedCechMonomialModel
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreFunctoriality

/-!
# The sheaf-level multiplication map of Serre's computation is the monomial one

Let `R` be a commutative ring, `n` a natural number, `i` a natural number and `d + i = e`. For a
homogeneous polynomial `f ∈ R[T₀, …, Tₙ]` of degree `i`, multiplication by `f` is a morphism of
sheaves of modules

`𝒪(d) ⟶ 𝒪(e)`

on `ℙⁿ_R = Proj R[T₀, …, Tₙ]`. It is the second datum of [Stacks, Tag 01XV], and it already
exists in this library: it is
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap`, the morphism of associated
sheaves induced by the degree-preserving map `S(d) → S(e)` of shifted graded modules given by
multiplication by `f`.

What is proved here is that this sheaf morphism **is** the multiplication
`Stacks.ProjectiveSpace.Cohomology.chartMul` of the monomial model: on the sections over the
standard open `D₊(∏_{i ∈ s} Tᵢ)`, through the identification
`Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart` of those sections with the
monomial chart `twistChart R n d s`, it is multiplication by `f` on Laurent coefficients — and
the same on every term of the Čech complex of the standard cover, a term being the sections over
an intersection of standard charts. This is the termwise content of the comparison between the
map of Čech complexes that the sheaf morphism induces and
`Stacks.ProjectiveSpace.Cohomology.laurentCechCochainMul`. Assembled into a morphism of complexes
and read on the cohomology of `𝒪(d)` this gives the multiplication clauses of [Stacks, Tag 01XV],
in `StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/SerreSheafFunctoriality.lean`.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 01XV](https://stacks.math.columbia.edu/tag/01XV)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory TopologicalSpace
  Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap
  associatedModuleSheafMap_standardOpen)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap
  homogeneousMul_mem_twistGrading)
open Stacks.Cohomology.Basis (res res_app)
open Stacks.Cohomology.CechSheaf (abSections)
open Stacks.ProjectiveCohomology (basicOpenXAtUniverse chartIndices polyGrading)

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ} {d e : ℤ}

/-- **A Laurent exponent vector with nonnegative entries, read as a monomial exponent.** The
`i`-th entry is `(a i).toNat`, so this is the exponent vector of the monomial `T^a` whenever every
`a i` is nonnegative. -/
def laurentToNatExp (a : Fin (n + 1) → ℤ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (a i).toNat

/-- The entries of `Stacks.ProjectiveSpace.Cohomology.laurentToNatExp`. -/
@[simp]
theorem laurentToNatExp_apply (a : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    laurentToNatExp a i = (a i).toNat := rfl

/-- **The polynomial with the given Laurent coefficients.** For a coefficient family `f`
supported on exponent vectors with nonnegative entries — that is, for an element of the monomial
chart `twistChart R n m ∅` with no variable inverted — this is the genuine polynomial
`∑_a f_a T^a` of `R[T₀, …, Tₙ]`. It is the translation in which a homogeneous polynomial of
degree `m` enters [Stacks, Tag 01XV]: `Stacks.ProjectiveSpace.Cohomology.polyOfLaurent_mem` says
that it is homogeneous of degree `m`. -/
def polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R) : MvPolynomial (Fin (n + 1)) R :=
  f.sum fun a c => MvPolynomial.monomial (laurentToNatExp a) c

/-- A Laurent exponent vector of total degree `m` with nonnegative entries is the exponent vector
of a monomial of degree `m`. -/
theorem degree_laurentToNatExp {i : ℕ} {a : Fin (n + 1) → ℤ}
    (ha : a ∈ laurentMonomials n (i : ℤ) (∅ : Set (Fin (n + 1)))) :
    (laurentToNatExp a).degree = i := by
  obtain ⟨hsum, hout⟩ := mem_laurentMonomials.1 ha
  have hnn : ∀ j, 0 ≤ a j := fun j => hout j (by simp)
  have hcast : ((∑ j, (a j).toNat : ℕ) : ℤ) = (i : ℤ) := by
    rw [Nat.cast_sum]
    exact Eq.trans (Finset.sum_congr rfl fun j _ => Int.toNat_of_nonneg (hnn j)) hsum
  rw [Finsupp.degree_eq_sum]
  exact Nat.cast_inj.mp hcast

/-- **An element of the degree-`m` monomial chart with no variable inverted is a homogeneous
polynomial of degree `m`.** -/
theorem polyOfLaurent_mem {i : ℕ} {f : (Fin (n + 1) → ℤ) →₀ R}
    (hf : f ∈ twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1)))) :
    polyOfLaurent f ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R i := by
  rw [polyOfLaurent, Finsupp.sum]
  refine Submodule.sum_mem _ fun a ha => ?_
  exact (MvPolynomial.mem_homogeneousSubmodule i _).2
    (MvPolynomial.isHomogeneous_monomial (f a)
      (degree_laurentToNatExp (mem_twistChart.1 hf (Finset.mem_coe.2 ha))))

/-- Localizing multiplication by a ring element is multiplication by that element: this is the
pointwise content of the sheaf-level multiplication map on a standard open. -/
theorem localizedModule_map_mul {A : Type u} [CommRing A] (P : Submonoid A) (a : A)
    (z : LocalizedModule P A) :
    LocalizedModule.map P (LinearMap.mul A A a) z = a • z := by
  induction z using LocalizedModule.induction_on with
  | h x b => rw [LocalizedModule.map_mk, LocalizedModule.smul'_mk]; rfl

/-- **Multiplying a Laurent monomial by a monomial adds the exponents.** In the localization
`R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]`, the monomial `c · T^a` with `a` nonnegative times the Laurent
monomial `T^k` is `c · T^{a + k}`. The same power of `∏_{i ∈ s} Tᵢ` clears the negative exponents
of `k` and of `a + k`, so both sides are read over one denominator. -/
theorem monomial_smul_laurentFrac (R : Type u) [CommRing R] (n : ℕ) (s : Finset (Fin (n + 1)))
    {a k : Fin (n + 1) → ℤ} (ha : ∀ i, 0 ≤ a i) (hk : ∀ i ∉ s, 0 ≤ k i) (c : R) :
    (MvPolynomial.monomial (laurentToNatExp a) c : MvPolynomial (Fin (n + 1)) R) •
        laurentFrac R n s k
      = c • laurentFrac R n s (a + k) := by
  classical
  have hkin : ∀ i ∈ s, 0 ≤ k i + (clearDen s k : ℤ) := le_add_clearDen s k
  have hak : ∀ i ∉ s, 0 ≤ (a + k) i := fun i hi => add_nonneg (ha i) (hk i hi)
  have hakin : ∀ i ∈ s, 0 ≤ (a + k) i + (clearDen s k : ℤ) := by
    intro i hi
    have h1 := hkin i hi
    have h2 := ha i
    show 0 ≤ a i + k i + (clearDen s k : ℤ)
    omega
  have hnum : laurentToNatExp a + numExp s k (clearDen s k) = numExp s (a + k) (clearDen s k) := by
    refine Finsupp.ext fun i => Nat.cast_injective (R := ℤ) ?_
    rw [Finsupp.add_apply, Nat.cast_add, natCast_numExp_apply hk hkin,
      natCast_numExp_apply hak hakin, laurentToNatExp_apply, Int.toNat_of_nonneg (ha i)]
    simp only [Pi.add_apply]
    ring
  rw [laurentFrac_eq_mk (R := R) hk hkin, laurentFrac_eq_mk (R := R) hak hakin,
    LocalizedModule.smul'_mk, LocalizedModule.smul'_mk]
  refine congrArg (fun z => LocalizedModule.mk z (chartPow R n s (clearDen s k))) ?_
  rw [smul_eq_mul, MvPolynomial.monomial_mul_monomial, mul_one, MvPolynomial.smul_monomial,
    smul_eq_mul, mul_one, hnum]

/-- **Multiplication by `f` on one Laurent monomial, read in the localization.** If `w` is the
coefficient family `laurentMul f (T^k)`, then as a section it is `f · T^k`: expand `f` into its
monomials and apply `Stacks.ProjectiveSpace.Cohomology.monomial_smul_laurentFrac` to each. -/
theorem coe_twistChartEquivTwistSections_laurentMul_single (R : Type u) [CommRing R] (n : ℕ)
    {d e : ℤ} {i : ℕ} (s : Finset (Fin (n + 1)))
    {f : (Fin (n + 1) → ℤ) →₀ R} (hf : f ∈ twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1))))
    (hde : d + (i : ℤ) = e) {k : Fin (n + 1) → ℤ}
    (hk : k ∈ laurentMonomials n d (↑s : Set (Fin (n + 1))))
    (w : twistChart R n e (↑s : Set (Fin (n + 1))))
    (hw : (w : (Fin (n + 1) → ℤ) →₀ R) = laurentMul f (Finsupp.single k 1)) :
    ((twistChartEquivTwistSections R n e s w :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
      = polyOfLaurent f • laurentFrac R n s k := by
  classical
  obtain ⟨hsk, houtk⟩ := hk
  have hpos : ∀ a ∈ f.support, ∀ j, 0 ≤ a j := fun a ha j =>
    (mem_twistChart.1 hf (Finset.mem_coe.2 ha)).2 j (by simp)
  have hdeg : ∀ a ∈ f.support, (∑ j, a j) = (i : ℤ) := fun a ha =>
    (mem_twistChart.1 hf (Finset.mem_coe.2 ha)).1
  have hmem : ∀ a ∈ f.support, a + k ∈ laurentMonomials n e (↑s : Set (Fin (n + 1))) := by
    intro a ha
    refine ⟨?_, fun j hj => add_nonneg (hpos a ha j) (houtk j hj)⟩
    have hadd : ∑ j, (a + k) j = (∑ j, a j) + ∑ j, k j := Finset.sum_add_distrib
    rw [hadd, hdeg a ha, hsk]
    omega
  have hsum : w = ∑ a ∈ f.support.attach,
      f a.1 • (⟨Finsupp.single (a.1 + k) 1, single_mem_twistChart (hmem a.1 a.2) 1⟩ :
        twistChart R n e (↑s : Set (Fin (n + 1)))) := by
    refine Subtype.ext ?_
    rw [hw, laurentMul_apply, AddSubmonoidClass.coe_finset_sum,
      ← Finset.sum_attach f.support
        (fun a => f a • Finsupp.mapDomain (fun z => a + z) (Finsupp.single k 1))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.mapDomain_single]
    rfl
  have hLHS : ((twistChartEquivTwistSections R n e s w :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
      = ∑ a ∈ f.support.attach, f a.1 • laurentFrac R n s (a.1 + k) := by
    rw [hsum, map_sum, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, SetLike.val_smul,
      coe_twistChartEquivTwistSections_single R n e s (hmem a.1 a.2) _ rfl]
  have hRHS : polyOfLaurent f • laurentFrac R n s k
      = ∑ a ∈ f.support.attach, f a.1 • laurentFrac R n s (a.1 + k) := by
    rw [polyOfLaurent, Finsupp.sum, Finset.sum_smul,
      ← Finset.sum_attach f.support
        (fun a => (MvPolynomial.monomial (laurentToNatExp a) (f a) :
          MvPolynomial (Fin (n + 1)) R) • laurentFrac R n s k)]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact monomial_smul_laurentFrac R n s (hpos a.1 a.2) houtk (f a.1)
  rw [hLHS, hRHS]

/-- **The monomial model of multiplication by a homogeneous polynomial is multiplication by that
polynomial.** Through the identification
`Stacks.ProjectiveSpace.Cohomology.twistChartEquivTwistSections` of the monomial chart with the
degree-`d` part of `R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]`, the map
`Stacks.ProjectiveSpace.Cohomology.chartMul` of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/SerreFunctoriality.lean` becomes genuine
multiplication by `Stacks.ProjectiveSpace.Cohomology.polyOfLaurent f` in the localization.

Both sides are `R`-linear, so it suffices to check this on the monomial basis
`Stacks.ProjectiveSpace.Cohomology.twistSectionsBasis`, which is
`coe_twistChartEquivTwistSections_laurentMul_single`. -/
theorem coe_twistChartEquivTwistSections_chartMul (R : Type u) [CommRing R] (n : ℕ)
    {d e : ℤ} {i : ℕ} (s : Finset (Fin (n + 1)))
    (f : twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1)))) (hde : d + (i : ℤ) = e)
    (z : twistSections R n d s) :
    ((twistChartEquivTwistSections R n e s
        (chartMul f hde (↑s : Set (Fin (n + 1)))
          ((twistChartEquivTwistSections R n d s).symm z)) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
      = polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R) •
          (z : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) := by
  have key :
      ((twistSections R n e s).subtype.comp
          ((twistChartEquivTwistSections R n e s).toLinearMap.comp
            ((chartMul f hde (↑s : Set (Fin (n + 1)))).comp
              (twistChartEquivTwistSections R n d s).symm.toLinearMap)))
        = ((LinearMap.lsmul (MvPolynomial (Fin (n + 1)) R)
              (LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))
              (polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R))).restrictScalars R).comp
            (twistSections R n d s).subtype := by
    refine (twistSectionsBasis R n d s).ext fun k => ?_
    have hw : ((chartMul f hde (↑s : Set (Fin (n + 1)))
          ((twistChartEquivTwistSections R n d s).symm (twistSectionsBasis R n d s k)) :
          twistChart R n e (↑s : Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R)
        = laurentMul (f : (Fin (n + 1) → ℤ) →₀ R)
            (Finsupp.single (k : Fin (n + 1) → ℤ) 1) := by
      rw [chartMul_coe, coe_twistChartEquivTwistSections_symm_basis]
    have hb : ((twistSectionsBasis R n d s k : twistSections R n d s) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))
        = laurentFrac R n s (k : Fin (n + 1) → ℤ) := by
      simp only [twistSectionsBasis, Module.Basis.coe_mk]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
    rw [coe_twistChartEquivTwistSections_laurentMul_single R n s f.2 hde k.2 _ hw, hb]
  exact DFunLike.congr_fun key z

/-- `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap`, the sheaf-level
multiplication map, unfolded: it is the morphism of associated sheaves induced by multiplication
by `a` on the shifted graded modules. -/
theorem twistScalarSheafMap_eq {S : Type u} {σ : Type v} [CommRing S] [SetLike σ S]
    [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮] (i : ℕ) (c k : ℤ) (hk : (i : ℤ) + c = k)
    (a : 𝒮 i) :
    twistScalarSheafMap 𝒮 i c k hk a
      = associatedModuleSheafMap 𝒮
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading 𝒮 c)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading 𝒮 k)
          (LinearMap.mul S S (a : S)) (homogeneousMul_mem_twistGrading 𝒮 i c k hk a) :=
  rfl

/-- **On a standard open, the morphism of twisting sheaves induced by multiplication by a
polynomial `p` is multiplication by `p`.** This is
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_standardOpen`, read
through the identification `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquiv` of the
sections of `𝒪(d)` over `D₊(∏_{i ∈ s} Tᵢ)` with the degree-`d` part of the localization — an
identification which is that standard-open equivalence, by
`Stacks.ProjectiveSpace.Cohomology.coe_chartSectionsAddEquiv` and
`Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading`, so no comparison appears. -/
theorem coe_chartSectionsAddEquiv_associatedModuleSheafMap (R : Type u) [CommRing R] (n : ℕ)
    {d e : ℤ} (p : MvPolynomial (Fin (n + 1)) R)
    (hp : ∀ (j : ℤ) (m : MvPolynomial (Fin (n + 1)) R),
        m ∈ AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d j →
        (LinearMap.mul (MvPolynomial (Fin (n + 1)) R) (MvPolynomial (Fin (n + 1)) R) p) m ∈
          AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) e j)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (x : chartSheafSections R n d s) :
    ((chartSectionsAddEquiv R n e s hs
        (((associatedModuleSheafMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d)
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) e)
            (LinearMap.mul (MvPolynomial (Fin (n + 1)) R) (MvPolynomial (Fin (n + 1)) R) p)
            hp).val.app
              (op (ProjectiveSpectrum.basicOpen
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
                  (chartDenom R n s)))).hom x) : twistSections R n e s) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))
      = p • ((chartSectionsAddEquiv R n d s hs x : twistSections R n d s) :
            LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) :=
  (associatedModuleSheafMap_standardOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) e)
      (LinearMap.mul (MvPolynomial (Fin (n + 1)) R) (MvPolynomial (Fin (n + 1)) R) p) hp
      (chartDenom_mem_homogeneousSubmodule n s) (Finset.card_pos.2 hs) x).trans
    (localizedModule_map_mul _ p _)

/-- A section `y` of `𝒪(e)` over the standard open whose fraction is `polyOfLaurent f` times that
of `x` has monomial model `chartMul f` applied to the monomial model of `x`. -/
theorem chartSectionsAddEquivTwistChart_eq_chartMul (R : Type u) [CommRing R] (n : ℕ)
    {d e : ℤ} {i : ℕ} (f : twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1))))
    (hde : d + (i : ℤ) = e) (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (x : chartSheafSections R n d s) (y : chartSheafSections R n e s)
    (hxy : ((chartSectionsAddEquiv R n e s hs y : twistSections R n e s) :
          LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))
        = polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R) •
            ((chartSectionsAddEquiv R n d s hs x : twistSections R n d s) :
              LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))) :
    chartSectionsAddEquivTwistChart R n e s hs y
      = chartMul f hde (↑s : Set (Fin (n + 1)))
          (chartSectionsAddEquivTwistChart R n d s hs x) := by
  have hA : chartSectionsAddEquiv R n e s hs y
      = twistChartEquivTwistSections R n e s
          (chartMul f hde (↑s : Set (Fin (n + 1)))
            ((twistChartEquivTwistSections R n d s).symm
              (chartSectionsAddEquiv R n d s hs x))) :=
    Subtype.ext (hxy.trans
      (coe_twistChartEquivTwistSections_chartMul R n s f hde
        (chartSectionsAddEquiv R n d s hs x)).symm)
  exact (congrArg (fun z : twistSections R n e s =>
      (twistChartEquivTwistSections R n e s).symm z) hA).trans
    ((twistChartEquivTwistSections R n e s).symm_apply_apply _)

/-- **The sheaf-level multiplication map of [Stacks, Tag 01XV] is the monomial-model
multiplication `chartMul`.** Let `f` be an element of the degree-`i` monomial chart with no
variable inverted — equivalently, by `Stacks.ProjectiveSpace.Cohomology.polyOfLaurent_mem`, a
homogeneous polynomial of degree `i` — and let `d + i = e`. Then the morphism of twisting sheaves
`𝒪(d) ⟶ 𝒪(e)` given by multiplication by that polynomial,
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap`, read on the sections over the
standard open `D₊(∏_{i ∈ s} Tᵢ)` through the monomial model
`Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart`, is exactly
`Stacks.ProjectiveSpace.Cohomology.chartMul f`.

The monomial Čech statements of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/SerreFunctoriality.lean` are about
`chartMul` and its assembly `laurentCechCochainMul` on the monomial Čech complex, and this says
that that operation *is* the sheaf-level multiplication by `f`, chart by chart;
`Stacks.ProjectiveSpace.Cohomology.coe_ordInterChartAddEquiv_twistScalarSheafMap` below carries
it to the terms of the Čech complex itself. -/
theorem chartSectionsAddEquivTwistChart_twistScalarSheafMap (R : Type u) [CommRing R] (n : ℕ)
    {d e : ℤ} {i : ℕ} (f : twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1))))
    (hde : d + (i : ℤ) = e) (hk : (i : ℤ) + d = e)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (x : chartSheafSections R n d s) :
    chartSectionsAddEquivTwistChart R n e s hs
        (((twistScalarSheafMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i d e hk
            ⟨polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R),
              polyOfLaurent_mem f.2⟩).val.app
              (op (ProjectiveSpectrum.basicOpen
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
                  (chartDenom R n s)))).hom x)
      = chartMul f hde (↑s : Set (Fin (n + 1)))
          (chartSectionsAddEquivTwistChart R n d s hs x) :=
  chartSectionsAddEquivTwistChart_eq_chartMul R n f hde s hs x _
    (coe_chartSectionsAddEquiv_associatedModuleSheafMap R n
      (polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R))
      (homogeneousMul_mem_twistGrading
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i d e hk
        ⟨polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R), polyOfLaurent_mem f.2⟩) s hs x)

/-! ### The Čech terms of the standard cover -/

/-- **On a Čech term of the standard cover, the sheaf-level multiplication map of
[Stacks, Tag 01XV] is multiplication by `f` on Laurent coefficients.** A degree-`p` Čech term of
`𝒪(d)` at a tuple `x` of coordinate indices with distinct entries is the sections over the
intersection of the standard charts the tuple selects, which
`Stacks.ProjectiveSpace.Cohomology.inter_eq_basicOpen_chartDenom` identifies with the standard
open of the chart denominator; `Stacks.ProjectiveSpace.Cohomology.interChartAddEquiv` restricts
along that identification and then reads off monomial coordinates. Restriction commutes with the
sheaf morphism (`Stacks.Cohomology.Basis.res_app` applied to
`CategoryTheory.PresheafOfModules.toPresheaf` of it), so
`chartSectionsAddEquivTwistChart_twistScalarSheafMap` transports to the Čech term. -/
theorem coe_interChartAddEquiv_twistScalarSheafMap (R : Type u) [CommRing R] (n : ℕ)
    {d e : ℤ} {i : ℕ} (f : twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1))))
    (hde : d + (i : ℤ) = e) (hk : (i : ℤ) + d = e) {p : ℕ}
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) (hx : Function.Injective (chartIndices x))
    (u : twistInterSections R n d x) :
    ((interChartAddEquiv R n e x hx
          (((twistScalarSheafMap
              (polyGrading R n) i d e hk
              ⟨polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R),
                polyOfLaurent_mem f.2⟩).val.app
                (op (CechCochains.inter
                  (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
                    (basicOpenXAtUniverse R n) x))).hom u) :
        twistChart R n e (Set.range (chartIndices x))) : (Fin (n + 1) → ℤ) →₀ R)
      = laurentMul (f : (Fin (n + 1) → ℤ) →₀ R)
          ((interChartAddEquiv R n d x hx u :
            twistChart R n d (Set.range (chartIndices x))) : (Fin (n + 1) → ℤ) →₀ R) := by
  have hA := res_app
    (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))
    ((PresheafOfModules.toPresheaf _).map
      (twistScalarSheafMap (polyGrading R n) i d e hk
        ⟨polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R), polyOfLaurent_mem f.2⟩).val)
    (inter_eq_basicOpen_chartDenom R n p x hx).ge u
  have hMain := chartSectionsAddEquivTwistChart_twistScalarSheafMap R n f hde hk
    (Finset.image (chartIndices x) Finset.univ) (image_univ_nonempty (chartIndices x))
    (res
      (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))
      (inter_eq_basicOpen_chartDenom R n p x hx).ge u)
  exact (congrArg (fun z : chartSheafSections R n e
        (Finset.image (chartIndices x) Finset.univ) =>
      ((chartSectionsAddEquivTwistChart R n e (Finset.image (chartIndices x) Finset.univ)
          (image_univ_nonempty (chartIndices x)) z :
        twistChart R n e (↑(Finset.image (chartIndices x) Finset.univ) :
          Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R)) hA).trans
    (congrArg (fun w : twistChart R n e (↑(Finset.image (chartIndices x) Finset.univ) :
        Set (Fin (n + 1))) => (w : (Fin (n + 1) → ℤ) →₀ R)) hMain)

/-- The same at a strictly increasing Čech index of the standard cover, which is the shape the
ordered Čech complex `Stacks.ProjectiveSpace.Cohomology.twistOrdCochainEquiv` is assembled
from. -/
theorem coe_ordInterChartAddEquiv_twistScalarSheafMap (R : Type u) [CommRing R] (n : ℕ)
    {d e : ℤ} {i : ℕ} (f : twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1))))
    (hde : d + (i : ℤ) = e) (hk : (i : ℤ) + d = e) (p : ℕ)
    (idx : CechCochains.OrdIndex (I := ULift.{u} (Fin (n + 1))) p)
    (u : twistInterSections R n d idx.1) :
    ((ordInterChartAddEquiv R n e p idx
          (((twistScalarSheafMap (polyGrading R n) i d e hk
              ⟨polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R),
                polyOfLaurent_mem f.2⟩).val.app
                (op (CechCochains.inter
                  (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
                    (basicOpenXAtUniverse R n) idx.1))).hom u) :
        twistChart R n e (Set.range (chartIndices idx.1))) : (Fin (n + 1) → ℤ) →₀ R)
      = laurentMul (f : (Fin (n + 1) → ℤ) →₀ R)
          ((ordInterChartAddEquiv R n d p idx u :
            twistChart R n d (Set.range (chartIndices idx.1))) : (Fin (n + 1) → ℤ) →₀ R) :=
  coe_interChartAddEquiv_twistScalarSheafMap R n f hde hk idx.1
    (strictMono_chartIndices idx.2).injective u

end Stacks.ProjectiveSpace.Cohomology

end
