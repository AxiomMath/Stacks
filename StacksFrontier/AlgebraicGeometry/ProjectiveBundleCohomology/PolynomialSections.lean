module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic

/-!
# The global sections of the twists on projective space are the homogeneous polynomials

Let `R` be a commutative ring, `n ≥ 1` and `P = R[T₀, …, Tₙ]` graded by total degree. The canonical
map `P_d → Γ(Proj P, 𝒪(d))`, sending a homogeneous polynomial `p` of degree `d` to the section
whose value at every point is `p / 1`, is bijective for every `d ≥ 0`, and `Γ(Proj P, 𝒪(d)) = 0`
for `d < 0`.

The proof reads the sections of `𝒪(d)` over the standard opens `D₊(Tᵢ)` as Laurent polynomials
through `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart`: the restriction maps
become inclusions of monomial charts, a Laurent monomial allowed in every chart `{i}` is a
polynomial monomial (`Stacks.ProjectiveSpace.Cohomology.iInter_laurentMonomials_singleton`), and
the canonical section of `p` reads as `p` itself in every chart.

## Main results

* `chartSectionsAddEquivTwistChart_degreeSection`: on the chart `D₊(∏_{i ∈ s} Tᵢ)`, the canonical
  section of `p` is the Laurent polynomial `p`.
* `bijective_degreeSection_polynomial`: **`P_d → Γ(Proj P, 𝒪(d))` is bijective.**
* `eq_of_neg`: **`Γ(Proj P, 𝒪(d)) = 0` for `d < 0`.**
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveSpace.Cohomology
open Stacks.AlgebraicGeometry.ProjTwistSections

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {n : ℕ}

local notation "𝒯" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- **On a standard open the canonical section of `p` is the fraction `p / 1`.** For `s` a
nonempty set of coordinates and `p` homogeneous of degree `k`, the restriction of the section of
`𝒪(k)` attached to `p` to `D₊(∏_{i ∈ s} Tᵢ)`, read in the localization
`R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]`, is `p / 1`. -/
public theorem coe_chartSectionsAddEquiv_degreeSection (k : ℕ) (s : Finset (Fin (n + 1)))
    (hs : s.Nonempty) (p : 𝒯 k) :
    ((chartSectionsAddEquiv R n (k : ℤ) s hs
        (((twistingSheaf 𝒯 (k : ℤ)).val.map
          (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒯 (chartDenom R n s) ≤ ⊤)).op).hom
          (degreeSection 𝒯 k p)) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
      = LocalizedModule.mk (p : MvPolynomial (Fin (n + 1)) R) 1 := by
  have hf := chartDenom_mem_homogeneousSubmodule (R := R) n s
  have hk : 0 < s.card := Finset.card_pos.2 hs
  have hp : (p : MvPolynomial (Fin (n + 1)) R) ∈
      twistGrading (S := MvPolynomial (Fin (n + 1)) R) 𝒯 (k : ℤ) (0 • (s.card : ℤ)) := by
    rw [zero_smul]
    exact mem_twistGrading_zero 𝒯 p
  let z := degreeZeroFraction 𝒯 (twistGrading (S := MvPolynomial (Fin (n + 1)) R) 𝒯 (k : ℤ))
    hf 0 (p : MvPolynomial (Fin (n + 1)) R) hp
  have hres : ((twistingSheaf 𝒯 (k : ℤ)).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒯 (chartDenom R n s) ≤ ⊤)).op).hom
        (degreeSection 𝒯 k p) =
      degreeZeroToSection 𝒯 (twistGrading (S := MvPolynomial (Fin (n + 1)) R) 𝒯 (k : ℤ))
        (chartDenom R n s) z := by
    refine Subtype.ext (funext fun x => ?_)
    refine (degreeSection_apply 𝒯 k p ⟨x.1, trivial⟩).trans ?_
    refine Eq.trans ?_ (degreeZeroToSection_fraction 𝒯 _ hf 0 _ hp x).symm
    congr 1
  have h2 : associatedModuleSheafStandardOpenEquiv 𝒯
      (twistGrading (S := MvPolynomial (Fin (n + 1)) R) 𝒯 (k : ℤ)) hf hk
      (((twistingSheaf 𝒯 (k : ℤ)).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒯 (chartDenom R n s) ≤ ⊤)).op).hom
          (degreeSection 𝒯 k p)) = z :=
    (congrArg (associatedModuleSheafStandardOpenEquiv 𝒯
      (twistGrading (S := MvPolynomial (Fin (n + 1)) R) 𝒯 (k : ℤ)) hf hk) hres).trans
      (LinearEquiv.ofBijective_symm_apply_apply _ z)
  refine (congrArg (fun y : GradedModuleDegreeZeroLocalization 𝒯
      (twistGrading (S := MvPolynomial (Fin (n + 1)) R) 𝒯 (k : ℤ)) (chartDenom R n s) =>
    (y : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))) h2).trans ?_
  show LocalizedModule.mk _ _ = _
  congr 1

/-- The polynomial chart identification on a monomial basis vector. -/
public theorem coe_twistChartEmptyLinearEquiv_single {d : ℤ} (hd : 0 ≤ d)
    (e : laurentMonomials n d (∅ : Set (Fin (n + 1)))) :
    ((twistChartEmptyLinearEquiv (R := R) n hd
        ((Finsupp.supportedEquivFinsupp (M := R) (R := R) _).symm (Finsupp.single e 1)) :
        MvPolynomial (Fin (n + 1)) R)) =
      MvPolynomial.monomial (laurentMonomialsEmptyEquiv n hd e : Fin (n + 1) →₀ ℕ) 1 := by
  have h1 : (Finsupp.domLCongr (M := R) (R := R) (laurentMonomialsEmptyEquiv n hd))
      ((Finsupp.supportedEquivFinsupp (M := R) (R := R) (laurentMonomials n d ∅))
        ((Finsupp.supportedEquivFinsupp (M := R) (R := R) (laurentMonomials n d ∅)).symm
          (Finsupp.single e 1))) =
      Finsupp.single (laurentMonomialsEmptyEquiv n hd e) (1 : R) := by
    rw [LinearEquiv.apply_symm_apply, Finsupp.domLCongr_single]
  show (((AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R)
    {m : Fin (n + 1) →₀ ℕ | m.degree = d.toNat}).symm
      ((Finsupp.domLCongr (M := R) (R := R) (laurentMonomialsEmptyEquiv n hd))
        ((Finsupp.supportedEquivFinsupp (M := R) (R := R) (laurentMonomials n d ∅))
          ((Finsupp.supportedEquivFinsupp (M := R) (R := R) (laurentMonomials n d ∅)).symm
            (Finsupp.single e 1)))) :
            AddMonoidAlgebra R (Fin (n + 1) →₀ ℕ))) = _
  rw [h1]
  show AddMonoidAlgebra.ofCoeff ((Finsupp.supportedEquivFinsupp (M := R) (R := R)
    {m : Fin (n + 1) →₀ ℕ | m.degree = d.toNat}).symm
      (Finsupp.single (laurentMonomialsEmptyEquiv n hd e) (1 : R)) :
        (Fin (n + 1) →₀ ℕ) →₀ R) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single (M := R) (R := R)]
  rfl

/-- **A polynomial, read in a chart, is the fraction `p / 1`.** The polynomial chart of degree
`k` included into the chart of `s` and read in `R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]` is the fraction
of the corresponding homogeneous polynomial over `1`. -/
public theorem coe_twistChartEquivTwistSections_inclusion_empty (k : ℕ)
    (s : Finset (Fin (n + 1))) (w : twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1)))) :
    ((twistChartEquivTwistSections R n (k : ℤ) s
        (Submodule.inclusion (twistChart_mono (R := R) (d := (k : ℤ))
          (Set.empty_subset (↑s : Set (Fin (n + 1))))) w) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
      = LocalizedModule.mk ((twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg k) w :
          MvPolynomial (Fin (n + 1)) R)) 1 := by
  let L₁ : twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1))) →ₗ[R]
      LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R) :=
    (twistSections R n (k : ℤ) s).subtype ∘ₗ
      (twistChartEquivTwistSections R n (k : ℤ) s).toLinearMap ∘ₗ
        Submodule.inclusion (twistChart_mono (R := R) (d := (k : ℤ))
          (Set.empty_subset (↑s : Set (Fin (n + 1)))))
  let L₂ : twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1))) →ₗ[R]
      LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R) :=
    ((LocalizedModule.mkLinearMap (Submonoid.powers (chartDenom R n s))
        (MvPolynomial (Fin (n + 1)) R)).restrictScalars R) ∘ₗ
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (k : ℤ).toNat).subtype ∘ₗ
        (twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg k)).toLinearMap
  have hL : L₁ = L₂ := by
    refine ((Finsupp.basisSingleOne).map
      (Finsupp.supportedEquivFinsupp (M := R) (R := R)
        (laurentMonomials n (k : ℤ) (∅ : Set (Fin (n + 1))))).symm).ext fun e => ?_
    have he := mem_laurentMonomials.mp e.2
    have hnn : ∀ i, 0 ≤ (e : Fin (n + 1) → ℤ) i := fun i => he.2 i (by simp)
    rw [Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
    set b : twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1))) :=
      (Finsupp.supportedEquivFinsupp (M := R) (R := R)
        (laurentMonomials n (k : ℤ) (∅ : Set (Fin (n + 1))))).symm (Finsupp.single e 1) with hb
    show ((twistChartEquivTwistSections R n (k : ℤ) s
        (Submodule.inclusion (twistChart_mono (R := R) (d := (k : ℤ))
          (Set.empty_subset (↑s : Set (Fin (n + 1))))) b) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))) =
      LocalizedModule.mk ((twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg k) b :
          MvPolynomial (Fin (n + 1)) R)) 1
    rw [coe_twistChartEquivTwistSections_single R n (k : ℤ) s
      (laurentMonomials_mono (Set.empty_subset _) e.2) _ (by
        exact Finsupp.supportedEquivFinsupp_symm_single (M := R) (R := R) _ _ _)]
    rw [laurentFrac_eq_mk (R := R) (N := 0) (fun i _ => hnn i) (fun i _ => by simpa using hnn i)]
    have hE : ((twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg k) b :
        MvPolynomial (Fin (n + 1)) R)) = MvPolynomial.monomial (numExp s e 0) 1 := by
      refine (coe_twistChartEmptyLinearEquiv_single (Int.natCast_nonneg k) e).trans ?_
      have hm : (laurentMonomialsEmptyEquiv n (Int.natCast_nonneg k) e :
          Fin (n + 1) →₀ ℕ) = numExp s (e : Fin (n + 1) → ℤ) 0 := by
        ext i
        simp [laurentMonomialsEmptyEquiv, numExp]
      rw [hm]
    rw [hE]
    congr 1
  exact DFunLike.congr_fun hL w

/-- The homogeneous polynomial of degree `k` attached to an element of the polynomial chart. -/
public def chartPoly {k : ℕ} (w : twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1)))) : 𝒯 k :=
  ⟨(twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg k) w :
      MvPolynomial (Fin (n + 1)) R), by simp⟩

/-- The restriction of a section of `𝒪(d)` to the standard open `D₊(∏_{i ∈ s} Tᵢ)`. -/
public abbrev resChart (d : ℤ) (s : Finset (Fin (n + 1)))
    (σ : (twistingSheaf 𝒯 d).val.obj (op ⊤)) : chartSheafSections R n d s :=
  ((twistingSheaf 𝒯 d).val.map
    (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒯 (chartDenom R n s) ≤ ⊤)).op).hom σ

/-- **On a chart, the canonical section of a polynomial is that polynomial.** For `w` in the
polynomial chart of degree `k`, the restriction to `D₊(∏_{i ∈ s} Tᵢ)` of the section of `𝒪(k)`
attached to the corresponding polynomial is `w` itself, read in the chart of `s`. -/
public theorem chartSectionsAddEquivTwistChart_degreeSection (k : ℕ) (s : Finset (Fin (n + 1)))
    (hs : s.Nonempty) (w : twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1)))) :
    chartSectionsAddEquivTwistChart R n (k : ℤ) s hs
        (resChart (k : ℤ) s (degreeSection 𝒯 k (chartPoly w))) =
      Submodule.inclusion (twistChart_mono (R := R) (d := (k : ℤ))
        (Set.empty_subset (↑s : Set (Fin (n + 1))))) w := by
  show (twistChartEquivTwistSections R n (k : ℤ) s).symm
    (chartSectionsAddEquiv R n (k : ℤ) s hs
      (resChart (k : ℤ) s (degreeSection 𝒯 k (chartPoly w)))) = _
  rw [LinearEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  exact (coe_chartSectionsAddEquiv_degreeSection k s hs (chartPoly w)).trans
    (coe_twistChartEquivTwistSections_inclusion_empty k s w).symm

/-- Restricting from `⊤` to a chart and then to a smaller chart is restricting to the smaller
chart. -/
public theorem map_resChart (d : ℤ) (s t : Finset (Fin (n + 1))) (_ : s.Nonempty) (hst : s ⊆ t)
    (σ : (twistingSheaf 𝒯 d).val.obj (op ⊤)) :
    ((twistingSheaf 𝒯 d).val.map
        (homOfLE (basicOpen_chartDenom_le R n s t hst)).op).hom (resChart d s σ) =
      resChart d t σ := by
  refine (PresheafOfModules.map_comp_apply (twistingSheaf 𝒯 d).val
    (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒯 (chartDenom R n s) ≤ ⊤)).op
    (homOfLE (basicOpen_chartDenom_le R n s t hst)).op σ).symm.trans ?_
  exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) σ

/-- The charts of the single coordinates read a global section as one Laurent polynomial. -/
public theorem coe_chartSectionsAddEquivTwistChart_resChart_singleton_eq (d : ℤ)
    (σ : (twistingSheaf 𝒯 d).val.obj (op ⊤)) (i j : Fin (n + 1)) :
    ((chartSectionsAddEquivTwistChart R n d {i} (Finset.singleton_nonempty i)
        (resChart d {i} σ) : twistChart R n d (↑({i} : Finset (Fin (n + 1))))) :
        (Fin (n + 1) → ℤ) →₀ R) =
      ((chartSectionsAddEquivTwistChart R n d {j} (Finset.singleton_nonempty j)
        (resChart d {j} σ) : twistChart R n d (↑({j} : Finset (Fin (n + 1))))) :
        (Fin (n + 1) → ℤ) →₀ R) := by
  have hi := chartSectionsAddEquivTwistChart_map_homOfLE R n d {i} {i, j}
    (Finset.singleton_nonempty i) (by simp) (resChart d {i} σ)
  have hj := chartSectionsAddEquivTwistChart_map_homOfLE R n d {j} {i, j}
    (Finset.singleton_nonempty j) (by simp) (resChart d {j} σ)
  have hi' := (congrArg (chartSectionsAddEquivTwistChart R n d {i, j} (by simp))
    (map_resChart d {i} {i, j} (Finset.singleton_nonempty i) (by simp) σ)).symm.trans hi
  have hj' := (congrArg (chartSectionsAddEquivTwistChart R n d {i, j} (by simp))
    (map_resChart d {j} {i, j} (Finset.singleton_nonempty j) (by simp) σ)).symm.trans hj
  exact congrArg (fun z : twistChart R n d (↑({i, j} : Finset (Fin (n + 1)))) =>
    (z : (Fin (n + 1) → ℤ) →₀ R)) (hi'.symm.trans hj')

/-- Every point of `Proj R[T₀, …, Tₙ]` lies in a coordinate chart. -/
public theorem exists_mem_basicOpen_chartDenom_singleton (x : ProjectiveSpectrum 𝒯) :
    ∃ i : Fin (n + 1), x ∈ ProjectiveSpectrum.basicOpen 𝒯 (chartDenom R n {i}) := by
  have hx : x ∈ (⊤ : (AlgebraicGeometry.Proj 𝒯).Opens) := trivial
  rw [← Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top R n] at hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨i, ?_⟩
  have hX : chartDenom R n {i} = MvPolynomial.X i := by simp [chartDenom]
  rwa [hX]

/-- **Two global sections of `𝒪(d)` agreeing on every coordinate chart are equal.** -/
public theorem eq_of_resChart_singleton_eq (d : ℤ) {σ τ : (twistingSheaf 𝒯 d).val.obj (op ⊤)}
    (h : ∀ i : Fin (n + 1), resChart d {i} σ = resChart d {i} τ) : σ = τ := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_chartDenom_singleton x.1
  exact congrArg (fun z : chartSheafSections R n d {i} => z.1 ⟨x.1, hi⟩) (h i)

/-- The Laurent polynomial of a global section of `𝒪(d)`, read in the chart of `T₀`. -/
public def globalChart (d : ℤ) (σ : (twistingSheaf 𝒯 d).val.obj (op ⊤)) :
    (Fin (n + 1) → ℤ) →₀ R :=
  (chartSectionsAddEquivTwistChart R n d {0} (Finset.singleton_nonempty 0)
    (resChart d {0} σ) : twistChart R n d (↑({0} : Finset (Fin (n + 1)))))

/-- The chart of a single coordinate reads a global section of `𝒪(d)` as `globalChart`. -/
public theorem coe_chartSectionsAddEquivTwistChart_resChart_singleton (d : ℤ)
    (σ : (twistingSheaf 𝒯 d).val.obj (op ⊤)) (i : Fin (n + 1)) :
    ((chartSectionsAddEquivTwistChart R n d {i} (Finset.singleton_nonempty i)
        (resChart d {i} σ) : twistChart R n d (↑({i} : Finset (Fin (n + 1))))) :
        (Fin (n + 1) → ℤ) →₀ R) = globalChart d σ :=
  coe_chartSectionsAddEquivTwistChart_resChart_singleton_eq d σ i 0

/-- **A global section of `𝒪(d)` is a polynomial**: its Laurent polynomial lies in the polynomial
chart, a Laurent monomial allowed in the chart of every single coordinate being a monomial. -/
public theorem globalChart_mem (hn : 0 < n) (d : ℤ) (σ : (twistingSheaf 𝒯 d).val.obj (op ⊤)) :
    globalChart d σ ∈ twistChart R n d (∅ : Set (Fin (n + 1))) := by
  rw [mem_twistChart, ← iInter_laurentMonomials_singleton n hn d]
  refine Set.subset_iInter fun i => ?_
  have h := (chartSectionsAddEquivTwistChart R n d {i} (Finset.singleton_nonempty i)
    (resChart d {i} σ)).2
  rw [coe_chartSectionsAddEquivTwistChart_resChart_singleton, mem_twistChart] at h
  simpa using h

/-- The chart element of a homogeneous polynomial. -/
public def polyChart {k : ℕ} (p : 𝒯 k) : twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1))) :=
  (twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg k)).symm
    ⟨(p : MvPolynomial (Fin (n + 1)) R), by simp⟩

/-- `chartPoly` is a left inverse of `polyChart`. -/
public theorem chartPoly_polyChart {k : ℕ} (p : 𝒯 k) : chartPoly (polyChart p) = p :=
  Subtype.ext <| by simp only [chartPoly, polyChart, LinearEquiv.apply_symm_apply]

/-- On a chart, the canonical section of a homogeneous polynomial `p` is `polyChart p`, read in
the chart of `s`. -/
public theorem chartSectionsAddEquivTwistChart_degreeSection' (k : ℕ) (s : Finset (Fin (n + 1)))
    (hs : s.Nonempty) (p : 𝒯 k) :
    chartSectionsAddEquivTwistChart R n (k : ℤ) s hs (resChart (k : ℤ) s (degreeSection 𝒯 k p)) =
      Submodule.inclusion (twistChart_mono (R := R) (d := (k : ℤ))
        (Set.empty_subset (↑s : Set (Fin (n + 1))))) (polyChart p) := by
  have h := chartSectionsAddEquivTwistChart_degreeSection k s hs (polyChart p)
  have e : degreeSection 𝒯 k (chartPoly (polyChart p)) = degreeSection 𝒯 k p :=
    congrArg (degreeSection 𝒯 k) (chartPoly_polyChart p)
  exact (congrArg (fun σ => chartSectionsAddEquivTwistChart R n (k : ℤ) s hs
    (resChart (k : ℤ) s σ)) e).symm.trans h

/-- **The global sections of `𝒪(k)` on `ℙⁿ_R` are the homogeneous polynomials of degree `k`**:
for `n ≥ 1` and every `k ≥ 0`, the map sending a homogeneous polynomial `p` of degree `k` to the
section of `𝒪(k)` with value `p / 1` everywhere is bijective. -/
public theorem bijective_degreeSection_polynomial (hn : 0 < n) (k : ℕ) :
    Function.Bijective (degreeSection 𝒯 k) := by
  refine ⟨fun p q hpq => ?_, fun σ => ?_⟩
  · have h := (chartSectionsAddEquivTwistChart_degreeSection' k {0}
      (Finset.singleton_nonempty 0) p).symm.trans ((congrArg (fun σ =>
        chartSectionsAddEquivTwistChart R n (k : ℤ) {0} (Finset.singleton_nonempty 0)
          (resChart (k : ℤ) {0} σ)) hpq).trans
      (chartSectionsAddEquivTwistChart_degreeSection' k {0} (Finset.singleton_nonempty 0) q))
    have h' := Submodule.inclusion_injective _ h
    rw [← chartPoly_polyChart p, ← chartPoly_polyChart q, h']
  · let w : twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1))) := ⟨_, globalChart_mem hn (k : ℤ) σ⟩
    refine ⟨chartPoly w, eq_of_resChart_singleton_eq (k : ℤ) fun i => ?_⟩
    refine
      (chartSectionsAddEquivTwistChart R n (k : ℤ) {i} (Finset.singleton_nonempty i)).injective ?_
    refine (chartSectionsAddEquivTwistChart_degreeSection k {i} (Finset.singleton_nonempty i)
      w).trans ?_
    refine Subtype.ext ?_
    exact (coe_chartSectionsAddEquivTwistChart_resChart_singleton (k : ℤ) σ i).symm

/-- For `n ≥ 1` and `d < 0`, the Laurent polynomial of a global section of `𝒪(d)` is zero. -/
public theorem globalChart_eq_zero_of_neg (hn : 0 < n) {d : ℤ} (hd : d < 0)
    (σ : (twistingSheaf 𝒯 d).val.obj (op ⊤)) : globalChart d σ = 0 := by
  have := globalChart_mem hn d σ
  rwa [twistChart_eq_bot_of_neg n hd, Submodule.mem_bot] at this

/-- **`Γ(ℙⁿ_R, 𝒪(d)) = 0` for `d < 0`**, for `n ≥ 1`: any two global sections agree. -/
public theorem eq_of_neg (hn : 0 < n) {d : ℤ} (hd : d < 0)
    (σ τ : (twistingSheaf 𝒯 d).val.obj (op ⊤)) : σ = τ :=
  eq_of_resChart_singleton_eq d fun i =>
    (chartSectionsAddEquivTwistChart R n d {i} (Finset.singleton_nonempty i)).injective
      (Subtype.ext ((coe_chartSectionsAddEquivTwistChart_resChart_singleton d σ i).trans
        ((globalChart_eq_zero_of_neg hn hd σ).trans
          ((globalChart_eq_zero_of_neg hn hd τ).symm.trans
            (coe_chartSectionsAddEquivTwistChart_resChart_singleton d τ i).symm))))

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
