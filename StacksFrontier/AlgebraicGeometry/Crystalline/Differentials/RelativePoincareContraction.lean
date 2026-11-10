module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSectorDecomposition
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSectorHorizontal

/-!
# The relative divided power Poincaré lemma: the contracting homotopy

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W`
index a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩`.  This module assembles
the sector homotopy into a homotopy on `Ω^*_{P/A,δ'}` itself.

## Main definitions

* `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy` — the homotopy `h`, the sector
  homotopy applied in each sector of the decomposition.
* `Crystalline.DividedPowerPolynomial.relativeFormsRetraction` — the coefficient retraction
  `ε : Ωⁿ_{P/A,δ'} → Ωⁿ_{B/A,δ}`, picking out the slot with no variables and no monomial.
* `Crystalline.DividedPowerPolynomial.relativeFormsProjection` — `ψ ∘ ε`, the projection onto
  the `K = 0` sector.

## References

* [Stacks Project, Lemma 60.19.1, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW

namespace Crystalline

namespace DividedPowerPolynomial

section Contraction

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-- **The contracting homotopy on one generator of the decomposition.**  The generator
indexed by `(i, j + 1, J, L)` lies in the sector `K = L + 1_J`, and the homotopy of that
sector carries it to bidegree `(i, j)`. -/
def relativeSectorHomotopyGenerator (i j : ℕ) (J : Set.powersetCard W (j + 1)) (L : W →₀ ℕ) :
    dividedPowerDifferentialForms (A := A) B.dividedPowers i →ₗ[A]
      dividedPowerPolynomialForms A B W (i + j) :=
  ((relativeSectorMap A B W (L + finsetMultiIndex J.val) i j).restrictScalars A) ∘ₗ
    ((relativeSectorHomotopy A B W (L + finsetMultiIndex J.val) i j).restrictScalars A) ∘ₗ
    (((sectorModuleEquiv A B W (L + finsetMultiIndex J.val) i
        (j + 1)).symm.toLinearMap).restrictScalars A) ∘ₗ
    Finsupp.lsingle (R := A) (sectorLiftSubset W (L + finsetMultiIndex J.val) (j + 1) J
      (subset_support_add_finsetMultiIndex J.val L))

/-- The contracting homotopy on the bidegree-`(i, j + 1)` summand, prescribed on the
generators by `Finsupp.lsum`.  This is the relative replacement for the absolute
`Module.Basis.constr`: there is no basis, only a `Finsupp`. -/
def relativeFormsHomotopyBidegree (i j : ℕ) :
    polynomialBidegreeForms A B W i (j + 1) →ₗ[A]
      dividedPowerPolynomialForms A B W (i + j) :=
  (Finsupp.lsum A fun J ↦ Finsupp.lsum A fun L ↦
      relativeSectorHomotopyGenerator A B W i j J L) ∘ₗ
    (((polynomialBidegreeFormsMonomialEquiv A B W i (j + 1)).toLinearMap).restrictScalars A)

/-- The contracting homotopy on one summand of the degree-`n + 1` decomposition.  The summands
with no variables are killed: there is no Koszul direction to contract there. -/
def relativeFormsHomotopyPiece (n : ℕ) : (i j : ℕ) → i + j = n + 1 →
    (polynomialBidegreeForms A B W i j →ₗ[A] dividedPowerPolynomialForms A B W n)
  | _, 0, _ => 0
  | i, (j + 1), hij =>
      (((exteriorPower.degCongr
            (show i + j = n from by omega)).toLinearMap).restrictScalars A) ∘ₗ
        relativeFormsHomotopyBidegree A B W i j

/-- **The contracting homotopy of `Ω^*_{P/A,δ'}`**, assembled from the sector homotopies. -/
def relativeFormsHomotopy (n : ℕ) :
    dividedPowerPolynomialForms A B W (n + 1) →ₗ[A]
      dividedPowerPolynomialForms A B W n :=
  (DirectSum.toModule A {ij : ℕ × ℕ // ij.1 + ij.2 = n + 1}
      (dividedPowerPolynomialForms A B W n)
      fun ij ↦ relativeFormsHomotopyPiece A B W n ij.1.1 ij.1.2 ij.2) ∘ₗ
    (((dividedPowerPolynomialFormsEquiv A B W (n + 1)).toLinearMap).restrictScalars A)

/-- The empty set as the unique `0`-element subset of `W`. -/
def emptyPowersetCard : Set.powersetCard W 0 := ⟨∅, rfl⟩

/-- **The coefficient retraction `ε : Ωⁿ_{P/A,δ'} → Ωⁿ_{B/A,δ}`**: the slot of the
decomposition with no variable differentials and the trivial monomial, which is the `K = 0`
sector. -/
def relativeFormsRetraction (n : ℕ) :
    dividedPowerPolynomialForms A B W n →ₗ[A]
      dividedPowerDifferentialForms (A := A) B.dividedPowers n :=
  Finsupp.lapply (R := A) (0 : W →₀ ℕ) ∘ₗ
    Finsupp.lapply (R := A) (emptyPowersetCard W) ∘ₗ
    (((polynomialBidegreeFormsMonomialEquiv A B W n 0).toLinearMap).restrictScalars A) ∘ₗ
    DirectSum.component A {ij : ℕ × ℕ // ij.1 + ij.2 = n}
      (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(n, 0), rfl⟩ ∘ₗ
    (((dividedPowerPolynomialFormsEquiv A B W n).toLinearMap).restrictScalars A)

/-- **The projection onto the `K = 0` sector**, `ψ ∘ ε`.  For `I = ⊥` the coefficient forms
vanish in positive degree and this is the absolute constant projection. -/
def relativeFormsProjection (n : ℕ) :
    dividedPowerPolynomialForms A B W n →ₗ[A] dividedPowerPolynomialForms A B W n :=
  ((coefficientFormsMap A B W n).restrictScalars A) ∘ₗ relativeFormsRetraction A B W n

/-! ### The homotopy read on a sector -/

/-- A `j`-element subset of `supp K`, read as a `j`-element subset of `W`. -/
def sectorSubsetDown (K : W →₀ ℕ) (j : ℕ) (I : Set.powersetCard (K.support : Type uW) j) :
    Set.powersetCard W j :=
  Set.powersetCard.map j (OrderEmbedding.subtype (· ∈ K.support)).toEmbedding I

/-- The image in `W` of a subset of `supp K` is contained in `supp K`. -/
theorem sectorSubsetDown_subset (K : W →₀ ℕ) (j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) j) :
    (sectorSubsetDown W K j I).val ⊆ K.support := by
  intro a ha
  rw [sectorSubsetDown, Set.powersetCard.val_map] at ha
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp ha
  exact b.property

/-- Lifting a subset of `W` contained in `supp K` to `supp K` and reading it back in `W` gives
the original subset. -/
theorem sectorSubsetDown_sectorLiftSubset (K : W →₀ ℕ) (j : ℕ) (J : Set.powersetCard W j)
    (hJ : J.val ⊆ K.support) : sectorSubsetDown W K j (sectorLiftSubset W K j J hJ) = J :=
  sectorLiftSubset_map W K j J hJ

/-- Reading a subset of `supp K` in `W` and lifting it back to `supp K` gives the original
subset. -/
theorem sectorLiftSubset_sectorSubsetDown (K : W →₀ ℕ) (j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) j) :
    sectorLiftSubset W K j (sectorSubsetDown W K j I) (sectorSubsetDown_subset W K j I) = I := by
  refine Subtype.ext ?_
  ext a
  simp [sectorLiftSubset, sectorSubsetDown]

/-- **The sector map on a sector basis vector**, for an arbitrary total multi-index `K`: it is
the generator whose subset is the image of the basis index in `W` and whose exponent vector is
`K` lowered by one there. -/
theorem relativeSectorMap_sectorBasis (K : W →₀ ℕ) (i j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorMap A B W K i j
        (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega) =
      sectorGenerator A B W (K - finsetMultiIndex (sectorSubsetDown W K j I).val) i omega j
        fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm (sectorSubsetDown W K j I) k := by
  classical
  have henum : (fun k ↦ ((Set.powersetCard.ofFinEmbEquiv.symm I k :
        (K.support : Type uW)) : W)) =
      fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm (sectorSubsetDown W K j I) k :=
    Set.powersetCard.ofFinEmbEquiv_symm_map I (OrderEmbedding.subtype (· ∈ K.support))
  refine Eq.trans (congrArg (relativeSectorMap A B W K i j)
    (congrArg (fun z : ⋀[(B : Type uB)]^j ((K.support : Type uW) →₀ (B : Type uB)) ↦
      z ⊗ₜ[(B : Type uB)] omega) (sectorExteriorBasis_apply B W K j I))) ?_
  refine Eq.trans (relativeSectorMap_tmul_ιMulti A B W K i j
    (fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm I k) omega) ?_
  refine Eq.trans (congrArg (fun g : Fin j → W ↦
    sectorGeneratorMap A B W (K - finsetMultiIndex (Finset.univ.image g)) i j g omega)
    henum) ?_
  exact congrArg (fun s : Finset W ↦
      sectorGenerator A B W (K - finsetMultiIndex s) i omega j
        fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm (sectorSubsetDown W K j I) k)
    (image_ofFinEmbEquiv_symm W j (sectorSubsetDown W K j I))

omit [LinearOrder W] in
/-- The two scalar rings give the same inclusion of a summand. -/
theorem lof_eq_lof (n : ℕ) (ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n})
    (y : polynomialBidegreeForms A B W ij.1.1 ij.1.2) :
    DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
        {ij : ℕ × ℕ // ij.1 + ij.2 = n}
        (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ij y =
      DirectSum.lof A {ij : ℕ × ℕ // ij.1 + ij.2 = n}
        (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ij y := by
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]

/-- The homotopy on a single summand of the decomposition. -/
theorem relativeFormsHomotopy_apply_symm_lof (n : ℕ)
    (ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n + 1})
    (y : polynomialBidegreeForms A B W ij.1.1 ij.1.2) :
    relativeFormsHomotopy A B W n
        ((dividedPowerPolynomialFormsEquiv A B W (n + 1)).symm
          (DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
            {ij : ℕ × ℕ // ij.1 + ij.2 = n + 1}
            (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ij y)) =
      relativeFormsHomotopyPiece A B W n ij.1.1 ij.1.2 ij.2 y := by
  simp only [relativeFormsHomotopy, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    lof_eq_lof]
  exact DirectSum.toModule_lof (M := fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n + 1} ↦
    polynomialBidegreeForms A B W ij.1.1 ij.1.2) A ij y

/-- **The homotopy on a generator with at least one variable differential**: the homotopy of
the sector `K = L + 1_J` of that generator. -/
theorem relativeFormsHomotopy_sectorGenerator (L : W →₀ ℕ) (i j : ℕ)
    (J : Set.powersetCard W (j + 1))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeFormsHomotopy A B W (i + j)
        (sectorGenerator A B W L i omega (j + 1) fun k ↦
          Set.powersetCard.ofFinEmbEquiv.symm J k) =
      relativeSectorMap A B W (L + finsetMultiIndex J.val) i j
        (relativeSectorHomotopy A B W (L + finsetMultiIndex J.val) i j
          (sectorExteriorBasis B W (L + finsetMultiIndex J.val) (j + 1)
              (sectorLiftSubset W (L + finsetMultiIndex J.val) (j + 1) J
                (subset_support_add_finsetMultiIndex J.val L)) ⊗ₜ[(B : Type uB)] omega)) := by
  refine Eq.trans (congrArg (relativeFormsHomotopy A B W (i + j))
    (dividedPowerPolynomialFormsEquiv_symm_lof_single A B W i (j + 1) L J omega).symm) ?_
  refine Eq.trans (relativeFormsHomotopy_apply_symm_lof A B W (i + j) ⟨(i, j + 1), rfl⟩ _) ?_
  change relativeFormsHomotopyBidegree A B W i j
      ((polynomialBidegreeFormsMonomialEquiv A B W i (j + 1)).symm
        (Finsupp.single J (Finsupp.single L omega))) = _
  simp only [relativeFormsHomotopyBidegree, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    Finsupp.lsum_single]
  change (relativeSectorMap A B W (L + finsetMultiIndex J.val) i j)
      ((relativeSectorHomotopy A B W (L + finsetMultiIndex J.val) i j)
        ((sectorModuleEquiv A B W (L + finsetMultiIndex J.val) i (j + 1)).symm
          (Finsupp.single (sectorLiftSubset W (L + finsetMultiIndex J.val) (j + 1) J
            (subset_support_add_finsetMultiIndex J.val L)) omega))) = _
  rw [sectorModuleEquiv_symm_single]

/-- **The homotopy kills a generator with no variable differential**: there is no Koszul
direction to contract in bidegree `(i, 0)`. -/
theorem relativeFormsHomotopy_sectorGenerator_zero (L : W →₀ ℕ) (i : ℕ)
    (J : Set.powersetCard W 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers (i + 1)) :
    relativeFormsHomotopy A B W i
        (sectorGenerator A B W L (i + 1) omega 0 fun k ↦
          Set.powersetCard.ofFinEmbEquiv.symm J k) = 0 := by
  refine Eq.trans (congrArg (relativeFormsHomotopy A B W i)
    (dividedPowerPolynomialFormsEquiv_symm_lof_single A B W (i + 1) 0 L J omega).symm) ?_
  exact relativeFormsHomotopy_apply_symm_lof A B W i ⟨(i + 1, 0), rfl⟩ _

/-- Two sectors with the same total multi-index and the same variable subset give the same
homotopy value. -/
theorem relativeSectorMap_homotopy_congr (K K' : W →₀ ℕ) (hK : K' = K) (i j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) (j + 1))
    (I' : Set.powersetCard (K'.support : Type uW) (j + 1))
    (hI : (sectorSubsetDown W K' (j + 1) I').val = (sectorSubsetDown W K (j + 1) I).val)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorMap A B W K' i j
        (relativeSectorHomotopy A B W K' i j
          (sectorExteriorBasis B W K' (j + 1) I' ⊗ₜ[(B : Type uB)] omega)) =
      relativeSectorMap A B W K i j
        (relativeSectorHomotopy A B W K i j
          (sectorExteriorBasis B W K (j + 1) I ⊗ₜ[(B : Type uB)] omega)) := by
  subst hK
  have hII : I' = I := by
    refine Subtype.ext ?_
    rw [sectorSubsetDown, sectorSubsetDown, Set.powersetCard.val_map,
      Set.powersetCard.val_map] at hI
    exact Finset.map_injective _ hI
  rw [hII]

/-- **The homotopy on the sector map, on a sector basis vector.** -/
theorem relativeFormsHomotopy_relativeSectorMap_basis (K : W →₀ ℕ) (i j : ℕ)
    (I : Set.powersetCard (K.support : Type uW) (j + 1))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeFormsHomotopy A B W (i + j)
        (relativeSectorMap A B W K i (j + 1)
          (sectorExteriorBasis B W K (j + 1) I ⊗ₜ[(B : Type uB)] omega)) =
      relativeSectorMap A B W K i j
        (relativeSectorHomotopy A B W K i j
          (sectorExteriorBasis B W K (j + 1) I ⊗ₜ[(B : Type uB)] omega)) := by
  refine Eq.trans (congrArg (relativeFormsHomotopy A B W (i + j))
    (relativeSectorMap_sectorBasis A B W K i (j + 1) I omega)) ?_
  refine Eq.trans (relativeFormsHomotopy_sectorGenerator A B W
    (K - finsetMultiIndex (sectorSubsetDown W K (j + 1) I).val) i j
    (sectorSubsetDown W K (j + 1) I) omega) ?_
  refine relativeSectorMap_homotopy_congr A B W K _
    (finsetMultiIndex_sub_add _ K (sectorSubsetDown_subset W K (j + 1) I)) i j I _ ?_ omega
  rw [sectorSubsetDown_sectorLiftSubset]

/-- Induction on an element of a sector module, along the basis-and-coefficients description. -/
private theorem sectorModule_induction (K : W →₀ ℕ) (i j : ℕ)
    {P : sectorModule A B W K i j → Prop} (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (basis : ∀ (I : Set.powersetCard (K.support : Type uW) j)
      (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i),
      P (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega))
    (x : sectorModule A B W K i j) : P x := by
  have key : ∀ (f : Set.powersetCard (K.support : Type uW) j →₀
        dividedPowerDifferentialForms (A := A) B.dividedPowers i)
      (y : sectorModule A B W K i j), (sectorModuleEquiv A B W K i j).symm f = y → P y := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => rintro y rfl; rwa [map_zero]
    | add f g hf hg => rintro y rfl; rw [map_add]; exact add _ _ (hf _ rfl) (hg _ rfl)
    | single I omega => rintro y rfl; rw [sectorModuleEquiv_symm_single]; exact basis I omega
  exact key _ x ((sectorModuleEquiv A B W K i j).symm_apply_apply x)

/-- **The homotopy on the sector map**: through the sector map, the homotopy of
`Ω^*_{P/A,δ'}` is the homotopy of the sector.  This is the relative
`Crystalline.DividedPowerPolynomial.dpFormsHomotopy_sectorMap`. -/
theorem relativeFormsHomotopy_relativeSectorMap (K : W →₀ ℕ) (i j : ℕ)
    (x : sectorModule A B W K i (j + 1)) :
    relativeFormsHomotopy A B W (i + j) (relativeSectorMap A B W K i (j + 1) x) =
      relativeSectorMap A B W K i j (relativeSectorHomotopy A B W K i j x) := by
  induction x using sectorModule_induction with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | basis I omega => exact relativeFormsHomotopy_relativeSectorMap_basis A B W K i j I omega

/-- **The homotopy kills the image of a sector in bidegree `(i, 0)`.** -/
theorem relativeFormsHomotopy_relativeSectorMap_zero (K : W →₀ ℕ) (i : ℕ)
    (x : sectorModule A B W K (i + 1) 0) :
    relativeFormsHomotopy A B W i (relativeSectorMap A B W K (i + 1) 0 x) = 0 := by
  induction x using sectorModule_induction with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | basis I omega =>
    refine Eq.trans (congrArg (relativeFormsHomotopy A B W i)
      (relativeSectorMap_sectorBasis A B W K (i + 1) 0 I omega)) ?_
    exact relativeFormsHomotopy_sectorGenerator_zero A B W
      (K - finsetMultiIndex (sectorSubsetDown W K 0 I).val) i (sectorSubsetDown W K 0 I) omega

/-! ### The sector map into a named degree -/

/-- **The sector map, landing in a named degree.**  The bidegrees `(i, j)`, `(i + 1, j)` and
`(i, j + 1)` of one sector have total degrees that are propositionally but not definitionally
`n`, `n + 1` and `n + 1`; carrying the degree as a parameter puts every term of the
contraction computation in the same type and absorbs the transports
`Crystalline.DividedPowerPolynomial.relativeSectorMap_dividedPowerDeRham` carries explicitly. -/
def relativeSectorMapDeg (K : W →₀ ℕ) (i j n : ℕ) (hn : i + j = n) :
    sectorModule A B W K i j →ₗ[(B : Type uB)] dividedPowerPolynomialForms A B W n :=
  (((exteriorPower.degCongr (R := setIndexedDividedPowerPolynomialAlgebra B W)
        (M := dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W))
        hn).toLinearMap).restrictScalars (B : Type uB)) ∘ₗ relativeSectorMap A B W K i j

/-- `relativeSectorMapDeg` is `relativeSectorMap` followed by the degree transport along
`i + j = n`. -/
@[simp] theorem relativeSectorMapDeg_apply (K : W →₀ ℕ) (i j n : ℕ) (hn : i + j = n)
    (x : sectorModule A B W K i j) :
    relativeSectorMapDeg A B W K i j n hn x =
      exteriorPower.degCongr hn (relativeSectorMap A B W K i j x) :=
  rfl

/-- A degree transport along a proof of a trivial equation is the identity. -/
theorem degCongr_self {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (h : n = n) (x : ⋀[R]^n M) : exteriorPower.degCongr h x = x :=
  rfl

/-- **The de Rham differential on a sector, in a named degree**: the total differential of the
bicomplex, with no degree transport left in sight. -/
theorem relativeSectorMapDeg_dividedPowerDeRham (K : W →₀ ℕ) (i j n : ℕ) (hn : i + j = n)
    (x : sectorModule A B W K i j) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
        (relativeSectorMapDeg A B W K i j n hn x) =
      relativeSectorMapDeg A B W K (i + 1) j (n + 1) (by omega)
          (relativeSectorCoefficientDifferential A B W K i j x) +
        relativeSectorMapDeg A B W K i (j + 1) (n + 1) (by omega)
          (relativeSectorKoszulDifferential A B W K i j x) := by
  subst hn
  simp only [relativeSectorMapDeg_apply, degCongr_self]
  exact relativeSectorMap_dividedPowerDeRham_total A B W K i j x

/-- **The homotopy on the sector map, in a named degree.** -/
theorem relativeFormsHomotopy_relativeSectorMapDeg (K : W →₀ ℕ) (i j n : ℕ) (hn : i + j = n)
    (x : sectorModule A B W K i (j + 1)) :
    relativeFormsHomotopy A B W n
        (relativeSectorMapDeg A B W K i (j + 1) (n + 1) (by omega) x) =
      relativeSectorMapDeg A B W K i j n hn (relativeSectorHomotopy A B W K i j x) := by
  subst hn
  simp only [relativeSectorMapDeg_apply, degCongr_self]
  exact relativeFormsHomotopy_relativeSectorMap A B W K i j x

/-- **The homotopy kills bidegree `(n + 1, 0)`, in a named degree.** -/
theorem relativeFormsHomotopy_relativeSectorMapDeg_zero (K : W →₀ ℕ) (n : ℕ)
    (x : sectorModule A B W K (n + 1) 0) :
    relativeFormsHomotopy A B W n
        (relativeSectorMapDeg A B W K (n + 1) 0 (n + 1) rfl x) = 0 := by
  simp only [relativeSectorMapDeg_apply, degCongr_self]
  exact relativeFormsHomotopy_relativeSectorMap_zero A B W K n x

end Contraction

end DividedPowerPolynomial

end Crystalline

end
