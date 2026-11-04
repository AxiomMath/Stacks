module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulSectionsProjection
public import StacksFrontier.RingTheory.Cech.GeneralReindex

/-!
# The top cohomology sheaf of the Koszul complex with coefficients

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let `ℱ` be a
sheaf of `𝒪`-modules. The Koszul complex with coefficients
`AlgebraicGeometry.RingedSite.koszulPowerComplexOn X f ℱ n` is the alternating Čech complex of
the constant system `S ↦ ℱ` on the subsets of `{1, …, r}` whose transition map along `S ⊆ T` is
multiplication by `f_{T ∖ S}^{n+1}`; its term in degree `p` is the product of copies of `ℱ`
indexed by the subsets of cardinality `p`, so it is concentrated in the degrees `0, …, r` and
**the quotient `ℱ / (f_1^{n+1}, …, f_r^{n+1})ℱ` is its cohomology sheaf in the top degree `r`**,
the Koszul complex of [Stacks, Tag 0913] being this complex shifted so that the quotient sits in
degree `0`.

This file proves that identification, with the quotient presented as the cokernel of the map

  `ℱ^r ⟶ ℱ`,  `(x_1, …, x_r) ↦ ∑_i f_i^{n+1} x_i`,

which is `AlgebraicGeometry.RingedSite.koszulGeneratorsMap`. It is the degree-zero half of the
pro-isomorphism `{ℱ ⊗^𝐋_𝒪 K(𝒪, f_1ⁿ, …, f_rⁿ)} ≅ {ℱ/ℐⁿℱ}` that the proof of
[Stacks, Tag 0A0K] part (3) runs on: the comparison of the Koszul tower with the quotient tower
is an isomorphism in the top degree because the top cohomology of the Koszul complex *is* the
quotient. The module-level statement of the same fact is
`Stacks.KoszulCoefficientProIso.isIso_homologyMap_zero_rTensor`.

No hypothesis on `𝒞`, `𝒪` or `ℱ` is used: the whole computation is the universal property of a
cokernel, the top-degree term being a product over a one-element index set and the next term a
product over an empty one.

## Main definitions

* `CategoryTheory.AlternatingCech.topIdx` — the full subset, as the unique index of the
  top-degree term.
* `CategoryTheory.AlternatingCech.coIdx` and `CategoryTheory.AlternatingCech.missing` — the
  mutually inverse bijection between `Fin r` and the subsets of cardinality `r - 1`, sending `i`
  to its complement and a subset to the element it omits.
* `AlgebraicGeometry.RingedSite.koszulGenExp` — the exponent vector `n + 1` at one index and `0`
  elsewhere.
* `AlgebraicGeometry.RingedSite.koszulGeneratorsMap` — **the map `ℱ^r ⟶ ℱ` given by
  `(x_i) ↦ ∑_i f_i^{n+1} x_i`**, whose cokernel is `ℱ / (f_1^{n+1}, …, f_r^{n+1})ℱ`.
* `AlgebraicGeometry.RingedSite.koszulTopProj` and
  `AlgebraicGeometry.RingedSite.koszulTopDifferential` — the projection of the top-degree term
  onto its unique factor, an isomorphism, and the last differential read through it.

## Main results

* `Stacks.cokernelIsoOfFactors` — two morphisms into the same object whose sources factor through
  one another have isomorphic cokernels. This is what lets the top differential of the Koszul
  complex, indexed by the subsets of cardinality `r - 1` and carrying Čech signs, be compared
  with the sign-free generator map indexed by `Fin r`.
* `AlgebraicGeometry.RingedSite.koszulGeneratorsMap_eq_comp` and
  `AlgebraicGeometry.RingedSite.koszulTopDifferential_comp_eq` — the two factorizations.
* `AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap` — **the cohomology sheaf
  of `koszulPowerComplexOn X f ℱ n` in degree `r` is `ℱ / (f_1^{n+1}, …, f_r^{n+1})ℱ`.**
* `AlgebraicGeometry.RingedSite.isZero_homology_koszulPowerComplexOn_of_neg` and
  `AlgebraicGeometry.RingedSite.isZero_homology_koszulPowerComplexOn_of_gt` — the complex has no
  cohomology outside the degrees `0, …, r`, so the identification above is at the only degree
  where a quotient of `ℱ` can appear.

## Implementation notes

Indices of the alternating Čech complex are integers, and the top degree is written `r - 1 + 1`
rather than `r` throughout the construction so that it is syntactically of the form `p + 1`,
which is the shape `CategoryTheory.AlternatingCech.d_comp_pi` and the differential of
`CochainComplex.of` are stated at. The final statement is transported to the degree `r` by
rewriting that index, which is harmless because the right-hand side does not mention it.

`topIdx` and `coIdx` are `abbrev`s rather than `def`s so that their underlying finite sets reduce
at reducible transparency: `(topIdx r).1` is `Finset.univ` and `((topIdx r).erase k)` is
`coIdx k` on the nose, which is what makes the component of the Čech differential at the full
subset literally the multiplication by `f_k^{n+1}` on the factor indexed by the complement of
`k`.

Both `r = 0` and `r ≥ 1` are covered uniformly. For `r = 0` the index set of degree `r - 1 = -1`
is empty, `Fin 0` is empty, and both the top differential and the generator map are zero, so the
cokernel of either is `ℱ` — which is indeed `H⁰` of the one-term complex.

The signs of the Čech differential are handled by the factorization lemma rather than by
inverting them: the two comparison maps are the sign-weighted reindexings in the two directions,
and their composites with the two differentials are the differentials themselves because
`Cech.cechSign` squares to one, `Cech.cechSign_mul_self`.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks

/-- **Two morphisms into the same object whose sources factor through one another have isomorphic
cokernels.** Both maps are induced by `cokernel.desc`, and each composite is the identity because
`cokernel.π` is an epimorphism. -/
def cokernelIsoOfFactors {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {A B M : C}
    (g : A ⟶ M) (h : B ⟶ M) [HasCokernel g] [HasCokernel h] (w : B ⟶ A) (hw : w ≫ g = h)
    (w' : A ⟶ B) (hw' : w' ≫ h = g) : cokernel g ≅ cokernel h where
  hom := cokernel.desc g (cokernel.π h)
    (by rw [← hw', Category.assoc, cokernel.condition, comp_zero])
  inv := cokernel.desc h (cokernel.π g)
    (by rw [← hw, Category.assoc, cokernel.condition, comp_zero])
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id]
  inv_hom_id := by
    refine coequalizer.hom_ext ?_
    rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id]

end Stacks

namespace CategoryTheory.AlternatingCech

variable {r : ℕ}

/-! ## The top degree and the degree below it -/

/-- The full subset, as an index of the top-degree term of the alternating Čech complex. The
degree is written `r - 1 + 1` so that it is syntactically a successor. -/
abbrev topIdx (r : ℕ) : Idx r ((r : ℤ) - 1 + 1) :=
  ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]; ring⟩

/-- The top-degree term has exactly one index: a subset of cardinality `r` is everything. -/
theorem eq_topIdx (S : Idx r ((r : ℤ) - 1 + 1)) : S = topIdx r := by
  refine Subtype.ext ?_
  have h : (S.1.card : ℤ) = (r : ℤ) - 1 + 1 := S.2
  have hc : S.1.card = Fintype.card (Fin r) := by rw [Fintype.card_fin]; omega
  rw [Finset.card_eq_iff_eq_univ] at hc
  exact hc

/-- The complement of a subset of `Fin r` of cardinality `r - 1` is a single element. -/
theorem card_compl_eq_one (S : Idx r ((r : ℤ) - 1)) : S.1ᶜ.card = 1 := by
  have h : (S.1.card : ℤ) = (r : ℤ) - 1 := S.2
  have hle : S.1.card ≤ r := by simpa using Finset.card_le_univ S.1
  rw [Finset.card_compl, Fintype.card_fin]
  omega

/-- **The element omitted by a subset of cardinality `r - 1`.** -/
def missing (S : Idx r ((r : ℤ) - 1)) : Fin r :=
  (Finset.card_eq_one.mp (card_compl_eq_one S)).choose

/-- The complement of a subset `S` of cardinality `r - 1` is the singleton `{missing S}`. -/
theorem compl_eq_singleton_missing (S : Idx r ((r : ℤ) - 1)) : S.1ᶜ = {missing S} :=
  (Finset.card_eq_one.mp (card_compl_eq_one S)).choose_spec

/-- **The subset `{1, …, r} ∖ {i}`, as an index of degree `r - 1`.** -/
abbrev coIdx (i : Fin r) : Idx r ((r : ℤ) - 1) :=
  ⟨Finset.univ.erase i, by
    have hr : 0 < r := i.pos
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega⟩

/-- A subset of cardinality `r - 1` omits the element whose complement it is. -/
theorem missing_eq_of_val_eq_erase {S : Idx r ((r : ℤ) - 1)} {k : Fin r}
    (h : S.1 = Finset.univ.erase k) : missing S = k := by
  have h1 : S.1ᶜ = {k} := by
    rw [h, Finset.compl_erase]
    simp
  have h2 := compl_eq_singleton_missing S
  rw [h1] at h2
  exact (Finset.singleton_injective h2).symm

/-- The element omitted by `coIdx i` is `i`. -/
@[simp]
theorem missing_coIdx (i : Fin r) : missing (coIdx i) = i :=
  missing_eq_of_val_eq_erase rfl

/-- A subset of cardinality `r - 1` is the complement of the element it omits. -/
theorem coIdx_missing (S : Idx r ((r : ℤ) - 1)) : coIdx (missing S) = S := by
  refine Subtype.ext ?_
  change Finset.univ.erase (missing S) = S.1
  rw [← Finset.compl_singleton, ← compl_eq_singleton_missing S, compl_compl]

/-- The complement of `i` is contained in the full subset. -/
theorem coIdx_subset_topIdx (i : Fin r) : (coIdx i).1 ⊆ (topIdx r).1 :=
  Finset.erase_subset _ _

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

open scoped IsMulCommutative


variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-! ## The generator map -/

/-- The exponent vector with `n + 1` at the index `i` and `0` elsewhere: the monomial it names is
`f_i^{n+1}`. -/
def koszulGenExp (n : ℕ) (i : Fin r) : Fin r → ℕ := fun j => if j = i then n + 1 else 0

/-- The exponent vector of the Koszul transition map out of the complement of `i` is
`koszulGenExp n i`: the set difference `{1, …, r} ∖ ({1, …, r} ∖ {i})` is `{i}`. -/
theorem koszulExp_erase_univ (n : ℕ) (i : Fin r) :
    koszulExp n (Finset.univ.erase i) Finset.univ = koszulGenExp n i := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [koszulExp, koszulGenExp, Finset.mem_sdiff]
  · simp [koszulExp, koszulGenExp, hj, Finset.mem_sdiff, Finset.mem_erase]

variable (n : ℕ) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **Multiplication by the generators, out of the `r`-fold product**: the map `ℱ^r ⟶ ℱ` sending
`(x_1, …, x_r)` to `∑_i f_i^{n+1} x_i`. Its cokernel is `ℱ / (f_1^{n+1}, …, f_r^{n+1})ℱ`. -/
def koszulGeneratorsMap : (∏ᶜ fun _ : Fin r => M) ⟶ M :=
  ∑ i : Fin r, Pi.π (fun _ : Fin r => M) i ≫ koszulScalarOn X f (koszulGenExp n i) M

/-! ## Reindexing the products of copies of `ℱ`

The terms of the Koszul complex with coefficients are products of copies of `ℱ`, so the
constructions of this subsection involve neither the chosen sections nor the exponent. -/

section Products

variable (X : RingedSite.{u, u, u}) (r : ℕ)
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The projection of the top-degree term of the Koszul complex onto its unique factor. It is an
isomorphism, the index set of that degree having one element. -/
def koszulTopProj : (∏ᶜ fun _ : AlternatingCech.Idx r ((r : ℤ) - 1 + 1) => M) ⟶ M :=
  Pi.π (fun _ : AlternatingCech.Idx r ((r : ℤ) - 1 + 1) => M) (AlternatingCech.topIdx r)

/-- The inverse of `AlgebraicGeometry.RingedSite.koszulTopProj`: the lift whose every component
is the identity of `ℱ`. -/
def koszulTopProjInv : M ⟶ (∏ᶜ fun _ : AlternatingCech.Idx r ((r : ℤ) - 1 + 1) => M) :=
  Pi.lift fun _ => 𝟙 M

/-- Every component of `koszulTopProjInv` is the identity of `ℱ`. -/
theorem koszulTopProjInv_comp_pi (S : AlternatingCech.Idx r ((r : ℤ) - 1 + 1)) :
    koszulTopProjInv X r M ≫
        Pi.π (fun _ : AlternatingCech.Idx r ((r : ℤ) - 1 + 1) => M) S = 𝟙 M :=
  Pi.lift_π _ S

/-- The projection of the top-degree term onto its unique factor is an isomorphism. -/
instance isIso_koszulTopProj : IsIso (koszulTopProj X r M) := by
  refine ⟨koszulTopProjInv X r M, Pi.hom_ext _ _ fun S => ?_, ?_⟩
  · obtain rfl : S = AlternatingCech.topIdx r := AlternatingCech.eq_topIdx S
    rw [Category.id_comp, Category.assoc, koszulTopProjInv_comp_pi, Category.comp_id,
      koszulTopProj]
  · exact koszulTopProjInv_comp_pi X r M (AlternatingCech.topIdx r)

/-- The sign-weighted reindexing from the `r`-fold product to the term of degree `r - 1`. -/
def toCoIdxProduct :
    (∏ᶜ fun _ : Fin r => M) ⟶ (∏ᶜ fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M) :=
  Pi.lift fun S => Cech.cechSign Finset.univ (AlternatingCech.missing S) •
    Pi.π (fun _ : Fin r => M) (AlternatingCech.missing S)

/-- The sign-weighted reindexing from the term of degree `r - 1` to the `r`-fold product. -/
def fromCoIdxProduct :
    (∏ᶜ fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M) ⟶ (∏ᶜ fun _ : Fin r => M) :=
  Pi.lift fun i => Cech.cechSign Finset.univ i •
    Pi.π (fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M) (AlternatingCech.coIdx i)

/-- The component of `toCoIdxProduct` at `coIdx i` is the `i`-th projection weighted by the
sign `cechSign univ i`. -/
theorem toCoIdxProduct_comp_pi (i : Fin r) :
    toCoIdxProduct X r M ≫
        Pi.π (fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M) (AlternatingCech.coIdx i) =
      Cech.cechSign Finset.univ i • Pi.π (fun _ : Fin r => M) i := by
  refine Eq.trans (Pi.lift_π _ (AlternatingCech.coIdx i)) ?_
  rw [AlternatingCech.missing_coIdx]

/-- The `i`-th component of `fromCoIdxProduct` is the projection onto the factor `coIdx i`
weighted by the sign `cechSign univ i`. -/
theorem fromCoIdxProduct_comp_pi (i : Fin r) :
    fromCoIdxProduct X r M ≫ Pi.π (fun _ : Fin r => M) i =
      Cech.cechSign Finset.univ i •
        Pi.π (fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M) (AlternatingCech.coIdx i) :=
  Pi.lift_π _ i

end Products

/-! ## The top differential of the Koszul complex -/

/-- The last differential of the Koszul complex, read into `ℱ` through the unique top-degree
factor. -/
def koszulTopDifferential :
    (∏ᶜ fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M) ⟶ M :=
  AlternatingCech.d (koszulPowerFunctorOn X f M n) ((r : ℤ) - 1) ≫ koszulTopProj X r M

/-- The component of the top differential at the factor indexed by the complement of `i` is
multiplication by `f_i^{n+1}`. -/
theorem koszulPowerFunctorOn_map_coIdx (i : Fin r) :
    (koszulPowerFunctorOn X f M n).map
        (homOfLE (AlternatingCech.coIdx_subset_topIdx (r := r) i)) =
      koszulScalarOn X f (koszulGenExp n i) M :=
  koszulScalarOn_congr X f (fun j => by rw [koszulExp_erase_univ]) M

/-- The top differential is the sign-weighted sum, over the indices `i`, of the projection onto
the factor indexed by the complement of `i` followed by multiplication by `f_i^{n+1}`. -/
theorem koszulTopDifferential_eq :
    koszulTopDifferential X f n M =
      ∑ i : Fin r, Cech.cechSign Finset.univ i •
        (Pi.π (fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M) (AlternatingCech.coIdx i) ≫
          koszulScalarOn X f (koszulGenExp n i) M) := by
  have hd := AlternatingCech.d_comp_pi (koszulPowerFunctorOn X f M n) ((r : ℤ) - 1)
    (AlternatingCech.topIdx r)
  refine hd.trans ?_
  have step : ∀ k : ((AlternatingCech.topIdx r).1 : Finset (Fin r)),
      Cech.cechSign (AlternatingCech.topIdx r).1 k.1 •
          AlternatingCech.proj (koszulPowerFunctorOn X f M n)
            ((AlternatingCech.topIdx r).erase k)
            ((AlternatingCech.topIdx r).erase_subset k) =
        Cech.cechSign Finset.univ k.1 •
          (Pi.π (fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M)
              (AlternatingCech.coIdx k.1) ≫
            koszulScalarOn X f (koszulGenExp n k.1) M) := by
    intro k
    exact congrArg
      (fun φ : M ⟶ M => Cech.cechSign Finset.univ k.1 •
        (Pi.π (fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M)
            (AlternatingCech.coIdx k.1) ≫ φ))
      (koszulPowerFunctorOn_map_coIdx X f n M k.1)
  refine Eq.trans (Finset.sum_congr rfl fun k _ => step k) ?_
  exact Finset.sum_attach Finset.univ fun i => Cech.cechSign Finset.univ i •
    (Pi.π (fun _ : AlternatingCech.Idx r ((r : ℤ) - 1) => M) (AlternatingCech.coIdx i) ≫
      koszulScalarOn X f (koszulGenExp n i) M)

/-! ## The two factorizations -/

/-- **The generator map factors through the top differential.** -/
theorem koszulGeneratorsMap_eq_comp :
    toCoIdxProduct X r M ≫ koszulTopDifferential X f n M = koszulGeneratorsMap X f n M := by
  rw [koszulTopDifferential_eq, Preadditive.comp_sum, koszulGeneratorsMap]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.comp_zsmul, ← Category.assoc, toCoIdxProduct_comp_pi,
    Preadditive.zsmul_comp, smul_smul, Cech.cechSign_mul_self, one_smul]

/-- **The top differential factors through the generator map.** -/
theorem koszulTopDifferential_comp_eq :
    fromCoIdxProduct X r M ≫ koszulGeneratorsMap X f n M = koszulTopDifferential X f n M := by
  rw [koszulGeneratorsMap, koszulTopDifferential_eq, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Category.assoc, fromCoIdxProduct_comp_pi, Preadditive.zsmul_comp]

/-! ## The identification of the top cohomology sheaf -/

/-- The term of the Koszul complex just above the top degree is a product over an empty index
set, so every morphism into it is zero.

The top degree is spelled `r - 1 + 1` here, as everywhere in this file; the same statement at the
degree `r` is `AlgebraicGeometry.RingedSite.koszulPowerComplexOn_d_top_eq_zero` of
`KoszulDualProZero.lean`, and the prime distinguishes the two spellings exactly as it does for
`AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap'`. -/
theorem koszulPowerComplexOn_d_top_eq_zero' :
    (koszulPowerComplexOn X f M n).d ((r : ℤ) - 1 + 1) ((r : ℤ) - 1 + 1 + 1) = 0 :=
  Pi.hom_ext _ _ fun S =>
    (AlternatingCech.isEmpty_idx_of_lt (r := r) (by omega)).elim S

/-- **The cohomology sheaf of the Koszul complex with coefficients in `ℱ` in the top degree is
the quotient `ℱ / (f_1^{n+1}, …, f_r^{n+1})ℱ`**, presented as the cokernel of the map
`ℱ^r ⟶ ℱ`, `(x_i) ↦ ∑_i f_i^{n+1} x_i`.

The degree is written `r - 1 + 1`; see
`AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap` for the same statement at
the degree `r`. -/
def homologyIsoCokernelKoszulGeneratorsMap' :
    (koszulPowerComplexOn X f M n).homology ((r : ℤ) - 1 + 1) ≅
      cokernel (koszulGeneratorsMap X f n M) := by
  -- The projection is an isomorphism; the instance is restated at the spelling of its source
  -- that the differential of the complex produces, namely the term of the complex.
  haveI hiso : @IsIso _ _
      (AlternatingCech.term (koszulPowerFunctorOn X f M n) ((r : ℤ) - 1 + 1)) M
      (koszulTopProj X r M) := isIso_koszulTopProj X r M
  exact
    (koszulPowerComplexOn X f M n).isoHomologyι ((r : ℤ) - 1 + 1) ((r : ℤ) - 1 + 1 + 1)
        (CochainComplex.next ℤ _) (koszulPowerComplexOn_d_top_eq_zero' X f n M) ≪≫
      IsColimit.coconePointUniqueUpToIso
        ((koszulPowerComplexOn X f M n).opcyclesIsCokernel
          (i := (r : ℤ) - 1) (j := (r : ℤ) - 1 + 1)
          ((ComplexShape.up ℤ).prev_eq' rfl))
        (cokernelIsCokernel _) ≪≫
      cokernelIsoOfEq (AlternatingCech.complex_d (koszulPowerFunctorOn X f M n) ((r : ℤ) - 1)) ≪≫
      (cokernelCompIsIso (AlternatingCech.d (koszulPowerFunctorOn X f M n) ((r : ℤ) - 1))
        (koszulTopProj X r M)).symm ≪≫
      Stacks.cokernelIsoOfFactors (koszulTopDifferential X f n M) (koszulGeneratorsMap X f n M)
        (toCoIdxProduct X r M) (koszulGeneratorsMap_eq_comp X f n M)
        (fromCoIdxProduct X r M) (koszulTopDifferential_comp_eq X f n M)

/-- **The cohomology sheaf of the Koszul complex with coefficients in `ℱ` in degree `r` is the
quotient `ℱ / (f_1^{n+1}, …, f_r^{n+1})ℱ`.**

In the grading of [Stacks, Tag 0913] — the Koszul complex placed in the degrees `-r, …, 0` — this
is the statement that `H⁰(ℱ ⊗ K(𝒪, f_1^{n+1}, …, f_r^{n+1}))` is
`ℱ / (f_1^{n+1}, …, f_r^{n+1})ℱ`; here the complex sits in the degrees `0, …, r`, so the quotient
is the cohomology sheaf in degree `r`. -/
def homologyIsoCokernelKoszulGeneratorsMap :
    (koszulPowerComplexOn X f M n).homology (r : ℤ) ≅
      cokernel (koszulGeneratorsMap X f n M) := by
  have h : ((r : ℤ) - 1 + 1) = (r : ℤ) := by ring
  rw [← h]
  exact homologyIsoCokernelKoszulGeneratorsMap' X f n M

/-- The Koszul complex with coefficients has no cohomology in a degree whose index set is empty. -/
private theorem isZero_homology_koszulPowerComplexOn_of_isEmpty_idx {p : ℤ}
    (h : IsEmpty (AlternatingCech.Idx r p)) :
    IsZero ((koszulPowerComplexOn X f M n).homology p) := by
  have hX : IsZero ((koszulPowerComplexOn X f M n).X p) := by
    rw [IsZero.iff_id_eq_zero]
    exact Pi.hom_ext _ _ fun S => h.elim S
  exact ((koszulPowerComplexOn X f M n).sc p).isZero_homology_of_isZero_X₂ hX

/-- The Koszul complex with coefficients has no cohomology in negative degrees: its terms there
are products over empty index sets. -/
theorem isZero_homology_koszulPowerComplexOn_of_neg {p : ℤ} (hp : p < 0) :
    IsZero ((koszulPowerComplexOn X f M n).homology p) :=
  isZero_homology_koszulPowerComplexOn_of_isEmpty_idx X f n M
    (AlternatingCech.isEmpty_idx_of_neg hp)

/-- The Koszul complex with coefficients has no cohomology above degree `r`. -/
theorem isZero_homology_koszulPowerComplexOn_of_gt {p : ℤ} (hp : (r : ℤ) < p) :
    IsZero ((koszulPowerComplexOn X f M n).homology p) :=
  isZero_homology_koszulPowerComplexOn_of_isEmpty_idx X f n M
    (AlternatingCech.isEmpty_idx_of_lt hp)

end AlgebraicGeometry.RingedSite

end
