module

public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.FilteredHomotopicSteps
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.StupidTruncation
public import StacksFrontier.Homology.FilteredDerivedCategory.InjectiveResolutions

/-!
# The first total filtration of a Cartan-Eilenberg resolution

Let `K^•` be a cochain complex of an abelian category and let `I^{•,•}` be a Cartan-Eilenberg
resolution of it ([Stacks, Tag 015H]). The total complex `Tot(I)` is a complex of injective
objects quasi-isomorphic to `K^•`, and the filtration of `Tot(I)` by the first coordinate,
`F^pTot(I)^n = ⨁_{i + j = n, i ≥ p}I^{i,j}`, is the filtered complex whose spectral sequence is
the first spectral sequence of [Stacks, Tag 015J].

This file records what that filtered complex is: it is finite in every degree, its graded pieces
are the columns of `I` and in particular have injective terms, so it is a complex of filtered
injective objects; and the augmentation `K^• ⟶ Tot(I)` of
`StacksDraft.CartanEilenbergResolutions.totalAugmentation` is filtered for the brutal truncation
filtration `σ_{≥ p}K^•` of the source.

That last point is the geometric content: `K^n` enters `Tot(I)^n` through the single summand
`I^{n,0}`, whose first coordinate is `n`, so the subcomplex `σ_{≥ p}K^•` lands in `F^pTot(I)`.

## Main results

* `StacksDraft.CartanEilenbergResolutions.isDegreewiseFinite_totalFiltration₁`: the filtration is
  finite in every degree.
* `StacksDraft.CartanEilenbergResolutions.injective_gradedPiece_totalFiltration₁_X`: the terms of
  the graded pieces are injective.
* `StacksDraft.CartanEilenbergResolutions.isFilteredInjective_evalFil_totalFiltration₁`: the
  filtered complex is a complex of filtered injective objects.
* `StacksDraft.CartanEilenbergResolutions.filteredTotalAugmentation`: the augmentation
  `σ_{≥ •}K^• ⟶ F^•Tot(I)`.

## References

* [Stacks Project, Tag 015H](https://stacks.math.columbia.edu/tag/015H)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace StacksDraft.CartanEilenbergResolutions

variable {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (I : K.CartanEilenbergResolution)
  [I.bicomplex.HasTotal (ComplexShape.up ℤ)]

/-- **The first total filtration of a Cartan-Eilenberg resolution is finite in every degree.**
On each antidiagonal only finitely many terms of `I` are nonzero
(`finite_not_isZero_bicomplex`), so the first coordinates occurring in `Tot(I)^n` are bounded
both ways. -/
lemma isDegreewiseFinite_totalFiltration₁ :
    I.bicomplex.totalFiltration₁.filtration.IsDegreewiseFinite :=
  HomologicalComplex₂.isDegreewiseFinite_totalFiltration₁ _
    (fun n => finite_not_isZero_bicomplex I n)

/-- The first total filtration is bounded below, by the bound of condition (1) of
[Stacks, Tag 015H] for `I`. -/
lemma exists_isStrictlyGE_totalFiltration₁ :
    ∃ b : ℤ, I.bicomplex.totalFiltration₁.X.IsStrictlyGE b :=
  plus_total I

/-- **The terms of the graded pieces of the first total filtration are injective.** The `p`-th
graded piece of `Tot(I)` filtered by the first coordinate is the column `I^{p,•}` placed in first
degree `p`, so its term in total degree `n` is `I^{p, n - p}`, injective by condition (3) of
[Stacks, Tag 015H].

The identification is read off the zeroth page of the spectral sequence of the filtered complex,
which `FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage` identifies with the
graded pieces and `HomologicalComplex₂.exists_iso_pages_totalFiltration₁` ([Stacks, Tag 0130])
identifies with the terms of `I`. -/
lemma injective_gradedPiece_totalFiltration₁_X (p n : ℤ) :
    Injective (((FilteredObject.gr p).obj I.bicomplex.totalFiltration₁).X n) := by
  let T := I.bicomplex.totalFiltration₁
  let F : ∀ (_p n : ℤ), Subobject (T.X.X n) := fun p n =>
    CochainComplex.filtrationSubobject T p n
  have hF (p n : ℤ) : F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n) := rfl
  let Z : ∀ (_r _p n : ℤ), Subobject (T.X.X n) := fun r p n =>
    FilteredComplexSpectralSequence.cycles T.X F r p n
  have hZ (r p n : ℤ) : Z r p n =
      F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1)) := rfl
  let D : ∀ (_r _p n : ℤ), Subobject (T.X.X n) := fun r p n =>
    FilteredComplexSpectralSequence.boundaries T.X F r p n
  have hD (r p n : ℤ) : D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)) := rfl
  have hanti := CochainComplex.antitone_of_eq T F hF
  let E := FilteredComplexSpectralSequence.spectralSequence T.X F hanti
  have hpages := HomologicalComplex₂.exists_iso_pages_totalFiltration₁ I.bicomplex F hF Z hZ D hD E
    (fun r p q n hr hn => FilteredComplexSpectralSequence.eIso T.X F hanti r p q n hr hn)
    (fun r p q n hr hn => ⟨FilteredComplexSpectralSequence.deltaCycles T.X F r p n,
      FilteredComplexSpectralSequence.deltaCycles_arrow T.X F r p n, by
      subst hn
      rw [FilteredComplexSpectralSequence.spectralSequence_d,
        FilteredComplexSpectralSequence.eIso_inv_rfl, Category.id_comp,
        ← Category.assoc, FilteredComplexSpectralSequence.π_comp_pageMap, Category.assoc]⟩)
  obtain ⟨α, -⟩ := hpages.1
  obtain ⟨β, -⟩ := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage T F hF hanti
  have e : ((FilteredObject.gr p).obj T).X n ≅ (I.bicomplex.X p).X (n - p) :=
    (β p (n - p) n (by omega)).symm ≪≫ α p (n - p)
  exact Injective.of_iso e.symm (I.injective p (n - p))

/-- **The first total filtration of a Cartan-Eilenberg resolution is a complex of filtered
injective objects**: it is finite in every degree and its graded pieces have injective terms. -/
lemma isFilteredInjective_evalFil_totalFiltration₁ (n : ℤ) :
    (CochainComplex.evalFil I.bicomplex.totalFiltration₁ n).IsFilteredInjective :=
  (CochainComplex.isFilteredInjective_evalFil_iff I.bicomplex.totalFiltration₁ n).2
    ⟨isDegreewiseFinite_totalFiltration₁ I n,
      fun p => injective_gradedPiece_totalFiltration₁_X I p n⟩



section Augmentation

/-- The predicate cutting out the summands of `Tot(I)^n` lying in `F^pTot(I)^n`, namely those of
first coordinate at least `p`. -/
abbrev totalFiltration₁Pred (p : ℤᵒᵖ) : ℤ → ℤ → Prop := fun i _ => p.unop ≤ i

/-- The inclusion `F^pTot(I)^n ⟶ Tot(I)^n`, at the spelling consumers present.  Written through
`CochainComplex.filtrationStepι`, whose ascribed type crosses the `Functor.const` seam in the
codomain of `CategoryTheory.FilteredObject.Filtration.ι` once and for all. -/
abbrev totalFiltration₁ι (p : ℤᵒᵖ) (n : ℤ) :
    (I.bicomplex.totalFiltration₁.filtration.obj p).X n ⟶
      (I.bicomplex.total (ComplexShape.up ℤ)).X n :=
  (CochainComplex.filtrationStepι I.bicomplex.totalFiltration₁ p).f n

instance (p : ℤᵒᵖ) (n : ℤ) : Mono (totalFiltration₁ι I p n) :=
  inferInstanceAs
    (Mono (imageSubobject (I.bicomplex.totalProjector (totalFiltration₁Pred p) n)).arrow)

/-- The inclusion `(σ_{≥ p}K^•)^n ⟶ K^n`, at the spelling consumers present; see
`totalFiltration₁ι`. -/
abbrev stupidTruncationFiltrationι (p : ℤᵒᵖ) (n : ℤ) :
    ((CochainComplex.stupidTruncationFiltration K).filtration.obj p).X n ⟶ K.X n :=
  (CochainComplex.filtrationStepι (CochainComplex.stupidTruncationFiltration K) p).f n

/-- **The augmentation `K^• ⟶ Tot(I)` carries `σ_{≥ p}K^•` into `F^pTot(I)`.**

In degree `n` the augmentation is `K^n ⟶ I^{n,0} ⟶ Tot(I)^n`, landing in the single summand of
first coordinate `n`.  For `p ≤ n` that summand is one of those `F^pTot(I)^n` is the image of, so
the projector cutting out `F^pTot(I)^n` fixes the composite; for `p > n` the source
`(σ_{≥ p}K^•)^n` vanishes and the composite is zero.  Either way the composite is fixed by the
projector, hence factors through its image, which is the required factorization. -/
lemma factors_totalAugmentation (p : ℤᵒᵖ) (n : ℤ) :
    (imageSubobject (I.bicomplex.totalProjector (totalFiltration₁Pred p) n)).Factors
      (stupidTruncationFiltrationι (K := K) p n ≫ totalAugmentationf I n) := by
  set g := stupidTruncationFiltrationι (K := K) p n ≫ totalAugmentationf I n with hg
  have h : g ≫ I.bicomplex.totalProjector (totalFiltration₁Pred p) n = g := by
    rw [hg]
    by_cases hp : p.unop ≤ n
    · dsimp only [totalAugmentationf]
      simp only [Category.assoc, HomologicalComplex₂.ι_totalProjector]
      simp [totalFiltration₁Pred, hp]
    · have hz : IsZero
          (((CochainComplex.stupidTruncationFiltration K).filtration.obj p).X n) :=
        CochainComplex.isZero_of_isStrictlyGE
          (K.stupidTrunc (ComplexShape.embeddingUpIntGE p.unop)) p.unop n (by omega)
      rw [hz.eq_of_src (stupidTruncationFiltrationι (K := K) p n) 0, zero_comp, zero_comp]
  have hle : imageSubobject g ≤
      imageSubobject (I.bicomplex.totalProjector (totalFiltration₁Pred p) n) := by
    apply imageSubobject_le g
      (g ≫ factorThruImageSubobject (I.bicomplex.totalProjector (totalFiltration₁Pred p) n))
    rw [Category.assoc, imageSubobject_arrow_comp]
    exact h
  exact Subobject.factors_of_le g hle
    (by simpa using imageSubobject_factors_comp_self g (𝟙 _))

/-- The inclusion of the `p`-th step of the first total filtration commutes with the
differentials, stated at the spelling the step map's commutation square presents. -/
lemma totalFiltration₁_d_ι (p : ℤᵒᵖ) (n n' : ℤ) :
    (I.bicomplex.totalFiltration₁.filtration.obj p).d n n' ≫ totalFiltration₁ι I p n' =
      totalFiltration₁ι I p n ≫ (I.bicomplex.total (ComplexShape.up ℤ)).d n n' :=
  CochainComplex.filtrationStepι_comm I.bicomplex.totalFiltration₁ p n n'

/-- The inclusion of the `p`-th brutal truncation step commutes with the differentials, stated at
the spelling the step map's commutation square presents. -/
lemma stupidTruncationFiltration_d_ι (p : ℤᵒᵖ) (n n' : ℤ) :
    ((CochainComplex.stupidTruncationFiltration K).filtration.obj p).d n n' ≫
        stupidTruncationFiltrationι (K := K) p n' =
      stupidTruncationFiltrationι (K := K) p n ≫ K.d n n' :=
  CochainComplex.filtrationStepι_comm (CochainComplex.stupidTruncationFiltration K) p n n'

/-- The degree-`n` component of the `p`-th step of the filtered augmentation. -/
def filteredTotalAugmentationStepf (p : ℤᵒᵖ) (n : ℤ) :
    ((CochainComplex.stupidTruncationFiltration K).filtration.obj p).X n ⟶
      (I.bicomplex.totalFiltration₁.filtration.obj p).X n :=
  Subobject.factorThru _ _ (factors_totalAugmentation I p n)

lemma filteredTotalAugmentationStepf_ι (p : ℤᵒᵖ) (n : ℤ) :
    filteredTotalAugmentationStepf I p n ≫ totalFiltration₁ι I p n =
      stupidTruncationFiltrationι (K := K) p n ≫ totalAugmentationf I n :=
  Subobject.factorThru_arrow _ _ (factors_totalAugmentation I p n)

/-- The `p`-th step of the filtered augmentation, `σ_{≥ p}K^• ⟶ F^pTot(I)`. -/
def filteredTotalAugmentationStep (p : ℤᵒᵖ) :
    (CochainComplex.stupidTruncationFiltration K).filtration.obj p ⟶
      I.bicomplex.totalFiltration₁.filtration.obj p where
  f n := filteredTotalAugmentationStepf I p n
  comm' n n' _ := by
    have h : totalAugmentationf I n ≫ (I.bicomplex.total (ComplexShape.up ℤ)).d n n' =
        K.d n n' ≫ totalAugmentationf I n' := by
      simpa using (totalAugmentation I).comm n n'
    rw [← cancel_mono (totalFiltration₁ι I p n')]
    simp only [Category.assoc]
    rw [totalFiltration₁_d_ι]
    conv_lhs => rw [← Category.assoc, filteredTotalAugmentationStepf_ι, Category.assoc, h]
    conv_rhs => rw [filteredTotalAugmentationStepf_ι, ← Category.assoc,
      stupidTruncationFiltration_d_ι, Category.assoc]

/-- **The filtered augmentation `σ_{≥ •}K^• ⟶ F^•Tot(I)`.**  The source is the brutal truncation
filtration of `K^•`, whose spectral sequence is the one of [Stacks, Tag 0FLK]; the target is the
first total filtration of a Cartan-Eilenberg resolution of `K^•`, whose spectral sequence is the
first spectral sequence of [Stacks, Tag 015J].  This is the morphism of filtered complexes which
compares the two, and its underlying map is the augmentation `K^• ⟶ Tot(I)`. -/
def filteredTotalAugmentation :
    CochainComplex.stupidTruncationFiltration K ⟶ I.bicomplex.totalFiltration₁ :=
  FilteredObject.homMk (totalAugmentation I) (filteredTotalAugmentationStep I)
    (fun p => by
      apply HomologicalComplex.Hom.ext
      funext n
      exact filteredTotalAugmentationStepf_ι I p n)

@[simp]
lemma filteredTotalAugmentation_hom :
    (filteredTotalAugmentation I).hom = totalAugmentation I :=
  rfl

@[simp]
lemma filteredTotalAugmentation_natTrans_app (p : ℤᵒᵖ) :
    (filteredTotalAugmentation I).natTrans.app p = filteredTotalAugmentationStep I p :=
  rfl

end Augmentation

end StacksDraft.CartanEilenbergResolutions

end
