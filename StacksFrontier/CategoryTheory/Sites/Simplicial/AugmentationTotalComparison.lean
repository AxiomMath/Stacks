module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationSpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagTotal

/-!
# The total complex of the augmentation double complex computes the total direct image

Let `S` be a simplicial-site situation (Stacks 09WE), let `a` be an augmentation of `S` towards a
site `(D, K)` (Stacks 0D6Z) and let `Z^•` be a bounded below complex of injective abelian sheaves
on the total site. The double complex

```
A^{q,p} = a_{p,*} Z^q_p
```

(`doubleComplexFunctor`) has, by Stacks 0D79, rows exact away from simplicial degree `0`, and in
simplicial degree `0` the augmentation `a_* Z^q → a_{0,*} Z^q_0` is a kernel of the first
differential. These are the hypotheses of Stacks 0133, so the induced comparison

```
a_* Z^• ⟶ Tot(A^{•,•})
```

is a quasi-isomorphism.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.totalAugmentationNat`: the augmentation
  `a_* Z^• ⟶ A^{•,0}` into the zeroth row of the double complex, natural in `Z^•`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.totalComparisonMap`: the comparison map of
  Stacks 0133, `a_* Z^• ⟶ Tot(A^{•,•})`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.exactAt_degreewisePushforwardComplexNat`:
  the complex `a_{0,*} F_0 → a_{1,*} F_1 → …` of an injective abelian sheaf is exact in positive
  degrees (Stacks 0D79).
* `CategoryTheory.SimplicialSiteSituation.Augmentation.totalHypotheses`: the hypotheses of
  Stacks 0133 for the double complex of a bounded below complex of injective abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.totalComparisonHomologyIso`:
  `H^n(a_* Z^•) ≅ H^n(Tot(A^{•,•}))`.

## References

* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

attribute [local instance] abelianSheafTarget abelianSheafTotal hasInjectiveResolutionsSheafTotal
  hasZeroObjectSheafTotal hasColimitsOfSizeSheafTarget hasColimitsOfShapeDiscreteSheafTarget

/-! ### The rows of the double complex -/

/-- **Stacks 0D79 in positive degrees, without the augmentation.** For an injective abelian sheaf
`F` on the total site the complex `a_{0,*}F_0 → a_{1,*}F_1 → a_{2,*}F_2 → …` is exact in every
positive degree. -/
theorem exactAt_degreewisePushforwardComplexNat (F : Sheaf S.totalTopology AddCommGrpCat.{u})
    [Injective F] (k : ℕ) (hk : 0 < k) :
    ((degreewisePushforwardComplexNat S D K a).obj F).ExactAt k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := augmentedCechComplex_exactAt_of_injective S D K a F (j + 2)
  rw [HomologicalComplex.exactAt_iff' _ (j + 1) (j + 2) (j + 3) (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 2) (by simp) (by simp)]
  exact h

/-- Evaluating the complex of degreewise direct images, extended by zero, in simplicial degree
`0` gives `a_{0,*}(-)_0`. -/
def degreewisePushforwardComplexCompEvalZero :
    degreewisePushforwardComplex S D K a ⋙
        HomologicalComplex.eval (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) (0 : ℤ) ≅
      abelianComponentPushforward S D K a ⦋0⦌ :=
  Functor.isoWhiskerLeft (degreewisePushforwardComplexNat S D K a)
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso (Sheaf K AddCommGrpCat.{u})
      (i := 0) (i' := (0 : ℤ)) rfl)

/-- The augmentation `a_* ⟶ a_{0,*}(-)_0` of the complex of Stacks 0D79. -/
abbrev augmentationNatTrans :
    abelianTotalPushforward S D K a ⟶ abelianComponentPushforward S D K a ⦋0⦌ :=
  (abelianCechConeNatTrans S D K a).app ⦋0⦌

variable [HasSheafify K AddCommGrpCat.{u}]

/-- **The augmentation `a_* Z^• ⟶ A^{•,0}` into the zeroth row of the double complex**, as a
natural transformation in the complex `Z^•`: in degree `q` it is the augmentation of the complex
of Stacks 0D79 at the sheaf `Z^q`. -/
def totalAugmentationNat :
    (abelianTotalPushforward S D K a).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      doubleComplexFunctor S D K a ⋙ rowZeroFunctor (Sheaf K AddCommGrpCat.{u}) :=
  NatTrans.mapHomologicalComplex (augmentationNatTrans S D K a) (ComplexShape.up ℤ) ≫
    (NatIso.mapHomologicalComplex (degreewisePushforwardComplexCompEvalZero S D K a)
      (ComplexShape.up ℤ)).inv ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (degreewisePushforwardComplex S D K a ⋙
      HomologicalComplex.eval (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) (0 : ℤ)))
      (ComplexShape.up ℤ)).inv

/-! ### The hypotheses of Stacks 0133 -/

variable (Z : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ)

/-- The double complex vanishes in negative simplicial degrees. -/
theorem isZero_doubleComplexFunctor_X_X_of_neg (q p : ℤ) (hp : p < 0) :
    IsZero ((((doubleComplexFunctor S D K a).obj Z).X q).X p) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
    fun i => by change ((i : ℕ) : ℤ) ≠ p; omega

/-- **The antidiagonals of the double complex are finite** for a bounded below complex: a nonzero
term `A^{q,p}` has `q ≥ n` and `p ≥ 0`. -/
theorem diagonalFinite_doubleComplexFunctor (n : ℤ) [Z.IsStrictlyGE n] :
    DiagonalFinite ((doubleComplexFunctor S D K a).obj Z) := by
  intro m
  refine Set.Finite.subset (Set.finite_Icc n m) fun q hq => ?_
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hq ((HomologicalComplex.eval _ _ (m - q)).map_isZero
      ((degreewisePushforwardComplex S D K a).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE Z n q (by omega))))
  · by_contra h
    exact hq (isZero_doubleComplexFunctor_X_X_of_neg S D K a Z q (m - q) (by omega))

/-- **The rows of the double complex are exact away from simplicial degree `0`** for a complex of
injective abelian sheaves. -/
theorem exactAt_doubleComplexFunctor_X (hinj : ∀ q : ℤ, Injective (Z.X q)) (q p : ℤ)
    (hp : p ≠ 0) : (((doubleComplexFunctor S D K a).obj Z).X q).ExactAt p := by
  rcases lt_trichotomy p 0 with h | h | h
  · exact HomologicalComplex.extend_exactAt _ ComplexShape.embeddingUpNat p
      fun j => by change ((j : ℕ) : ℤ) ≠ p; omega
  · exact absurd h hp
  · have hk : ComplexShape.embeddingUpNat.f p.toNat = p := by
      show ((p.toNat : ℕ) : ℤ) = p; omega
    refine (HomologicalComplex.extend_exactAt_iff _ ComplexShape.embeddingUpNat hk).2 ?_
    have := hinj q
    exact exactAt_degreewisePushforwardComplexNat S D K a (Z.X q) p.toNat (by omega)

/-- **The augmentation is a kernel of the first differential in every degree.** This is the
exactness of the complex of Stacks 0D79 in degrees `-1` and `0`. -/
theorem inducesIsoKernel_totalAugmentation (q : ℤ) :
    ∃ hα : ((totalAugmentationNat S D K a).app Z).f q ≫
        (((doubleComplexFunctor S D K a).obj Z).X q).d 0 1 = 0,
      IsIso (kernel.lift ((((doubleComplexFunctor S D K a).obj Z).X q).d 0 1)
        (((totalAugmentationNat S D K a).app Z).f q) hα) := by
  have hc := CosimplicialObject.isLimitKernelFork (abelianCechDiagram S D K a (Z.X q))
    (abelianCechCone S D K a (Z.X q)) (abelianCechCone_isLimit S D K a (Z.X q))
  exact inducesIsoKernel_extendAugmentation
    ((alternatingCofaceMapComplex _).obj (abelianCechDiagram S D K a (Z.X q)))
    ((abelianCechCone S D K a (Z.X q)).π.app ⦋0⦌)
    (CosimplicialObject.coneLeg_comp_d _ _) (mono_of_isLimit_fork hc)
    (ShortComplex.exact_of_f_is_kernel _ hc) rfl rfl _ rfl

/-- **The hypotheses of Stacks 0133 for the double complex `A^{q,p} = a_{p,*} Z^q_p`** of a
bounded below complex of injective abelian sheaves on the total site. -/
theorem totalHypotheses (n : ℤ) [Z.IsStrictlyGE n] (hinj : ∀ q : ℤ, Injective (Z.X q)) :
    Hypotheses (((abelianTotalPushforward S D K a).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z) ((doubleComplexFunctor S D K a).obj Z)
      ((totalAugmentationNat S D K a).app Z) where
  diagonalFinite := diagonalFinite_doubleComplexFunctor S D K a Z n
  zero_of_neg q p hp := isZero_doubleComplexFunctor_X_X_of_neg S D K a Z q p hp
  exactAt_of_ne_zero := exactAt_doubleComplexFunctor_X S D K a Z hinj
  inducesIsoKernel := inducesIsoKernel_totalAugmentation S D K a Z

/-! ### The comparison with the total complex -/

variable (n : ℤ) [Z.IsStrictlyGE n] (hinj : ∀ q : ℤ, Injective (Z.X q))

/-- **The comparison map of Stacks 0133** for the double complex `A^{q,p} = a_{p,*} Z^q_p`:
`a_* Z^• ⟶ Tot(A^{•,•})`, in degree `m` the augmentation of Stacks 0D79 followed by the inclusion
of the summand `A^{m,0}`. -/
def totalComparisonMap :
    ((abelianTotalPushforward S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ⟶
      ((doubleComplexFunctor S D K a).obj Z).total (ComplexShape.up ℤ) :=
  comparisonMapP _ _ _ (totalHypotheses S D K a Z n hinj)

/-- The comparison map `a_* Z^• ⟶ Tot(A^{•,•})` is a quasi-isomorphism. -/
instance quasiIso_totalComparisonMap : QuasiIso (totalComparisonMap S D K a Z n hinj) :=
  quasiIso_comparisonMapP _ _ _ _

/-- **`H^m(a_* Z^•) ≅ H^m(Tot(A^{•,•}))`** for a bounded below complex `Z^•` of injective abelian
sheaves on the total site: Stacks 0133 for the double complex `A^{q,p} = a_{p,*} Z^q_p`. -/
def totalComparisonHomologyIso (m : ℤ) :
    (((abelianTotalPushforward S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z).homology
        m ≅
      (((doubleComplexFunctor S D K a).obj Z).total (ComplexShape.up ℤ)).homology m :=
  comparisonHomologyIso _ _ _ (totalHypotheses S D K a Z n hinj) m

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
