module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedPlusDoubleComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagTotal

/-!
# The spectral sequence of an augmented functor to complexes in non-negative degrees

Let `A` and `B` be abelian categories, `A` with enough injectives. This file specialises the
spectral sequence of
`StacksFrontier/Algebra/Homology/SpectralSequence/DerivedPlusDoubleComplex.lean`
to the shape in which the source's applications meet it: an additive functor
`C : A ⥤ C^{≥0}(B)` to complexes indexed by `ℕ`, with an augmentation `ε : T ⟶ C(-)^0` from an
additive functor `T : A ⥤ B`, such that

* for every `X` the sequence `0 ⟶ T(X) ⟶ C(X)^0 ⟶ C(X)^1` is exact, and
* for every injective `X` the complex `C(X)` is exact in positive degrees.

Extending `C` by zero to complexes indexed by `ℤ`, the double complex `C(I^•)` of a bounded
below complex of injectives `I^•` then satisfies the hypotheses of Stacks 0133, so the spectral
sequence of its filtration by the degree of `C`, which has `E_1^{p,q} = H^q(C(I^•)^p)`, abuts
to `H^n(RT(K))` for the object `K` of `D⁺(A)` represented by `I^•`. Its first page vanishes in
the negative columns.

This is the shape of the proofs of Stacks 0D7A and Stacks 0D7F: there `C(F)` is the complex
`a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …` of Stacks 0D79, resp. Stacks 0D7D, and `T = a_*`.

## Main definitions

* `Stacks.DegreewiseSpectralSequence.natExtend`: the functor `C` extended by zero to complexes
  indexed by `ℤ`.
* `Stacks.DegreewiseSpectralSequence.natExtendAugmentation`: the augmentation
  `T(Z^•) ⟶ C(Z^•)^0` into the zeroth row of the double complex.

## Main results

* `Stacks.DegreewiseSpectralSequence.hypotheses_natExtend`: the hypotheses of Stacks 0133 for a
  bounded below complex of injectives.
* `Stacks.DegreewiseSpectralSequence.natExtendPageOneIsoOfRightAcyclic`:
  `E_1^{p,q} ≅ H^q(RP(R K))`, naturally in `K`, for `C(-)^p ≅ R ⋙ P`.
* `Stacks.DegreewiseSpectralSequence.isZero_natExtend_page_one`: the first page vanishes in the
  negative columns.
* `Stacks.DegreewiseSpectralSequence.abutsTo_natExtend`: the abutment is `H^n(RT(K))`.

## References

* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0D7F](https://stacks.math.columbia.edu/tag/0D7F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DegreewiseSpectralSequence

variable {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]
  (C : A ⥤ CochainComplex B ℕ) [C.Additive]

/-! ### Extension by zero -/

/-- The functor `C` to complexes indexed by `ℕ`, extended by zero to complexes indexed by `ℤ`. -/
abbrev natExtend : A ⥤ CochainComplex B ℤ :=
  C ⋙ ComplexShape.embeddingUpNat.extendFunctor B

/-- The term in a non-negative degree `p` of the extended functor is the term of `C`. -/
def natExtendCompEvalIso (p : ℕ) :
    natExtend C ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) (p : ℤ) ≅
      C ⋙ HomologicalComplex.eval B (ComplexShape.up ℕ) p :=
  Functor.isoWhiskerLeft C
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso B (i := p) (i' := (p : ℤ)) rfl)

omit [Abelian A] [C.Additive] in
/-- The extended functor vanishes in negative degrees. -/
theorem isZero_natExtend_obj_X (X : A) (p : ℤ) (hp : p < 0) :
    IsZero (((natExtend C).obj X).X p) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
    fun i => by change ((i : ℕ) : ℤ) ≠ p; omega

/-! ### The augmentation -/

variable (T : A ⥤ B) [T.Additive] (ε : T ⟶ C ⋙ HomologicalComplex.eval B (ComplexShape.up ℕ) 0)

/-- **The augmentation `T(Z^•) ⟶ C(Z^•)^0` into the zeroth row of the double complex**, as a
natural transformation in the complex `Z^•`: in degree `q` it is `ε` at `Z^q`. -/
def natExtendAugmentation :
    T.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (natExtend C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ rowZeroFunctor B :=
  NatTrans.mapHomologicalComplex ε (ComplexShape.up ℤ) ≫
    (NatIso.mapHomologicalComplex (natExtendCompEvalIso C 0) (ComplexShape.up ℤ)).inv ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (natExtend C ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) (0 : ℤ)))
      (ComplexShape.up ℤ)).inv

/-- The component in degree `q` of the augmentation is `ε` at `Z^q`, followed by the
identification of the degree `0` term of the extension. -/
theorem natExtendAugmentation_app_f (Z : CochainComplex A ℤ) (q : ℤ) :
    ((natExtendAugmentation C T ε).app Z).f q =
      ε.app (Z.X q) ≫ ((C.obj (Z.X q)).extendXIso ComplexShape.embeddingUpNat
        (i := 0) (i' := (0 : ℤ)) rfl).inv := by
  change ε.app (Z.X q) ≫ ((C.obj (Z.X q)).extendXIso ComplexShape.embeddingUpNat
    (i := 0) (i' := (0 : ℤ)) rfl).inv ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-! ### The hypotheses of Stacks 0133 -/

variable (hε : ∀ X, ε.app X ≫ (C.obj X).d 0 1 = 0) (hmono : ∀ X, Mono (ε.app X))
  (hex : ∀ X, (ShortComplex.mk (ε.app X) ((C.obj X).d 0 1) (hε X)).Exact)
  (hinj : ∀ X, Injective X → ∀ k : ℕ, 0 < k → (C.obj X).ExactAt k)

include hε hmono hex hinj in
/-- **The hypotheses of Stacks 0133** for the double complex `C(Z^•)` of a bounded below complex
of injectives `Z^•`, with the augmentation `T(Z^•) ⟶ C(Z^•)^0`. -/
theorem hypotheses_natExtend (Z : CochainComplex A ℤ) (n : ℤ) (hZ : Z.IsStrictlyGE n)
    (hZinj : ∀ q, Injective (Z.X q)) :
    Hypotheses ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
      (((natExtend C).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
      ((natExtendAugmentation C T ε).app Z) where
  diagonalFinite m := by
    refine Set.Finite.subset (Set.finite_Icc n m) fun q hq => ?_
    refine Set.mem_Icc.2 ⟨?_, ?_⟩
    · by_contra h
      exact hq ((HomologicalComplex.eval _ _ (m - q)).map_isZero
        ((natExtend C).map_isZero (CochainComplex.isZero_of_isStrictlyGE Z n q (by omega))))
    · by_contra h
      exact hq (isZero_natExtend_obj_X C (Z.X q) (m - q) (by omega))
  zero_of_neg q p hp := isZero_natExtend_obj_X C (Z.X q) p hp
  exactAt_of_ne_zero q p hp := by
    rcases lt_trichotomy p 0 with h | h | h
    · exact HomologicalComplex.extend_exactAt _ ComplexShape.embeddingUpNat p
        fun j => by change ((j : ℕ) : ℤ) ≠ p; omega
    · exact absurd h hp
    · have hk : ComplexShape.embeddingUpNat.f p.toNat = p := by
        change ((p.toNat : ℕ) : ℤ) = p; omega
      exact (HomologicalComplex.extend_exactAt_iff _ ComplexShape.embeddingUpNat hk).2
        (hinj (Z.X q) (hZinj q) p.toNat (by omega))
  inducesIsoKernel q :=
    CategoryTheory.inducesIsoKernel_extendAugmentation (C.obj (Z.X q)) (ε.app (Z.X q))
      (hε (Z.X q)) (hmono (Z.X q)) (hex (Z.X q)) rfl rfl _
      (natExtendAugmentation_app_f C T ε Z q)

/-! ### The spectral sequence on `D⁺(A)` -/

variable [∀ L : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    L.HasTotal (ComplexShape.up ℤ)]
  [EnoughInjectives A] [HasDerivedCategory A]

/-- **The first page vanishes in the negative columns.** -/
theorem isZero_natExtend_page_one (K : DerivedCategory.Plus A) (p q : ℤ) (hp : p < 0) :
    IsZero ((((derivedFunctor (natExtend C)).obj K).page 1 le_rfl).X (p, q)) :=
  isZero_derivedFunctor_page_one (natExtend C) p q
    (fun X => isZero_natExtend_obj_X C X p hp) K

variable [HasDerivedCategory B]

variable {A' : Type*} [Category* A'] [Abelian A'] [EnoughInjectives A'] [HasDerivedCategory A']
  (R : A ⥤ A') [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (P : A' ⥤ B) [P.Additive]

-- `CategoryTheory.Functor.rightAcyclic` mentions `HasRightDerivedFunctor`; the instance coming
-- from `EnoughInjectives` is given precedence, as in `derivedPageOneIsoOfRightAcyclic`.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **`E_1^{p,q} ≅ H^q(RP(R K))`, naturally in `K` in `D⁺(A)`**, for `p ≥ 0` and
`C(-)^p ≅ R ⋙ P` with `R` exact and carrying injective objects to objects right acyclic for
`P`. -/
def natExtendPageOneIsoOfRightAcyclic (p : ℕ) (q : ℤ)
    (e : C ⋙ HomologicalComplex.eval B (ComplexShape.up ℕ) p ≅ R ⋙ P)
    (hR : ∀ X : A, Injective X → P.rightAcyclic (R.obj X)) :
    derivedFunctor (natExtend C) ⋙ CategoryTheory.SpectralSequence.pageFunctor B _ 1 1 le_rfl ⋙
        HomologicalComplex.eval B _ ((p : ℤ), q) ≅
      R.mapDerivedCategoryPlus ⋙ P.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor B q :=
  derivedPageOneIsoOfRightAcyclic (natExtend C) (p : ℤ) q R P (natExtendCompEvalIso C p ≪≫ e) hR

include hε hmono hex hinj in
/-- **The spectral sequence of `K` in `D⁺(A)` abuts to `H^n(RT(K))`.** -/
theorem abutsTo_natExtend (K : DerivedCategory.Plus A) :
    CategoryTheory.SpectralSequence.AbutsTo ((derivedFunctor (natExtend C)).obj K)
      (fun n => (DerivedCategory.Plus.homologyFunctor B n).obj
        (T.rightDerivedFunctorPlus.obj K)) :=
  abutsTo_derivedFunctor (natExtend C) T (natExtendAugmentation C T ε)
    (fun Z n hZ hZinj => hypotheses_natExtend C T ε hε hmono hex hinj Z n hZ hZinj) K

end Stacks.DegreewiseSpectralSequence

end
