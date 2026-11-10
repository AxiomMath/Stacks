module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Homology.HomBicomplexExt
public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentKInjective
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolution
public import StacksFrontier.Algebra.Homology.AbelianGroupComplexResolutions
public import StacksFrontier.Homology.Ext.DerivedCoyoneda
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.ProductTotalComplex

/-!
# Vanishing of cohomology on a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE), with total site `C_total` and component
sites `C_p`, and let `K` be an object of the unbounded derived category `D(C_total)` of abelian
sheaves on the total site. Write `K_p` for the restriction of `K` to `C_p`. If the diagonal
cohomology `H^{-p}(C_p, K_p)` vanishes for every `p ≥ 0`, then `H^0(C_total, K)` vanishes; and if
`RΓ(C_p, K_p)` vanishes for every `p ≥ 0`, then `RΓ(C_total, K)` vanishes.

Represent `K` by a K-injective complex `I` with injective terms.
The integral resolution `… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ` of the constant integer sheaf on the
total site (Stacks 09WI) is a resolution, so for a K-injective target the Hom complex out of the
constant integer sheaf is quasi-isomorphic to the Hom complex out of that resolution. Placing the
resolution in non-positive degrees, its Hom complex into `I` is the *product* total complex of the
double complex `A^{p,q} = Hom(g_{p!} ℤ, I^q) = Γ(C_p, I^q_p)`, with the two differential
conventions differing by a quadratic sign. The `p`-th column of that double complex computes
`H^•(C_p, K_p)` by adjunction and by the fact that restriction to a component preserves
K-injectivity (Stacks 09WH); so the vanishing hypothesis says that the `p`-th column is exact in
degree `-p`, and Stacks 0H0Q gives `H^0` of the product total complex. Part (2) is part (1)
applied to every shift of `K`.

## Main definitions

* `CochainComplex.coyonedaComplex`: the complex `Hom(X, I^•)` of morphisms from an object into a
  cochain complex.
* `CochainComplex.homProductDoubleComplex`: the double complex `Hom(P_p, I^q)` of a chain complex
  `P` indexed by `ℕ` and a cochain complex `I`.
* `HomologicalComplex₂.toCplxCplx`: a double complex of abelian groups whose first index runs
  over `ℕ`, read as a complex of complexes in the vocabulary of Stacks 0H0Q.
* `CategoryTheory.SimplicialSiteSituation.componentRestrictionDerived`: restriction to the
  component in simplicial degree `n` on unbounded derived categories, induced by the restriction
  `CategoryTheory.SimplicialSiteSituation.restrictAb` of abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.integerChainAugmentation` and
  `.integerCochainAugmentation`: the augmentation of the integral resolution of Stacks 09WI to
  the constant integer sheaf placed in degree zero, as a chain and as a cochain map.
* `CategoryTheory.SimplicialSiteSituation.totalKInjectiveModel`: a K-injective complex with
  injective terms representing a given object of `D(C_total)`.

## Main results

* `CochainComplex.homProductTotalIso`: the Hom complex out of a chain complex placed in
  non-positive degrees is the product total complex of the double complex `Hom(P_p, I^q)`.
* `HomologicalComplex₂.productTotal_exactAt_zero`: Stacks 0H0Q for the product total complex of a
  double complex, namely `H^0(Tot_π) = 0` when the `p`-th column is exact in degree `-p` for all
  `p ≥ 0`.
* `CochainComplex.exactAt_coyonedaComplex`: `Hom(X, I^•)` is exact in degree `n` when the group of
  morphisms `X ⟶ I[n]` in the derived category vanishes, for `I` K-injective.
* `CategoryTheory.SimplicialSiteSituation.integerResolutionColumnIso`: the `p`-th column of the
  double complex of the integral resolution is `Hom(ℤ, I^•|_{C_p})`.
* `CategoryTheory.SimplicialSiteSituation.subsingleton_hom_totalIntegerSheaf`: **Stacks 0H0W**
  part (1).
* `CategoryTheory.SimplicialSiteSituation.subsingleton_hom_totalIntegerSheaf_shift`:
  **Stacks 0H0W** part (2).

## Implementation notes

Cohomology is written in its derived-Hom form throughout: `H^i(C, K)` is the group of morphisms
from the constant integer sheaf of `C`, placed in degree `0`, to `K[i]` in the unbounded derived
category, and "vanishes" is `Subsingleton` of that group. Vanishing of `RΓ` is the vanishing of
all of these groups at once.

The comparison of the Hom complex with the product total complex is twisted by the sign
`CochainComplex.HomBicomplex.sign`, which is quadratic in the bidegree: the differential of the
Hom complex is `d_I ∘ z + (-1)^{n+1} z ∘ d_P`, while the differential of the product total
complex is `d_1 + (-1)^p d_2`.

## References

* [Stacks Project, Tag 0H0W](https://stacks.math.columbia.edu/tag/0H0W)
* [Stacks Project, Tag 0H0V](https://stacks.math.columbia.edu/tag/0H0V)
* [Stacks Project, Tag 0H0Q](https://stacks.math.columbia.edu/tag/0H0Q)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

/-! ### The differential of a product total complex -/

namespace HomologicalComplex₂

/-- The component in `K^{0, q}` of the differential of the product total complex, for any
degree `q'` with `q' + 1 = q`. -/
lemma productTotal_d_apply_zero
    (K : HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℕ) (ComplexShape.up ℤ))
    (n m q q' : ℤ) (hnm : n + 1 = m) (hq : q' + 1 = q)
    (h : ((0 : ℕ) : ℤ) + q = m) (h' : ((0 : ℕ) : ℤ) + q' = n)
    (x : K.productTotalX n) :
    K.productTotal.d n m x ⟨(0, q), h⟩ = (K.X 0).d q' q (x ⟨(0, q'), h'⟩) := by
  subst m
  rw [HomologicalComplex₂.productTotal_d]
  exact K.productTotalD_apply_zero_left n x q q' hq h h'

/-- The component in `K^{p + 1, q}` of the differential of the product total complex, for any
degree `q'` with `q' + 1 = q`. -/
lemma productTotal_d_apply_succ
    (K : HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℕ) (ComplexShape.up ℤ))
    (n m : ℤ) (p : ℕ) (q q' : ℤ) (hnm : n + 1 = m) (hq : q' + 1 = q)
    (h : ((p + 1 : ℕ) : ℤ) + q = m) (h' : ((p + 1 : ℕ) : ℤ) + q' = n)
    (x : K.productTotalX n) :
    K.productTotal.d n m x ⟨(p + 1, q), h⟩ =
      (K.d p (p + 1)).f q (x ⟨(p, q), by push_cast at h h' ⊢; omega⟩) +
        (-1 : ℤ) ^ (p + 1) • (K.X (p + 1)).d q' q (x ⟨(p + 1, q'), h'⟩) := by
  subst m
  rw [HomologicalComplex₂.productTotal_d]
  exact K.productTotalD_apply_succ n x p q q' hq h h'

end HomologicalComplex₂

/-! ### The Hom complex out of a chain complex -/

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The complex `Hom(X, I^•)` of morphisms from an object into a cochain complex. -/
abbrev coyonedaComplex (X : C) (I : CochainComplex C ℤ) : CochainComplex AddCommGrpCat.{v} ℤ :=
  ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I

/-- **An adjunction identifies `Hom(F X, I^•)` with `Hom(X, G I^•)`**, degreewise by the
adjunction bijections of `F ⊣ G`. -/
def coyonedaComplexAdjIso {A B : Type u} [Category.{v} A] [Abelian A] [Category.{v} B]
    [Abelian B] {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) [F.Additive] [G.Additive] (X : A)
    (I : CochainComplex B ℤ) :
    coyonedaComplex (F.obj X) I ≅
      coyonedaComplex X ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => AddEquiv.toAddCommGrpIso (adj.homAddEquiv _ (I.X q)))
    (by
      intro i j _
      ext x
      exact (adj.homEquiv_naturality_right x (I.d i j)).symm)

/-- **The double complex `Hom(P_p, I^q)`** attached to a chain complex `P` indexed by `ℕ` and a
cochain complex `I`: its `p`-th column is the complex `Hom(P_p, I^•)`, and its horizontal
differential is precomposition with the differential `P_{p + 1} → P_p`. -/
def homProductDoubleComplex (P : ChainComplex C ℕ) (I : CochainComplex C ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  CochainComplex.of
    (fun p => coyonedaComplex (P.X p) I)
    (fun p => (NatTrans.mapHomologicalComplex
      (preadditiveCoyoneda.map (P.d (p + 1) p).op) (ComplexShape.up ℤ)).app I)
    (fun p => by
      ext q (f : P.X p ⟶ I.X q)
      change P.d (p + 1 + 1) (p + 1) ≫ P.d (p + 1) p ≫ f = 0
      rw [← Category.assoc, P.d_comp_d, Limits.zero_comp])

/-- The horizontal differential of `homProductDoubleComplex` is precomposition with the
differential of `P`. -/
lemma homProductDoubleComplex_d (P : ChainComplex C ℕ) (I : CochainComplex C ℤ) (p : ℕ) :
    (homProductDoubleComplex P I).d p (p + 1) =
      (NatTrans.mapHomologicalComplex
        (preadditiveCoyoneda.map (P.d (p + 1) p).op) (ComplexShape.up ℤ)).app I := by
  dsimp only [homProductDoubleComplex]
  exact CochainComplex.of_d _ _ _

/-- On elements, the horizontal differential of `homProductDoubleComplex` is precomposition. -/
lemma homProductDoubleComplex_d_f_apply (P : ChainComplex C ℕ) (I : CochainComplex C ℤ)
    (p : ℕ) (q : ℤ) (f : P.X p ⟶ I.X q) :
    ((homProductDoubleComplex P I).d p (p + 1)).f q f = P.d (p + 1) p ≫ f := by
  rw [homProductDoubleComplex_d]
  rfl

/-- On elements, the vertical differential of `homProductDoubleComplex` is postcomposition. -/
lemma homProductDoubleComplex_X_d_apply (P : ChainComplex C ℕ) (I : CochainComplex C ℤ)
    (p : ℕ) (q q' : ℤ) (f : P.X p ⟶ I.X q) :
    ((homProductDoubleComplex P I).X p).d q q' f = f ≫ I.d q q' :=
  rfl

/-- The `p`-th column of the double complex `Hom(P_p, I^q)` is the complex
`Hom(P_p, I^•)`. -/
lemma homProductDoubleComplex_X (P : ChainComplex C ℕ) (I : CochainComplex C ℤ) (p : ℕ) :
    (homProductDoubleComplex P I).X p = coyonedaComplex (P.X p) I :=
  rfl

/-- **The cohomology of `Hom(X, I^•)` for a K-injective complex `I`** is the group of morphisms
`X ⟶ I[n]` in the derived category. -/
def coyonedaComplexHomologyEquiv [HasDerivedCategory.{w} C] (X : C) (I : CochainComplex C ℤ)
    [I.IsKInjective] (n : ℤ) :
    (coyonedaComplex X I).homology n ≃+
      ((DerivedCategory.singleFunctor C 0).obj X ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :=
  (HomologicalComplex.homologyMapIso
        (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda X I)
        n).symm.addCommGroupIsoToAddEquiv.trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ I n).trans
      ((StacksDraft.DerivedCoyoneda.cohomologyClassAddEquivDerivedHom _ I n).trans
        (Linear.homCongr ℤ ((DerivedCategory.singleFunctorIsoCompQ C 0).app X).symm
          (Iso.refl _)).toAddEquiv))

/-- **`Hom(X, I^•)` is exact in degree `n`** as soon as `X ⟶ I[n]` vanishes in the derived
category, for `I` a K-injective complex. -/
lemma exactAt_coyonedaComplex [HasDerivedCategory.{w} C] (X : C) (I : CochainComplex C ℤ)
    [I.IsKInjective] (n : ℤ)
    (h : Subsingleton
      ((DerivedCategory.singleFunctor C 0).obj X ⟶ (DerivedCategory.Q.obj I)⟦n⟧)) :
    (coyonedaComplex X I).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, AddCommGrpCat.isZero_iff_subsingleton]
  exact (coyonedaComplexHomologyEquiv X I n).toEquiv.subsingleton

/-- `Hom(X, I^•)` is the Hom complex out of `X` placed in degree zero; so if the latter is exact
in degree `n`, so is the former. -/
lemma exactAt_coyonedaComplex_of_homComplex (X : C) (I : CochainComplex C ℤ) (n : ℤ)
    (h : (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X) I).ExactAt n) :
    (coyonedaComplex X I).ExactAt n :=
  h.of_iso (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda X I)

/-! ### The Hom complex out of a chain complex is a product total complex -/

open CochainComplex.HomComplex

/-- Evaluation of a degree-`n` cochain out of a chain complex `P` extended into non-positive
degrees: such a cochain is determined by its components `P_p ⟶ I^q` with `p + q = n`. -/
def extendCochainEval (P : ChainComplex C ℕ) (I : CochainComplex C ℤ) (n : ℤ) :
    Cochain (P.extend ComplexShape.embeddingDownNat) I n →+
      (∀ i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}, P.X i.1.1 ⟶ I.X i.1.2) where
  toFun z i := (P.extendXIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f i.1.1 = -(i.1.1 : ℤ) from rfl)).inv ≫
      z.v (-(i.1.1 : ℤ)) i.1.2 (by have := i.2; omega)
  map_zero' := by ext i; simp
  map_add' z z' := by ext i; simp [Cochain.add_v, Preadditive.comp_add]

/-- Cancelling the two identifications of the degree-`p` term of an extended chain complex. -/
lemma extendXIso_inv_hom_apply (P : ChainComplex C ℕ) (I : CochainComplex C ℤ) (n : ℤ)
    (x : ∀ i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}, P.X i.1.1 ⟶ I.X i.1.2)
    (p p' : ℕ) (q : ℤ) (h : p' = p)
    (hpq : (p : ℤ) + q = n) (hpq' : (p' : ℤ) + q = n)
    (hf : ComplexShape.embeddingDownNat.f p' = -(p : ℤ)) :
    (P.extendXIso ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl).inv ≫
      (P.extendXIso ComplexShape.embeddingDownNat hf).hom ≫
        x ⟨(p', q), hpq'⟩ = x ⟨(p, q), hpq⟩ := by
  subst p'
  simp

/-- A degree-`n` cochain out of an extended chain complex is exactly a family of maps
`P_p ⟶ I^q` with `p + q = n`. -/
lemma extendCochainEval_bijective (P : ChainComplex C ℕ) (I : CochainComplex C ℤ)
    (n : ℤ) : Function.Bijective (extendCochainEval P I n) := by
  constructor
  · intro z z' h
    ext r q hrq
    by_cases hr : r ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, r = -(p : ℤ) := ⟨(-r).toNat, by omega⟩
      have hh := congrFun h ⟨(p, q), by omega⟩
      change (P.extendXIso ComplexShape.embeddingDownNat rfl).inv ≫ z.v _ _ hrq =
        (P.extendXIso ComplexShape.embeddingDownNat rfl).inv ≫ z'.v _ _ hrq at hh
      exact (cancel_epi (P.extendXIso ComplexShape.embeddingDownNat
        (i := p) (i' := -(p : ℤ)) rfl).inv).mp hh
    · exact (P.isZero_extend_X ComplexShape.embeddingDownNat r
        (by intro p; change -(p : ℤ) ≠ r; omega)).eq_of_src _ _
  · intro x
    let z : Cochain (P.extend ComplexShape.embeddingDownNat) I n :=
      Cochain.mk fun r q hrq => if hr : r ≤ 0 then
        (P.extendXIso ComplexShape.embeddingDownNat
          (show ComplexShape.embeddingDownNat.f (-r).toNat = r by
            change -((-r).toNat : ℤ) = r; omega)).hom ≫
          x ⟨((-r).toNat, q), by dsimp; omega⟩
      else 0
    refine ⟨z, ?_⟩
    ext ⟨⟨p, q⟩, hpq⟩
    change (P.extendXIso ComplexShape.embeddingDownNat rfl).inv ≫
      z.v (-(p : ℤ)) q (by omega) = x ⟨(p, q), hpq⟩
    dsimp only [z, Cochain.mk_v]
    simp only [neg_nonpos, Nat.cast_nonneg, dite_true]
    exact extendXIso_inv_hom_apply P I n x p _ q (by simp) hpq _ _

/-- Degree-`n` cochains out of an extended chain complex, as the product of the groups of their
components. -/
def extendCochainEquiv (P : ChainComplex C ℕ) (I : CochainComplex C ℤ) (n : ℤ) :
    Cochain (P.extend ComplexShape.embeddingDownNat) I n ≃+
      (∀ i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}, P.X i.1.1 ⟶ I.X i.1.2) :=
  AddEquiv.ofBijective (extendCochainEval P I n) (extendCochainEval_bijective P I n)

/-- The component of `δ z` in column `0`: only the vertical term contributes, the differential
of `P` out of degree `0` being zero. -/
lemma extendCochainEval_δ_zero (P : ChainComplex C ℕ) (I : CochainComplex C ℤ)
    (n m q : ℤ) (hnm : n + 1 = m) (hq : ((0 : ℕ) : ℤ) + q = m)
    (z : Cochain (P.extend ComplexShape.embeddingDownNat) I n) :
    extendCochainEval P I m (δ n m z) ⟨(0, q), hq⟩ =
      extendCochainEval P I n z ⟨(0, q - 1), by dsimp; omega⟩ ≫ I.d (q - 1) q := by
  change (P.extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl).inv ≫
    (δ n m z).v 0 q (by dsimp at hq; omega) = _
  rw [δ_v n m hnm z 0 q (by dsimp at hq; omega) (q - 1) 1 rfl (by simp),
    P.extend_d_from_eq_zero ComplexShape.embeddingDownNat 0 1 0 rfl (by simp)]
  simp [extendCochainEval, Category.assoc]

/-- The component of `δ z` in column `p + 1`: the vertical term plus the horizontal term coming
from the differential of `P`. -/
lemma extendCochainEval_δ_succ (P : ChainComplex C ℕ) (I : CochainComplex C ℤ)
    (n m : ℤ) (p : ℕ) (q : ℤ) (hnm : n + 1 = m) (hq : ((p + 1 : ℕ) : ℤ) + q = m)
    (z : Cochain (P.extend ComplexShape.embeddingDownNat) I n) :
    extendCochainEval P I m (δ n m z) ⟨(p + 1, q), hq⟩ =
      extendCochainEval P I n z ⟨(p + 1, q - 1), by dsimp; omega⟩ ≫ I.d (q - 1) q +
      m.negOnePow • (P.d (p + 1) p ≫
        extendCochainEval P I n z ⟨(p, q), by dsimp; omega⟩) := by
  change (P.extendXIso ComplexShape.embeddingDownNat
    (i := p + 1) (i' := -((p + 1 : ℕ) : ℤ)) rfl).inv ≫
    (δ n m z).v (-((p + 1 : ℕ) : ℤ)) q (by dsimp at hq; omega) = _
  rw [δ_v n m hnm z _ q (by dsimp at hq; omega) (q - 1) (-(p : ℤ)) rfl (by push_cast; omega),
    P.extend_d_eq ComplexShape.embeddingDownNat (i := p + 1) (j := p)
      (i' := -((p + 1 : ℕ) : ℤ)) (j' := -(p : ℤ)) rfl rfl]
  simp [extendCochainEval, Preadditive.comp_add, Linear.comp_units_smul, Category.assoc]

/-- The sign-twisted component of `δ z` in column `0`. -/
lemma signedEval_δ_zero (P : ChainComplex C ℕ) (I : CochainComplex C ℤ)
    (n m q : ℤ) (hnm : n + 1 = m) (hq : ((0 : ℕ) : ℤ) + q = m)
    (hq' : ((0 : ℕ) : ℤ) + (q - 1) = n)
    (z : Cochain (P.extend ComplexShape.embeddingDownNat) I n) :
    HomBicomplex.sign ((0 : ℕ) : ℤ) q • extendCochainEval P I m (δ n m z) ⟨(0, q), hq⟩ =
      (HomBicomplex.sign ((0 : ℕ) : ℤ) (q - 1) •
        extendCochainEval P I n z ⟨(0, q - 1), hq'⟩) ≫ I.d (q - 1) q := by
  rw [extendCochainEval_δ_zero P I n m q hnm hq]
  simp [HomBicomplex.sign, HomBicomplex.triangularSign]

/-- The sign-twisted component of `δ z` in column `p + 1`, in the shape of the differential of
the product total complex. -/
lemma signedEval_δ_succ (P : ChainComplex C ℕ) (I : CochainComplex C ℤ)
    (n m : ℤ) (p : ℕ) (q : ℤ) (hnm : n + 1 = m) (hq : ((p + 1 : ℕ) : ℤ) + q = m)
    (hq₁ : (p : ℤ) + q = n) (hq₂ : ((p + 1 : ℕ) : ℤ) + (q - 1) = n)
    (z : Cochain (P.extend ComplexShape.embeddingDownNat) I n) :
    HomBicomplex.sign ((p + 1 : ℕ) : ℤ) q •
        extendCochainEval P I m (δ n m z) ⟨(p + 1, q), hq⟩ =
      P.d (p + 1) p ≫ (HomBicomplex.sign (p : ℤ) q •
          extendCochainEval P I n z ⟨(p, q), hq₁⟩) +
        (-1 : ℤ) ^ (p + 1) • ((HomBicomplex.sign ((p + 1 : ℕ) : ℤ) (q - 1) •
          extendCochainEval P I n z ⟨(p + 1, q - 1), hq₂⟩) ≫ I.d (q - 1) q) := by
  rw [extendCochainEval_δ_succ P I n m p q hnm hq, ← Int.coe_negOnePow_natCast]
  have hs₁ : HomBicomplex.sign ((p + 1 : ℕ) : ℤ) q * m.negOnePow =
      HomBicomplex.sign (p : ℤ) q := by
    have hm : m = (p : ℤ) + q + 1 := by push_cast at hq; omega
    rw [Nat.cast_add, Nat.cast_one, HomBicomplex.sign_succ_left, hm, mul_right_comm,
      Int.units_mul_self, one_mul]
  have hs₂ : HomBicomplex.sign ((p + 1 : ℕ) : ℤ) q =
      (((p + 1 : ℕ) : ℤ)).negOnePow * HomBicomplex.sign ((p + 1 : ℕ) : ℤ) (q - 1) := by
    simpa using HomBicomplex.sign_succ_right ((p + 1 : ℕ) : ℤ) (q - 1)
  simp only [← Units.smul_def]
  simp only [smul_add, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  rw [hs₁, ← hs₂]
  exact add_comm _ _

/-- Multiplication by a unit of `ℤ`, as an automorphism of an abelian group. -/
def unitsZSmulAddEquiv {G : Type*} [AddCommGroup G] (s : ℤˣ) : G ≃+ G where
  toFun g := s • g
  invFun g := s⁻¹ • g
  left_inv g := inv_smul_smul s g
  right_inv g := smul_inv_smul s g
  map_add' _ _ := smul_add _ _ _

/-- **The degree-`n` term of the Hom complex out of an extended chain complex is the degree-`n`
term of the product total complex of the double complex `Hom(P_p, I^q)`**, the component in
column `p` and row `q` being twisted by the sign `CochainComplex.HomBicomplex.sign p q`. -/
def homProductTotalEquiv (P : ChainComplex C ℕ) (I : CochainComplex C ℤ) (n : ℤ) :
    Cochain (P.extend ComplexShape.embeddingDownNat) I n ≃+
      (homProductDoubleComplex P I).productTotalX n :=
  (extendCochainEquiv P I n).trans
    (AddEquiv.piCongrRight fun i =>
      unitsZSmulAddEquiv (G := P.X i.1.1 ⟶ I.X i.1.2) (HomBicomplex.sign i.1.1 i.1.2))

/-- The comparison of the Hom complex with the product total complex commutes with the
differentials. -/
lemma homProductTotalEquiv_d (P : ChainComplex C ℕ) (I : CochainComplex C ℤ)
    (n m : ℤ) (hnm : n + 1 = m)
    (z : Cochain (P.extend ComplexShape.embeddingDownNat) I n) :
    homProductTotalEquiv P I m (δ n m z) =
      (homProductDoubleComplex P I).productTotal.d n m (homProductTotalEquiv P I n z) := by
  apply funext
  rintro ⟨⟨p, q⟩, hpq⟩
  cases p with
  | zero =>
    rw [HomologicalComplex₂.productTotal_d_apply_zero (homProductDoubleComplex P I) n m q
      (q - 1) hnm (by omega) hpq (by dsimp at hpq ⊢; omega)]
    exact signedEval_δ_zero P I n m q hnm hpq (by dsimp at hpq ⊢; omega) z
  | succ p =>
    rw [HomologicalComplex₂.productTotal_d_apply_succ (homProductDoubleComplex P I) n m p q
      (q - 1) hnm (by omega) hpq (by dsimp at hpq ⊢; omega), homProductDoubleComplex_d]
    exact signedEval_δ_succ P I n m p q hnm hpq
      (by dsimp at hpq ⊢; omega)
      (by dsimp at hpq ⊢; omega) z

/-- **The Hom complex out of a chain complex `P` placed in non-positive degrees is the product
total complex of the double complex `Hom(P_p, I^q)`.** -/
def homProductTotalIso (P : ChainComplex C ℕ) (I : CochainComplex C ℤ) :
    CochainComplex.HomComplex (P.extend ComplexShape.embeddingDownNat) I ≅
      (homProductDoubleComplex P I).productTotal :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homProductTotalEquiv P I n).toAddCommGrpIso)
    fun n m h => by
      ext z
      exact (homProductTotalEquiv_d P I n m h z).symm

end CochainComplex

/-! ### Vanishing of `H^0` of a product total complex -/

namespace HomologicalComplex₂

variable (D : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ))

/-- A double complex of abelian groups whose first index runs over `ℕ`, read as a complex of
complexes in the vocabulary of Stacks 0H0Q. -/
def toCplxCplx : CplxCplx.{u} where
  A p q := (D.X p).X q
  instAb p q := inferInstance
  d p q := ((D.X p).d q (q + 1)).hom
  f p q := ((D.d p (p + 1)).f q).hom
  d_d p q x := by
    rw [← ConcreteCategory.comp_apply, (D.X p).d_comp_d]
    rfl
  f_f p q x := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, D.d_comp_d]
    rfl
  f_d p q x := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (D.d p (p + 1)).comm]

/-- The product total complex of `toCplxCplx`, assembled from the product total group and the
total differential of Stacks 0H0Q. -/
def cplxTotalComplex : CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.of (fun n => AddCommGrpCat.of ((toCplxCplx D).Tot n))
    (fun n => AddCommGrpCat.ofHom ((toCplxCplx D).totalD n))
    (fun n => by ext x; exact (toCplxCplx D).totalD_totalD_eq_zero x)

/-- The differential of `cplxTotalComplex` is the total differential of Stacks 0H0Q. -/
lemma cplxTotalComplex_d (n : ℤ) :
    (cplxTotalComplex D).d n (n + 1) = AddCommGrpCat.ofHom ((toCplxCplx D).totalD n) := by
  dsimp only [cplxTotalComplex]
  exact CochainComplex.of_d _ _ _

/-- The vertical differential of `D` in the vocabulary of Stacks 0H0Q, with its target degree
transported along an equality. -/
lemma vertical_transport (p : ℕ) {q r : ℤ} (h : q + 1 = r) (x : (D.X p).X q) :
    (D.X p).d q r x =
      (CplxCplx.cast (toCplxCplx D) p h) ((D.X p).d q (q + 1) x) := by
  cases h
  rfl

/-- The degree-`n` term of the product total complex of Stacks 0H0Q is the degree-`n` term of
`Tot_π(D)`: the index `q` of a factor is determined by its index `p`. -/
def cplxTotalEquiv (n : ℤ) : (toCplxCplx D).Tot n ≃+ D.productTotalX n where
  toFun x i := CplxCplx.cast (toCplxCplx D) i.1.1 (by omega) (x i.1.1)
  invFun y p := y ⟨(p, n - p), by push_cast; ring⟩
  left_inv := by
    intro x
    funext p
    change CplxCplx.cast (toCplxCplx D) p (by omega) (x p) = x p
    have hp : (by omega : n - (p : ℤ) = n - (p : ℤ)) = rfl := Subsingleton.elim _ _
    rw [hp]
    rfl
  right_inv := by
    intro y
    funext i
    obtain ⟨⟨p, q⟩, h⟩ := i
    obtain rfl : q = n - p := by omega
    change CplxCplx.cast (toCplxCplx D) p (by omega)
        (y ⟨(p, n - p), by push_cast; ring⟩) = y ⟨(p, n - p), by push_cast; ring⟩
    have hp : (by omega : n - (p : ℤ) = n - (p : ℤ)) = rfl := Subsingleton.elim _ _
    rw [hp]
    rfl
  map_add' := by
    intro x y
    funext i
    exact (CplxCplx.cast (toCplxCplx D) i.1.1 (by omega)).map_add _ _

/-- The components of `cplxTotalEquiv`. -/
lemma cplxTotalEquiv_apply (n : ℤ) (x : (toCplxCplx D).Tot n) (p : ℕ) (q : ℤ)
    (h : (p : ℤ) + q = n) :
    cplxTotalEquiv D n x ⟨(p, q), h⟩ =
      CplxCplx.cast (toCplxCplx D) p (show n - (p : ℤ) = q by omega) (x p) := rfl

/-- **The product total complex of Stacks 0H0Q is `Tot_π(D)`.** -/
def cplxTotalComplexIso : cplxTotalComplex D ≅ D.productTotal := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (cplxTotalEquiv D n).toAddCommGrpIso) ?_
  intro n n' hnn'
  obtain rfl : n + 1 = n' := hnn'
  rw [cplxTotalComplex_d]
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => funext ?_)
  change (toCplxCplx D).Tot n at x
  rintro ⟨⟨p, q⟩, h⟩
  obtain rfl : q = n - (p : ℤ) + 1 := by omega
  change D.productTotal.d n (n + 1) (cplxTotalEquiv D n x) ⟨(p, n - (p : ℤ) + 1), h⟩ =
    cplxTotalEquiv D (n + 1) ((toCplxCplx D).totalD n x) ⟨(p, n - (p : ℤ) + 1), h⟩
  rw [cplxTotalEquiv_apply]
  cases p with
  | zero =>
    rw [productTotal_d_apply_zero D n (n + 1) (n - ((0 : ℕ) : ℤ) + 1) (n - ((0 : ℕ) : ℤ))
      rfl rfl h (by push_cast; ring),
      cplxTotalEquiv_apply, CplxCplx.totalD_apply_zero, CplxCplx.dPartHom_apply,
      CplxCplx.cast_cast, pow_zero, one_smul]
    rfl
  | succ p =>
    rw [productTotal_d_apply_succ D n (n + 1) p (n - ((p + 1 : ℕ) : ℤ) + 1)
      (n - ((p + 1 : ℕ) : ℤ)) rfl rfl h (by push_cast; ring),
      cplxTotalEquiv_apply, cplxTotalEquiv_apply, CplxCplx.totalD_apply_succ,
      CplxCplx.dPartHom_apply, CplxCplx.fPartHom_apply, map_add, CplxCplx.cast_cast,
      CplxCplx.cast_cast, ← CplxCplx.f_cast]
    exact add_comm _ _

/-- **The total differential of Stacks 0H0Q is the differential of `Tot_π(D)`**, read through
`cplxTotalEquiv`. -/
lemma cplxTotalEquiv_totalD (n : ℤ) (x : (toCplxCplx D).Tot n) :
    D.productTotal.d n (n + 1) (cplxTotalEquiv D n x) =
      cplxTotalEquiv D (n + 1) ((toCplxCplx D).totalD n x) := by
  have h := ConcreteCategory.congr_hom ((cplxTotalComplexIso D).hom.comm n (n + 1)) x
  rwa [cplxTotalComplex_d] at h

/-- Exactness of the `p`-th column of `D` in degree `-p` is the vanishing hypothesis of
Stacks 0H0Q for `toCplxCplx D`. -/
lemma internalCohomologyVanishes_of_exactAt (p : ℕ) (hD : (D.X p).ExactAt (-(p : ℤ))) :
    (toCplxCplx D).InternalCohomologyVanishes p := by
  intro z hz
  have hex := (HomologicalComplex.exactAt_iff' (D.X p) (-(p : ℤ) - 1) (-(p : ℤ)) (-(p : ℤ) + 1)
    (by simp) (by simp)).mp hD
  obtain ⟨w, hw⟩ := (ShortComplex.ab_exact_iff _).mp hex z hz
  exact ⟨w, (vertical_transport D p (show -(p : ℤ) - 1 + 1 = -(p : ℤ) by ring) w).symm.trans hw⟩

/-- **`H^0(Tot_π(D)) = 0`** as soon as the `p`-th column of `D` is exact in degree `-p` for every
`p ≥ 0`. This is `CplxCplx.total_H0_eq_zero` (Stacks 0H0Q), transported along
`cplxTotalComplexIso`. -/
lemma productTotal_exactAt_zero (hD : ∀ p : ℕ, (D.X p).ExactAt (-(p : ℤ))) :
    D.productTotal.ExactAt 0 := by
  refine HomologicalComplex.ExactAt.of_iso ?_ (cplxTotalComplexIso D)
  rw [HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  exact (ShortComplex.ab_exact_iff _).mpr fun x hx => (toCplxCplx D).total_H0_eq_zero
    (fun p => internalCohomologyVanishes_of_exactAt D p (hD p)) x hx

end HomologicalComplex₂

/-! ### The integral resolution as a resolution of complexes -/

namespace CategoryTheory.SimplicialSiteSituation

open CochainComplex CochainComplex.HomComplex
open scoped Simplicial

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})

/-- The augmentation of the integral resolution of Stacks 09WI, read as a morphism of chain
complexes into the constant integer sheaf placed in degree zero. -/
def integerChainAugmentation :
    S.simplicialIntegerComplex ⟶
      (ChainComplex.single₀ (Sheaf S.totalTopology Ab.{u})).obj S.totalIntegerSheaf :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(S.simplicialIntegerResolution).augmentation,
      (S.simplicialIntegerResolution).augmentation_comp⟩

/-- **The integral resolution of Stacks 09WI is a resolution**: its augmentation to the constant
integer sheaf in degree zero is a quasi-isomorphism. -/
instance quasiIso_integerChainAugmentation :
    QuasiIso (S.integerChainAugmentation) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · exact ⟨(S.simplicialIntegerResolution).exact_zero,
        (S.simplicialIntegerResolution).augmentation_epi⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact (S.simplicialIntegerResolution).exact_positive (n + 1) (by omega)
    · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The integral resolution of Stacks 09WI, read as a cochain complex supported in non-positive
degrees, together with its augmentation to the constant integer sheaf in degree zero. -/
def integerCochainAugmentation :
    (S.simplicialIntegerComplex).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj S.totalIntegerSheaf :=
  HomologicalComplex.extendMap (S.integerChainAugmentation)
    ComplexShape.embeddingDownNat ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        S.totalIntegerSheaf 0 0 rfl).hom

/-- The cochain form of the augmentation of the integral resolution is a
quasi-isomorphism. -/
instance quasiIso_integerCochainAugmentation :
    QuasiIso (S.integerCochainAugmentation) := by
  dsimp only [integerCochainAugmentation]
  infer_instance

/-! ### Restriction to a simplicial component -/

/-- Lower shriek along a component inclusion is left adjoint to restriction. -/
def componentAdjunctionAb (n : SimplexCategory) :
    componentLowerShriekAb S n ⊣ restrictAb S n :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (S.componentFunctor n) Ab.{u}
    (S.componentTopology n) S.totalTopology

/-- Lower shriek along a component inclusion is additive, being exact by Stacks 09WG (7). -/
instance additive_componentLowerShriekAb (n : SimplexCategory) :
    (componentLowerShriekAb S n).Additive :=
  haveI : PreservesFiniteLimits (componentLowerShriekAb S n) :=
    (componentLowerShriek_exactFunctor S n).1
  Functor.additive_of_preserves_binary_products _

/-- Restriction to the component in simplicial degree `n`, on unbounded derived categories. -/
abbrev componentRestrictionDerived (n : SimplexCategory) :
    DerivedCategory (Sheaf S.totalTopology Ab.{u}) ⥤
      DerivedCategory (Sheaf (S.componentTopology n) Ab.{u}) :=
  (restrictAb S n).mapDerivedCategory

/-- **Adjunction identifies `Hom(g_{n!} ℤ, I^•)` with `Hom(ℤ, I^•|_{C_n})`.** -/
def componentCoyonedaComplexIso (n : SimplexCategory)
    (I : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    CochainComplex.coyonedaComplex (S.componentIntegerSheaf n) I ≅
      CochainComplex.coyonedaComplex (integerSheaf (S.componentTopology n))
        (((restrictAb S n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => AddEquiv.toAddCommGrpIso ((componentAdjunctionAb S n).homAddEquiv _ (I.X q)))
    (by
      intro i j _
      ext x
      exact (componentAdjunctionAb S n).homEquiv_naturality_right x (I.d i j))

/-- **The `p`-th column of the double complex `Hom(P_p, I^q)` of the integral resolution is the
complex of sections `Hom(ℤ, I^•|_{C_p})` on the component in simplicial degree `p`.** -/
def integerResolutionColumnIso (p : ℕ) (I : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    (CochainComplex.homProductDoubleComplex (S.simplicialIntegerComplex) I).X p ≅
      CochainComplex.coyonedaComplex (integerSheaf (S.componentTopology ⦋p⦌))
        (((restrictAb S ⦋p⦌).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  refine ?_ ≪≫ componentCoyonedaComplexIso S ⦋p⦌ I
  exact ((NatIso.mapHomologicalComplex
    (preadditiveCoyoneda.mapIso ((S.simplicialIntegerResolution).degreeIso p).op)
    (ComplexShape.up ℤ)).app I).symm

/-- **The `p`-th column is exact in degree `-p`** as soon as `H^{-p}(C_p, K_p)` vanishes, for `K`
represented by the K-injective complex `I`. -/
lemma exactAt_column (p : ℕ) (I : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)
    [I.IsKInjective]
    (h : Subsingleton
      ((DerivedCategory.singleFunctor (Sheaf (S.componentTopology ⦋p⦌) Ab.{u}) 0).obj
          (integerSheaf (S.componentTopology ⦋p⦌)) ⟶
        (DerivedCategory.Q.obj (((restrictAb S ⦋p⦌).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))⟦-(p : ℤ)⟧)) :
    ((CochainComplex.homProductDoubleComplex
      (S.simplicialIntegerComplex) I).X p).ExactAt (-(p : ℤ)) := by
  have := isKInjective_componentRestriction S ⦋p⦌ I
  exact (CochainComplex.exactAt_coyonedaComplex _ _ _ h).of_iso
    (integerResolutionColumnIso S p I).symm

/-! ### Vanishing of the cohomology of the total site -/

/-- **The complex `Hom(ℤ, I^•)` on the total site is exact in degree zero** as soon as
`H^{-p}(C_p, K_p)` vanishes for every `p ≥ 0`, for `K` represented by the K-injective complex
`I`. This is the core of Stacks 0H0W (1), through the integral resolution of Stacks 09WI and
Stacks 0H0Q. -/
lemma exactAt_coyonedaComplex_totalIntegerSheaf
    (I : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) [I.IsKInjective]
    (h : ∀ p : ℕ, Subsingleton
      ((DerivedCategory.singleFunctor (Sheaf (S.componentTopology ⦋p⦌) Ab.{u}) 0).obj
          (integerSheaf (S.componentTopology ⦋p⦌)) ⟶
        (DerivedCategory.Q.obj (((restrictAb S ⦋p⦌).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))⟦-(p : ℤ)⟧)) :
    (CochainComplex.coyonedaComplex S.totalIntegerSheaf I).ExactAt 0 := by
  have := CochainComplex.HomComplex.homComplexMap_quasiIso
    (S.integerCochainAugmentation) (𝟙 I)
  refine CochainComplex.exactAt_coyonedaComplex_of_homComplex _ _ _ ?_
  refine (exactAt_iff_of_quasiIsoAt (CochainComplex.HomComplex.homComplexMap
    (S.integerCochainAugmentation) (𝟙 I)) 0).2 ?_
  refine HomologicalComplex.ExactAt.of_iso ?_
    (CochainComplex.homProductTotalIso (S.simplicialIntegerComplex) I).symm
  exact HomologicalComplex₂.productTotal_exactAt_zero _
    (fun p => exactAt_column S p I (h p))

/-- A K-injective complex with injective terms representing a given object of the unbounded
derived category of the total site. -/
abbrev totalKInjectiveModel (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ :=
  (Stacks.Injectives.kInjectiveResolutionFunctor _).obj (DerivedCategory.Q.objPreimage K)

/-- The chosen K-injective complex represents the object it was chosen for. -/
def totalKInjectiveModelIso (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    DerivedCategory.Q.obj (totalKInjectiveModel S K) ≅ K :=
  (asIso (DerivedCategory.Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion _).app
    (DerivedCategory.Q.objPreimage K)))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K

/-- **Stacks 0H0W (1).** In the situation of Stacks 09WE, let `K` be an object of
`D(C_total)`. If `H^{-p}(C_p, K_p) = 0` for all `p ≥ 0`, then `H^0(C_total, K) = 0`.

Cohomology is written in its derived-Hom form: `H^i(C, K)` is the group of morphisms from the
constant integer sheaf of `C`, placed in degree zero, to `K[i]`; and the restriction `K_p` of
`K` to the component in simplicial degree `p` is `componentRestrictionDerived S ⦋p⦌` applied
to `K`. -/
@[stacks 0H0W "part (1): vanishing of H^0"]
theorem subsingleton_hom_totalIntegerSheaf
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    (h : ∀ p : ℕ, Subsingleton
      ((DerivedCategory.singleFunctor (Sheaf (S.componentTopology ⦋p⦌) Ab.{u}) 0).obj
          (integerSheaf (S.componentTopology ⦋p⦌)) ⟶
        ((componentRestrictionDerived S ⦋p⦌).obj K)⟦-(p : ℤ)⟧)) :
    Subsingleton ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
      S.totalIntegerSheaf ⟶ K) := by
  have eI : DerivedCategory.Q.obj (totalKInjectiveModel S K) ≅ K := totalKInjectiveModelIso S K
  have h' : ∀ p : ℕ, Subsingleton
      ((DerivedCategory.singleFunctor (Sheaf (S.componentTopology ⦋p⦌) Ab.{u}) 0).obj
          (integerSheaf (S.componentTopology ⦋p⦌)) ⟶
        (DerivedCategory.Q.obj (((restrictAb S ⦋p⦌).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (totalKInjectiveModel S K)))⟦-(p : ℤ)⟧) := by
    intro p
    have := h p
    have α : DerivedCategory.Q.obj (((restrictAb S ⦋p⦌).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (totalKInjectiveModel S K)) ≅
        (componentRestrictionDerived S ⦋p⦌).obj K :=
      ((restrictAb S ⦋p⦌).mapDerivedCategoryFactors.app
        (totalKInjectiveModel S K)).symm ≪≫ (componentRestrictionDerived S ⦋p⦌).mapIso eI
    exact (Iso.homCongr (Iso.refl _) ((shiftFunctor _ (-(p : ℤ))).mapIso α)).subsingleton
  have hsub : Subsingleton ((CochainComplex.coyonedaComplex S.totalIntegerSheaf
      (totalKInjectiveModel S K)).homology 0) :=
    AddCommGrpCat.isZero_iff_subsingleton.1
      (S.exactAt_coyonedaComplex_totalIntegerSheaf (totalKInjectiveModel S K) h').isZero_homology
  have hβ : Subsingleton
      ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
        S.totalIntegerSheaf ⟶ (DerivedCategory.Q.obj (totalKInjectiveModel S K))⟦(0 : ℤ)⟧) :=
    (CochainComplex.coyonedaComplexHomologyEquiv S.totalIntegerSheaf
      (totalKInjectiveModel S K) 0).symm.toEquiv.subsingleton
  exact (Iso.homCongr (Iso.refl _)
    ((shiftFunctorZero _ ℤ).app (DerivedCategory.Q.obj (totalKInjectiveModel S K)) ≪≫
      eI)).symm.subsingleton

/-- **Stacks 0H0W (2).** In the situation of Stacks 09WE, let `K` be an object of
`D(C_total)`. If `RΓ(C_p, K_p) = 0` for all `p ≥ 0`, then `RΓ(C_total, K) = 0`.

Vanishing of `RΓ` is the vanishing of every cohomology group, written in derived-Hom form as in
`subsingleton_hom_totalIntegerSheaf`. -/
@[stacks 0H0W "part (2): vanishing of RΓ"]
theorem subsingleton_hom_totalIntegerSheaf_shift
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    (h : ∀ (p : ℕ) (i : ℤ), Subsingleton
      ((DerivedCategory.singleFunctor (Sheaf (S.componentTopology ⦋p⦌) Ab.{u}) 0).obj
          (integerSheaf (S.componentTopology ⦋p⦌)) ⟶
        ((componentRestrictionDerived S ⦋p⦌).obj K)⟦i⟧)) (i : ℤ) :
    Subsingleton ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
      S.totalIntegerSheaf ⟶ K⟦i⟧) := by
  refine S.subsingleton_hom_totalIntegerSheaf (K⟦i⟧) fun p => ?_
  have := h p (i - p)
  have e : ((componentRestrictionDerived S ⦋p⦌).obj (K⟦i⟧))⟦-(p : ℤ)⟧ ≅
      ((componentRestrictionDerived S ⦋p⦌).obj K)⟦i - (p : ℤ)⟧ :=
    (shiftFunctor _ (-(p : ℤ))).mapIso
        (((componentRestrictionDerived S ⦋p⦌).commShiftIso i).app K) ≪≫
      (shiftFunctorAdd' _ i (-(p : ℤ)) (i - (p : ℤ)) (by omega)).symm.app
        ((componentRestrictionDerived S ⦋p⦌).obj K)
  exact (Iso.homCongr (Iso.refl _) e).subsingleton

end CategoryTheory.SimplicialSiteSituation

end
