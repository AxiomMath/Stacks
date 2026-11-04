module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectCornerBridge

/-!
# The comparison functor of Stacks Tag 0EXC is an equivalence

Let `p` be a prime, let `A` be a ring in characteristic `p`, let `f ∈ A` and let `J ⊆ A` be an
ideal annihilated by `f ^ n`, so that the spectra of

```
A ⧸ (J + fA) <--- A ⧸ J
      ^             ^
      |             |
   A ⧸ fA   <---    A
```

form the almost blowup square of More on Flatness, Example 0EVG. The comparison functor

`colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`

is `AlgebraicGeometry.colimVectComparison`; it is faithful by
`AlgebraicGeometry.colimVectComparison_faithful`, full by
`AlgebraicGeometry.colimVectComparison_full`, and essentially surjective as soon as the
compatibility over the exceptional corner of
`AlgebraicGeometry.colimVectComparison_essSurj_of_corner_compat` holds. This file proves that
compatibility, hence that the comparison functor is an equivalence.

## Main definitions

* `AlgebraicGeometry.OneGeneratorSquare.ctrIterSpecIso`, `…modIterSpecIso` and
  `…excIterSpecIso`: the `N`-fold Frobenius pullback on each of the three closed subschemes of
  the square, read as restriction along `Spec` of the `p ^ N`-power map.

## Main results

* `AlgebraicGeometry.OneGeneratorSquare.ctrCornerSquareIter_inv_eq` and
  `…modCornerSquareIter_inv_eq`: the inverse iterated Frobenius comparison on each leg into the
  exceptional corner, as the comparison of the square of the two `p ^ N`-power morphisms.
* `AlgebraicGeometry.OneGeneratorSquare.colimVectComparison_corner_compat`: **the compatibility
  over the exceptional corner of the two restrictions of the vector bundle glued from a finite
  projective `A ⧸ (J ∩ fA)`-module.**
* `AlgebraicGeometry.colimVectComparison_essSurj`: **the comparison functor of Stacks Tag 0EXC is
  essentially surjective.**
* `AlgebraicGeometry.colimVectComparison_isEquivalence`: **Stacks Tag 0EXC** — the comparison
  functor is an equivalence.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius
open MilnorPatching.OneGeneratorFrobenius

universe u

namespace AlgebraicGeometry

namespace OneGeneratorSquare

/-! ### The iterated Frobenius pullback as restriction along the power map -/

section Iter

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime]
  (hp : (p : A) = 0) (N : ℕ)

/-- **The `N`-fold Frobenius pullback on the centre is restriction along `Spec` of the
`p ^ N`-power map.** This is `AlgebraicGeometry.frobeniusPullbackIterSpecIso` with the iterate
written as `CategoryTheory.Functor.endoIter` of `AlgebraicGeometry.OneGeneratorSquare.frobCtr`. -/
def ctrIterSpecIso :
    (frobCtr A f p hp).endoIter N ≅
      Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (frobeniusPow (A ⧸ Ideal.span {f}) p
          (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N))) :=
  frobeniusPullbackIterSpecIso (A ⧸ Ideal.span {f}) p
    (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N

/-- **The `N`-fold Frobenius pullback on the modification is restriction along `Spec` of the
`p ^ N`-power map.** -/
def modIterSpecIso :
    (frobMod A J p hp).endoIter N ≅
      Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (frobeniusPow (A ⧸ J) p (natCast_quotient_eq_zero A p hp J) N))) :=
  frobeniusPullbackIterSpecIso (A ⧸ J) p (natCast_quotient_eq_zero A p hp J) N

/-- **The `N`-fold Frobenius pullback on the exceptional corner is restriction along `Spec` of
the `p ^ N`-power map.** -/
def excIterSpecIso :
    (frobExc A f J p hp).endoIter N ≅
      Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (frobeniusPow (A ⧸ (J ⊔ Ideal.span {f})) p
          (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f})) N))) :=
  frobeniusPullbackIterSpecIso (A ⧸ (J ⊔ Ideal.span {f})) p
    (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f})) N

/-- **The inverse iterated Frobenius comparison on the leg from the centre into the exceptional
corner is the comparison of the square of the two `p ^ N`-power morphisms.** -/
lemma ctrCornerSquareIter_inv_eq
    (hF : Spec.map (ctrToExc A f J) ≫
        Spec.map (CommRingCat.ofHom (frobeniusPow (A ⧸ Ideal.span {f}) p
          (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N)) =
      Spec.map (CommRingCat.ofHom (frobeniusPow (A ⧸ (J ⊔ Ideal.span {f})) p
          (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f})) N)) ≫
        Spec.map (ctrToExc A f J))
    (E : (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Vect) :
    (vectCtrExc A f J).map ((ctrIterSpecIso A f p hp N).inv.app E) ≫
        (ctrCornerSquareIter A f J p hp N E).inv =
      (vectPullbackSquareIso hF).hom.app E ≫
        (excIterSpecIso A f J p hp N).inv.app ((vectCtrExc A f J).obj E) :=
  specIter_squareIter_inv (A ⧸ (J ⊔ Ideal.span {f})) (A ⧸ Ideal.span {f}) p
    (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f}))
    (natCast_quotient_eq_zero A p hp (Ideal.span {f})) (Spec.map (ctrToExc A f J)) N hF E

/-- **The inverse iterated Frobenius comparison on the leg from the modification into the
exceptional corner is the comparison of the square of the two `p ^ N`-power morphisms.** -/
lemma modCornerSquareIter_inv_eq
    (hF : Spec.map (modToExc A f J) ≫
        Spec.map (CommRingCat.ofHom (frobeniusPow (A ⧸ J)
          p (natCast_quotient_eq_zero A p hp J) N)) =
      Spec.map (CommRingCat.ofHom (frobeniusPow (A ⧸ (J ⊔ Ideal.span {f})) p
          (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f})) N)) ≫
        Spec.map (modToExc A f J))
    (E : (Spec (CommRingCat.of (A ⧸ J))).Vect) :
    (vectModExc A f J).map ((modIterSpecIso A J p hp N).inv.app E) ≫
        (modCornerSquareIter A f J p hp N E).inv =
      (vectPullbackSquareIso hF).hom.app E ≫
        (excIterSpecIso A f J p hp N).inv.app ((vectModExc A f J).obj E) :=
  specIter_squareIter_inv (A ⧸ (J ⊔ Ideal.span {f})) (A ⧸ J) p
    (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f}))
    (natCast_quotient_eq_zero A p hp J) (Spec.map (modToExc A f J)) N hF E

end Iter

/-! ### The compatibility over the exceptional corner -/

/-- Pasting a commuting square along `σ` with a square commuting up to an endomorphism. -/
private theorem comp_comp_eq_of_squares {C : Type*} [Category C] {W X Y Z : C}
    {σ : W ⟶ X} {c : X ⟶ Y} {b : Y ⟶ Z} {P₁ : X ⟶ X} {ρ : X ⟶ Z} {P : W ⟶ W}
    (h : c ≫ b = P₁ ≫ ρ) (hF : σ ≫ P₁ = P ≫ σ) : (σ ≫ c) ≫ b = P ≫ σ ≫ ρ := by
  rw [Category.assoc, h, ← Category.assoc, hF, Category.assoc]

/-- **The compatibility over the exceptional corner of the two restrictions of the vector bundle
glued from a finite projective `A ⧸ (J ∩ fA)`-module.** The two restrictions of
`AlgebraicGeometry.OneGeneratorSquare.betaGluedVect`, identified with the `N`-th Frobenius twists
of the two reductions of `L` and pushed into the corner, differ by the structural isomorphism
`AlgebraicGeometry.OneGeneratorSquare.finProjCornerIso` of the compatible pair attached to `L`. -/
theorem colimVectComparison_corner_compat (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) (N n : ℕ) (hann : ∀ x ∈ J, f ^ n * x = 0)
    (hN : n + 1 ≤ p ^ N) (L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))) :
    (vectCtrExc A f J).map (betaGluedVectCentreTwistIso A f J n hann p hp N hN L).hom ≫
        (ctrCornerSquareIter A f J p hp N (vectOfFinProjCentre A f J L)).inv =
      (squareVectIso A f J).inv.app (betaGluedVect A f J n hann p hp N hN L) ≫
        (vectModExc A f J).map (betaGluedVectModificationTwistIso A f J n hann p hp N hN L).hom ≫
          (modCornerSquareIter A f J p hp N (vectOfFinProjModification A f J L)).inv ≫
            ((frobExc A f J p hp).endoIter N).map (finProjCornerIso A f J L).hom := by
  have hFC := specMap_frobeniusPow_square p
    (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f}))
    (natCast_quotient_eq_zero A p hp (Ideal.span {f})) (ctrToExc A f J) N
  have hFM := specMap_frobeniusPow_square p
    (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f}))
    (natCast_quotient_eq_zero A p hp J) (modToExc A f J) N
  have legC : ((vectCtrExc A f J).map
            ((vectPullbackSquareIso
                  (specMap_betaHom_centre_square A f J n hann p hp N hN)).hom.app
                ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L) ≫
              (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
                (frobeniusPow (A ⧸ Ideal.span {f}) p
                  (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N)))).map
                ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
                  (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).hom.app L)) ≫
          (vectPullbackSquareIso hFC).hom.app (vectOfFinProjCentre A f J L)) ≫
        (excIterSpecIso A f J p hp N).inv.app
          ((vectCtrExc A f J).obj (vectOfFinProjCentre A f J L)) =
      (vectCtrExc A f J).map (betaGluedVectCentreTwistIso A f J n hann p hp N hN L).hom ≫
        (ctrCornerSquareIter A f J p hp N (vectOfFinProjCentre A f J L)).inv := by
    rw [Category.assoc, ← ctrCornerSquareIter_inv_eq A f J p hp N hFC
        (vectOfFinProjCentre A f J L),
      ← Category.assoc, ← CategoryTheory.Functor.map_comp]
    rfl
  have legM : ((vectModExc A f J).map
            ((vectPullbackSquareIso
                  (specMap_betaHom_modification_square A f J n hann p hp N hN)).hom.app
                ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L) ≫
              (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
                (frobeniusPow (A ⧸ J) p (natCast_quotient_eq_zero A p hp J) N)))).map
                ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
                  (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).hom.app L)) ≫
          (vectPullbackSquareIso hFM).hom.app (vectOfFinProjModification A f J L)) ≫
        (excIterSpecIso A f J p hp N).inv.app
          ((vectModExc A f J).obj (vectOfFinProjModification A f J L)) =
      (vectModExc A f J).map (betaGluedVectModificationTwistIso A f J n hann p hp N hN L).hom ≫
        (modCornerSquareIter A f J p hp N (vectOfFinProjModification A f J L)).inv := by
    rw [Category.assoc, ← modCornerSquareIter_inv_eq A f J p hp N hFM
        (vectOfFinProjModification A f J L),
      ← Category.assoc, ← CategoryTheory.Functor.map_comp]
    rfl
  have flat := vectCornerFlat
    (Spec.map (CommRingCat.ofHom (betaHom hann p hp N hN)))
    (Spec.map (toCtr A f)) (Spec.map (toMod A J))
    (Spec.map (ctrToExc A f J)) (Spec.map (modToExc A f J))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f}))))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J))))
    (Spec.map (CommRingCat.ofHom (frobeniusPow (A ⧸ Ideal.span {f}) p
      (natCast_quotient_eq_zero A p hp (Ideal.span {f})) N)))
    (Spec.map (CommRingCat.ofHom (frobeniusPow (A ⧸ J) p (natCast_quotient_eq_zero A p hp J) N)))
    (Spec.map (CommRingCat.ofHom (frobeniusPow (A ⧸ (J ⊔ Ideal.span {f})) p
      (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f})) N)))
    (specMap_betaHom_centre_square A f J n hann p hp N hN)
    (specMap_betaHom_modification_square A f J n hann p hp N hN)
    (specMap_square A f J) hFC hFM (specMap_factor_square A f J)
    (comp_comp_eq_of_squares (specMap_betaHom_centre_square A f J n hann p hp N hN) hFC)
    (comp_comp_eq_of_squares (specMap_betaHom_modification_square A f J n hann p hp N hN) hFM)
    ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L)
    (vectOfFinProjCentre A f J L) (vectOfFinProjModification A f J L)
    ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
      (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).hom.app L)
    ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
      (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).hom.app L)
    (finProjCornerIso A f J L).hom (tildeVect_cornerFlat_hyp A f J L)
  refine legC.symm.trans ?_
  rw [flat]
  simp only [Category.assoc]
  rw [(excIterSpecIso A f J p hp N).inv.naturality (finProjCornerIso A f J L).hom,
    reassoc_of% legM]
  exact congrArg (fun z ↦ (squareVectIso A f J).inv.app
    (betaGluedVect A f J n hann p hp N hN L) ≫ z) (Category.assoc _ _ _)

end OneGeneratorSquare

/-! ### Stacks Tag 0EXC -/

open OneGeneratorSquare

/-- The comparison functor `AlgebraicGeometry.colimVectComparison` is essentially
surjective. -/
theorem colimVectComparison_essSurj (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    (colimVectComparison A f J p hp).EssSurj :=
  colimVectComparison_essSurj_of_corner_compat A f J n hann p hp (n + 1)
    (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    fun L ↦ colimVectComparison_corner_compat A f J p hp (n + 1) n hann
      (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le L

/-- Let `p` be a prime, let `A` be a ring with `p = 0`, let `f ∈ A` and let `J ⊆ A` be an ideal
annihilated by `f ^ n`, so that

```
A ⧸ (J + fA) <--- A ⧸ J
      ^             ^
      |             |
   A ⧸ fA   <---    A
```

is the almost blowup square of More on Flatness, Example 0EVG. Then the comparison functor

`colim_F Vect(Spec A) ⟶ colim_F Vect(Spec (A ⧸ fA)) ×_{colim_F Vect(Spec (A ⧸ (J + fA)))}
  colim_F Vect(Spec (A ⧸ J))`

of Frobenius-colimit categories of vector bundles **is an equivalence.** -/
@[stacks 0EXC]
theorem colimVectComparison_isEquivalence (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (n : ℕ) (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    (colimVectComparison A f J p hp).IsEquivalence :=
  ⟨colimVectComparison_faithful A f J n hann p hp, colimVectComparison_full A f J p hp,
    colimVectComparison_essSurj A f J n hann p hp⟩

end AlgebraicGeometry

end
