module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Basic
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing
public import StacksFrontier.RingTheory.Henselian.Pair.Operations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale covers of a scheme finite over a henselian pair

Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be a *finite* morphism.  This file proves
that base change to the closed fibre `X ×_{Spec A} Spec (A ⧸ I) ⟶ X` is an equivalence on
categories of finite étale covers — that is, the conclusion of Stacks Tag 0GS2 for the finite
morphisms, which are exactly the proper morphisms along which no algebraization is needed.  Taking
`I` to be the maximal ideal of a henselian local ring gives Stacks Tag 0A48 for the finite
morphisms.

The mechanism is that a finite morphism is affine, so `X ≅ Spec B` for `B = Γ(X, ⊤)` a finite —
hence integral — `A`-algebra, and `(B, I B)` is again a henselian pair
(`henselianPair_map_of_isIntegral`, Tag 09XK).  Gabber's equivalence for a henselian pair in the
affine case (`finiteEtaleBaseChange_isEquivalence_of_henselianPair`, Tag 09ZS) applies to `(B, I B)`
directly, and what remains is to identify the closed fibre of `X ⟶ Spec A` with `Spec (B ⧸ I B)`.
That identification is made in two steps: `pullbackSpecIso` turns the closed fibre into
`Spec (B ⊗[A] (A ⧸ I))`, and `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` identifies that
`B`-algebra with `B ⧸ I B`.  Both steps change the base-change morphism only by composition with an
isomorphism, which is absorbed by the three transport lemmas proved first.

The general — proper, not merely finite — case of Tag 0GS2 is
`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair` in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianPair`; it uses
Grothendieck existence and Artin approximation, none of which is needed here.  The general case is
reduced to *essential surjectivity* by
`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`, and
`finiteEtaleBaseChange_essSurj_of_isFinite_of_henselianPair` proves that family of
essential-surjectivity statements directly for a finite `f`.

## Main results

* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isIso` — base change along an
  isomorphism is an equivalence on finite étale covers.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_isIso_comp` and
  `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_comp_isIso` — composing the base-change
  morphism with an isomorphism on either side does not change whether base change is an
  equivalence.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPair` — the
  affine core: for an integral algebra `B` over a henselian pair `(A, I)`, base change along the
  closed fibre of `Spec B ⟶ Spec A` is an equivalence.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianPair` — the
  conclusion of Tag 0GS2 for a finite morphism to the spectrum of a henselian pair.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianLocalRing` — the
  same statement over a henselian local ring and its maximal ideal, which is Tag 0A48 for a
  finite morphism.
* `AlgebraicGeometry.finiteEtaleBaseChange_essSurj_of_isFinite_of_henselianPair` — the
  essential-surjectivity family assumed by the reduction of Tag 0GS2, proved for a finite
  morphism.

## References

* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 09ZS](https://stacks.math.columbia.edu/tag/09ZS)
* [Stacks Project, Tag 09XK](https://stacks.math.columbia.edu/tag/09XK)
-/

@[expose] public section

open CategoryTheory Limits TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Transport along an isomorphism -/

/-- Base change along an isomorphism is an equivalence of categories of finite étale covers.
The quasi-inverse is base change along the inverse isomorphism, and the two unit isomorphisms come
from `finiteEtaleBaseChangeComp` together with `finiteEtaleBaseChangeId`. -/
theorem isEquivalence_finiteEtaleBaseChange_of_isIso {Y₁ Y₂ : Scheme.{u}} (θ : Y₁ ⟶ Y₂) [IsIso θ] :
    (finiteEtaleBaseChange θ).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (finiteEtaleBaseChange θ) (finiteEtaleBaseChange (inv θ))
    (finiteEtaleBaseChangeId.symm.trans
      (finiteEtaleBaseChangeComp (inv θ) θ (𝟙 Y₂) (by simp)))
    ((finiteEtaleBaseChangeComp θ (inv θ) (𝟙 Y₁) (by simp)).symm.trans
      finiteEtaleBaseChangeId)).isEquivalence_functor

/-- The composite of two morphisms along which base change is an equivalence has the same
property. -/
private theorem isEquivalence_finiteEtaleBaseChange_comp {Y₁ Y₂ Y₃ : Scheme.{u}} (f : Y₁ ⟶ Y₂)
    (g : Y₂ ⟶ Y₃) (hf : (finiteEtaleBaseChange f).IsEquivalence)
    (hg : (finiteEtaleBaseChange g).IsEquivalence) :
    (finiteEtaleBaseChange (f ≫ g)).IsEquivalence :=
  have : (finiteEtaleBaseChange g ⋙ finiteEtaleBaseChange f).IsEquivalence :=
    Functor.isEquivalence_trans _ _
  Functor.isEquivalence_of_iso (finiteEtaleBaseChangeComp f g).symm

/-- Precomposing the base-change morphism with an isomorphism does not change whether base change
is an equivalence on finite étale covers. -/
theorem isEquivalence_finiteEtaleBaseChange_isIso_comp {Y₁ Y₂ P : Scheme.{u}} (θ : Y₁ ⟶ Y₂)
    [IsIso θ] (g : Y₂ ⟶ P) (h : (finiteEtaleBaseChange g).IsEquivalence) :
    (finiteEtaleBaseChange (θ ≫ g)).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_comp θ g (isEquivalence_finiteEtaleBaseChange_of_isIso θ) h

/-- Postcomposing the base-change morphism with an isomorphism does not change whether base change
is an equivalence on finite étale covers. -/
theorem isEquivalence_finiteEtaleBaseChange_comp_isIso {Y₁ Y₂ P : Scheme.{u}} (g : Y₁ ⟶ Y₂)
    (θ : Y₂ ⟶ P) [IsIso θ] (h : (finiteEtaleBaseChange g).IsEquivalence) :
    (finiteEtaleBaseChange (g ≫ θ)).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_comp g θ h (isEquivalence_finiteEtaleBaseChange_of_isIso θ)

/-! ### The affine core -/

/-- **The affine core of Tag 0GS2 for a finite morphism.** If `(A, I)` is a henselian pair and `B`
is an integral `A`-algebra, then base change along the first projection of
`Spec B ×_{Spec A} Spec (A ⧸ I)` is an equivalence on finite étale covers.

The pair `(B, I B)` is henselian by Tag 09XK, so Tag 09ZS gives the equivalence for the quotient map
`B ⟶ B ⧸ I B`.  The projection of the displayed pullback is that quotient map after two
isomorphisms: `pullbackSpecIso` presents the pullback as `Spec (B ⊗[A] (A ⧸ I))`, and
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot` identifies `B ⊗[A] (A ⧸ I)` with `B ⧸ I B` as a
`B`-algebra. -/
theorem isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPair
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (I : Ideal A) (hI : HenselianPair A I) :
    (finiteEtaleBaseChange
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))))).IsEquivalence := by
  have hJhens : HenselianPair B (I.map (algebraMap A B)) :=
    henselianPair_map_of_isIntegral I hI
  have h09ZS : (finiteEtaleBaseChange
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.map (algebraMap A B)))))).IsEquivalence :=
    finiteEtaleBaseChange_isEquivalence_of_henselianPair B _ hJhens
  have hfac : (CommRingCat.ofHom (algebraMap B (B ⊗[A] (A ⧸ I)))) =
      CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A B))) ≫
        CommRingCat.ofHom ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I :
          (B ⧸ (I.map (algebraMap A B))) →+* B ⊗[A] (A ⧸ I))) := by
    apply CommRingCat.hom_ext
    ext b
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk B I b).symm
  have heiso : IsIso (CommRingCat.ofHom
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I :
        (B ⧸ (I.map (algebraMap A B))) →+* B ⊗[A] (A ⧸ I)))) :=
    Iso.isIso_hom (RingEquiv.toCommRingCatIso
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toRingEquiv)
  have hstruct : (finiteEtaleBaseChange
      (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] (A ⧸ I)))))).IsEquivalence := by
    rw [hfac, Spec.map_comp]
    exact isEquivalence_finiteEtaleBaseChange_isIso_comp _ _ h09ZS
  have hproj : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
      = (pullbackSpecIso A B (A ⧸ I)).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] (A ⧸ I)))) := by
    rw [← pullbackSpecIso_inv_fst' A B (A ⧸ I), Iso.hom_inv_id_assoc]
  rw [hproj]
  exact isEquivalence_finiteEtaleBaseChange_isIso_comp _ _ hstruct

/-! ### Tag 0GS2 for a finite morphism -/

/-- **Tag 0GS2 for a finite morphism.** If `(A, I)` is a henselian pair and `f : X ⟶ Spec A` is
finite, then base change to the closed fibre `X ×_{Spec A} Spec (A ⧸ I) ⟶ X` is an equivalence on
finite étale covers.

A finite morphism is affine, so `X.isoSpec` presents `X` as `Spec Γ(X, ⊤)` with `Γ(X, ⊤)` a finite,
hence integral, `A`-algebra, and the statement becomes the affine core
`isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPair`.  The two differences
between the two base-change morphisms are absorbed by the transport lemmas: the pullback along a
composite is rebracketed by `pullbackRightPullbackFstIso`, and a pullback projection along the
isomorphism `X.isoSpec.hom` is itself that isomorphism's inverse precomposed with an isomorphism.

This is the finite case of Tag 0GS2, in which no algebraization — neither Grothendieck existence
nor Artin approximation — enters. The full statement, for any proper `f`, is
`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair`. -/
theorem isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsFinite f] :
    (finiteEtaleBaseChange
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).IsEquivalence := by
  have hX : IsAffine X := isAffine_of_isAffineHom f
  let φ : CommRingCat.of A ⟶ CommRingCat.of Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f)
  let _ : Algebra A Γ(X, ⊤) := φ.hom.toAlgebra
  have hfin : Module.Finite A Γ(X, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    exact (IsFinite.SpecMap_iff φ).mp (by rw [Spec.map_preimage]; infer_instance)
  have hint : Algebra.IsIntegral A Γ(X, ⊤) := Algebra.IsIntegral.of_finite A Γ(X, ⊤)
  have hf : f = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))) := by
    change f = X.isoSpec.hom ≫ Spec.map φ
    rw [Spec.map_preimage]
    simp
  have hcore : (finiteEtaleBaseChange
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).IsEquivalence :=
    isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPair A Γ(X, ⊤) I hI
  rw [hf]
  rw [show pullback.fst (X.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      = (pullbackRightPullbackFstIso (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) X.isoSpec.hom).inv ≫
          pullback.fst X.isoSpec.hom
            (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) from by
    rw [← pullbackRightPullbackFstIso_hom_fst
      (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) X.isoSpec.hom,
      Iso.inv_hom_id_assoc]]
  refine isEquivalence_finiteEtaleBaseChange_isIso_comp _ _ ?_
  have hiso : IsIso (pullback.snd X.isoSpec.hom
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :=
    (MorphismProperty.isomorphisms Scheme).pullback_snd _ _
      (inferInstanceAs (IsIso X.isoSpec.hom))
  rw [show pullback.fst X.isoSpec.hom
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
      = pullback.snd X.isoSpec.hom
          (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≫
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ X.isoSpec.inv) from by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]]
  exact @isEquivalence_finiteEtaleBaseChange_isIso_comp _ _ _ _ hiso _
    (isEquivalence_finiteEtaleBaseChange_comp_isIso _ _ hcore)

/-- **Tag 0A48 for a finite morphism.** If `A` is a henselian local ring and `f : X ⟶ Spec A` is
finite, then base change to the closed fibre `X ×_{Spec A} Spec (A ⧸ 𝔪) ⟶ X` is an equivalence on
finite étale covers.

A henselian local ring forms a henselian pair with its maximal ideal
(`henselianPair_maximalIdeal`), so this is the case `I = 𝔪` of
`isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianPair`. As there, no algebraization
is used: the general proper case of Tag 0A48 needs Grothendieck existence together with Artin
approximation. -/
@[stacks 0A48 "for a finite morphism `f : X ⟶ Spec A`, which is the case of a proper `f` in \
which no algebraization is needed",
  sga "3 X 4.0" "more general",
  sga "4 XII 5.9bis" "special case",
  sga "4 XIII 1.1" "partial",
  sga "4½ Arcata 4.2.2" "special case",
  sga "7 IX 2.2.4" "more general"]
theorem isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianLocalRing
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsFinite f] :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianPair A _
    (henselianPair_maximalIdeal A) f

/-- The essential-surjectivity family assumed by
`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`, proved for a finite
morphism `f : X ⟶ Spec A` over a henselian pair `(A, I)`.

Every `P` finite étale over `X` is in particular finite over `X`, so `P.hom ≫ f` is again finite and
`isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianPair` applies to it.  This exhibits a
witness for that hypothesis, so the reduction of Tag 0GS2 it feeds is not vacuous. -/
theorem finiteEtaleBaseChange_essSurj_of_isFinite_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsFinite f] (P : FiniteEtaleOver X) :
    (finiteEtaleBaseChange
      (pullback.fst (P.hom ≫ f)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).EssSurj :=
  have : IsFinite P.hom := P.prop.1
  have : IsFinite (P.hom ≫ f) := inferInstance
  (isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianPair A I hI (P.hom ≫ f)).essSurj

end AlgebraicGeometry

end
