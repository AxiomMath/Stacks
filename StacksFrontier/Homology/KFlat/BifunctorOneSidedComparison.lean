module

public import StacksFrontier.Homology.KFlat.BifunctorOneSided

/-!
# The one-sided K-flat comparison agrees with the two-sided one

For an additive bifunctor `F : A ⥤ B ⥤ D` whose derived descent
`CochainComplex.KFlatBifunctor.derivedBifunctor` exists there are two comparisons of that
descent with the total complex `Tot(F(K, L))`: the two-sided
`CochainComplex.KFlatBifunctor.comparison`, which assumes `K` left K-flat and `L` K-flat,
and the one-sided `CochainComplex.KFlatBifunctor.comparisonRight`, which assumes only that
`L` is K-flat. This file shows that they agree wherever both apply.

## Main results

* `CochainComplex.KFlatBifunctor.comparisonRight_eq_comparison`: **the one-sided and the
  two-sided K-flat comparisons are the same isomorphism** on a pair for which both are
  defined, together with its `hom`-level form
  `CochainComplex.KFlatBifunctor.comparisonRight_hom_eq_comparison_hom`.

## Implementation notes

There is no mathematics here: `comparisonRight` is *built* from the same `Lifting₂`
isomorphism `derivedBifunctorComparisonIso` that `comparison` is built from, so the
statement is a bookkeeping identity, and the work is to strip the two `preimageIso`s that
stand between the two spellings.

Each of the two one-sided constructions is a `CategoryTheory.Functor.FullyFaithful.preimageIso`
along precomposition with a localization functor, so applying that precomposition functor
back to it returns the isomorphism it was built from; that is
`CategoryTheory.Functor.FullyFaithful.map_preimage`, and it is the content of
`whiskerLeft_homotopyToDerivedRightIso_hom` and `whiskerLeft_derivedBifunctorRightIso_hom`.
Reading those two off componentwise gives the value of each isomorphism at an object *in the
image* of the localization — `derivedBifunctorRightIso` at `Qh(K̄)` and
`homotopyToDerivedRightIso` at `K̄` — which is where the two chains can be compared.

Both comparisons start at `Q K`, not at `Qh(K̄)`, so after that the two components must be
transported along `DerivedCategory.quotientCompQhIso`. This is done twice, in opposite
directions, and the two transports are exactly what makes the identity come out:

* `derivedToDerivedRightFac_hom_app` moves `derivedToDerivedRightFac` from `Q K` to `K̄`,
  using that `homotopyToDerivedRightIso` is the preimage of a composite whose middle factor
  is `quotientCompQhIso` whiskered into `derivedToDerivedRight`. The two directions of
  `quotientCompQhIso` cancel under `derivedToDerivedRight`.
* `comparisonRightFac_hom_app` then moves `derivedBifunctorRightIso` from `Q K` to `Qh(K̄)`
  by its own naturality along `(quotientCompQhIso A).inv.app K`, which is the step that
  turns the one-sided factor into `derivedBifunctorComparisonIso` plus a `derivedBifunctor`
  map — and that map is precisely the leading factor of `comparison` which `comparisonRight`
  does not have.

With that, `comparison` and `comparisonRight` have the same three trailing factors, and the
remaining discrepancy is one naturality square for `derivedBifunctor` in its second
variable (`quotientCompQhIso B` against the `Q K` versus `Qh(K̄)` map).

Every intermediate statement here is written in the `Qh.obj (quotient.obj K)` spelling rather
than the `(quotient ⋙ Qh).obj K` one that the localization API produces, and is proved by a
term whose type is only definitionally that; this keeps `rw` from failing on two spellings of
one object.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

section

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]

omit [HasDerivedCategory B] in
/-- `homotopyToDerivedRightIso` is the preimage, along precomposition with the homotopy
quotient, of the `Q` versus `Qh ∘ quotient` bridge whiskered into `derivedToDerivedRight`.
Precomposition with a localization functor is fully faithful, so whiskering the isomorphism
back along the quotient returns that bridge. -/
theorem whiskerLeft_homotopyToDerivedRightIso_hom :
    Functor.whiskerLeft (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (homotopyToDerivedRightIso F).hom =
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
          (derivedToDerivedRight F) ≪≫
        derivedToDerivedRightFac F).hom :=
  (CategoryTheory.Localization.fullyFaithfulWhiskeringLeft
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    ((kFlatObjects F).FullSubcategory ⥤ DerivedCategory D)).map_preimage _

omit [HasDerivedCategory B] in
/-- The component of `homotopyToDerivedRightIso` at the homotopy class of a cochain complex:
the `Q` versus `Qh ∘ quotient` bridge, pushed through `derivedToDerivedRight`, followed by
the descent's factorisation. -/
theorem homotopyToDerivedRightIso_hom_app_quotient (K : CochainComplex A ℤ) :
    (homotopyToDerivedRightIso F).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      (derivedToDerivedRight F).map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫
        (derivedToDerivedRightFac F).hom.app K := by
  simpa using NatTrans.congr_app (whiskerLeft_homotopyToDerivedRightIso_hom F) K

omit [HasDerivedCategory B] in
/-- **`derivedToDerivedRightFac` transported from `Q K` to the homotopy class of `K`.** The
two directions of the `Q` versus `Qh ∘ quotient` bridge cancel inside
`derivedToDerivedRight`, so reading `homotopyToDerivedRightIso_hom_app_quotient` backwards
recovers the factorisation itself. -/
theorem derivedToDerivedRightFac_hom_app (K : CochainComplex A ℤ) :
    (derivedToDerivedRightFac F).hom.app K =
      (derivedToDerivedRight F).map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
        (homotopyToDerivedRightIso F).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) := by
  rw [homotopyToDerivedRightIso_hom_app_quotient, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

section Comparison

variable [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- `derivedBifunctorRightIso` is the preimage, along precomposition with `kFlatQLeft`, of
the two-sided comparison `derivedBifunctorComparisonIso` corrected by
`homotopyToDerivedRightIso`. Whiskering it back along `kFlatQLeft` returns that composite,
precomposition with a localization functor being fully faithful. -/
theorem whiskerLeft_derivedBifunctorRightIso_hom :
    Functor.whiskerLeft (kFlatQLeft F) (derivedBifunctorRightIso F).hom =
      (derivedBifunctorComparisonIso F ≪≫
        (Functor.isoWhiskerLeft (kFlatObjectsLeft F).ι
          (homotopyToDerivedRightIso F)).symm ≪≫
        (Functor.associator _ _ _).symm).hom :=
  (CategoryTheory.Localization.fullyFaithfulWhiskeringLeft (kFlatQLeft F)
    (kFlatQuasiIsoLeft F)
    ((kFlatObjects F).FullSubcategory ⥤ DerivedCategory D)).map_preimage _

/-- The component of `derivedBifunctorRightIso` at a left K-flat object of `K(A)`, read in
the derived category: the two-sided comparison there, corrected by
`homotopyToDerivedRightIso`. -/
theorem derivedBifunctorRightIso_hom_app
    (W : HomotopyCategory A (ComplexShape.up ℤ)) (hW : kFlatObjectsLeft F W) :
    (derivedBifunctorRightIso F).hom.app ((DerivedCategory.Qh (C := A)).obj W) =
      (derivedBifunctorComparisonIso F).hom.app ⟨W, hW⟩ ≫
        (homotopyToDerivedRightIso F).inv.app W := by
  simpa using
    NatTrans.congr_app (whiskerLeft_derivedBifunctorRightIso_hom F)
      (⟨W, hW⟩ : (kFlatObjectsLeft F).FullSubcategory)

/-- `derivedBifunctorRightIso_hom_app` with the correction cancelled off: on a left K-flat
object of `K(A)` the one-sided comparison followed by `homotopyToDerivedRightIso` *is* the
two-sided comparison. -/
theorem derivedBifunctorRightIso_hom_app_comp
    (W : HomotopyCategory A (ComplexShape.up ℤ)) (hW : kFlatObjectsLeft F W) :
    (derivedBifunctorRightIso F).hom.app ((DerivedCategory.Qh (C := A)).obj W) ≫
        (homotopyToDerivedRightIso F).hom.app W =
      (derivedBifunctorComparisonIso F).hom.app ⟨W, hW⟩ := by
  have hcancel : (homotopyToDerivedRightIso F).inv.app W ≫
      (homotopyToDerivedRightIso F).hom.app W =
    𝟙 ((kFlatToDerived F).obj ⟨W, hW⟩) := (homotopyToDerivedRightIso F).inv_hom_id_app W
  rw [derivedBifunctorRightIso_hom_app F W hW, Category.assoc, hcancel, Category.comp_id]

/-- **`comparisonRightFac` is the two-sided comparison, transported to `Q K`.** The
one-sided factorisation at `K` is `derivedBifunctorComparisonIso` at the homotopy class of
`K`, preceded by the `derivedBifunctor`-image of the `Q` versus `Qh ∘ quotient` bridge; the
transport is naturality of `derivedBifunctorRightIso` along that bridge, and the correction
it introduces is cancelled by `derivedBifunctorRightIso_hom_app_comp`. -/
theorem comparisonRightFac_hom_app (K : CochainComplex A ℤ) (hK : KFlatLeft F K) :
    (comparisonRightFac F).hom.app K =
      (derivedBifunctorRight F).map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
        (derivedBifunctorComparisonIso F).hom.app
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ := by
  have hfac : (comparisonRightFac F).hom.app K =
      (derivedBifunctorRightIso F).hom.app (DerivedCategory.Q.obj K) ≫
        (derivedToDerivedRightFac F).hom.app K := by
    simp only [comparisonRightFac, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  have hnat : (derivedBifunctorRight F).map
          ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
        (derivedBifunctorRightIso F).hom.app
          ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      (derivedBifunctorRightIso F).hom.app (DerivedCategory.Q.obj K) ≫
        (derivedToDerivedRight F).map ((DerivedCategory.quotientCompQhIso A).inv.app K) :=
    (derivedBifunctorRightIso F).hom.naturality _
  rw [hfac, derivedToDerivedRightFac_hom_app, ← Category.assoc, ← hnat, Category.assoc,
    derivedBifunctorRightIso_hom_app_comp F
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) hK]

/-- The four factors of the two-sided `comparison`, with its last two bundled as
`totalComplexQhIso`, which is the spelling `comparisonRight_hom` uses. -/
theorem comparison_hom (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : KFlatLeft F K) (hL : KFlat F L) :
    (comparison F K L hK hL).hom =
      ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).inv.app K)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((derivedBifunctorComparisonIso F).hom.app
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≫
        (totalComplexQhIso F K L).hom := by
  simp only [comparison, totalComplexQhIso, homotopyBifunctorIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]

/-- **The one-sided comparison agrees with the two-sided one**, at the level of the
underlying morphism. -/
theorem comparisonRight_hom_eq_comparison_hom (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) (hK : KFlatLeft F K) (hL : KFlat F L) :
    (comparisonRight F K L hL).hom = (comparison F K L hK hL).hom := by
  have hmid : ((comparisonRightFac F).hom.app K).app
        ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ =
      ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).inv.app K)).app
          ((DerivedCategory.Qh (C := B)).obj
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) ≫
        ((derivedBifunctorComparisonIso F).hom.app
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ :=
    NatTrans.congr_app (comparisonRightFac_hom_app F K hK) _
  have hnat : ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).inv.app K)).app
          ((DerivedCategory.Qh (C := B)).obj
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) =
      ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).inv.app K)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) :=
    ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).inv.app K)).naturality _
  rw [comparisonRight_hom, comparison_hom, hmid]
  simp only [Category.assoc]
  rw [← Category.assoc, hnat, Category.assoc]

/-- **The one-sided K-flat comparison is the two-sided one** wherever both apply: a K-flat
right factor and a left K-flat left factor. Both are built from the same `Lifting₂`
isomorphism `derivedBifunctorComparisonIso`, and the identity is the bookkeeping that
identifies the two routes to it. -/
theorem comparisonRight_eq_comparison (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : KFlatLeft F K) (hL : KFlat F L) :
    comparisonRight F K L hL = comparison F K L hK hL :=
  Iso.ext (comparisonRight_hom_eq_comparison_hom F K L hK hL)

end Comparison

end

end CochainComplex.KFlatBifunctor

end

end
