module

public import StacksFrontier.Homology.KFlat.BifunctorComparisonCommShift
public import StacksFrontier.Homology.KFlat.BifunctorComplexModelsShiftLeft
import StacksCore.Tactic.StacksAttribute

/-!
# The K-flat comparison of Tag 06YU is shift-compatible, one variable at a time

`CochainComplex.KFlatBifunctor.comparison` is the comparison of [Stacks, Tag 06YU]: on a left
K-flat complex `K` and a K-flat complex `L` the derived bifunctor `derivedBifunctor F` evaluated
at `(QK, QL)` is `Q(Tot(F(K, L)))`.  `derivedComparisonNatIso` bundles it as an isomorphism of
bifunctors on the (left) K-flat complexes, and that bundling is *not* the level at which to prove
it shift-compatible: written out, it exposes three junctions, each needing a generic
`CategoryTheory.Functor.CommShift₂` closure property which does not exist (see the implementation
note in `PullbackTensorCommShiftComparisons.lean`, in the directory
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/`).

This file does it **one variable at a time**, which is all `CategoryTheory.NatTrans.CommShift₂`
ever asks for: that class is two one-variable conditions.  At one variable the toolbox is
complete — `CategoryTheory.NatTrans.CommShift.associator`, `whiskerLeft` and `whiskerRight` are
Mathlib's, the two bridges are `kFlatQuotientCompQIso_commShift` and
`kFlatQuotientCompQIsoLeft_commShift`, the two lift comparisons are
`kFlatQuotientCompι_commShift` and `kFlatQuotientCompιLeft_commShift`, and the two factors
carrying the content are the `commShift_app` and `commShift_flipApp` fields of
`derivedBifunctorComparisonIso_commShift₂` and `homotopyBifunctorComparisonIso_commShift₂`, which
are one-variable statements already.

## Main results

* `CochainComplex.KFlatBifunctor.comparisonSecond`: **the comparison at a fixed left K-flat first
  factor, as an isomorphism of functors on the K-flat complexes**, with `comparisonSecond_hom_app`
  recording that its components are the comparison and `comparisonSecond_commShift` that it is
  compatible with the shift.
* `CochainComplex.KFlatBifunctor.comparisonFirst`, `comparisonFirst_hom_app` and
  `comparisonFirst_commShift`: the mirror at a fixed K-flat second factor, as an isomorphism of
  functors on the left K-flat complexes.
* `CochainComplex.KFlatBifunctor.derivedComparisonObj`, `homotopyComparisonObj` and their flips:
  the four components of the two lifting isomorphisms, **restated at the spelling at which
  instance search finds the shift data of their source and target.**

## Implementation notes

**Why the four components of the lifting isomorphisms are restated.**
`CategoryTheory.Functor.whiskeringLeft₂` is `implicit_reducible` and not `instance_reducible`, so
the source of `(derivedBifunctorComparisonIso F).hom.app M` — which Lean displays as
`((((whiskeringLeft₂ _).obj (kFlatQLeft F)).obj (kFlatQ F)).obj (derivedBifunctor F)).obj M` —
carries no `CategoryTheory.Functor.CommShift` that instance search can find, even though it *is*
`kFlatQ F ⋙ (derivedBifunctor F).obj (Qh.obj M.obj)`, which does.  A `def` with an explicit type
fixes the spelling of its own type, so `derivedComparisonObj` is that component with the good
spelling, and its shift compatibility is the `commShift_app` field transported by nothing more
than the definitional unfolding.  Doing this for the four components is what makes the two chains
below close by `infer_instance` with no per-factor seating at all.

**Why the factors are reassociated rather than used as they stand.**  Each of the five factors of
`comparison` is a morphism *at an object*; what is needed is the natural transformation in the
other variable whose component it is.  The reassociation makes the source and target of each
factor spelled so that `infer_instance` sees the whiskering: `CategoryTheory.Functor.CommShift` of
a composite is `CategoryTheory.Functor.CommShift.comp`, which is not associative on the nose, so
`(q ⋙ q') ⋙ G` and `q ⋙ (q' ⋙ G)` carry different data and the passage between them is
`CategoryTheory.NatTrans.CommShift.associator`.  This is the step `kFlatQuotientCompQIsoAssoc`
takes one level down.

**The two lift comparisons are `CategoryTheory.Iso.refl`.**
`CategoryTheory.ObjectProperty.liftCompιIso` is literally the identity isomorphism, so
`kFlatQuotient F ⋙ (kFlatObjects F).ι` and `(kFlatComplexes F).ι ⋙ quotient` are the same
functor; what differs is the `CategoryTheory.Functor.CommShift` datum instance search finds for
each, and that is precisely what `kFlatQuotientCompι_commShift` crosses.  So those two factors are
invisible in `comparisonSecond_hom_app` and indispensable in `comparisonSecond_commShift`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization

noncomputable section

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- `Tot(F(-, -))` on cochain complexes, the bifunctor `comparison` lands in. -/
abbrev totalBifunctor :
    CochainComplex A ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex D ℤ :=
  F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The lifting isomorphism of the homotopy-category descent, named so that the chains below and
`CochainComplex.KFlatBifunctor.comparison` refer to the same term. -/
abbrev homotopyComparisonIso :=
  Localization.Lifting₂.iso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F)

/-! ### The four components of the two lifting isomorphisms, respelled -/

/-- **The derived descent's lifting isomorphism at a left K-flat object of `K(A)`**, with its
source and target spelled as composites rather than through
`CategoryTheory.Functor.whiskeringLeft₂`. -/
def derivedComparisonObj (M : (kFlatObjectsLeft F).FullSubcategory) :
    kFlatQ F ⋙ (derivedBifunctor F).obj (DerivedCategory.Qh.obj M.obj) ≅
      (kFlatObjects F).ι ⋙ ((homotopyBifunctor F).obj M.obj ⋙ DerivedCategory.Qh) :=
  (derivedBifunctorComparisonIso F).app M

/-- `derivedComparisonObj` is shift-compatible: this is the `commShift_app` field of
`derivedBifunctorComparisonIso_commShift₂`, which at the respelled type no longer needs its
source's datum seated by hand. -/
theorem derivedComparisonObj_commShift (M : (kFlatObjectsLeft F).FullSubcategory) :
    NatTrans.CommShift (derivedComparisonObj F M).hom ℤ :=
  (derivedBifunctorComparisonIso_commShift₂ F).commShift_app M

/-- The mirror of `derivedComparisonObj` in the first variable. -/
def derivedComparisonFlipObj (N : (kFlatObjects F).FullSubcategory) :
    kFlatQLeft F ⋙ (derivedBifunctor F).flip.obj (DerivedCategory.Qh.obj N.obj) ≅
      (kFlatObjectsLeft F).ι ⋙
        ((homotopyBifunctor F).flip.obj N.obj ⋙ DerivedCategory.Qh) :=
  ((flipFunctor _ _ _).mapIso (derivedBifunctorComparisonIso F)).app N

/-- The mirror of `derivedComparisonObj_commShift`, from the `commShift_flipApp` field. -/
theorem derivedComparisonFlipObj_commShift (N : (kFlatObjects F).FullSubcategory) :
    NatTrans.CommShift (derivedComparisonFlipObj F N).hom ℤ :=
  (derivedBifunctorComparisonIso_commShift₂ F).commShift_flipApp N

/-- **The homotopy descent's lifting isomorphism at a cochain complex of `A`**, respelled. -/
def homotopyComparisonObj (K : CochainComplex A ℤ) :
    HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙
        (homotopyBifunctor F).obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≅
      (totalBifunctor F).obj K ⋙ HomotopyCategory.quotient D (ComplexShape.up ℤ) :=
  (homotopyComparisonIso F).app K

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- `homotopyComparisonObj` is shift-compatible, from the `commShift_app` field of
`homotopyBifunctorComparisonIso_commShift₂`. -/
theorem homotopyComparisonObj_commShift (K : CochainComplex A ℤ) :
    NatTrans.CommShift (homotopyComparisonObj F K).hom ℤ :=
  (homotopyBifunctorComparisonIso_commShift₂ F).commShift_app K

/-- The mirror of `homotopyComparisonObj` in the first variable. -/
def homotopyComparisonFlipObj (L : CochainComplex B ℤ) :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (homotopyBifunctor F).flip.obj
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) ≅
      (totalBifunctor F).flip.obj L ⋙ HomotopyCategory.quotient D (ComplexShape.up ℤ) :=
  ((flipFunctor _ _ _).mapIso (homotopyComparisonIso F)).app L

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- The mirror of `homotopyComparisonObj_commShift`, from the `commShift_flipApp` field. -/
theorem homotopyComparisonFlipObj_commShift (L : CochainComplex B ℤ) :
    NatTrans.CommShift (homotopyComparisonFlipObj F L).hom ℤ :=
  (homotopyBifunctorComparisonIso_commShift₂ F).commShift_flipApp L

/-! ### The comparison at a fixed left K-flat first factor -/

section Second

variable (K : CochainComplex A ℤ)

/-- The last two factors of `comparison`, as an isomorphism of functors of the second variable:
the homotopy descent's lifting isomorphism at `K`, followed by the `Q` versus `Qh ∘ quotient`
bridge on the total complex. -/
def comparisonSecondHomotopy :
    HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙
        ((homotopyBifunctor F).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
          DerivedCategory.Qh) ≅
      (totalBifunctor F).obj K ⋙ DerivedCategory.Q :=
  (Functor.associator (HomotopyCategory.quotient B (ComplexShape.up ℤ))
      ((homotopyBifunctor F).obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerRight (homotopyComparisonObj F K) DerivedCategory.Qh ≪≫
      Functor.associator ((totalBifunctor F).obj K)
          (HomotopyCategory.quotient D (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft ((totalBifunctor F).obj K) (DerivedCategory.quotientCompQhIso D)

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- `comparisonSecondHomotopy` is shift-compatible. -/
theorem comparisonSecondHomotopy_commShift :
    NatTrans.CommShift (comparisonSecondHomotopy F K).hom ℤ := by
  let := homotopyComparisonObj_commShift F K
  unfold comparisonSecondHomotopy
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

variable (hK : KFlatLeft F K)

/-- **The comparison of [Stacks, Tag 06YU] at a fixed left K-flat first factor**, as an
isomorphism of functors on the K-flat complexes: the five factors of
`CochainComplex.KFlatBifunctor.comparison` read as transformations in the second variable, with
every junction written out. -/
def comparisonSecond :
    kFlatComplexQ F ⋙ (derivedBifunctor F).obj (DerivedCategory.Q.obj K) ≅
      (kFlatComplexes F).ι ⋙ ((totalBifunctor F).obj K ⋙ DerivedCategory.Q) :=
  Functor.isoWhiskerLeft (kFlatComplexQ F)
      ((derivedBifunctor F).mapIso ((DerivedCategory.quotientCompQhIso A).app K).symm) ≪≫
    Functor.isoWhiskerRight (kFlatQuotientCompQIso F).symm
        ((derivedBifunctor F).obj (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) ≪≫
      Functor.associator (kFlatQuotient F) (kFlatQ F)
          ((derivedBifunctor F).obj (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) ≪≫
        Functor.isoWhiskerLeft (kFlatQuotient F) (derivedComparisonObj F
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩) ≪≫
          (Functor.associator (kFlatQuotient F) (kFlatObjects F).ι
              ((homotopyBifunctor F).obj
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
                DerivedCategory.Qh)).symm ≪≫
            Functor.isoWhiskerRight ((kFlatObjects F).liftCompιIso
                ((kFlatComplexes F).ι ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ))
                (fun L ↦ L.2))
                ((homotopyBifunctor F).obj
                    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
                  DerivedCategory.Qh) ≪≫
              Functor.associator (kFlatComplexes F).ι
                  (HomotopyCategory.quotient B (ComplexShape.up ℤ))
                  ((homotopyBifunctor F).obj
                      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
                    DerivedCategory.Qh) ≪≫
                Functor.isoWhiskerLeft (kFlatComplexes F).ι (comparisonSecondHomotopy F K)

/-- **`comparisonSecond` is the comparison of [Stacks, Tag 06YU]**: the three associators and the
lift comparison are the identity on every object, so what is left is the five factors of
`CochainComplex.KFlatBifunctor.comparison`. -/
theorem comparisonSecond_hom_app (L : (kFlatComplexes F).FullSubcategory) :
    (comparisonSecond F K hK).hom.app L = (comparison F K L.1 hK L.2).hom := by
  have h : ((kFlatObjects F).liftCompιIso
      ((kFlatComplexes F).ι ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (fun L ↦ L.2)).hom.app L = 𝟙 _ := rfl
  simp [comparisonSecond, comparisonSecondHomotopy, comparison, kFlatQuotientCompQIso,
    derivedComparisonObj, homotopyComparisonObj, h]
  rfl

/-- **The comparison of [Stacks, Tag 06YU] at a fixed left K-flat first factor is compatible with
the shift in the second variable.**  Every factor of `comparisonSecond` is: the three associators
by `CategoryTheory.NatTrans.CommShift.associator`, the bridge by
`kFlatQuotientCompQIso_commShift`, the lift comparison by `kFlatQuotientCompι_commShift`, the two
lifting isomorphisms by `derivedComparisonObj_commShift` and `homotopyComparisonObj_commShift`,
and the two remaining whiskerings by the `commShift_map` field of the
`CategoryTheory.Functor.CommShift₂` of `derivedBifunctor F` and by Mathlib's
`DerivedCategory.quotientCompQhIso`. -/
theorem comparisonSecond_commShift :
    NatTrans.CommShift (comparisonSecond F K hK).hom ℤ := by
  let := kFlatQuotient_commShift F
  let := kFlatQuotientCompι_commShift F
  let := kFlatQuotientCompQIso_commShift F
  let := derivedComparisonObj_commShift F
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
  let := comparisonSecondHomotopy_commShift F K
  unfold comparisonSecond
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  infer_instance

end Second

/-! ### The comparison at a fixed K-flat second factor -/

section First

variable (L : CochainComplex B ℤ)

/-- The last two factors of `comparison`, as an isomorphism of functors of the first variable. -/
def comparisonFirstHomotopy :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        ((homotopyBifunctor F).flip.obj
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) ⋙
          DerivedCategory.Qh) ≅
      (totalBifunctor F).flip.obj L ⋙ DerivedCategory.Q :=
  (Functor.associator (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      ((homotopyBifunctor F).flip.obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerRight (homotopyComparisonFlipObj F L) DerivedCategory.Qh ≪≫
      Functor.associator ((totalBifunctor F).flip.obj L)
          (HomotopyCategory.quotient D (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft ((totalBifunctor F).flip.obj L)
          (DerivedCategory.quotientCompQhIso D)

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- `comparisonFirstHomotopy` is shift-compatible. -/
theorem comparisonFirstHomotopy_commShift :
    NatTrans.CommShift (comparisonFirstHomotopy F L).hom ℤ := by
  let := homotopyComparisonFlipObj_commShift F L
  unfold comparisonFirstHomotopy
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

variable (hL : KFlat F L)

/-- **The comparison of [Stacks, Tag 06YU] at a fixed K-flat second factor**, as an isomorphism of
functors on the left K-flat complexes: the mirror of `comparisonSecond`. -/
def comparisonFirst :
    kFlatComplexQLeft F ⋙ (derivedBifunctor F).flip.obj (DerivedCategory.Q.obj L) ≅
      (kFlatComplexesLeft F).ι ⋙ ((totalBifunctor F).flip.obj L ⋙ DerivedCategory.Q) :=
  Functor.isoWhiskerRight (kFlatQuotientCompQIsoLeft F).symm
      ((derivedBifunctor F).flip.obj (DerivedCategory.Q.obj L)) ≪≫
    Functor.associator (kFlatQuotientLeft F) (kFlatQLeft F)
        ((derivedBifunctor F).flip.obj (DerivedCategory.Q.obj L)) ≪≫
      Functor.isoWhiskerLeft (kFlatQuotientLeft F)
          (Functor.isoWhiskerLeft (kFlatQLeft F) ((derivedBifunctor F).flip.mapIso
            ((DerivedCategory.quotientCompQhIso B).app L).symm)) ≪≫
        Functor.isoWhiskerLeft (kFlatQuotientLeft F) (derivedComparisonFlipObj F
            ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩) ≪≫
          (Functor.associator (kFlatQuotientLeft F) (kFlatObjectsLeft F).ι
              ((homotopyBifunctor F).flip.obj
                  ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) ⋙
                DerivedCategory.Qh)).symm ≪≫
            Functor.isoWhiskerRight ((kFlatObjectsLeft F).liftCompιIso
                ((kFlatComplexesLeft F).ι ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ))
                (fun K ↦ K.2))
                ((homotopyBifunctor F).flip.obj
                    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) ⋙
                  DerivedCategory.Qh) ≪≫
              Functor.associator (kFlatComplexesLeft F).ι
                  (HomotopyCategory.quotient A (ComplexShape.up ℤ))
                  ((homotopyBifunctor F).flip.obj
                      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) ⋙
                    DerivedCategory.Qh) ≪≫
                Functor.isoWhiskerLeft (kFlatComplexesLeft F).ι (comparisonFirstHomotopy F L)

/-- **`comparisonFirst` is the comparison of [Stacks, Tag 06YU]**, the mirror of
`comparisonSecond_hom_app`. -/
theorem comparisonFirst_hom_app (K : (kFlatComplexesLeft F).FullSubcategory) :
    (comparisonFirst F L hL).hom.app K = (comparison F K.1 L K.2 hL).hom := by
  have h : ((kFlatObjectsLeft F).liftCompιIso
      ((kFlatComplexesLeft F).ι ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (fun K ↦ K.2)).hom.app K = 𝟙 _ := rfl
  simp [comparisonFirst, comparisonFirstHomotopy, comparison, kFlatQuotientCompQIsoLeft,
    derivedComparisonFlipObj, homotopyComparisonFlipObj, h]
  rfl

/-- **The comparison of [Stacks, Tag 06YU] at a fixed K-flat second factor is compatible with the
shift in the first variable**, the mirror of `comparisonSecond_commShift`. -/
theorem comparisonFirst_commShift :
    NatTrans.CommShift (comparisonFirst F L hL).hom ℤ := by
  let := kFlatQuotientLeft_commShift F
  let := kFlatQuotientCompιLeft_commShift F
  let := kFlatQuotientCompQIsoLeft_commShift F
  let := derivedComparisonFlipObj_commShift F
    ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩
  let := comparisonFirstHomotopy_commShift F L
  unfold comparisonFirst
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  infer_instance

end First

end CochainComplex.KFlatBifunctor

end

end
