module

public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.Homology.TotalComplexTransport
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Transporting a derived bifunctor along an exact functor

Let `F : A ⥤ B ⥤ D` and `F' : A' ⥤ B' ⥤ D'` be additive bifunctors between abelian
categories, each admitting K-flat resolutions in both variables, so that each descends to a
bifunctor `derivedBifunctor` on the unbounded derived categories — the derived tensor product,
when `F` is a tensor product. Let `G₁ : A ⥤ A'`, `G₂ : B ⥤ B'` and `G₃ : D ⥤ D'` be exact
functors, and suppose that `G₃` carries `F` to `F'` along `G₁` and `G₂`, i.e. that there are
isomorphisms `G₃(F(a, b)) ≅ F'(G₁ a, G₂ b)` natural in `a` and in `b`. If moreover `G₃`
preserves the antidiagonal coproducts occurring in a total complex and `G₁`, `G₂` carry (left)
K-flat complexes to (left) K-flat complexes, then

  `G₃(F^L(K, L)) ≅ F'^L(G₁ K, G₂ L)`

as an isomorphism of **bifunctors on the derived categories**: on arbitrary objects `K` and
`L`, and natural in both of them.

This extends the comparisons on K-flat representatives
(`Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat`,
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`) to arbitrary objects of the
derived categories, naturally in homotopy classes of maps.

## Main definitions

* `CochainComplex.KFlatBifunctor.transportNatIso`: the comparison at the level of cochain
  complexes, `G₃(Tot(F(-, -))) ≅ Tot(F'(G₁ -, G₂ -))`, as an isomorphism of bifunctors.
* `CochainComplex.KFlatBifunctor.homotopyTransportIso`: the same on the **homotopy
  categories**, hence natural in homotopy classes of maps.
* `CochainComplex.KFlatBifunctor.derivedTransportIso`: **the comparison on the derived
  categories**, on arbitrary objects and natural in both variables.

## Implementation notes

The descent is done in two steps, each an application of `CategoryTheory.Localization.
lift₂NatIso`, and each with its two `Localization.Lifting₂` data supplied as the identity: the
bifunctor being lifted is in both cases taken to *be* the restriction of the one being
constructed, so that the whole content of the step is the isomorphism of the restrictions and
`lift₂NatIso` does the extension.

* The first step is along the two homotopy quotients, which are localizations at the homotopy
  equivalences. Its input is `transportNatIso`, whose two naturality squares are
  `CategoryTheory.Functor.mapBifunctorTotalIso_hom_naturality`.
* The second is along `kFlatQLeft` and `kFlatQ`, the two K-flat localizations of
  `StacksFrontier.Homology.KFlat.BifunctorLocalization`, which is where the K-flatness hypotheses
  on `G₁` and `G₂` enter: they are what makes `G₁` and `G₂` act on the K-flat subcategories at
  all, as `kFlatMapLeft` and `kFlatMapRight`.

Apart from `transportNatIso` itself — two squares, discharged from the one naturality lemma of
`StacksFrontier.Homology.TotalComplexTransport` — **no naturality square is checked by hand**.
Every other constituent is assembled by `Functor.isoWhiskerLeft`, `Functor.isoWhiskerRight` and
`Functor.mapIso` out of isomorphisms of functors, which carry their naturality with them. The
chains rely on associativity of functor composition and on
`(X ⋙ whiskeringRight.obj v) ⋙ whiskeringRight.obj w = X ⋙ whiskeringRight.obj (v ⋙ w)`
and its `whiskeringLeft` analogue holding by definitional equality, so no `eqToIso` occurs.

`ε` is taken as a family of isomorphisms with its two naturality squares rather than as a
natural isomorphism of curried functors, following
`CategoryTheory.Functor.mapBifunctorTotalIso`, whose implementation notes record the reason: a
caller has the isomorphism degreewise.

## References

* [Stacks Project, Lemma 20.26.4 (Tag 079U)](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Lemma 17.16.1 (Tag 01CB)](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

universe v v' u u'

variable {A B D A' B' D' : Type*}
  [Category A] [Category B] [Category D] [Category A'] [Category B'] [Category D']
  [Abelian A] [Abelian B] [Abelian D] [Abelian A'] [Abelian B'] [Abelian D']
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  (F' : A' ⥤ B' ⥤ D') [F'.Additive] [∀ X, (F'.obj X).Additive]
  [∀ (K₁ : CochainComplex A' ℤ) (K₂ : CochainComplex B' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)]
  (G₁ : A ⥤ A') (G₂ : B ⥤ B') (G₃ : D ⥤ D')
  [G₁.Additive] [G₂.Additive] [G₃.Additive]
  (ε : ∀ (a : A) (b : B), G₃.obj ((F.obj a).obj b) ≅ (F'.obj (G₁.obj a)).obj (G₂.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : B),
    G₃.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (G₁.map f)).app (G₂.obj b))
  (hε₂ : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
    G₃.map ((F.obj a).map g) ≫ (ε a b').hom =
      (ε a b).hom ≫ (F'.obj (G₁.obj a)).map (G₂.map g))
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) G₃]
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex G₃
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]

/-- The transport of the total complex of `F` along `G₃`:
`G₃(Tot(F(K, L))) ≅ Tot(F'(G₁ K, G₂ L))`. -/
abbrev transportComplexIso (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    (G₃.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K L F (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F' (ComplexShape.up ℤ) :=
  Functor.mapBifunctorTotalIso F F' G₁ G₂ G₃ ε (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) hε₁ hε₂ K L

/-- Naturality of `transportComplexIso` in the second complex. -/
lemma transportComplexIso_naturality_right (K : CochainComplex A ℤ)
    {L L' : CochainComplex B ℤ} (g : L ⟶ L') :
    (G₃.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapBifunctorMap (𝟙 K) g F (ComplexShape.up ℤ)) ≫
        (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K L').hom =
      (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K L).hom ≫
        HomologicalComplex.mapBifunctorMap
          (𝟙 ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
          ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).map g) F' (ComplexShape.up ℤ) := by
  have h := Functor.mapBifunctorTotalIso_hom_naturality F F' G₁ G₂ G₃ ε
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c := ComplexShape.up ℤ) hε₁ hε₂
    K K L L' (𝟙 K) g
  simpa only [CategoryTheory.Functor.map_id] using h

/-- Naturality of `transportComplexIso` in the first complex. -/
lemma transportComplexIso_naturality_left {K K' : CochainComplex A ℤ} (f : K ⟶ K')
    (L : CochainComplex B ℤ) :
    (G₃.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapBifunctorMap f (𝟙 L) F (ComplexShape.up ℤ)) ≫
        (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K' L).hom =
      (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K L).hom ≫
        HomologicalComplex.mapBifunctorMap
          ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          (𝟙 ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F'
          (ComplexShape.up ℤ) := by
  have h := Functor.mapBifunctorTotalIso_hom_naturality F F' G₁ G₂ G₃ ε
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c := ComplexShape.up ℤ) hε₁ hε₂
    K K' L L f (𝟙 L)
  simpa only [CategoryTheory.Functor.map_id] using h

/-- The complex-level transport, as a natural isomorphism of bifunctors on cochain
complexes: `G₃(Tot(F(-, -))) ≅ Tot(F'(G₁ -, G₂ -))`. -/
def transportNatIso :
    F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj (G₃.mapHomologicalComplex (ComplexShape.up ℤ)) ≅
      G₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F'.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringLeft _ _ _).obj (G₂.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun L => transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K L)
      (fun {L L'} g =>
        transportComplexIso_naturality_right F F' G₁ G₂ G₃ ε hε₁ hε₂ K g))
    (fun {K K'} f => by
      ext L : 2
      exact transportComplexIso_naturality_left F F' G₁ G₂ G₃ ε hε₁ hε₂ f L)

/-! ### The descent to the homotopy categories -/

section Homotopy

/-- `Tot(F(-, -))` followed by `G₃`, on the homotopy categories. -/
abbrev homotopyTransportSource :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ HomotopyCategory B (ComplexShape.up ℤ) ⥤
      HomotopyCategory D' (ComplexShape.up ℤ) :=
  homotopyBifunctor F ⋙ (Functor.whiskeringRight _ _ _).obj
    (G₃.mapHomotopyCategory (ComplexShape.up ℤ))

/-- `Tot(F'(G₁ -, G₂ -))` on the homotopy categories. -/
abbrev homotopyTransportTarget :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ HomotopyCategory B (ComplexShape.up ℤ) ⥤
      HomotopyCategory D' (ComplexShape.up ℤ) :=
  G₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ homotopyBifunctor F' ⋙
    (Functor.whiskeringLeft _ _ _).obj (G₂.mapHomotopyCategory (ComplexShape.up ℤ))

/-- Restriction of a bifunctor on the homotopy categories to cochain complexes. -/
abbrev restrictToComplexes
    (P : HomotopyCategory A (ComplexShape.up ℤ) ⥤ HomotopyCategory B (ComplexShape.up ℤ) ⥤
      HomotopyCategory D' (ComplexShape.up ℤ)) :
    CochainComplex A ℤ ⥤ CochainComplex B ℤ ⥤ HomotopyCategory D' (ComplexShape.up ℤ) :=
  (((Functor.whiskeringLeft₂ (HomotopyCategory D' (ComplexShape.up ℤ))).obj
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))).obj
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))).obj P

/-- The `Lifting₂` isomorphism of `homotopyBifunctor`: on complexes the descent of
`Tot(F(-, -))` to the homotopy categories is `Tot(F(-, -))`. -/
abbrev homotopyBifunctorLiftingIso :
    restrictToComplexes (D' := D) (homotopyBifunctor F) ≅ totalToHomotopy F :=
  CategoryTheory.Localization.Lifting₂.iso
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F)

/-- **The transport of `Tot(F(-, -))` along `G₃`, descended to the homotopy categories and
read back on complexes.** All six constituents are isomorphisms of functors, so no naturality
has to be checked by hand. -/
def homotopyTransportRestrIso :
    restrictToComplexes (homotopyTransportSource F G₃) ≅
      restrictToComplexes (homotopyTransportTarget F' G₁ G₂) :=
  Functor.isoWhiskerRight (homotopyBifunctorLiftingIso F)
      ((Functor.whiskeringRight _ _ _).obj (G₃.mapHomotopyCategory (ComplexShape.up ℤ))) ≪≫
    Functor.isoWhiskerLeft
      (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
      ((Functor.whiskeringRight (CochainComplex B ℤ) (CochainComplex D ℤ)
        (HomotopyCategory D' (ComplexShape.up ℤ))).mapIso
          (G₃.mapHomotopyCategoryFactors (ComplexShape.up ℤ))) ≪≫
    Functor.isoWhiskerRight (transportNatIso F F' G₁ G₂ G₃ ε hε₁ hε₂)
      ((Functor.whiskeringRight (CochainComplex B ℤ) (CochainComplex D' ℤ)
        (HomotopyCategory D' (ComplexShape.up ℤ))).obj
          (HomotopyCategory.quotient D' (ComplexShape.up ℤ))) ≪≫
    Functor.isoWhiskerLeft (G₁.mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (homotopyBifunctorLiftingIso F').symm
        ((Functor.whiskeringLeft (CochainComplex B ℤ) (CochainComplex B' ℤ)
          (HomotopyCategory D' (ComplexShape.up ℤ))).obj
            (G₂.mapHomologicalComplex (ComplexShape.up ℤ)))) ≪≫
    Functor.isoWhiskerLeft (G₁.mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.isoWhiskerLeft
        (HomotopyCategory.quotient A' (ComplexShape.up ℤ) ⋙ homotopyBifunctor F')
        ((Functor.whiskeringLeft (CochainComplex B ℤ) (HomotopyCategory B' (ComplexShape.up ℤ))
          (HomotopyCategory D' (ComplexShape.up ℤ))).mapIso
            (G₂.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm)) ≪≫
    Functor.isoWhiskerRight (G₁.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
      (homotopyBifunctor F' ⋙
        (Functor.whiskeringLeft (CochainComplex B ℤ) (HomotopyCategory B' (ComplexShape.up ℤ))
          (HomotopyCategory D' (ComplexShape.up ℤ))).obj
            (HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙
              G₂.mapHomotopyCategory (ComplexShape.up ℤ)))

/-- **The transport of the derived bifunctor's homotopy-category descent.** On the homotopy
categories, `G₃(Tot(F(-, -))) ≅ Tot(F'(G₁ -, G₂ -))`, now on arbitrary objects and natural in
homotopy classes of maps: the comparison on complexes is descended along the two homotopy
quotients, which are localizations at the homotopy equivalences. -/
def homotopyTransportIso :
    homotopyTransportSource F G₃ ≅ homotopyTransportTarget F' G₁ G₂ :=
  letI : CategoryTheory.Localization.Lifting₂
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
      (restrictToComplexes (homotopyTransportSource F G₃))
      (homotopyTransportSource F G₃) := ⟨Iso.refl _⟩
  letI : CategoryTheory.Localization.Lifting₂
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
      (restrictToComplexes (homotopyTransportTarget F' G₁ G₂))
      (homotopyTransportTarget F' G₁ G₂) := ⟨Iso.refl _⟩
  CategoryTheory.Localization.lift₂NatIso
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    _ _ _ _ (homotopyTransportRestrIso F F' G₁ G₂ G₃ ε hε₁ hε₂)

end Homotopy

/-! ### The descent to the derived categories -/

section Derived

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory D']
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]
  [(kFlatQLeft F').IsLocalization (kFlatQuasiIsoLeft F')]
  [(kFlatQ F').IsLocalization (kFlatQuasiIso F')]
  (hKFlatLeft : ∀ K : CochainComplex A ℤ, KFlatLeft F K →
    KFlatLeft F' ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hKFlat : ∀ L : CochainComplex B ℤ, KFlat F L →
    KFlat F' ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))

/-- `G₁` on the left K-flat objects of the homotopy categories. -/
abbrev kFlatMapLeft :
    (kFlatObjectsLeft F).FullSubcategory ⥤ (kFlatObjectsLeft F').FullSubcategory :=
  (kFlatObjectsLeft F').lift
    ((kFlatObjectsLeft F).ι ⋙ G₁.mapHomotopyCategory (ComplexShape.up ℤ))
    (fun X => hKFlatLeft X.1.as X.2)

/-- `G₂` on the K-flat objects of the homotopy categories. -/
abbrev kFlatMapRight :
    (kFlatObjects F).FullSubcategory ⥤ (kFlatObjects F').FullSubcategory :=
  (kFlatObjects F').lift
    ((kFlatObjects F).ι ⋙ G₂.mapHomotopyCategory (ComplexShape.up ℤ))
    (fun X => hKFlat X.1.as X.2)

/-- The left-hand square: `G₁` on the derived categories agrees with `G₁` on the left K-flat
objects. -/
abbrev kFlatSquareLeft :
    kFlatQLeft F ⋙ G₁.mapDerivedCategory ≅
      kFlatMapLeft F F' G₁ hKFlatLeft ⋙ kFlatQLeft F' :=
  Functor.isoWhiskerLeft (kFlatObjectsLeft F).ι
    (G₁.mapDerivedCategoryFactorsh)

/-- The right-hand square, for `G₂`. -/
abbrev kFlatSquareRight :
    kFlatQ F ⋙ G₂.mapDerivedCategory ≅ kFlatMapRight F F' G₂ hKFlat ⋙ kFlatQ F' :=
  Functor.isoWhiskerLeft (kFlatObjects F).ι
    (G₂.mapDerivedCategoryFactorsh)

/-- The derived bifunctor of `F`, followed by `G₃`. -/
abbrev derivedTransportSource :
    DerivedCategory A ⥤ DerivedCategory B ⥤ DerivedCategory D' :=
  derivedBifunctor F ⋙ (Functor.whiskeringRight _ _ _).obj G₃.mapDerivedCategory

/-- The derived bifunctor of `F'`, precomposed with `G₁` and `G₂`. -/
abbrev derivedTransportTarget :
    DerivedCategory A ⥤ DerivedCategory B ⥤ DerivedCategory D' :=
  G₁.mapDerivedCategory ⋙ derivedBifunctor F' ⋙
    (Functor.whiskeringLeft _ _ _).obj G₂.mapDerivedCategory

/-- Restriction of a bifunctor on the derived categories to the (left) K-flat objects. -/
abbrev restrictToKFlat
    (P : DerivedCategory A ⥤ DerivedCategory B ⥤ DerivedCategory D') :
    (kFlatObjectsLeft F).FullSubcategory ⥤ (kFlatObjects F).FullSubcategory ⥤
      DerivedCategory D' :=
  (((Functor.whiskeringLeft₂ (DerivedCategory D')).obj (kFlatQLeft F)).obj (kFlatQ F)).obj P

/-- **The comparison on (left) K-flat objects.** Every constituent is an isomorphism of
functors, so naturality is not checked by hand. -/
def derivedTransportRestrIso :
    restrictToKFlat F (derivedTransportSource F G₃) ≅
      restrictToKFlat F (derivedTransportTarget F' G₁ G₂) :=
  Functor.isoWhiskerRight (derivedBifunctorComparisonIso F)
      ((Functor.whiskeringRight _ _ _).obj G₃.mapDerivedCategory) ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategory D')).obj (kFlatObjectsLeft F).ι).obj
      (kFlatObjects F).ι).mapIso
        (Functor.isoWhiskerLeft (homotopyBifunctor F)
          ((Functor.whiskeringRight (HomotopyCategory B (ComplexShape.up ℤ))
            (HomotopyCategory D (ComplexShape.up ℤ)) (DerivedCategory D')).mapIso
              (G₃.mapDerivedCategoryFactorsh))) ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategory D')).obj (kFlatObjectsLeft F).ι).obj
      (kFlatObjects F).ι).mapIso
        (Functor.isoWhiskerRight (homotopyTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂)
          ((Functor.whiskeringRight (HomotopyCategory B (ComplexShape.up ℤ))
            (HomotopyCategory D' (ComplexShape.up ℤ)) (DerivedCategory D')).obj
              DerivedCategory.Qh)) ≪≫
    Functor.isoWhiskerLeft (kFlatMapLeft F F' G₁ hKFlatLeft)
      (Functor.isoWhiskerRight (derivedBifunctorComparisonIso F').symm
        ((Functor.whiskeringLeft ((kFlatObjects F).FullSubcategory)
          ((kFlatObjects F').FullSubcategory) (DerivedCategory D')).obj
            (kFlatMapRight F F' G₂ hKFlat))) ≪≫
    Functor.isoWhiskerLeft (kFlatMapLeft F F' G₁ hKFlatLeft)
      (Functor.isoWhiskerLeft (kFlatQLeft F' ⋙ derivedBifunctor F')
        ((Functor.whiskeringLeft ((kFlatObjects F).FullSubcategory)
          (DerivedCategory B') (DerivedCategory D')).mapIso
            (kFlatSquareRight F F' G₂ hKFlat).symm)) ≪≫
    Functor.isoWhiskerRight (kFlatSquareLeft F F' G₁ hKFlatLeft).symm
      (derivedBifunctor F' ⋙
        (Functor.whiskeringLeft ((kFlatObjects F).FullSubcategory)
          (DerivedCategory B') (DerivedCategory D')).obj
            (kFlatQ F ⋙ G₂.mapDerivedCategory))

/-- **The derived bifunctor transported along an exact functor.**

If `G₃` carries `F` to `F'` along `G₁` and `G₂`, preserves the antidiagonal coproducts of the
total complex, and `G₁`, `G₂` preserve (left) K-flatness, then

  `G₃(K ⊗^L_F L) ≅ (G₁ K) ⊗^L_{F'} (G₂ L)`

as an isomorphism of bifunctors on the derived categories: on *arbitrary* objects, and natural
in both variables. -/
def derivedTransportIso :
    derivedTransportSource F G₃ ≅ derivedTransportTarget F' G₁ G₂ :=
  letI : CategoryTheory.Localization.Lifting₂ (kFlatQLeft F) (kFlatQ F)
      (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
      (restrictToKFlat F (derivedTransportSource F G₃))
      (derivedTransportSource F G₃) := ⟨Iso.refl _⟩
  letI : CategoryTheory.Localization.Lifting₂ (kFlatQLeft F) (kFlatQ F)
      (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
      (restrictToKFlat F (derivedTransportTarget F' G₁ G₂))
      (derivedTransportTarget F' G₁ G₂) := ⟨Iso.refl _⟩
  CategoryTheory.Localization.lift₂NatIso (kFlatQLeft F) (kFlatQ F)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) _ _ _ _
    (derivedTransportRestrIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlatLeft hKFlat)

end Derived

end CochainComplex.KFlatBifunctor

end
