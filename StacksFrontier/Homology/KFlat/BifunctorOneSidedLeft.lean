module

public import StacksFrontier.Homology.KFlat.BifunctorOneSided
import StacksCore.Tactic.StacksAttribute

/-!
# One-sided K-flat comparison in the left variable

For an additive bifunctor `F : A ⥤ B ⥤ D` whose derived descent
`CochainComplex.KFlatBifunctor.derivedBifunctor` exists, the two-sided comparison
`CochainComplex.KFlatBifunctor.comparison` identifies the descent with the total complex
`Tot(F(K, L))` when `K` is left K-flat *and* `L` is K-flat. `Tag06YUOneSided` drops the
left-hand hypothesis; this file drops the right-hand one, so that a left K-flat `K` computes
the descent against an arbitrary `L`.

## Main definitions

* `CochainComplex.KFlatBifunctor.derivedToDerivedLeft`: the descent of `Tot(F(K, -))` to
  `D(B)`, uniformly in the left K-flat object `K`, as a functor valued in the functor
  category over the left K-flat objects of `K(A)`.
* `CochainComplex.KFlatBifunctor.derivedBifunctorLeftIso`: the identification of
  `derivedBifunctor` with that descent, as an isomorphism of functors on `D(B)`.
* `CochainComplex.KFlatBifunctor.comparisonLeft`: **a left K-flat left factor computes the
  derived bifunctor against an arbitrary right factor**, the one-sided comparison.

## Main results

* `CochainComplex.KFlatBifunctor.comparisonLeft_naturality_right`: `comparisonLeft` is
  natural in the arbitrary right complex, with no K-flatness assumed there.
* `CochainComplex.KFlatBifunctor.comparisonLeft_naturality_left`: and in the left K-flat
  left complex.
* `CochainComplex.KFlatBifunctor.comparisonLeft_naturality`: hence in both variables at
  once, the right-hand map being the total complex of the pair written as the composite of
  its two one-variable halves, in the same spelling as `comparisonRight_naturality`.

## Implementation notes

This is the mirror of `Tag06YUOneSided` across the two variables of `F`, and it is a mirror
rather than a transport along `F.flip`: flipping would replace `Tot(F(K, L))` by
`Tot(F.flip(L, K))` and owe the Koszul-sign reconciliation of
`HomologicalComplex.mapBifunctorFlipIso` in every statement. `Tag06YUPieces` already builds
both sides of the K-flat engine — `kFlatObjectsLeft`, `kFlatQLeft` and the preservation
lemma `isIso_Qh_map_homotopyBifunctor_obj_map` — precisely so that the mirror needs no
symmetry of `F` at all, and none is used here.

The one place a flip does appear is `derivedBifunctorComparisonIsoFlip`, which is the
`Lifting₂` isomorphism of `derivedBifunctor` read with its two localizations exchanged. That
is `Localization.Lifting₂.flip`, an instance, so the exchange is supplied by the localization
API rather than built; it transports no total complex and therefore carries no sign.

As in `Tag06YUOneSided` the left K-flat factor is kept inside the target functor category
instead of being fixed one object at a time, so that naturality in both variables is a
projection of a single isomorphism of functors rather than a diagram chase, and
`Localization.fullyFaithfulWhiskeringLeft` *produces* that isomorphism from its restriction
to the K-flat objects. No transparency guard is needed anywhere, and none is used.

The three naturality squares are stated with their two sides written out and closed by the
naturality term itself rather than by `simp`-normalizing the `Lifting₂` composite: a
`NatTrans.congr_app` of a composite leaves `(α ≫ β).app Z` undistributed, which the
subsequent `rw` then fails to match, whereas a term-mode assignment checks the two spellings
at default transparency.

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

/-! ### A left K-flat left factor, uniformly in that factor -/

/-- `Tot(F(-, -))` with the first variable restricted to the left K-flat objects of `K(A)`
and the second left as the whole homotopy category `K(B)`, landing in `D(D)`. Restricting
the second variable along the inclusion of the K-flat objects recovers the flip of
`kFlatToDerived`. -/
abbrev homotopyToDerivedLeft :
    HomotopyCategory B (ComplexShape.up ℤ) ⥤
      (kFlatObjectsLeft F).FullSubcategory ⥤ DerivedCategory D :=
  ((homotopyBifunctor F).flip ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Qh (C := D))) ⋙
    (Functor.whiskeringLeft _ _ _).obj (kFlatObjectsLeft F).ι

/-- The same bifunctor read on cochain complexes of `B`, which is what the descent to
`D(B)` localizes. -/
abbrev totalToDerivedLeft :
    CochainComplex B ℤ ⥤ (kFlatObjectsLeft F).FullSubcategory ⥤ DerivedCategory D :=
  HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ homotopyToDerivedLeft F

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- **`Tot(F(-, -))` inverts quasi-isomorphisms of the second variable, uniformly over left
K-flat first arguments.** A natural transformation of functors is an isomorphism exactly
when each component is, and each component is
`isIso_Qh_map_homotopyBifunctor_obj_map`. This is the hypothesis `Localization.lift`
consumes in the functor category. -/
theorem totalToDerivedLeft_inverts :
    (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)).IsInvertedBy
      (totalToDerivedLeft F) := by
  intro L L' g hg
  let _ : ∀ Z, IsIso (((totalToDerivedLeft F).map g).app Z) := fun Z ↦
    isIso_Qh_map_homotopyBifunctor_obj_map F Z.1 Z.2
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g)
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff g).2 hg)
  exact NatIso.isIso_of_isIso_app _

/-- The descent of `Tot(F(-, -))` to `D(B)` in the second variable, uniformly over left
K-flat first arguments. -/
def derivedToDerivedLeft :
    DerivedCategory B ⥤ (kFlatObjectsLeft F).FullSubcategory ⥤ DerivedCategory D :=
  CategoryTheory.Localization.lift (totalToDerivedLeft F)
    (totalToDerivedLeft_inverts F) (DerivedCategory.Q (C := B))

/-- The descent agrees with `Tot(F(-, -))` on complexes. -/
def derivedToDerivedLeftFac :
    DerivedCategory.Q (C := B) ⋙ derivedToDerivedLeft F ≅ totalToDerivedLeft F :=
  CategoryTheory.Localization.fac (totalToDerivedLeft F)
    (totalToDerivedLeft_inverts F) (DerivedCategory.Q (C := B))

/-- The descent agrees with the homotopy-level descent on `K(B)`. The homotopy quotient is
a localization at the homotopy equivalences, so this is the `preimageIso` of the `Q` versus
`Qh ∘ quotient` bridge and nothing more. -/
def homotopyToDerivedLeftIso :
    DerivedCategory.Qh (C := B) ⋙ derivedToDerivedLeft F ≅ homotopyToDerivedLeft F :=
  (CategoryTheory.Localization.fullyFaithfulWhiskeringLeft
      (HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
      ((kFlatObjectsLeft F).FullSubcategory ⥤ DerivedCategory D)).preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B)
        (derivedToDerivedLeft F) ≪≫
      derivedToDerivedLeftFac F)


section Comparison
variable [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- `derivedBifunctor` with its variables exchanged and the first one restricted to the
left K-flat objects of `K(A)`, so that it is comparable with `derivedToDerivedLeft`. -/
abbrev derivedBifunctorLeft :
    DerivedCategory B ⥤ (kFlatObjectsLeft F).FullSubcategory ⥤ DerivedCategory D :=
  (derivedBifunctor F).flip ⋙ (Functor.whiskeringLeft _ _ _).obj (kFlatQLeft F)

/-- The `Lifting₂` isomorphism of `derivedBifunctor` with its two localizations exchanged.
`Localization.Lifting₂.flip` is an instance, so this is supplied by the localization API;
it transports no total complex and so introduces no Koszul sign. -/
def derivedBifunctorComparisonIsoFlip :=
  CategoryTheory.Localization.Lifting₂.iso (kFlatQ F) (kFlatQLeft F)
    (kFlatQuasiIso F) (kFlatQuasiIsoLeft F) ((kFlatToDerived F).flip)
    ((derivedBifunctor F).flip)

/-- **The derived bifunctor is the descent of `Tot(F(-, -))` in the second variable
alone**, uniformly over left K-flat first arguments. Both sides restrict, along the
localization `kFlatQ`, to the two-sided comparison, and precomposition with a localization
functor is fully faithful on functor categories; so the isomorphism is the `preimageIso` of
the flipped `derivedBifunctorComparisonIso`, with no flatness hypothesis surviving on the
second variable. -/
def derivedBifunctorLeftIso :
    derivedBifunctorLeft F ≅ derivedToDerivedLeft F :=
  (CategoryTheory.Localization.fullyFaithfulWhiskeringLeft (kFlatQ F) (kFlatQuasiIso F)
      ((kFlatObjectsLeft F).FullSubcategory ⥤ DerivedCategory D)).preimageIso
    (derivedBifunctorComparisonIsoFlip F ≪≫
      (Functor.isoWhiskerLeft (kFlatObjects F).ι (homotopyToDerivedLeftIso F)).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- **A left K-flat left factor computes the derived bifunctor against an arbitrary right
factor.** This is the `comparisonLeft` field of the ringed-site statement of Tag 06YU: the
two-sided `comparison` with its right-hand K-flatness hypothesis dropped. -/
def comparisonLeft (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) (hK : KFlatLeft F K) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (totalComplex F K L) :=
  ((derivedBifunctor F).mapIso ((DerivedCategory.quotientCompQhIso A).app K).symm).app
      (DerivedCategory.Q.obj L) ≪≫
    ((derivedBifunctorLeftIso F).app (DerivedCategory.Q.obj L)).app
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ ≪≫
    ((derivedToDerivedLeftFac F).app L).app
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ ≪≫
    totalComplexQhIso F K L


/-- **The derived bifunctor read on cochain complexes of `B` is the total complex**,
uniformly over left K-flat first arguments: the two middle factors of `comparisonLeft`
bundled into one isomorphism of functors on `CochainComplex B ℤ`. Naturality of
`comparisonLeft` in either variable is a projection of this. -/
def comparisonLeftFac :
    DerivedCategory.Q (C := B) ⋙ derivedBifunctorLeft F ≅ totalToDerivedLeft F :=
  Functor.isoWhiskerLeft (DerivedCategory.Q (C := B)) (derivedBifunctorLeftIso F) ≪≫
    derivedToDerivedLeftFac F

/-- The three factors of `comparisonLeft`, in the one spelling the naturality squares are
stated in. -/
theorem comparisonLeft_hom (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : KFlatLeft F K) :
    (comparisonLeft F K L hK).hom =
      ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).inv.app K)).app
          (DerivedCategory.Q.obj L) ≫
        ((comparisonLeftFac F).hom.app L).app
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ ≫
        (totalComplexQhIso F K L).hom := by
  simp only [comparisonLeft, comparisonLeftFac, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]

/-- Three commuting squares side by side give the commuting rectangle of their composites. -/
private theorem comp_eq_comp_of_three_squares {C : Type*} [Category C]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : C} {x : X₁ ⟶ X₂} {a : X₁ ⟶ Y₁} {a' : X₂ ⟶ Y₂} {m : Y₁ ⟶ Y₂}
    {b : Y₁ ⟶ Z₁} {b' : Y₂ ⟶ Z₂} {n : Z₁ ⟶ Z₂} {c : Z₁ ⟶ W₁} {c' : Z₂ ⟶ W₂} {y : W₁ ⟶ W₂}
    (hA : x ≫ a' = a ≫ m) (hB : m ≫ b' = b ≫ n) (hC : n ≫ c' = c ≫ y) :
    x ≫ a' ≫ b' ≫ c' = (a ≫ b ≫ c) ≫ y := by
  simp only [Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hB, hC]

/-- **Naturality of `comparisonLeft` in the arbitrary right complex.** The three squares
are: the `Q` versus `Qh ∘ quotient` bridge in the left-hand variable, which is natural;
`comparisonLeftFac`, which is itself a natural transformation of functors on
`CochainComplex B ℤ`; and `totalComplexQhIso_naturality_right`. No K-flatness is assumed on
either `L` or `L'`. -/
theorem comparisonLeft_naturality_right
    (K : CochainComplex A ℤ) {L L' : CochainComplex B ℤ} (g : L ⟶ L')
    (hK : KFlatLeft F K) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        (comparisonLeft F K L' hK).hom =
      (comparisonLeft F K L hK).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K).map g) := by
  have hA := ((derivedBifunctor F).map
    ((DerivedCategory.quotientCompQhIso A).inv.app K)).naturality (DerivedCategory.Q.map g)
  have hB : ((derivedBifunctor F).obj
          ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          (DerivedCategory.Q.map g) ≫
        ((comparisonLeftFac F).hom.app L').app
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ =
      ((comparisonLeftFac F).hom.app L).app
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ ≫
        (DerivedCategory.Qh (C := D)).map
          (((homotopyBifunctor F).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).map
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g)) :=
    NatTrans.congr_app ((comparisonLeftFac F).hom.naturality g)
      (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ :
        (kFlatObjectsLeft F).FullSubcategory)
  have hC := totalComplexQhIso_naturality_right F K g
  rw [comparisonLeft_hom, comparisonLeft_hom]
  exact comp_eq_comp_of_three_squares hA hB hC

/-- **Naturality of `comparisonLeft` in the left K-flat left complex.** Here the three
squares are: the `Q` versus `Qh ∘ quotient` bridge, natural by
`DerivedCategory.quotientCompQhIso_inv_naturality`; the component of `comparisonLeftFac` at
`L`, which is a natural transformation of functors on the left K-flat objects of `K(A)`, so
this square is exactly its naturality at the morphism induced by `f`; and
`totalComplexQhIso_naturality_left`. -/
theorem comparisonLeft_naturality_left
    {K K' : CochainComplex A ℤ} (f : K ⟶ K') (L : CochainComplex B ℤ)
    (hK : KFlatLeft F K) (hK' : KFlatLeft F K') :
    ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (comparisonLeft F K' L hK').hom =
      (comparisonLeft F K L hK).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app L) := by
  have hA : ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).map
          ((DerivedCategory.quotientCompQhIso A).inv.app K')).app
          (DerivedCategory.Q.obj L) =
      ((derivedBifunctor F).map
          ((DerivedCategory.quotientCompQhIso A).inv.app K)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).map
          ((DerivedCategory.Qh (C := A)).map
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))).app
          (DerivedCategory.Q.obj L) := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun t ↦ ((derivedBifunctor F).map t).app (DerivedCategory.Q.obj L))
      (DerivedCategory.quotientCompQhIso_inv_naturality f)
  have hB : ((derivedBifunctor F).map
          ((DerivedCategory.Qh (C := A)).map
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))).app
          (DerivedCategory.Q.obj L) ≫
        ((comparisonLeftFac F).hom.app L).app
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K', hK'⟩ =
      ((comparisonLeftFac F).hom.app L).app
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ ≫
        (DerivedCategory.Qh (C := D)).map
          (((homotopyBifunctor F).map
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)).app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) :=
    ((comparisonLeftFac F).hom.app L).naturality
      (ObjectProperty.homMk ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) :
        (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ :
            (kFlatObjectsLeft F).FullSubcategory) ⟶
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K', hK'⟩)
  have hC := totalComplexQhIso_naturality_left F f L
  rw [comparisonLeft_hom, comparisonLeft_hom]
  exact comp_eq_comp_of_three_squares hA hB hC

/-- **`comparisonLeft` is natural in both variables at once**: the composite of the two
one-variable squares. The right-hand map is the total complex of `f` and `g` written as the
composite of the two one-variable maps, the same spelling as in
`comparisonRight_naturality`. -/
theorem comparisonLeft_naturality
    {K K' : CochainComplex A ℤ} {L L' : CochainComplex B ℤ} (f : K ⟶ K') (g : L ⟶ L')
    (hK : KFlatLeft F K) (hK' : KFlatLeft F K') :
    ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫
        (comparisonLeft F K' L' hK').hom =
      (comparisonLeft F K L hK).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).map f).app L ≫
            ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).obj K').map g) := by
  rw [comparisonLeft_naturality_right F K' g hK', ← Category.assoc,
    comparisonLeft_naturality_left F f L hK hK', Category.assoc, ← Functor.map_comp]

end Comparison

end
end CochainComplex.KFlatBifunctor
end

end
