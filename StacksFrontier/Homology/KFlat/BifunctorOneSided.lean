module

public import StacksFrontier.Homology.KFlat.BifunctorLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# One-sided K-flat comparisons for a derived bifunctor

For an additive bifunctor `F : A ⥤ B ⥤ D` whose derived descent
`CochainComplex.KFlatBifunctor.derivedBifunctor` exists, the two-sided comparison
`CochainComplex.KFlatBifunctor.comparison` identifies the descent with the total complex
`Tot(F(K, L))` when `K` is left K-flat *and* `L` is K-flat. Only one of the two hypotheses
is needed: a K-flat `L` already computes the descent against an arbitrary `K`, and a left
K-flat `K` against an arbitrary `L`.

## Main definitions

* `CochainComplex.KFlatBifunctor.derivedToDerivedRight`: the descent of `Tot(F(-, L))` to
  `D(A)`, uniformly in the K-flat object `L`, as a functor valued in the functor category
  over the K-flat objects of `K(B)`.
* `CochainComplex.KFlatBifunctor.derivedBifunctorRightIso`: the identification of
  `derivedBifunctor` with that descent, as an isomorphism of functors on `D(A)`.
* `CochainComplex.KFlatBifunctor.comparisonRight`: **a K-flat right factor computes the
  derived bifunctor against an arbitrary left factor**, the one-sided comparison.

## Main results

* `CochainComplex.KFlatBifunctor.comparisonRight_naturality_left`: `comparisonRight` is
  natural in the arbitrary left complex, with no K-flatness assumed there.
* `CochainComplex.KFlatBifunctor.comparisonRight_naturality_right`: and in the K-flat right
  complex.
* `CochainComplex.KFlatBifunctor.comparisonRight_naturality`: hence in both variables at
  once, the right-hand map being the total complex of the pair written as the composite of
  its two one-variable halves.
* `CochainComplex.KFlatBifunctor.totalComplexQhIso_naturality_left` and
  `totalComplexQhIso_naturality_right`: the `Qh ∘ quotient` versus `Q` bridge for the total
  complex is natural in each variable, which is the tail square of each of the above.

## Implementation notes

The one-sided comparison is a *uniqueness-of-lifts* statement, not a new construction, and
the whole point of the shape chosen here is to make that visible. Both sides of
`derivedBifunctorRightIso` are functors `D(A) ⥤ ((K-flat objects of K(B)) ⥤ D(D))` — the
K-flat right factor is kept inside the target functor category rather than being fixed one
object at a time. That is what makes the comparison a single isomorphism of functors, from
which naturality in *both* variables is a projection instead of a diagram chase: naturality
in the arbitrary left complex is naturality of the isomorphism itself, and naturality in the
K-flat right complex is naturality of each of its components.

Fixing the K-flat factor first and comparing one-variable functors `D(A) ⥤ D(D)` would
produce the same objects and then owe a separate two-variable coherence argument, which is
precisely the cost this shape avoids. `Localization.lift` is applied in the functor category
for the same reason: `Tot(F(-, -))` inverts quasi-isomorphisms of the first variable
*componentwise* over K-flat second arguments, and a natural transformation of functors is an
isomorphism exactly when each component is, so the componentwise statement
`isIso_Qh_map_homotopyBifunctor_map_app` is already the hypothesis `Localization.lift`
consumes at the level of the functor category.

No transparency guard is needed anywhere, and none is used. The identification of the
descent with `derivedBifunctor` is obtained from
`Localization.fullyFaithfulWhiskeringLeft` — precomposition with a localization functor is
fully faithful on functor categories — so the isomorphism is *produced* by the localization
API from its restriction to the left K-flat objects, rather than being hand-built and then
reconciled with the two spellings of one object by relaxing `isDefEq`.

Three localizations are crossed, in this order: the homotopy quotient
`K ↦ K̄` at the homotopy equivalences of `A`, which turns the homotopy-level descent
`homotopyBifunctor` into a functor on `K(A)`; `Qh` at the quasi-isomorphisms, which is the
`Qh ∘ quotient` versus `Q` bridge `DerivedCategory.quotientCompQhIso`; and `kFlatQLeft` at
the quasi-isomorphisms between left K-flat objects, which is where the two-sided comparison
enters. Each is a single `preimageIso`.

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

/-- The homotopy-level `Lifting₂` isomorphism exhibiting `homotopyBifunctor` as the descent
of `Tot(F(-, -))`, named so that the naturality squares below can be stated in one
spelling. -/
abbrev homotopyBifunctorIso :=
  CategoryTheory.Localization.Lifting₂.iso
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F)

/-- The `Qh ∘ quotient` versus `Q` bridge for the total complex: the image in `D(D)` of the
homotopy-level descent at the homotopy classes of `K` and `L` is the image of `Tot(F(K, L))`
under `Q`. This is the tail of the two-sided `comparison`, and unlike the rest of that chain
it needs no flatness hypothesis on either complex. -/
def totalComplexQhIso (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    (DerivedCategory.Qh (C := D)).obj
        (((homotopyBifunctor F).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).obj
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) ≅
      DerivedCategory.Q.obj (totalComplex F K L) :=
  (DerivedCategory.Qh (C := D)).mapIso
      (((homotopyBifunctorIso F).app K).app L) ≪≫
    (DerivedCategory.quotientCompQhIso D).app (totalComplex F K L)

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The total-complex bridge intertwines the homotopy-level descent with `Tot(F(-, L))` in
the first variable. Both halves of the bridge are natural: the homotopy-level `Lifting₂`
isomorphism in its first variable, and `DerivedCategory.quotientCompQhIso`. -/
theorem totalComplexQhIso_naturality_left
    {K K' : CochainComplex A ℤ} (f : K ⟶ K') (L : CochainComplex B ℤ) :
    (DerivedCategory.Qh (C := D)).map
          (((homotopyBifunctor F).map
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)).app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) ≫
        (totalComplexQhIso F K' L).hom =
      (totalComplexQhIso F K L).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app L) := by
  have h : ((homotopyBifunctor F).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)).app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) ≫
      (((homotopyBifunctorIso F).hom.app K').app L) =
    (((homotopyBifunctorIso F).hom.app K).app L) ≫ ((totalToHomotopy F).map f).app L :=
    NatTrans.congr_app ((homotopyBifunctorIso F).hom.naturality f) L
  have h₂ : (DerivedCategory.Qh (C := D)).map (((totalToHomotopy F).map f).app L) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app (totalComplex F K' L) =
      (DerivedCategory.quotientCompQhIso D).hom.app (totalComplex F K L) ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app L) :=
    DerivedCategory.quotientCompQhIso_hom_naturality _
  simp only [totalComplexQhIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc, h₂]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The mirror of `totalComplexQhIso_naturality_left`: the total-complex bridge intertwines
the homotopy-level descent with `Tot(F(K, -))` in the second variable. -/
theorem totalComplexQhIso_naturality_right
    (K : CochainComplex A ℤ) {L L' : CochainComplex B ℤ} (g : L ⟶ L') :
    (DerivedCategory.Qh (C := D)).map
          (((homotopyBifunctor F).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).map
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g)) ≫
        (totalComplexQhIso F K L').hom =
      (totalComplexQhIso F K L).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K).map g) := by
  have h : ((homotopyBifunctor F).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).map
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g) ≫
      (((homotopyBifunctorIso F).hom.app K).app L') =
    (((homotopyBifunctorIso F).hom.app K).app L) ≫ ((totalToHomotopy F).obj K).map g :=
    ((homotopyBifunctorIso F).hom.app K).naturality g
  have h₂ : (DerivedCategory.Qh (C := D)).map (((totalToHomotopy F).obj K).map g) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app (totalComplex F K L') =
      (DerivedCategory.quotientCompQhIso D).hom.app (totalComplex F K L) ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K).map g) :=
    DerivedCategory.quotientCompQhIso_hom_naturality _
  simp only [totalComplexQhIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc, h₂]

/-! ### A K-flat right factor, uniformly in that factor -/

/-- `Tot(F(-, -))` with the second variable restricted to the K-flat objects of `K(B)` and
the first left as the whole homotopy category `K(A)`, landing in `D(D)`. Restricting the
first variable along the inclusion of the left K-flat objects recovers `kFlatToDerived`. -/
abbrev homotopyToDerivedRight :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤
      (kFlatObjects F).FullSubcategory ⥤ DerivedCategory D :=
  (homotopyBifunctor F ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Qh (C := D))) ⋙
    (Functor.whiskeringLeft _ _ _).obj (kFlatObjects F).ι

/-- The same bifunctor read on cochain complexes of `A`, which is what the descent to `D(A)`
localizes. -/
abbrev totalToDerivedRight :
    CochainComplex A ℤ ⥤ (kFlatObjects F).FullSubcategory ⥤ DerivedCategory D :=
  HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ homotopyToDerivedRight F

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- **`Tot(F(-, -))` inverts quasi-isomorphisms of the first variable, uniformly over K-flat
second arguments.** A natural transformation of functors is an isomorphism exactly when each
component is, and each component is `isIso_Qh_map_homotopyBifunctor_map_app`. This is the
hypothesis `Localization.lift` consumes in the functor category. -/
theorem totalToDerivedRight_inverts :
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
      (totalToDerivedRight F) := by
  intro K K' f hf
  let _ : ∀ Z, IsIso (((totalToDerivedRight F).map f).app Z) := fun Z ↦
    isIso_Qh_map_homotopyBifunctor_map_app F
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf) Z.1 Z.2
  exact NatIso.isIso_of_isIso_app _

/-- The descent of `Tot(F(-, -))` to `D(A)` in the first variable, uniformly over K-flat
second arguments. -/
def derivedToDerivedRight :
    DerivedCategory A ⥤ (kFlatObjects F).FullSubcategory ⥤ DerivedCategory D :=
  CategoryTheory.Localization.lift (totalToDerivedRight F)
    (totalToDerivedRight_inverts F) (DerivedCategory.Q (C := A))

/-- The descent agrees with `Tot(F(-, -))` on complexes. -/
def derivedToDerivedRightFac :
    DerivedCategory.Q (C := A) ⋙ derivedToDerivedRight F ≅ totalToDerivedRight F :=
  CategoryTheory.Localization.fac (totalToDerivedRight F)
    (totalToDerivedRight_inverts F) (DerivedCategory.Q (C := A))

/-- The descent agrees with the homotopy-level descent on `K(A)`. The homotopy quotient is a
localization at the homotopy equivalences, so this is the `preimageIso` of the `Q` versus
`Qh ∘ quotient` bridge and nothing more. -/
def homotopyToDerivedRightIso :
    DerivedCategory.Qh (C := A) ⋙ derivedToDerivedRight F ≅ homotopyToDerivedRight F :=
  (CategoryTheory.Localization.fullyFaithfulWhiskeringLeft
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      ((kFlatObjects F).FullSubcategory ⥤ DerivedCategory D)).preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        (derivedToDerivedRight F) ≪≫
      derivedToDerivedRightFac F)

section Comparison

variable [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- `derivedBifunctor` with its second variable restricted to the K-flat objects of `K(B)`,
so that it is comparable with `derivedToDerivedRight`. -/
abbrev derivedBifunctorRight :
    DerivedCategory A ⥤ (kFlatObjects F).FullSubcategory ⥤ DerivedCategory D :=
  derivedBifunctor F ⋙ (Functor.whiskeringLeft _ _ _).obj (kFlatQ F)

/-- **The derived bifunctor is the descent of `Tot(F(-, -))` in the first variable alone**,
uniformly over K-flat second arguments. Both sides restrict, along the localization
`kFlatQLeft`, to the two-sided comparison, and precomposition with a localization functor is
fully faithful on functor categories; so the isomorphism is the `preimageIso` of
`derivedBifunctorComparisonIso`, with no flatness hypothesis surviving on the first
variable. -/
def derivedBifunctorRightIso :
    derivedBifunctorRight F ≅ derivedToDerivedRight F :=
  (CategoryTheory.Localization.fullyFaithfulWhiskeringLeft (kFlatQLeft F)
      (kFlatQuasiIsoLeft F)
      ((kFlatObjects F).FullSubcategory ⥤ DerivedCategory D)).preimageIso
    (derivedBifunctorComparisonIso F ≪≫
      (Functor.isoWhiskerLeft (kFlatObjectsLeft F).ι
        (homotopyToDerivedRightIso F)).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- **A K-flat right factor computes the derived bifunctor against an arbitrary left
factor.** This is the `comparisonRight` field of the ringed-site statement of Tag 06YU: the
two-sided `comparison` with its left-hand K-flatness hypothesis dropped. -/
def comparisonRight (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) (hL : KFlat F L) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (totalComplex F K L) :=
  ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).mapIso
      ((DerivedCategory.quotientCompQhIso B).app L).symm ≪≫
    ((derivedBifunctorRightIso F).app (DerivedCategory.Q.obj K)).app
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≪≫
    ((derivedToDerivedRightFac F).app K).app
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≪≫
    totalComplexQhIso F K L

/-- **The derived bifunctor read on cochain complexes of `A` is the total complex**,
uniformly over K-flat second arguments: the two middle factors of `comparisonRight` bundled
into one isomorphism of functors on `CochainComplex A ℤ`. Naturality of `comparisonRight` in
either variable is a projection of this, which is why it is stated before the components. -/
def comparisonRightFac :
    DerivedCategory.Q (C := A) ⋙ derivedBifunctorRight F ≅ totalToDerivedRight F :=
  Functor.isoWhiskerLeft (DerivedCategory.Q (C := A)) (derivedBifunctorRightIso F) ≪≫
    derivedToDerivedRightFac F

/-- The three factors of `comparisonRight`, in the one spelling the naturality squares are
stated in. -/
theorem comparisonRight_hom (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hL : KFlat F L) :
    (comparisonRight F K L hL).hom =
      ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((comparisonRightFac F).hom.app K).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≫
        (totalComplexQhIso F K L).hom := by
  simp only [comparisonRight, comparisonRightFac, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]

/-- **Naturality of `comparisonRight` in the arbitrary left complex.** The isomorphism is
assembled from three natural transformations, and this is the composite of their three
squares: the `Q` versus `Qh ∘ quotient` bridge in the right-hand variable is natural,
`comparisonRightFac` is itself a natural transformation of functors on `CochainComplex A ℤ`,
and the total-complex bridge is `totalComplexQhIso_naturality_left`. No K-flatness is
assumed on either `K` or `K'`. -/
theorem comparisonRight_naturality_left
    {K K' : CochainComplex A ℤ} (f : K ⟶ K') (L : CochainComplex B ℤ) (hL : KFlat F L) :
    ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (comparisonRight F K' L hL).hom =
      (comparisonRight F K L hL).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app L) := by
  have hA : ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K')).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) =
      ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app
          ((kFlatQ F).obj ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩) :=
    (((derivedBifunctor F).map (DerivedCategory.Q.map f)).naturality _).symm
  have hB : ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app
          ((kFlatQ F).obj ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩) ≫
        ((comparisonRightFac F).hom.app K').app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ =
      ((comparisonRightFac F).hom.app K).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≫
        ((totalToDerivedRight F).map f).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ :=
    NatTrans.congr_app ((comparisonRightFac F).hom.naturality f)
      (⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ :
        (kFlatObjects F).FullSubcategory)
  have hC : ((totalToDerivedRight F).map f).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≫
        (totalComplexQhIso F K' L).hom =
      (totalComplexQhIso F K L).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app L) :=
    totalComplexQhIso_naturality_left F f L
  rw [comparisonRight_hom, comparisonRight_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hB]
  exact congrArg _ (congrArg _ hC)

/-- **Naturality of `comparisonRight` in the K-flat right complex.** Here the three squares
are: the `Q` versus `Qh ∘ quotient` bridge, which is natural by
`DerivedCategory.quotientCompQhIso_inv_naturality`; the component of `comparisonRightFac` at
`K`, which is a natural transformation of functors on the K-flat objects of `K(B)`, so this
square is exactly its naturality at the K-flat morphism induced by `g`; and
`totalComplexQhIso_naturality_right`. -/
theorem comparisonRight_naturality_right
    (K : CochainComplex A ℤ) {L L' : CochainComplex B ℤ} (g : L ⟶ L')
    (hL : KFlat F L) (hL' : KFlat F L') :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        (comparisonRight F K L' hL').hom =
      (comparisonRight F K L hL).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K).map g) := by
  have hA : ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map g) ≫
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L') =
      ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.Qh (C := B)).map
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (DerivedCategory.quotientCompQhIso_inv_naturality g)
  have hB : ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.Qh (C := B)).map
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g)) ≫
        ((comparisonRightFac F).hom.app K).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L', hL'⟩ =
      ((comparisonRightFac F).hom.app K).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≫
        (DerivedCategory.Qh (C := D)).map
          (((homotopyBifunctor F).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).map
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g)) :=
    ((comparisonRightFac F).hom.app K).naturality
      (ObjectProperty.homMk ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g) :
        (⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ :
            (kFlatObjects F).FullSubcategory) ⟶
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L', hL'⟩)
  have hC := totalComplexQhIso_naturality_right F K g
  rw [comparisonRight_hom, comparisonRight_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hB]
  exact congrArg _ (congrArg _ hC)

/-- **`comparisonRight` is natural in both variables at once**: the composite of the two
one-variable squares. The right-hand map is the total complex of `f` and `g` written as the
composite of the two one-variable maps, which is the one spelling in which both squares are
stated. -/
theorem comparisonRight_naturality
    {K K' : CochainComplex A ℤ} {L L' : CochainComplex B ℤ} (f : K ⟶ K') (g : L ⟶ L')
    (hL : KFlat F L) (hL' : KFlat F L') :
    ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫
        (comparisonRight F K' L' hL').hom =
      (comparisonRight F K L hL).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).map f).app L ≫
            ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).obj K').map g) := by
  rw [comparisonRight_naturality_right F K' g hL hL', ← Category.assoc,
    comparisonRight_naturality_left F f L hL, Category.assoc, ← Functor.map_comp]

end Comparison

end

end CochainComplex.KFlatBifunctor

end

end
