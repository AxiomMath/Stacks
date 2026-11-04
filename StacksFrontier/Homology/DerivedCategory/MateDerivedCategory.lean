module

public import StacksFrontier.CategoryTheory.Localization.MateLocalization
public import StacksFrontier.CategoryTheory.Localization.NatTransMapDerivedCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedCategory

/-!
# The derived category of a square carries mates to mates

Let

```
         L₁                  R₁
      𝒜 --→ ℬ             𝒜 ←-- ℬ
    G ↓  ↗   ↓ H         G ↓  ↘  ↓ H
      𝒞 --→ 𝒟             𝒞 ←-- 𝒟
         L₂                  R₂
```

be a square of exact additive functors of abelian categories with derived categories, with
adjunctions `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` as its horizontal edges.
`CategoryTheory.mateEquiv` turns a 2-cell `α : G ⋙ L₂ ⟶ L₁ ⋙ H` into its mate
`β : R₁ ⋙ G ⟶ H ⋙ R₂`.  Each of the six functors acts on derived categories by
`CategoryTheory.Functor.mapDerivedCategory`, each of the two adjunctions by
`CategoryTheory.Adjunction.mapDerivedCategory`, and a 2-cell by
`CategoryTheory.TwoSquare.mapDerivedCategory` below — the derived form of its transformation,
read through the comparisons of the derived functor of a composite with the composite of the
derived functors.  This file shows that the derived form of the mate is the mate of the derived
form.

Both the mate and the derived category are determined by a universal property, and the proof is
the composite of the two: a 2-cell between the relevant composites is a mate as soon as it
satisfies one equation involving the counits
(`CategoryTheory.eq_mateEquiv_of_counit`), and an equation between transformations out of a
localized category holds as soon as it holds on the image of the localization functor
(`CategoryTheory.Localization.natTrans_ext`).  Both steps are already carried out at an
arbitrary localization in `CategoryTheory.mateEquiv_localization`, whose hypotheses ask exactly
that the descended 2-cells agree with the undescended ones on the image of the localization
functor.  So all that happens here is that those hypotheses are verified for
`DerivedCategory.Q`, which is
`CategoryTheory.TwoSquare.mapDerivedCategory_app_Q`, and that the mate is computed degreewise
on cochain complexes, which is
`CategoryTheory.mateEquiv_mapHomologicalComplex`.

## Main definitions

* `CategoryTheory.TwoSquare.mapHomologicalComplex`: the degreewise 2-square of a 2-square of
  additive functors.
* `CategoryTheory.TwoSquare.mapDerivedCategory`: the derived 2-square of a 2-square of exact
  additive functors.

## Main results

* `CategoryTheory.mateEquiv_mapHomologicalComplex`: **the degreewise action on complexes carries
  mates to mates.**
* `CategoryTheory.TwoSquare.mapDerivedCategory_app_Q`: the derived 2-square descends the
  degreewise one: on the image of `DerivedCategory.Q`, the two agree under the canonical
  factorizations of the four derived functors.
* `CategoryTheory.mateEquiv_mapDerivedCategory`: **the derived category carries mates to
  mates.**

## Implementation notes

The composition comparison used is
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`.  Both ends of the derived 2-square
are read through that one comparison, so the only values of it that enter are the two already
recorded on the image of `DerivedCategory.Q`:
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q`.

A 2-square is a natural transformation between composites, but `CategoryTheory.TwoSquare` is a
plain definition rather than an abbreviation: a term whose type is spelled `TwoSquare T L R B` is
not matched by a lemma about a term of type `T ⋙ R ⟶ L ⋙ B` at reducible transparency, so `simp`
will not rewrite a whiskering of it.  Where such a rewrite is wanted the transformation is named
through `CategoryTheory.TwoSquare.natTrans`, which is an abbreviation and so does reduce.

Nothing here is a result of the Stacks project: it is the compatibility of the mates
correspondence with passing to derived categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

open Stacks.DerivedCategoryComparisons (mapDerivedCategoryCompIso
  mapDerivedCategoryCompIso_hom_app_Q mapDerivedCategoryCompIso_inv_app_Q)

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

/-! ### The degreewise 2-square -/

section Degreewise

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] {D : Type u₄} [Category.{v₄} D] [Abelian D]

/-- **The degreewise 2-square of a 2-square of additive functors.**  The four functors act on
homological complexes degreewise, and so does the transformation; the degreewise action of a
composite *is* the composite of the degreewise actions. -/
def TwoSquare.mapHomologicalComplex {T : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D} {Bo : C ⥤ D}
    [T.Additive] [L.Additive] [R.Additive] [Bo.Additive] (α : TwoSquare T L R Bo)
    {ι : Type*} (c : ComplexShape ι) :
    TwoSquare (T.mapHomologicalComplex c) (L.mapHomologicalComplex c)
      (R.mapHomologicalComplex c) (Bo.mapHomologicalComplex c) :=
  TwoSquare.mk _ _ _ _ (NatTrans.mapHomologicalComplex α.natTrans c)

/-- The component of the degreewise 2-square at a complex `K`, in degree `i`, is the component
of the original 2-square at the object `K.X i`. -/
@[simp]
theorem TwoSquare.mapHomologicalComplex_app_f {T : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D} {Bo : C ⥤ D}
    [T.Additive] [L.Additive] [R.Additive] [Bo.Additive] (α : TwoSquare T L R Bo)
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex A c) (i : ι) :
    ((α.mapHomologicalComplex c).app K).f i = α.app (K.X i) :=
  rfl

variable {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  [G.Additive] [H.Additive] [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]

/-- **The degreewise action on complexes carries mates to mates.**  The unit and counit of the
degreewise adjunction are degreewise, so the equation of
`CategoryTheory.mateEquiv_counit` which pins down the mate holds degreewise. -/
theorem mateEquiv_mapHomologicalComplex (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) {ι : Type*} (c : ComplexShape ι) :
    mateEquiv (adj₁.mapHomologicalComplex c) (adj₂.mapHomologicalComplex c)
        (α.mapHomologicalComplex c) =
      (mateEquiv adj₁ adj₂ α).mapHomologicalComplex c :=
  (eq_mateEquiv_of_counit (adj₁.mapHomologicalComplex c) (adj₂.mapHomologicalComplex c)
    (α.mapHomologicalComplex c) ((mateEquiv adj₁ adj₂ α).mapHomologicalComplex c) fun K => by
      ext i
      exact mateEquiv_counit adj₁ adj₂ α (K.X i)).symm

end Degreewise

/-! ### The derived 2-square -/

section Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **The derived 2-square of a 2-square of exact additive functors.**  The derived form
`CategoryTheory.NatTrans.mapDerivedCategory` of the transformation goes between the derived
functors of the two composites; the two comparisons
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` identify those with the composites
of the derived functors. -/
def TwoSquare.mapDerivedCategory {T : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D} {Bo : C ⥤ D}
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [Bo.Additive] [PreservesFiniteLimits Bo] [PreservesFiniteColimits Bo]
    (α : TwoSquare T L R Bo) :
    TwoSquare T.mapDerivedCategory L.mapDerivedCategory R.mapDerivedCategory
      Bo.mapDerivedCategory :=
  TwoSquare.mk _ _ _ _
    ((mapDerivedCategoryCompIso T R).inv ≫ NatTrans.mapDerivedCategory α.natTrans ≫
      (mapDerivedCategoryCompIso L Bo).hom)

/-- The chase that remains once the three comparisons have been computed on the image of the
localization: four pairs of mutually inverse morphisms, one of them in the image of a functor,
leave only the middle morphism.  Stated at an arbitrary pair of categories with the objects
implicit and the morphisms explicit, so that it applies by `exact`. -/
private theorem chase {𝒳 : Type u₅} [Category.{v₅} 𝒳] {𝒴 : Type u₆} [Category.{v₆} 𝒴]
    (Φ : 𝒳 ⥤ 𝒴) {X Y : 𝒳} {P Q R S Z : 𝒴} (u : X ⟶ Y) (v : Y ⟶ X) (a : P ⟶ Φ.obj X)
    (a' : Φ.obj X ⟶ P) (f : P ⟶ Q) (f' : Q ⟶ P) (g : P ⟶ R) (h : R ⟶ S) (h' : S ⟶ R)
    (t : R ⟶ Z) (hu : u ≫ v = 𝟙 X) (ha : a ≫ a' = 𝟙 P) (hf : f ≫ f' = 𝟙 P)
    (hh : h ≫ h' = 𝟙 R) :
    a ≫ Φ.map u ≫ Φ.map v ≫ a' ≫ f ≫ f' ≫ g ≫ h ≫ h' ≫ t = g ≫ t := by
  have hΦ : Φ.map u ≫ Φ.map v = 𝟙 (Φ.obj X) :=
    ((Φ.map_comp u v).symm.trans (congrArg Φ.map hu)).trans (Φ.map_id X)
  rw [← Category.assoc (Φ.map u) (Φ.map v), hΦ, Category.id_comp, ← Category.assoc a a', ha,
    Category.id_comp, ← Category.assoc f f', hf, Category.id_comp, ← Category.assoc h h', hh,
    Category.id_comp]

/-- **The derived 2-square descends the degreewise one.**  On the image of `DerivedCategory.Q`
the derived 2-square agrees with the degreewise one, read through the canonical factorization
`CategoryTheory.Functor.mapDerivedCategoryFactors` of each of the four derived functors.  This is
the hypothesis that `CategoryTheory.mateEquiv_localization` asks of a descended 2-cell. -/
theorem TwoSquare.mapDerivedCategory_app_Q {T : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D} {Bo : C ⥤ D}
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [Bo.Additive] [PreservesFiniteLimits Bo] [PreservesFiniteColimits Bo]
    (α : TwoSquare T L R Bo) (K : CochainComplex A ℤ) :
    R.mapDerivedCategoryFactors.inv.app
          ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        R.mapDerivedCategory.map (T.mapDerivedCategoryFactors.inv.app K) ≫
        α.mapDerivedCategory.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app K) ≫
        Bo.mapDerivedCategoryFactors.inv.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        Bo.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K) := by
  show R.mapDerivedCategoryFactors.inv.app _ ≫
      R.mapDerivedCategory.map (T.mapDerivedCategoryFactors.inv.app K) ≫
      ((mapDerivedCategoryCompIso T R).inv ≫ NatTrans.mapDerivedCategory α.natTrans ≫
        (mapDerivedCategoryCompIso L Bo).hom).app (DerivedCategory.Q.obj K) = _
  rw [NatTrans.comp_app, NatTrans.comp_app, mapDerivedCategoryCompIso_inv_app_Q,
    NatTrans.mapDerivedCategory_app_Q,
    mapDerivedCategoryCompIso_hom_app_Q]
  simp only [Category.assoc]
  exact chase R.mapDerivedCategory _ _ _ _ _ _ _ _ _ _
    (T.mapDerivedCategoryFactors.inv_hom_id_app K)
    (R.mapDerivedCategoryFactors.inv_hom_id_app _)
    ((T ⋙ R).mapDerivedCategoryFactors.inv_hom_id_app K)
    ((L ⋙ Bo).mapDerivedCategoryFactors.inv_hom_id_app K)

variable {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]

/-- The canonical factorization of `F.mapDerivedCategory` through `DerivedCategory.Q`, as a
`CatCommSq`. -/
private instance catCommSq_mapDerivedCategory {F : A ⥤ B} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactors.symm⟩

/-- **The derived category carries mates to mates.**  For a square of exact additive functors of
abelian categories with derived categories whose horizontal edges are adjunctions, the derived
2-square of the mate of a 2-cell is the mate of its derived 2-square, with respect to the two
derived adjunctions. -/
theorem mateEquiv_mapDerivedCategory (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) :
    mateEquiv adj₁.mapDerivedCategory adj₂.mapDerivedCategory α.mapDerivedCategory =
      (mateEquiv adj₁ adj₂ α).mapDerivedCategory := by
  refine (mateEquiv_localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    (adj₁.mapHomologicalComplex (ComplexShape.up ℤ))
    (adj₂.mapHomologicalComplex (ComplexShape.up ℤ))
    adj₁.mapDerivedCategory adj₂.mapDerivedCategory rfl rfl
    (α.mapHomologicalComplex (ComplexShape.up ℤ)) α.mapDerivedCategory
    (mateEquiv adj₁ adj₂ α).mapDerivedCategory
    (fun K => α.mapDerivedCategory_app_Q K) ?_).symm
  intro K
  rw [mateEquiv_mapHomologicalComplex adj₁ adj₂ α (ComplexShape.up ℤ)]
  exact (mateEquiv adj₁ adj₂ α).mapDerivedCategory_app_Q K

end Derived

end CategoryTheory

end
