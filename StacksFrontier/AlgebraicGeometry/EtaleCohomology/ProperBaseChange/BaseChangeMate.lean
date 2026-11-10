module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition

/-!
# The derived étale base change map is a mate

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. This file constructs the comparison of the two composite
derived inverse images around the square, as a 2-square, and identifies the derived base change
map `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` with its mate. As a consequence the
derived base change maps of a tower of two commutative squares compose.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'` — the composition isomorphism
  `(fg)^{-1} ≅ g^{-1} ⋙ f^{-1}` for inverse image on unbounded derived categories of abelian
  sheaves on small étale sites, with the composite `fg` carried as a named morphism.
* `Stacks.EtaleCohomology.etaleAbelianHomotopySquare` and
  `Stacks.EtaleCohomology.etaleAbelianDerivedSquare` — the comparison of the two composite
  inverse images around the square, degreewise on homotopy categories and on the unbounded
  derived categories.

## Main results

* `Stacks.EtaleCohomology.derivedSquare_app_Qh` — the derived square comparison is the
  localization of the degreewise one.
* `Stacks.EtaleCohomology.etaleAbelianHomotopyBaseChange_eq_mateEquiv` — the degreewise base
  change comparison, on the homotopy categories, is the mate of the degreewise square
  comparison.
* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_mateEquiv` — the derived étale base
  change map is the mate of the derived square comparison.
* `Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'_assoc` — the associativity
  pentagon of the derived inverse image comparison.
* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_app` — the derived base change
  comparisons of a tower of two commutative squares compose.
* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_isIso_of_comp` — if the derived base
  change maps of two stacked commutative squares are isomorphisms at `K`, so is the derived base
  change map of the outer rectangle.

## Implementation notes

The rearrangements `mate_descent_chase` and `compIso_lift_assoc_app` are stated with every object,
functor and morphism a variable: at the concrete types the functors involved are localizations
and total derived functors, and the elaborator and the kernel would unfold the derived-category
construction.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- The quasi-isomorphisms in the homotopy category of unbounded complexes of abelian sheaves on
the small étale site of a scheme: the morphisms that `DerivedCategory.Qh` inverts. -/
public abbrev etaleAbelianQuasiIso (X : Scheme.{u}) :
    MorphismProperty (HomotopyCategory
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)

section CompIso

variable {X Y Z : Scheme.{u}}

/-- The localization `Qh` lifts the degreewise composite of two inverse images to the composite of
the two derived inverse images: both exactness comparisons, read in sequence. -/
public instance liftingInverseImageComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Localization.Lifting DerivedCategory.Qh (etaleAbelianQuasiIso.{u, v} Z)
      ((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((etaleAbelianInverseImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh))
      (etaleAbelianDerivedInverseImage.{u, v} g ⋙ etaleAbelianDerivedInverseImage.{u, v} f) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
        (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh
        (etaleAbelianDerivedInverseImage.{u, v} f) ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          ((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ))
          (etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh⟩

/-- The composition isomorphism `(fg)^{-1} ≅ g^{-1} ⋙ f^{-1}` for inverse image on unbounded
derived categories of abelian sheaves on the small étale sites, with the composite `fg` carried
as a named morphism together with an equation naming it: the degreewise composition isomorphism
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'` lifted along the localization. -/
public def etaleAbelianDerivedInverseImageCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    etaleAbelianDerivedInverseImage.{u, v} fg ≅
      etaleAbelianDerivedInverseImage.{u, v} g ⋙ etaleAbelianDerivedInverseImage.{u, v} f :=
  Localization.liftNatIso DerivedCategory.Qh (etaleAbelianQuasiIso.{u, v} Z) _ _ _ _
    (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
          (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).symm (ComplexShape.up ℤ)).symm
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _)

/-- The lifting of degreewise inverse image along `Qh` is the exactness comparison. -/
private theorem liftingIso_single (m : X ⟶ Z) :
    Localization.Lifting.iso DerivedCategory.Qh (etaleAbelianQuasiIso.{u, v} Z)
        ((etaleAbelianInverseImage.{u, v} m).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh)
        (etaleAbelianDerivedInverseImage.{u, v} m) =
      (etaleAbelianInverseImage.{u, v} m).mapDerivedCategoryFactorsh :=
  rfl

/-- The lifting of the degreewise composite of two inverse images along `Qh`, written out. -/
public theorem liftingIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Localization.Lifting.iso DerivedCategory.Qh (etaleAbelianQuasiIso.{u, v} Z)
        ((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          ((etaleAbelianInverseImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh))
        (etaleAbelianDerivedInverseImage.{u, v} g ⋙ etaleAbelianDerivedInverseImage.{u, v} f) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
            (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh
            (etaleAbelianDerivedInverseImage.{u, v} f) ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft
              ((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ))
              (etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh :=
  rfl

variable (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
  (K : HomotopyCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (ComplexShape.up ℤ))

/-- The component of the derived composition isomorphism at the object represented by a complex:
the two exactness comparisons and the degreewise composition isomorphism. -/
private theorem etaleAbelianDerivedInverseImageCompIso'_hom_app_Qh :
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g fg hfg).hom.app
        (DerivedCategory.Qh.obj K) =
      (etaleAbelianInverseImage.{u, v} fg).mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).symm
            (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh.inv.app
          (((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (etaleAbelianDerivedInverseImage.{u, v} f).map
          ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app K) := by
  dsimp only [etaleAbelianDerivedInverseImageCompIso', Localization.liftNatIso]
  rw [Localization.liftNatTrans_app, liftingIso_single, liftingIso_comp]
  simp

end CompIso

/-! ### Abstract bookkeeping -/

section Abstract

universe v₁ v₂ u₁ u₂

/-- The component of a mate, written out. -/
private theorem mateEquiv_app' {A B C D : Type*} [Category A] [Category B] [Category C]
    [Category D] {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (d : B) :
    (mateEquiv adj₁ adj₂ α).app d =
      adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (α.app (R₁.obj d)) ≫
        R₂.map (H.map (adj₁.counit.app d)) := by
  simp [mateEquiv]

/-- If `h' ≫ h = 𝟙` and `(h ≫ tail) ≫ e = 𝟙`, then `tail ≫ e = h'`. -/
private theorem tail_comp_inv {C : Type u₁} [Category.{v₁} C] {O₁ O₂ O₃ : C} (h : O₁ ⟶ O₂)
    (h' : O₂ ⟶ O₁) (tail : O₂ ⟶ O₃) (e : O₃ ⟶ O₁) (hh : h' ≫ h = 𝟙 O₂)
    (he : (h ≫ tail) ≫ e = 𝟙 O₁) :
    tail ≫ e = h' := by
  calc tail ≫ e = (h' ≫ h) ≫ tail ≫ e := by rw [hh, Category.id_comp]
    _ = h' ≫ (h ≫ tail) ≫ e := by simp only [Category.assoc]
    _ = h' := by rw [he, Category.comp_id]

/-- If `a ≫ a' = 𝟙` and `F.map a' ≫ t = r`, then `t = F.map a ≫ r`. -/
private theorem eq_map_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {c₁ c₂ : C} (a : c₁ ⟶ c₂) (a' : c₂ ⟶ c₁) (haa : a ≫ a' = 𝟙 c₁) {d : D}
    (t : F.obj c₁ ⟶ d) (r : F.obj c₂ ⟶ d) (h : F.map a' ≫ t = r) :
    t = F.map a ≫ r := by
  rw [← h, ← Category.assoc, ← F.map_comp, haa, F.map_id, Category.id_comp]

/-- For an adjunction `L ⊣ R` and morphisms satisfying the identities `hϕ`, `hnat`, `hcounit`,
`hunit`, `hA`, `hb` and `hη`, the composites `u₁ ≫ u₂ ≫ η ≫ R s₂ ≫ R w` and `σ ≫ ρ₂' ≫ R z₂`
agree, where `η` is the unit of the adjunction. -/
private theorem mate_descent_chase {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {a₀ a₁ a₂ a₃ a₄ : A} {b₀ b₁ b₂ b₃ b₄ b₅ : B}
    (u₁ : a₀ ⟶ a₁) (u₂ : a₁ ⟶ a₂) (s₁ : L.obj a₁ ⟶ b₁) (s₂ : L.obj a₂ ⟶ b₂) (v : b₁ ⟶ b₂)
    (w : b₂ ⟶ b₃) (p : b₁ ⟶ b₄) (q : b₄ ⟶ b₃) (ϕ : L.obj a₀ ⟶ b₀) (ϕ' : b₀ ⟶ L.obj a₀)
    (ρ₁ : a₀ ⟶ a₃) (ρ₂ : a₃ ⟶ R.obj b₀) (τ : a₃ ⟶ a₄) (ρ₂' : a₄ ⟶ R.obj b₅) (z₁ : b₀ ⟶ b₅)
    (z₂ : b₅ ⟶ b₃) (σ : a₀ ⟶ a₄)
    (hϕ : ϕ ≫ ϕ' = 𝟙 (L.obj a₀))
    (hnat : L.map u₂ ≫ s₂ = s₁ ≫ v)
    (hcounit : v ≫ w = p ≫ q)
    (hunit : adj.unit.app a₀ ≫ R.map ϕ = ρ₁ ≫ ρ₂)
    (hA : ϕ' ≫ L.map u₁ ≫ s₁ ≫ p ≫ q = z₁ ≫ z₂)
    (hb : ρ₁ ≫ τ = σ)
    (hη : τ ≫ ρ₂' = ρ₂ ≫ R.map z₁) :
    u₁ ≫ u₂ ≫ adj.unit.app a₂ ≫ R.map s₂ ≫ R.map w = σ ≫ ρ₂' ≫ R.map z₂ := by
  have hum : u₁ ≫ u₂ ≫ adj.unit.app a₂ =
      adj.unit.app a₀ ≫ R.map (L.map u₁) ≫ R.map (L.map u₂) := by
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      ← Adjunction.unit_naturality adj (u₁ ≫ u₂)]
  calc u₁ ≫ u₂ ≫ adj.unit.app a₂ ≫ R.map s₂ ≫ R.map w
      = (u₁ ≫ u₂ ≫ adj.unit.app a₂) ≫ R.map s₂ ≫ R.map w := by
        simp only [Category.assoc]
    _ = adj.unit.app a₀ ≫ R.map (L.map u₁ ≫ (L.map u₂ ≫ s₂) ≫ w) := by
        rw [hum]; simp only [Functor.map_comp, Category.assoc]
    _ = adj.unit.app a₀ ≫ R.map (L.map u₁ ≫ s₁ ≫ p ≫ q) := by
        rw [hnat]; simp only [Category.assoc]; rw [hcounit]
    _ = adj.unit.app a₀ ≫ R.map ϕ ≫ R.map (ϕ' ≫ L.map u₁ ≫ s₁ ≫ p ≫ q) := by
        rw [← Functor.map_comp, ← Category.assoc, ← Category.assoc, ← Category.assoc,
          ← Category.assoc, hϕ, Category.id_comp]
    _ = (ρ₁ ≫ ρ₂) ≫ R.map z₁ ≫ R.map z₂ := by
        rw [hA, Functor.map_comp, ← Category.assoc, hunit]
    _ = ρ₁ ≫ (τ ≫ ρ₂') ≫ R.map z₂ := by rw [hη]; simp only [Category.assoc]
    _ = σ ≫ ρ₂' ≫ R.map z₂ := by simp only [← Category.assoc, hb]

end Abstract

/-! ### Mates and the degreewise functors -/

section MapHomotopyCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {ι : Type*} {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  [Preadditive A] [Preadditive B] [Preadditive A'] [Preadditive B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc : A ⥤ B'}
  [Lf.Additive] [Rf.Additive] [Lf'.Additive] [Rf'.Additive] [Lg.Additive] [Lg'.Additive]
  [Lc.Additive]

/-- The unit of the adjunction induced on complexes is, in each degree, the unit of the given
adjunction. -/
private theorem mapHomologicalComplexAdjunction_unit_app_f {V W : Type*} [Category V]
    [Category W] [Preadditive V] [Preadditive W] {F : V ⥤ W} {G : W ⥤ V} [F.Additive]
    [G.Additive] (adj : G ⊣ F) (c : ComplexShape ι) (K : HomologicalComplex W c) (n : ι) :
    ((Adjunction.mapHomologicalComplexAdjunction adj c).unit.app K).f n =
      adj.unit.app (K.X n) := rfl

/-- The counit of the adjunction induced on complexes is, in each degree, the counit of the
given adjunction. -/
private theorem mapHomologicalComplexAdjunction_counit_app_f {V W : Type*} [Category V]
    [Category W] [Preadditive V] [Preadditive W] {F : V ⥤ W} {G : W ⥤ V} [F.Additive]
    [G.Additive] (adj : G ⊣ F) (c : ComplexShape ι) (K : HomologicalComplex V c) (n : ι) :
    ((Adjunction.mapHomologicalComplexAdjunction adj c).counit.app K).f n =
      adj.counit.app (K.X n) := rfl

/-- Taking mates commutes with applying the functors degreewise to complexes: the base change
2-square of a square of adjunctions, applied degreewise, is the base change 2-square of the
squares of adjunctions induced on categories of complexes. -/
private theorem twoSquare_mapHomologicalComplex (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (c : ComplexShape ι) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (Rf ⋙ Lg)) c).hom ≫
        NatTrans.mapHomologicalComplex
          (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef) c ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (Lg' ⋙ Rf')) c).inv =
      (Stacks.CategoryTheory.BaseChange.twoSquare
        (Adjunction.mapHomologicalComplexAdjunction adjf c)
        (Adjunction.mapHomologicalComplexAdjunction adjf' c)
        (Functor.mapHomologicalComplexCompIso eg c)
        (Functor.mapHomologicalComplexCompIso ef c)) := by
  ext K n
  simp [Stacks.CategoryTheory.BaseChange.twoSquare,
    Stacks.CategoryTheory.BaseChange.pullbackComparison, mateEquiv,
    mapHomologicalComplexAdjunction_unit_app_f, mapHomologicalComplexAdjunction_counit_app_f]

/-- Taking mates commutes with passing to the homotopy categories: the base change 2-square of a
square of adjunctions, applied degreewise and passed to the homotopy categories, is the base
change 2-square of the squares of adjunctions induced on the homotopy categories. -/
private theorem twoSquare_mapHomotopyCategory (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (c : ComplexShape ι) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (Rf ⋙ Lg)) c).hom ≫
        NatTrans.mapHomotopyCategory
          (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef) c ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (Lg' ⋙ Rf')) c).inv =
      (Stacks.CategoryTheory.BaseChange.twoSquare
        (Adjunction.mapHomotopyCategoryAdjunction adjf c)
        (Adjunction.mapHomotopyCategoryAdjunction adjf' c)
        (Functor.mapHomotopyCategoryCompIso eg c)
        (Functor.mapHomotopyCategoryCompIso ef c)) := by
  ext ⟨K⟩
  exact congrArg (HomotopyCategory.quotient A' c).map
    (NatTrans.congr_app (twoSquare_mapHomologicalComplex adjf adjf' eg ef c) K)

end MapHomotopyCategory

/-! ### The derived base change map as a mate -/

section DerivedMate

variable {X X' Y Y' : Scheme.{u}}

/-- The comparison of the two composite derived inverse images around a commutative square, as a
2-square. The common composite `X' ⟶ Y` is
carried as a named morphism together with the two equations naming it. -/
public def etaleAbelianDerivedSquare (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g) :
    TwoSquare (etaleAbelianDerivedInverseImage.{u, v} g)
      (etaleAbelianDerivedInverseImage.{u, v} f)
      (etaleAbelianDerivedInverseImage.{u, v} f')
      (etaleAbelianDerivedInverseImage.{u, v} g') :=
  TwoSquare.mk _ _ _ _
    ((etaleAbelianDerivedInverseImageCompIso'.{u, v} f' g P hP₂).inv ≫
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} g' f P hP₁).hom)

/-- The comparison of the two composite inverse images around the square, applied degreewise to
unbounded complexes and passed to the homotopy categories. The common composite `X' ⟶ Y` is
carried as a named morphism together with the two equations naming it. -/
public def etaleAbelianHomotopySquare (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g) :
    (etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianInverseImage.{u, v} f').mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (etaleAbelianInverseImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso
      (etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).symm (ComplexShape.up ℤ)).hom ≫
    (Functor.mapHomotopyCategoryCompIso
      (etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).symm (ComplexShape.up ℤ)).inv

/-- The derived-functor unit exhibiting `Rf_* ⋙ g^{-1}` as a right derived functor of degreewise
`f_* ⋙ g^{-1}`: the unit of `Rf_*` whiskered with `g^{-1}`. -/
private abbrev derivedBaseChangeUnit (f : X ⟶ Y) (g : Y' ⟶ Y) :
    etaleAbelianPushforwardToDerivedCategory.{u, v} f ⋙
        etaleAbelianDerivedInverseImage.{u, v} g ⟶
      DerivedCategory.Qh ⋙ (etaleAbelianDerivedDirectImage.{u, v} f ⋙
        etaleAbelianDerivedInverseImage.{u, v} g) :=
  Functor.whiskerRight (etaleAbelianDerivedDirectImageUnit.{u, v} f)
      (etaleAbelianDerivedInverseImage.{u, v} g) ≫ (Functor.associator _ _ _).hom

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g)
  (N : HomotopyCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (ComplexShape.up ℤ))

/-- The second leg of the derived square comparison, read at an object represented by a
complex: the derived composition isomorphism around the lower-left of the square, cancelled
against the exactness comparison for the composite. -/
private theorem derivedSquare_leg₁ :
    (etaleAbelianInverseImage.{u, v} P).mapDerivedCategoryFactorsh.inv.app N ≫
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} g' f P hP₁).hom.app
          (DerivedCategory.Qh.obj N) ≫
        (etaleAbelianDerivedInverseImage.{u, v} g').map
          ((etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh.hom.app N) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).symm
            (ComplexShape.up ℤ)).inv.app N) ≫
        (etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app
          (((etaleAbelianInverseImage.{u, v} f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj N) := by
  rw [etaleAbelianDerivedInverseImageCompIso'_hom_app_Qh.{u, v} g' f P hP₁ N]
  simp [← Functor.map_comp]

/-- The first leg of the derived square comparison, read at an object represented by a complex:
the inverse of the derived composition isomorphism around the upper-right of the square. -/
private theorem derivedSquare_leg₂ :
    (etaleAbelianInverseImage.{u, v} f').mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj N) ≫
      (etaleAbelianDerivedInverseImage.{u, v} f').map
        ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app N) ≫
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} f' g P hP₂).inv.app
        (DerivedCategory.Qh.obj N) =
    DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso
          (etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).symm
          (ComplexShape.up ℤ)).hom.app N) ≫
      (etaleAbelianInverseImage.{u, v} P).mapDerivedCategoryFactorsh.inv.app N := by
  have key := tail_comp_inv
    ((etaleAbelianInverseImage.{u, v} P).mapDerivedCategoryFactorsh.hom.app N)
    ((etaleAbelianInverseImage.{u, v} P).mapDerivedCategoryFactorsh.inv.app N)
    (DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso
          (etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).symm
          (ComplexShape.up ℤ)).inv.app N) ≫
      (etaleAbelianInverseImage.{u, v} f').mapDerivedCategoryFactorsh.inv.app
          (((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj N) ≫
        (etaleAbelianDerivedInverseImage.{u, v} f').map
          ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app N))
    ((etaleAbelianDerivedInverseImageCompIso'.{u, v} f' g P hP₂).inv.app
      (DerivedCategory.Qh.obj N))
    (Iso.inv_hom_id_app _ _)
    (by
      rw [← etaleAbelianDerivedInverseImageCompIso'_hom_app_Qh.{u, v} f' g P hP₂ N]
      exact Iso.hom_inv_id_app _ _)
  simp only [Category.assoc] at key
  exact eq_map_comp DerivedCategory.Qh _ _ (Iso.hom_inv_id_app _ _) _ _ key

/-- The derived square comparison is the localization of the degreewise one: read at an
object represented by a complex, and conjugated by the four exactness comparisons, the
comparison of the two composite derived inverse images around the square is the image under
the localization functor of the degreewise comparison. -/
public theorem derivedSquare_app_Qh :
    (etaleAbelianInverseImage.{u, v} f').mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj N) ≫
      (etaleAbelianDerivedInverseImage.{u, v} f').map
        ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app N) ≫
      (etaleAbelianDerivedSquare.{u, v} f g g' f' P hP₁ hP₂).app
        (DerivedCategory.Qh.obj N) ≫
      (etaleAbelianDerivedInverseImage.{u, v} g').map
        ((etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh.hom.app N) =
    DerivedCategory.Qh.map
        ((etaleAbelianHomotopySquare.{u, v} f g g' f' P hP₁ hP₂).app N) ≫
      (etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianInverseImage.{u, v} f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj N) := by
  simp only [etaleAbelianDerivedSquare, etaleAbelianHomotopySquare, TwoSquare.mk,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% derivedSquare_leg₂ g f' P hP₂ N, derivedSquare_leg₁ f g' P hP₁ N]

/-- Applied degreewise to unbounded complexes and passed to the homotopy categories, the étale
base change comparison of a commutative square is the mate, under the two adjunctions induced on
homotopy categories by the inverse-image/direct-image adjunctions, of the degreewise comparison
`Stacks.EtaleCohomology.etaleAbelianHomotopySquare` of the two composite inverse images around
the square. -/
public theorem etaleAbelianHomotopyBaseChange_eq_mateEquiv :
    etaleAbelianHomotopyBaseChange.{u, v} f g g' f' (hP₁.symm.trans hP₂) =
      (mateEquiv
          (Adjunction.mapHomotopyCategoryAdjunction
            (etaleAbelianInverseImageDirectImageAdj.{u, v} f) (ComplexShape.up ℤ))
          (Adjunction.mapHomotopyCategoryAdjunction
            (etaleAbelianInverseImageDirectImageAdj.{u, v} f') (ComplexShape.up ℤ))
          (TwoSquare.mk _ _ _ _
            (etaleAbelianHomotopySquare.{u, v} f g g' f' P hP₁ hP₂))) := by
  subst hP₂
  have heg : (etaleAbelianInverseImageCompIso.{u, v} f' g).symm =
      (etaleAbelianInverseImageCompIso'.{u, v} f' g (f' ≫ g) rfl).symm :=
    congrArg Iso.symm (etaleAbelianInverseImageCompIso'_rfl.{u, v} f' g).symm
  have hef : (etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k)
          (hP₁.symm.trans rfl)) =
      (etaleAbelianInverseImageCompIso'.{u, v} g' f (f' ≫ g) hP₁).symm := by
    rw [etaleAbelianInverseImageCompIso'_eq.{u, v} g' f (f' ≫ g) hP₁]
    rfl
  refine (twoSquare_mapHomotopyCategory
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
    (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
    ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
      eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k)
        (hP₁.symm.trans rfl)))
    (ComplexShape.up ℤ)).trans ?_
  rw [heg, hef]
  rfl

/-- For a commutative square of schemes, the base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on
unbounded derived categories of abelian sheaves on the small étale sites is the mate, under the
two derived inverse-image/direct-image adjunctions, of the comparison
`Stacks.EtaleCohomology.etaleAbelianDerivedSquare` of the two composite derived inverse images
around the square. -/
public theorem etaleAbelianDerivedBaseChange_eq_mateEquiv :
    etaleAbelianDerivedBaseChange.{u, v} f g g' f' (hP₁.symm.trans hP₂) =
      (mateEquiv (etaleAbelianDerivedAdjunction.{u, v} f)
        (etaleAbelianDerivedAdjunction.{u, v} f')
        (etaleAbelianDerivedSquare.{u, v} f g g' f' P hP₁ hP₂)) := by
  refine Functor.rightDerived_ext
      (etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g)
      (derivedBaseChangeUnit.{u, v} f g)
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ))
      _ _ _ ?_
  ext K
  set N := ((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K
  set M := ((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ)).obj N
  set ψ := (Adjunction.mapHomotopyCategoryAdjunction
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f) (ComplexShape.up ℤ)).counit.app K
  set ξ := (etaleAbelianHomotopySquare.{u, v} f g g' f' P hP₁ hP₂).app N ≫
    ((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).map ψ
  have hcc := Stacks.DerivedFunctor.derivedAdjunction_counit_app
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianDerivedDirectImage.{u, v} f)
    (etaleAbelianDerivedDirectImageUnit.{u, v} f)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective K
  have hcounit : (etaleAbelianDerivedInverseImage.{u, v} g').map
          ((etaleAbelianDerivedInverseImage.{u, v} f).map
            ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K)) ≫
        (etaleAbelianDerivedInverseImage.{u, v} g').map
          ((etaleAbelianDerivedAdjunction.{u, v} f).counit.app (DerivedCategory.Qh.obj K)) =
      (etaleAbelianDerivedInverseImage.{u, v} g').map
          ((etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh.hom.app N) ≫
        (etaleAbelianDerivedInverseImage.{u, v} g').map (DerivedCategory.Qh.map ψ) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun t => (etaleAbelianDerivedInverseImage.{u, v} g').map t) hcc
  have hunit := Stacks.DerivedFunctor.derivedAdjunction_unit_app
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
    (etaleAbelianDerivedDirectImage.{u, v} f')
    (etaleAbelianDerivedDirectImageUnit.{u, v} f')
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective M
  have hnatg : DerivedCategory.Qh.map
          (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory
            (ComplexShape.up ℤ)).map ψ) ≫
        (etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app K =
      (etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app
          (((etaleAbelianInverseImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) ≫
        (etaleAbelianDerivedInverseImage.{u, v} g').map (DerivedCategory.Qh.map ψ) :=
    (etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.naturality ψ
  have hA : (etaleAbelianInverseImage.{u, v} f').mapDerivedCategoryFactorsh.inv.app M ≫
        (etaleAbelianDerivedInverseImage.{u, v} f').map
          ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app N) ≫
        (etaleAbelianDerivedSquare.{u, v} f g g' f' P hP₁ hP₂).app
          (DerivedCategory.Qh.obj N) ≫
        (etaleAbelianDerivedInverseImage.{u, v} g').map
          ((etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh.hom.app N) ≫
        (etaleAbelianDerivedInverseImage.{u, v} g').map (DerivedCategory.Qh.map ψ) =
      DerivedCategory.Qh.map ξ ≫
        (etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app K := by
    rw [reassoc_of% (derivedSquare_app_Qh.{u, v} f g g' f' P hP₁ hP₂ N), ← hnatg,
      ← Category.assoc, ← Functor.map_comp]
  have hb : DerivedCategory.Qh.map ((Adjunction.mapHomotopyCategoryAdjunction
          (etaleAbelianInverseImageDirectImageAdj.{u, v} f') (ComplexShape.up ℤ)).unit.app M) ≫
        DerivedCategory.Qh.map
          (((etaleAbelianDirectImage.{u, v} f').mapHomotopyCategory
            (ComplexShape.up ℤ)).map ξ) =
      DerivedCategory.Qh.map
        ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' (hP₁.symm.trans hP₂)).app K) := by
    rw [← Functor.map_comp]
    refine congrArg (fun t => DerivedCategory.Qh.map t) ?_
    rw [etaleAbelianHomotopyBaseChange_eq_mateEquiv f g g' f' P hP₁ hP₂, mateEquiv_app',
      Functor.map_comp]
  have hη : DerivedCategory.Qh.map
          (((etaleAbelianDirectImage.{u, v} f').mapHomotopyCategory
            (ComplexShape.up ℤ)).map ξ) ≫
        (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
          (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) =
      (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
          (((etaleAbelianInverseImage.{u, v} f').mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M) ≫
        (etaleAbelianDerivedDirectImage.{u, v} f').map (DerivedCategory.Qh.map ξ) :=
    (etaleAbelianDerivedDirectImageUnit.{u, v} f').naturality ξ
  have hchase := mate_descent_chase (etaleAbelianDerivedAdjunction.{u, v} f')
    ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app N)
    ((etaleAbelianDerivedInverseImage.{u, v} g).map
      ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K))
    ((etaleAbelianDerivedSquare.{u, v} f g g' f' P hP₁ hP₂).app (DerivedCategory.Qh.obj N))
    ((etaleAbelianDerivedSquare.{u, v} f g g' f' P hP₁ hP₂).app
      ((etaleAbelianDerivedDirectImage.{u, v} f).obj (DerivedCategory.Qh.obj K)))
    ((etaleAbelianDerivedInverseImage.{u, v} g').map
      ((etaleAbelianDerivedInverseImage.{u, v} f).map
        ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K)))
    ((etaleAbelianDerivedInverseImage.{u, v} g').map
      ((etaleAbelianDerivedAdjunction.{u, v} f).counit.app (DerivedCategory.Qh.obj K)))
    ((etaleAbelianDerivedInverseImage.{u, v} g').map
      ((etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh.hom.app N))
    ((etaleAbelianDerivedInverseImage.{u, v} g').map (DerivedCategory.Qh.map ψ))
    ((etaleAbelianInverseImage.{u, v} f').mapDerivedCategoryFactorsh.hom.app M)
    ((etaleAbelianInverseImage.{u, v} f').mapDerivedCategoryFactorsh.inv.app M)
    (DerivedCategory.Qh.map ((Adjunction.mapHomotopyCategoryAdjunction
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f') (ComplexShape.up ℤ)).unit.app M))
    ((etaleAbelianDerivedDirectImageUnit.{u, v} f').app
      (((etaleAbelianInverseImage.{u, v} f').mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
    (DerivedCategory.Qh.map
      (((etaleAbelianDirectImage.{u, v} f').mapHomotopyCategory (ComplexShape.up ℤ)).map ξ))
    ((etaleAbelianDerivedDirectImageUnit.{u, v} f').app
      (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (DerivedCategory.Qh.map ξ)
    ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app K)
    (DerivedCategory.Qh.map
      ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' (hP₁.symm.trans hP₂)).app K))
    (Iso.hom_inv_id_app _ _)
    ((etaleAbelianDerivedSquare.{u, v} f g g' f' P hP₁ hP₂).naturality
      ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K))
    hcounit hunit hA hb hη
  have hfac := etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' (hP₁.symm.trans hP₂) K
  have hgoal : (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app N ≫
        (etaleAbelianDerivedInverseImage.{u, v} g).map
          ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K) ≫
        (etaleAbelianDerivedBaseChange.{u, v} f g g' f' (hP₁.symm.trans hP₂)).app
          (DerivedCategory.Qh.obj K) =
      (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app N ≫
        (etaleAbelianDerivedInverseImage.{u, v} g).map
          ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K) ≫
        (mateEquiv (etaleAbelianDerivedAdjunction.{u, v} f)
          (etaleAbelianDerivedAdjunction.{u, v} f')
          (etaleAbelianDerivedSquare.{u, v} f g g' f' P hP₁ hP₂)).app
            (DerivedCategory.Qh.obj K) := by
    rw [hfac, mateEquiv_app']
    exact hchase.symm
  have hcan := congrArg
    (fun t => (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.hom.app N ≫ t)
    hgoal
  simp only [Iso.hom_inv_id_app_assoc] at hcan
  simpa only [derivedBaseChangeUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
    Functor.comp_obj] using hcan

end DerivedMate

/-! ### The associativity pentagon of the derived composition isomorphism -/

section AbstractAssoc

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- An associativity pentagon of composition isomorphisms, read at an object. -/
private theorem pentagon_app {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] {Ff : C₀ ⥤ C₁} {Fi : C₁ ⥤ C₂} {Fj : C₂ ⥤ C₃} {Fa : C₀ ⥤ C₂} {Fq : C₁ ⥤ C₃}
    {Fp : C₀ ⥤ C₃} (efi : Ff ⋙ Fi ≅ Fa) (eij : Fi ⋙ Fj ≅ Fq) (efq : Ff ⋙ Fq ≅ Fp)
    (eaj : Fa ⋙ Fj ≅ Fp)
    (h : Functor.whiskerLeft Ff eij.hom ≫ efq.hom =
      (Functor.associator Ff Fi Fj).inv ≫ Functor.whiskerRight efi.hom Fj ≫ eaj.hom)
    (X : C₀) :
    eij.hom.app (Ff.obj X) ≫ efq.hom.app X = Fj.map (efi.hom.app X) ≫ eaj.hom.app X := by
  simpa using NatTrans.congr_app h X

section Degreewise

variable {ι : Type*} {A₀ : Type u₁} {A₁ : Type u₂} {A₂ : Type u₃} {A₃ : Type u₄}
  [Category.{v₁} A₀] [Category.{v₂} A₁] [Category.{v₃} A₂] [Category.{v₄} A₃]
  [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
  {Ff : A₀ ⥤ A₁} {Fi : A₁ ⥤ A₂} {Fj : A₂ ⥤ A₃} {Fa : A₀ ⥤ A₂} {Fq : A₁ ⥤ A₃} {Fp : A₀ ⥤ A₃}
  [Ff.Additive] [Fi.Additive] [Fj.Additive] [Fa.Additive] [Fq.Additive] [Fp.Additive]

/-- An associativity pentagon of composition isomorphisms is inherited by the functors induced
on categories of complexes. -/
private theorem compIso_mapHomologicalComplex_assoc (efi : Ff ⋙ Fi ≅ Fa) (eij : Fi ⋙ Fj ≅ Fq)
    (efq : Ff ⋙ Fq ≅ Fp) (eaj : Fa ⋙ Fj ≅ Fp)
    (h : Functor.whiskerLeft Ff eij.hom ≫ efq.hom =
      (Functor.associator Ff Fi Fj).inv ≫ Functor.whiskerRight efi.hom Fj ≫ eaj.hom)
    (c : ComplexShape ι) :
    Functor.whiskerLeft (Ff.mapHomologicalComplex c)
          (Functor.mapHomologicalComplexCompIso eij c).hom ≫
        (Functor.mapHomologicalComplexCompIso efq c).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.mapHomologicalComplexCompIso efi c).hom
            (Fj.mapHomologicalComplex c) ≫
          (Functor.mapHomologicalComplexCompIso eaj c).hom := by
  ext K n
  simpa using pentagon_app efi eij efq eaj h (K.X n)

/-- An associativity pentagon of composition isomorphisms is inherited by the functors induced
on homotopy categories. -/
private theorem compIso_mapHomotopyCategory_assoc (efi : Ff ⋙ Fi ≅ Fa) (eij : Fi ⋙ Fj ≅ Fq)
    (efq : Ff ⋙ Fq ≅ Fp) (eaj : Fa ⋙ Fj ≅ Fp)
    (h : Functor.whiskerLeft Ff eij.hom ≫ efq.hom =
      (Functor.associator Ff Fi Fj).inv ≫ Functor.whiskerRight efi.hom Fj ≫ eaj.hom)
    (c : ComplexShape ι) :
    Functor.whiskerLeft (Ff.mapHomotopyCategory c)
          (Functor.mapHomotopyCategoryCompIso eij c).hom ≫
        (Functor.mapHomotopyCategoryCompIso efq c).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso efi c).hom
            (Fj.mapHomotopyCategory c) ≫
          (Functor.mapHomotopyCategoryCompIso eaj c).hom := by
  ext ⟨K⟩
  exact congrArg (HomotopyCategory.quotient A₃ c).map
    (NatTrans.congr_app (compIso_mapHomologicalComplex_assoc efi eij efq eaj h c) K)

end Degreewise

section Lifted

variable {C₀ : Type u₁} {C₁ : Type u₂} {C₂ : Type u₃} {C₃ : Type u₄}
  {D₀ D₁ D₂ D₃ : Type*} [Category.{v₁} C₀] [Category.{v₂} C₁] [Category.{v₃} C₂]
  [Category.{v₄} C₃] [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  {L₀ : C₀ ⥤ D₀} {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  {Ff : C₀ ⥤ C₁} {Fi : C₁ ⥤ C₂} {Fj : C₂ ⥤ C₃} {Fa : C₀ ⥤ C₂} {Fq : C₁ ⥤ C₃} {Fp : C₀ ⥤ C₃}
  {Gf : D₀ ⥤ D₁} {Gi : D₁ ⥤ D₂} {Gj : D₂ ⥤ D₃} {Ga : D₀ ⥤ D₂} {Gq : D₁ ⥤ D₃} {Gp : D₀ ⥤ D₃}

/-- The associativity pentagon of a descended composition isomorphism, at an object in the image
of the localization: if `κf, …, κp` exhibit six functors as descents along the localizations,
each `hE…` computes one of the four comparison isomorphisms at an object in the image of the
localization in terms of its counterpart `e…` upstairs, and `h` is the pentagon upstairs, then
the pentagon holds downstairs at that object. -/
private theorem compIso_lift_assoc_app (κf : L₀ ⋙ Gf ≅ Ff ⋙ L₁) (κi : L₁ ⋙ Gi ≅ Fi ⋙ L₂)
    (κj : L₂ ⋙ Gj ≅ Fj ⋙ L₃) (κa : L₀ ⋙ Ga ≅ Fa ⋙ L₂) (κq : L₁ ⋙ Gq ≅ Fq ⋙ L₃)
    (κp : L₀ ⋙ Gp ≅ Fp ⋙ L₃)
    (efi : Ff ⋙ Fi ≅ Fa) (eij : Fi ⋙ Fj ≅ Fq) (efq : Ff ⋙ Fq ≅ Fp) (eaj : Fa ⋙ Fj ≅ Fp)
    (Efi : Gf ⋙ Gi ≅ Ga) (Eij : Gi ⋙ Gj ≅ Gq) (Efq : Gf ⋙ Gq ≅ Gp) (Eaj : Ga ⋙ Gj ≅ Gp)
    (hEfi : ∀ X, Efi.hom.app (L₀.obj X) = Gi.map (κf.hom.app X) ≫ κi.hom.app (Ff.obj X) ≫
      L₂.map (efi.hom.app X) ≫ κa.inv.app X)
    (hEij : ∀ X, Eij.hom.app (L₁.obj X) = Gj.map (κi.hom.app X) ≫ κj.hom.app (Fi.obj X) ≫
      L₃.map (eij.hom.app X) ≫ κq.inv.app X)
    (hEfq : ∀ X, Efq.hom.app (L₀.obj X) = Gq.map (κf.hom.app X) ≫ κq.hom.app (Ff.obj X) ≫
      L₃.map (efq.hom.app X) ≫ κp.inv.app X)
    (hEaj : ∀ X, Eaj.hom.app (L₀.obj X) = Gj.map (κa.hom.app X) ≫ κj.hom.app (Fa.obj X) ≫
      L₃.map (eaj.hom.app X) ≫ κp.inv.app X)
    (h : Functor.whiskerLeft Ff eij.hom ≫ efq.hom =
      (Functor.associator Ff Fi Fj).inv ≫ Functor.whiskerRight efi.hom Fj ≫ eaj.hom)
    (X : C₀) :
    (Functor.whiskerLeft Gf Eij.hom ≫ Efq.hom).app (L₀.obj X) =
      ((Functor.associator Gf Gi Gj).inv ≫ Functor.whiskerRight Efi.hom Gj ≫
        Eaj.hom).app (L₀.obj X) := by
  have hpent := pentagon_app efi eij efq eaj h X
  have hκj := κj.hom.naturality (efi.hom.app X)
  have hnat := Eij.hom.naturality (κf.hom.app X)
  simp only [Functor.comp_map, Functor.comp_obj] at hpent hκj hnat
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Functor.comp_obj]
  have hL₃ : L₃.map (eij.hom.app (Ff.obj X)) ≫ L₃.map (efq.hom.app X) =
      L₃.map (Fj.map (efi.hom.app X)) ≫ L₃.map (eaj.hom.app X) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hpent]
  have key : Gj.map (Gi.map (κf.hom.app X)) ≫ Eij.hom.app (L₁.obj (Ff.obj X)) ≫
      Gq.map (κf.inv.app X) = Eij.hom.app (Gf.obj (L₀.obj X)) := by
    rw [← Category.assoc, hnat, Category.assoc, ← Gq.map_comp, Iso.hom_inv_id_app]; simp
  rw [← key, hEij, hEfq, hEfi, hEaj]
  simp only [Functor.map_comp, Category.assoc]
  erw [(κf.app X).inv_hom_id_map_assoc Gq, (κa.app X).inv_hom_id_map_assoc Gj]
  rw [Iso.inv_hom_id_app_assoc, reassoc_of% hκj, reassoc_of% hL₃]

end Lifted

end AbstractAssoc

section DerivedAssoc

variable {X Y Z : Scheme.{u}}

/-- The inverse of the derived composition isomorphism at the object represented by a complex:
the two exactness comparisons, the degreewise composition isomorphism, and the exactness
comparison for the composite. -/
public theorem etaleAbelianDerivedInverseImageCompIso'_inv_app_Qh (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (K : HomotopyCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)) :
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g fg hfg).inv.app
        (DerivedCategory.Qh.obj K) =
      (etaleAbelianDerivedInverseImage.{u, v} f).map
          ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.hom.app K) ≫
        (etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh.hom.app
          (((etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).symm
            (ComplexShape.up ℤ)).hom.app K) ≫
        (etaleAbelianInverseImage.{u, v} fg).mapDerivedCategoryFactorsh.inv.app K := by
  dsimp only [etaleAbelianDerivedInverseImageCompIso', Localization.liftNatIso]
  rw [Localization.liftNatTrans_app, liftingIso_single, liftingIso_comp]
  simp

/-- The associativity pentagon of the derived inverse image comparison: for `f : X₁ ⟶ X₀`,
`i : X₂ ⟶ X₁` and `j : X₃ ⟶ X₂` the two ways of comparing the derived inverse image along a
threefold composite with the composite of the three derived inverse images agree. -/
public lemma etaleAbelianDerivedInverseImageCompIso'_assoc {X₀ X₁ X₂ X₃ : Scheme.{u}}
    (f : X₁ ⟶ X₀) (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂) (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁)
    (hq : q = j ≫ i) (p : X₃ ⟶ X₀) (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a) :
    Functor.isoWhiskerLeft (etaleAbelianDerivedInverseImage.{u, v} f)
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} j i q hq).symm ≪≫
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} q f p hp₁).symm =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (etaleAbelianDerivedInverseImageCompIso'.{u, v} i f a ha).symm
            (etaleAbelianDerivedInverseImage.{u, v} j) ≪≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} j a p hp₂).symm := by
  have hdeg := compIso_mapHomotopyCategory_assoc
    (etaleAbelianInverseImageCompIso'.{u, v} i f a ha).symm
    (etaleAbelianInverseImageCompIso'.{u, v} j i q hq).symm
    (etaleAbelianInverseImageCompIso'.{u, v} q f p hp₁).symm
    (etaleAbelianInverseImageCompIso'.{u, v} j a p hp₂).symm
    (congrArg Iso.hom
      (etaleAbelianInverseImageCompIso'_assoc.{u, v} f i j a ha q hq p hp₁ hp₂))
    (ComplexShape.up ℤ)
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Qh
    (etaleAbelianQuasiIso.{u, v} X₀) fun K => ?_)
  exact compIso_lift_assoc_app
    (etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryFactorsh
    (etaleAbelianInverseImage.{u, v} i).mapDerivedCategoryFactorsh
    (etaleAbelianInverseImage.{u, v} j).mapDerivedCategoryFactorsh
    (etaleAbelianInverseImage.{u, v} a).mapDerivedCategoryFactorsh
    (etaleAbelianInverseImage.{u, v} q).mapDerivedCategoryFactorsh
    (etaleAbelianInverseImage.{u, v} p).mapDerivedCategoryFactorsh
    _ _ _ _ _ _ _ _
    (etaleAbelianDerivedInverseImageCompIso'_inv_app_Qh.{u, v} i f a ha)
    (etaleAbelianDerivedInverseImageCompIso'_inv_app_Qh.{u, v} j i q hq)
    (etaleAbelianDerivedInverseImageCompIso'_inv_app_Qh.{u, v} q f p hp₁)
    (etaleAbelianDerivedInverseImageCompIso'_inv_app_Qh.{u, v} j a p hp₂)
    hdeg K

end DerivedAssoc

/-! ### The derived base change maps of a tower of two squares compose -/

section DerivedPasting

variable {S T W X Y Z : Scheme.{u}}

/-- The derived base change comparisons of a tower of two commutative squares compose, as an
identity of 2-squares: the comparison attached to the outer rectangle is the vertical composite
of the comparisons attached to the two squares, whiskered with the derived inverse image
comparisons identifying the inverse image along a composite.  Every composite of two morphisms of
schemes is carried as a named morphism together with the equations naming it. -/
private theorem derivedBaseChangeComp_aux (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i)
    (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T) (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    (P₁ : Y ⟶ S) (hP₁e : P₁ = e ≫ g) (hP₁h : P₁ = h ≫ f)
    (P₂ : Z ⟶ X) (hP₂k : P₂ = k ≫ h) (hP₂j : P₂ = j ≫ i)
    (P : Z ⟶ S) (hPb : P = b ≫ g) (hPj : P = j ≫ a) (hPP₂ : P = P₂ ≫ f)
    (hPk : P = k ≫ P₁) :
    etaleAbelianDerivedBaseChange.{u, v} g a b j hyp =
      TwoSquare.whiskerLeft
        (TwoSquare.whiskerRight
          (TwoSquare.vComp (etaleAbelianDerivedBaseChange.{u, v} g f e h sq₁)
            (etaleAbelianDerivedBaseChange.{u, v} h i k j sq₂))
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} i f a ha).hom)
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} k e b hb).inv := by
  have hA1 := etaleAbelianDerivedInverseImageCompIso'_assoc.{u, v} f i j a ha P₂ hP₂j P hPP₂ hPj
  have hA2 := etaleAbelianDerivedInverseImageCompIso'_assoc.{u, v} f h k P₁ hP₁h P₂ hP₂k P
    hPP₂ hPk
  have hA3 := etaleAbelianDerivedInverseImageCompIso'_assoc.{u, v} g e k P₁ hP₁e b hb P hPb hPk
  have h1 := Stacks.CategoryTheory.isoRearrange
    (Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, v} f)
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} j i P₂ hP₂j).inv)
    (Functor.associator _ _ _)
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} P₂ f P hPP₂)
    (Functor.isoWhiskerRight (etaleAbelianDerivedInverseImageCompIso'.{u, v} i f a ha)
      (etaleAbelianDerivedInverseImage.{u, v} j))
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} j a P hPj)
    (congrArg Iso.hom hA1)
  have h2 := Stacks.CategoryTheory.isoRearrange₂
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} P₂ f P hPP₂).hom
    (Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, v} f)
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} k h P₂ hP₂k).hom)
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} k P₁ P hPk).hom
    (Functor.isoWhiskerRight (etaleAbelianDerivedInverseImageCompIso'.{u, v} h f P₁ hP₁h)
      (etaleAbelianDerivedInverseImage.{u, v} k))
    (Functor.associator _ _ _)
    (congrArg Iso.inv hA2)
  have h3 := Stacks.CategoryTheory.isoRearrange₃
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} b g P hPb).hom
    (Functor.isoWhiskerLeft (etaleAbelianDerivedInverseImage.{u, v} g)
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} k e b hb))
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} k P₁ P hPk).hom
    (Functor.whiskerRight (etaleAbelianDerivedInverseImageCompIso'.{u, v} e g P₁ hP₁e).hom
      (etaleAbelianDerivedInverseImage.{u, v} k))
    (Functor.associator _ _ _)
    (congrArg Iso.inv hA3)
  simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv] at h1 h2 h3
  rw [etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, v} g a b j P hPb hPj,
    etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, v} g f e h P₁ hP₁e hP₁h,
    etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, v} h i k j P₂ hP₂k hP₂j,
    ← mateEquiv_vcomp, ← Stacks.CategoryTheory.mateEquiv_whisker]
  refine congrArg (fun α => mateEquiv (etaleAbelianDerivedAdjunction.{u, v} g)
    (etaleAbelianDerivedAdjunction.{u, v} j) α) ?_
  simp only [etaleAbelianDerivedSquare, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.hComp, Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, h3]

/-- The derived étale base change comparisons of a tower of two commutative squares compose: for
squares `e ≫ g = h ≫ f` and `k ≫ h = j ≫ i` of schemes, with `a = i ≫ f` and
`b = k ≫ e` the composites along the two sides of the outer rectangle, the comparison
`f⁻¹ Rg_* ⟶ Rj_* b⁻¹` attached to the outer rectangle is `i⁻¹` of the comparison of the lower
square followed by the comparison of the upper square, read through the derived inverse image
comparisons for the two composites. -/
public theorem etaleAbelianDerivedBaseChange_comp_app (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i)
    (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T) (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleAbelianDerivedBaseChange.{u, v} g a b j hyp).app K =
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} i f a ha).hom.app
          ((etaleAbelianDerivedDirectImage.{u, v} g).obj K) ≫
        (etaleAbelianDerivedInverseImage.{u, v} i).map
          ((etaleAbelianDerivedBaseChange.{u, v} g f e h sq₁).app K) ≫
        (etaleAbelianDerivedBaseChange.{u, v} h i k j sq₂).app
          ((etaleAbelianDerivedInverseImage.{u, v} e).obj K) ≫
        (etaleAbelianDerivedDirectImage.{u, v} j).map
          ((etaleAbelianDerivedInverseImageCompIso'.{u, v} k e b hb).inv.app K) := by
  have hPk : b ≫ g = k ≫ e ≫ g := by rw [hb, Category.assoc]
  have hPP₂ : b ≫ g = (k ≫ h) ≫ f := by
    rw [hb, Category.assoc, sq₁, ← Category.assoc]
  rw [derivedBaseChangeComp_aux.{u, v} f g h e i j k sq₁ sq₂ a ha b hb hyp (e ≫ g) rfl sq₁
    (k ≫ h) rfl sq₂ (b ≫ g) rfl hyp hPP₂ hPk]
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp]

/-- Consider a tower of two commutative squares of schemes
```
W <--j-- Z
|i       |k
X <--h-- Y
|f       |e
S <--g-- T
```
and `K` in `D(T_étale)`.  If the base change maps `f⁻¹ Rg_* K ⟶ Rh_* e⁻¹ K` and
`i⁻¹ Rh_* e⁻¹ K ⟶ Rj_* k⁻¹ e⁻¹ K` of the two squares are isomorphisms, then so is the base change
map `(i ≫ f)⁻¹ Rg_* K ⟶ Rj_* (k ≫ e)⁻¹ K` of the outer rectangle. -/
@[stacks 0EZS "the derived half: for K in D(T_étale), if f⁻¹Rg_*K → Rh_*e⁻¹K and \
i⁻¹Rh_*e⁻¹K → Rj_*k⁻¹e⁻¹K are isomorphisms then (f∘i)⁻¹Rg_*K → Rj_*(e∘k)⁻¹K is an isomorphism; \
the R^q statement of the same tag is not covered here"]
public theorem etaleAbelianDerivedBaseChange_isIso_of_comp (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i)
    (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T) (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (h₁ : IsIso ((etaleAbelianDerivedBaseChange.{u, v} g f e h sq₁).app K))
    (h₂ : IsIso ((etaleAbelianDerivedBaseChange.{u, v} h i k j sq₂).app
      ((etaleAbelianDerivedInverseImage.{u, v} e).obj K))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} g a b j hyp).app K) := by
  rw [etaleAbelianDerivedBaseChange_comp_app.{u, v} f g h e i j k sq₁ sq₂ a ha b hb hyp K]
  infer_instance

end DerivedPasting

end Stacks.EtaleCohomology

end
