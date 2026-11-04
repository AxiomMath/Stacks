module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentation

/-!
# The total site of the simplicial object in sites attached to a simplicial object of a site

Let `U` be a simplicial object of a site `(C, J)` with fibre products. Stacks 09WL part (1),
in `StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObject`, makes the localizations
`C/U_n` into a simplicial object in sites: the morphism of sites attached to a simplex map
`φ : [m] ⟶ [n]` is represented by the base change functor `u_φ = Over.pullback f_φ`.

This file is part (2) and part (3) of that lemma.

Part (2) is the comparison of sites. The construction of Stacks 09WC applied to the structure
of part (1) is written out here as `CategoryTheory.SimplicialOver.PullbackTotal`: its objects
are the pairs `(n, V/U_n)`, a morphism `(n, V/U_n) ⟶ (m, W/U_m)` is a simplex map `φ` together
with a morphism `V ⟶ W ×_{U_m} U_n` over `U_n`, and composition is the one of Stacks 09WC,
`(φ, f) ≫ (ψ, g) = (φ ∘ ψ, u_φ(g) ∘ f)`, with the canonical comparison of base changes
inserted — chosen fibre products make `u_φ ⋙ u_ψ ≅ u_{ψ ∘ φ}` an isomorphism rather than the
equality the source writes, which is the same caveat as in part (1). The comparison
with `(C/U)_total`, the covariant Grothendieck construction of the localization functors, is
then an isomorphism of categories which is the identity on objects, and the covering families
of the two sites are the same families, both being the families lying in a single simplicial
degree.

Part (3) is the augmentation. For an augmentation `a : U → X`, base change along `a_0` is a
morphism of sites `C/U_0 → C/X` and its composites with the transitions of part (1) are
canonically isomorphic to base change along `a_n`, independently of the vertex `φ : [0] ⟶ [n]`
used; that is the condition of Stacks 0D6Z part (A), again up to the canonical comparison of
chosen fibre products rather than as an equality of functors. By Stacks 09W9 the morphism of
topoi of that morphism of sites is the one of the localization functor `j_{a_0} = Over.map
a_0`, which is cocontinuous, so `a_0` is also an augmentation in the sense of case (B) and
determines a morphism of topoi `a : Sh((C/U)_total) ⟶ Sh(C/X)`. That morphism of topoi is the
one above: its direct image is the direct image of the cocontinuous functor `V/U_n ↦ V/X` of
Stacks 09X8, and in fact the functor out of `(C/U)_total` which the augmentation determines is
that functor on the nose.

The localizations `C/U_n` also form a simplicial family of sites in case (B) of the
simplicial-site situation, through their cocontinuous transitions `j = Over.map f_φ`; the two
presentations have the same morphisms of topoi, and the generic total site of that family is the
site `(C/U)_total` on the nose.

## Main definitions

* `CategoryTheory.SimplicialOver.PullbackTotal`: the total category of Stacks 09WC for the
  structure of part (1), with its category structure.
* `CategoryTheory.SimplicialOver.totalComparison`: the comparison functor from `(C/U)_total`.
* `CategoryTheory.SimplicialOver.pullbackIota`: the inclusion of a simplicial degree.
* `CategoryTheory.SimplicialOver.pullbackTotalCoverings` and `.pullbackTotalTopology`: the
  covering families of that total site and the topology they generate.
* `CategoryTheory.SimplicialOver.augmentationApp`: the component `a_n : U_n ⟶ X` of an
  augmentation.
* `CategoryTheory.SimplicialOver.simplicialSite` and `.situation`: the localizations `C/U_n`
  as a simplicial family of sites in case (B), and as a simplicial-site situation.
* `CategoryTheory.SimplicialOver.augmentation`: the augmentation of that family given by
  `a_0`, and `CategoryTheory.SimplicialOver.augmentationFunctor` the functor `V/U_n ↦ V/X` of
  Stacks 09X8 out of `(C/U)_total`.
* `CategoryTheory.SimplicialOver.augmentationMorphismOfTopoi`: the morphism of topoi
  `a : Sh((C/U)_total) ⟶ Sh(C/X)` which the augmentation gives.

## Main results

* `CategoryTheory.SimplicialOver.totalHomEquiv_id` and `.totalHomEquiv_comp`: the bijection on
  morphisms of `CategoryTheory.SimplicialOver.totalHomEquiv` carries the identity and the
  composition of `(C/U)_total` to those of Stacks 09WC.
* `CategoryTheory.SimplicialOver.totalComparisonEquivalence`: **part (2)**, the two total
  categories are isomorphic, by a comparison which is the identity on objects.
* `CategoryTheory.SimplicialOver.pullbackTotalCoverings_iff`: **part (2)**, the two total
  sites have the same covering families.
* `CategoryTheory.SimplicialOver.totalTopology_eq`: **part (2)**, the total site of the
  generic construction applied to the family `n ↦ C/U_n` is `(C/U)_total`.
* `CategoryTheory.SimplicialOver.hasCoverPullbacks_overMap`: property P of Stacks 09W7 for
  the localization functors.
* `CategoryTheory.SimplicialOver.isMorphismOfSites_augmentationPullback` and
  `.augmentationVertexCompat`: **part (3)**, `a_0` is an augmentation in the sense of
  Stacks 0D6Z part (A).
* `CategoryTheory.SimplicialOver.ι_comp_augmentationFunctor`: the functor
  `augmentationFunctor` is `V/U_n ↦ V/X`, that is, in each simplicial degree the localization
  functor along `a_n`.
* `CategoryTheory.SimplicialOver.augmentationMorphismOfTopoi_pushforward`: **part (3)**, the
  morphism of topoi which the augmentation gives is the one above — its direct image is the
  direct image of `V/U_n ↦ V/X`.
* `CategoryTheory.SimplicialOver.augmentationSheafPushforwardIso`: in each simplicial degree
  base change along `a_n` and the localization functor `Over.map a_n` give the same morphism of
  topoi.

## References

* [Stacks Project, Tag 09WL](https://stacks.math.columbia.edu/tag/09WL)
* [Stacks Project, Tag 09W9](https://stacks.math.columbia.edu/tag/09W9)
* [Stacks Project, Tag 09WC](https://stacks.math.columbia.edu/tag/09WC)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory

namespace Adjunction

/-- Transposing a morphism precomposed with a natural transformation of left adjoints is
transposing it and postcomposing with the conjugate transformation of right adjoints. -/
theorem homEquiv_conjugateEquiv {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {X : A} {Y : B} (u : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (α.app X ≫ u) =
      adj₁.homEquiv X Y u ≫ (conjugateEquiv adj₁ adj₂ α).app Y := by
  have h := unit_conjugateEquiv adj₁ adj₂ α X
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← h, Category.assoc, ← (conjugateEquiv adj₁ adj₂ α).naturality u, ← Category.assoc]

end Adjunction

namespace Over

variable {C : Type u} [SmallCategory C] [HasPullbacks C]

/-- Transposing along `Over.map (f ≫ g) ⊣ Over.pullback (f ≫ g)` is transposing twice,
followed by the canonical comparison of base changes. -/
theorem homEquiv_mapComp_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Over X) (W : Over Z)
    (u : (Over.map f ⋙ Over.map g).obj V ⟶ W) :
    (Over.mapPullbackAdj (f ≫ g)).homEquiv V W ((Over.mapComp f g).hom.app V ≫ u) =
      (Over.mapPullbackAdj f).homEquiv V _ ((Over.mapPullbackAdj g).homEquiv _ W u) ≫
        (Over.pullbackComp f g).inv.app W := by
  rw [Adjunction.homEquiv_conjugateEquiv ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g)) (Over.mapComp f g).hom u, Adjunction.comp_homEquiv]
  rfl

/-- Transposing along `Over.map (𝟙 X) ⊣ Over.pullback (𝟙 X)` a morphism precomposed with the
canonical identification of `Over.map (𝟙 X)` with the identity functor is that morphism
followed by the canonical comparison of base change along the identity with the identity
functor. -/
theorem homEquiv_mapId (X : C) (V W : Over X) (g : V ⟶ W) :
    (Over.mapPullbackAdj (𝟙 X)).homEquiv V W ((Over.mapId X).hom.app V ≫ g) =
      g ≫ (Over.pullbackId (X := X)).inv.app W := by
  have h := Adjunction.homEquiv_conjugateEquiv (Adjunction.id (C := Over X))
    (Over.mapPullbackAdj (𝟙 X)) (Over.mapId X).hom g
  have hid : (Adjunction.id (C := Over X)).homEquiv V W g = g := by
    rw [Adjunction.homEquiv_unit]; simp
  rw [hid] at h
  rw [h]
  rfl

end Over

namespace SimplicialOver

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : SimplicialObject C)
  [HasPullbacks C]

/-- The comparison `u_{𝟙} ≅ 𝟭` of `pullbackMapId`, for an identity of the opposite simplex
category. -/
def pullbackMapId' (n : SimplexCategoryᵒᵖ) :
    Over.pullback (U.map (𝟙 n)) ≅ 𝟭 (Over (U.obj n)) :=
  pullbackMapId U n.unop

/-- The comparison `u_{α ≫ β} ≅ u_β ⋙ u_α` of `pullbackMapComp`, for maps of the opposite
simplex category. -/
def pullbackMapComp' {l m n : SimplexCategoryᵒᵖ} (α : l ⟶ m) (β : m ⟶ n) :
    Over.pullback (U.map (α ≫ β)) ≅ Over.pullback (U.map β) ⋙ Over.pullback (U.map α) :=
  pullbackMapComp U β.unop α.unop

variable {U}

/-- For a morphism `m` which is the identity, transposing a morphism precomposed with the
canonical identification of `Over.map m` with the identity functor is that morphism followed
by the canonical comparison of base change along `m` with the identity functor. -/
theorem homEquiv_eqToHom_id' {X : C} {m : X ⟶ X} (hm : m = 𝟙 X) (V W : Over X)
    (e : (Over.map m).obj V = V) (g : V ⟶ W) :
    (Over.mapPullbackAdj m).homEquiv V W (eqToHom e ≫ g) =
      g ≫ (pullbackCongr hm ≪≫ Over.pullbackId).inv.app W := by
  subst hm
  have h₁ : eqToHom e = (Over.mapId X).hom.app V := by ext; simp
  rw [h₁, Over.homEquiv_mapId]
  simp [pullbackCongr]

/-- The case of `homEquiv_eqToHom_id'` of the identity morphism. -/
theorem homEquiv_eqToHom_id {X : C} {m : X ⟶ X} (hm : m = 𝟙 X) (V : Over X)
    (e : (Over.map m).obj V = V) :
    (Over.mapPullbackAdj m).homEquiv V V (eqToHom e) =
      (pullbackCongr hm ≪≫ Over.pullbackId).inv.app V := by
  simpa only [Category.comp_id, Category.id_comp] using homEquiv_eqToHom_id' hm V V e (𝟙 V)

/-- Transposing along `Over.map h ⊣ Over.pullback h`, for a morphism `h` which is a composite
`f ≫ g`, is transposing twice followed by the canonical comparison of base changes. -/
theorem homEquiv_eqToHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (hh : h = f ≫ g)
    (V : Over X) (W : Over Z) (u : (Over.map f ⋙ Over.map g).obj V ⟶ W)
    (e : (Over.map h).obj V = (Over.map f ⋙ Over.map g).obj V) :
    (Over.mapPullbackAdj h).homEquiv V W (eqToHom e ≫ u) =
      (Over.mapPullbackAdj f).homEquiv V _ ((Over.mapPullbackAdj g).homEquiv _ W u) ≫
        (pullbackCongr hh ≪≫ Over.pullbackComp f g).inv.app W := by
  subst hh
  have h₁ : eqToHom e = (Over.mapComp f g).hom.app V := by ext; simp
  rw [h₁, Over.homEquiv_mapComp_comp]
  simp [pullbackCongr]

/-- `homEquiv_eqToHom_comp` for a morphism presented as `u_g(u₁) ∘ u₂`. -/
theorem homEquiv_eqToHom_comp' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (hh : h = f ≫ g)
    (V : Over X) (W' : Over Y) (W : Over Z)
    (u₁ : (Over.map f).obj V ⟶ W') (u₂ : (Over.map g).obj W' ⟶ W)
    (e : (Over.map h).obj V = (Over.map f ⋙ Over.map g).obj V) :
    (Over.mapPullbackAdj h).homEquiv V W (eqToHom e ≫ (Over.map g).map u₁ ≫ u₂) =
      (Over.mapPullbackAdj f).homEquiv V W' u₁ ≫
        (Over.pullback f).map ((Over.mapPullbackAdj g).homEquiv W' W u₂) ≫
          (pullbackCongr hh ≪≫ Over.pullbackComp f g).inv.app W := by
  rw [homEquiv_eqToHom_comp f g hh V W ((Over.map g).map u₁ ≫ u₂) e,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Category.assoc]

variable (U)

/-- The total category of the construction of Stacks 09WC applied to the simplicial object in
sites of Stacks 09WL part (1): an object is an object `V/U_n` of one of the localizations. -/
structure PullbackTotal where
  /-- The simplicial degree. -/
  base : SimplexCategoryᵒᵖ
  /-- The object of the localization `C/U_n` in that degree. -/
  fiber : Over (U.obj base)

namespace PullbackTotal

variable {U}

/-- The object of `(C/U)_total` with the same degree and the same object of the localization. -/
abbrev toGrothendieck (A : PullbackTotal U) : Grothendieck (slices U) :=
  ⟨A.base, A.fiber⟩

omit [HasPullbacks C] in
/-- The degree of `A.toGrothendieck` is the degree of `A`. -/
@[simp]
theorem toGrothendieck_base (A : PullbackTotal U) : A.toGrothendieck.base = A.base := rfl

omit [HasPullbacks C] in
/-- The object of the localization underlying `A.toGrothendieck` is the one of `A`. -/
@[simp]
theorem toGrothendieck_fiber (A : PullbackTotal U) : A.toGrothendieck.fiber = A.fiber := rfl

variable (U)

/-- A morphism `(n, V/U_n) ⟶ (m, W/U_m)` of the total category of Stacks 09WC: a simplex map
`φ : [m] ⟶ [n]` together with a morphism `V ⟶ W ×_{U_m} U_n` of `C/U_n`. -/
def Hom (A B : PullbackTotal U) : Type u :=
  Σ α : A.base ⟶ B.base, (A.fiber ⟶ (Over.pullback (U.map α)).obj B.fiber)

/-- The identity of Stacks 09WC: the identity simplex map together with the canonical
comparison of base change along `f_{𝟙}` with the identity functor. -/
def id' (A : PullbackTotal U) : Hom U A A :=
  ⟨𝟙 A.base, (pullbackMapId' U A.base).inv.app A.fiber⟩

/-- The composition of Stacks 09WC: `(φ, f) ≫ (ψ, g) = (φ ∘ ψ, u_φ(g) ∘ f)`, with the
canonical comparison `u_φ ⋙ u_ψ ≅ u_{ψ ∘ φ}` of base changes inserted, as chosen fibre
products make that comparison an isomorphism rather than an equality. -/
def comp' {A B D : PullbackTotal U} (f : Hom U A B) (g : Hom U B D) : Hom U A D :=
  ⟨f.1 ≫ g.1, f.2 ≫ (Over.pullback (U.map f.1)).map g.2 ≫
    (pullbackMapComp' U f.1 g.1).inv.app D.fiber⟩

end PullbackTotal

/-- **Stacks 09WL part (2).** The bijection of `totalHomEquiv` takes the identity of
`(C/U)_total` to the identity of the total category of Stacks 09WC. -/
theorem totalHomEquiv_id (A : PullbackTotal U) :
    totalHomEquiv U A.toGrothendieck A.toGrothendieck (𝟙 A.toGrothendieck) =
      PullbackTotal.id' U A := by
  exact Sigma.ext rfl (heq_of_eq (homEquiv_eqToHom_id (U.map_id A.base) A.fiber
    (by simp only [U.map_id, Over.mapId_eq, Functor.id_obj])))

/-- **Stacks 09WL part (2).** The bijection of `totalHomEquiv` takes composition in
`(C/U)_total` to the composition of Stacks 09WC. -/
theorem totalHomEquiv_comp {A B D : PullbackTotal U}
    (f : A.toGrothendieck ⟶ B.toGrothendieck) (g : B.toGrothendieck ⟶ D.toGrothendieck) :
    totalHomEquiv U A.toGrothendieck D.toGrothendieck (f ≫ g) =
      PullbackTotal.comp' U (totalHomEquiv U A.toGrothendieck B.toGrothendieck f)
        (totalHomEquiv U B.toGrothendieck D.toGrothendieck g) := by
  exact Sigma.ext rfl (heq_of_eq (homEquiv_eqToHom_comp' (U.map f.base) (U.map g.base)
    (U.map_comp f.base g.base) A.fiber B.fiber D.fiber f.fiber g.fiber
    (by simp only [U.map_comp, Over.mapComp_eq, Functor.comp_obj])))

namespace PullbackTotal

/-- The identity of Stacks 09WC is a left unit for its composition. -/
theorem id'_comp' {A B : PullbackTotal U} (f : Hom U A B) : comp' U (id' U A) f = f := by
  obtain ⟨f, rfl⟩ := (totalHomEquiv U A.toGrothendieck B.toGrothendieck).surjective f
  rw [← totalHomEquiv_id, ← totalHomEquiv_comp, Category.id_comp]

/-- The identity of Stacks 09WC is a right unit for its composition. -/
theorem comp'_id' {A B : PullbackTotal U} (f : Hom U A B) : comp' U f (id' U B) = f := by
  obtain ⟨f, rfl⟩ := (totalHomEquiv U A.toGrothendieck B.toGrothendieck).surjective f
  rw [← totalHomEquiv_id, ← totalHomEquiv_comp, Category.comp_id]

/-- The composition of Stacks 09WC is associative. -/
theorem comp'_assoc {A B D E : PullbackTotal U} (f : Hom U A B) (g : Hom U B D)
    (h : Hom U D E) : comp' U (comp' U f g) h = comp' U f (comp' U g h) := by
  obtain ⟨f, rfl⟩ := (totalHomEquiv U A.toGrothendieck B.toGrothendieck).surjective f
  obtain ⟨g, rfl⟩ := (totalHomEquiv U B.toGrothendieck D.toGrothendieck).surjective g
  obtain ⟨h, rfl⟩ := (totalHomEquiv U D.toGrothendieck E.toGrothendieck).surjective h
  rw [← totalHomEquiv_comp, ← totalHomEquiv_comp, ← totalHomEquiv_comp, ← totalHomEquiv_comp,
    Category.assoc]

/-- **Stacks 09WL part (2).** The total category of the construction of Stacks 09WC applied to
the simplicial object in sites of part (1): the objects are the `V/U_n`, a morphism
`(n, V/U_n) ⟶ (m, W/U_m)` is a simplex map `φ : [m] ⟶ [n]` together with a morphism
`V ⟶ W ×_{U_m} U_n` over `U_n`, and composition is the one of Stacks 09WC. -/
instance : Category (PullbackTotal U) where
  Hom := Hom U
  id := id' U
  comp := comp' U
  id_comp := id'_comp' U
  comp_id := comp'_id' U
  assoc := comp'_assoc U

end PullbackTotal

/-- **Stacks 09WL part (2).** The comparison functor from `(C/U)_total` to the total category
of Stacks 09WC: it is the identity on objects, and on morphisms it is the bijection of
`totalHomEquiv`, which is functorial by `totalHomEquiv_id` and `totalHomEquiv_comp`. -/
def totalComparison : Grothendieck (slices U) ⥤ PullbackTotal U where
  obj A := ⟨A.base, A.fiber⟩
  map {A B} f := totalHomEquiv U A B f
  map_id A := totalHomEquiv_id U ⟨A.base, A.fiber⟩
  map_comp {A' B' D'} f g :=
    totalHomEquiv_comp U (A := ⟨A'.base, A'.fiber⟩) (B := ⟨B'.base, B'.fiber⟩)
      (D := ⟨D'.base, D'.fiber⟩) f g

/-- The comparison functor is faithful: on morphisms it is a bijection. -/
instance : (totalComparison U).Faithful where
  map_injective {A B} := (totalHomEquiv U A B).injective

/-- The comparison functor is full: on morphisms it is a bijection. -/
instance : (totalComparison U).Full where
  map_surjective {A B} := (totalHomEquiv U A B).surjective

/-- The comparison functor is surjective on objects. -/
instance : (totalComparison U).EssSurj where
  mem_essImage A := ⟨A.toGrothendieck, ⟨Iso.refl _⟩⟩

/-- The comparison functor is an equivalence: it is fully faithful and essentially
surjective. -/
instance : (totalComparison U).IsEquivalence where

/-- **Stacks 09WL part (2).** The construction of Stacks 09WC applied to the simplicial object
in sites of part (1) reproduces the category `(C/U)_total`: the comparison functor, which is
the identity on objects and the bijection `totalHomEquiv` on morphisms, is an isomorphism of
categories. -/
@[stacks 09WL "part (2), the comparison of the two total categories"]
def totalComparisonEquivalence : Grothendieck (slices U) ≌ PullbackTotal U :=
  (totalComparison U).asEquivalence

/-- The inclusion of the localization of degree `n` into the total category of Stacks 09WC: it
sends `V` to the object `(n, V)` and a morphism `g` of `C/U_n` to the morphism of the total
category over the identity simplex map which `g` determines. -/
def pullbackIota (n : SimplexCategoryᵒᵖ) : Over (U.obj n) ⥤ PullbackTotal U :=
  Grothendieck.ι (slices U) n ⋙ totalComparison U

/-- The inclusion of degree `n` sends `V` to the object `(n, V)`. -/
@[simp]
theorem pullbackIota_obj (n : SimplexCategoryᵒᵖ) (V : Over (U.obj n)) :
    (pullbackIota U n).obj V = ⟨n, V⟩ :=
  rfl

/-- The inclusion of a degree sends a morphism of `C/U_n` to the morphism of the total category
of Stacks 09WC lying over the identity simplex map which it determines. -/
theorem pullbackIota_map (n : SimplexCategoryᵒᵖ) {V W : Over (U.obj n)} (g : V ⟶ W) :
    (pullbackIota U n).map g = ⟨𝟙 n, g ≫ (pullbackMapId' U n).inv.app W⟩ :=
  Sigma.ext rfl (heq_of_eq (homEquiv_eqToHom_id' (U.map_id n) V W
    (by simp only [U.map_id, Over.mapId_eq, Functor.id_obj]) g))

/-- The covering families of the total site of Stacks 09WC: a family covers exactly when it
lies in a single simplicial degree and covers there. -/
def pullbackTotalCoverings : Covering.{u, u, u} (PullbackTotal U) → Prop := fun 𝒱 ↦
  ∃ E : PreZeroHypercover.{u} 𝒱.1.fiber,
    sliceCoverings J U 𝒱.1.base ⟨𝒱.1.fiber, E⟩ ∧ 𝒱.2 = E.map (pullbackIota U 𝒱.1.base)

/-- The topology of the total site of Stacks 09WC, generated by the covering families lying in
a single simplicial degree. -/
def pullbackTotalTopology : GrothendieckTopology (PullbackTotal U) :=
  topologyOfCoverings (pullbackTotalCoverings J U)

/-- **Stacks 09WL part (2).** The two sites have the same covering families: a family of the
total category of Stacks 09WC is covering exactly when it is the image under the comparison of
a covering family of `(C/U)_total`. Both topologies are generated by these families. -/
@[stacks 09WL "part (2), the coverings of the two total sites agree"]
theorem pullbackTotalCoverings_iff (𝒱 : Covering.{u, u, u} (PullbackTotal U)) :
    pullbackTotalCoverings J U 𝒱 ↔
      ∃ 𝒰 : Covering.{u, u, u} (Grothendieck (slices U)),
        SimplicialCoverings.total (slices U) (sliceCoverings J U) 𝒰 ∧
          𝒱 = ⟨(totalComparison U).obj 𝒰.1, 𝒰.2.map (totalComparison U)⟩ := by
  constructor
  · rintro ⟨E, hE, hF⟩
    refine ⟨⟨𝒱.1.toGrothendieck, E.map (Grothendieck.ι (slices U) 𝒱.1.base)⟩, ⟨E, hE, rfl⟩, ?_⟩
    exact Sigma.ext rfl (heq_of_eq hF)
  · rintro ⟨𝒰, ⟨E, hE, hG⟩, h⟩
    subst h
    exact ⟨E, hE, by rw [hG]; rfl⟩

/-! ### `(C/U)_total` as the total site of a simplicial family of sites -/

omit [HasPullbacks C] in
/-- The covering families of `C/U_n` are the covering families of the localized topology. -/
theorem sliceCoverings_eq (n : SimplexCategoryᵒᵖ) :
    sliceCoverings J U n =
      fun 𝒰 : Covering.{u, u, u} (Over (U.obj n)) ↦
        𝒰.2.presieve₀ ∈ (J.over (U.obj n)).toCoverage 𝒰.1 :=
  rfl

omit [HasPullbacks C] in
/-- The covering families of `C/U_n` generate the localized topology. -/
theorem topologyOfCoverings_sliceCoverings (n : SimplexCategoryᵒᵖ) :
    topologyOfCoverings (sliceCoverings J U n) = J.over (U.obj n) := by
  rw [sliceCoverings_eq]
  exact GrothendieckTopology.topologyOfCoverings_coverings _

/-- The covering families of `C/U_n` satisfy the site axioms. -/
theorem isSite_sliceCoverings (n : SimplexCategoryᵒᵖ) : IsSite (sliceCoverings J U n) := by
  rw [sliceCoverings_eq]
  exact GrothendieckTopology.isSite_coverings _

omit [HasPullbacks C] in
/-- The transition functor `j = Over.map f_φ` of a simplex map is cocontinuous for the
topologies generated by the covering families of the two degrees. -/
theorem isCocontinuous_sliceCoverings {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    (Over.map (U.map α)).IsCocontinuous (topologyOfCoverings (sliceCoverings J U m))
      (topologyOfCoverings (sliceCoverings J U n)) := by
  rw [topologyOfCoverings_sliceCoverings, topologyOfCoverings_sliceCoverings]
  infer_instance

/-- **Property P of Stacks 09W7** for the localization functor `j = Over.map f : C/A ⥤ C/B`: a
covering family of `C/B` has, along a morphism `j(V) ⟶ W` out of the image of an object of
`C/A`, base changes which are representable in `C/A`, and they form a covering family there. -/
theorem hasCoverPullbacks_overMap {A B : C} (f : A ⟶ B) :
    Functor.HasCoverPullbacks (Over.map f)
      (fun 𝒰 : Covering.{u, u, u} (Over A) ↦ 𝒰.2.presieve₀ ∈ (J.over A).toCoverage 𝒰.1)
      (fun 𝒱 : Covering.{u, u, u} (Over B) ↦ 𝒱.2.presieve₀ ∈ (J.over B).toCoverage 𝒱.1) := by
  classical
  intro 𝒱 h𝒱 V g
  refine ⟨fun i ↦ Limits.pullback ((Over.mapPullbackAdj f).homEquiv V 𝒱.1 g)
      ((Over.pullback f).map (𝒱.2.f i)),
    fun i ↦ Limits.pullback.fst _ _,
    fun i ↦ ((Over.mapPullbackAdj f).homEquiv _ (𝒱.2.X i)).symm (Limits.pullback.snd _ _),
    fun i ↦ ⟨?_, ?_⟩, ?_⟩
  · change (Over.map f).map (Limits.pullback.fst _ _) ≫ g =
      ((Over.mapPullbackAdj f).homEquiv _ (𝒱.2.X i)).symm (Limits.pullback.snd _ _) ≫ 𝒱.2.f i
    apply ((Over.mapPullbackAdj f).homEquiv _ 𝒱.1).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
    exact Limits.pullback.condition
  · change ∀ (T : Over A) (a : T ⟶ V) (b : (Over.map f).obj T ⟶ 𝒱.2.X i),
      (Over.map f).map a ≫ g = b ≫ 𝒱.2.f i →
        ∃! l : T ⟶ Limits.pullback ((Over.mapPullbackAdj f).homEquiv V 𝒱.1 g)
            ((Over.pullback f).map (𝒱.2.f i)),
          l ≫ Limits.pullback.fst _ _ = a ∧
            (Over.map f).map l ≫ ((Over.mapPullbackAdj f).homEquiv _ (𝒱.2.X i)).symm
              (Limits.pullback.snd _ _) = b
    intro T a b h
    have h' : a ≫ (Over.mapPullbackAdj f).homEquiv V 𝒱.1 g =
        (Over.mapPullbackAdj f).homEquiv T (𝒱.2.X i) b ≫ (Over.pullback f).map (𝒱.2.f i) := by
      rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right, h]
    refine ⟨Limits.pullback.lift a _ h', ⟨Limits.pullback.lift_fst _ _ _, ?_⟩, ?_⟩
    · apply ((Over.mapPullbackAdj f).homEquiv _ (𝒱.2.X i)).injective
      rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, Limits.pullback.lift_snd]
    · rintro l ⟨hl₁, hl₂⟩
      have hl₂' := congrArg ((Over.mapPullbackAdj f).homEquiv T (𝒱.2.X i)) hl₂
      rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply] at hl₂'
      exact Limits.pullback.hom_ext (by rw [hl₁, Limits.pullback.lift_fst])
        (by rw [hl₂', Limits.pullback.lift_snd])
  · have h𝒱' : Sieve.generate 𝒱.2.presieve₀ ∈ J.over B 𝒱.1 :=
      (GrothendieckTopology.mem_toCoverage_iff _).1 h𝒱
    have hpush : (Sieve.generate 𝒱.2.presieve₀).functorPushforward (Over.pullback f) ∈
        J.over A ((Over.pullback f).obj 𝒱.1) :=
      (GrothendieckTopology.coverPreserving_overPullback J f).cover_preserve h𝒱'
    have hle : (Sieve.generate 𝒱.2.presieve₀).functorPushforward (Over.pullback f) ≤
        Sieve.generate (Presieve.ofArrows (fun i ↦ (Over.pullback f).obj (𝒱.2.X i))
          (fun i ↦ (Over.pullback f).map (𝒱.2.f i))) := by
      rintro Z v ⟨Z', h, k, ⟨Z'', w, fi, hfi, rfl⟩, rfl⟩
      obtain ⟨i⟩ := hfi
      exact ⟨(Over.pullback f).obj (𝒱.2.X i), k ≫ (Over.pullback f).map w,
        (Over.pullback f).map (𝒱.2.f i), Presieve.ofArrows.mk i, by
          simp only [Functor.map_comp, Category.assoc]⟩
    have hcovY : Presieve.ofArrows (fun i ↦ (Over.pullback f).obj (𝒱.2.X i))
        (fun i ↦ (Over.pullback f).map (𝒱.2.f i)) ∈
          (J.over A).toPrecoverage ((Over.pullback f).obj 𝒱.1) := by
      rw [GrothendieckTopology.mem_toPrecoverage_iff]
      exact (J.over A).superset_covering hle hpush
    change Presieve.ofArrows _ _ ∈ (J.over A).toCoverage V
    rw [GrothendieckTopology.mem_toCoverage_iff, ← GrothendieckTopology.mem_toPrecoverage_iff]
    exact Precoverage.IsStableUnderBaseChange.mem_coverings_of_isPullback
      (J := (J.over A).toPrecoverage) (fun i ↦ (Over.pullback f).map (𝒱.2.f i)) hcovY
      ((Over.mapPullbackAdj f).homEquiv V 𝒱.1 g) _ _
      fun i ↦ IsPullback.of_hasPullback _ _

/-- The simplicial family of sites `n ↦ C/U_n` of Stacks 09WL part (1), in case (B) of the
simplicial-site situation: the transition functors are the localization functors
`j = Over.map f_φ`, which are cocontinuous and have property P of Stacks 09W7. By Stacks 09W9
they induce the same morphisms of topoi as the morphisms of sites of part (1), so this is the
same simplicial family of sites, presented by its cocontinuous transitions. -/
def simplicialSite : CocontinuousSimplicialSite.{u} where
  underlying := slices U
  coverage := sliceCoverings J U
  isSite n := isSite_sliceCoverings J U n
  isCocontinuous {_ _} α := isCocontinuous_sliceCoverings J U α
  hasCoverPullbacks {_ _} α := hasCoverPullbacks_overMap J (U.map α)

/-- The simplicial family of sites `n ↦ C/U_n`, read as a simplicial-site situation. -/
def situation : SimplicialSiteSituation.{u} := ⟨Sum.inr (simplicialSite J U)⟩

/-- The site in simplicial degree `n` of that situation is the localization `C/U_n`. -/
theorem componentTopology_eq (n : SimplexCategory) :
    (situation J U).componentTopology n = J.over (U.obj (op n)) :=
  topologyOfCoverings_sliceCoverings J U (op n)

/-- The total category of that situation is the category `(C/U)_total`. -/
theorem totalCategory_eq : (situation J U).totalCategory = Cat.of (Grothendieck (slices U)) :=
  rfl

/-- **Stacks 09WL part (2).** The total site of that situation is the site `(C/U)_total`: the
generic construction of the total site, applied to the simplicial family of sites `n ↦ C/U_n`,
gives the category `(C/U)_total` and the topology `totalTopology` on the nose. -/
@[stacks 09WL "part (2), the generic total site is (C/U)_total"]
theorem totalTopology_eq : (situation J U).totalTopology = SimplicialOver.totalTopology J U :=
  rfl

section Augmentation

variable {X : C} (a : U ⟶ (SimplicialObject.const C).obj X)

/-- The component `a_n : U_n ⟶ X` of an augmentation `a : U → X`. -/
def augmentationApp (n : SimplexCategoryᵒᵖ) : U.obj n ⟶ X :=
  a.app n

omit [HasPullbacks C] in
/-- The augmentation `a : U → X` satisfies `f_φ ≫ a_m = a_n`, that is, every structure map of
`U` is a morphism over `X`. -/
theorem augmentationApp_naturality {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    U.map α ≫ augmentationApp U a n = augmentationApp U a m := by
  simp [augmentationApp]

/-- **Stacks 09WL part (3).** For an augmentation `a : U → X`, base change along
`a_0 : U_0 ⟶ X` is continuous with exact pullback on sheaves of sets, that is, it represents a
morphism of sites `a_0 : C/U_0 → C/X`. This is Stacks 09W9 applied to `a_0`. -/
@[stacks 09WL "part (3), a_0 is a morphism of sites"]
theorem isMorphismOfSites_augmentationPullback :
    (Over.pullback (augmentationApp U a (op (SimplexCategory.mk 0)))).IsMorphismOfSites
      (J.over X) (J.over (U.obj (op (SimplexCategory.mk 0)))) :=
  StacksRelocalization.isMorphismOfSites_overPullback J _

/-- Base change along `a_n` followed by base change along `f_φ` is base change along `a_m`, by
the canonical comparison of chosen fibre products: this is the composition comparison of
`CategoryTheory.Over.pullbackComp` read through `f_φ ≫ a_n = a_m`. -/
def augmentationVertexIso {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    Over.pullback (augmentationApp U a n) ⋙ Over.pullback (U.map α) ≅
      Over.pullback (augmentationApp U a m) :=
  (pullbackCongr (augmentationApp_naturality U a α).symm ≪≫
    Over.pullbackComp (U.map α) (augmentationApp U a n)).symm

/-- **Stacks 09WL part (3).** The functor `u_0 = Over.pullback a_0` representing the
augmentation satisfies the compatibility of Stacks 0D6Z part (A): the composites `u_φ ∘ u_0`
for the vertices `φ : [0] ⟶ [n]` of a simplicial degree agree, both being canonically
isomorphic to base change along `a_n`. Chosen fibre products make this an isomorphism rather
than the equality of functors the source writes, exactly as in part (1). -/
@[stacks 09WL "part (3), the vertex compatibility of the augmentation"]
def augmentationVertexCompat (n : SimplexCategory) (φ ψ : SimplexCategory.mk 0 ⟶ n) :
    Over.pullback (augmentationApp U a (op (SimplexCategory.mk 0))) ⋙
        Over.pullback (U.map φ.op) ≅
      Over.pullback (augmentationApp U a (op (SimplexCategory.mk 0))) ⋙
        Over.pullback (U.map ψ.op) :=
  augmentationVertexIso U a φ.op ≪≫ (augmentationVertexIso U a ψ.op).symm

/-- In simplicial degree `n` the morphism of topoi of the morphism of sites given by base change
along `a_n` is the one of the localization functor `j = Over.map a_n`: the two have the same
direct image. This is Stacks 09W9 applied to `a_n`, the same comparison that part (1) makes for
the transitions `f_φ`. -/
def augmentationSheafPushforwardIso (n : SimplexCategoryᵒᵖ) :
    (Over.map (augmentationApp U a n)).sheafPushforwardCocontinuous (Type u)
        (J.over (U.obj n)) (J.over X) ≅
      (Over.pullback (augmentationApp U a n)).sheafPushforwardContinuous (Type u) (J.over X)
        (J.over (U.obj n)) :=
  StacksRelocalization.sheafPushforwardOverMapIso J (augmentationApp U a n)

/-! ### The augmentation and its morphism of topoi out of the total topos -/

/-- The functor `j_{a_c} = Over.map a_c : C/U_c ⥤ C/X` of simplicial degree `c`. -/
def augmentationFibre (c : SimplexCategoryᵒᵖ) : ((slices U).obj c : Cat.{u, u}) ⥤ Over X :=
  Over.map (augmentationApp U a c)

omit [HasPullbacks C] in
/-- Relocalizing along a simplex map and then localizing along `a_c` is localizing along `a_b`:
the transition functor of `α : b ⟶ c` followed by `j_{a_c}` is `j_{a_b}`, because
`f_α ≫ a_c = a_b`. -/
theorem slicesMap_comp_augmentationFibre {b c : SimplexCategoryᵒᵖ} (α : b ⟶ c) :
    ((slices U).map α).toFunctor ⋙ augmentationFibre U a c = augmentationFibre U a b := by
  change Over.map (U.map α) ⋙ Over.map (augmentationApp U a c) = Over.map (augmentationApp U a b)
  rw [← Over.mapComp_eq, augmentationApp_naturality]

/-- The functor `j_{a_c}` is cocontinuous for the topology of the degree and the localized
topology of `C/X`. -/
instance augmentationFibre_isCocontinuous (c : SimplexCategoryᵒᵖ) :
    (Over.map (augmentationApp U a c)).IsCocontinuous
      (topologyOfCoverings (sliceCoverings J U c)) (J.over X) := by
  rw [topologyOfCoverings_sliceCoverings]
  infer_instance

/-- **Stacks 09WL part (3).** The augmentation `a_0 : C/U_0 → C/X` of the simplicial family of
sites `n ↦ C/U_n`: the localization functor `j_{a_0} = Over.map a_0` is cocontinuous and its
composite with the functor of any vertex of a simplicial degree is `j_{a_n}`, which does not
mention the vertex. By `isMorphismOfSites_augmentationPullback` and
`augmentationSheafPushforwardIso` this is the augmentation given by the morphism of sites
`a_0` of Stacks 0D6Z part (A): the two presentations of `a_0` give the same morphism of topoi
`Sh(C/U_0) ⟶ Sh(C/X)`. -/
@[stacks 09WL "part (3), a_0 is an augmentation of the simplicial site C/U"]
def augmentation : (simplicialSite J U).Augmentation (Cat.of (Over X)) (J.over X) where
  functor := augmentationFibre U a (op (SimplexCategory.mk 0))
  isCocontinuous := augmentationFibre_isCocontinuous J U a _
  compatibility _ φ ψ :=
    (slicesMap_comp_augmentationFibre U a φ.op).trans
      (slicesMap_comp_augmentationFibre U a ψ.op).symm

/-- The augmentation of the simplicial-site situation attached to `a`. -/
def situationAugmentation :
    SimplicialSiteSituation.Augmentation (situation J U) (Cat.of (Over X)) (J.over X) :=
  augmentation J U a

/-- The functor which the augmentation attaches to simplicial degree `c` — the vertex functor
of that degree followed by `j_{a_0}` — is `j_{a_c}`. -/
theorem totalAugmentationFibre_eq (c : SimplexCategoryᵒᵖ) :
    CocontinuousSimplicialSite.Augmentation.totalAugmentationFibre (augmentation J U a) c =
      augmentationFibre U a c :=
  slicesMap_comp_augmentationFibre U a (CocontinuousSimplicialSite.degreeZeroVertexOp c)

omit [HasPullbacks C] in
/-- The functor `j_{a_b}` is the transition functor of `α : b ⟶ c` followed by `j_{a_c}`. -/
theorem augmentationFibre_eq {b c : SimplexCategoryᵒᵖ} (α : b ⟶ c) :
    augmentationFibre U a b = ((slices U).map α).toFunctor ⋙ augmentationFibre U a c :=
  (slicesMap_comp_augmentationFibre U a α).symm

omit [HasPullbacks C] in
/-- At an identity simplex map, the identification `augmentationFibre_eq` is the identification
`Grothendieck.fib_map_id_eq` of the transition of an identity. -/
theorem augmentationFibre_eq_id (c : SimplexCategoryᵒᵖ) :
    eqToHom (augmentationFibre_eq U a (𝟙 c)) =
      eqToHom (Grothendieck.fib_map_id_eq (F := slices U) (augmentationFibre U a) c) :=
  rfl

omit [HasPullbacks C] in
/-- At a composite `α ≫ β`, the identification `augmentationFibre_eq` is the one along `α`,
followed by the one along `β` whiskered by the transition of `α`, followed by the identification
`Grothendieck.fib_map_comp_eq` of the transition of a composite. -/
theorem augmentationFibre_eq_comp (c₁ c₂ c₃ : SimplexCategoryᵒᵖ) (α : c₁ ⟶ c₂) (β : c₂ ⟶ c₃) :
    eqToHom (augmentationFibre_eq U a (α ≫ β)) =
      eqToHom (augmentationFibre_eq U a α) ≫
        Functor.whiskerLeft ((slices U).map α).toFunctor
            (eqToHom (augmentationFibre_eq U a β)) ≫
          eqToHom (Grothendieck.fib_map_comp_eq (F := slices U) (augmentationFibre U a) α β) := by
  rw [Functor.whiskerLeft_eqToHom, eqToHom_trans, eqToHom_trans]

/-- The functor `V/U_n ↦ V/X` out of `(C/U)_total` of Stacks 09X8, which gives the augmentation
morphism of topoi `a : Sh((C/U)_total) ⟶ Sh(C/X)` above: in simplicial degree `c` it is the
localization functor `j_{a_c} = Over.map a_c`. -/
def augmentationFunctor : Grothendieck (slices U) ⥤ Over X :=
  Grothendieck.functorFromOfEq (F := slices U) (augmentationFibre U a)
    (fun {_ _} α ↦ eqToHom (augmentationFibre_eq U a α))
    (augmentationFibre_eq_id U a) (augmentationFibre_eq_comp U a)

omit [HasPullbacks C] in
/-- The inclusion of the component of simplicial degree `c` followed by the functor
`V/U_n ↦ V/X` is the localization functor `j_{a_c} = Over.map a_c` of that degree. -/
theorem ι_comp_augmentationFunctor (c : SimplexCategoryᵒᵖ) :
    Grothendieck.ι (slices U) c ⋙ augmentationFunctor U a = augmentationFibre U a c := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) fun y z α ↦ ?_
  simp only [Functor.comp_map, augmentationFunctor, Grothendieck.functorFromOfEq, Grothendieck.ι,
    eqToHom_app, CategoryTheory.Functor.map_comp]
  rw [eqToHom_comp_map_eqToHom_assoc]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The functor out of `(C/U)_total` which the augmentation `a_0` determines is the functor
`V/U_n ↦ V/X` above: both are assembled from the same fibrewise family `j_{a_c}`. -/
theorem totalAugmentationFunctor_eq :
    CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor (augmentation J U a) =
      augmentationFunctor U a := by
  have h : CocontinuousSimplicialSite.Augmentation.totalAugmentationFibre (augmentation J U a) =
      augmentationFibre U a :=
    funext fun c ↦ totalAugmentationFibre_eq J U a c
  rw [CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor, augmentationFunctor]
  exact Grothendieck.functorFromOfEq_congr _ _ _ _ _ _ _ _ h

/-- The functor `V/U_n ↦ V/X` is cocontinuous for the topology of `(C/U)_total`, so it induces
a morphism of topoi `Sh((C/U)_total) ⟶ Sh(C/X)`. -/
instance augmentationFunctor_isCocontinuous :
    (augmentationFunctor U a).IsCocontinuous (SimplicialOver.totalTopology J U) (J.over X) := by
  rw [← totalAugmentationFunctor_eq J U a]
  exact CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_isCocontinuous
    (augmentation J U a)

/-- Equal cocontinuous site functors have equal direct images: the direct image depends on the
functor and on the proof that it is cocontinuous, and the latter is a proposition. -/
theorem sheafPushforwardCocontinuous_congr {Y Z : Type u} [SmallCategory Y] [SmallCategory Z]
    (Jy : GrothendieckTopology Y) (Jz : GrothendieckTopology Z) {F G : Y ⥤ Z}
    [iF : F.IsCocontinuous Jy Jz] [iG : G.IsCocontinuous Jy Jz] (h : F = G) :
    F.sheafPushforwardCocontinuous (Type u) Jy Jz =
      G.sheafPushforwardCocontinuous (Type u) Jy Jz := by
  subst h
  rfl

/-- **Stacks 09WL part (3).** The morphism of topoi `a : Sh((C/U)_total) ⟶ Sh(C/X)` which the
augmentation `a_0` gives: the morphism of topoi of Stacks 0D70 attached to the augmentation of
the simplicial family of sites `n ↦ C/U_n` determined by `a_0`. -/
@[stacks 09WL "part (3), the morphism of topoi Sh((C/U)_total) to Sh(C/X) of the augmentation"]
noncomputable def augmentationMorphismOfTopoi :
    MorphismOfTopoi (Sheaf (SimplicialOver.totalTopology J U) (Type u))
      (Sheaf (J.over X) (Type u)) :=
  CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi (augmentation J U a)

/-- **Stacks 09WL part (3).** That morphism of topoi is the one above: its direct image is the
direct image of the cocontinuous functor `V/U_n ↦ V/X` of Stacks 09X8. The two are *equal*,
not merely isomorphic. -/
@[stacks 09WL "part (3), the augmentation gives the morphism of topoi above"]
theorem augmentationMorphismOfTopoi_pushforward :
    (augmentationMorphismOfTopoi J U a).pushforward =
      (augmentationFunctor U a).sheafPushforwardCocontinuous (Type u)
        (SimplicialOver.totalTopology J U) (J.over X) :=
  sheafPushforwardCocontinuous_congr (SimplicialOver.totalTopology J U) (J.over X)
    (iF := CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_isCocontinuous
      (augmentation J U a))
    (iG := augmentationFunctor_isCocontinuous J U a) (totalAugmentationFunctor_eq J U a)

end Augmentation

end SimplicialOver

end CategoryTheory

end
