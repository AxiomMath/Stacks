module

public import StacksFrontier.CategoryTheory.Triangulated.MilnorFibreDerivedLimit

/-!
# Formation of the strict Milnor fibre commutes with an additive functor

Let `G : A ⥤ B` be an additive functor between abelian categories with countable products,
and let `F : ℕᵒᵖ ⥤ CochainComplex A ℤ` be a tower of cochain complexes. Applying `G` degreewise
turns `F` into a tower `F ⋙ G.mapHomologicalComplex _` of cochain complexes in `B`. This file
constructs a **canonical** map

`Stacks.MilnorTower.baseChange : G(R lim F) ⟶ R lim (G ∘ F)`

between the two strict Milnor fibres, shows that it carries the projections and the canonical
comparison map out of an augmented complex to theirs, and shows that it is an isomorphism as
soon as `G` preserves the countable products involved.

## Why this is what a locality argument needs

The canonical comparison map of a cone into a derived limit is the point of the whole
construction. A presentation of a derived limit as a distinguished triangle determines its
vertex only up to non-unique isomorphism, and a cone on the tower lifts through the triangle
only up to the indeterminacy `Hom(Y, (∏ Kₙ)⟦-1⟧)`, which does not vanish. So from "`K|_U` is
*some* derived limit of `F|_U`" for every `U` in a cover one gets no statement about a global
map at all, and the invertibility of a global comparison cannot be checked chart by chart.

With the Milnor fibre and the comparison map given by formulas, and with
`Stacks.MilnorTower.augmentationMap_baseChange` identifying the `G`-image of the comparison map
with the comparison map of the `G`-image, invertibility *is* checkable chart by chart: this is
`Stacks.MilnorTower.quasiIso_augmentationMap_of_forall`, which concludes that the comparison
map of a tower is a quasi-isomorphism from the comparison maps of the base-changed towers being
quasi-isomorphisms, for a family of additive product-preserving functors that jointly detects
quasi-isomorphisms. Taking that family to be the restrictions to the members of a cover turns a
chart-by-chart hypothesis into a global conclusion.

## Main definitions

* `Stacks.MilnorTower.TowerAugmentation.map` — the `G`-image of an augmented complex.
* `Stacks.MilnorTower.baseChange` — the canonical map `G(R lim F) ⟶ R lim (G ∘ F)`.
* `Stacks.MilnorTower.mapDegreeIso` — the `G`-image of
  `Stacks.MilnorTower.degreeIso`, i.e. the degreewise biproduct decomposition of the `G`-image
  of a mapping cocone.

## Main results

* `Stacks.MilnorTower.baseChange_proj` — the canonical map carries the projections of the
  base-changed tower to the `G`-images of the projections.
* `Stacks.MilnorTower.augmentationMap_baseChange` — it carries the comparison map of an
  augmented complex to the comparison map of its `G`-image.
* `Stacks.MilnorTower.isIso_baseChange` — it is an isomorphism of cochain complexes when the
  comparison map of the product is one, in particular when `G` preserves `ℕ`-indexed products.
* `Stacks.MilnorTower.quasiIso_augmentationMap_of_forall` — **invertibility of the comparison
  map is local**: if the comparison maps of the base-changed towers are quasi-isomorphisms for a
  family of additive product-preserving functors that jointly detects quasi-isomorphisms, so is
  the comparison map of the tower.

## Implementation notes

`Stacks.MilnorTower.baseChange` is built with `CochainComplex.mappingCocone.lift`, its first
argument being the `G`-image of the first cocone coordinate followed by the product comparison
map and its second the `G`-image of the second coordinate followed by the same; the side
condition is `Stacks.MilnorTower.δ_mappingCocone_snd` transported along `G` by
`CochainComplex.HomComplex.δ_map`. It is *not* built as the composite of
`CochainComplex.mappingCone.mapHomologicalComplexIso` with a transport of mapping cones along
an isomorphism of arrows, which would additionally require commuting
`G.mapHomologicalComplex _` with the shift by `-1` on cochain complexes.

That it is an isomorphism is checked degreewise rather than by two-out-of-three in a triangle:
the two coordinates of a mapping cocone split each of its degrees as a biproduct, and in that
splitting the map is the biproduct of two degrees of the product comparison map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive
open CochainComplex CochainComplex.HomComplex

universe w₂ w v₂ v u₂ u

namespace Stacks.MilnorTower

/-! ### The `G`-image of a mapping cocone, degreewise -/

section MapDegreeIso

variable {A : Type u} [Category.{v} A] [Preadditive A] {B : Type u₂} [Category.{v₂} B]
  [Preadditive B] (G : A ⥤ B) [G.Additive] [Limits.HasBinaryBiproducts B]
  {K L : CochainComplex A ℤ} (φ : K ⟶ L) [HomologicalComplex.HasHomotopyCofiber φ]

/-- **The `G`-image of a degree of a mapping cocone is the biproduct of the `G`-images of the
two coordinates.** This is `Stacks.MilnorTower.degreeIso` transported along `G`; an additive
functor preserves binary biproducts, and the inverse is the `G`-image of the inverse. -/
public def mapDegreeIso (i j : ℤ) (hij : i + -1 = j) :
    G.obj ((mappingCocone φ).X i) ≅ G.obj (K.X i) ⊞ G.obj (L.X j) where
  hom := biprod.lift (G.map ((mappingCocone.fst φ).f i))
    (G.map ((mappingCocone.snd φ).v i j hij))
  inv := biprod.desc (G.map ((mappingCocone.inl φ).v i i (add_zero i)))
    (G.map ((mappingCocone.inr φ).1.v j i (by omega)))
  hom_inv_id := by
    rw [biprod.lift_desc, ← G.map_comp, ← G.map_comp, ← G.map_add,
      mappingCocone.id_X φ i j hij, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_)
    all_goals
      simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, Category.comp_id,
        biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd]
    all_goals rw [← Category.assoc]
    all_goals
      simp only [biprod.inl_desc, biprod.inr_desc, ← G.map_comp, mappingCocone.inl_v_fst_f,
        mappingCocone.inl_v_snd_v, mappingCocone.inr_v_fst_f, mappingCocone.inr_v_snd_v,
        CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]

/-- The first component of `mapDegreeIso` is the `G`-image of the first cocone coordinate. -/
@[reassoc (attr := simp)]
public theorem mapDegreeIso_hom_fst (i j : ℤ) (hij : i + -1 = j) :
    (mapDegreeIso G φ i j hij).hom ≫ biprod.fst = G.map ((mappingCocone.fst φ).f i) := by
  simp [mapDegreeIso]

/-- The second component of `mapDegreeIso` is the `G`-image of the second cocone coordinate. -/
@[reassoc (attr := simp)]
public theorem mapDegreeIso_hom_snd (i j : ℤ) (hij : i + -1 = j) :
    (mapDegreeIso G φ i j hij).hom ≫ biprod.snd = G.map ((mappingCocone.snd φ).v i j hij) := by
  simp [mapDegreeIso]

end MapDegreeIso

/-! ### The canonical base-change map of Milnor fibres -/

section BaseChange

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasProductsOfShape ℕ B]
  (G : A ⥤ B) [G.Additive] (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)

/-- The comparison map from the `G`-image of the product of the terms of a tower to the product
of the `G`-images. -/
public abbrev towerProductComparison :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (towerProductObj F) ⟶
      towerProductObj (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  piComparison (G.mapHomologicalComplex (ComplexShape.up ℤ)) fun n : ℕ ↦ F.obj ⟨n⟩

/-- **The product comparison map intertwines the two Milnor endomorphisms.** -/
@[reassoc]
public theorem mapHomologicalComplex_oneMinusShift :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (oneMinusShift F) ≫
        towerProductComparison G F =
      towerProductComparison G F ≫
        oneMinusShift (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  map_familyDifference_piComparison (G.mapHomologicalComplex (ComplexShape.up ℤ))
    (fun n : ℕ ↦ F.obj ⟨n⟩) fun n ↦ F.map (homOfLE (Nat.le_succ n)).op

/-- The components of the product comparison map are the `G`-images of the projections. -/
@[reassoc (attr := simp)]
public theorem towerProductComparison_π (n : ℕ) :
    towerProductComparison G F ≫
        Pi.π (fun k : ℕ ↦ (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)).obj ⟨k⟩) n =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n) :=
  piComparison_comp_π _ _ n

/-- **The canonical map `G(R lim F) ⟶ R lim (G ∘ F)` of strict Milnor fibres.** Its first
coordinate is the `G`-image of the first coordinate followed by the product comparison map, and
its second coordinate is the `G`-image of the second coordinate followed by the same. -/
public def baseChange :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (milnorObj F) ⟶
      milnorObj (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  mappingCocone.lift (oneMinusShift (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)))
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCocone.fst (oneMinusShift F)) ≫
      towerProductComparison G F)
    (((mappingCocone.snd (oneMinusShift F)).map G).comp
      (Cochain.ofHom (towerProductComparison G F)) (add_zero (-1))) (by
    rw [δ_comp_ofHom, δ_map, δ_mappingCocone_snd, Cochain.map_neg, Cochain.map_ofHom,
      Cochain.neg_comp, ← Cochain.ofHom_comp,
      show ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (mappingCocone.fst (oneMinusShift F)) ≫ towerProductComparison G F) ≫
            oneMinusShift (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) =
          (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (mappingCocone.fst (oneMinusShift F) ≫ oneMinusShift F) ≫
            towerProductComparison G F by
        rw [Category.assoc, ← mapHomologicalComplex_oneMinusShift, ← Category.assoc,
          ← (G.mapHomologicalComplex (ComplexShape.up ℤ)).map_comp],
      neg_add_cancel])

/-- The first coordinate of `baseChange` is the `G`-image of the first coordinate followed by
the product comparison map. -/
@[reassoc (attr := simp)]
public theorem baseChange_fst :
    baseChange G F ≫
        mappingCocone.fst (oneMinusShift (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ))) =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCocone.fst (oneMinusShift F)) ≫
        towerProductComparison G F :=
  mappingCocone.lift_fst _ _ _ _

/-- In each degree, the second coordinate of `baseChange` is the `G`-image of the second
coordinate followed by the product comparison map. -/
@[reassoc (attr := simp)]
public theorem baseChange_snd (n m : ℤ) (hnm : n + -1 = m) :
    (baseChange G F).f n ≫ (mappingCocone.snd
        (oneMinusShift (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)))).v n m hnm =
      G.map ((mappingCocone.snd (oneMinusShift F)).v n m hnm) ≫
        (towerProductComparison G F).f m := by
  rw [baseChange, mappingCocone.lift_f_snd_v,
    Cochain.comp_v _ _ (add_zero (-1)) n m m hnm (add_zero m), Cochain.ofHom_v, Cochain.map_v]

/-- **The canonical base-change map carries the projections to the `G`-images of the
projections.** -/
@[reassoc (attr := simp)]
public theorem baseChange_proj (n : ℕ) :
    baseChange G F ≫ proj (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) n =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (proj F n) := by
  rw [proj, baseChange_fst_assoc, towerProductComparison_π, proj,
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map_comp]

end BaseChange

/-! ### The `G`-image of an augmented complex -/

namespace TowerAugmentation

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasProductsOfShape ℕ B]
  {F : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : TowerAugmentation F) (G : A ⥤ B) [G.Additive]

/-- The `G`-image of a complex augmented over a tower, augmented over the `G`-image of the
tower. -/
public def map : TowerAugmentation (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) where
  source := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj a.source
  app n := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (a.app n)
  naturality n :=
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (a.naturality n))

omit [HasProductsOfShape ℕ A] [HasProductsOfShape ℕ B] in
/-- The augmenting complex of `a.map G` is the `G`-image of the augmenting complex of `a`. -/
@[simp]
public theorem map_source :
    (a.map G).source = (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj a.source :=
  rfl

omit [HasProductsOfShape ℕ A] [HasProductsOfShape ℕ B] in
/-- The components of the augmentation `a.map G` are the `G`-images of those of `a`. -/
@[simp]
public theorem map_app (n : ℕ) :
    (a.map G).app n = (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (a.app n) :=
  rfl

/-- The `G`-image of the map to the product of the tower, followed by the product comparison
map, is the map to the product of the `G`-images. -/
@[reassoc (attr := simp)]
public theorem mapHomologicalComplex_piLift :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (Limits.Pi.lift a.app) ≫
        towerProductComparison G F =
      Limits.Pi.lift (a.map G).app :=
  Limits.Pi.hom_ext _ _ fun n ↦ by
    refine Eq.trans ?_ (Limits.Pi.lift_comp_π (a.map G).app n).symm
    rw [Category.assoc, towerProductComparison_π,
      ← (G.mapHomologicalComplex (ComplexShape.up ℤ)).map_comp, Limits.Pi.lift_comp_π, map_app]

end TowerAugmentation

/-! ### The base-change map on comparison maps, and its invertibility -/

section Transfer

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasProductsOfShape ℕ B]
  (G : A ⥤ B) [G.Additive] {F : ℕᵒᵖ ⥤ CochainComplex A ℤ}

/-- **The canonical base-change map carries the canonical comparison map of an augmented
complex to the canonical comparison map of its `G`-image.** Both sides are determined by their
two cocone coordinates: the first is the `G`-image of the map to the product followed by the
product comparison map, and the second is zero. -/
@[reassoc]
public theorem augmentationMap_baseChange (a : TowerAugmentation F) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map a.augmentationMap ≫ baseChange G F =
      (a.map G).augmentationMap := by
  refine mappingCocone_hom_ext _ ?_ fun n m hnm ↦ ?_
  · have h1 : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map a.augmentationMap ≫
        baseChange G F ≫ mappingCocone.fst
          (oneMinusShift (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ))) =
        Limits.Pi.lift (a.map G).app := by
      rw [baseChange_fst, ← Category.assoc,
        ← (G.mapHomologicalComplex (ComplexShape.up ℤ)).map_comp,
        TowerAugmentation.augmentationMap_fst,
        TowerAugmentation.mapHomologicalComplex_piLift]
    exact ((Category.assoc _ _ _).trans h1).trans
      (TowerAugmentation.augmentationMap_fst (a.map G)).symm
  · refine Eq.trans ?_ (TowerAugmentation.augmentationMap_snd (a.map G) n m hnm).symm
    rw [HomologicalComplex.comp_f, Category.assoc, baseChange_snd, ← Category.assoc,
      show ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map a.augmentationMap).f n ≫
          G.map ((mappingCocone.snd (oneMinusShift F)).v n m hnm) =
          G.map (a.augmentationMap.f n ≫ (mappingCocone.snd (oneMinusShift F)).v n m hnm) from
        (G.map_comp _ _).symm,
      TowerAugmentation.augmentationMap_snd, CategoryTheory.Functor.map_zero, zero_comp]
    rfl

/-- **In each degree the base-change map is the biproduct of two degrees of the product
comparison map**, read through `Stacks.MilnorTower.mapDegreeIso` and
`Stacks.MilnorTower.degreeIso`. -/
@[reassoc]
public theorem baseChange_degreeIso (i j : ℤ) (hij : i + -1 = j) :
    (baseChange G F).f i ≫
        (degreeIso (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) i j hij).hom =
      (mapDegreeIso G (oneMinusShift F) i j hij).hom ≫
        biprod.map ((towerProductComparison G F).f i) ((towerProductComparison G F).f j) := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, degreeIso_hom_fst, Category.assoc, biprod.map_fst,
      mapDegreeIso_hom_fst_assoc]
    exact congrArg (fun w ↦ HomologicalComplex.Hom.f w i) (baseChange_fst G F)
  · rw [Category.assoc, degreeIso_hom_snd, Category.assoc, biprod.map_snd,
      mapDegreeIso_hom_snd_assoc, baseChange_snd]

/-- **The canonical base-change map is an isomorphism as soon as the product comparison map
is.** The product comparison map is an isomorphism whenever `G` preserves `ℕ`-indexed
products, since products of cochain complexes are computed degreewise. -/
public theorem isIso_baseChange (h : IsIso (towerProductComparison G F)) :
    IsIso (baseChange G F) := by
  have := h
  have hf (k : ℤ) : IsIso ((towerProductComparison G F).f k) :=
    (HomologicalComplex.eval B (ComplexShape.up ℤ) k).map_isIso _
  have : ∀ i : ℤ, IsIso ((baseChange G F).f i) := fun i ↦ by
    have : IsIso ((baseChange G F).f i ≫
        (degreeIso (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) i (i + -1) rfl).hom) := by
      rw [baseChange_degreeIso]
      exact (mapDegreeIso G (oneMinusShift F) i (i + -1) rfl ≪≫
        biprod.mapIso (asIso ((towerProductComparison G F).f i))
          (asIso ((towerProductComparison G F).f (i + -1)))).isIso_hom
    exact IsIso.of_isIso_comp_right _
      (degreeIso (F ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) i (i + -1) rfl).hom
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The canonical base-change map is an isomorphism when `G` preserves the countable
products of cochain complexes involved.** -/
public theorem isIso_baseChange_of_preservesProducts
    [Limits.PreservesLimitsOfShape (Discrete ℕ)
      (G.mapHomologicalComplex (ComplexShape.up ℤ))] :
    IsIso (baseChange G F) :=
  isIso_baseChange G inferInstance

/-- **The canonical comparison map of a tower becomes a quasi-isomorphism after base change
along `G` as soon as the comparison map of the base-changed tower is one.** This is the step a
locality argument is made of: the hypothesis is about the base-changed data alone, and the
conclusion is about the `G`-image of the global map. -/
public theorem quasiIso_mapHomologicalComplex_augmentationMap
    (h : IsIso (towerProductComparison G F)) (a : TowerAugmentation F)
    (ha : QuasiIso (a.map G).augmentationMap) :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map a.augmentationMap) := by
  have := isIso_baseChange G h
  have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map a.augmentationMap ≫
      baseChange G F) := by
    rw [augmentationMap_baseChange]
    exact ha
  exact quasiIso_of_comp_right _ (baseChange G F)

end Transfer

/-! ### Invertibility of the canonical comparison map is local -/

section Locality

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]
  {F : ℕᵒᵖ ⥤ CochainComplex A ℤ}

/-- **Invertibility of the canonical comparison map of a tower of cochain complexes is a local
property.** Let `Gᵢ : A ⥤ Bᵢ` be additive functors preserving the countable products involved,
and suppose they jointly detect quasi-isomorphisms out of the augmenting complex. If the
canonical comparison map of each base-changed tower is a quasi-isomorphism, so is the canonical
comparison map of the tower.

This is the statement that the existential presentations of a derived limit cannot supply.
`CategoryTheory.Pretriangulated.IsDerivedLimit` and
`NoetherianAdicCompletion.IsDerivedLimitWithProjections` both leave the comparison map
unnamed, and the lift of a cone through a Milnor triangle is determined only up to
`Hom(Y, (∏ Kₙ)⟦-1⟧)`, which does not vanish; so a chart-by-chart hypothesis about *some* lift
says nothing about any global map. Here the comparison map is
`Stacks.MilnorTower.TowerAugmentation.augmentationMap`, a formula, and
`Stacks.MilnorTower.augmentationMap_baseChange` says its `Gᵢ`-image is the comparison map of
the `Gᵢ`-image of the data. -/
public theorem quasiIso_augmentationMap_of_forall {ι : Type*} {Bs : ι → Type u₂}
    [∀ i, Category.{v₂} (Bs i)] [∀ i, Abelian (Bs i)] [∀ i, HasProductsOfShape ℕ (Bs i)]
    (Gs : ∀ i, A ⥤ Bs i) [∀ i, (Gs i).Additive]
    (hpc : ∀ i, IsIso (towerProductComparison (Gs i) F)) (a : TowerAugmentation F)
    (hdetect : ∀ f : a.source ⟶ milnorObj F,
      (∀ i, QuasiIso (((Gs i).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) → QuasiIso f)
    (hlocal : ∀ i, QuasiIso (a.map (Gs i)).augmentationMap) :
    QuasiIso a.augmentationMap :=
  hdetect _ fun i ↦
    quasiIso_mapHomologicalComplex_augmentationMap (Gs i) (hpc i) a (hlocal i)

end Locality

/-! ### The comparison map in the derived category -/

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]
  [HasDerivedCategory.{w} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasProductsOfShape ℕ B] [HasDerivedCategory.{w₂} B]
  (G : A ⥤ B) [G.Additive] {F : ℕᵒᵖ ⥤ CochainComplex A ℤ}

omit [HasDerivedCategory A] in
/-- **The base-change map carries the comparison map of an augmented complex to that of its
`G`-image, in the derived category.** -/
public theorem Q_map_augmentationMap_baseChange (a : TowerAugmentation F) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          a.augmentationMap) ≫ DerivedCategory.Q.map (baseChange G F) =
      DerivedCategory.Q.map (a.map G).augmentationMap :=
  (DerivedCategory.Q.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Q.map (augmentationMap_baseChange G a))

omit [HasDerivedCategory A] in
/-- **The `G`-image of the canonical comparison map is invertible in `D(B)` as soon as the
canonical comparison map of the base-changed tower is.** The derived-category form of
`Stacks.MilnorTower.quasiIso_mapHomologicalComplex_augmentationMap`. -/
public theorem isIso_Q_map_augmentationMap (h : IsIso (towerProductComparison G F))
    (a : TowerAugmentation F)
    (ha : IsIso (DerivedCategory.Q.map (a.map G).augmentationMap)) :
    IsIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      a.augmentationMap)) := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at ha ⊢
  exact quasiIso_mapHomologicalComplex_augmentationMap G h a ha

end Derived

end Stacks.MilnorTower

end
