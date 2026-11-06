module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# The countable Milnor functor

For a tower of cochain complexes of modules, we construct the product, the endomorphism
`1 - shift`, and its mapping cocone.  This gives a strict functorial model for the derived
inverse limit together with its projections.

## Main definitions

* `CountableMilnorTower.towerProduct` is the product of the terms of a tower.
* `CountableMilnorTower.oneMinusShift` is the Milnor endomorphism of that product.
* `CountableMilnorTower.countableMilnorFunctor` is its mapping cocone, functorially in
  strict morphisms of towers.
* `CountableMilnorTower.projection` is the natural map from the mapping cocone to a term of
  the tower, and `CountableMilnorTower.projectionTransitionHomotopy` is the canonical chain
  homotopy making the projections compatible with tower transitions.
* `CountableMilnorTower.TowerAugmentation` and
  `CountableMilnorTower.TowerAugmentation.augmentationMap` give the canonical map
  from a compatible augmented complex.
* `CountableMilnorTower.augmentationNatTrans` assembles these maps into a natural unit.

## Main results

* `CountableMilnorTower.map_quasiIso_and_milnor_triangle` records preservation of
  objectwise quasi-isomorphisms and the distinguished Milnor triangle after localization.
* `CountableMilnorTower.countableMilnorFunctor_map_shortExact` shows that the strict Milnor
  functor carries short exact sequences of towers to short exact sequences of complexes.

## Implementation notes

The mapping fiber is implemented as `CochainComplex.mappingCocone`; functoriality uses the
strict arrow map `HomologicalComplex.homotopyCofiber.mapArrowHom`.  Thus no functorial choice
of cones in the derived category is made.  Exactness of countable products of modules applies
with independent universes for the ring and its coefficient modules. The second cocone
projection supplies the chain homotopy for compatibility with tower transitions;
`projection_transition` is the resulting equality after localization.

Short exactness is checked degreewise, after transporting each degree of the mapping cocone
across `CountableMilnorTower.milnorDegreeIso` to a raw product of module-theoretic sections.

## References

* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 091D](https://stacks.math.columbia.edu/tag/091D)
* [Stacks Project, Tag 091Z](https://stacks.math.columbia.edu/tag/091Z)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace CountableMilnorTower

variable {A : Type u} [Ring A]

local instance : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} A) :=
  moduleCat_hasExactLimitsOfShape_discrete.{v} A ℕ

attribute [local instance] HasDerivedCategory.standard

/-- Cochain complexes of coefficient modules. -/
public abbrev CoefficientComplex := CochainComplex (ModuleCat.{v} A) ℤ

/-- Towers of cochain complexes of coefficient modules. -/
public abbrev Tower := ℕᵒᵖ ⥤ CoefficientComplex.{u, v} (A := A)

/-- The product object underlying the countable Milnor construction. -/
public noncomputable abbrev towerProductObj (F : Tower.{u, v} (A := A)) :
    CoefficientComplex.{u, v} (A := A) :=
  ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩

/-- The product map induced by a strict morphism of towers. -/
public noncomputable abbrev towerProductMap {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) :
    towerProductObj F ⟶ towerProductObj G :=
  Limits.Pi.map fun n ↦ f.app ⟨n⟩

/-- The product of all terms of a tower of cochain complexes. -/
public noncomputable def towerProduct :
    Tower.{u, v} (A := A) ⥤ CoefficientComplex.{u, v} (A := A) where
  obj := towerProductObj
  map := towerProductMap
  map_id F := Limits.Pi.map_id
  map_comp f g := by
    rw [Limits.Pi.map_comp_map]
    apply Limits.Pi.hom_ext _ _
    intro n
    simp

/-- The `1 - shift` endomorphism of the product of a tower. -/
public noncomputable def oneMinusShift (F : Tower.{u, v} (A := A)) :
    towerProductObj F ⟶ towerProductObj F :=
  Limits.Pi.lift fun n : ℕ ↦
    Limits.Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
      Limits.Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
        F.map (homOfLE (Nat.le_succ n)).op

/-- The components of the Milnor endomorphism are the identity minus the transition. -/
@[reassoc (attr := simp)]
public theorem oneMinusShift_π (F : Tower.{u, v} (A := A)) (n : ℕ) :
    oneMinusShift F ≫ Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n =
      Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n -
        Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op := by
  simp [oneMinusShift]

/-- Strict maps of towers commute with the Milnor endomorphism. -/
@[reassoc]
public theorem towerProduct_map_naturality {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) :
    towerProductMap f ≫ oneMinusShift G = oneMinusShift F ≫ towerProductMap f := by
  apply Limits.Pi.hom_ext _ _
  intro n
  simp [oneMinusShift, towerProductMap, f.naturality]

/-- The Milnor endomorphism, natural in the strict tower. -/
public noncomputable def oneMinusShiftNatTrans :
    towerProduct.{u, v} (A := A) ⟶ towerProduct.{u, v} (A := A) where
  app := oneMinusShift
  naturality _ _ f := towerProduct_map_naturality f

/-- The commutative square between the Milnor endomorphisms induced by a strict map of towers. -/
public noncomputable def oneMinusShiftArrowMap {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) :
    Arrow.mk (oneMinusShift F) ⟶ Arrow.mk (oneMinusShift G) :=
  Arrow.homMk (towerProductMap f) (towerProductMap f) (towerProduct_map_naturality f)

/-- The induced map of the (unshifted) mapping cones. -/
public noncomputable abbrev mappingConeMap {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) :
    CochainComplex.mappingCone (oneMinusShift F) ⟶
      CochainComplex.mappingCone (oneMinusShift G) :=
  HomologicalComplex.homotopyCofiber.mapArrowHom
    (oneMinusShift F) (oneMinusShift G) (fun j ↦ ⟨j - 1, by simp⟩) (oneMinusShiftArrowMap f)

/-- The functorial map between the mapping cocones of the Milnor endomorphisms. -/
public noncomputable def mappingCoconeMap {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) :
    CochainComplex.mappingCocone (oneMinusShift F) ⟶
      CochainComplex.mappingCocone (oneMinusShift G) :=
  (shiftFunctor (CoefficientComplex.{u, v} (A := A)) (-1 : ℤ)).map
    (mappingConeMap f)

/-- The mapping-cocone object underlying the countable Milnor functor. -/
public noncomputable abbrev countableMilnorObj (F : Tower.{u, v} (A := A)) :
    CoefficientComplex.{u, v} (A := A) :=
  CochainComplex.mappingCocone (oneMinusShift F)

/-- The strict countable-product mapping-fiber functor on towers of cochain complexes. -/
public noncomputable def countableMilnorFunctor : Tower.{u, v} (A := A) ⥤
    CoefficientComplex.{u, v} (A := A) where
  obj := countableMilnorObj
  map f := mappingCoconeMap f
  map_id F := by
    change mappingCoconeMap (𝟙 F) = 𝟙 (countableMilnorObj F)
    have h : oneMinusShiftArrowMap (𝟙 F) = 𝟙 (Arrow.mk (oneMinusShift F)) := by
      apply Arrow.hom_ext <;> simp [oneMinusShiftArrowMap, towerProductMap]
    dsimp only [mappingCoconeMap, mappingConeMap]
    rw [h, HomologicalComplex.homotopyCofiber.mapArrowHom_id]
    exact (shiftFunctor (CoefficientComplex.{u, v} (A := A)) (-1 : ℤ)).map_id _
  map_comp f g := by
    change mappingCoconeMap (f ≫ g) = mappingCoconeMap f ≫ mappingCoconeMap g
    have h : oneMinusShiftArrowMap (f ≫ g) =
        oneMinusShiftArrowMap f ≫ oneMinusShiftArrowMap g := by
      apply Arrow.hom_ext <;>
        simp [oneMinusShiftArrowMap, towerProductMap, ← Limits.Pi.map_comp_map]
    dsimp only [mappingCoconeMap, mappingConeMap]
    rw [h, HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
    exact (shiftFunctor (CoefficientComplex.{u, v} (A := A)) (-1 : ℤ)).map_comp _ _

private lemma mappingCoconeMap_f {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) (i : ℤ) :
    (mappingCoconeMap f).f i =
      (CochainComplex.mappingCocone.fst (oneMinusShift F)).f i ≫
        (towerProductMap f).f i ≫
          (CochainComplex.mappingCocone.inl (oneMinusShift G)).v i i (add_zero i) +
      (CochainComplex.mappingCocone.snd (oneMinusShift F)).v i (i + -1) rfl ≫
        (towerProductMap f).f (i + -1) ≫
          (CochainComplex.mappingCocone.inr (oneMinusShift G)).1.v (i + -1) i (by omega) := by
  dsimp [mappingCoconeMap]
  show (mappingConeMap f).f (i + (-1 : ℤ)) = _
  dsimp only [mappingConeMap, oneMinusShiftArrowMap,
    HomologicalComplex.homotopyCofiber.mapArrowHom]
  rw [HomologicalComplex.homotopyCofiber.desc_f _ _ _ (i + (-1 : ℤ)) i
    (by simp : (ComplexShape.up ℤ).Rel (i + (-1 : ℤ)) i)]
  dsimp only [Homotopy.trans, Homotopy.ofEq, Homotopy.compLeft]
  simp only [Pi.zero_apply, Pi.add_apply, add_zero, zero_add]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom
    (oneMinusShift G) (fun j ↦ ⟨j - 1, by simp⟩) i (i + (-1 : ℤ))
    (by simp : (ComplexShape.up ℤ).Rel (i + (-1 : ℤ)) i)]
  simp [CochainComplex.mappingCocone.fst, CochainComplex.mappingCocone.snd,
    CochainComplex.mappingCocone.inl, CochainComplex.mappingCocone.inr,
    CochainComplex.mappingCone.fst, CochainComplex.mappingCone.snd,
    CochainComplex.mappingCone.inl, CochainComplex.mappingCone.inr,
    CochainComplex.HomComplex.Cochain.leftShift_v (n := 1) _ _ _ _ _ i _ (i + -1) (by omega),
    CochainComplex.HomComplex.Cochain.leftShift_v (n := 0)
      _ (-1) (-1) _ i (i + -1) _ (i + -1) (by omega),
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1) _ _ _ _ i _ _ (i + -1) (by omega),
    CochainComplex.HomComplex.Cochain.rightShift_v (n := 0)
      _ _ _ _ (i + -1) _ _ (i + -1) (by omega),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

/-- Naturality of the map from the mapping fiber to the product. -/
@[reassoc (attr := simp)]
public theorem mappingCoconeMap_fst {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) :
    mappingCoconeMap f ≫ CochainComplex.mappingCocone.fst (oneMinusShift G) =
      CochainComplex.mappingCocone.fst (oneMinusShift F) ≫ towerProductMap f := by
  apply HomologicalComplex.hom_ext
  intro i
  simp [mappingCoconeMap_f]

/-- The two normalized mapping-fiber coordinates in each degree. -/
public def milnorDegreeIso (F : Tower.{u, v} (A := A)) (i : ℤ) :
    (countableMilnorFunctor.obj F).X i ≅
      (towerProductObj F).X i ⊞ (towerProductObj F).X (i + -1) where
  hom := biprod.lift ((CochainComplex.mappingCocone.fst (oneMinusShift F)).f i)
    ((CochainComplex.mappingCocone.snd (oneMinusShift F)).v i (i + -1) rfl)
  inv := biprod.desc
    ((CochainComplex.mappingCocone.inl (oneMinusShift F)).v i i (add_zero i))
    ((CochainComplex.mappingCocone.inr (oneMinusShift F)).1.v (i + -1) i (by omega))
  hom_inv_id := by
    rw [biprod.lift_desc]
    exact CochainComplex.mappingCocone.id_X _ i (i + -1) rfl
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    all_goals simp only [← Category.assoc, biprod.inl_desc, biprod.inr_desc]
    all_goals simp [Category.assoc]

/-- Compatibility with the actual normalized cone map, on both fiber coordinates. -/
@[reassoc] public theorem milnorDegreeIso_naturality
    {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) (i : ℤ) :
    (countableMilnorFunctor.map f).f i ≫ (milnorDegreeIso G i).hom =
      (milnorDegreeIso F i).hom ≫
        biprod.map ((towerProductMap f).f i) ((towerProductMap f).f (i + -1)) := by
  show (mappingCoconeMap f).f i ≫ _ = _
  rw [mappingCoconeMap_f]
  apply biprod.hom_ext
  all_goals simp [milnorDegreeIso, Preadditive.add_comp, Category.assoc]

public instance countableMilnorFunctor_additive :
    (countableMilnorFunctor.{u, v} (A := A)).Additive where
  map_add := by
    intro F G f g
    have hp : towerProductMap (f + g) = towerProductMap f + towerProductMap g := by
      apply Pi.hom_ext
      intro n
      simp [towerProductMap, Preadditive.add_comp]
    apply HomologicalComplex.hom_ext
    intro i
    apply (cancel_mono (milnorDegreeIso G i).hom).mp
    simp only [HomologicalComplex.add_f_apply]
    rw [milnorDegreeIso_naturality, Preadditive.add_comp,
      milnorDegreeIso_naturality, milnorDegreeIso_naturality, hp]
    apply biprod.hom_ext
    all_goals simp [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

/-- Evaluation of a tower at `n`. -/
public abbrev towerEvaluation (n : ℕ) :
    Tower.{u, v} (A := A) ⥤ CoefficientComplex.{u, v} (A := A) :=
  (evaluation ℕᵒᵖ (CoefficientComplex.{u, v} (A := A))).obj ⟨n⟩

/-- The natural projection from the Milnor mapping fiber to the `n`-th term of the tower. -/
public noncomputable def projection (n : ℕ) :
    countableMilnorFunctor.{u, v} (A := A) ⟶ towerEvaluation.{u, v} (A := A) n where
  app F := CochainComplex.mappingCocone.fst (oneMinusShift F) ≫
    Limits.Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n
  naturality F G f := by
    change mappingCoconeMap f ≫ _ = _
    rw [mappingCoconeMap_fst_assoc]
    simp [towerProductMap]

open CochainComplex CochainComplex.HomComplex in
/-- The canonical chain homotopy expressing compatibility of the projections with transitions. -/
public noncomputable def projectionTransitionHomotopy (F : Tower.{u, v} (A := A)) (n : ℕ) :
    Homotopy ((projection (n + 1)).app F ≫ F.map (homOfLE (Nat.le_succ n)).op)
      ((projection n).app F) := by
  have hδ : δ (-1) 0 (mappingCocone.snd (oneMinusShift F)) =
      -Cochain.ofHom (mappingCocone.fst (oneMinusShift F) ≫ oneMinusShift F) := by
    simp [mappingCocone.snd, mappingCocone.fst,
      Cochain.δ_leftShift (mappingCone.snd (oneMinusShift F)) (-1) (-1) 0
        (by simp) 1 (by simp), Cochain.ofHom_comp]
  refine (Cochain.equivHomotopy _ _).symm ?_
  refine ⟨(mappingCocone.snd (oneMinusShift F)).comp
    (Cochain.ofHom (Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n)) (add_zero (-1)), ?_⟩
  rw [δ_comp_ofHom, hδ]
  simp only [Cochain.neg_comp, ← Cochain.ofHom_comp, Category.assoc, oneMinusShift_π,
    comp_sub, Cochain.ofHom_sub, neg_sub]
  simp [projection]

open CochainComplex CochainComplex.HomComplex in
/-- In adjacent degrees the transition homotopy is the second cocone projection followed
by the projection to the specified tower term. -/
@[simp]
public theorem projectionTransitionHomotopy_hom (F : Tower.{u, v} (A := A))
    (n : ℕ) (i j : ℤ) (hij : i + (-1) = j) :
    (projectionTransitionHomotopy F n).hom i j =
      (mappingCocone.snd (oneMinusShift F)).v i j hij ≫
        (Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n).f j := by
  simp [projectionTransitionHomotopy, Cochain.equivHomotopy, hij]

/-- The projections commute with transition maps after localization. -/
@[reassoc (attr := simp)]
public theorem projection_transition (F : Tower.{u, v} (A := A)) (n : ℕ) :
    DerivedCategory.Q.map ((projection (n + 1)).app F) ≫
        DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op) =
      DerivedCategory.Q.map ((projection n).app F) := by
  rw [← Functor.map_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy _ (projectionTransitionHomotopy F n)

/-- A cochain complex equipped with compatible maps to every term of a tower. -/
public structure TowerAugmentation (F : Tower.{u, v} (A := A)) where
  /-- The augmenting complex. -/
  source : CoefficientComplex.{u, v} (A := A)
  /-- The map to the `n`-th term. -/
  app (n : ℕ) : source ⟶ F.obj ⟨n⟩
  /-- Compatibility with the transition maps. -/
  naturality (n : ℕ) :
    app (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = app n

namespace TowerAugmentation

variable {F : Tower.{u, v} (A := A)} (a : TowerAugmentation F)

/-- The map from an augmented complex to the product of the tower. -/
public noncomputable def productLift : a.source ⟶ towerProductObj F :=
  Limits.Pi.lift a.app

@[reassoc (attr := simp)]
public theorem productLift_oneMinusShift : productLift a ≫ oneMinusShift F = 0 := by
  apply Limits.Pi.hom_ext _ _
  intro n
  dsimp only [productLift]
  simp [oneMinusShift, a.naturality]

/-- The canonical map from a compatibly augmented complex to the Milnor mapping fiber. -/
public noncomputable def augmentationMap :
    a.source ⟶ countableMilnorObj F :=
  CochainComplex.mappingCocone.lift (oneMinusShift F) (productLift a) 0 (by
    simp [productLift_oneMinusShift])

@[reassoc (attr := simp)]
public theorem augmentationMap_fst :
    augmentationMap a ≫ CochainComplex.mappingCocone.fst (oneMinusShift F) = productLift a :=
  CochainComplex.mappingCocone.lift_fst (oneMinusShift F) (productLift a) 0 _

@[reassoc (attr := simp)]
public theorem augmentationMap_projection (n : ℕ) :
    augmentationMap a ≫ (projection (A := A) n).app F = a.app n := by
  rw [show (projection (A := A) n).app F =
      CochainComplex.mappingCocone.fst (oneMinusShift F) ≫
        Limits.Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n by rfl]
  show (augmentationMap a ≫ CochainComplex.mappingCocone.fst (oneMinusShift F)) ≫
      Limits.Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n = a.app n
  rw [augmentationMap_fst, productLift, Pi.lift_comp_π]

private lemma augmentationMap_f (i : ℤ) :
    (augmentationMap a).f i = (productLift a).f i ≫
      (CochainComplex.mappingCocone.inl (oneMinusShift F)).v i i (add_zero i) := by
  have h := congrArg (fun g ↦ (augmentationMap a).f i ≫ g)
    (CochainComplex.mappingCocone.id_X (oneMinusShift F) i (i + -1) rfl)
  simpa only [comp_add, ← Category.assoc, augmentationMap,
    CochainComplex.mappingCocone.lift_f_fst_f,
    CochainComplex.mappingCocone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.zero_v, zero_comp, add_zero, Category.comp_id] using h.symm

/-- The augmentation map is natural in both the coefficient complex and the tower. -/
@[reassoc]
public theorem augmentationMap_naturality {G : Tower.{u, v} (A := A)}
    (b : TowerAugmentation G) (k : a.source ⟶ b.source) (f : F ⟶ G)
    (h : ∀ n, k ≫ b.app n = a.app n ≫ f.app ⟨n⟩) :
    k ≫ augmentationMap b = augmentationMap a ≫ countableMilnorFunctor.map f := by
  have hp : k ≫ productLift b = productLift a ≫ towerProductMap f := by
    apply Pi.hom_ext
    intro n
    simpa [productLift, towerProductMap] using h n
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f]
  show k.f i ≫ (augmentationMap b).f i =
    (augmentationMap a).f i ≫ (mappingCoconeMap f).f i
  rw [mappingCoconeMap_f, augmentationMap_f, augmentationMap_f]
  simp only [comp_add, Category.assoc,
    CochainComplex.mappingCocone.inl_v_fst_f_assoc,
    CochainComplex.mappingCocone.inl_v_snd_v_assoc,
    zero_comp, comp_zero, add_zero]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun g ↦ g.f i ≫
      (CochainComplex.mappingCocone.inl (oneMinusShift G)).v i i (add_zero i)) hp

end TowerAugmentation

/-- The natural unit associated to a functorial family of compatible tower augmentations. -/
public noncomputable def augmentationNatTrans
    {D : Type*} [Category D] (S : D ⥤ CoefficientComplex.{u, v} (A := A))
    (T : D ⥤ Tower.{u, v} (A := A))
    (a : ∀ n, S ⟶ T ⋙ towerEvaluation n)
    (ha : ∀ X n, (a (n + 1)).app X ≫
      (T.obj X).map (homOfLE (Nat.le_succ n)).op = (a n).app X) :
    S ⟶ T ⋙ countableMilnorFunctor where
  app X := TowerAugmentation.augmentationMap
    { source := S.obj X, app n := (a n).app X, naturality := ha X }
  naturality X Y f := TowerAugmentation.augmentationMap_naturality
    { source := S.obj X, app n := (a n).app X, naturality := ha X }
    { source := S.obj Y, app n := (a n).app Y, naturality := ha Y }
    (S.map f) (T.map f) (fun n ↦ (a n).naturality f)

/-- The unit of a functorially augmented tower recovers the supplied maps to each term. -/
@[reassoc (attr := simp)]
public theorem augmentationNatTrans_projection
    {D : Type*} [Category D] (S : D ⥤ CoefficientComplex.{u, v} (A := A))
    (T : D ⥤ Tower.{u, v} (A := A))
    (a : ∀ n, S ⟶ T ⋙ towerEvaluation n)
    (ha : ∀ X n, (a (n + 1)).app X ≫
      (T.obj X).map (homOfLE (Nat.le_succ n)).op = (a n).app X) (X : D) (n : ℕ) :
    (augmentationNatTrans S T a ha).app X ≫ (projection n).app (T.obj X) = (a n).app X :=
  TowerAugmentation.augmentationMap_projection
    { source := S.obj X, app n := (a n).app X, naturality := ha X } n

local instance : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

private noncomputable def mappingConeTriangleMap
    {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) :
    CochainComplex.mappingCone.triangle (oneMinusShift F) ⟶
      CochainComplex.mappingCone.triangle (oneMinusShift G) :=
  Triangle.homMk _ _ (towerProductMap f) (towerProductMap f) (mappingConeMap f)
    (towerProduct_map_naturality f).symm (HomologicalComplex.homotopyCofiber.inr_desc _ _ _) (by
      ext i
      simp [CochainComplex.mappingCone.triangle, mappingConeMap,
        HomologicalComplex.homotopyCofiber.mapArrowHom,
        HomologicalComplex.homotopyCofiber.desc_f,
        HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
        CochainComplex.mappingCone.fst,
        CochainComplex.HomComplex.Cochain.rightShift_v, oneMinusShiftArrowMap])

/-- Objectwise quasi-isomorphisms induce quasi-isomorphisms of strict Milnor mapping fibers.
After localization the specified projections, with the `1 - shift` endomorphism of the product
in the derived category, give the distinguished Milnor triangle. -/
public theorem map_quasiIso_and_milnor_triangle :
    (∀ {F G : Tower.{u, v} (A := A)} (f : F ⟶ G),
      (∀ n : ℕ, QuasiIso (f.app ⟨n⟩)) → QuasiIso (countableMilnorFunctor.map f)) ∧
    (∀ F : Tower.{u, v} (A := A),
      ∃ δ : (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) ⟶
          (DerivedCategory.Q.obj (countableMilnorFunctor.obj F))⟦(1 : ℤ)⟧,
        Triangle.mk (Pi.lift fun n ↦ DerivedCategory.Q.map ((projection n).app F))
          (Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) n -
              Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) (n + 1) ≫
                DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op)) δ ∈
          distTriang (DerivedCategory (ModuleCat.{v} A))) := by
  constructor
  · intro F G f hf
    have hp : QuasiIso (towerProductMap f) := by
      let := Stacks.DerivedProducts.quasiIso_isStableUnderProductsOfShape
        (A := ModuleCat.{v} A) (I := ℕ)
      rw [show towerProductMap f = Limits.limMap (Discrete.natTrans fun X ↦ f.app ⟨X.as⟩) from rfl]
      exact MorphismProperty.limMap
        (W := HomologicalComplex.quasiIso (ModuleCat.{v} A) (ComplexShape.up ℤ)) _
          (fun j ↦ hf j.as)
    have hQ : IsIso (DerivedCategory.Q.map (towerProductMap f)) := by
      rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    have hc : QuasiIso (mappingConeMap f) := by
      rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact isIso₃_of_isIso₁₂ (DerivedCategory.Q.mapTriangle.map (mappingConeTriangleMap f))
        (DerivedCategory.mappingCone_triangle_distinguished (oneMinusShift F))
        (DerivedCategory.mappingCone_triangle_distinguished (oneMinusShift G)) hQ hQ
    show IsIso (DerivedCategory.Q.map
      ((shiftFunctor (CoefficientComplex.{u, v} (A := A)) (-1 : ℤ)).map (mappingConeMap f)))
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_shift_iff]
  · intro F
    let K : ℕ → CoefficientComplex.{u, v} (A := A) := fun n ↦ F.obj ⟨n⟩
    let N := DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCocone.triangle (oneMinusShift F))
    let h₁ : IsLimit (Stacks.DerivedProducts.productFanInDerivedCategory K) :=
      Classical.choice (Stacks.DerivedProducts.isLimit_productFanInDerivedCategory K)
    let h₂ : IsLimit (Fan.mk (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (K n))
        (fun n ↦ Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (K n)) n)) :=
      productIsProduct _
    let e := h₁.conePointUniqueUpToIso h₂
    have he (n : ℕ) : e.hom ≫ Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (K n)) n =
        DerivedCategory.Q.map (Pi.π K n) :=
      h₁.conePointUniqueUpToIso_hom_comp h₂ ⟨n⟩
    let p := Pi.lift fun n : ℕ ↦ DerivedCategory.Q.map ((projection n).app F)
    let s := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) n -
        Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) (n + 1) ≫
          DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op)
    let δ := e.inv ≫ N.mor₃
    refine ⟨δ, ?_⟩
    let T := Triangle.mk p s δ
    have hcomm₁ : N.mor₁ ≫ e.hom = p := by
      refine Pi.hom_ext _ _ fun n ↦ ?_
      rw [Category.assoc, he n]
      simp [N, p, K, projection]
    have hcomm₂ : N.mor₂ ≫ e.hom = e.hom ≫ s := by
      dsimp [N]
      refine Pi.hom_ext _ _ fun n ↦ ?_
      rw [Category.assoc, he n, ← Functor.map_comp, oneMinusShift_π,
        Functor.map_sub, Functor.map_comp]
      dsimp [s]
      rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, he n, ← Category.assoc (f := e.hom)
        (g := Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (K n)) (n + 1)), he (n + 1)]
    have hcomm₃ : N.mor₃ ≫ (Iso.refl N.obj₁).hom⟦(1 : ℤ)⟧' = e.hom ≫ δ := by
      simp [δ]
    let i : N ≅ T := Triangle.isoMk N T (Iso.refl _) e e
      (by dsimp [T]; simpa only [Category.id_comp] using hcomm₁) hcomm₂ hcomm₃
    exact isomorphic_distinguished N
      (DerivedCategory.mappingCocone_triangle_distinguished (oneMinusShift F)) T i.symm

private def productDegreeIso (F : Tower.{u, v} (A := A)) (i : ℤ) :
    (towerProductObj F).X i ≅ ModuleCat.of A (∀ n : ℕ, (F.obj ⟨n⟩).X i) :=
  PreservesProduct.iso (HomologicalComplex.eval _ _ i) (fun n : ℕ ↦ F.obj ⟨n⟩) ≪≫
    ModuleCat.piIsoPi _

@[reassoc (attr := simp)] private lemma productDegreeIso_π
    (F : Tower.{u, v} (A := A)) (i : ℤ) (n : ℕ) :
    (productDegreeIso F i).hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
      (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n).f i := by
  dsimp only [productDegreeIso, Iso.trans_hom]
  rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom,
    piComparison_comp_π]
  rfl

private lemma productDegreeIso_naturality {F G : Tower.{u, v} (A := A)}
    (f : F ⟶ G) (i : ℤ) :
    (towerProductMap f).f i ≫ (productDegreeIso G i).hom =
      (productDegreeIso F i).hom ≫ ModuleCat.ofHom
        (LinearMap.pi fun n : ℕ ↦ ((f.app ⟨n⟩).f i).hom.comp (LinearMap.proj n)) := by
  apply (cancel_mono (ModuleCat.piIsoPi (fun n : ℕ ↦ (G.obj ⟨n⟩).X i)).inv).mp
  refine Pi.hom_ext _ _ fun n ↦ ?_
  simp only [Category.assoc, ModuleCat.piIsoPi_inv_kernel_ι, productDegreeIso_π]
  refine Eq.trans ?_ (productDegreeIso_π_assoc F i n ((f.app ⟨n⟩).f i)).symm
  show (towerProductMap f ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n).f i =
    (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n ≫ f.app ⟨n⟩).f i
  simp [towerProductMap]

private def degreeIso (F : Tower.{u, v} (A := A)) (i : ℤ) :
    (countableMilnorFunctor.obj F).X i ≅ ModuleCat.of A
      ((∀ n : ℕ, (F.obj ⟨n⟩).X i) × (∀ n : ℕ, (F.obj ⟨n⟩).X (i + -1))) :=
  milnorDegreeIso F i ≪≫ biprod.mapIso (productDegreeIso F i) (productDegreeIso F (i + -1)) ≪≫
    ModuleCat.biprodIsoProd _ _

private def degreeMap {F G : Tower.{u, v} (A := A)} (f : F ⟶ G) (i : ℤ) :=
  LinearMap.prodMap
    (LinearMap.pi fun n : ℕ ↦ ((f.app ⟨n⟩).f i).hom.comp (LinearMap.proj n))
    (LinearMap.pi fun n : ℕ ↦ ((f.app ⟨n⟩).f (i + -1)).hom.comp (LinearMap.proj n))

@[reassoc (attr := simp)] private lemma rawBiprod_fst (M N : ModuleCat.{v} A) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.fst A M N) =
      biprod.fst := by
  apply (cancel_epi (ModuleCat.biprodIsoProd M N).inv).mp
  simp

@[reassoc (attr := simp)] private lemma rawBiprod_snd (M N : ModuleCat.{v} A) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.snd A M N) =
      biprod.snd := by
  apply (cancel_epi (ModuleCat.biprodIsoProd M N).inv).mp
  simp

private lemma rawBiprod_naturality {M N M' N' : ModuleCat.{v} A}
    (f : M ⟶ M') (g : N ⟶ N') :
    biprod.map f g ≫ (ModuleCat.biprodIsoProd M' N').hom =
      (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (f.hom.prodMap g.hom) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd M' N').inv).mp
  apply biprod.hom_ext
  · simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
      rawBiprod_fst, biprod.map_fst]
    exact (rawBiprod_fst_assoc M N f).symm
  · simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd,
      rawBiprod_snd, biprod.map_snd]
    exact (rawBiprod_snd_assoc M N g).symm

private lemma biprodMapComp {M N M' N' M'' N'' : ModuleCat.{v} A}
    (f : M ⟶ M') (g : N ⟶ N') (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    biprod.map (f ≫ f') (g ≫ g') = biprod.map f g ≫ biprod.map f' g' := by
  apply biprod.hom_ext <;> simp [Category.assoc]

private lemma degreeIso_naturality {F G : Tower.{u, v} (A := A)}
    (f : F ⟶ G) (i : ℤ) :
    (countableMilnorFunctor.map f).f i ≫ (degreeIso G i).hom =
      (degreeIso F i).hom ≫ ModuleCat.ofHom (degreeMap f i) := by
  dsimp only [degreeIso, Iso.trans_hom, biprod.mapIso_hom]
  rw [← Category.assoc, milnorDegreeIso_naturality]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← biprodMapComp, productDegreeIso_naturality,
    productDegreeIso_naturality, biprodMapComp, Category.assoc, rawBiprod_naturality]
  rfl

private def degreeSequence (S : ShortComplex (Tower.{u, v} (A := A))) (i : ℤ) :
    ShortComplex (ModuleCat.{v} A) :=
  ShortComplex.moduleCatMk (degreeMap S.f i) (degreeMap S.g i) <|
    LinearMap.ext fun x ↦ Prod.ext
      (funext fun n ↦ congrArg (fun f ↦ ((f.app ⟨n⟩).f i).hom (x.1 n)) S.zero)
      (funext fun n ↦ congrArg (fun f ↦ ((f.app ⟨n⟩).f (i + -1)).hom (x.2 n)) S.zero)

private theorem degreeSequence_shortExact (S : ShortComplex (Tower.{u, v} (A := A)))
    (hS : S.ShortExact) (i : ℤ) : (degreeSequence S i).ShortExact := by
  have hs (n : ℕ) (j : ℤ) := (hS.map_of_exact
    ((evaluation _ _).obj (Opposite.op n))).map_of_exact
      (HomologicalComplex.eval _ _ j)
  have hex (n : ℕ) (j : ℤ) :=
    (ShortComplex.moduleCat_exact_iff _).mp (hs n j).exact
  have hinj (n : ℕ) (j : ℤ) :=
    (ModuleCat.mono_iff_injective _).mp (hs n j).mono_f
  have hsurj (n : ℕ) (j : ℤ) :=
    (ModuleCat.epi_iff_surjective _).mp (hs n j).epi_g
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    choose y hy using fun n ↦ hex n i (x.1 n) (congrArg (fun y ↦ y.1 n) hx)
    choose z hz using fun n ↦ hex n (i + -1) (x.2 n) (congrArg (fun y ↦ y.2 n) hx)
    exact ⟨(y, z), Prod.ext (funext hy) (funext hz)⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y h
    exact Prod.ext (funext fun n ↦ hinj n i (congrArg (fun z ↦ z.1 n) h))
      (funext fun n ↦ hinj n (i + -1) (congrArg (fun z ↦ z.2 n) h))
  · rw [ModuleCat.epi_iff_surjective]
    intro x
    choose y hy using fun n ↦ hsurj n i (x.1 n)
    choose z hz using fun n ↦ hsurj n (i + -1) (x.2 n)
    exact ⟨(y, z), Prod.ext (funext hy) (funext hz)⟩

/-- The strict Milnor functor preserves short exact sequences, with its specified cone maps. -/
public theorem countableMilnorFunctor_map_shortExact
    (S : ShortComplex (Tower.{u, v} (A := A))) (hS : S.ShortExact) :
    (S.map countableMilnorFunctor).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  let e : (S.map countableMilnorFunctor).map (HomologicalComplex.eval _ _ i) ≅
      degreeSequence S i := ShortComplex.isoMk (degreeIso S.X₁ i) (degreeIso S.X₂ i)
        (degreeIso S.X₃ i) (degreeIso_naturality S.f i).symm
          (degreeIso_naturality S.g i).symm
  exact ShortComplex.shortExact_of_iso e.symm (degreeSequence_shortExact S hS i)

end CountableMilnorTower

end
