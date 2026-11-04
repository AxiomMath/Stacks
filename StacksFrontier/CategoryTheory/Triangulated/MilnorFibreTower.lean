module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitTriangulatedTower

/-!
# The strict Milnor fibre of a tower of cochain complexes

Let `A` be an abelian category with countable products and let `F : ℕᵒᵖ ⥤ CochainComplex A ℤ`
be a tower of cochain complexes. Writing `Kₙ = F.obj ⟨n⟩` and `fₙ₊₁ : Kₙ₊₁ ⟶ Kₙ` for the
transition maps, the **Milnor endomorphism** of `∏ₙ Kₙ` is the difference map
`(kₙ) ↦ (kₙ - fₙ₊₁(kₙ₊₁))`, and the **strict Milnor fibre** of `F` is the mapping cocone of
that endomorphism. This file builds it as a *functor* of `F`, with its projections onto the
terms of the tower and with a canonical map into it out of any complex carrying a compatible
family of maps to the terms.

Everything here is a formula: no cone in a derived category is chosen, and nothing is
existentially quantified. That is the point — see
`StacksFrontier/CategoryTheory/Triangulated/MilnorFibreDerivedLimit.lean`, where the Milnor fibre
is shown to be a derived limit of the tower *through those projections*, so that the derived
limit and the comparison map into it are named rather than merely known to exist.

## Main definitions

* `Stacks.MilnorTower.towerProduct` — the product of the terms of a tower, as a functor.
* `Stacks.MilnorTower.oneMinusShift` — the Milnor endomorphism of that product. It is
  `CategoryTheory.Pretriangulated.familyDifference` of the terms and transition maps.
* `Stacks.MilnorTower.milnorFunctor` — the strict Milnor fibre, as a functor of the tower.
* `Stacks.MilnorTower.projection` — the natural map from the Milnor fibre to a term of the
  tower.
* `Stacks.MilnorTower.TowerAugmentation` — a complex with a compatible family of maps to the
  terms of a tower, and `Stacks.MilnorTower.TowerAugmentation.augmentationMap` the canonical
  map it induces into the Milnor fibre.

## Main results

* `Stacks.MilnorTower.projectionTransitionHomotopy` — the projections form a cone on the tower
  up to a canonical chain homotopy (not on the nose: the discrepancy is the second cocone
  coordinate).
* `Stacks.MilnorTower.TowerAugmentation.augmentationMap_proj` — the canonical map out of
  an augmented complex recovers the given maps on the nose.
* `Stacks.MilnorTower.degreeIso` — in each degree the Milnor fibre is the biproduct of two
  consecutive degrees of the product of the tower.

## Implementation notes

The functorial map and the canonical map out of an augmented complex are both built with
`CochainComplex.mappingCocone.lift`, whose two arguments are a morphism to the source of the
endomorphism and a cochain of degree `-1` to its target: for the functorial map the second
argument is the second cocone coordinate composed with the product map, and for the
augmentation map it is zero. Defining the functorial map this way rather than as a shift of
`HomologicalComplex.homotopyCofiber.mapArrowHom` makes its two coordinates
(`Stacks.MilnorTower.mappingCoconeMap_fst` and `Stacks.MilnorTower.mappingCoconeMap_snd`)
instances of `CochainComplex.mappingCocone.lift_fst` and
`CochainComplex.mappingCocone.lift_f_snd_v` rather than degreewise computations with shifted
cochains.

`Stacks.MilnorTower.oneMinusShift` is `CategoryTheory.Pretriangulated.familyDifference`, the
difference map of a family with transition maps, and not a new definition; the definition of
`CategoryTheory.Pretriangulated.IsDerivedLimit` is spelled with the same term.

## Relation to `Homology/DerivedComplete/CountableMilnorTower.lean`

`CountableMilnorTower` is this construction at `CochainComplex (ModuleCat A) ℤ` for a ring `A`,
and is subsumed by it: `CountableMilnorTower.oneMinusShift`, `.towerProduct`,
`.countableMilnorFunctor`, `.projection`, `.TowerAugmentation` and its `augmentationMap` have
the same definitions as the ones here. It is left in place rather than rewritten to delegate,
and the reason is mechanical: its functorial map `CountableMilnorTower.mappingCoconeMap` is the
shift by `-1` of `HomologicalComplex.homotopyCofiber.mapArrowHom` where
`Stacks.MilnorTower.mappingCoconeMap` is a `CochainComplex.mappingCocone.lift`, so
`CountableMilnorTower.countableMilnorFunctor` and `Stacks.MilnorTower.milnorFunctor` are not
the same functor until those two are identified, and `CountableMilnorTower.augmentationNatTrans`
is typed by that functor. Delegating `oneMinusShift` alone was tried and breaks three
consumers, whose proofs unfold it by name in a `simp` set:
`Homology/DerivedComplete/MilnorEpiTower.lean` (`shortExact_ofCone`),
`Homology/DerivedComplete/AdicDerivedCompletionKoszul.lean`
(`constantTower_augmentation_quasiIso`) and
`Algebra/Category/ModuleCat/Sheaf/DifferentialGradedChaoticMilnorGlobalSections.lean`
(`milnorAug_naturality`).

What this file therefore does *not* introduce is an abbreviation for
`CategoryTheory.Limits.Pi.lift a.app`: `CountableMilnorTower.TowerAugmentation.productLift` is
the one in the library, and the facts stated here about that map are stated about
`CategoryTheory.Limits.Pi.lift a.app` itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive
open CochainComplex CochainComplex.HomComplex

universe v u

namespace Stacks.MilnorTower

/-! ### Two coordinates of a mapping cocone -/

section MappingCocone

variable {C : Type u} [Category.{v} C] [Preadditive C] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
  [HomologicalComplex.HasHomotopyCofiber φ]

/-- **The two coordinates of a mapping cocone are jointly monic in each degree.** -/
public theorem mappingCocone_hom_ext_X {Z : C} (n m : ℤ) (hnm : n + -1 = m)
    {x y : Z ⟶ (mappingCocone φ).X n}
    (h₁ : x ≫ (mappingCocone.fst φ).f n = y ≫ (mappingCocone.fst φ).f n)
    (h₂ : x ≫ (mappingCocone.snd φ).v n m hnm = y ≫ (mappingCocone.snd φ).v n m hnm) :
    x = y := by
  have key : x ≫ 𝟙 _ = y ≫ 𝟙 _ := by
    rw [← mappingCocone.id_X φ n m hnm, comp_add, comp_add, ← Category.assoc, ← Category.assoc,
      ← Category.assoc, ← Category.assoc, h₁, h₂]
  simpa using key

/-- **Two maps into a mapping cocone with the same two coordinates are equal.** -/
public theorem mappingCocone_hom_ext {M : CochainComplex C ℤ} {x y : M ⟶ mappingCocone φ}
    (h₁ : x ≫ mappingCocone.fst φ = y ≫ mappingCocone.fst φ)
    (h₂ : ∀ (n m : ℤ) (hnm : n + -1 = m), x.f n ≫ (mappingCocone.snd φ).v n m hnm =
      y.f n ≫ (mappingCocone.snd φ).v n m hnm) :
    x = y :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    mappingCocone_hom_ext_X φ n (n + -1) rfl
      (by simpa using congrArg (fun g ↦ HomologicalComplex.Hom.f g n) h₁) (h₂ n (n + -1) rfl)

/-- **The differential of the second coordinate of a mapping cocone** is the negative of its
first coordinate followed by the map the cocone is taken of.

Every step is staged as a `have` whose statement mentions either `mappingCocone φ` or
`(mappingCone φ)⟦-1⟧` but never both: `mappingCocone` is a `def` for the shift, so a goal
mixing the two spellings is not type-correct at `instances` transparency and neither `rw` nor
`simp` will fire on it. -/
public theorem δ_mappingCocone_snd :
    δ (-1) 0 (mappingCocone.snd φ) = -Cochain.ofHom (mappingCocone.fst φ ≫ φ) := by
  have h1 : δ (-1) 0 (mappingCocone.snd φ) =
      ((-1 : ℤ).negOnePow) • (δ 0 1 (mappingCone.snd φ)).leftShift (-1) 0 (by omega) :=
    Cochain.δ_leftShift (mappingCone.snd φ) (-1) (-1) 0 (by omega) 1 (by omega)
  have h2 : (δ 0 1 (mappingCone.snd φ)).leftShift (-1) 0 (by omega) =
      -(((mappingCone.fst φ) : Cochain (mappingCone φ) K 1).leftShift (-1) 0
        (by omega)).comp (Cochain.ofHom φ) (add_zero 0) := by
    rw [mappingCone.δ_snd, Cochain.leftShift_neg, Cochain.leftShift_comp_zero_cochain]
  have hf : mappingCocone.fst φ =
      -(((mappingCone.fst φ).leftShift (-1) 0 (by omega)).homOf) := rfl
  have e1 : mappingCocone.fst φ ≫ φ =
      -((((mappingCone.fst φ).leftShift (-1) 0 (by omega)).homOf) ≫ φ) :=
    (congrArg (fun w : mappingCocone φ ⟶ K ↦ w ≫ φ) hf).trans (Preadditive.neg_comp _ _)
  have e2 : Cochain.ofHom (mappingCocone.fst φ ≫ φ) =
      -Cochain.ofHom ((((mappingCone.fst φ).leftShift (-1) 0 (by omega)).homOf) ≫ φ) :=
    (congrArg Cochain.ofHom e1).trans (Cochain.ofHom_neg _)
  have e3 : Cochain.ofHom ((((mappingCone.fst φ).leftShift (-1) 0 (by omega)).homOf) ≫ φ) =
      (((mappingCone.fst φ) : Cochain (mappingCone φ) K 1).leftShift (-1) 0
        (by omega)).comp (Cochain.ofHom φ) (add_zero 0) :=
    (Cochain.ofHom_comp _ _).trans
      (congrArg (fun c ↦ Cochain.comp c (Cochain.ofHom φ) (add_zero 0))
        (Cocycle.cochain_ofHom_homOf_eq_coe _))
  have h3 : -Cochain.ofHom (mappingCocone.fst φ ≫ φ) =
      (((mappingCone.fst φ) : Cochain (mappingCone φ) K 1).leftShift (-1) 0
        (by omega)).comp (Cochain.ofHom φ) (add_zero 0) :=
    (congrArg (fun c ↦ -c) e2).trans ((neg_neg _).trans e3)
  rw [h1, h2, h3]
  simp
  rfl

/-- The second coordinate of a mapping cocone, as the witness that the first coordinate is
killed by the map the cocone is taken of up to a coboundary: the form in which
`CochainComplex.mappingCocone.lift` consumes it. -/
public theorem δ_mappingCocone_snd_add :
    δ (-1) 0 (mappingCocone.snd φ) + Cochain.ofHom (mappingCocone.fst φ ≫ φ) = 0 := by
  rw [δ_mappingCocone_snd, neg_add_cancel]

end MappingCocone

/-! ### The product of the terms of a tower -/

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]

/-- The product of the terms of a tower of cochain complexes. -/
public abbrev towerProductObj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex A ℤ :=
  ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩

/-- The product map induced by a strict morphism of towers. -/
public abbrev towerProductMap {F G : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : F ⟶ G) :
    towerProductObj F ⟶ towerProductObj G :=
  Limits.Pi.map fun n ↦ f.app ⟨n⟩

/-- The product map of the identity is the identity. -/
@[simp]
public theorem towerProductMap_id (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    towerProductMap (𝟙 F) = 𝟙 (towerProductObj F) :=
  Limits.Pi.map_id

/-- The product map of a composite is the composite of the product maps. -/
@[simp]
public theorem towerProductMap_comp {F G H : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (f : F ⟶ G) (g : G ⟶ H) :
    towerProductMap (f ≫ g) = towerProductMap f ≫ towerProductMap g :=
  (Limits.Pi.map_comp_map _ _).symm

/-- The product of all the terms of a tower of cochain complexes, as a functor. -/
public def towerProduct :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ where
  obj := towerProductObj
  map := towerProductMap
  map_id := towerProductMap_id
  map_comp := towerProductMap_comp

/-- The Milnor endomorphism `(kₙ) ↦ (kₙ - fₙ₊₁(kₙ₊₁))` of the product of the terms of a
tower. -/
public def oneMinusShift (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    towerProductObj F ⟶ towerProductObj F :=
  familyDifference (fun n : ℕ ↦ F.obj ⟨n⟩) fun n ↦ F.map (homOfLE (Nat.le_succ n)).op

/-- The components of the Milnor endomorphism are the identity minus the transition map. -/
@[reassoc (attr := simp)]
public theorem oneMinusShift_π (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) :
    oneMinusShift F ≫ Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n =
      Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n -
        Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op :=
  familyDifference_π _ _ n

/-- Strict maps of towers commute with the Milnor endomorphism. -/
@[reassoc]
public theorem towerProduct_map_naturality {F G : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : F ⟶ G) :
    towerProductMap f ≫ oneMinusShift G = oneMinusShift F ≫ towerProductMap f :=
  piMap_familyDifference (fun n ↦ f.app ⟨n⟩) fun _ ↦ (f.naturality _).symm

/-! ### The strict Milnor fibre -/

/-- The **strict Milnor fibre** of a tower of cochain complexes: the mapping cocone of the
Milnor endomorphism of the product of its terms. -/
public abbrev milnorObj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex A ℤ :=
  mappingCocone (oneMinusShift F)

/-- The induced map of the Milnor fibres of a strict morphism of towers: its first coordinate
is the product map, and its second is the second cocone coordinate followed by the product
map. -/
public def mappingCoconeMap {F G : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : F ⟶ G) :
    milnorObj F ⟶ milnorObj G :=
  mappingCocone.lift (oneMinusShift G)
    (mappingCocone.fst (oneMinusShift F) ≫ towerProductMap f)
    ((mappingCocone.snd (oneMinusShift F)).comp
      (Cochain.ofHom (towerProductMap f)) (add_zero (-1))) (by
    rw [δ_comp_ofHom, δ_mappingCocone_snd, Cochain.neg_comp, ← Cochain.ofHom_comp,
      show (mappingCocone.fst (oneMinusShift F) ≫ towerProductMap f) ≫ oneMinusShift G =
          (mappingCocone.fst (oneMinusShift F) ≫ oneMinusShift F) ≫ towerProductMap f by
        rw [Category.assoc, Category.assoc, towerProduct_map_naturality],
      neg_add_cancel])

/-- **The first coordinate of the induced map of Milnor fibres is the product map.** -/
@[reassoc (attr := simp)]
public theorem mappingCoconeMap_fst {F G : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : F ⟶ G) :
    mappingCoconeMap f ≫ mappingCocone.fst (oneMinusShift G) =
      mappingCocone.fst (oneMinusShift F) ≫ towerProductMap f :=
  mappingCocone.lift_fst _ _ _ _

/-- **The second coordinate of the induced map of Milnor fibres is the second cocone
coordinate followed by the product map.** -/
@[reassoc (attr := simp)]
public theorem mappingCoconeMap_snd {F G : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : F ⟶ G)
    (n m : ℤ) (hnm : n + -1 = m) :
    (mappingCoconeMap f).f n ≫ (mappingCocone.snd (oneMinusShift G)).v n m hnm =
      (mappingCocone.snd (oneMinusShift F)).v n m hnm ≫ (towerProductMap f).f m := by
  rw [mappingCoconeMap, mappingCocone.lift_f_snd_v,
    Cochain.comp_v _ _ (add_zero (-1)) n m m hnm (add_zero m), Cochain.ofHom_v]

/-- The induced map of Milnor fibres of the identity is the identity. -/
@[simp]
public theorem mappingCoconeMap_id (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    mappingCoconeMap (𝟙 F) = 𝟙 (milnorObj F) := by
  refine mappingCocone_hom_ext (oneMinusShift F) ?_ fun n m hnm ↦ ?_
  · simp
  · simp

/-- The induced map of Milnor fibres of a composite is the composite. -/
@[simp]
public theorem mappingCoconeMap_comp {F G H : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (f : F ⟶ G) (g : G ⟶ H) :
    mappingCoconeMap (f ≫ g) = mappingCoconeMap f ≫ mappingCoconeMap g := by
  refine mappingCocone_hom_ext (oneMinusShift H) ?_ fun n m hnm ↦ ?_
  · simp
  · simp

/-- The strict Milnor fibre of a tower of cochain complexes, as a functor of the tower. -/
public def milnorFunctor :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ where
  obj := milnorObj
  map f := mappingCoconeMap f
  map_id := mappingCoconeMap_id
  map_comp := mappingCoconeMap_comp

/-- The induced map of Milnor fibres is the action of `Stacks.MilnorTower.milnorFunctor`. -/
public theorem milnorFunctor_map {F G : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : F ⟶ G) :
    milnorFunctor.map f = mappingCoconeMap f :=
  rfl

/-! ### The degreewise description -/

/-- **In each degree the Milnor fibre is the biproduct of two consecutive degrees of the
product of the terms of the tower**, through the two cocone coordinates. -/
public def degreeIso (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i j : ℤ) (hij : i + -1 = j) :
    (milnorObj F).X i ≅ (towerProductObj F).X i ⊞ (towerProductObj F).X j where
  hom := biprod.lift ((mappingCocone.fst (oneMinusShift F)).f i)
    ((mappingCocone.snd (oneMinusShift F)).v i j hij)
  inv := biprod.desc ((mappingCocone.inl (oneMinusShift F)).v i i (add_zero i))
    ((mappingCocone.inr (oneMinusShift F)).1.v j i (by omega))
  hom_inv_id := by
    rw [biprod.lift_desc]
    exact mappingCocone.id_X _ i j hij
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    all_goals simp only [← Category.assoc, biprod.inl_desc, biprod.inr_desc]
    all_goals simp

/-- The first component of `Stacks.MilnorTower.degreeIso` is the first cocone coordinate in
degree `i`. -/
@[reassoc (attr := simp)]
public theorem degreeIso_hom_fst (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i j : ℤ) (hij : i + -1 = j) :
    (degreeIso F i j hij).hom ≫ biprod.fst = (mappingCocone.fst (oneMinusShift F)).f i := by
  simp [degreeIso]

/-- The second component of `Stacks.MilnorTower.degreeIso` is the second cocone coordinate
from degree `i` to degree `j`. -/
@[reassoc (attr := simp)]
public theorem degreeIso_hom_snd (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i j : ℤ) (hij : i + -1 = j) :
    (degreeIso F i j hij).hom ≫ biprod.snd =
      (mappingCocone.snd (oneMinusShift F)).v i j hij := by
  simp [degreeIso]

/-- **The induced map of Milnor fibres is the biproduct of two product maps**, read through
`Stacks.MilnorTower.degreeIso`. -/
@[reassoc]
public theorem degreeIso_naturality {F G : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : F ⟶ G)
    (i j : ℤ) (hij : i + -1 = j) :
    (mappingCoconeMap f).f i ≫ (degreeIso G i j hij).hom =
      (degreeIso F i j hij).hom ≫
        biprod.map ((towerProductMap f).f i) ((towerProductMap f).f j) := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, degreeIso_hom_fst, Category.assoc, biprod.map_fst,
      degreeIso_hom_fst_assoc]
    exact congrArg (fun w ↦ HomologicalComplex.Hom.f w i) (mappingCoconeMap_fst f)
  · rw [Category.assoc, degreeIso_hom_snd, Category.assoc, biprod.map_snd,
      degreeIso_hom_snd_assoc, mappingCoconeMap_snd]

/-! ### The projections onto the terms of the tower -/

/-- Evaluation of a tower of cochain complexes at `n`. -/
public abbrev towerEvaluation (n : ℕ) :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ :=
  (evaluation ℕᵒᵖ (CochainComplex A ℤ)).obj ⟨n⟩

/-- **The projection from the Milnor fibre of a tower to its `n`-th term**: the first cocone
coordinate followed by the `n`-th projection of the product. -/
public def proj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) : milnorObj F ⟶ F.obj ⟨n⟩ :=
  mappingCocone.fst (oneMinusShift F) ≫ Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n

/-- **The projections are natural in the tower.** -/
@[reassoc (attr := simp)]
public theorem mappingCoconeMap_proj {F G : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : F ⟶ G) (n : ℕ) :
    mappingCoconeMap f ≫ proj G n = proj F n ≫ f.app ⟨n⟩ := by
  rw [proj, proj, mappingCoconeMap_fst_assoc, Category.assoc, Limits.Pi.map_π]

/-- The projections of the Milnor fibre, as a natural transformation. -/
public def projection (n : ℕ) :
    milnorFunctor (A := A) ⟶ towerEvaluation (A := A) n where
  app F := proj F n
  naturality _ _ f := mappingCoconeMap_proj f n

/-- The components of `Stacks.MilnorTower.projection` are the projections. -/
public theorem projection_app (n : ℕ) (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (projection n).app F = proj F n :=
  rfl

/-- **The projections form a cone on the tower up to a canonical chain homotopy.** The
discrepancy is the second cocone coordinate followed by the `n`-th projection of the product:
the projections do *not* commute with the transition maps on the nose, and the difference is a
coboundary. -/
public def projectionTransitionHomotopy (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) :
    Homotopy (proj F (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) (proj F n) := by
  refine (Cochain.equivHomotopy _ _).symm ⟨(mappingCocone.snd (oneMinusShift F)).comp
    (Cochain.ofHom (Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n)) (add_zero (-1)), ?_⟩
  rw [δ_comp_ofHom, δ_mappingCocone_snd, Cochain.neg_comp, ← Cochain.ofHom_comp,
    Category.assoc, oneMinusShift_π, comp_sub, Cochain.ofHom_sub, neg_sub, proj, proj,
    Category.assoc, sub_add_cancel]

/-! ### Maps into the Milnor fibre out of an augmented complex -/

/-- A cochain complex together with a compatible family of maps to the terms of a tower. -/
public structure TowerAugmentation (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) where
  /-- The augmenting complex. -/
  source : CochainComplex A ℤ
  /-- The map to the `n`-th term. -/
  app (n : ℕ) : source ⟶ F.obj ⟨n⟩
  /-- Compatibility with the transition maps. -/
  naturality (n : ℕ) :
    app (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = app n

namespace TowerAugmentation

variable {F : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : TowerAugmentation F)

/-- **The Milnor endomorphism kills the map to the product of the terms assembled from a
compatible family.** -/
@[reassoc (attr := simp)]
public theorem piLift_oneMinusShift : Limits.Pi.lift a.app ≫ oneMinusShift F = 0 :=
  Limits.Pi.hom_ext _ _ fun n ↦ by
    rw [Category.assoc, oneMinusShift_π, comp_sub, Limits.Pi.lift_π, ← Category.assoc,
      Limits.Pi.lift_π, a.naturality n, sub_self, zero_comp]

/-- **The canonical map from an augmented complex to the Milnor fibre of the tower.** Its
first coordinate is the map to the product and its second coordinate is zero; it is a formula
in the augmentation, with nothing chosen. -/
public def augmentationMap : a.source ⟶ milnorObj F :=
  mappingCocone.lift (oneMinusShift F) (Limits.Pi.lift a.app) 0 (by
    rw [δ_zero, zero_add, piLift_oneMinusShift, Cochain.ofHom_zero])

/-- The first cocone coordinate of `augmentationMap` is the map to the product of the terms
of the tower assembled from the augmentation. -/
@[reassoc (attr := simp)]
public theorem augmentationMap_fst :
    augmentationMap a ≫ mappingCocone.fst (oneMinusShift F) = Limits.Pi.lift a.app :=
  mappingCocone.lift_fst _ _ _ _

/-- The second cocone coordinate of `augmentationMap` vanishes in every degree. -/
@[reassoc (attr := simp)]
public theorem augmentationMap_snd (n m : ℤ) (hnm : n + -1 = m) :
    (augmentationMap a).f n ≫ (mappingCocone.snd (oneMinusShift F)).v n m hnm = 0 := by
  rw [augmentationMap, mappingCocone.lift_f_snd_v]
  exact Cochain.zero_v _ _ _

/-- **The canonical map out of an augmented complex recovers the given maps**: followed by the
`n`-th projection of the Milnor fibre it is the `n`-th map of the augmentation, on the nose. -/
@[reassoc (attr := simp)]
public theorem augmentationMap_proj (n : ℕ) :
    augmentationMap a ≫ proj F n = a.app n := by
  rw [proj, augmentationMap_fst_assoc, Limits.Pi.lift_π]

/-- **The canonical map out of an augmented complex is natural** in the augmented complex and
the tower together. -/
@[reassoc]
public theorem augmentationMap_naturality {G : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (b : TowerAugmentation G) (k : a.source ⟶ b.source) (f : F ⟶ G)
    (h : ∀ n, k ≫ b.app n = a.app n ≫ f.app ⟨n⟩) :
    k ≫ augmentationMap b = augmentationMap a ≫ mappingCoconeMap f := by
  refine mappingCocone_hom_ext _ ?_ fun n m hnm ↦ ?_
  · rw [Category.assoc, augmentationMap_fst, Category.assoc, mappingCoconeMap_fst,
      augmentationMap_fst_assoc]
    refine Limits.Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, Limits.Pi.lift_π, Category.assoc, Limits.Pi.map_π,
      Limits.Pi.lift_π_assoc]
    exact h n
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc,
      augmentationMap_snd, comp_zero, Category.assoc, mappingCoconeMap_snd,
      augmentationMap_snd_assoc, zero_comp]

end TowerAugmentation

/-- **A functorial family of compatible augmentations gives a natural map into the Milnor
fibre.** -/
public def augmentationNatTrans {D : Type*} [Category D] (S : D ⥤ CochainComplex A ℤ)
    (T : D ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ)) (a : ∀ n, S ⟶ T ⋙ towerEvaluation n)
    (ha : ∀ X n, (a (n + 1)).app X ≫
      (T.obj X).map (homOfLE (Nat.le_succ n)).op = (a n).app X) :
    S ⟶ T ⋙ milnorFunctor where
  app X := TowerAugmentation.augmentationMap
    { source := S.obj X, app n := (a n).app X, naturality := ha X }
  naturality X Y f := TowerAugmentation.augmentationMap_naturality
    { source := S.obj X, app n := (a n).app X, naturality := ha X }
    { source := S.obj Y, app n := (a n).app Y, naturality := ha Y }
    (S.map f) (T.map f) fun n ↦ (a n).naturality f

/-- The natural map of `Stacks.MilnorTower.augmentationNatTrans` recovers the given maps. -/
@[reassoc (attr := simp)]
public theorem augmentationNatTrans_projection {D : Type*} [Category D]
    (S : D ⥤ CochainComplex A ℤ) (T : D ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ))
    (a : ∀ n, S ⟶ T ⋙ towerEvaluation n)
    (ha : ∀ X n, (a (n + 1)).app X ≫
      (T.obj X).map (homOfLE (Nat.le_succ n)).op = (a n).app X) (X : D) (n : ℕ) :
    (augmentationNatTrans S T a ha).app X ≫ proj (T.obj X) n = (a n).app X :=
  TowerAugmentation.augmentationMap_proj
    { source := S.obj X, app n := (a n).app X, naturality := ha X } n

end Stacks.MilnorTower

end
