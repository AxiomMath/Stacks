module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Triangulated.MilnorFibreTower

/-!
# The strict Milnor fibre is a derived limit, through its own projections

Let `A` be an abelian category with countable products whose derived category also has them, and
let `F : ℕᵒᵖ ⥤ CochainComplex A ℤ` be a tower of cochain complexes whose product comparison map
`Q(∏ₙ Kₙ) ⟶ ∏ₙ Q(Kₙ)` is invertible. The strict Milnor fibre
`Stacks.MilnorTower.milnorObj F` of `MilnorFibreTower.lean` is a *named* object of
`CochainComplex A ℤ` with *named* projections `Stacks.MilnorTower.proj F n` onto the terms of
the tower. This file proves that its image in `D(A)` is a derived limit of the tower
`F ⋙ DerivedCategory.Q` **through the images of those projections**, and that the canonical
map out of an augmented complex is the comparison map of that presentation.

That is the whole point of the construction. `CategoryTheory.Pretriangulated.IsDerivedLimit`
quantifies over both the structural map and the connecting map of its triangle, and
`NoetherianAdicCompletion.IsDerivedLimitWithProjections` still quantifies over the connecting
map; neither names an object, so neither can be transported along a functor or compared with
another presentation except up to a non-unique isomorphism. Here the object, the projections
and the comparison map out of a cone are all formulas, and only the connecting map — a `Prop`
witness nothing downstream consumes — remains existentially quantified.

## Main results

* `Stacks.MilnorTower.distTriang_Q_milnorObj` — the Milnor triangle of `F` in `D(A)`, with all
  three of its maps formulas in `F`: the structural map is the product of the images of the
  projections, and the connecting map is `Stacks.MilnorTower.milnorConnecting`.
* `Stacks.MilnorTower.exists_distTriang_Q_milnorObj` — the same with the connecting map
  forgotten. This is
  `NoetherianAdicCompletion.IsDerivedLimitWithProjections (F ⋙ DerivedCategory.Q)`
  `(DerivedCategory.Q.obj (milnorObj F)) (fun n ↦ DerivedCategory.Q.map (proj F n))` written
  out, so that no import of the ring-theoretic file that predicate lives in is needed.
* `Stacks.MilnorTower.isDerivedLimit_Q_milnorObj` — the same statement as the predicate
  `CategoryTheory.Pretriangulated.IsDerivedLimit`.
* `Stacks.MilnorTower.Q_proj_succ_comp_map` — the images of the projections form a cone on
  `F ⋙ DerivedCategory.Q`.

## Implementation notes

The product `∏ₙ Q(Kₙ)` taken in `D(A)` and the image `Q(∏ₙ Kₙ)` of the product taken in
`CochainComplex A ℤ` are different objects, and the whole file runs on the comparison map
between them. The proof transports the mapping-cocone triangle of the Milnor endomorphism along
`Stacks.MilnorTower.towerProductIso`. The two squares to check are that that isomorphism
carries `Q(fst)` to the product of the `Q(proj F n)` and `Q(1 - shift)` to the Milnor difference
of `F ⋙ Q`, both of which are checked on components by `CategoryTheory.Limits.Pi.hom_ext`.

Invertibility of the comparison map is carried as an explicit hypothesis `hpc` rather than
derived from an instance, because the two suppliers of it have incomparable hypotheses and only
one reaches sheaves of modules on a site.

* Exactness of the countable products of `A` — Grothendieck's axiom AB4\* — gives it through
  `Stacks.DerivedProducts.preservesLimitsOfShape_Q`, for *every* tower. This is [Stacks, Tag
  07KC], it holds in `ModuleCat R`, and it is how every earlier consumer of this file obtained
  the triangle.
* K-injectivity of the terms of the tower gives it through
  `Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective`, for *no* exactness at all. This
  is [Stacks, Tag 0BK6]: a termwise product of K-injective complexes is K-injective and computes
  the product in the derived category.

AB4\* fails for sheaves of modules on a site — a countable product of epimorphisms of sheaves
need not be an epimorphism — so the second route is the only one available there, and the
hypothesis form is what lets this file be used on both sides of that divide. The countable
products of `D(A)` are an instance binder for the same reason; for sheaves of modules they come
from `Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`, which is the
same K-injective argument run for the mere existence of the products.

## References

* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive
open CochainComplex CochainComplex.HomComplex

universe w v u

namespace Stacks.MilnorTower

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasProductsOfShape ℕ A] [HasProductsOfShape ℕ (DerivedCategory A)]

omit [HasProductsOfShape ℕ (DerivedCategory A)] in
/-- **The images of the projections form a cone on the tower in `D(A)`.** On the nose the
projections only form a cone up to the homotopy
`Stacks.MilnorTower.projectionTransitionHomotopy`; after localization that homotopy becomes an
equality. -/
@[reassoc (attr := simp)]
public theorem Q_proj_succ_comp_map (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) :
    DerivedCategory.Q.map (proj F (n + 1)) ≫
        DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op) =
      DerivedCategory.Q.map (proj F n) :=
  (DerivedCategory.Q.map_comp _ _).symm.trans
    (DerivedCategory.Q_map_eq_of_homotopy _ (projectionTransitionHomotopy F n))

/-- **Exactness of the countable products of `A` makes the product comparison map invertible at
every tower.** This is the AB4\* supplier of the hypothesis `hpc` below, named so that the
consumers which do have AB4\* need not repeat the instance argument. It is [Stacks, Tag 07KC]
through `Stacks.DerivedProducts.preservesLimitsOfShape_Q`; the K-injective supplier, which needs
no exactness, is `Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective`. -/
public theorem isIso_piComparison_Q_of_hasExactLimits (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    [HasExactLimitsOfShape (Discrete ℕ) A] :
    IsIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩) :=
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := A) (I := ℕ)
  inferInstance

/-- The comparison isomorphism between the image in `D(A)` of the product of the terms of a
tower and the product of their images, at a tower whose product comparison map is invertible.

Invertibility is a hypothesis rather than a consequence because there are two different reasons
it can hold, and only one of them is available for sheaves of modules on a site. It follows from
exactness of the countable products of `A` — Grothendieck's axiom AB4\*, through
`Stacks.DerivedProducts.preservesLimitsOfShape_Q` — and also, with no exactness whatsoever, from
the terms of the tower being K-injective, through
`Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective` ([Stacks, Tag 0BK6]). AB4\* fails
for sheaves of modules on a site, so the second route is the one that reaches them. -/
public def towerProductIso (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (hpc : IsIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩)) :
    DerivedCategory.Q.obj (towerProductObj F) ≅
      ∏ᶜ fun k : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨k⟩) :=
  haveI := hpc
  asIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩)

/-- The forward map of `Stacks.MilnorTower.towerProductIso F hpc` followed by the `n`-th product
projection is the image in `D(A)` of the `n`-th projection of the product of the tower. -/
@[reassoc (attr := simp)]
public theorem towerProductIso_hom_π (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (hpc : IsIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩)) (n : ℕ) :
    (towerProductIso F hpc).hom ≫ Pi.π (fun k : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨k⟩)) n =
      DerivedCategory.Q.map (Pi.π (fun k : ℕ ↦ F.obj ⟨k⟩) n) :=
  piComparison_comp_π _ _ n

/-- **The connecting map of the Milnor triangle of a tower of cochain complexes.** The third
map of the mapping-cocone triangle of the Milnor endomorphism, read through
`Stacks.MilnorTower.towerProductIso`. Like the object and the projections it is a formula, so
the Milnor triangle of `Stacks.MilnorTower.distTriang_Q_milnorObj` has no existential in it at
all. -/
public def milnorConnecting (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (hpc : IsIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩)) :
    (∏ᶜ fun k : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨k⟩)) ⟶
      (DerivedCategory.Q.obj (milnorObj F))⟦(1 : ℤ)⟧ :=
  (towerProductIso F hpc).inv ≫
    (DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle (oneMinusShift F))).mor₃

/-- **The Milnor triangle of a tower of cochain complexes, with all three of its maps named.**
The image in `D(A)` of the strict Milnor fibre of `F` sits in a distinguished triangle whose
first map is the product of the images of the projections `Stacks.MilnorTower.proj F n`, whose
second map is the Milnor difference of `F ⋙ DerivedCategory.Q`, and whose connecting map is
`Stacks.MilnorTower.milnorConnecting F`. -/
public theorem distTriang_Q_milnorObj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (hpc : IsIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩)) :
    Triangle.mk (Pi.lift fun n : ℕ ↦ DerivedCategory.Q.map (proj F n))
        (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) n -
            Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) (n + 1) ≫
              DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op))
        (milnorConnecting F hpc) ∈
      distTriang (DerivedCategory A) := by
  have sq1 : DerivedCategory.Q.map (mappingCocone.fst (oneMinusShift F)) ≫
      (towerProductIso F hpc).hom =
      Pi.lift fun n : ℕ ↦ DerivedCategory.Q.map (proj F n) :=
    Limits.Pi.hom_ext _ _ fun n ↦ by
      rw [Category.assoc, towerProductIso_hom_π, Limits.Pi.lift_π, proj,
        DerivedCategory.Q.map_comp]
  have sq2 : DerivedCategory.Q.map (oneMinusShift F) ≫ (towerProductIso F hpc).hom =
      (towerProductIso F hpc).hom ≫
      Pi.lift fun n : ℕ ↦
        Pi.π (fun k : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨k⟩)) n -
          Pi.π (fun k : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨k⟩)) (n + 1) ≫
            DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op) :=
    Limits.Pi.hom_ext _ _ fun n ↦ by
      rw [Category.assoc, towerProductIso_hom_π, Category.assoc, Limits.Pi.lift_π, comp_sub,
        towerProductIso_hom_π, ← Category.assoc (f := (towerProductIso F hpc).hom),
        towerProductIso_hom_π, ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
        ← CategoryTheory.Functor.map_sub]
      exact congrArg DerivedCategory.Q.map (oneMinusShift_π F n)
  refine isomorphic_distinguished _
    (DerivedCategory.mappingCocone_triangle_distinguished (oneMinusShift F)) _ (Iso.symm ?_)
  refine Triangle.isoMk _ _ (Iso.refl _) (towerProductIso F hpc) (towerProductIso F hpc)
    ?_ sq2 ?_
  · exact sq1.trans (Category.id_comp _).symm
  · exact (congrArg (fun w ↦ (DerivedCategory.Q.mapTriangle.obj
          (mappingCocone.triangle (oneMinusShift F))).mor₃ ≫ w)
        ((CategoryTheory.shiftFunctor (DerivedCategory A) (1 : ℤ)).map_id _)).trans
      ((Category.comp_id _).trans ((Category.id_comp _).symm.trans
        ((congrArg (fun w ↦ w ≫ (DerivedCategory.Q.mapTriangle.obj
            (mappingCocone.triangle (oneMinusShift F))).mor₃)
          (towerProductIso F hpc).hom_inv_id.symm).trans (Category.assoc _ _ _))))

/-- **The Milnor triangle of a tower of cochain complexes, with its structural map named.**
The connecting map of `Stacks.MilnorTower.distTriang_Q_milnorObj` forgotten.

Unfolding `NoetherianAdicCompletion.IsDerivedLimitWithProjections`, this says
`Q(milnorObj F)` is a derived limit of `F ⋙ DerivedCategory.Q` through the cone
`fun n ↦ Q.map (proj F n)`. -/
public theorem exists_distTriang_Q_milnorObj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (hpc : IsIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩)) :
    ∃ δ : (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) ⟶
        (DerivedCategory.Q.obj (milnorObj F))⟦(1 : ℤ)⟧,
      Triangle.mk (Pi.lift fun n : ℕ ↦ DerivedCategory.Q.map (proj F n))
        (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) n -
            Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) (n + 1) ≫
              DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op)) δ ∈
        distTriang (DerivedCategory A) :=
  ⟨milnorConnecting F hpc, distTriang_Q_milnorObj F hpc⟩

/-- **The strict Milnor fibre of a tower of cochain complexes is a derived limit of the
tower.** The projections are forgotten; see
`Stacks.MilnorTower.exists_distTriang_Q_milnorObj` for the form that names them. -/
public theorem isDerivedLimit_Q_milnorObj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (hpc : IsIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩))
    [HasProduct fun n : ℕ ↦ (F ⋙ DerivedCategory.Q).obj ⟨n⟩] :
    IsDerivedLimit (F ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj (milnorObj F)) := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_Q_milnorObj F hpc
  exact ⟨_, δ, hδ⟩

omit [HasProductsOfShape ℕ (DerivedCategory A)] in
/-- **The canonical map out of an augmented complex is the comparison map of the presentation**:
its image in `D(A)` followed by the `n`-th projection of the Milnor fibre is the image of the
`n`-th map of the augmentation. -/
@[reassoc (attr := simp)]
public theorem Q_augmentationMap_proj {F : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : TowerAugmentation F)
    (n : ℕ) :
    DerivedCategory.Q.map a.augmentationMap ≫ DerivedCategory.Q.map (proj F n) =
      DerivedCategory.Q.map (a.app n) :=
  (DerivedCategory.Q.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Q.map (a.augmentationMap_proj n))

end Stacks.MilnorTower

end
