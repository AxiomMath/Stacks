module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushPullUnit

/-!
# The unit of the graded push–pull adjunction preserves the unit

`Stacks.PushforwardGradedAlgebra.gradedUnit` is the canonical homomorphism of sheaves of graded
algebras `A ⟶ f_* f^* A`, the unit of
`Stacks.PushforwardGradedAlgebra.pullbackPushforwardGradedAlgebraAdjunction`. It is a
`SheafOfModules.GradedAlgebra.Hom`, which does not require preservation of the degree-zero unit.
We show that it nevertheless preserves the unit, so that it is a
`SheafOfModules.GradedAlgebra.UnitalHom`.

The unit law holds for the unit of any monoidal adjunction: it follows from the unit being a
monoidal natural transformation at the unit object,
`CategoryTheory.Adjunction.unit_app_unit_comp_map_η`.

## Main results

* `Stacks.MonoidalGraded.comp_unit_app_eq_mapOne_mapOne`: for a monoidal adjunction `L ⊣ G` and
  a unit `o : 𝟙_ ⟶ X`, the composite `o ≫ η_X` is the double transport
  `mapOne G (mapOne L o)`.
* `SheafOfModules.GradedAlgebra.transportAdjunction_unit_app_map_one`: the degree-zero component
  of the unit of the transported adjunction carries the global unit of `B` to the global unit of
  `G(L(B))`, over every object of the site.
* `SheafOfModules.GradedAlgebra.transportAdjunctionUnitUnitalHom`: the unit of the transported
  adjunction as a unital homomorphism of sheaves of graded algebras.
* `Stacks.PushforwardGradedAlgebra.gradedUnitUnitalHom`: `A ⟶ f_* f^* A` as a unital
  homomorphism, for a morphism of ringed spaces, with
  `Stacks.PushforwardGradedAlgebra.gradedUnitUnitalHom_toHom` identifying the underlying
  homomorphism with `Stacks.PushforwardGradedAlgebra.gradedUnit`.

## Implementation notes

The unit law is stated over each object of the site, the form of the `map_one` field of
`SheafOfModules.GradedAlgebra.UnitalHom`; it is equivalent to the single equation between global
sections by `SheafOfModules.GradedAlgebra.UnitalHom.map_one_iff`.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX) — functoriality of
  sheaves of graded algebras for a morphism of ringed topoi.
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW) — sheaves of graded
  algebras and their homomorphisms.
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096) — the adjunction between
  pullback and pushforward of sheaves of modules on ringed spaces.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace

universe v₁ v₂ u₁ u₂ u w

namespace Stacks.MonoidalGraded

/-! ### The unit of a monoidal adjunction on a unit morphism -/

section Unit

variable {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E]
  {E' : Type u₂} [Category.{v₂} E'] [MonoidalCategory E']
  {L : E' ⥤ E} {G : E ⥤ E'} (adj : L ⊣ G)
  [L.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- For a monoidal adjunction `L ⊣ G` and `o : 𝟙_ E' ⟶ X`, the composite `o ≫ η_X` equals
`mapOne G (mapOne L o)`. -/
theorem comp_unit_app_eq_mapOne_mapOne {X : E'} (o : 𝟙_ E' ⟶ X) :
    o ≫ adj.unit.app X = mapOne G (mapOne L o) := by
  refine (adj.unit_naturality o).symm.trans ?_
  rw [mapOne, mapOne, ← adj.unit_app_unit_comp_map_η, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Functor.Monoidal.η_ε_assoc]

end Unit

end Stacks.MonoidalGraded

namespace SheafOfModules.GradedAlgebra

/-! ### The unit of the transported adjunction is unital -/

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {L : SheafOfModules.{w} (toRingCat K Psharp) ⥤ SheafOfModules.{w} (toRingCat J Osharp)}
  {G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp)}
  (adj : L ⊣ G) [L.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hO hP

/-- The degree-zero component of the unit of the transported adjunction carries the global unit
of `B` to the global unit of `G(L(B))`, over every object of the site. -/
theorem transportAdjunction_unit_app_map_one (B : GradedAlgebra.{w, w} (toRingCat K Psharp))
    (U : Dᵒᵖ) :
    (((transportAdjunction adj hO hP).unit.app B).app 0).val.app U (B.one.eval U) =
      (transport G (transport L B hP hO) hO hP).one.eval U := by
  rw [transportAdjunction_unit_app_app adj hO hP B 0]
  let one : (𝟙_ (SheafOfModules.{w} (toRingCat K Psharp))).val.obj U :=
    (1 : (toRingCat K Psharp).obj.obj U)
  have h (B' : GradedAlgebra.{w, w} (toRingCat K Psharp)) :
      (oneHom B').val.app U one = B'.one.eval U :=
    (oneHom_val_app B' U 1).trans (one_smul _ _)
  have e : oneHom (transport G (transport L B hP hO) hO hP) =
      Stacks.MonoidalGraded.mapOne G (Stacks.MonoidalGraded.mapOne L (oneHom B)) :=
    (oneHom_transport G (transport L B hP hO) hO hP).trans
      (congrArg (Stacks.MonoidalGraded.mapOne G) (oneHom_transport L B hP hO))
  rw [← h B, ← h (transport G (transport L B hP hO) hO hP)]
  exact (SheafOfModules.hom_congr_app_apply
    (Stacks.MonoidalGraded.comp_unit_app_eq_mapOne_mapOne adj (oneHom B)) U one).trans
    (SheafOfModules.hom_congr_app_apply e.symm U one)

/-- The unit of the transported adjunction at `B`, as a unital homomorphism of sheaves of graded
algebras `B ⟶ G(L(B))`. -/
noncomputable def transportAdjunctionUnitUnitalHom
    (B : GradedAlgebra.{w, w} (toRingCat K Psharp)) :
    UnitalHom B (transport G (transport L B hP hO) hO hP) where
  app n := ((transportAdjunction adj hO hP).unit.app B).app n
  map_mul := ((transportAdjunction adj hO hP).unit.app B).map_mul
  map_one := transportAdjunction_unit_app_map_one adj hO hP B

/-- The degree-`n` component of `transportAdjunctionUnitUnitalHom` is the degree-`n` component of
the unit of the transported adjunction. -/
@[simp]
theorem transportAdjunctionUnitUnitalHom_app (B : GradedAlgebra.{w, w} (toRingCat K Psharp))
    (n : ℤ) :
    (transportAdjunctionUnitUnitalHom adj hO hP B).app n =
      ((transportAdjunction adj hO hP).unit.app B).app n :=
  rfl

/-- The homomorphism underlying `transportAdjunctionUnitUnitalHom` is the unit of the
transported adjunction. -/
theorem transportAdjunctionUnitUnitalHom_toHom
    (B : GradedAlgebra.{w, w} (toRingCat K Psharp)) :
    (transportAdjunctionUnitUnitalHom adj hO hP B).toHom =
      (transportAdjunction adj hO hP).unit.app B :=
  rfl

end Adjunction

end SheafOfModules.GradedAlgebra

namespace Stacks.PushforwardGradedAlgebra

/-! ### `A ⟶ f_* f^* A` as a unital homomorphism -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal pushforwardFunctorLaxMonoidal

/-- The canonical homomorphism of sheaves of graded algebras `A ⟶ f_* f^* A`, as a
`SheafOfModules.GradedAlgebra.UnitalHom`. -/
noncomputable def gradedUnitUnitalHom
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)) :
    SheafOfModules.GradedAlgebra.UnitalHom A
      ((SheafOfModules.GradedAlgebra.transportFunctor (pushforwardFunctor f)
          (structureSheafRing X).property (structureSheafRing Y).property).obj
        ((SheafOfModules.GradedAlgebra.transportFunctor (pullbackFunctor f)
          (structureSheafRing Y).property (structureSheafRing X).property).obj A)) :=
  SheafOfModules.GradedAlgebra.transportAdjunctionUnitUnitalHom (pullbackAdjunction f)
    (structureSheafRing X).property (structureSheafRing Y).property A

/-- The degree-`n` component of `gradedUnitUnitalHom f A` is that of `gradedUnit f A`. -/
@[simp]
theorem gradedUnitUnitalHom_app
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)) (n : ℤ) :
    (gradedUnitUnitalHom f A).app n = (gradedUnit f A).app n :=
  rfl

/-- The homomorphism underlying `gradedUnitUnitalHom f A` is `gradedUnit f A`. -/
theorem gradedUnitUnitalHom_toHom
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)) :
    (gradedUnitUnitalHom f A).toHom = gradedUnit f A :=
  rfl

end Stacks.PushforwardGradedAlgebra

end
