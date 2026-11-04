module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.FibrePullbackFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory

/-!
# The presheaf of fibre homology of a fibred category

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site `(D, O_D)`, as in
Stacks 08P8, and assume its fibres are small. For an abelian presheaf `F` on `C` and `n : ℕ` the
assignment

```
V ↦ H_n(C_V, F|_{C_V})
```

is a presheaf on `D`: the restriction map along `h : V' ⟶ V` is the map of Stacks 08PH attached to
the pullback functor `h^* : C_V ⥤ C_{V'}` of the chosen pullbacks of `p` and to restriction of `F`
along the chosen cartesian lifts, and those maps obey the identity and composition laws by
`Stacks.CategoryHomology.categoryHomologyMap_pullbackFunctor_id` and
`Stacks.CategoryHomology.categoryHomologyMap_pullbackFunctor_comp`. The assignment is moreover
functorial in `F`, the map induced by `α : F ⟶ G` being the one attached to the identity functor of
each fibre and to `α` restricted to it.

This is the presheaf `L_{n,p}(F)` of Stacks 08PI, whose associated sheaf is the sheaf `L_n(F)` of
that lemma.

## Main definitions

* `Stacks.Sites.FibredCategory.fiberCartesianRestriction`: restriction of `F` along the chosen
  cartesian lifts of a morphism of the base.
* `Stacks.Sites.FibredCategory.fiberHomologyPresheafFunctor`: the presheaf `L_{n,p}(F)` of fibre
  homology, as a functor of `F`.
* `Stacks.Sites.FibredCategory.fiberHomologySheaf`: the associated sheaf `L_n(F)`.

## Main results

* `Stacks.Sites.FibredCategory.fiberHomologyPresheaf_map`: the restriction maps of `L_{n,p}(F)` are
  the maps of Stacks 08PH attached to the chosen pullbacks.
* `Stacks.Sites.FibredCategory.fiberHomologyPresheafFunctor_map_app`: the map induced by a morphism
  of coefficients is the map of Stacks 08PH attached to the identity functor of the fibre.

## Implementation notes

The value of the presheaf at `V` is by definition `Stacks.CategoryHomology.categoryHomology` of
the restriction of `F` to the fibre at `V`, so the two results above hold by `rfl`.

The fibres have to be small for `Stacks.CategoryHomology.categoryHomology` to apply, so the
morphisms of `C` are taken in the same universe as its objects.

`CategoryTheory.Functor.Fiber` and `CategoryTheory.Functor.Fiber.fiberInclusion` are plain `def`s,
so goals about the structure arrow of an object of a fibre are not type-correct at `implicit`
transparency; they are therefore made locally `implicit_reducible`.

## References

* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks

universe uD vD uC v w

namespace CategoryHomology

/-- **The map of Stacks 08PH over the identity functor is compatible with composition of
coefficient morphisms**: composing coefficient morphisms composes the induced maps on category
homology. -/
lemma categoryHomologyMap_id_comp {C : Type uC} [SmallCategory C]
    {F G H : Cᵒᵖ ⥤ AddCommGrpCat.{max uC v}} (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    categoryHomologyMap.{uC, uC, max uC v} (𝟭 C) (α ≫ β) n =
      categoryHomologyMap.{uC, uC, max uC v} (𝟭 C) α n ≫
        categoryHomologyMap.{uC, uC, max uC v} (𝟭 C) β n :=
  categoryHomologyMap_comp.{uC, uC, uC, max uC v} (𝟭 C) (𝟭 C)
    (F := H) (F' := G) (F'' := F) β α n

end CategoryHomology

namespace Sites.FibredCategory

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

/-- Restriction of an abelian presheaf on the total category along the chosen cartesian lifts of
`h : V' ⟶ V`: a morphism from the restriction of `F` to the fibre at `V` to the restriction of `F`
to the fibre at `V'`, reindexed along the chosen pullback functor `h^*`. -/
def fiberCartesianRestriction (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
    {V V' : s.base.C} (h : V' ⟶ V) :
    ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) ⟶
      ((Functor.chosenPullbacks s.p).pullbackFunctor h).op ⋙
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V')).op ⋙ F) where
  app x := F.map (.op ((Functor.chosenPullbacks s.p).map h x.unop))
  naturality := by
    intro X Y f
    change F.map ((Functor.Fiber.fiberInclusion.map f.unop).op) ≫
        F.map (.op ((Functor.chosenPullbacks s.p).map h Y.unop)) =
      F.map (.op ((Functor.chosenPullbacks s.p).map h X.unop)) ≫
        F.map ((Functor.Fiber.fiberInclusion.map
          ((Functor.chosenPullbacks s.p).homMap h f.unop)).op)
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map
      (congrArg (fun k => k.op) ((Functor.chosenPullbacks s.p).homMap_fac h f.unop).symm)

/-- On an object of the fibre, `fiberCartesianRestriction` is restriction of `F` along the chosen
cartesian lift. -/
@[simp]
lemma fiberCartesianRestriction_app (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
    {V V' : s.base.C} (h : V' ⟶ V) (x : s.p.Fiber V) :
    (fiberCartesianRestriction s F h).app (.op x) =
      F.map (.op ((Functor.chosenPullbacks s.p).map h x)) :=
  rfl

/-- **The presheaf of fibre homology.** The presheaf `L_{n,p}(F)` on the base whose value at `V` is
the homology `H_n(C_V, F|_{C_V})` of the fibre at `V`, with restriction maps given by the chosen
pullback functors and restriction of `F` along the chosen cartesian lifts, and regarded as a
functor of the coefficient presheaf `F`. -/
@[stacks 08PI "the presheaf of fibre homology"]
def fiberHomologyPresheafFunctor (n : ℕ) :
    (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) ⥤
      (s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) where
  obj F :=
    { obj := fun V => CategoryHomology.categoryHomology.{uC, max w uD vD uC}
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op ⋙ F) n
      map := fun {_ _} h => CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC}
        ((Functor.chosenPullbacks s.p).pullbackFunctor h.unop)
        (fiberCartesianRestriction s F h.unop) n
      map_id := fun V =>
        CategoryHomology.categoryHomologyMap_pullbackFunctor_id.{uD, vD, uC, w}
          s.p F (fun {_ _} h => fiberCartesianRestriction s F h)
          (fun {_ _} _ _ => rfl) n V.unop
      map_comp := fun {_ _ _} f g =>
        CategoryHomology.categoryHomologyMap_pullbackFunctor_comp.{uD, vD, uC, w}
          s.p F (fun {_ _} h => fiberCartesianRestriction s F h)
          (fun {_ _} _ _ => rfl) n g.unop f.unop }
  map {F G} α :=
    { app := fun V => CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC}
        (𝟭 (s.p.Fiber V.unop))
        (Functor.whiskerLeft (Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op α) n
      naturality := by
        intro V V' f
        set h := f.unop
        set τF := fiberCartesianRestriction s F h
        set τG := fiberCartesianRestriction s G h
        set αV := Functor.whiskerLeft
          (Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op α
        set αV' := Functor.whiskerLeft
          (Functor.Fiber.fiberInclusion (p := s.p) (S := V'.unop)).op α
        have hτ : αV ≫ τG = τF ≫
            Functor.whiskerLeft ((Functor.chosenPullbacks s.p).pullbackFunctor h).op αV' := by
          refine NatTrans.ext (funext fun x => ?_)
          change α.app (.op (Functor.Fiber.fiberInclusion.obj x.unop)) ≫
              G.map (.op ((Functor.chosenPullbacks s.p).map h x.unop)) =
            F.map (.op ((Functor.chosenPullbacks s.p).map h x.unop)) ≫
              α.app (.op (Functor.Fiber.fiberInclusion.obj
                ((Functor.chosenPullbacks s.p).obj h x.unop)))
          exact (α.naturality ((Functor.chosenPullbacks s.p).map h x.unop).op).symm
        have hid : (𝟭 (s.p.Fiber V.unop)).op.whiskerLeft τG = τG :=
          NatTrans.ext (funext fun _ => rfl)
        change CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC}
              ((Functor.chosenPullbacks s.p).pullbackFunctor h) τF n ≫
            CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC}
              (𝟭 (s.p.Fiber V'.unop)) αV' n =
          CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC}
              (𝟭 (s.p.Fiber V.unop)) αV n ≫
            CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC}
              ((Functor.chosenPullbacks s.p).pullbackFunctor h) τG n
        rw [← CategoryHomology.categoryHomologyMap_comp.{uC, uC, uC, max w uD vD uC},
          ← CategoryHomology.categoryHomologyMap_comp.{uC, uC, uC, max w uD vD uC}, hid]
        simpa [Functor.comp_id, Functor.id_comp] using
          congrArg (fun θ => CategoryHomology.categoryHomologyMap
            ((Functor.chosenPullbacks s.p).pullbackFunctor h) θ n) hτ.symm }
  map_id F :=
    NatTrans.ext (funext fun V =>
      CategoryHomology.categoryHomologyMap_id.{uC, max w uD vD uC}
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op ⋙ F) n)
  map_comp {F G H} α β :=
    NatTrans.ext (funext fun V =>
      CategoryHomology.categoryHomologyMap_id_comp.{uC, max w uD vD uC}
        (Functor.whiskerLeft (Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op α)
        (Functor.whiskerLeft (Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op β) n)

/-- The presheaf `L_{n,p}(F)` of fibre homology of a fixed coefficient presheaf. -/
abbrev fiberHomologyPresheaf (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ) :
    s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC} :=
  (fiberHomologyPresheafFunctor s n).obj F

/-- **The values of the presheaf of fibre homology.** Its value at `V` is the homology
`H_n(C_V, F|_{C_V})` of the fibre at `V`. -/
@[stacks 08PI "the values of the presheaf of fibre homology"]
lemma fiberHomologyPresheaf_obj (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ)
    (V : s.base.Cᵒᵖ) :
    (fiberHomologyPresheaf s F n).obj V =
      CategoryHomology.categoryHomology.{uC, max w uD vD uC}
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op ⋙ F) n :=
  rfl

/-- **The restriction maps of the presheaf of fibre homology.** The restriction map along
`h : V' ⟶ V` is the map on homology of Stacks 08PH attached to the chosen pullback functor `h^*`
and to restriction of `F` along the chosen cartesian lifts of `h`. -/
@[stacks 08PI "the restriction maps of the presheaf of fibre homology"]
lemma fiberHomologyPresheaf_map (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ)
    {V V' : s.base.C} (h : V' ⟶ V) :
    (fiberHomologyPresheaf s F n).map h.op =
      CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC}
        ((Functor.chosenPullbacks s.p).pullbackFunctor h) (fiberCartesianRestriction s F h) n :=
  rfl

/-- **Functoriality of the presheaf of fibre homology in the coefficients.** The map induced by
`α : F ⟶ G` is the map on homology of Stacks 08PH attached to the identity functor of the fibre and
to `α` restricted to it. -/
@[stacks 08PI "functoriality of the presheaf of fibre homology in the coefficients"]
lemma fiberHomologyPresheafFunctor_map_app {F G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}}
    (α : F ⟶ G) (n : ℕ) (V : s.base.Cᵒᵖ) :
    ((fiberHomologyPresheafFunctor s n).map α).app V =
      CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC} (𝟭 (s.p.Fiber V.unop))
        (Functor.whiskerLeft (Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op α) n :=
  rfl

/-- **The sheaf `L_n(F)` of fibre homology.** The abelian sheaf on the base associated to the
presheaf of fibre homology. -/
@[stacks 08PI "the sheaf of fibre homology"]
abbrev fiberHomologySheaf [HasWeakSheafify s.base.J AddCommGrpCat.{max w uD vD uC}]
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ) :
    Sheaf s.base.J AddCommGrpCat.{max w uD vD uC} :=
  (presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC}).obj (fiberHomologyPresheaf s F n)

end Sites.FibredCategory

end Stacks

end
