module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceFreeAbelianLowerShriekNaturality

/-!
# `L ↦ j_{L!} j_L^{-1} ℤ_V^♯` is a functor on semi-representable objects

Let `(C, J)` be a small site and `V` an object of `C`. For a semi-representable object `L` of `C`,
Stacks 0D87 part (2) on free abelian sheaves identifies `j_{L!} j_L^{-1} ℤ_V^♯` with the free
abelian sheaf `ℤ_{h_V × F(L)}^♯`
(`CategoryTheory.SemiRepresentable.freeYonedaSheafPushforwardPullbackIso`), and that
identification is natural in `L` for the shriek restriction transition
`CategoryTheory.SemiRepresentable.shriekRestrictionTransition`
(`CategoryTheory.SemiRepresentable`
`.shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIso`).

The right-hand side is manifestly functorial in `L`. This module uses that naturality to transfer
the functoriality to the left-hand side: the shriek restriction transitions at the coefficient
sheaf `ℤ_V^♯` take identities to identities and compose, so `L ↦ j_{L!} j_L^{-1} ℤ_V^♯` is a
functor on semi-representable objects and the identification is an isomorphism of functors.

The functoriality is worth isolating. `shriekRestrictionTransition` is built from the comparison
of the left adjoints of the relocalization triangle, and this library proves no cocycle law for
those comparisons: nothing here says that the comparison attached to `f ≫ g` is the one of `f`
followed by the one of `g`. So the transitions are *not* known to compose in general. At the
coefficient sheaf `ℤ_V^♯` they do, and the only reason is that the other side of Stacks 0D87
part (2) is a functor.

## Main definitions

* `CategoryTheory.SemiRepresentable.freeYonedaProd`: the functor `L ↦ ℤ_{h_V × F(L)}^♯`.
* `CategoryTheory.SemiRepresentable.shriekRestrictionFreeYoneda`: the functor
  `L ↦ j_{L!} j_L^{-1} ℤ_V^♯`, whose action on morphisms is the shriek restriction transition.
* `CategoryTheory.SemiRepresentable.shriekRestrictionFreeYonedaIso`: **Stacks 0D87 part (2) at
  `ℤ_V^♯` as an isomorphism of functors on semi-representable objects.**

## Main results

* `CategoryTheory.SemiRepresentable.shriekRestrictionTransition_freeYonedaSheaf_id` and
  `.shriekRestrictionTransition_freeYonedaSheaf_comp`: **the shriek restriction transitions at
  `ℤ_V^♯` take identities to identities and compose.** These are what make
  `shriekRestrictionFreeYoneda` a functor.

## Implementation notes

Both facts are proved by cancelling the identification, which is an isomorphism: Stacks 0D87
part (2) carries `τ_{f ≫ g}` and `τ_f ≫ τ_g` to the same morphism `ℤ_{h_V × F(f ≫ g)}^♯`, and
`CategoryTheory.Iso.cancel_iso_hom_right` turns that into the equality of the two transitions.
The reassociations are in term mode: `rw [CategoryTheory.Category.assoc]` does not fire in these
sheaf categories, the outer and inner `≫` carrying different spellings of the category instance.

The morphisms of `freeYonedaProd` are written out rather than obtained as a composite of named
functors, so that they are *syntactically* the right-hand side of that square, which is stated
with `CategoryTheory.Limits.prod.map (𝟙 h_V)` of the image of the morphism under
`CategoryTheory.FormalCoproduct.yoneda`.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective (Type u)] (V : C)

/-! ### The functor `L ↦ ℤ_{h_V × F(L)}^♯` -/

/-- **The functor `L ↦ ℤ_{h_V × F(L)}^♯`** on semi-representable objects of `C`: the free abelian
sheaf on the product of the presheaf represented by `V` with the presheaf represented by `L`.

This is the right-hand side of Stacks 0D87 part (2) at the free abelian sheaf on a representable,
and it is a functor for a trivial reason: `F` is a functor, the product with `h_V` is a functor,
and so is the free abelian sheaf. -/
def freeYonedaProd : FormalCoproduct.{u} C ⥤ Sheaf J AddCommGrpCat.{u} where
  obj L := (presheafToSheaf J AddCommGrpCat.{u}).obj
    ((yoneda.obj V ⨯ (FormalCoproduct.yoneda (C := C)).obj L) ⋙ AddCommGrpCat.free)
  map f := (presheafToSheaf J AddCommGrpCat.{u}).map
    (Functor.whiskerRight (Limits.prod.map (𝟙 (yoneda.obj V))
      ((FormalCoproduct.yoneda (C := C)).map f)) AddCommGrpCat.free)
  map_id L := by
    rw [(FormalCoproduct.yoneda (C := C)).map_id, Limits.prod.map_id_id,
      Functor.whiskerRight_id', CategoryTheory.Functor.map_id]
  map_comp {L M N} f g := by
    have h : Limits.prod.map (𝟙 (yoneda.obj V)) ((FormalCoproduct.yoneda (C := C)).map (f ≫ g)) =
        Limits.prod.map (𝟙 (yoneda.obj V)) ((FormalCoproduct.yoneda (C := C)).map f) ≫
          Limits.prod.map (𝟙 (yoneda.obj V)) ((FormalCoproduct.yoneda (C := C)).map g) := by
      rw [Limits.prod.map_map, Category.comp_id, (FormalCoproduct.yoneda (C := C)).map_comp]
    rw [h, Functor.whiskerRight_comp, Functor.map_comp]

omit [J.WEqualsLocallyBijective (Type u)] in
/-- The value of `L ↦ ℤ_{h_V × F(L)}^♯`. -/
theorem freeYonedaProd_obj (L : FormalCoproduct.{u} C) :
    (freeYonedaProd J V).obj L =
      (presheafToSheaf J AddCommGrpCat.{u}).obj
        ((yoneda.obj V ⨯ (FormalCoproduct.yoneda (C := C)).obj L) ⋙ AddCommGrpCat.free) :=
  rfl

omit [J.WEqualsLocallyBijective (Type u)] in
/-- The action of `L ↦ ℤ_{h_V × F(L)}^♯` on a morphism: the free abelian sheaf of the product of
the identity of `h_V` with the image of the morphism under `F`. -/
theorem freeYonedaProd_map {L M : FormalCoproduct.{u} C} (f : L ⟶ M) :
    (freeYonedaProd J V).map f =
      (presheafToSheaf J AddCommGrpCat.{u}).map
        (Functor.whiskerRight (Limits.prod.map (𝟙 (yoneda.obj V))
          ((FormalCoproduct.yoneda (C := C)).map f)) AddCommGrpCat.free) :=
  rfl

/-! ### The shriek restriction transitions at `ℤ_V^♯` are functorial -/

/-- **Stacks 0D87 part (2) at `ℤ_V^♯`, with the right-hand side read as `freeYonedaProd`.** -/
theorem shriekRestrictionTransition_comp_freeYonedaProd {L M : FormalCoproduct.{u} C}
    (f : L ⟶ M) :
    (shriekRestrictionTransition J f (componentwiseTopology J L) (componentwiseTopology J M)
            AddCommGrpCat.{u}).app
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ≫
        (freeYonedaSheafPushforwardPullbackIso J M V).hom =
      (freeYonedaSheafPushforwardPullbackIso J L V).hom ≫ (freeYonedaProd J V).map f :=
  shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIso J f V

/-- **The shriek restriction transition of an identity is the identity, at the coefficient sheaf
`ℤ_V^♯`**: the transition is not degenerate.

Stacks 0D87 part (2) carries it to `ℤ_{h_V × F(𝟙_L)}^♯`, which is the identity because
`ℤ_{h_V × F(-)}^♯` is a functor, and the identification may be cancelled because it is an
isomorphism. -/
theorem shriekRestrictionTransition_freeYonedaSheaf_id (L : FormalCoproduct.{u} C) :
    (shriekRestrictionTransition J (𝟙 L) (componentwiseTopology J L) (componentwiseTopology J L)
          AddCommGrpCat.{u}).app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) =
      𝟙 ((Functor.sheafPullbackConstruction.sheafPullback (componentOverForget L)
            AddCommGrpCat.{u} (componentwiseTopology J L) J).obj
          (((componentOverForget L).sheafPushforwardContinuous AddCommGrpCat.{u}
            (componentwiseTopology J L) J).obj
            (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) := by
  refine (Iso.cancel_iso_hom_right _ _ (freeYonedaSheafPushforwardPullbackIso J L V)).mp ?_
  refine Eq.trans (shriekRestrictionTransition_comp_freeYonedaProd J V (𝟙 L)) ?_
  refine Eq.trans (whisker_eq _ ((freeYonedaProd J V).map_id L)) ?_
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The shriek restriction transitions compose, at the coefficient sheaf `ℤ_V^♯`.** For
`f : L ⟶ M` and `g : M ⟶ N` the transition of `f ≫ g` is the transition of `f` followed by the
transition of `g`.

Functoriality of `CategoryTheory.SemiRepresentable.shriekRestrictionTransition` in the
semi-representable object is not available in this library in general: the comparison of left
adjoints it is built from carries no cocycle law here. At the coefficient sheaf `ℤ_V^♯` it is a
consequence of Stacks 0D87 part (2), which carries both sides to `ℤ_{h_V × F(f ≫ g)}^♯`. -/
theorem shriekRestrictionTransition_freeYonedaSheaf_comp {L M N : FormalCoproduct.{u} C}
    (f : L ⟶ M) (g : M ⟶ N) :
    (shriekRestrictionTransition J (f ≫ g) (componentwiseTopology J L)
            (componentwiseTopology J N) AddCommGrpCat.{u}).app
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) =
        (shriekRestrictionTransition J f (componentwiseTopology J L) (componentwiseTopology J M)
              AddCommGrpCat.{u}).app
            (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ≫
          (shriekRestrictionTransition J g (componentwiseTopology J M)
                (componentwiseTopology J N) AddCommGrpCat.{u}).app
            (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) := by
  have h1 :
      (shriekRestrictionTransition J (f ≫ g) (componentwiseTopology J L)
              (componentwiseTopology J N) AddCommGrpCat.{u}).app
            (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ≫
          (freeYonedaSheafPushforwardPullbackIso J N V).hom =
        (freeYonedaSheafPushforwardPullbackIso J L V).hom ≫
          ((freeYonedaProd J V).map f ≫ (freeYonedaProd J V).map g) :=
    (shriekRestrictionTransition_comp_freeYonedaProd J V (f ≫ g)).trans
      (whisker_eq _ ((freeYonedaProd J V).map_comp f g))
  have h2 :
      ((shriekRestrictionTransition J f (componentwiseTopology J L) (componentwiseTopology J M)
                AddCommGrpCat.{u}).app
              (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ≫
            (shriekRestrictionTransition J g (componentwiseTopology J M)
                  (componentwiseTopology J N) AddCommGrpCat.{u}).app
              (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
          (freeYonedaSheafPushforwardPullbackIso J N V).hom =
        (freeYonedaSheafPushforwardPullbackIso J L V).hom ≫
          ((freeYonedaProd J V).map f ≫ (freeYonedaProd J V).map g) :=
    (Category.assoc _ _ _).trans
      ((whisker_eq _ (shriekRestrictionTransition_comp_freeYonedaProd J V g)).trans
        ((Category.assoc _ _ _).symm.trans
          ((eq_whisker (shriekRestrictionTransition_comp_freeYonedaProd J V f) _).trans
            (Category.assoc _ _ _))))
  exact (Iso.cancel_iso_hom_right _ _ (freeYonedaSheafPushforwardPullbackIso J N V)).mp
    (h1.trans h2.symm)

/-! ### The functor `L ↦ j_{L!} j_L^{-1} ℤ_V^♯` -/

/-- **The functor `L ↦ j_{L!} j_L^{-1} ℤ_V^♯`** on semi-representable objects of `C`: the free
abelian sheaf on `V`, restricted to `C/L` and extended by zero again, with the shriek restriction
transition as its action on morphisms.

That this is a functor is Stacks 0D87 part (2):
`shriekRestrictionTransition_freeYonedaSheaf_id` and
`shriekRestrictionTransition_freeYonedaSheaf_comp`. -/
def shriekRestrictionFreeYoneda : FormalCoproduct.{u} C ⥤ Sheaf J AddCommGrpCat.{u} where
  obj L := (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget L)
      AddCommGrpCat.{u} (componentwiseTopology J L) J).obj
    (((componentOverForget L).sheafPushforwardContinuous AddCommGrpCat.{u}
      (componentwiseTopology J L) J).obj
      (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))
  map {L M} f := (shriekRestrictionTransition J f (componentwiseTopology J L)
      (componentwiseTopology J M) AddCommGrpCat.{u}).app
    (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
  map_id L := shriekRestrictionTransition_freeYonedaSheaf_id J V L
  map_comp f g := shriekRestrictionTransition_freeYonedaSheaf_comp J V f g

/-- The value of `L ↦ j_{L!} j_L^{-1} ℤ_V^♯`. -/
theorem shriekRestrictionFreeYoneda_obj (L : FormalCoproduct.{u} C) :
    (shriekRestrictionFreeYoneda J V).obj L =
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget L)
          AddCommGrpCat.{u} (componentwiseTopology J L) J).obj
        (((componentOverForget L).sheafPushforwardContinuous AddCommGrpCat.{u}
          (componentwiseTopology J L) J).obj
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) :=
  rfl

/-- The action of `L ↦ j_{L!} j_L^{-1} ℤ_V^♯` on a morphism is the shriek restriction
transition. -/
theorem shriekRestrictionFreeYoneda_map {L M : FormalCoproduct.{u} C} (f : L ⟶ M) :
    (shriekRestrictionFreeYoneda J V).map f =
      (shriekRestrictionTransition J f (componentwiseTopology J L) (componentwiseTopology J M)
            AddCommGrpCat.{u}).app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) :=
  rfl

/-- **Stacks 0D87 part (2) at `ℤ_V^♯`, as an isomorphism of functors on semi-representable
objects.** Its naturality is
`shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIso`. -/
def shriekRestrictionFreeYonedaIso : shriekRestrictionFreeYoneda J V ≅ freeYonedaProd J V :=
  NatIso.ofComponents (fun L => freeYonedaSheafPushforwardPullbackIso J L V)
    (fun {_ _} f => shriekRestrictionTransition_comp_freeYonedaProd J V f)

end CategoryTheory.SemiRepresentable

end
