module

public import StacksFrontier.CategoryTheory.Sites.Continuous.PushforwardSheafificationComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceLowerShriekFreeAbelian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceLowerShriekRestrictionNaturality

/-!
# Stacks 0D87 part (2) on free abelian sheaves is natural in the semi-representable object

Let `(C, J)` be a small site.
`StacksFrontier/CategoryTheory/Sites/Simplicial/SliceLowerShriekFreeAbelian.lean` carries Stacks
0D87 part (2) across the free abelian sheaf functor, culminating in
`CategoryTheory.SemiRepresentable.freeYonedaSheafPushforwardPullbackIso`,
`j_{L!} j_L^{-1} ℤ_V^♯ ≅ ℤ_{h_V × F(L)}^♯`. None of the four isomorphisms in that chain had a
naturality statement in the semi-representable object `L`. This module supplies them, taking as
input the set-level naturality square of
`SemiRepresentable.shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso`.

## Main results

* `CategoryTheory.SemiRepresentable.sheafificationProdIso_hom_comp_map_fst` and
  `.sheafificationProdIso_hom_comp_map_snd`: the two projections of the comparison of the product
  of two sheafifications with the sheafification of the product.
* `CategoryTheory.SemiRepresentable.sheafificationProdIso_naturality`: that comparison is natural
  in the second presheaf.
* `CategoryTheory.SemiRepresentable.freeAbelianSheafTensorIso_naturality`: **the free abelian
  sheaf on a product of sheafifications is natural in the second presheaf.** This is the third of
  the three ingredients, and the only one that does not mention the semi-representable object: in
  the chain it is read at the morphism `F(f) : F(M) ⟶ F(N)` of presheaves.
* `CategoryTheory.SemiRepresentable.relocalizationForgetPushforwardIso'_hom_app_hom`: the
  underlying presheaf morphism of the relocalization comparison, the
  natural-transformation-level companion of
  `CategoryTheory.SemiRepresentable.relocalizationForgetPushforwardIso'_hom_app_hom_app`.
* `SemiRepresentable.composeAndSheafify_map_relocalizationForgetPushforwardIso'_comp`:
  the free abelian sheaf functor applied to the relocalization comparison inverts the reindexing
  factor of the composition hexagon.
* `CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_naturality`: **restriction along `j`
  commutes with the free abelian sheaf functor, naturally in the semi-representable object.**
  This is the first of the three ingredients.

## What this file does not contain

The naturality in `L` of `CategoryTheory.SemiRepresentable.freeSheafPullbackIso` is not here: it
is `CategoryTheory.Functor.freeLowerShriekIso_comp`, in
`StacksFrontier/CategoryTheory/Sites/Continuous/FreeAbelianLowerShriekComp.lean`, whose comparison is
a `CategoryTheory.Adjunction.leftAdjointUniq` and so needs the hexagon of
`CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker` rather than the one used here. The
naturality in `L` of `CategoryTheory.SemiRepresentable.freeYonedaSheafPushforwardPullbackIso`
itself is not here either: it is `CategoryTheory.SemiRepresentable`
`.shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIso`, in
`StacksFrontier/CategoryTheory/Sites/Simplicial/SliceFreeAbelianLowerShriekNaturality.lean`, which
is the three ingredients assembled with that hexagon, with the counit square for `r_f`, and with
the set-level square of component 1. Nor is the compatibility of
`componentLowerShriekCompAugmentationAbelianIso` with the transition, which is
`CategoryTheory.SimplicialSemiRepresentable`
`.componentLowerShriekCompAugmentationAbelianIso_transition`.

What remains unproved anywhere in the tree, of the statements the `hacyclic` hypotheses of
Stacks 0D8G, 0D8H and 0D8I need, is the naturality in the **simplex map** of
`CategoryTheory.SimplicialSemiRepresentable.augmentationComponentFreeYonedaIso`. Two things stand
between it and the naturality in `L` that is proved: there is no bridge identifying
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso` with
`CategoryTheory.SemiRepresentable.shriekRestrictionTransition` or with
`CategoryTheory.Functor.lowerShriekComp`, and the tree holds no simplicial object whose degree-`p`
value is `a_! g_{p!}` of anything, so there is nothing yet for the degreewise isomorphism to be
natural *as*.

## Implementation notes

`sheafificationProdIso` is a composite of two limit comparisons, so its two projections are read
off by `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp` at the two objects of
`CategoryTheory.Limits.WalkingPair` together with
`CategoryTheory.Limits.PreservesLimitPair.iso_inv_fst` and `.iso_inv_snd`; the naturality is then
the joint monomorphy of the two, by `CategoryTheory.Limits.prod.hom_ext` after cancelling
`CategoryTheory.Limits.PreservesLimitPair.iso`. The naturality of `freeAbelianSheafTensorIso`
adds nothing beyond that and the naturality of
`CategoryTheory.presheafToSheafCompComposeAndSheafifyIso`, which is a natural isomorphism.

The naturality of `freeSheafPushforwardIso` is stated on the *inverses* of the three
commutations. That is the direction in which it is literally the composition hexagon
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility_comp'`: inverting all
four isomorphisms of a commuting square gives the other form, but carrying out that inversion
inside Lean runs into the two-spellings obstruction below, whereas the `inv` form is two
rewrites.

Two frictions, both the one the module docstring of
`StacksFrontier/CategoryTheory/Sites/Simplicial/SliceLowerShriekRestrictionNaturality.lean`
records: `rw` is unusable wherever one object has two spellings. Here the spellings are
`(r_f ⋙ j_N).op ⋙ X ⋙ ℤ` against `r_f.op ⋙ (j_N.op ⋙ X ⋙ ℤ)` and
`Sheaf.composeAndSheafify` against its expansion; `CategoryTheory.Category.assoc` itself fails on
the first, and `composeAndSheafify_map_relocalizationForgetPushforwardIso'_comp` cannot be applied
by `rw` on the second. Both are applied as terms, under
`CategoryTheory.eq_whisker` and `CategoryTheory.whisker_eq`.

A `simp` set that unfolds `CategoryTheory.eqToIso` loses the `Iso.hom_inv_id_app` cancellation and
leaves an `eqToHom` that then has to be collapsed object by object. The cancellation inside
`composeAndSheafify_map_relocalizationForgetPushforwardIso'_comp` is therefore done by a closed
`simp only` set that does *not* mention `eqToIso`, and no destructuring of the component index is
needed.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Opposite

universe t u

namespace CategoryTheory.SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
-- Mathlib's instance that a left adjoint preserves sheafification, tried first: at its default
-- priority the search for `J.PreservesSheafification AddCommGrpCat.free` runs out of budget.
attribute [local instance high] Sheaf.instPreservesSheafificationOfIsLeftAdjoint

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective (Type u)]

/-! ### The product of two sheafifications -/

omit [J.WEqualsLocallyBijective (Type u)] in
/-- The first projection of `sheafificationProdIso` is the first projection of the monoidal
product. -/
theorem sheafificationProdIso_hom_comp_map_fst (P Q : Cᵒᵖ ⥤ Type u) :
    (sheafificationProdIso J P Q).hom ≫ (presheafToSheaf J (Type u)).map Limits.prod.fst =
      fst ((presheafToSheaf J (Type u)).obj P) ((presheafToSheaf J (Type u)).obj Q) := by
  simp [sheafificationProdIso]

omit [J.WEqualsLocallyBijective (Type u)] in
/-- The second projection of `sheafificationProdIso` is the second projection of the monoidal
product. -/
theorem sheafificationProdIso_hom_comp_map_snd (P Q : Cᵒᵖ ⥤ Type u) :
    (sheafificationProdIso J P Q).hom ≫ (presheafToSheaf J (Type u)).map Limits.prod.snd =
      snd ((presheafToSheaf J (Type u)).obj P) ((presheafToSheaf J (Type u)).obj Q) := by
  simp [sheafificationProdIso]

omit [J.WEqualsLocallyBijective (Type u)] in
/-- **`sheafificationProdIso` is natural in the second presheaf.** -/
theorem sheafificationProdIso_naturality (P Q Q' : Cᵒᵖ ⥤ Type u) (q : Q ⟶ Q') :
    ((presheafToSheaf J (Type u)).obj P ◁ (presheafToSheaf J (Type u)).map q) ≫
        (sheafificationProdIso J P Q').hom =
      (sheafificationProdIso J P Q).hom ≫
        (presheafToSheaf J (Type u)).map (Limits.prod.map (𝟙 P) q) := by
  rw [← cancel_mono (PreservesLimitPair.iso (presheafToSheaf J (Type u)) P Q').hom]
  refine Limits.prod.hom_ext ?_ ?_
  · simp only [Category.assoc, PreservesLimitPair.iso_hom, Limits.prodComparison_fst]
    rw [sheafificationProdIso_hom_comp_map_fst, ← Functor.map_comp, Limits.prod.map_fst,
      Category.comp_id, sheafificationProdIso_hom_comp_map_fst]
    exact whiskerLeft_fst _ _
  · simp only [Category.assoc, PreservesLimitPair.iso_hom, Limits.prodComparison_snd]
    rw [sheafificationProdIso_hom_comp_map_snd, ← Functor.map_comp, Limits.prod.map_snd,
      Functor.map_comp, ← Category.assoc, sheafificationProdIso_hom_comp_map_snd]
    exact whiskerLeft_snd _ _

omit [J.WEqualsLocallyBijective (Type u)] in
/-- **`freeAbelianSheafTensorIso` is natural in the second presheaf.** -/
theorem freeAbelianSheafTensorIso_naturality (P Q Q' : Cᵒᵖ ⥤ Type u) (q : Q ⟶ Q') :
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).map
        ((presheafToSheaf J (Type u)).obj P ◁ (presheafToSheaf J (Type u)).map q) ≫
      (freeAbelianSheafTensorIso J P Q').hom =
    (freeAbelianSheafTensorIso J P Q).hom ≫
      (presheafToSheaf J AddCommGrpCat.{u}).map
        (Functor.whiskerRight (Limits.prod.map (𝟙 P) q) AddCommGrpCat.free) := by
  dsimp only [freeAbelianSheafTensorIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, sheafificationProdIso_naturality,
    Functor.map_comp, Category.assoc]
  exact congrArg (fun m => (Sheaf.composeAndSheafify J AddCommGrpCat.free).map
      (sheafificationProdIso J P Q).hom ≫ m)
    ((presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free).hom.naturality
      (Limits.prod.map (𝟙 P) q))

/-! ### Restriction along `j` and the free abelian sheaf, naturally in `L` -/

section

variable {M N : FormalCoproduct.{u} C} (f : M ⟶ N)

omit [J.WEqualsLocallyBijective (Type u)] in
/-- The underlying presheaf morphism of the relocalization comparison is the reindexing of the
presheaf along the equality `r_f ⋙ j_N = j_M` of site functors. -/
theorem relocalizationForgetPushforwardIso'_hom_app_hom (A : Type t) [Category.{u} A]
    (Z : Sheaf J A) :
    ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
          (componentwiseTopology J N) A).hom.app Z).hom =
      Functor.whiskerRight
        (NatTrans.op (eqToIso (componentOverMap_comp_componentOverForget f)).inv) Z.obj := by
  let : (componentOverMap f ⋙ componentOverForget N).IsContinuous
      (componentwiseTopology J M) J :=
    Functor.isContinuous_comp (componentOverMap f) (componentOverForget N)
      (componentwiseTopology J M) (componentwiseTopology J N) J
  exact (Category.id_comp (((Functor.sheafPushforwardContinuousNatTrans
      (eqToIso (componentOverMap_comp_componentOverForget f)).inv A
      (componentwiseTopology J M) J).app Z).hom)).trans
    (Functor.sheafPushforwardContinuousNatTrans_app_hom
      (eqToIso (componentOverMap_comp_componentOverForget f)).inv A
      (componentwiseTopology J M) J Z)

omit [J.WEqualsLocallyBijective (Type u)] in
/-- `freeSheafPushforwardIso` is, at a sheaf, the inverse of the pushforward-sheafification
comparison at the presheaf `X ⋙ ℤ`. -/
theorem freeSheafPushforwardIso_hom_app (K : FormalCoproduct.{u} C) (X : Sheaf J (Type u)) :
    (freeSheafPushforwardIso J K).hom.app X =
      ((componentOverForget K).pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat.{u} (componentwiseTopology J K) J).inv.app
        (X.obj ⋙ AddCommGrpCat.free) :=
  rfl

omit [J.WEqualsLocallyBijective (Type u)] in
/-- `freeSheafPushforwardIso` is, at a sheaf, the pushforward-sheafification comparison at the
presheaf `X ⋙ ℤ`. -/
theorem freeSheafPushforwardIso_inv_app (K : FormalCoproduct.{u} C) (X : Sheaf J (Type u)) :
    (freeSheafPushforwardIso J K).inv.app X =
      ((componentOverForget K).pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat.{u} (componentwiseTopology J K) J).hom.app
        (X.obj ⋙ AddCommGrpCat.free) :=
  rfl

omit [J.WEqualsLocallyBijective (Type u)] in
/-- **The free abelian sheaf functor applied to the relocalization comparison inverts the
reindexing of the composition hexagon.** The hexagon
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility_comp'` begins with the
reindexing of the presheaf along `r_f ⋙ j_N = j_M`; on the presheaf `X ⋙ ℤ` that reindexing is
inverse to the free abelian sheaf functor applied to the relocalization comparison on sheaves of
sets. Both are `whiskerRight` of the two directions of one and the same `eqToIso`. -/
theorem composeAndSheafify_map_relocalizationForgetPushforwardIso'_comp (X : Sheaf J (Type u)) :
    (Sheaf.composeAndSheafify (componentwiseTopology J M) AddCommGrpCat.free).map
          ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
            (componentwiseTopology J N) (Type u)).hom.app X) ≫
        (presheafToSheaf (componentwiseTopology J M) AddCommGrpCat.{u}).map
          (Functor.whiskerRight
            (NatTrans.op (eqToIso (componentOverMap_comp_componentOverForget f)).hom)
            (X.obj ⋙ AddCommGrpCat.free)) = 𝟙 _ := by
  have hab : Functor.whiskerRight (Functor.whiskerRight
          (NatTrans.op (eqToIso (componentOverMap_comp_componentOverForget f)).inv) X.obj)
          AddCommGrpCat.free ≫
        Functor.whiskerRight
          (NatTrans.op (eqToIso (componentOverMap_comp_componentOverForget f)).hom)
          (X.obj ⋙ AddCommGrpCat.free) = 𝟙 _ := by
    refine NatTrans.ext (funext fun Y => ?_)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app, Functor.comp_map,
      NatTrans.op_app, ← Functor.map_comp, ← op_comp, Iso.hom_inv_id_app, op_id]
    exact (congrArg AddCommGrpCat.free.map (X.obj.map_id _)).trans
      (AddCommGrpCat.free.map_id _)
  refine Eq.trans
    (congrArg (fun m => m ≫ (presheafToSheaf (componentwiseTopology J M) AddCommGrpCat.{u}).map
        (Functor.whiskerRight
          (NatTrans.op (eqToIso (componentOverMap_comp_componentOverForget f)).hom)
          (X.obj ⋙ AddCommGrpCat.free)))
      (congrArg (fun m => (presheafToSheaf (componentwiseTopology J M) AddCommGrpCat.{u}).map
          (Functor.whiskerRight m AddCommGrpCat.free))
        (relocalizationForgetPushforwardIso'_hom_app_hom J f (Type u) X))) ?_
  exact ((presheafToSheaf (componentwiseTopology J M) AddCommGrpCat.{u}).map_comp _ _).symm.trans
    ((congrArg (presheafToSheaf (componentwiseTopology J M) AddCommGrpCat.{u}).map hab).trans
      ((presheafToSheaf (componentwiseTopology J M) AddCommGrpCat.{u}).map_id _))

omit [J.WEqualsLocallyBijective (Type u)] in
/-- **`freeSheafPushforwardIso` is natural in the semi-representable object.** For a morphism
`f : M ⟶ N` of semi-representable objects, the relocalization comparison carries the commutation
of restriction along `j_N` with the free abelian sheaf functor, followed by the commutation along
the relocalization functor `r_f`, to the commutation along `j_M`.

The square is stated on the inverses of the three commutations, which is the direction in which
it is the composition hexagon
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility_comp'` read at the
presheaf `X ⋙ ℤ`: inverting all four isomorphisms gives the `hom` form. The reindexing factor of
the hexagon is cancelled by
`composeAndSheafify_map_relocalizationForgetPushforwardIso'_comp`. -/
theorem freeSheafPushforwardIso_naturality (X : Sheaf J (Type u)) :
    (Sheaf.composeAndSheafify (componentwiseTopology J M) AddCommGrpCat.free).map
          ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
            (componentwiseTopology J N) (Type u)).hom.app X) ≫
        (freeSheafPushforwardIso J M).inv.app X =
      ((componentOverMap f).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u}
            (componentwiseTopology J M) (componentwiseTopology J N)).hom.app
          ((componentOverForget N).op ⋙ (X.obj ⋙ AddCommGrpCat.free)) ≫
        ((componentOverMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
              (componentwiseTopology J M) (componentwiseTopology J N)).map
            ((freeSheafPushforwardIso J N).inv.app X) ≫
          (relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
              (componentwiseTopology J N) AddCommGrpCat.{u}).hom.app
            ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj X) := by
  rw [freeSheafPushforwardIso_inv_app, freeSheafPushforwardIso_inv_app,
    Functor.pushforwardContinuousSheafificationCompatibility_comp'
      (eqToIso (componentOverMap_comp_componentOverForget f)) AddCommGrpCat.{u}
      (componentwiseTopology J M) (componentwiseTopology J N) J (X.obj ⋙ AddCommGrpCat.free)]
  exact (Category.assoc _ _ _).symm.trans
    ((eq_whisker (composeAndSheafify_map_relocalizationForgetPushforwardIso'_comp J f X) _).trans
      (Category.id_comp _))

end

end CategoryTheory.SemiRepresentable

end
