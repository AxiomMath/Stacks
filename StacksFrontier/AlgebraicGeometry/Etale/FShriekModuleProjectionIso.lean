module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionFiberComponents
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionStalk

/-!
# The projection formula for the direct image with compact support

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring, let `F` be a sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. The comparison

`can : f_!F ⊗_Λ G ⟶ f_!(F ⊗_Λ f^{-1}G)`

of [Stacks, Tag 0GKF] is `AlgebraicGeometry.SmallEtale.modFShriekProjectionMap`, the
sheafification of the source's recipe `(Z, s) ⊗ t ↦ (Z, s ⊗ f^{-1}t)` on presheaves. This file
proves it an isomorphism, which is the content of the tag.

## Main definitions

* `AlgebraicGeometry.SmallEtale.modFShriekProjectionIso` — **the projection formula**
  `f_!F ⊗_Λ G ≅ f_!(F ⊗_Λ f^{-1}G)`.

## Main results

* `AlgebraicGeometry.SmallEtale.presheafFiber_map_modFiniteSupportTensorPresheafMap` — **the
  fibre of the projection map of presheaves is the fibre comparison
  `AlgebraicGeometry.SmallEtale.modProjectionFiberIso`.** This is the identity the source's
  stalk computation amounts to.
* `AlgebraicGeometry.SmallEtale.W_modFiniteSupportTensorPresheafMap` — the projection map of
  presheaves is a local isomorphism.
* `AlgebraicGeometry.SmallEtale.isIso_modFShriekProjectionMap` — **`can` is an isomorphism.**

## Implementation notes

The fibre identity is checked on germs: by
`CategoryTheory.GrothendieckTopology.Point.presheafFiber_hom_ext` it suffices to compare the two
maps on the germ at a pointed étale neighbourhood `V` of a section of `f_{p!}F ⊗_Λ G` over `V`,
by `TensorProduct.ext'` on a pure tensor, and by
`AlgebraicGeometry.SmallEtale.exists_modFiniteSupportGenerator_sum` — the formal-sum
presentation of Stacks 0F6J — on a generator tensored with a section of `G`. There the two sides
are the germ formulae of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionFiberComponents`.

From that identity the fibre of the projection map is an isomorphism at every geometric point of
`Y`, hence so is the fibre of its sheafification
(`CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`) and hence so is
the stalk of the underlying morphism of abelian sheaves
(`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso`). Geometric stalks detect
isomorphisms of abelian étale sheaves (`AlgebraicGeometry.isIso_of_isIso_etaleStalkMap`), and
`CategoryTheory.sheafCompose` by a forgetful functor reflecting isomorphisms carries that back to
sheaves of `Λ`-modules; `CategoryTheory.GrothendieckTopology.W_iff` then puts the presheaf map in
`J.W`, which is what `AlgebraicGeometry.SmallEtale.isIso_modFShriekProjectionMap_of_W` consumes.

The detour through abelian sheaves is forced: Mathlib's
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` instance asks the coefficient
category's carriers to live in the universe of the site, and the coefficient universe here is
independent of the universe of the schemes.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 0F6J](https://stacks.math.columbia.edu/tag/0F6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped DirectSum

namespace Stacks

/-- **Cancelling two isomorphisms on the right.** Isolated as a statement about abstract
morphisms so that it applies to terms whose types agree only up to unfolding a definition, where
`CategoryTheory.Iso.cancel_iso_hom_right` cannot be rewritten with. -/
public theorem comp_iso_cancel {C : Type*} [Category* C] {W P Q R : C} (g g' : W ⟶ P)
    (e : P ≅ Q) (d : Q ≅ R) (h : g ≫ e.hom ≫ d.hom = g' ≫ e.hom ≫ d.hom) : g = g' := by
  rw [← Category.assoc, ← Category.assoc] at h
  exact (cancel_mono e.hom).1 ((cancel_mono d.hom).1 h)

/-- **Transporting `IsIso` along a commuting square two of whose sides are isomorphisms.**
Isolated as a statement about abstract morphisms so that it applies to terms whose types agree
only up to unfolding a definition. -/
public theorem isIso_of_comp_iso_eq {C : Type*} [Category* C] {W P Q R : C} (a : W ⟶ Q)
    (e : Q ≅ R) (b : W ≅ P) (m : P ⟶ R) [IsIso m] (h : a ≫ e.hom = b.hom ≫ m) : IsIso a := by
  have : IsIso (a ≫ e.hom) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_right a e.hom

end Stacks

namespace AlgebraicGeometry.SmallEtale

universe u v

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat
attribute [local instance] hasLimitsOfSizeModuleCatSmall
attribute [local instance] preservesFilteredColimitsTensorLeftSmall
attribute [local instance] preservesFilteredColimitsTensorRightSmall

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The fibre of the projection map is the fibre comparison.** -/
public theorem presheafFiber_map_modFiniteSupportTensorPresheafMap (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
        (modFiniteSupportTensorPresheafMap B Λ f F G) =
      (modProjectionFiberIso.{u, v} B Λ f s F G).hom := by
  refine (geometricPointSitePoint B Y.obj Y.property s).presheafFiber_hom_ext fun V y => ?_
  rw [toPresheafFiber_modFiniteSupportTensorPresheafMap B Λ f F G s V y]
  refine Stacks.comp_iso_cancel _ _
    (modFiniteSupportFiberIso B Λ f
      (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s)
    (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
      (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) ?_
  refine ModuleCat.hom_ext (TensorProduct.ext' fun pp tt => ?_)
  obtain ⟨n, Z, aa, rfl⟩ := exists_modFiniteSupportGenerator_sum B Λ f F V pp
  rw [TensorProduct.sum_tmul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => DFinsupp.ext fun x => ?_
  exact (modFiniteSupportTensorBilinear_germ_generator B Λ f s F G ⟨V, y⟩ (Z i) (aa i) tt x).trans
    (modProjectionFiberIso_germ_generator B Λ f s F G ⟨V, y⟩ (Z i) (aa i) tt x).symm

/-- The fibre of the projection map at a geometric point of `Y` is an isomorphism. -/
public theorem isIso_presheafFiber_map_modFiniteSupportTensorPresheafMap
    (s : GeometricPoint Y.obj) (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    IsIso ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
      (modFiniteSupportTensorPresheafMap B Λ f F G)) := by
  rw [presheafFiber_map_modFiniteSupportTensorPresheafMap B Λ f s F G]
  infer_instance

/-- The fibre of the sheafified projection map at a geometric point of `Y` is an isomorphism:
the fibre of a sheafification is the fibre of the presheaf. -/
public theorem isIso_presheafFiber_map_sheafify_modFiniteSupportTensorPresheafMap
    (s : GeometricPoint Y.obj) (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    IsIso ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
      (((presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
          (ModuleCat.{max (u + 1) v} Λ)).map
        (modFiniteSupportTensorPresheafMap B Λ f F G)).hom)) := by
  have := isIso_presheafFiber_map_modFiniteSupportTensorPresheafMap B Λ f s F G
  exact (NatIso.isIso_map_iff
    ((geometricPointSitePoint B Y.obj Y.property s).presheafToSheafCompSheafFiberIso
      (ModuleCat.{max (u + 1) v} Λ)) (modFiniteSupportTensorPresheafMap B Λ f F G)).2 this

/-- The stalk at a geometric point of the abelian sheaf morphism underlying the sheafified
projection map is an isomorphism: the fibre of the underlying abelian presheaf is the abelian
group underlying the fibre. -/
public theorem isIso_etaleStalk_map_sheafify_modFiniteSupportTensorPresheafMap
    (s : GeometricPoint Y.obj) (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    IsIso ((etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{max (u + 1) v}).map
      (((sheafCompose (SmallEtale.topology B Y.obj Y.property)
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).map
          ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
              (ModuleCat.{max (u + 1) v} Λ)).map
            (modFiniteSupportTensorPresheafMap B Λ f F G))).hom)) := by
  have := isIso_presheafFiber_map_sheafify_modFiniteSupportTensorPresheafMap B Λ f s F G
  exact (NatIso.isIso_map_iff ((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}))
    ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
      (ModuleCat.{max (u + 1) v} Λ)).map (modFiniteSupportTensorPresheafMap B Λ f F G)).hom).2
    (Functor.map_isIso (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})
      ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map _))

/-- **The projection map of presheaves is a local isomorphism.** Its fibre at every geometric
point of `Y` is the fibre comparison, which is an isomorphism; the geometric stalks of the
underlying abelian sheaves therefore detect that the sheafification is an isomorphism, and a map
of presheaves inverted by sheafification lies in `J.W`. -/
public theorem W_modFiniteSupportTensorPresheafMap
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (SmallEtale.topology B Y.obj Y.property).W
      (modFiniteSupportTensorPresheafMap B Λ f F G) := by
  rw [GrothendieckTopology.W_iff]
  have : IsIso ((sheafCompose (SmallEtale.topology B Y.obj Y.property)
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).map
      ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
          (ModuleCat.{max (u + 1) v} Λ)).map
        (modFiniteSupportTensorPresheafMap B Λ f F G))) :=
    isIso_of_isIso_etaleStalkMap.{u, max (u + 1) v} B Y.obj Y.property _
      fun s => isIso_etaleStalk_map_sheafify_modFiniteSupportTensorPresheafMap B Λ f s F G
  exact isIso_of_reflects_iso _ (sheafCompose (SmallEtale.topology B Y.obj Y.property)
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}))

/-- **Stacks 0GKF**, the projection formula for the direct image with compact support: for a
locally quasi-finite morphism `f : X ⟶ Y` the canonical map
`can : f_!F ⊗_Λ G ⟶ f_!(F ⊗_Λ f^{-1}G)` of
`AlgebraicGeometry.SmallEtale.modFShriekProjectionMap` is an isomorphism. -/
public theorem isIso_modFShriekProjectionMap
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    IsIso (modFShriekProjectionMap B Λ f F G) :=
  isIso_modFShriekProjectionMap_of_W B Λ f F G
    (W_modFiniteSupportTensorPresheafMap B Λ f F G)

/-- **Stacks 0GKF**, the canonical isomorphism of the projection formula
`f_!F ⊗_Λ G ≅ f_!(F ⊗_Λ f^{-1}G)` for a locally quasi-finite morphism `f : X ⟶ Y`. -/
@[stacks 0GKF "the projection formula isomorphism"]
public def modFShriekProjectionIso
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G ≅
      (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj
        (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) :=
  haveI := isIso_modFShriekProjectionMap B Λ f F G
  asIso (modFShriekProjectionMap B Λ f F G)

end AlgebraicGeometry.SmallEtale

end
