module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriekFreeYoneda
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceLowerShriekFreeYonedaFunctor

/-!
# The simplicial abelian sheaf `p ↦ a_! g_{p!} j_p^{-1} ℤ_V^♯`

Let `(C, J)` be a small site, `V` an object of `C` and `K` a simplicial object of `SR(C)`.
`CategoryTheory.SemiRepresentable.shriekRestrictionFreeYoneda` is the functor
`L ↦ j_{L!} j_L^{-1} ℤ_V^♯` on semi-representable objects, isomorphic to `L ↦ ℤ_{h_V × F(L)}^♯`
by Stacks 0D87 part (2). Composing the two with `K` gives **simplicial** abelian sheaves, and the
isomorphism becomes an isomorphism of simplicial abelian sheaves: a degreewise comparison with a
naturality in the simplex maps.

In simplicial degree `p` the composite `a_! g_{p!}` of the extension by zero from the component of
degree `p` into the total site with the extension by zero along the augmentation is `j_{p!}`
(`CategoryTheory.SimplicialSemiRepresentable.componentLowerShriekCompAugmentationAbelianIso`), and
`CategoryTheory.SimplicialSemiRepresentable.augmentationComponentFreeYonedaIso` identifies
`a_! g_{p!} j_p^{-1} ℤ_V^♯` with `ℤ_{h_V × F(K_p)}^♯`. This module also assembles that family into
a simplicial abelian sheaf whose degree-`p` value is the composite of the two extensions by zero
on the nose -- which is the shape the Čech resolution of `a^{-1}ℤ_V^♯` has after `a_!` is applied
to it degreewise, and the shape a degreewise comparison of that resolution with
`p ↦ ℤ_{h_V × F(K_p)}^♯` must be natural as.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.freeYonedaSimplicial` and
  `.shriekRestrictionFreeYonedaSimplicial`: the two functors of
  `StacksFrontier/CategoryTheory/Sites/Simplicial/SliceLowerShriekFreeYonedaFunctor.lean` along `K`,
  with `.shriekRestrictionFreeYonedaSimplicialIso` the resulting isomorphism of simplicial
  abelian sheaves.
* `CategoryTheory.SimplicialSemiRepresentable.sliceFreeYonedaLowerShriekSimplicial` and
  `.augmentationComponentFreeYonedaSimplicial`: simplicial abelian sheaves whose degree-`p`
  values are `j_{p!} j_p^{-1} ℤ_V^♯` at the topology of the simplicial degree, and the composite
  `a_! g_{p!} j_p^{-1} ℤ_V^♯` through the total site, with
  `.sliceFreeYonedaLowerShriekSimplicialIso` and `.augmentationComponentFreeYonedaSimplicialIso`
  their identifications with `p ↦ ℤ_{h_V × F(K_p)}^♯` and
  `.augmentationComponentFreeYonedaSimplicialIsoShriekRestriction` the comparison of the last of
  these with the carrier whose simplex maps are the transitions themselves.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.shriekRestrictionFreeYonedaSimplicial_map`: the
  simplex maps of `p ↦ j_{K_p!} j_{K_p}^{-1} ℤ_V^♯` are the shriek restriction transitions of the
  morphisms `K α` of semi-representable objects.
* `CategoryTheory.SimplicialSemiRepresentable.augmentationComponentFreeYonedaSimplicialIso_app`:
  the identification of `p ↦ a_! g_{p!} j_p^{-1} ℤ_V^♯` factors in each degree through the one of
  `p ↦ j_{p!} j_p^{-1} ℤ_V^♯`.

## Implementation notes

`sliceFreeYonedaLowerShriekSimplicial` and `augmentationComponentFreeYonedaSimplicial` are
`CategoryTheory.Functor.copyObj` of `freeYonedaSimplicial` rather than composites with a functor
on semi-representable objects, so their simplex maps are the transported ones and their
simplicial identities are Mathlib's. The reason is that their degree-`p` values are stated at the
topology `(situation J K).componentTopology p` of the simplicial degree, which is only
*propositionally* the componentwise localized topology, and at that spelling the shriek
restriction transition cannot be written down at all: neither the continuity of `j_p`, registered
for `sliceForget K (op p)` and asked for at `componentOverForget (K.obj (op p))`, nor the
sheafification of abelian sheaves on a component, which is
`CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent` and a theorem rather than an
instance, is found by instance search there -- and installing both by hand, as local instances or
as local hypotheses of a `letI`, does not help either, because the two spellings of the component
category are identified only by unfolding the definitions of `situation` and of
`SimplicialSiteSituation.component`, which instance search does not do. What the two carry
instead is their identification with `freeYonedaSimplicial`, which composed with
`shriekRestrictionFreeYonedaSimplicialIso` relates their simplex maps to the transitions;
`augmentationComponentFreeYonedaSimplicialIsoShriekRestriction` is that composite.

For the same reason a goal mentioning the degree-`p` value of either of the two is not
type-correct at the `implicit` transparency level that `rw` checks its motive at, so no `rw` in
such a goal fires. Their `..._map_eq` lemmas are supplied so that the transported form is reached
by `Eq.trans` instead.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.WEqualsLocallyBijective (Type u)] (V : C)

/-! ### The two functors along a simplicial semi-representable object -/

/-- **The simplicial abelian sheaf `p ↦ ℤ_{h_V × F(K_p)}^♯`**: the functor
`CategoryTheory.SemiRepresentable.freeYonedaProd` along `K`. -/
def freeYonedaSimplicial : SimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  K ⋙ freeYonedaProd J V

/-- **The simplicial abelian sheaf `p ↦ j_{K_p!} j_{K_p}^{-1} ℤ_V^♯`**: the functor
`CategoryTheory.SemiRepresentable.shriekRestrictionFreeYoneda` along `K`. Its simplex maps are
the shriek restriction transitions of the morphisms `K α` of semi-representable objects, which is
`shriekRestrictionFreeYonedaSimplicial_map`. -/
def shriekRestrictionFreeYonedaSimplicial : SimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  K ⋙ shriekRestrictionFreeYoneda J V

/-- The degree-`p` term of `p ↦ j_{K_p!} j_{K_p}^{-1} ℤ_V^♯`. -/
theorem shriekRestrictionFreeYonedaSimplicial_obj (p : SimplexCategoryᵒᵖ) :
    (shriekRestrictionFreeYonedaSimplicial J K V).obj p =
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget (K.obj p))
          AddCommGrpCat.{u} (componentwiseTopology J (K.obj p)) J).obj
        (((componentOverForget (K.obj p)).sheafPushforwardContinuous AddCommGrpCat.{u}
          (componentwiseTopology J (K.obj p)) J).obj
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) :=
  rfl

/-- **The simplex maps of `p ↦ j_{K_p!} j_{K_p}^{-1} ℤ_V^♯` are the shriek restriction
transitions.** -/
theorem shriekRestrictionFreeYonedaSimplicial_map {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    (shriekRestrictionFreeYonedaSimplicial J K V).map α =
      (shriekRestrictionTransition J (K.map α) (componentwiseTopology J (K.obj p))
            (componentwiseTopology J (K.obj q)) AddCommGrpCat.{u}).app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) :=
  rfl

/-- **Stacks 0D87 part (2) at `ℤ_V^♯` along a simplicial semi-representable object, as an
isomorphism of simplicial abelian sheaves.** This is the degreewise identification
`j_{K_p!} j_{K_p}^{-1} ℤ_V^♯ ≅ ℤ_{h_V × F(K_p)}^♯` together with its naturality in the simplex
maps. -/
def shriekRestrictionFreeYonedaSimplicialIso :
    shriekRestrictionFreeYonedaSimplicial J K V ≅ freeYonedaSimplicial J K V :=
  Functor.isoWhiskerLeft K (shriekRestrictionFreeYonedaIso J V)

/-! ### The two spellings through the simplicial-site situation -/

section Situation

variable [J.toCoverage.HasPullbacks]

/-- **The simplicial abelian sheaf `p ↦ j_{p!} j_p^{-1} ℤ_V^♯`**, with its degree-`p` value
spelled by the extension by zero
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriek` of the simplicial degree and
the topology of that degree.

This is `freeYonedaSimplicial` with its objects replaced by that spelling along
`CategoryTheory.SimplicialSemiRepresentable.sliceFreeYonedaLowerShriekIso`, rather than
`shriekRestrictionFreeYonedaSimplicial` itself: see the implementation notes for why the
transition cannot be written at the topology of a simplicial degree. -/
def sliceFreeYonedaLowerShriekSimplicial : SimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  (freeYonedaSimplicial J K V).copyObj
    (fun p => (sliceAbelianLowerShriek J K p.unop).obj
      (((sliceForget K (op p.unop)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology p.unop) J).obj
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))
    (fun p => (sliceFreeYonedaLowerShriekIso J K p.unop V).symm)

/-- The degree-`p` term of `p ↦ j_{p!} j_p^{-1} ℤ_V^♯`. -/
theorem sliceFreeYonedaLowerShriekSimplicial_obj (p : SimplexCategoryᵒᵖ) :
    (sliceFreeYonedaLowerShriekSimplicial J K V).obj p =
      (sliceAbelianLowerShriek J K p.unop).obj
        (((sliceForget K (op p.unop)).sheafPushforwardContinuous AddCommGrpCat.{u}
          ((situation J K).componentTopology p.unop) J).obj
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) :=
  rfl

/-- The simplex map of `p ↦ j_{p!} j_p^{-1} ℤ_V^♯`, in the transported form it is defined by. -/
theorem sliceFreeYonedaLowerShriekSimplicial_map_eq {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    (sliceFreeYonedaLowerShriekSimplicial J K V).map α =
      (sliceFreeYonedaLowerShriekIso J K p.unop V).hom ≫
        (freeYonedaSimplicial J K V).map α ≫
          (sliceFreeYonedaLowerShriekIso J K q.unop V).inv :=
  rfl

/-- **The degreewise identification `j_{p!} j_p^{-1} ℤ_V^♯ ≅ ℤ_{h_V × F(K_p)}^♯` is an
isomorphism of simplicial abelian sheaves.** -/
def sliceFreeYonedaLowerShriekSimplicialIso :
    sliceFreeYonedaLowerShriekSimplicial J K V ≅ freeYonedaSimplicial J K V :=
  ((freeYonedaSimplicial J K V).isoCopyObj _ _).symm

/-- In degree `p` the simplicial identification is the degreewise one. -/
theorem sliceFreeYonedaLowerShriekSimplicialIso_app (p : SimplexCategoryᵒᵖ) :
    (sliceFreeYonedaLowerShriekSimplicialIso J K V).hom.app p =
      (sliceFreeYonedaLowerShriekIso J K p.unop V).hom :=
  rfl

/-- **The simplicial abelian sheaf `p ↦ a_! g_{p!} j_p^{-1} ℤ_V^♯`**: in simplicial degree `p`
the free abelian sheaf on `V`, restricted to the site `C/K_p` of that degree, extended by zero
into the total site and then extended by zero along the augmentation.

Its degree-`p` value is the composite of the two extensions by zero on the nose, which is the
shape the Čech resolution of `a^{-1}ℤ_V^♯` has after `a_!` is applied to it degreewise. -/
def augmentationComponentFreeYonedaSimplicial : SimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  (freeYonedaSimplicial J K V).copyObj
    (fun p => (augmentationAbelianLowerShriek J K).obj
      ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) p.unop).obj
        (((sliceForget K (op p.unop)).sheafPushforwardContinuous AddCommGrpCat.{u}
          ((situation J K).componentTopology p.unop) J).obj
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))))
    (fun p => (augmentationComponentFreeYonedaIso J K p.unop V).symm)

/-- The degree-`p` term of `p ↦ a_! g_{p!} j_p^{-1} ℤ_V^♯` is the composite of the two extensions
by zero applied to the restriction of `ℤ_V^♯`. -/
theorem augmentationComponentFreeYonedaSimplicial_obj (p : SimplexCategoryᵒᵖ) :
    (augmentationComponentFreeYonedaSimplicial J K V).obj p =
      (augmentationAbelianLowerShriek J K).obj
        ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) p.unop).obj
          (((sliceForget K (op p.unop)).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).componentTopology p.unop) J).obj
            (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) :=
  rfl

/-- The simplex map of `p ↦ a_! g_{p!} j_p^{-1} ℤ_V^♯`, in the transported form it is defined
by. -/
theorem augmentationComponentFreeYonedaSimplicial_map_eq {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    (augmentationComponentFreeYonedaSimplicial J K V).map α =
      (augmentationComponentFreeYonedaIso J K p.unop V).hom ≫
        (freeYonedaSimplicial J K V).map α ≫
          (augmentationComponentFreeYonedaIso J K q.unop V).inv :=
  rfl

/-- **The degreewise identification `a_! g_{p!} j_p^{-1} ℤ_V^♯ ≅ ℤ_{h_V × F(K_p)}^♯` is an
isomorphism of simplicial abelian sheaves.** -/
def augmentationComponentFreeYonedaSimplicialIso :
    augmentationComponentFreeYonedaSimplicial J K V ≅ freeYonedaSimplicial J K V :=
  ((freeYonedaSimplicial J K V).isoCopyObj _ _).symm

/-- **The two simplicial identifications differ by `a_! g_{p!} ≅ j_{p!}` in each degree.** The
identification of `p ↦ a_! g_{p!} j_p^{-1} ℤ_V^♯` with `p ↦ ℤ_{h_V × F(K_p)}^♯` is, in degree `p`,
the identification of the composite of the two extensions by zero with `j_{p!}` followed by the
identification of `p ↦ j_{p!} j_p^{-1} ℤ_V^♯` with `p ↦ ℤ_{h_V × F(K_p)}^♯`. -/
theorem augmentationComponentFreeYonedaSimplicialIso_app (p : SimplexCategoryᵒᵖ) :
    (augmentationComponentFreeYonedaSimplicialIso J K V).hom.app p =
      (componentLowerShriekCompAugmentationAbelianIso J K p.unop).hom.app _ ≫
        (sliceFreeYonedaLowerShriekSimplicialIso J K V).hom.app p :=
  rfl

/-- **The carrier `p ↦ a_! g_{p!} j_p^{-1} ℤ_V^♯` is isomorphic, as a simplicial abelian sheaf, to
the one whose simplex maps are the shriek restriction transitions.** This is what relates its
simplex maps, which are transported, to the canonical transitions of
`shriekRestrictionFreeYonedaSimplicial`. -/
def augmentationComponentFreeYonedaSimplicialIsoShriekRestriction :
    augmentationComponentFreeYonedaSimplicial J K V ≅
      shriekRestrictionFreeYonedaSimplicial J K V :=
  augmentationComponentFreeYonedaSimplicialIso J K V ≪≫
    (shriekRestrictionFreeYonedaSimplicialIso J K V).symm

end Situation

end CategoryTheory.SimplicialSemiRepresentable

end
