module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CohomologyZeroRepresentatives

/-!
# Semi-representable objects of the localization of a site at a presheaf of sets

Let `C` be a category and `G` a presheaf of sets on `C`. The localization `C/G` of Stacks 0791,
read for a presheaf, is `CostructuredArrow yoneda G`: its objects are the pairs `(U, s)` with
`s ∈ G(U)`. Write `F : SR(C) ⥤ PSh(C)` for the functor of Stacks 09VU sending a family `{U_i}` to
`∐ h_{U_i}`. This file proves the identification on which the hypercovering half of Stacks 09X6
rests:

`SR(C/G) ≌ SR(C)/G`,

where the right hand side is the category of semi-representable objects `X` of `C` together with
a map `F(X) ⟶ G`. A family `{(U_i, s_i)}` goes to `{U_i}` with the map `F({U_i}) ⟶ G` whose
restriction to the summand `h_{U_i}` is `s_i`; conversely a map `F({U_i}) ⟶ G` is the same as a
family of elements `s_i ∈ G(U_i)`.

It also records the first assertion of Stacks 09X6 about the site `C/G`: if `C` has fibre
products and equalizers, so does `C/G`.

## Main definitions

* `descOfElements` and `elementOf`: maps `F(X) ⟶ G` are families of elements of `G` over the
  summands of `X`.
* `forgetSR`: the functor `SR(C/G) ⥤ SR(C)` forgetting the elements.
* `augmentationOf`: the canonical map `F(forgetSR X) ⟶ G` of an object `X` of `SR(C/G)`.
* `toOver`, `ofOver` and `equivalence`: the equivalence `SR(C/G) ≌ SR(C)/G`.

## Main results

* `hasPullbacks_and_hasEqualizers`: **Stacks 09X6**, `C/G` has fibre products and equalizers
  when `C` has.
* `preservesLimitsOfShape_forgetSR`: `forgetSR` preserves limits of every connected shape, being
  the equivalence followed by the projection from a category of costructured arrows.

## Implementation notes

The functor `F` is `Stacks.CategoryTheory.Hypercovering.associatedPresheafFunctor` and `G` enters
through `liftedPresheaf`, exactly as in the definition `HypercoveringOf` of Stacks 09VU; both are
valued in `Type (max v w)` for index universe `w`. Maps out of `F(X)` are handled through
`sectionEquiv`, which identifies the sections of `F(X)` over `U` with the morphisms
`incl U ⟶ X` of `SR(C)`, so no computation with the chosen coproducts is needed.

## References

* [Stacks Project, Tag 09X6](https://stacks.math.columbia.edu/tag/09X6)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.CategoryTheory.Hypercovering.LocalizationAtPresheaf

variable {C : Type u} [Category.{v} C] {G : Cᵒᵖ ⥤ Type v}

/-! ### Maps from the presheaf of a semi-representable object to `G` -/

section Elements

/-- The function underlying `descOfElements`: the section `(i, k : U ⟶ X_i)` goes to
`G(k)(t_i)`. -/
def descOfElementsApp (X : FormalCoproduct.{w} C) (t : ∀ i : X.I, G.obj (op (X.obj i)))
    (U : C) (z : ((associatedPresheafFunctor.{v}).obj X).obj (op U)) :
    (liftedPresheaf.{v, w} G).obj (op U) :=
  ULift.up (G.map ((sectionEquiv X U) z).asSigma.2.op (t _))

/-- `descOfElementsApp` is natural in `U`. -/
lemma descOfElementsApp_naturality (X : FormalCoproduct.{w} C)
    (t : ∀ i : X.I, G.obj (op (X.obj i))) {U U' : C} (g : U' ⟶ U)
    (z : ((associatedPresheafFunctor.{v}).obj X).obj (op U)) :
    descOfElementsApp X t U' (((associatedPresheafFunctor.{v}).obj X).map g.op z) =
      (liftedPresheaf.{v, w} G).map g.op (descOfElementsApp X t U z) := by
  unfold descOfElementsApp
  rw [sectionEquiv_restrict]
  change ULift.up (G.map (g ≫ ((sectionEquiv X U) z).asSigma.2).op
      (t ((sectionEquiv X U) z).asSigma.1)) =
    ULift.up (G.map g.op (G.map ((sectionEquiv X U) z).asSigma.2.op
      (t ((sectionEquiv X U) z).asSigma.1)))
  rw [op_comp, Functor.map_comp_apply]

/-- The map `F(X) ⟶ G` determined by elements `t_i ∈ G(X_i)` over the summands of `X`. -/
def descOfElements (X : FormalCoproduct.{w} C) (t : ∀ i : X.I, G.obj (op (X.obj i))) :
    (associatedPresheafFunctor.{v}).obj X ⟶ liftedPresheaf.{v, w} G where
  app U := TypeCat.ofHom (descOfElementsApp X t U.unop)
  naturality U U' f := by
    ext z
    exact descOfElementsApp_naturality X t f.unop z

/-- The components of `descOfElements` are given by `descOfElementsApp`. -/
lemma descOfElements_app_apply (X : FormalCoproduct.{w} C)
    (t : ∀ i : X.I, G.obj (op (X.obj i))) (U : C)
    (z : ((associatedPresheafFunctor.{v}).obj X).obj (op U)) :
    (descOfElements X t).app (op U) z = descOfElementsApp X t U z :=
  rfl

/-- `descOfElements` on the section given by a component map. -/
lemma descOfElements_app_fromIncl (X : FormalCoproduct.{w} C)
    (t : ∀ i : X.I, G.obj (op (X.obj i))) {U : C} (i : X.I) (k : U ⟶ X.obj i) :
    (descOfElements X t).app (op U)
        ((sectionEquiv X U).symm (FormalCoproduct.Hom.fromIncl i k)) =
      ULift.up (G.map k.op (t i)) := by
  rw [descOfElements_app_apply]
  unfold descOfElementsApp
  rw [Equiv.apply_symm_apply]
  rfl

/-- The element `t_i ∈ G(X_i)` attached to the summand `i` by a map `F(X) ⟶ G`. -/
def elementOf {X : FormalCoproduct.{w} C}
    (α : (associatedPresheafFunctor.{v}).obj X ⟶ liftedPresheaf.{v, w} G) (i : X.I) :
    G.obj (op (X.obj i)) :=
  (α.app (op (X.obj i))
    ((sectionEquiv X (X.obj i)).symm (FormalCoproduct.Hom.fromIncl i (𝟙 _)))).down

/-- A map `F(X) ⟶ G` evaluated on the section `(i, k)`. -/
lemma app_fromIncl {X : FormalCoproduct.{w} C}
    (α : (associatedPresheafFunctor.{v}).obj X ⟶ liftedPresheaf.{v, w} G) {U : C} (i : X.I)
    (k : U ⟶ X.obj i) :
    α.app (op U) ((sectionEquiv X U).symm (FormalCoproduct.Hom.fromIncl i k)) =
      ULift.up (G.map k.op (elementOf α i)) := by
  have h : FormalCoproduct.Hom.fromIncl i k =
      (FormalCoproduct.incl C).map k ≫ FormalCoproduct.Hom.fromIncl i (𝟙 (X.obj i)) :=
    FormalCoproduct.hom_ext rfl (fun _ ↦ by
      simp only [FormalCoproduct.Hom.fromIncl]
      rfl)
  rw [h, sectionEquiv_symm_precomp, NatTrans.naturality_apply]
  rfl

/-- The elements of `descOfElements X t` are the `t_i`. -/
@[simp]
lemma elementOf_descOfElements (X : FormalCoproduct.{w} C)
    (t : ∀ i : X.I, G.obj (op (X.obj i))) (i : X.I) :
    elementOf (descOfElements X t) i = t i := by
  unfold elementOf
  rw [descOfElements_app_fromIncl]
  simp

/-- A map `F(X) ⟶ G` is recovered by `descOfElements` from its elements. -/
@[simp]
lemma descOfElements_elementOf {X : FormalCoproduct.{w} C}
    (α : (associatedPresheafFunctor.{v}).obj X ⟶ liftedPresheaf.{v, w} G) :
    descOfElements X (elementOf α) = α := by
  ext U z
  obtain ⟨s, rfl⟩ := (sectionEquiv X U.unop).symm.surjective z
  have h := (descOfElements_app_fromIncl X (elementOf α) s.asSigma.1 s.asSigma.2).trans
    (app_fromIncl α s.asSigma.1 s.asSigma.2).symm
  rw [s.fromIncl_asSigma] at h
  exact h

/-- Precomposing a map to `G` with the image of a morphism of `SR(C)`. -/
lemma elementOf_comp {X Y : FormalCoproduct.{w} C} (f : X ⟶ Y)
    (α : (associatedPresheafFunctor.{v}).obj Y ⟶ liftedPresheaf.{v, w} G) (i : X.I) :
    elementOf ((associatedPresheafFunctor.{v}).map f ≫ α) i =
      G.map (f.φ i).op (elementOf α (f.f i)) := by
  have h : FormalCoproduct.Hom.fromIncl i (𝟙 (X.obj i)) ≫ f =
      FormalCoproduct.Hom.fromIncl (f.f i) (f.φ i) :=
    FormalCoproduct.hom_ext rfl (fun _ ↦ by
      simp only [FormalCoproduct.Hom.fromIncl, FormalCoproduct.category_comp_φ]
      exact (Category.comp_id _).trans (Category.id_comp _))
  change (((associatedPresheafFunctor.{v}).map f ≫ α).app (op (X.obj i))
    ((sectionEquiv X (X.obj i)).symm (FormalCoproduct.Hom.fromIncl i (𝟙 _)))).down = _
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, ← sectionEquiv_symm_postcomp, h,
    app_fromIncl]

/-- Two maps `F(X) ⟶ G` agree as soon as their elements agree. -/
lemma hom_ext_of_elementOf {X : FormalCoproduct.{w} C}
    {α β : (associatedPresheafFunctor.{v}).obj X ⟶ liftedPresheaf.{v, w} G}
    (h : ∀ i, elementOf α i = elementOf β i) : α = β := by
  rw [← descOfElements_elementOf α, ← descOfElements_elementOf β]
  congr 1
  funext i
  exact h i

end Elements

/-! ### The equivalence `SR(C/G) ≌ SR(C)/G` -/

variable (G)

/-- The functor `SR(C/G) ⥤ SR(C)` forgetting the elements: `{(U_i, s_i)} ↦ {U_i}`. -/
abbrev forgetSR :
    FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G) ⥤ FormalCoproduct.{w} C :=
  mapFormalCoproduct (CostructuredArrow.proj yoneda G)

/-- The canonical map `F({U_i}) ⟶ G` of a family `{(U_i, s_i)}` of objects of `C/G`, whose
restriction to the summand `h_{U_i}` is `s_i`. -/
def augmentationOf (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)) :
    (associatedPresheafFunctor.{v}).obj ((forgetSR G).obj X) ⟶ liftedPresheaf.{v, w} G :=
  descOfElements ((forgetSR G).obj X) (fun i ↦ yonedaEquiv (X.obj i).hom)

/-- The element of `augmentationOf G X` over the summand `(U_i, s_i)` is `s_i`. -/
@[simp]
lemma elementOf_augmentationOf (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))
    (i : X.I) :
    elementOf (augmentationOf G X) i = yonedaEquiv (X.obj i).hom :=
  elementOf_descOfElements ((forgetSR G).obj X) (fun i ↦ yonedaEquiv (X.obj i).hom) i

/-- `augmentationOf` is natural: it is compatible with the image of a morphism of
`SR(C/G)`. -/
lemma map_comp_augmentationOf
    {X Y : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)} (f : X ⟶ Y) :
    (associatedPresheafFunctor.{v}).map ((forgetSR G).map f) ≫ augmentationOf G Y =
      augmentationOf G X := by
  refine hom_ext_of_elementOf (fun i ↦ ?_)
  rw [elementOf_comp]
  refine (congrArg (G.map ((f.φ i).left).op) (elementOf_augmentationOf G Y (f.f i))).trans ?_
  refine Eq.trans ?_ (elementOf_augmentationOf G X i).symm
  rw [yonedaEquiv_naturality, CostructuredArrow.w]

/-- The functor `SR(C/G) ⥤ SR(C)/G`. -/
def toOver :
    FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G) ⥤
      CostructuredArrow (associatedPresheafFunctor.{v} (C := C)) (liftedPresheaf.{v, w} G) :=
  Functor.toCostructuredArrow (forgetSR G) associatedPresheafFunctor.{v} (liftedPresheaf G)
    (augmentationOf G) (map_comp_augmentationOf G)

/-- The comparison of the elements of `G` underlying a morphism of `SR(C)/G`. -/
lemma yoneda_map_comp_yonedaEquiv_symm_elementOf
    {Y Y' : CostructuredArrow (associatedPresheafFunctor.{v} (C := C)) (liftedPresheaf.{v, w} G)}
    (φ : Y ⟶ Y') (i : Y.left.I) :
    yoneda.map (φ.left.φ i) ≫ yonedaEquiv.symm (elementOf Y'.hom (φ.left.f i)) =
      yonedaEquiv.symm (elementOf Y.hom i) := by
  rw [yonedaEquiv_symm_naturality_left, ← elementOf_comp, CostructuredArrow.w]

/-- The functor `SR(C)/G ⥤ SR(C/G)`: a map `F({U_i}) ⟶ G` is a family of elements
`s_i ∈ G(U_i)`. -/
def ofOver :
    CostructuredArrow (associatedPresheafFunctor.{v} (C := C)) (liftedPresheaf.{v, w} G) ⥤
      FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G) where
  obj Y := ⟨Y.left.I, fun i ↦ CostructuredArrow.mk (yonedaEquiv.symm (elementOf Y.hom i))⟩
  map {Y Y'} φ := ⟨φ.left.f, fun i ↦ CostructuredArrow.homMk (φ.left.φ i)
    (yoneda_map_comp_yonedaEquiv_symm_elementOf G φ i)⟩
  map_id Y := by
    refine FormalCoproduct.hom_ext rfl (fun i ↦ ?_)
    ext
    simp
  map_comp f g := by
    refine FormalCoproduct.hom_ext rfl (fun i ↦ ?_)
    ext
    simp

/-- Forgetting the elements after `ofOver` is the projection, on the nose. -/
lemma ofOver_comp_forgetSR :
    ofOver.{w} G ⋙ forgetSR G = CostructuredArrow.proj _ _ :=
  rfl

/-- `toOver` followed by the projection is `forgetSR`, on the nose. -/
lemma toOver_comp_proj :
    toOver.{w} G ⋙ CostructuredArrow.proj _ _ = forgetSR G :=
  rfl

/-- The component of `ofOver ⋙ toOver ≅ 𝟭` at an object: going down to `SR(C/G)` and back
returns the same semi-representable object of `C` with the same map to `G`. -/
def toOverObjOfOverIso
    (Y : CostructuredArrow (associatedPresheafFunctor.{v} (C := C)) (liftedPresheaf.{v, w} G)) :
    (toOver G).obj ((ofOver G).obj Y) ≅ Y :=
  CostructuredArrow.isoMk (Iso.refl _) (by
    change (associatedPresheafFunctor.{v}).map (𝟙 _) ≫ Y.hom = augmentationOf G ((ofOver G).obj Y)
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    refine hom_ext_of_elementOf (fun i ↦ ?_)
    exact ((elementOf_augmentationOf G ((ofOver G).obj Y) i).trans
      (Equiv.apply_symm_apply yonedaEquiv (elementOf Y.hom i))).symm)

/-- A morphism of `SR(C)/G` between images of `toOver` underlies a morphism of `SR(C/G)`: the
compatibility with the maps to `G` says that each component respects the elements. -/
def toOverPreimage {X Y : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)}
    (φ : (toOver G).obj X ⟶ (toOver G).obj Y) : X ⟶ Y :=
  ⟨φ.left.f, fun i ↦ CostructuredArrow.homMk (φ.left.φ i) (by
    apply yonedaEquiv.injective
    have h := congrArg (fun (α : (associatedPresheafFunctor.{v}).obj ((forgetSR G).obj X) ⟶
      liftedPresheaf.{v, w} G) ↦ elementOf α i) (CostructuredArrow.w φ)
    have h' : G.map (φ.left.φ i).op (elementOf (augmentationOf G Y) (φ.left.f i)) =
        elementOf (augmentationOf G X) i := (elementOf_comp φ.left _ i).symm.trans h
    have h₁ := elementOf_augmentationOf G X i
    have h₂ := elementOf_augmentationOf G Y (φ.left.f i)
    exact (yonedaEquiv_naturality (Y.obj (φ.left.f i)).hom (φ.left.φ i)).symm.trans
      ((congrArg (G.map (φ.left.φ i).op) h₂.symm).trans (h'.trans h₁)))⟩

/-- `toOver` is faithful. -/
instance faithful_toOver : (toOver.{w} G).Faithful where
  map_injective {X Y} f g h := by
    have h' : (forgetSR G).map f = (forgetSR G).map g := congrArg CommaMorphism.left h
    have hf : f.f = g.f :=
      congrArg (fun p : (forgetSR G).obj X ⟶ (forgetSR G).obj Y ↦ p.f) h'
    refine FormalCoproduct.hom_ext hf (fun i ↦ CostructuredArrow.hom_ext _ _ ?_)
    have h₂ := ((FormalCoproduct.hom_ext_iff _ _).1 h').2 i
    rw [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
    exact h₂

/-- `toOver` is full, with preimages given by `toOverPreimage`. -/
instance full_toOver : (toOver.{w} G).Full where
  map_surjective {_ _} φ := ⟨toOverPreimage G φ, CostructuredArrow.hom_ext _ _ rfl⟩

/-- `toOver` is essentially surjective, every object being isomorphic to the image of its
image under `ofOver`. -/
instance essSurj_toOver : (toOver.{w} G).EssSurj where
  mem_essImage Y := ⟨(ofOver G).obj Y, ⟨toOverObjOfOverIso G Y⟩⟩

/-- `toOver` is an equivalence of categories. -/
instance isEquivalence_toOver : (toOver.{w} G).IsEquivalence where

/-- **`SR(C/G) ≌ SR(C)/G`.** Semi-representable objects of the localization of `C` at the
presheaf `G` are the semi-representable objects of `C` endowed with a map to `G`. -/
def equivalence :
    FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G) ≌
      CostructuredArrow (associatedPresheafFunctor.{v} (C := C)) (liftedPresheaf.{v, w} G) :=
  (toOver G).asEquivalence

/-- `forgetSR` preserves limits of every connected shape: it is the equivalence
`SR(C/G) ≌ SR(C)/G` followed by the projection, which preserves connected limits. -/
instance preservesLimitsOfShape_forgetSR (J : Type*) [Category J] [IsConnected J] :
    PreservesLimitsOfShape J (forgetSR.{w} G) := by
  change PreservesLimitsOfShape J (toOver G ⋙ CostructuredArrow.proj _ _)
  infer_instance

/-! ### Limits in the localization -/

/-- **Stacks 09X6, the site `C/G` has fibre products and equalizers.** If `C` has fibre products
and equalizers, so does the localization `C/G` of `C` at a presheaf of sets `G`: the projection
`C/G ⥤ C` creates connected limits. -/
@[stacks 09X6 "the site `C/G` of pairs `(U, s)`, `s ∈ G(U)`, has fibre products and equalizers"]
theorem hasPullbacks_and_hasEqualizers [HasPullbacks C] [HasEqualizers C] :
    HasPullbacks (CostructuredArrow (yoneda (C := C)) G) ∧
      HasEqualizers (CostructuredArrow (yoneda (C := C)) G) :=
  ⟨inferInstance, inferInstance⟩

end Stacks.CategoryTheory.Hypercovering.LocalizationAtPresheaf

end
