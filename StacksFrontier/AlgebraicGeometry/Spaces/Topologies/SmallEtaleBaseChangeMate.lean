module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.MateCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChange

/-!
# The étale base-change 2-cell is an isomorphism

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  The adjunctions of the morphisms of small étale topoi of `i` and of `g` turn
the direct-image comparison `i_* f_* ≅ f'_* g_*` of the square into a 2-cell

`f_{small,*} ∘ g_{small}^{-1} ⟶ i_{small}^{-1} ∘ f'_{small,*}`,

its *mate*, which is `AlgebraicGeometry.Space.properBaseChangeMap`. This file proves that the
mate is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.spacesToposBaseChangeSquare`: the same 2-cell on the spaces-étale
  topoi, as the mate of the comparison of composite direct images.
* `AlgebraicGeometry.Space.smallToposBaseChangeSquareIso`: the base-change isomorphism on the
  small étale topoi, obtained from the spaces-étale one by the comparison equivalences.

## Main results

* `AlgebraicGeometry.Space.isIso_properBaseChangeMap`: the base-change 2-cell of a cartesian
  square with étale bottom arrow is an isomorphism.
* `AlgebraicGeometry.Space.mateEquiv_smallToposBaseChangeSquareIso` and
  `AlgebraicGeometry.Space.properBaseChangeMap_eq_smallToposBaseChangeSquareIso`: the 2-cell is
  the base-change isomorphism, and conversely.
* `AlgebraicGeometry.Space.properBaseChangeMap_eq_mateEquiv_inverseImageSquare`: the two usual
  constructions of the base-change 2-cell — the mate of the direct-image comparison across the
  two étale legs, and the mate of the inverse-image comparison across the two vertical legs —
  agree.
* `CategoryTheory.mateEquiv_beckChevalleyIso`,
  `AlgebraicGeometry.Space.mateEquiv_spacesEtaleBaseChangeSquare` and
  `AlgebraicGeometry.Space.mateEquiv_spacesPushforwardBaseChangeIso`: the same identification on
  slice categories, on the spaces-étale sites, and on the spaces-étale topoi.

## References

* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.CategoryTheory

universe v₁ v₂ u₁ u₂ u₃ u₄ t w

/-! ### Pushforward of sheaves along a natural transformation of sites -/

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type w} [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- Restriction of sheaves along a composite of natural transformations of continuous functors
of sites is the composite of the restrictions, in the opposite order. -/
theorem sheafPushforwardContinuousNatTrans_comp {F F' F'' : C ⥤ D}
    [F.IsContinuous J K] [F'.IsContinuous J K] [F''.IsContinuous J K]
    (τ : F ⟶ F') (τ' : F' ⟶ F'') :
    sheafPushforwardContinuousNatTrans (A := A) (τ ≫ τ') J K =
      sheafPushforwardContinuousNatTrans (A := A) τ' J K ≫
        sheafPushforwardContinuousNatTrans (A := A) τ J K := by
  ext M U
  exact M.obj.map_comp _ _

/-- Restriction of sheaves along the identity transformation is the identity. -/
theorem sheafPushforwardContinuousNatTrans_id {F : C ⥤ D} [F.IsContinuous J K] :
    sheafPushforwardContinuousNatTrans (A := A) (𝟙 F) J K = 𝟙 _ := by
  ext M U
  exact M.obj.map_id _

/-- Restriction of sheaves along an equality of continuous functors of sites is the
corresponding equality of restriction functors. -/
theorem sheafPushforwardContinuousNatTrans_eqToHom {F F' : C ⥤ D}
    [F.IsContinuous J K] [F'.IsContinuous J K] (h : F = F') :
    sheafPushforwardContinuousNatTrans (A := A) (eqToHom h) J K =
      eqToHom (by subst h; rfl) := by
  subst h
  ext M U
  exact M.obj.map_id _

end CategoryTheory.Functor

/-! ### Transporting a morphism of topoi along equivalences -/

namespace MorphismOfTopoi

variable {E : Type u₁} [Category.{v₁} E] {F : Type u₂} [Category.{v₂} F]
  {E' : Type u₃} [Category.{v₁} E'] {F' : Type u₄} [Category.{v₂} F']

/-- The inverse image of a transported morphism of topoi agrees with the original one after the
two equivalences: precomposing with `eF.functor` cancels the `eF.inverse` in the definition of
`MorphismOfTopoi.transport`, by the unit isomorphism of `eF`. -/
def transport_inverseImage_comparison (φ : MorphismOfTopoi E F) (eE : E ≌ E') (eF : F ≌ F') :
    eF.functor ⋙ (φ.transport eE eF).inverseImage ≅ φ.inverseImage ⋙ eE.functor :=
  Functor.isoWhiskerRight eF.unitIso.symm (φ.inverseImage ⋙ eE.functor) ≪≫
    Functor.leftUnitor _

/-- Restricting a transported morphism of topoi back along the two equivalences, through the
canonical comparisons of its direct and inverse images, returns the original adjunction. -/
theorem transport_restrict_adj (φ : MorphismOfTopoi E F) (eE : E ≌ E') (eF : F ≌ F') :
    (φ.transport eE eF).adj.restrictFullyFaithful eF.fullyFaithfulFunctor
        eE.fullyFaithfulFunctor (transport_inverseImage_comparison φ eE eF)
        (transport_pushforward_comparison φ eE eF) = φ.adj := by
  refine Adjunction.ext (NatTrans.ext (funext fun W => ?_))
  apply eF.fullyFaithfulFunctor.map_injective
  refine Eq.trans (Adjunction.map_restrictFullyFaithful_unit_app _ _ _ _ _ W) ?_
  simp only [Functor.id_obj, Functor.comp_obj, transport, Equivalence.symm_functor,
    Equivalence.symm_inverse, Equivalence.toAdjunction, Equivalence.symm_unit,
    Equivalence.symm_counit, Adjunction.comp, Functor.whiskerRight_comp, Category.assoc,
    Adjunction.mk'_unit, Adjunction.mk'_counit, Functor.whiskerLeft_comp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, CategoryTheory.Functor.map_id,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.comp_map, Category.comp_id, Category.id_comp, transport_inverseImage_comparison,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.leftUnitor_hom_app,
    Equivalence.inv_fun_map, Functor.map_comp, transport_pushforward_comparison, cancelIso]
  rw [← Functor.map_comp, φ.adj.unit_naturality, Functor.map_comp, ← Category.assoc]
  simp

end MorphismOfTopoi

/-! ### Beck–Chevalley on slice categories -/

namespace CategoryTheory

variable {C : Type*} [Category C] [HasPullbacks C] {X' X Y' Y : C}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- For a commuting square, the comparison of the two composites of base change on slices,
assembled from `CategoryTheory.Over.pullbackComp` on the two diagonals. -/
def overPullbackCompSquare (w : i ≫ f = f' ≫ g) :
    Over.pullback g ⋙ Over.pullback f' ⟶ Over.pullback f ⋙ Over.pullback i :=
  (Over.pullbackComp f' g).inv ≫
    eqToHom (congrArg (fun k : X' ⟶ Y => Over.pullback (f := k)) w.symm) ≫
    (Over.pullbackComp i f).hom

/-- The two canonical comparisons of `Over.pullback f' ⋙ Over.map i` with
`Over.map g ⋙ Over.pullback f` attached to a cartesian square agree: both are determined by the
two projections of the fibre product. -/
theorem beckChevalleyIso_hom_eq (sq : IsPullback i f' f g) :
    (Over.beckChevalleyIso sq).hom = (overPullbackBaseChangeIso i f' f g sq).inv := by
  ext W
  apply pullback.hom_ext <;>
    simp [Over.beckChevalleyIso, Over.beckChevalleyObjIso, overPullbackBaseChangeIso]

/-- The conjugate of the comparison of the two composites of postcomposition on slices is the
comparison of the two composites of base change. -/
theorem conjugateEquiv_overMapCommSquare (w : i ≫ f = f' ≫ g) :
    conjugateEquiv ((Over.mapPullbackAdj f').comp (Over.mapPullbackAdj g))
        ((Over.mapPullbackAdj i).comp (Over.mapPullbackAdj f))
        (overMapCommSquare i f' f g w).hom =
      overPullbackCompSquare i f' f g w := by
  have conj_eqToHom : ∀ {U V : C} {k k' : U ⟶ V} (hk : k = k'),
      conjugateEquiv (Over.mapPullbackAdj k') (Over.mapPullbackAdj k)
          (eqToHom (congrArg (fun h : U ⟶ V => Over.map h) hk)) =
        eqToHom (congrArg (fun h : U ⟶ V => Over.pullback (f := h)) hk.symm) := by
    rintro U V k k' rfl
    simp
  rw [show (overMapCommSquare i f' f g w).hom =
      ((Over.mapComp i f).inv ≫ eqToHom (congrArg (fun h : X' ⟶ Y => Over.map h) w)) ≫
        (Over.mapComp f' g).hom from by
      simp [overMapCommSquare, Category.assoc]]
  rw [← conjugateEquiv_comp _ (Over.mapPullbackAdj (f' ≫ g)) _,
    ← conjugateEquiv_comp _ (Over.mapPullbackAdj (i ≫ f)) _, conj_eqToHom w]
  rfl

/-- An equation between two composites whose outer factors are identities is the equation
between the inner factors. The four outer factors are given with hypotheses `hu`, `hu'`, `hv`,
`hv'` saying that they are identities. -/
theorem eq_of_comp_comp_eq_comp_comp {C₀ : Type*} [Category C₀] {X₀ Y₀ : C₀}
    {u u' : X₀ ⟶ X₀} {v v' : Y₀ ⟶ Y₀} {a b : X₀ ⟶ Y₀} (hu : u = 𝟙 X₀) (hu' : u' = 𝟙 X₀)
    (hv : v = 𝟙 Y₀) (hv' : v' = 𝟙 Y₀) (h : u ≫ u' ≫ a = b ≫ v ≫ v') : a = b := by
  simpa [hu, hu', hv, hv'] using h

/-- Cancelling a fully faithful functor off a natural isomorphism, read on components. -/
theorem map_fullyFaithfulCancelRight_hom_app {A₀ B₀ C₀ : Type*} [Category A₀] [Category B₀]
    [Category C₀] {F G : A₀ ⥤ B₀} {H : B₀ ⥤ C₀} [H.Full] [H.Faithful] (comp_iso : F ⋙ H ≅ G ⋙ H)
    (X : A₀) :
    H.map ((Functor.fullyFaithfulCancelRight H comp_iso).hom.app X) = comp_iso.hom.app X := by
  simp [Functor.fullyFaithfulCancelRight_hom_app]

/-- Beck–Chevalley on slices, as a mate: for a cartesian square, the mate of the
Beck–Chevalley isomorphism with respect to the adjunctions along the two horizontal arrows is
the comparison of the two composites of base change. -/
theorem mateEquiv_beckChevalleyIso (sq : IsPullback i f' f g) :
    mateEquiv (Over.mapPullbackAdj g) (Over.mapPullbackAdj i)
        (TwoSquare.mk _ _ _ _ (Over.beckChevalleyIso sq).hom) =
      TwoSquare.mk _ _ _ _ (overPullbackCompSquare i f' f g sq.w) := by
  have key := iterated_mateEquiv_conjugateEquiv (Over.mapPullbackAdj f')
    (Over.mapPullbackAdj f) (Over.mapPullbackAdj i) (Over.mapPullbackAdj g)
    (TwoSquare.mk _ _ _ _ (overMapCommSquare i f' f g sq.w).hom)
  rwa [mateEquiv_overMapCommSquare i f' f g sq, ← beckChevalleyIso_hom_eq i f' f g sq,
    conjugateEquiv_overMapCommSquare] at key

end CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-! ### Beck–Chevalley on the spaces-étale sites -/

/-- For a commuting square of algebraic spaces, the comparison of the two composites of
spaces-étale base change, assembled from the composition isomorphism of base change on the two
diagonals. -/
def spacesBaseChangeCompSquare (w : i ≫ f = f' ≫ g) :
    (spacesBaseChange B S hS g).functor ⋙ (spacesBaseChange B S hS f').functor ⟶
      (spacesBaseChange B S hS f).functor ⋙ (spacesBaseChange B S hS i).functor :=
  (spacesBaseChange_comp B S hS f' g).hom ≫
    eqToHom (congrArg (fun k : X' ⟶ Y => (spacesBaseChange B S hS k).functor) w.symm) ≫
    (spacesBaseChange_comp B S hS i f).inv

/-- The inclusion of a spaces-étale site into the slice carries the comparison of the
base-change functors along two equal morphisms to the comparison of the two slice base-change
functors. -/
theorem inclusion_map_spacesBaseChange_eqToHom_app {U V : AlgebraicSpaces B S hS} {k k' : U ⟶ V}
    (hk : k = k') (W : SpacesEtale B S hS V) :
    (SpacesEtale.inclusion B S hS U).map
        ((eqToHom (congrArg (fun m : U ⟶ V => (spacesBaseChange B S hS m).functor) hk)).app W) =
      (eqToHom (congrArg (fun m : U ⟶ V => Over.pullback (f := m)) hk)).app
        ((SpacesEtale.inclusion B S hS V).obj W) := by
  subst hk
  rfl

/-- `AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare` is the Beck–Chevalley isomorphism of
slices with the fully faithful inclusion of the spaces-étale site cancelled off, so the two have
the same components. -/
theorem spacesEtaleBaseChangeSquare_hom_app_map (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (V : SpacesEtale B S hS Y') :
    (SpacesEtale.inclusion B S hS X).map
        ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app V) =
      (Over.beckChevalleyIso sq).hom.app ((SpacesEtale.inclusion B S hS Y').obj V) :=
  CategoryTheory.map_fullyFaithfulCancelRight_hom_app _ V

/-- The spaces-étale and the slice comparisons of the two composites of base change have the
same components: each factor of the former is the restriction to the étale objects of the
corresponding factor of the latter. -/
theorem spacesBaseChangeCompSquare_app_map (w : i ≫ f = f' ≫ g) (V : SpacesEtale B S hS Y) :
    (SpacesEtale.inclusion B S hS X').map
        ((spacesBaseChangeCompSquare B S hS i f' f g w).app V) =
      (overPullbackCompSquare i f' f g w).app ((SpacesEtale.inclusion B S hS Y).obj V) := by
  simp only [spacesBaseChangeCompSquare, overPullbackCompSquare, NatTrans.comp_app,
    Functor.map_comp]
  rw [inclusion_map_spacesBaseChange_eqToHom_app B S hS w.symm]
  rfl

/-- Beck–Chevalley on the spaces-étale sites, as a mate: for a cartesian square with étale
bottom arrow, the mate of the spaces-étale Beck–Chevalley isomorphism with respect to the two
adjunctions between postcomposition and base change is the comparison of the two composites of
base change. -/
theorem mateEquiv_spacesEtaleBaseChangeSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    mateEquiv (spacesEtalePostcompBaseChangeAdjunction B S hS g hg)
        (spacesEtalePostcompBaseChangeAdjunction B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (TwoSquare.mk _ _ _ _ (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom) =
      TwoSquare.mk _ _ _ _ (spacesBaseChangeCompSquare B S hS i f' f g sq.w) := by
  have hi := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  have key := mateEquiv_restrictFullyFaithful_app
    (iC := SpacesEtale.inclusion B S hS Y') (iD := SpacesEtale.inclusion B S hS Y)
    (iE := SpacesEtale.inclusion B S hS X') (iF := SpacesEtale.inclusion B S hS X)
    (L₁ := spacesEtalePostcomp B S hS g hg) (R₁ := (spacesBaseChange B S hS g).functor)
    (L₂ := spacesEtalePostcomp B S hS i hi) (R₂ := (spacesBaseChange B S hS i).functor)
    (G := (spacesBaseChange B S hS f').functor) (H := (spacesBaseChange B S hS f).functor)
    (G' := Over.pullback f') (H' := Over.pullback f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Over.mapPullbackAdj g) (Over.mapPullbackAdj i)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm
    (TwoSquare.mk _ _ _ _ (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom)
    (TwoSquare.mk _ _ _ _ (Over.beckChevalleyIso sq).hom)
    (fun W => comp_comp_eq_comp_comp_of_eq_id
      (spacesEtaleBaseChangeSquare_hom_app_map B S hS i f' f g sq hg W)
      ((Over.map i).map_id _) rfl ((Over.pullback f).map_id _) rfl)
  refine TwoSquare.ext _ _ fun V => ?_
  have hV := eq_of_comp_comp_eq_comp_comp ((Over.pullback f').map_id _) rfl
    ((Over.pullback i).map_id _) rfl (key V)
  have hbig := congrArg
    (fun t : TwoSquare (Over.pullback g) (Over.pullback f) (Over.pullback f') (Over.pullback i) =>
      t.natTrans.app ((SpacesEtale.inclusion B S hS Y).obj V))
    (mateEquiv_beckChevalleyIso i f' f g sq)
  exact (ObjectProperty.fullyFaithfulι (IsEtaleOver B S hS X')).map_injective
    (hV.trans (hbig.trans (spacesBaseChangeCompSquare_app_map B S hS i f' f g sq.w V).symm))

/-! ### Beck–Chevalley on the spaces-étale topoi -/

/-- The comparison of the two composite direct images of a commuting square on the spaces-étale
topoi, assembled from the composition isomorphism of direct images on the two diagonals. -/
def spacesPushforwardCompSquare (w : i ≫ f = f' ≫ g) :
    (spacesBaseChange B S hS i).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X') ⋙
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⟶
    (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') ⋙
      (spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y') :=
  (spacesBaseChange_pushforward_comp B S hS i f).hom ≫
    eqToHom (congrArg (fun k : X' ⟶ Y =>
      (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) w) ≫
    (spacesBaseChange_pushforward_comp B S hS f' g).inv

/-- The comparison of the two composite direct images is the restriction to sheaves of the
comparison of the two composites of base change on the sites. -/
theorem spacesPushforwardCompSquare_eq (w : i ≫ f = f' ≫ g) :
    letI := Functor.isContinuous_comp (spacesBaseChange B S hS g).functor
      (spacesBaseChange B S hS f').functor
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y')
      (SpacesEtale.topology B S hS X')
    letI := Functor.isContinuous_comp (spacesBaseChange B S hS f).functor
      (spacesBaseChange B S hS i).functor
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
      (SpacesEtale.topology B S hS X')
    spacesPushforwardCompSquare B S hS i f' f g w =
      Functor.sheafPushforwardContinuousNatTrans
        (spacesBaseChangeCompSquare B S hS i f' f g w) (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X') := by
  rw [spacesPushforwardCompSquare, spacesBaseChangeCompSquare,
    Functor.sheafPushforwardContinuousNatTrans_comp,
    Functor.sheafPushforwardContinuousNatTrans_comp,
    Functor.sheafPushforwardContinuousNatTrans_eqToHom, Category.assoc]
  rfl

/-- The spaces-étale base-change isomorphism
`AlgebraicGeometry.Space.spacesPushforwardBaseChangeIso` is the restriction to sheaves of the
Beck–Chevalley isomorphism of the sites. -/
theorem spacesPushforwardBaseChangeIso_inv (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    letI := Functor.isContinuous_comp (spacesBaseChange B S hS f').functor
      (spacesEtalePostcomp B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X')
      (SpacesEtale.topology B S hS X)
    letI := Functor.isContinuous_comp
      (spacesEtalePostcomp B S hS g hg) (spacesBaseChange B S hS f).functor
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS Y)
      (SpacesEtale.topology B S hS X)
    (spacesPushforwardBaseChangeIso B S hS i f' f g sq hg).inv =
      Functor.sheafPushforwardContinuousNatTrans
        (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom (Type (u + 1))
        (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X) :=
  rfl

/-- Beck–Chevalley on the spaces-étale topoi, as a mate: the mate of the spaces-étale base-change
isomorphism `AlgebraicGeometry.Space.spacesPushforwardBaseChangeIso`, with respect to the two
adjunctions between restriction along étale postcomposition and direct image, is the comparison of
the two composite direct images. -/
theorem mateEquiv_spacesPushforwardBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    mateEquiv (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) g hg)
        (TwoSquare.mk _ _ _ _
          (spacesPushforwardBaseChangeIso B S hS i f' f g sq hg).inv) =
      TwoSquare.mk _ _ _ _ (spacesPushforwardCompSquare B S hS i f' f g sq.w) := by
  have key := mateEquiv_sheafPushforwardContinuousNatTrans
    (adj₁ := spacesEtalePostcompBaseChangeAdjunction B S hS g hg)
    (adj₂ := spacesEtalePostcompBaseChangeAdjunction B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
    (A := Type (u + 1))
    (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS X') (SpacesEtale.topology B S hS X)
    (TwoSquare.mk _ _ _ _ (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom)
  rw [mateEquiv_spacesEtaleBaseChangeSquare] at key
  rw [spacesPushforwardBaseChangeIso_inv, spacesPushforwardCompSquare_eq]
  exact key

/-! ### The two constructions of the base-change 2-cell -/

/-- The conjugate of the inverse of the inverse-image composition isomorphism of small étale
topoi is the inverse of the direct-image one. -/
theorem conjugateEquiv_smallToposMorphism_comp_inverseImage_inv {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (smallToposMorphism B S hS (f ≫ g)).adj
        ((smallToposMorphism B S hS g).adj.comp (smallToposMorphism B S hS f).adj)
        (smallToposMorphism_comp_inverseImage B S hS f g).inv =
      (smallToposMorphism_comp B S hS f g).inv := by
  rw [show (smallToposMorphism_comp_inverseImage B S hS f g).inv =
    (Adjunction.leftAdjointUniq
      (((smallToposMorphism B S hS g).adj.comp
        (smallToposMorphism B S hS f).adj).ofNatIsoRight
          (smallToposMorphism_comp B S hS f g))
      (smallToposMorphism B S hS (f ≫ g)).adj).hom from
      NatTrans.ext (funext fun x => Adjunction.leftAdjointUniq_inv_app _ _ x)]
  exact conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

/-- The conjugate of the inverse-image composition isomorphism of small étale topoi is the
direct-image one. -/
theorem conjugateEquiv_smallToposMorphism_comp_inverseImage {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((smallToposMorphism B S hS g).adj.comp (smallToposMorphism B S hS f).adj)
        (smallToposMorphism B S hS (f ≫ g)).adj
        (smallToposMorphism_comp_inverseImage B S hS f g).hom =
      (smallToposMorphism_comp B S hS f g).hom := by
  have hcomm := conjugateEquiv_comm
    ((smallToposMorphism B S hS g).adj.comp (smallToposMorphism B S hS f).adj)
    (smallToposMorphism B S hS (f ≫ g)).adj
    (α := (smallToposMorphism_comp_inverseImage B S hS f g).hom)
    (β := (smallToposMorphism_comp_inverseImage B S hS f g).inv)
    (Iso.inv_hom_id _)
  rw [conjugateEquiv_smallToposMorphism_comp_inverseImage_inv] at hcomm
  exact ((Iso.comp_inv_eq (smallToposMorphism_comp B S hS f g)).mp hcomm).trans
    (Category.id_comp _)

/-- The conjugate of the identification of the inverse images of two equal morphisms is the
identification of their direct images. -/
theorem conjugateEquiv_smallToposMorphism_inverseImage_eqToHom {U V : AlgebraicSpaces B S hS}
    {k k' : U ⟶ V} (hk : k = k') :
    conjugateEquiv (smallToposMorphism B S hS k).adj (smallToposMorphism B S hS k').adj
        (eqToHom (congrArg (fun h : U ⟶ V => (smallToposMorphism B S hS h).inverseImage)
          hk.symm)) =
      eqToHom (congrArg (fun h : U ⟶ V => (smallToposMorphism B S hS h).pushforward) hk) := by
  subst hk
  simp

variable {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The inverse-image comparison of a cartesian square and the direct-image comparison are
conjugate: each of their three factors is conjugate to the corresponding factor of the other. -/
theorem conjugateEquiv_smallEtaleInverseImageSquareIso (sq : IsPullback i f' f g) :
    conjugateEquiv ((smallToposMorphism B S hS f).adj.comp (smallToposMorphism B S hS i).adj)
        ((smallToposMorphism B S hS g).adj.comp (smallToposMorphism B S hS f').adj)
        (smallEtaleInverseImageSquareIso B S hS i f' f g sq).hom =
      (smallToposPushforwardBaseChange B S hS f g f' i sq.w).hom := by
  rw [show (smallEtaleInverseImageSquareIso B S hS i f' f g sq).hom =
      ((smallToposMorphism_comp_inverseImage B S hS f' g).inv ≫
        eqToHom (congrArg (fun h : X' ⟶ Y =>
          (smallToposMorphism B S hS h).inverseImage) sq.w.symm)) ≫
        (smallToposMorphism_comp_inverseImage B S hS i f).hom from by
      simp [smallEtaleInverseImageSquareIso, Category.assoc]]
  rw [← conjugateEquiv_comp _ (smallToposMorphism B S hS (i ≫ f)).adj _,
    ← conjugateEquiv_comp _ (smallToposMorphism B S hS (f' ≫ g)).adj _,
    conjugateEquiv_smallToposMorphism_comp_inverseImage B S hS i f,
    conjugateEquiv_smallToposMorphism_inverseImage_eqToHom B S hS sq.w,
    conjugateEquiv_smallToposMorphism_comp_inverseImage_inv B S hS f' g]
  rfl

/-- The two usual constructions of the base-change 2-cell of a cartesian square agree: the mate
of the direct-image comparison across the two horizontal adjunctions is the mate of the
inverse-image comparison across the two vertical ones. -/
theorem properBaseChangeMap_eq_mateEquiv_inverseImageSquare (sq : IsPullback i f' f g) :
    properBaseChangeMap B S hS f g f' i sq =
      mateEquiv (smallToposMorphism B S hS f).adj (smallToposMorphism B S hS f').adj
        (smallEtaleInverseImageSquareIso B S hS i f' f g sq).hom := by
  have key := iterated_mateEquiv_conjugateEquiv_symm
    (smallToposMorphism B S hS f).adj (smallToposMorphism B S hS f').adj
    (smallToposMorphism B S hS g).adj (smallToposMorphism B S hS i).adj
    (smallToposPushforwardBaseChange B S hS f g f' i sq.w).hom
  have hc := (Equiv.symm_apply_eq
    (conjugateEquiv ((smallToposMorphism B S hS f).adj.comp (smallToposMorphism B S hS i).adj)
      ((smallToposMorphism B S hS g).adj.comp
        (smallToposMorphism B S hS f').adj))).mpr
          (conjugateEquiv_smallEtaleInverseImageSquareIso B S hS i f' f g sq).symm
  rw [Equiv.trans_apply, hc] at key
  exact (Equiv.symm_apply_eq _).mp key

/-! ### From the spaces-étale topoi to the small étale topoi -/

/-- The inverse image of the morphism of small étale topoi agrees, through the comparison
equivalences, with the inverse image of the spaces-étale morphism of topoi. -/
def smallToposMorphism_inverseImage_comparison {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) :
    (smallEtaleToposEquiv B S hS V).functor ⋙ (smallToposMorphism B S hS h).inverseImage ≅
      ((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).inverseImage ⋙
        (smallEtaleToposEquiv B S hS U).functor :=
  MorphismOfTopoi.transport_inverseImage_comparison _ _ _

/-- The adjunction of the spaces-étale morphism of topoi, with its direct image written out as
restriction along base change. -/
def spacesToposAdjunction {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) :
    ((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).inverseImage ⊣
      (spacesBaseChange B S hS h).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS U) :=
  ((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).adj

/-- The base-change 2-cell of a cartesian square on the spaces-étale topoi: the mate of the
comparison of the two composite direct images. -/
def spacesToposBaseChangeSquare (sq : IsPullback i f' f g) :
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        ((spacesBaseChange_isMorphismOfSites B S hS g).morphismOfTopoi).inverseImage ⟶
      ((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).inverseImage ⋙
        (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') :=
  (mateEquiv (spacesToposAdjunction B S hS i) (spacesToposAdjunction B S hS g)).symm
    (spacesPushforwardCompSquare B S hS i f' f g sq.w)

/-- Beck–Chevalley for inverse images on the spaces-étale topoi: for a cartesian square with
étale bottom arrow the base-change 2-cell is invertible. -/
theorem isIso_spacesToposBaseChangeSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq) := by
  have hi := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  have h1 : (mateEquiv (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) i hi)
        (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) g hg)).symm
          (spacesPushforwardCompSquare B S hS i f' f g sq.w) =
      (spacesPushforwardBaseChangeIso B S hS i f' f g sq hg).inv :=
    (Equiv.symm_apply_eq _).mpr
      (mateEquiv_spacesPushforwardBaseChangeIso B S hS i f' f g sq hg).symm
  have h3 := mateEquiv_symm_congr_left (spacesToposAdjunction B S hS i)
      (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) i hi)
      (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) g hg)
      (spacesPushforwardCompSquare B S hS i f' f g sq.w)
  have h2 := mateEquiv_symm_congr_right (spacesToposAdjunction B S hS i)
      (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) g hg)
      (spacesToposAdjunction B S hS g)
      (spacesPushforwardCompSquare B S hS i f' f g sq.w)
  rw [h3, h1] at h2
  refine Eq.mpr (congrArg IsIso h2) ?_
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
  infer_instance

/-- The base-change 2-cell on the spaces-étale topoi of a cartesian square with étale bottom
arrow, as an isomorphism. -/
def spacesToposBaseChangeSquareIso (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) :
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        ((spacesBaseChange_isMorphismOfSites B S hS g).morphismOfTopoi).inverseImage ≅
      ((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).inverseImage ⋙
        (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') :=
  @asIso _ _ _ _ (spacesToposBaseChangeSquare B S hS i f' f g sq)
    (isIso_spacesToposBaseChangeSquare B S hS i f' f g sq hg)

/-- The source of the small étale base-change square, carried into the spaces-étale topos of
`Y'` by the comparison equivalences and the spaces-étale base-change isomorphism. -/
def smallToposBaseChangeHalfLeft (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) :
    (smallEtaleToposEquiv B S hS X).functor ⋙
        (smallToposMorphism B S hS f).pushforward ⋙
          (smallToposMorphism B S hS g).inverseImage ≅
      ((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).inverseImage ⋙
        (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') ⋙
          (smallEtaleToposEquiv B S hS Y').functor :=
  let Iy' := (smallEtaleToposEquiv B S hS Y').functor
  let Ig := (smallToposMorphism B S hS g).inverseImage
  let Rf := (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  Functor.isoWhiskerRight (smallToposMorphism_comparison B S hS f) Ig ≪≫
    Functor.isoWhiskerLeft Rf (smallToposMorphism_inverseImage_comparison B S hS g) ≪≫
    Functor.isoWhiskerRight (spacesToposBaseChangeSquareIso B S hS i f' f g sq hg) Iy'

/-- The target of the small étale base-change square, carried into the spaces-étale topos of
`Y'` by the comparison equivalences. -/
def smallToposBaseChangeHalfRight :
    (smallEtaleToposEquiv B S hS X).functor ⋙
        (smallToposMorphism B S hS i).inverseImage ⋙
          (smallToposMorphism B S hS f').pushforward ≅
      ((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).inverseImage ⋙
        (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') ⋙
          (smallEtaleToposEquiv B S hS Y').functor :=
  let Pf' := (smallToposMorphism B S hS f').pushforward
  let Li := ((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).inverseImage
  Functor.isoWhiskerRight (smallToposMorphism_inverseImage_comparison B S hS i) Pf' ≪≫
    Functor.isoWhiskerLeft Li (smallToposMorphism_comparison B S hS f')

/-- The base-change isomorphism of the small étale topoi, precomposed with the comparison
equivalence of `X`. -/
def smallToposBaseChangeBigIso (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) :
    (smallEtaleToposEquiv B S hS X).functor ⋙
        (smallToposMorphism B S hS f).pushforward ⋙
          (smallToposMorphism B S hS g).inverseImage ≅
      (smallEtaleToposEquiv B S hS X).functor ⋙
        (smallToposMorphism B S hS i).inverseImage ⋙
          (smallToposMorphism B S hS f').pushforward :=
  smallToposBaseChangeHalfLeft B S hS i f' f g sq hg ≪≫
    (smallToposBaseChangeHalfRight B S hS i f').symm

/-- Composing the base-change isomorphism with the right half returns the left half. -/
theorem smallToposBaseChangeBigIso_hom_comp (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    (smallToposBaseChangeBigIso B S hS i f' f g sq hg).hom ≫
        (smallToposBaseChangeHalfRight B S hS i f').hom =
      (smallToposBaseChangeHalfLeft B S hS i f' f g sq hg).hom := by
  simp [smallToposBaseChangeBigIso]

/-- Étale base change for direct images of sheaves of sets on the small étale topoi: for a
cartesian square with étale bottom arrow, direct image along `f` followed by restriction to `Y'`
is isomorphic to restriction to `X'` followed by direct image along `f'`. -/
def smallToposBaseChangeSquareIso (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) :
    (smallToposMorphism B S hS f).pushforward ⋙
        (smallToposMorphism B S hS g).inverseImage ≅
      (smallToposMorphism B S hS i).inverseImage ⋙
        (smallToposMorphism B S hS f').pushforward :=
  ((Functor.whiskeringLeft _ _ _).obj (smallEtaleToposEquiv B S hS X).functor).preimageIso
    (smallToposBaseChangeBigIso B S hS i f' f g sq hg)

/-- The comparison of the small étale direct image with the spaces-étale one is natural in the
morphism of algebraic spaces. -/
theorem smallToposMorphism_comparison_eqToHom {U V : AlgebraicSpaces B S hS} {k k' : U ⟶ V}
    (hk : k = k') (d : Sheaf (SpacesEtale.topology B S hS U) (Type (u + 1))) :
    (smallToposMorphism_comparison B S hS k).hom.app d ≫
        (smallEtaleToposEquiv B S hS V).functor.map
          ((eqToHom (congrArg (fun m : U ⟶ V =>
            (spacesBaseChange B S hS m).functor.sheafPushforwardContinuous (Type (u + 1))
              (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS U)) hk)).app d) =
      (eqToHom (congrArg (fun m : U ⟶ V =>
          (smallToposMorphism B S hS m).pushforward) hk)).app
            ((smallEtaleToposEquiv B S hS U).functor.obj d) ≫
        (smallToposMorphism_comparison B S hS k').hom.app d := by
  subst hk
  simp only [eqToHom_refl, NatTrans.id_app, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Cancelling the invertible factors in a chain of four commuting pieces. -/
private theorem comp_comp_eq_of_comparisons {C₀ : Type*} [Category C₀]
    {P Q R S T U P' P'' V W : C₀} {a : P ⟶ Q} {cf : Q ⟶ R} {M : R ⟶ S} {e : S ⟶ T} {N : T ⟶ U}
    {s : P ⟶ P'} {C₁ : P' ⟶ S} {q : P' ⟶ P''} {C₂ : P'' ⟶ T} {t : P'' ⟶ V} {B₁ : V ⟶ W}
    {B₂ : W ⟶ U} {M' : U ⟶ T} {m : P ⟶ V} (h₁ : a ≫ cf ≫ M = s ≫ C₁) (h₂ : C₁ ≫ e = q ≫ C₂)
    (h₃ : t ≫ B₁ ≫ B₂ ≫ M' = C₂) (h₄ : M' ≫ N = 𝟙 U) (hm : m = s ≫ q ≫ t) :
    a ≫ cf ≫ M ≫ e ≫ N = m ≫ B₁ ≫ B₂ := by
  rw [hm, reassoc_of% h₁, reassoc_of% h₂, ← h₃]
  simp [h₄]

/-- The comparison of the two composite direct images on the small étale topoi is the transport,
along the comparison equivalences, of the spaces-étale one. -/
theorem smallToposPushforwardBaseChange_comparison (sq : IsPullback i f' f g)
    (d : Sheaf (SpacesEtale.topology B S hS X') (Type (u + 1))) :
    (smallToposMorphism B S hS f).pushforward.map
          ((smallToposMorphism_comparison B S hS i).hom.app d) ≫
        (smallToposMorphism_comparison B S hS f).hom.app
          (((spacesBaseChange B S hS i).functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X')).obj d) ≫
        (smallEtaleToposEquiv B S hS Y).functor.map
          ((spacesPushforwardCompSquare B S hS i f' f g sq.w).app d) =
      (smallToposPushforwardBaseChange B S hS f g f' i sq.w).hom.app
          ((smallEtaleToposEquiv B S hS X').functor.obj d) ≫
        (smallToposMorphism B S hS g).pushforward.map
          ((smallToposMorphism_comparison B S hS f').hom.app d) ≫
        (smallToposMorphism_comparison B S hS g).hom.app
          (((spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X')).obj d) := by
  have hA :
      (smallToposMorphism B S hS f).pushforward.map
          ((smallToposMorphism_comparison B S hS i).hom.app d) ≫
        (smallToposMorphism_comparison B S hS f).hom.app
          (((spacesBaseChange B S hS i).functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X')).obj d) ≫
        (smallEtaleToposEquiv B S hS Y).functor.map
          ((spacesBaseChange_pushforward_comp B S hS i f).hom.app d) =
      (smallToposMorphism_comp B S hS i f).hom.app
          ((smallEtaleToposEquiv B S hS X').functor.obj d) ≫
        (smallToposMorphism_comparison B S hS (i ≫ f)).hom.app d :=
    smallToposMorphism_comp_comparison B S hS i f d
  have hB :
      (smallToposMorphism B S hS g).pushforward.map
          ((smallToposMorphism_comparison B S hS f').hom.app d) ≫
        (smallToposMorphism_comparison B S hS g).hom.app
          (((spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X')).obj d) ≫
        (smallEtaleToposEquiv B S hS Y).functor.map
          ((spacesBaseChange_pushforward_comp B S hS f' g).hom.app d) =
      (smallToposMorphism_comp B S hS f' g).hom.app
          ((smallEtaleToposEquiv B S hS X').functor.obj d) ≫
        (smallToposMorphism_comparison B S hS (f' ≫ g)).hom.app d :=
    smallToposMorphism_comp_comparison B S hS f' g d
  have hE : (smallToposMorphism_comparison B S hS (i ≫ f)).hom.app d ≫
        (smallEtaleToposEquiv B S hS Y).functor.map
          ((eqToHom (congrArg (fun k : X' ⟶ Y =>
            (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type (u + 1))
              (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) sq.w)).app d) =
      (eqToHom (congrArg (fun h : X' ⟶ Y => (smallToposMorphism B S hS h).pushforward)
          sq.w)).app ((smallEtaleToposEquiv B S hS X').functor.obj d) ≫
        (smallToposMorphism_comparison B S hS (f' ≫ g)).hom.app d :=
    smallToposMorphism_comparison_eqToHom B S hS sq.w d
  have hcancel : (smallEtaleToposEquiv B S hS Y).functor.map
      ((spacesBaseChange_pushforward_comp B S hS f' g).hom.app d) ≫
        (smallEtaleToposEquiv B S hS Y).functor.map
          ((spacesBaseChange_pushforward_comp B S hS f' g).inv.app d) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have s6a : (smallToposPushforwardBaseChange B S hS f g f' i sq.w).hom =
      (smallToposMorphism_comp B S hS i f).hom ≫
        eqToHom (congrArg (fun h : X' ⟶ Y =>
          (smallToposMorphism B S hS h).pushforward) sq.w) ≫
        (smallToposMorphism_comp B S hS f' g).inv := rfl
  have hPBC : (smallToposPushforwardBaseChange B S hS f g f' i sq.w).hom.app
        ((smallEtaleToposEquiv B S hS X').functor.obj d) =
      (smallToposMorphism_comp B S hS i f).hom.app
          ((smallEtaleToposEquiv B S hS X').functor.obj d) ≫
        (eqToHom (congrArg (fun h : X' ⟶ Y => (smallToposMorphism B S hS h).pushforward)
          sq.w)).app ((smallEtaleToposEquiv B S hS X').functor.obj d) ≫
        (smallToposMorphism_comp B S hS f' g).inv.app
          ((smallEtaleToposEquiv B S hS X').functor.obj d) :=
    (NatTrans.congr_app s6a _).trans
      ((NatTrans.comp_app _ _ _).trans
        ((smallToposMorphism_comp B S hS i f).hom.app
          ((smallEtaleToposEquiv B S hS X').functor.obj d) ≫= NatTrans.comp_app _ _ _))
  simp only [spacesPushforwardCompSquare, NatTrans.comp_app, Functor.map_comp]
  exact comp_comp_eq_of_comparisons hA hE
    (((smallToposMorphism_comp B S hS f' g).inv.app
      ((smallEtaleToposEquiv B S hS X').functor.obj d) ≫= hB).trans
        (Iso.inv_hom_id_app_assoc _ _ _)) hcancel hPBC

/-- The small étale base-change isomorphism is compatible, through the comparison equivalences,
with the spaces-étale base-change 2-cell. -/
theorem smallToposBaseChangeSquareIso_comparison (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    (c : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) :
    (smallToposMorphism B S hS g).inverseImage.map
          ((smallToposMorphism_comparison B S hS f).hom.app c) ≫
        (smallToposMorphism_inverseImage_comparison B S hS g).hom.app
          (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj c) ≫
        (smallEtaleToposEquiv B S hS Y').functor.map
          ((spacesToposBaseChangeSquare B S hS i f' f g sq).app c) =
      (smallToposBaseChangeSquareIso B S hS i f' f g sq hg).hom.app
          ((smallEtaleToposEquiv B S hS X).functor.obj c) ≫
        (smallToposMorphism B S hS f').pushforward.map
          ((smallToposMorphism_inverseImage_comparison B S hS i).hom.app c) ≫
        (smallToposMorphism_comparison B S hS f').hom.app
          (((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).inverseImage.obj c) := by
  rw [smallToposBaseChangeSquareIso, Functor.preimageIso_whiskeringLeft_hom_app]
  exact congrArg (fun t => t.app c)
    (smallToposBaseChangeBigIso_hom_comp B S hS i f' f g sq hg).symm

/-- Restricting the adjunction of the morphism of small étale topoi back along the comparison
equivalences returns the adjunction of the spaces-étale morphism of topoi. -/
theorem smallToposMorphism_restrict_adj {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) :
    (smallToposMorphism B S hS h).adj.restrictFullyFaithful
        (smallEtaleToposEquiv B S hS V).fullyFaithfulFunctor
        (smallEtaleToposEquiv B S hS U).fullyFaithfulFunctor
        (smallToposMorphism_inverseImage_comparison B S hS h)
        (smallToposMorphism_comparison B S hS h) =
      ((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).adj :=
  MorphismOfTopoi.transport_restrict_adj _ _ _

/-! ### The base-change 2-cell on the small étale topoi -/

/-- For a cartesian square with étale bottom arrow, the mate of the direct-image comparison of the
square is the base-change isomorphism of the small étale topoi. -/
theorem mateEquiv_smallToposBaseChangeSquareIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    mateEquiv (smallToposMorphism B S hS i).adj (smallToposMorphism B S hS g).adj
        (smallToposBaseChangeSquareIso B S hS i f' f g sq hg).hom =
      (smallToposPushforwardBaseChange B S hS f g f' i sq.w).hom := by
  have key := mateEquiv_restrictFullyFaithful_app
    (iC := (smallEtaleToposEquiv B S hS X).functor)
    (iD := (smallEtaleToposEquiv B S hS X').functor)
    (iE := (smallEtaleToposEquiv B S hS Y).functor)
    (iF := (smallEtaleToposEquiv B S hS Y').functor)
    (smallEtaleToposEquiv B S hS X).fullyFaithfulFunctor
    (smallEtaleToposEquiv B S hS X').fullyFaithfulFunctor
    (smallEtaleToposEquiv B S hS Y).fullyFaithfulFunctor
    (smallEtaleToposEquiv B S hS Y').fullyFaithfulFunctor
    (smallToposMorphism B S hS i).adj (smallToposMorphism B S hS g).adj
    (smallToposMorphism_inverseImage_comparison B S hS i)
    (smallToposMorphism_comparison B S hS i)
    (smallToposMorphism_inverseImage_comparison B S hS g)
    (smallToposMorphism_comparison B S hS g)
    (smallToposMorphism_comparison B S hS f) (smallToposMorphism_comparison B S hS f')
    (spacesToposBaseChangeSquare B S hS i f' f g sq)
    (smallToposBaseChangeSquareIso B S hS i f' f g sq hg).hom
    (smallToposBaseChangeSquareIso_comparison B S hS i f' f g sq hg)
  rw [smallToposMorphism_restrict_adj, smallToposMorphism_restrict_adj] at key
  have hms : mateEquiv ((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).adj
        ((spacesBaseChange_isMorphismOfSites B S hS g).morphismOfTopoi).adj
        (spacesToposBaseChangeSquare B S hS i f' f g sq) =
      spacesPushforwardCompSquare B S hS i f' f g sq.w :=
    (mateEquiv _ _).apply_symm_apply _
  refine ((Functor.whiskeringLeft _ _ _).obj
    (smallEtaleToposEquiv B S hS X').functor).map_injective (NatTrans.ext (funext fun d => ?_))
  have e := congrArg (fun t : (((spacesBaseChange B S hS i).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X') ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⟶
        ((spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') ⋙
        (spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y'))) =>
      (smallToposMorphism B S hS f).pushforward.map
          ((smallToposMorphism_comparison B S hS i).hom.app d) ≫
        (smallToposMorphism_comparison B S hS f).hom.app
          (((spacesBaseChange B S hS i).functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X')).obj d) ≫
        (smallEtaleToposEquiv B S hS Y).functor.map (t.app d)) hms
  have hfin := (key d).symm.trans (e.trans
    (smallToposPushforwardBaseChange_comparison B S hS i f' f g sq d))
  exact (Iso.cancel_iso_hom_right _ _
    ((smallToposMorphism B S hS g).pushforward.mapIso
        (Iso.app (smallToposMorphism_comparison B S hS f') d) ≪≫
      Iso.app (smallToposMorphism_comparison B S hS g)
        (((spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X')).obj d))).mp hfin

/-- The base-change 2-cell of a cartesian square with étale bottom arrow is the base-change
isomorphism of the small étale topoi. -/
theorem properBaseChangeMap_eq_smallToposBaseChangeSquareIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    properBaseChangeMap B S hS f g f' i sq =
      (smallToposBaseChangeSquareIso B S hS i f' f g sq hg).hom :=
  (Equiv.symm_apply_eq _).mpr
    (mateEquiv_smallToposBaseChangeSquareIso B S hS i f' f g sq hg).symm

/-- For a cartesian square of algebraic spaces whose bottom arrow `g` is étale, the base-change
2-cell `f_{small,*} ∘ g_{small}^{-1} ⟶ i_{small}^{-1} ∘ f'_{small,*}` is an isomorphism. -/
@[stacks 03LR "part (1), invertibility of the canonical base-change 2-cell"]
theorem isIso_properBaseChangeMap (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) :
    IsIso (properBaseChangeMap B S hS f g f' i sq) := by
  rw [properBaseChangeMap_eq_smallToposBaseChangeSquareIso B S hS i f' f g sq hg]
  infer_instance

end AlgebraicGeometry.Space

end
