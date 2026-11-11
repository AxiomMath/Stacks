module

public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.CategoryTheory.Sites.RelocalizationMorphism
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi

/-! # Relocalizing a morphism of sheaf topoi (Stacks 04IV)

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two
(small) sites, let `G` be a sheaf on `D`, `F` a sheaf on `C` and `s : F ⟶ f⁻¹G`.  Stacks 04IV
asserts that

1. there is a morphism of topoi `f_s : Sh(C)/F ⟶ Sh(D)/G` with `j_G ∘ f_s = f ∘ j_F`;
2. `f_s = f' ∘ j_{F/f⁻¹G}`, with `f'` the morphism of Stacks 04H1 and `j_{F/f⁻¹G}` the
   relocalization morphism of Stacks 04IR;
3. `(f_s)⁻¹(H ⟶ G) = (f⁻¹H ×_{f⁻¹G, s} F ⟶ F)`;
4. for `b : G' ⟶ G`, `a : F' ⟶ F` and `s' : F' ⟶ f⁻¹G'` with `s ∘ a = f⁻¹b ∘ s'`, the square
   `j_{G'/G} ∘ f_{s'} = f_s ∘ j_{F'/F}` commutes.

`StacksFrontier/CategoryTheory/Sites/RelocalizationMorphism.lean` (Stacks 04IN) proves all of this
for an arbitrary morphism of topoi, but there the pushforward of the relocalization morphism
`j_{U/U'}` (the right adjoint of base change `Over U' ⥤ Over U`) is an input.  The one thing
that is special to sheaf topoi is that this right adjoint exists, and this file constructs it:

* in any category with pullbacks, base change along `c : U ⟶ V` is `toOver (Over.mk c)` in the
  slice `Over V` followed by the iterated-slice equivalence
  (`Over.pullbackIsoToOverCompIteratedSliceForward`), so it is a left adjoint as soon as `Over V`
  is cartesian closed (`Over.isLeftAdjoint_pullback_of_monoidalClosed`, using Mathlib's sections
  functor `Over.sections`);
* for a sheaf `V` on a small site, `Sh(C)/V` is equivalent to the topos of sheaves on the site of
  elements of `V` (Stacks 0791, `Stacks.Topos.Localized.sheafEquivalence`), and a category of
  sheaves of sets is cartesian closed, hence so is `Sh(C)/V` (`Sheaf.monoidalClosedOver`).

With that adjoint in hand, the morphism of topoi `f_s` and its four properties are the
specializations of the 04IN results, with nothing taken as data.  As in 04IN (and 04H1), the two
squares are stated as isomorphisms of inverse-image functors, where `j_F⁻¹ = toOver F` and
`j_{F'/F}⁻¹ = Over.pullback a`.

## Main results

* `CategoryTheory.Sheaf.isLeftAdjoint_overPullback`: base change `Over V ⥤ Over U` along a
  morphism `c : U ⟶ V` of sheaves has a right adjoint.
* `MorphismOfTopoi.sheafOverRelocalization`: the relocalization morphism of topoi
  `j_{F'/F} : Sh(C)/F' ⟶ Sh(C)/F` (Stacks 04IR), with constructed pushforward.
* `MorphismOfTopoi.sheafRelocalize` (Stacks 04IV): the morphism of topoi `f_s`, with
  `sheafRelocalize_eq_comp` (`f_s = f' ∘ j_{F/f⁻¹G}`), `sheafRelocalize_inverseImage_obj`
  (the formula for `(f_s)⁻¹`), `sheafRelocalizeInverseImageIso` (the first square) and
  `sheafRelocalizeCompPullbackIso` (the last square).

Tags covered: 04IV.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory CartesianMonoidalCategory

section

variable {A : Type*} [Category* A] [HasPullbacks A]

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- Base change along `c : U ⟶ V` is the product with `Over.mk c` in the slice `Over V`, read in
`Over U` through the iterated-slice equivalence `Over (Over.mk c) ≌ Over U`.  Both sides are
right adjoints of `Over.map c`, so this is uniqueness of right adjoints. -/
noncomputable def Over.pullbackIsoToOverCompIteratedSliceForward {U V : A} (c : U ⟶ V) :
    Over.pullback c ≅ toOver (Over.mk c) ⋙ (Over.mk c).iteratedSliceForward :=
  Adjunction.rightAdjointUniq (Over.mapPullbackAdj c)
    (((Over.mk c).iteratedSliceEquiv.symm.toAdjunction.comp
      (forgetAdjToOver (Over.mk c))).ofNatIsoLeft
        (eqToIso (Over.iteratedSliceBackward_forget (Over.mk c))))

/-- If the slice `Over V` is cartesian closed (for its pullback products), then base change along
any `c : U ⟶ V` has a right adjoint: `toOver (Over.mk c)` has the right adjoint
`Over.sections`, and base change is `toOver (Over.mk c)` followed by an equivalence. -/
lemma Over.isLeftAdjoint_pullback_of_monoidalClosed {U V : A} (c : U ⟶ V)
    [MonoidalClosed (Over V)] : (Over.pullback c).IsLeftAdjoint := by
  let : ChosenPullbacksAlong (curryRightUnitorHom (Over.mk c)) :=
    ChosenPullbacksAlong.ofHasPullbacksAlong _
  have : (toOver (Over.mk c) ⋙ (Over.mk c).iteratedSliceForward).IsLeftAdjoint :=
    ((toOverSectionsAdj (Over.mk c)).comp (Over.mk c).iteratedSliceEquiv.toAdjunction).isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso (Over.pullbackIsoToOverCompIteratedSliceForward c).symm

end

section

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The slice `Sh(C)/V` of the topos of sheaves of sets on a small site is cartesian closed:
it is equivalent to the topos of sheaves on the site of elements of `V` (Stacks 0791), and a
category of sheaves of sets is cartesian closed. -/
@[instance_reducible]
noncomputable def Sheaf.monoidalClosedOver (V : Sheaf J (Type u)) :
    letI := Over.cartesianMonoidalCategory V
    MonoidalClosed (Over V) :=
  haveI hS : MonoidalClosed
      (Sheaf ((CostructuredArrow.proj yoneda V.obj).restrictedTopology J) (Type u)) :=
    instMonoidalClosedSheafOfHasSheafifyOfFunctorOpposite _ _
  @cartesianClosedOfEquiv _ _ inferInstance _ _ (Over.cartesianMonoidalCategory V)
    (Stacks.Topos.Localized.sheafEquivalence V.obj J V.property) hS

/-- **Base change of sheaves has a right adjoint.**  For a morphism `c : U ⟶ V` of sheaves of
sets on a small site, base change `Over V ⥤ Over U` is a left adjoint; its right adjoint is the
pushforward `j_{U/V,*}` of the relocalization morphism of Stacks 04IR. -/
instance Sheaf.isLeftAdjoint_overPullback {U V : Sheaf J (Type u)} (c : U ⟶ V) :
    (Over.pullback c).IsLeftAdjoint :=
  letI := Over.cartesianMonoidalCategory V
  letI := Sheaf.monoidalClosedOver J V
  Over.isLeftAdjoint_pullback_of_monoidalClosed c

end

end CategoryTheory

namespace MorphismOfTopoi

open CategoryTheory Limits

universe u u'

section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- **The relocalization morphism of sheaf topoi** `j_{F'/F} : Sh(C)/F' ⟶ Sh(C)/F` attached to a
morphism of sheaves `a : F' ⟶ F` (Stacks 04IR): its inverse image is base change along `a`, and
its pushforward is the right adjoint of base change constructed in
`CategoryTheory.Sheaf.isLeftAdjoint_overPullback`. -/
noncomputable def sheafOverRelocalization {F' F : Sheaf J (Type u)} (a : F' ⟶ F) :
    MorphismOfTopoi (Over F') (Over F) :=
  overRelocalization a (Adjunction.ofIsLeftAdjoint (Over.pullback a))

/-- The inverse image of `j_{F'/F}` is base change along `a`. -/
lemma sheafOverRelocalization_inverseImage {F' F : Sheaf J (Type u)} (a : F' ⟶ F) :
    (sheafOverRelocalization a).inverseImage = Over.pullback a :=
  rfl

end

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {D : Type u'} [SmallCategory D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u')))

/-- **Stacks 04IV**, the morphism of topoi `f_s`.  Let `f : Sh(C) ⟶ Sh(D)` be a morphism of
topoi, `G` a sheaf on `D`, `F` a sheaf on `C` and `s : F ⟶ f⁻¹G`.  The morphism of topoi
`f_s : Sh(C)/F ⟶ Sh(D)/G` is
```
  f_s = f' ∘ j_{F/f⁻¹G} ,
```
the composite of the relocalization morphism `j_{F/f⁻¹G}` (Stacks 04IR,
`sheafOverRelocalization s`) with the morphism `f'` of Stacks 04H1 (`f.over G`).  Both
pushforwards are constructed: that of `f'` from `f_*`, that of `j_{F/f⁻¹G}` as the right adjoint
of base change along `s`. -/
@[stacks 04IV "the morphism of topoi f_s : Sh(C)/F ⟶ Sh(D)/G"]
noncomputable def sheafRelocalize {G : Sheaf K (Type u')} {F : Sheaf J (Type u)}
    (s : F ⟶ f.inverseImage.obj G) : MorphismOfTopoi (Over F) (Over G) :=
  f.relocalize s (Adjunction.ofIsLeftAdjoint (Over.pullback s))

/-- **Stacks 04IV**, the factorization `f_s = f' ∘ j_{F/f⁻¹G}`, where `f' = f.over G` is the
morphism of Stacks 04H1 and `j_{F/f⁻¹G} = sheafOverRelocalization s` is the relocalization
morphism of Stacks 04IR. -/
@[stacks 04IV "the factorization f_s = f' ∘ j_{F/f⁻¹G}"]
lemma sheafRelocalize_eq_comp {G : Sheaf K (Type u')} {F : Sheaf J (Type u)}
    (s : F ⟶ f.inverseImage.obj G) :
    f.sheafRelocalize s = (f.over G).comp (sheafOverRelocalization s) :=
  rfl

/-- **Stacks 04IV**, the description of `(f_s)⁻¹`: an object `φ : H ⟶ G` of `Sh(D)/G` is sent to
```
  (f⁻¹H ×_{f⁻¹φ, f⁻¹G, s} F ⟶ F) .
``` -/
@[stacks 04IV "the description of (f_s)⁻¹ as a fibre product"]
lemma sheafRelocalize_inverseImage_obj {G : Sheaf K (Type u')} {F : Sheaf J (Type u)}
    (s : F ⟶ f.inverseImage.obj G) (H : Over G) :
    (f.sheafRelocalize s).inverseImage.obj H =
      Over.mk (pullback.snd (f.inverseImage.map H.hom) s) :=
  rfl

/-- **Stacks 04IV**, commutativity of the first square `j_G ∘ f_s = f ∘ j_F`, on inverse images:
`j_F⁻¹ ∘ f⁻¹ ≅ (f_s)⁻¹ ∘ j_G⁻¹`, where `j_F⁻¹ = toOver F` and `j_G⁻¹ = toOver G`. -/
@[stacks 04IV "commutativity of the square j_G ∘ f_s = f ∘ j_F, on inverse images"]
noncomputable def sheafRelocalizeInverseImageIso {G : Sheaf K (Type u')}
    {F : Sheaf J (Type u)} (s : F ⟶ f.inverseImage.obj G) :
    f.inverseImage ⋙ toOver F ≅ toOver G ⋙ (f.sheafRelocalize s).inverseImage :=
  f.relocalizeInverseImageIso s _

/-- **Stacks 04IV**, commutativity of the last square: given `b : G' ⟶ G`, `a : F' ⟶ F` and
`s' : F' ⟶ f⁻¹G'` with `s ∘ a = f⁻¹b ∘ s'`, the square of topoi
```
  Sh(C)/F' --j_{F'/F}--> Sh(C)/F
     |f_{s'}                |f_s
  Sh(D)/G' --j_{G'/G}--> Sh(D)/G
```
commutes: the inverse images of `j_{G'/G} ∘ f_{s'}` and of `f_s ∘ j_{F'/F}` are isomorphic.
This is the formal identity `f⁻¹H ×_{f⁻¹G} F ×_F F' = f⁻¹(H ×_G G') ×_{f⁻¹G'} F'`. -/
@[stacks 04IV "commutativity of the last square j_{G'/G} ∘ f_{s'} = f_s ∘ j_{F'/F}"]
noncomputable def sheafRelocalizeCompPullbackIso {G G' : Sheaf K (Type u')} (b : G' ⟶ G)
    {F F' : Sheaf J (Type u)} (a : F' ⟶ F) (s : F ⟶ f.inverseImage.obj G)
    (s' : F' ⟶ f.inverseImage.obj G') (hs : a ≫ s = s' ≫ f.inverseImage.map b) :
    ((sheafOverRelocalization b).comp (f.sheafRelocalize s')).inverseImage ≅
      ((f.sheafRelocalize s).comp (sheafOverRelocalization a)).inverseImage :=
  f.relocalizeCompPullbackIso b a s s' hs.symm _ _

end MorphismOfTopoi
