module

public import StacksFrontier.Algebra.Category.ModuleCat.PowerFunctors
public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing

/-!
# Applying a functor degreewise to a simplicial homotopy

A simplicial homotopy between morphisms of simplicial objects is a family of morphisms subject to
equations between composites of itself, the faces and the degeneracies. A functor `F : C ⥤ D`
applied degreewise therefore carries a simplicial homotopy to a simplicial homotopy, with no
hypothesis on `F`.

If moreover `F` sends zero morphisms to zero morphisms, then a simplicial contraction of `X` —
a simplicial homotopy from `0` to `𝟙 X` — is carried to a simplicial contraction of `X ⋙ F`,
and hence the alternating face map complex of `X ⋙ F` is acyclic. The symmetric and exterior
power functors of positive degree, which are neither additive nor exact, send zero morphisms to
zero morphisms.

## Main definitions

* `CategoryTheory.SimplicialObject.Homotopy.whiskerRightFunctor`: a simplicial homotopy, carried
  along by a functor applied degreewise.
* `CategoryTheory.SimplicialObject.Homotopy.nullHomotopyWhiskerRight`: a simplicial contraction,
  carried along by a functor applied degreewise which preserves zero morphisms.

## Main results

* `CategoryTheory.SimplicialObject.isZero_homology_whiskerRight_of_nullHomotopy`: if `X` is
  simplicially contractible and `F` preserves zero morphisms, the alternating face map complex of
  `X ⋙ F` has vanishing homology in every degree.
* `Stacks.ModuleCat.symPowFunctor_map_eq_zero`, `Stacks.ModuleCat.extPowFunctor_map_eq_zero`: the
  symmetric and exterior power functors of positive degree preserve zero morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe v u v' u'

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A simplicial homotopy is carried along by any functor applied degreewise: the components of
the new homotopy are the images under `F` of the components of the old one. -/
public def whiskerRightFunctor {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : Homotopy f g)
    (F : C ⥤ D) :
    Homotopy (Functor.whiskerRight f F) (Functor.whiskerRight g F) :=
  H.whiskerRight F

/-- A simplicial contraction is carried along by any functor applied degreewise that preserves
zero morphisms: if zero is simplicially homotopic to the identity of `X`, the same holds for
`X ⋙ F`. -/
public def nullHomotopyWhiskerRight [HasZeroMorphisms C] [HasZeroMorphisms D]
    {X : SimplicialObject C} (H : Homotopy (0 : X ⟶ X) (𝟙 X)) (F : C ⥤ D)
    (hF : ∀ Z W : C, F.map (0 : Z ⟶ W) = 0) :
    Homotopy (0 : X ⋙ F ⟶ X ⋙ F) (𝟙 (X ⋙ F)) :=
  (H.whiskerRightFunctor F).ofEq (by ext; simp [hF]) (Functor.whiskerRight_id' F)

end CategoryTheory.SimplicialObject.Homotopy

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- If zero is simplicially homotopic to the identity of `X` and the functor `F` preserves zero
morphisms, then the alternating face map complex of `X ⋙ F` has vanishing homology in every
degree. -/
public lemma isZero_homology_whiskerRight_of_nullHomotopy [Preadditive C] [Preadditive D]
    [CategoryWithHomology D] {X : SimplicialObject C} (H : Homotopy (0 : X ⟶ X) (𝟙 X)) (F : C ⥤ D)
    (hF : ∀ Z W : C, F.map (0 : Z ⟶ W) = 0) (n : ℕ) :
    IsZero (((alternatingFaceMapComplex D).obj (X ⋙ F)).homology n) :=
  (H.nullHomotopyWhiskerRight F hF).isZero_homology_of_nullHomotopy n

end CategoryTheory.SimplicialObject

namespace Stacks.ModuleCat

/-- The `k`-th symmetric power functor preserves zero morphisms when `k` is positive: a symmetric
power of positive degree of the zero map is zero. -/
public lemma symPowFunctor_map_eq_zero {B : Type u} [CommRing B] {k : ℕ} (hk : 0 < k)
    (M N : _root_.ModuleCat.{u} B) : (symPowFunctor B k).map (0 : M ⟶ N) = 0 := by
  exact _root_.ModuleCat.hom_ext (Stacks.ChaoticSite.symMap_zero_of_pos k hk)

/-- The `k`-th exterior power functor preserves zero morphisms when `k` is positive: an exterior
power of positive degree of the zero map is zero. -/
public lemma extPowFunctor_map_eq_zero {B : Type u} [CommRing B] {k : ℕ} (hk : 0 < k)
    (M N : _root_.ModuleCat.{u} B) : (extPowFunctor B k).map (0 : M ⟶ N) = 0 := by
  exact _root_.ModuleCat.hom_ext (Stacks.ChaoticSite.exteriorPower_map_zero_of_pos k hk)

end Stacks.ModuleCat

end
