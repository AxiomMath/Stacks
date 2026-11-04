module

public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolution

/-!
# The inverse image of the standard resolution

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `a : A ⟶ B` a homomorphism of sheaves of
commutative rings on `D`. The isomorphisms `CategoryTheory.Sheaf.forgetAlgebraSheafInverseImageIso`
and `CategoryTheory.Sheaf.freeAlgebraSheafInverseImageIso` form the commuting square of the two
free–forgetful adjunctions and the two inverse images, and
`CategoryTheory.Sheaf.standardResolutionComonadInverseImageIso` is the comparison of the two
free–forgetful comonads which that square induces. This file carries that comparison through the
counit, the comultiplication, the iterates and the simplicial structure, and so identifies the
inverse image of the standard resolution of `a` with the standard resolution of `f⁻¹a`.

## Main definitions

* `CategoryTheory.Functor.iterateCompIsoObj` reads the iterated comparison of commuting
  endofunctors at an object of the source whose image is presented as a given object of the
  target.
* `CategoryTheory.SimplicialObject.isoCompOfFacesAndDegeneracies` assembles degreewise
  isomorphisms out of a simplicial object pushed along a functor.
* `CategoryTheory.Sheaf.standardResolutionInverseImageTermIso` is the comparison in simplicial
  degree `n`.
* `CategoryTheory.Sheaf.standardResolutionInverseImageIso` is the comparison
  `f⁻¹P_• ≅ P_•(f⁻¹a)` of the standard resolutions.

## Main results

* `CategoryTheory.Sheaf.standardResolutionComonadInverseImageIso_counit` and
  `CategoryTheory.Sheaf.standardResolutionComonadInverseImageIso_comul`: the comonad comparison
  commutes with the counits and with the comultiplications.
* `CategoryTheory.Sheaf.standardResolutionInverseImageTermIso_delta` and
  `CategoryTheory.Sheaf.standardResolutionInverseImageTermIso_sigma`: the degreewise comparison
  commutes with the faces and the degeneracies of the two standard resolutions.
* `CategoryTheory.Sheaf.standardResolutionInverseImageIso_hom_app_comp_augmentation`: the
  comparison is compatible with the augmentations in every degree, so it is an isomorphism of
  augmented simplicial sheaves of algebras.

## Implementation notes

Every reference here to the comparisons this file builds on
(`CategoryTheory.Sheaf.forgetAlgebraSheafInverseImageIso`,
`CategoryTheory.Sheaf.freeAlgebraSheafInverseImageIso`,
`CategoryTheory.Sheaf.standardResolutionComonadInverseImageIso` and their lemmas), and to the
declarations of this file, carries an explicit universe list. This is not decoration. Those
declarations take a morphism of topoi between `Sheaf J (Type (max u v w))` and
`Sheaf K (Type (max u' v' w'))`, so the section universes `w` and `w'` occur only inside a `max`;
supplying such a declaration as an argument without naming its universes leaves the elaborator
with `max u v ?w =?= max u v w`, which it cannot solve and instead postpones into an unbounded
`isDefEq` on the concrete sheaf functors. This is a universe-unification problem, not a reduction
blowup, and naming the universes removes it.

For the same reason the two assembly steps are routed through abstract-type wrappers rather than
applied directly: `SimplicialObject.isoCompOfFacesAndDegeneracies` restates
`SimplicialObject.isoOfFacesAndDegeneracies` in the whiskered spelling, and
`Functor.iterateCompIsoObj` restates `Functor.iterateCompIso` with the image object presented as
a named object of the target. Both are proved at abstract types, where the identifications are
reflexivity, so that instantiating them at the sheaf categories is a syntactic match and needs no
reduction. Applying the original lemmas directly asks the elaborator to identify
`(P_• ⋙ f⁻¹).obj ⦋n⦌` with `f⁻¹(P_n)` and `f⁻¹(Under.mk a)` with `Under.mk (f⁻¹a)` underneath the
concrete inverse image of sheaves of rings, which does not terminate.

### No `@[stacks 08SV]`

Tag 08SV asserts `f⁻¹L_{B/A} = L_{f⁻¹B/f⁻¹A}` for the cotangent complexes of sheaves of rings.
This file proves the algebra half of that assertion: the comparison of the standard resolutions
themselves, compatibly with faces, degeneracies and augmentations. The module half is that the
inverse image of sheaves of modules transposes derivations, i.e. that `Der_A(P, f_*M)` is
`Der_{f⁻¹A}(f⁻¹P, M)`; that transposition turns the comparison of standard resolutions into a
comparison of the base-changed sheaves of differentials `Ω_{P_•/A} ⊗_{P_•} B`, and hence of
`CategoryTheory.Sheaf.cotangentComplex`. The module half is not proved here, so nothing in this
file carries the tag.

The two sites, their morphism universes and the two universes of sections all vary
independently, as in `CategoryTheory.Sheaf.cotangentComplex`.

## References

* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV)
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

attribute [local implicit_reducible] CategoryTheory.Under.post

namespace CategoryTheory

universe t₁ s₁ t₂ s₂

section IterateTransport

variable {C : Type t₁} [Category.{s₁} C] {D : Type t₂} [Category.{s₂} D]
  {G : C ⥤ C} {G' : D ⥤ D} {H : C ⥤ D}

/-- The `n`-fold iterated comparison of commuting endofunctors, read at an object `X` of the
source whose image `H.obj X` is presented as a given object `Y` of the target. -/
noncomputable def Functor.iterateCompIsoObj (e : G ⋙ H ≅ H ⋙ G') (n : ℕ) {X : C} {Y : D}
    (h : H.obj X = Y) : H.obj ((G.iterate n).obj X) ≅ (G'.iterate n).obj Y :=
  (Functor.iterateCompIso e n).app X ≪≫ eqToIso (congrArg (G'.iterate n).obj h)

/-- At the first iterate the transported comparison still commutes with the given counits. -/
lemma Functor.iterateCompIsoObj_one_counit (e : G ⋙ H ≅ H ⋙ G') (ε : G ⟶ 𝟭 C) (ε' : G' ⟶ 𝟭 D)
    (hε : ∀ X, e.hom.app X ≫ ε'.app (H.obj X) = H.map (ε.app X)) {X : C} {Y : D}
    (h : H.obj X = Y) :
    (Functor.iterateCompIsoObj e 1 h).hom ≫ ε'.app Y = H.map (ε.app X) ≫ eqToHom h := by
  subst h
  simpa [Functor.iterateCompIsoObj] using Functor.iterateCompIso_one_counit e ε ε' hε X

/-- The transported iterated comparison commutes with Godement's face maps. -/
lemma Functor.iterateCompIsoObj_godementFace (e : G ⋙ H ≅ H ⋙ G') (ε : G ⟶ 𝟭 C) (ε' : G' ⟶ 𝟭 D)
    (hε : ∀ X, e.hom.app X ≫ ε'.app (H.obj X) = H.map (ε.app X))
    (n : ℕ) (j : Fin (n + 1)) {X : C} {Y : D} (h : H.obj X = Y) :
    H.map ((Godement.face ε n j).app X) ≫ (Functor.iterateCompIsoObj e n h).hom =
      (Functor.iterateCompIsoObj e (n + 1) h).hom ≫ (Godement.face ε' n j).app Y := by
  subst h
  simpa [Functor.iterateCompIsoObj] using
    Functor.iterateCompIso_godementFace e ε ε' hε n j X

/-- The transported iterated comparison commutes with Godement's degeneracy maps. -/
lemma Functor.iterateCompIsoObj_godementDegeneracy (e : G ⋙ H ≅ H ⋙ G') (δ : G ⟶ G ⋙ G)
    (δ' : G' ⟶ G' ⋙ G')
    (hδ : ∀ X, H.map (δ.app X) ≫ e.hom.app (G.obj X) ≫ G'.map (e.hom.app X) =
      e.hom.app X ≫ δ'.app (H.obj X))
    (n : ℕ) (j : Fin (n + 1)) {X : C} {Y : D} (h : H.obj X = Y) :
    H.map ((Godement.degeneracy δ n j).app X) ≫
        (Functor.iterateCompIsoObj e (n + 2) h).hom =
      (Functor.iterateCompIsoObj e (n + 1) h).hom ≫ (Godement.degeneracy δ' n j).app Y := by
  subst h
  simpa [Functor.iterateCompIsoObj] using
    Functor.iterateCompIso_godementDegeneracy e δ δ' hδ n j X

/-- The transported comparison of the first iterates carries the counit presentation of one
augmentation to the counit presentation of the other. -/
lemma Functor.transportObjIso_hom_comp_counit (e : G ⋙ H ≅ H ⋙ G') (ε : G ⟶ 𝟭 C) (ε' : G' ⟶ 𝟭 D)
    (hε : ∀ Z, e.hom.app Z ≫ ε'.app (H.obj Z) = H.map (ε.app Z))
    {X₁ : C} {Y₁ : D} {X : C} {Y : D}
    (p : X₁ = (G.iterate 1).obj X) (q : Y₁ = (G'.iterate 1).obj Y) (h : H.obj X = Y)
    {m : X₁ ⟶ X} {k : Y₁ ⟶ Y} {c : H.obj X ⟶ Y}
    (hm : m = eqToHom p ≫ ε.app X) (hk : k = eqToHom q ≫ ε'.app Y) (hc : c = eqToHom h) :
    (Functor.transportObjIso H p q (Functor.iterateCompIsoObj e 1 h)).hom ≫ k =
      H.map m ≫ c := by
  subst h p q hm hk hc
  simpa [Functor.transportObjIso] using
    Functor.iterateCompIsoObj_one_counit e ε ε' hε (X := X) (Y := H.obj X) rfl

end IterateTransport

section SimplicialTransport

variable {C : Type t₁} [Category.{s₁} C] {D : Type t₂} [Category.{s₂} D]

/-- Degreewise isomorphisms from a simplicial object pushed along a functor to another simplicial
object, commuting with every face and every degeneracy map, assemble into an isomorphism of
simplicial objects. This is `SimplicialObject.isoOfFacesAndDegeneracies` in the whiskered
spelling, stated here at abstract types so that instantiating it needs no reduction. -/
noncomputable def SimplicialObject.isoCompOfFacesAndDegeneracies (H : C ⥤ D)
    (X : SimplicialObject C) (Y : SimplicialObject D)
    (e : ∀ n, H.obj (X.obj (op ⦋n⦌)) ≅ Y.obj (op ⦋n⦌))
    (hδ : ∀ n (j : Fin (n + 2)), H.map (X.δ j) ≫ (e n).hom = (e (n + 1)).hom ≫ Y.δ j)
    (hσ : ∀ n (j : Fin (n + 1)), H.map (X.σ j) ≫ (e (n + 1)).hom = (e n).hom ≫ Y.σ j) :
    X ⋙ H ≅ Y :=
  SimplicialObject.isoOfFacesAndDegeneracies (X := X ⋙ H) (Y := Y) e hδ hσ

/-- The components of `SimplicialObject.isoCompOfFacesAndDegeneracies` are the given
degreewise isomorphisms. -/
lemma SimplicialObject.isoCompOfFacesAndDegeneracies_hom_app (H : C ⥤ D)
    (X : SimplicialObject C) (Y : SimplicialObject D)
    (e : ∀ n, H.obj (X.obj (op ⦋n⦌)) ≅ Y.obj (op ⦋n⦌))
    (hδ : ∀ n (j : Fin (n + 2)), H.map (X.δ j) ≫ (e n).hom = (e (n + 1)).hom ≫ Y.δ j)
    (hσ : ∀ n (j : Fin (n + 1)), H.map (X.σ j) ≫ (e (n + 1)).hom = (e n).hom ≫ Y.σ j)
    (n : ℕ) :
    (SimplicialObject.isoCompOfFacesAndDegeneracies H X Y e hδ hσ).hom.app (op ⦋n⦌) =
      (e n).hom :=
  rfl

end SimplicialTransport

end CategoryTheory

namespace CategoryTheory.Sheaf

universe u v w u' v' w'

section Comparison

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  (A : Sheaf K CommRingCat.{max u' v' w'})

/-- The comparison of the two free–forgetful comonads commutes with their counits. -/
lemma standardResolutionComonadInverseImageIso_counit (X : Under A) :
    (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A).hom.app X ≫
        (standardResolutionComonad.{v, u, w} J (f.inverseImageRing.obj A)).ε.app
          ((Under.post (X := A) f.inverseImageRing).obj X) =
      (Under.post (X := A) f.inverseImageRing).map
        ((standardResolutionComonad.{v', u', w'} K A).ε.app X) :=
  Adjunction.comonadSquareIso_counit
    (freeAlgebraSheafAdjunction.{v', u', w'} K A)
    (freeAlgebraSheafAdjunction.{v, u, w} J (f.inverseImageRing.obj A))
    (freeAlgebraSheafInverseImageIso.{u, v, w, u', v', w'} J K f A)
    (forgetAlgebraSheafInverseImageIso.{u, v, w, u', v', w'} J K f A)
    (freeAlgebraSheafInverseImageIso_unit.{u, v, w, u', v', w'} J K f A) X

/-- The comparison of the two free–forgetful comonads commutes with their
comultiplications. -/
lemma standardResolutionComonadInverseImageIso_comul (X : Under A) :
    (Under.post (X := A) f.inverseImageRing).map
          ((standardResolutionComonad.{v', u', w'} K A).δ.app X) ≫
        (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A).hom.app
          ((standardResolutionComonad.{v', u', w'} K A : Under A ⥤ Under A).obj X) ≫
        (standardResolutionComonad.{v, u, w} J (f.inverseImageRing.obj A) :
            Under (f.inverseImageRing.obj A) ⥤ Under (f.inverseImageRing.obj A)).map
          ((standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A).hom.app X) =
      (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A).hom.app X ≫
        (standardResolutionComonad.{v, u, w} J (f.inverseImageRing.obj A)).δ.app
          ((Under.post (X := A) f.inverseImageRing).obj X) :=
  Adjunction.comonadSquareIso_comul
    (freeAlgebraSheafAdjunction.{v', u', w'} K A)
    (freeAlgebraSheafAdjunction.{v, u, w} J (f.inverseImageRing.obj A))
    (freeAlgebraSheafInverseImageIso.{u, v, w, u', v', w'} J K f A)
    (forgetAlgebraSheafInverseImageIso.{u, v, w, u', v', w'} J K f A)
    (freeAlgebraSheafInverseImageIso_unit.{u, v, w, u', v', w'} J K f A) X

end Comparison

section Resolution

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ B)

/-- The inverse image of the degree-`n` term of the standard resolution of `a` is the degree-`n`
term of the standard resolution of `f⁻¹a`. -/
@[implicit_reducible]
noncomputable def standardResolutionInverseImageTermIso (n : ℕ) :
    (Under.post (X := A) f.inverseImageRing).obj
        ((standardResolution.{v', u', w'} K a).left.obj (op ⦋n⦌)) ≅
      (standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left.obj (op ⦋n⦌) :=
  Functor.transportObjIso (Under.post (X := A) f.inverseImageRing)
    (standardResolution_obj.{v', u', w'} K a n)
    (standardResolution_obj.{v, u, w} J (f.inverseImageRing.map a) n)
    (Functor.iterateCompIsoObj
      (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A) (n + 1) rfl)

/-- The termwise comparison commutes with the face maps. -/
lemma standardResolutionInverseImageTermIso_delta (n : ℕ) (j : Fin (n + 2)) :
    (Under.post (X := A) f.inverseImageRing).map
          ((standardResolution.{v', u', w'} K a).left.δ j) ≫
        (standardResolutionInverseImageTermIso.{u, v, w, u', v', w'} J K f a n).hom =
      (standardResolutionInverseImageTermIso.{u, v, w, u', v', w'} J K f a (n + 1)).hom ≫
        (standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left.δ j :=
  Functor.transportObjIso_naturality (Under.post (X := A) f.inverseImageRing)
    (standardResolution_obj.{v', u', w'} K a (n + 1))
    (standardResolution_obj.{v', u', w'} K a n)
    (standardResolution_obj.{v, u, w} J (f.inverseImageRing.map a) (n + 1))
    (standardResolution_obj.{v, u, w} J (f.inverseImageRing.map a) n)
    (Functor.iterateCompIsoObj
      (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A) (n + 2) rfl)
    (Functor.iterateCompIsoObj
      (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A) (n + 1) rfl)
    (standardResolution_delta.{u', v', w'} K a n j)
    (standardResolution_delta.{u, v, w} J (f.inverseImageRing.map a) n j)
    (Functor.iterateCompIsoObj_godementFace
      (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A)
      (standardResolutionComonad.{v', u', w'} K A).ε
      (standardResolutionComonad.{v, u, w} J (f.inverseImageRing.obj A)).ε
      (standardResolutionComonadInverseImageIso_counit.{u, v, w, u', v', w'} J K f A)
      (n + 1) j rfl)

/-- The termwise comparison commutes with the degeneracy maps. -/
lemma standardResolutionInverseImageTermIso_sigma (n : ℕ) (j : Fin (n + 1)) :
    (Under.post (X := A) f.inverseImageRing).map
          ((standardResolution.{v', u', w'} K a).left.σ j) ≫
        (standardResolutionInverseImageTermIso.{u, v, w, u', v', w'} J K f a (n + 1)).hom =
      (standardResolutionInverseImageTermIso.{u, v, w, u', v', w'} J K f a n).hom ≫
        (standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left.σ j :=
  Functor.transportObjIso_naturality (Under.post (X := A) f.inverseImageRing)
    (standardResolution_obj.{v', u', w'} K a n)
    (standardResolution_obj.{v', u', w'} K a (n + 1))
    (standardResolution_obj.{v, u, w} J (f.inverseImageRing.map a) n)
    (standardResolution_obj.{v, u, w} J (f.inverseImageRing.map a) (n + 1))
    (Functor.iterateCompIsoObj
      (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A) (n + 1) rfl)
    (Functor.iterateCompIsoObj
      (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A) (n + 2) rfl)
    (standardResolution_sigma.{u', v', w'} K a n j)
    (standardResolution_sigma.{u, v, w} J (f.inverseImageRing.map a) n j)
    (Functor.iterateCompIsoObj_godementDegeneracy
      (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A)
      (standardResolutionComonad.{v', u', w'} K A).δ
      (standardResolutionComonad.{v, u, w} J (f.inverseImageRing.obj A)).δ
      (standardResolutionComonadInverseImageIso_comul.{u, v, w, u', v', w'} J K f A)
      n j rfl)

/-- **The simplicial comparison of Stacks 08SV.** The inverse image of the standard resolution of
`a : A ⟶ B` is the standard resolution of `f⁻¹a`. -/
noncomputable def standardResolutionInverseImageIso :
    (standardResolution.{v', u', w'} K a).left ⋙ Under.post (X := A) f.inverseImageRing ≅
      (standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left :=
  SimplicialObject.isoCompOfFacesAndDegeneracies
    (Under.post (X := A) f.inverseImageRing)
    (standardResolution.{v', u', w'} K a).left
    (standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left
    (standardResolutionInverseImageTermIso.{u, v, w, u', v', w'} J K f a)
    (standardResolutionInverseImageTermIso_delta.{u, v, w, u', v', w'} J K f a)
    (standardResolutionInverseImageTermIso_sigma.{u, v, w, u', v', w'} J K f a)

/-- The components of the simplicial comparison are the termwise comparisons. -/
lemma standardResolutionInverseImageIso_hom_app (n : ℕ) :
    (standardResolutionInverseImageIso.{u, v, w, u', v', w'} J K f a).hom.app (op ⦋n⦌) =
      (standardResolutionInverseImageTermIso.{u, v, w, u', v', w'} J K f a n).hom :=
  rfl

/-- In degree zero the termwise comparison carries the augmentation of the standard resolution of
`f⁻¹a` to the inverse image of the augmentation of the standard resolution of `a`. -/
lemma standardResolutionInverseImageTermIso_augmentation_zero :
    (standardResolutionInverseImageTermIso.{u, v, w, u', v', w'} J K f a 0).hom ≫
        (standardResolution.{v, u, w} J (f.inverseImageRing.map a)).hom.app (op ⦋0⦌) =
      (Under.post (X := A) f.inverseImageRing).map
          ((standardResolution.{v', u', w'} K a).hom.app (op ⦋0⦌)) ≫ 𝟙 _ :=
  Functor.transportObjIso_hom_comp_counit
    (standardResolutionComonadInverseImageIso.{u, v, w, u', v', w'} J K f A)
    (standardResolutionComonad.{v', u', w'} K A).ε
    (standardResolutionComonad.{v, u, w} J (f.inverseImageRing.obj A)).ε
    (standardResolutionComonadInverseImageIso_counit.{u, v, w, u', v', w'} J K f A)
    (standardResolution_obj.{v', u', w'} K a 0)
    (standardResolution_obj.{v, u, w} J (f.inverseImageRing.map a) 0) rfl
    (standardResolution_augmentation_app_zero.{u', v', w'} K a)
    (standardResolution_augmentation_app_zero.{u, v, w} J (f.inverseImageRing.map a)) rfl

/-- **The augmented simplicial comparison of Stacks 08SV.** The simplicial comparison of the
standard resolutions is compatible with their augmentations in every degree. -/
lemma standardResolutionInverseImageIso_hom_app_comp_augmentation (n : ℕ) :
    (standardResolutionInverseImageIso.{u, v, w, u', v', w'} J K f a).hom.app (op ⦋n⦌) ≫
        (standardResolution.{v, u, w} J (f.inverseImageRing.map a)).hom.app (op ⦋n⦌) =
      (Under.post (X := A) f.inverseImageRing).map
        ((standardResolution.{v', u', w'} K a).hom.app (op ⦋n⦌)) := by
  refine (SimplicialObject.hom_comp_toConst_of_zero
    (SimplicialObject.mapToConst (Under.post (X := A) f.inverseImageRing)
      (standardResolution.{v', u', w'} K a).hom)
    (standardResolution.{v, u, w} J (f.inverseImageRing.map a)).hom
    (standardResolutionInverseImageIso.{u, v, w, u', v', w'} J K f a) (𝟙 _) ?_ n).trans
      (Category.comp_id _)
  rw [standardResolutionInverseImageIso_hom_app.{u, v, w, u', v', w'}]
  exact standardResolutionInverseImageTermIso_augmentation_zero.{u, v, w, u', v', w'} J K f a

end Resolution

end CategoryTheory.Sheaf

end
