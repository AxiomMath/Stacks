module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic

/-!
# Étale maps out of a filtered colimit, and descent along a pushout square

An étale algebra over a filtered colimit of rings is the base change of an étale algebra over one
of the stages: in a pushout square
```
  D j ---> T'
   |        |
   v        v
  colim D -> T
```
the left vertical map is a colimit leg and the top map is étale. This is item (9) of Stacks
Lemma 00U2, and it is the step which lets a faithfully flat étale cover of the colimit of the
ind-étale construction be pushed back to a finite stage.

Alongside it, two facts about such a square: faithful flatness of the left vertical map descends
from the right vertical map, and a section of the top map produces a retraction of the right
vertical map.

Finally, ind-étaleness in the `Under (CommRingCat.of A)` formulation used by the Stacks statements
is identified with ind-étaleness in the `CommAlgCat A` formulation of the filtered-colimit API.

## Main results

* `exists_isPushout_etale` (now in `StacksFrontier.RingTheory.Etale.FilteredColimit.Basic`)
* `AlgebraicGeometry.ProEtale.faithfullyFlat_descends_pushout`
* `AlgebraicGeometry.ProEtale.faithfullyFlat_of_isPushout`
* `AlgebraicGeometry.ProEtale.exists_retraction_of_isPushout`
* `AlgebraicGeometry.ProEtale.ind_etale_iff_algebra_ind`

## References

* [Stacks Project, Tag 00U2](https://stacks.math.columbia.edu/tag/00U2)
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- Faithful flatness descends along a faithfully flat base change: in a pushout square of
commutative rings with `R → S` and `S → U` faithfully flat, `R → T` is faithfully flat. -/
lemma faithfullyFlat_descends_pushout
    (R S T U : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra S U] [Algebra T U] [Algebra R U]
    [IsScalarTower R S U] [IsScalarTower R T U]
    (hp : Algebra.IsPushout R S T U)
    (hRS : (algebraMap R S).FaithfullyFlat)
    (hSU : (algebraMap S U).FaithfullyFlat) :
    (algebraMap R T).FaithfullyFlat := by
  have : Module.FaithfullyFlat R S := (RingHom.faithfullyFlat_algebraMap_iff).mp hRS
  have : Module.FaithfullyFlat S U := (RingHom.faithfullyFlat_algebraMap_iff).mp hSU
  have hST : Module.Flat S (S ⊗[R] T) :=
    Module.Flat.of_linearEquiv (hp.equiv R S T U).toLinearEquiv
  have hT : Module.Flat R T := Module.Flat.of_flat_tensorProduct R T S
  refine (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective
    (f := algebraMap R T)).mpr ⟨?_, ?_⟩
  · exact (RingHom.flat_algebraMap_iff).mpr hT
  · have hRU : (algebraMap R U).FaithfullyFlat := by
      rw [IsScalarTower.algebraMap_eq R S U]
      exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hRS hSU
    have hs := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective
      (f := algebraMap R U)).mp hRU |>.2
    intro p
    obtain ⟨q, hq⟩ := hs p
    refine ⟨PrimeSpectrum.comap (algebraMap T U) q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq]
    exact hq

/-- `faithfullyFlat_descends_pushout` for a pushout square in `CommRingCat`: if `f` and the map
`p` parallel to it are faithfully flat, then so is `g`. -/
lemma faithfullyFlat_of_isPushout {X Y Z W : CommRingCat.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (p : Y ⟶ W) (q : Z ⟶ W)
    (h : IsPushout f g p q) (hf : f.hom.FaithfullyFlat)
    (hp : p.hom.FaithfullyFlat) : g.hom.FaithfullyFlat := by
  algebraize [f.hom, g.hom, p.hom, q.hom]
  let : Algebra X W := (p.hom.comp f.hom).toAlgebra
  let : IsScalarTower X Y W := .of_algebraMap_eq' rfl
  let : IsScalarTower X Z W := .of_algebraMap_eq' (by
    have hw := congrArg CommRingCat.Hom.hom h.w
    show p.hom.comp f.hom = q.hom.comp g.hom
    simpa only [CommRingCat.hom_comp] using hw)
  exact faithfullyFlat_descends_pushout X Y Z W
    (CommRingCat.isPushout_iff_isPushout.mp h) hf hp

/-- In a pushout square, a map `φ : Z ⟶ Y` splitting the triangle over `f` produces a retraction
of `p : Y ⟶ W`. -/
lemma exists_retraction_of_isPushout {X Y Z W : CommRingCat.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (p : Y ⟶ W) (q : Z ⟶ W)
    (h : IsPushout f g p q) (φ : Z ⟶ Y) (hφ : g ≫ φ = f) :
    ∃ s : W ⟶ Y, p ≫ s = 𝟙 Y := by
  have hw : f ≫ 𝟙 Y = g ≫ φ := by simp [hφ]
  exact ⟨h.desc (𝟙 Y) φ hw, by simp⟩

/-- Ind-étaleness of `A → C` as a property of the object `Under.mk (algebraMap A C)` of
`Under (CommRingCat.of A)` agrees with ind-étaleness of `CommAlgCat.of A C` for the object
property of étale `A`-algebras. -/
lemma ind_etale_iff_algebra_ind {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] :
    ObjectProperty.ind.{u}
      (fun D : Under (CommRingCat.of A) ↦ D.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A C))) ↔
      (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A C) := by
  show (CommRingCat.etale.underObj).ind.{u}
      (Under.mk (CommRingCat.ofHom (algebraMap A C))) ↔ _
  rw [← MorphismProperty.ind_iff_ind_underMk]
  exact (CommAlgCat.ind_etale_iff_ind_algebraMap (R := A) (Λ := C)).symm

end AlgebraicGeometry.ProEtale

end
