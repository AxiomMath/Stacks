module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksCore.CategoryTheory.Subobject.Lattice
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredDifferentialObjectSpectralSequence

/-!
# Comparisons between quotients of subobjects

Several identifications of quotients `N/W` of subobjects of an object of an abelian category.

The first is the modular-lattice comparison: for subobjects `V`, `W`, `B` of `X` with `B ≤ V`, the
inclusion `V ⟶ V ⊔ W` induces
```
V/((V ⊓ W) ⊔ B) ≅ (V ⊔ W)/(B ⊔ W).
```

The remaining ones transport such a quotient along an isomorphism of the ambient object, and
identify the cokernel of `Subobject.ofLE` between two image subobjects with the cokernel of the
comparison `image.preComp` of images.

## Main definitions

* `CategoryTheory.Subobject.underlyingMapIso`: the underlying object of a subobject is unchanged by
  transporting it along an isomorphism of the ambient object.
* `CategoryTheory.Subobject.cokernelMapIso`: the induced identification of a quotient `N/W` with
  its transport.
* `CategoryTheory.Subobject.cokernelImagePreCompIso`: the cokernel of `image.preComp g f` as a
  quotient of image subobjects.

## Main results

* `CategoryTheory.Subobject.nonempty_cokernelOfLE_inf_sup_iso`: the modular-lattice comparison
  `V/((V ⊓ W) ⊔ B) ≅ (V ⊔ W)/(B ⊔ W)`.
* `CategoryTheory.Subobject.map_imageSubobject`: the transport of an image subobject along an
  isomorphism is the image subobject of the composite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Subobject

/-- **The modular comparison of quotients of subobjects.** For subobjects `V`, `W`, `B` of `X` with
`B ≤ V`, the inclusion of `V` into `V ⊔ W` identifies `V/((V ⊓ W) ⊔ B)` with `(V ⊔ W)/(B ⊔ W)`. -/
lemma nonempty_cokernelOfLE_inf_sup_iso {A : Type*} [Category* A] [Abelian A]
    {X : A} (V W B : Subobject X) (hB : B ≤ V) :
    Nonempty (cokernel (Subobject.ofLE ((V ⊓ W) ⊔ B) V (_root_.sup_le _root_.inf_le_left hB)) ≅
      cokernel (Subobject.ofLE (B ⊔ W) (V ⊔ W)
        (_root_.sup_le (hB.trans _root_.le_sup_left) _root_.le_sup_right))) := by
  let P := (V ⊓ W) ⊔ B
  let Q := V ⊔ W
  let P' := B ⊔ W
  have hP : P ≤ V := _root_.sup_le _root_.inf_le_left hB
  have hP' : P' ≤ Q := _root_.sup_le (hB.trans _root_.le_sup_left) _root_.le_sup_right
  have heq : P = V ⊓ P' := by
    dsimp [P, P']
    calc
      V ⊓ W ⊔ B = B ⊔ W ⊓ V := by ac_rfl
      _ = (B ⊔ W) ⊓ V := (_root_.sup_inf_assoc_of_le W hB).symm
      _ = V ⊓ (B ⊔ W) := _root_.inf_comm _ _
  have : Epi (𝟙 (V : A) ≫ cokernel.π (Subobject.ofLE P V hP)) := by
    rw [Category.id_comp]
    infer_instance
  have : Epi (Subobject.ofLE V Q _root_.le_sup_left ≫ cokernel.π (Subobject.ofLE P' Q hP')) :=
    Subobject.epi_ofLE_comp_cokernel_π
      (Subobject.ofLE P' Q hP') (Subobject.ofLE_arrow _)
      _root_.le_sup_left le_rfl _root_.le_sup_right
  obtain ⟨e, _⟩ := Subobject.exists_iso_cokernel_of_factors_iff
    (Subobject.ofLE P V hP) (Subobject.ofLE_arrow _)
    (Subobject.ofLE P' Q hP') (Subobject.ofLE_arrow _)
    (𝟙 (V : A)) (Subobject.ofLE V Q _root_.le_sup_left) (by
      intro T g
      simp only [Category.id_comp, Subobject.ofLE_arrow, heq]
      exact ⟨fun h ↦ ((Subobject.inf_factors _).mp h).2,
        fun h ↦ (Subobject.inf_factors _).mpr
          ⟨Subobject.factors_comp_arrow g, h⟩⟩)
  exact ⟨e⟩

/-- The cokernel of the comparison `image.preComp g f` of images, read as a quotient of image
subobjects. -/
def cokernelImagePreCompIso {A : Type*} [Category* A] [Abelian A]
    {X Y Z : A} (g : X ⟶ Y) (f : Y ⟶ Z) :
    cokernel (image.preComp g f) ≅
      cokernel (Subobject.ofLE (imageSubobject (g ≫ f)) (imageSubobject f)
        (imageSubobject_comp_le g f)) := by
  have w : Subobject.ofLE (imageSubobject (g ≫ f)) (imageSubobject f)
      (imageSubobject_comp_le g f) ≫ (imageSubobjectIso f).hom =
      (imageSubobjectIso (g ≫ f)).hom ≫ image.preComp g f := by
    rw [← cancel_mono (image.ι f)]
    simp only [Category.assoc, imageSubobject_arrow, Subobject.ofLE_arrow, image.preComp_ι]
  exact (cokernel.mapIso _ _ (imageSubobjectIso (g ≫ f)) (imageSubobjectIso f) w).symm

/-- Transporting an image subobject along an isomorphism of the ambient object gives the image
subobject of the composite. -/
theorem map_imageSubobject {C : Type*} [Category* C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (e : Y ≅ Z) :
    (Subobject.map e.hom).obj (imageSubobject f) = imageSubobject (f ≫ e.hom) := by
  rw [imageSubobject, imageSubobject, Subobject.map_mk]
  let i := (imageSubobjectIso f).symm ≪≫
    (imageSubobjectCompIso f e.hom).symm ≪≫ imageSubobjectIso (f ≫ e.hom)
  exact Subobject.mk_eq_mk_of_comm _ _ i (by simp [i, Category.assoc])

/-- An isomorphism of the ambient object does not change the underlying object of a subobject. -/
def underlyingMapIso {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) (P : Subobject X) :
    Subobject.underlying.obj P ≅
      Subobject.underlying.obj (Subobject.mapIsoToOrderIso e P) :=
  ((MonoOver.forget _ ⋙ Over.forget _).mapIso
    ((Subobject.lowerCompRepresentativeIso (MonoOver.map e.hom)).app P)).symm

/-- `underlyingMapIso` is compatible with the inclusions of the subobjects into the ambient
objects. -/
lemma underlyingMapIso_arrow {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) (P : Subobject X) :
    (underlyingMapIso e P).hom ≫ (Subobject.mapIsoToOrderIso e P).arrow = P.arrow ≫ e.hom := by
  let η := (Subobject.lowerCompRepresentativeIso (MonoOver.map e.hom)).app P
  show η.inv.hom.left ≫ (Subobject.representative.obj
      ((Subobject.mapIsoToOrderIso e P))).obj.hom =
    (Subobject.representative.obj P).obj.hom ≫ e.hom
  exact MonoOver.w η.inv

/-- `underlyingMapIso` is compatible with the inclusion of one subobject in a larger one. -/
lemma underlyingMapIso_ofLE {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) (P Q : Subobject X)
    (h : P ≤ Q) :
    (P.ofLE Q h) ≫ (underlyingMapIso e Q).hom =
      (underlyingMapIso e P).hom ≫
        (Subobject.mapIsoToOrderIso e P).ofLE (Subobject.mapIsoToOrderIso e Q)
          ((Subobject.mapIsoToOrderIso e).map_rel_iff'.2 h) := by
  let φ := Subobject.mapIsoToOrderIso e
  have h' : φ P ≤ φ Q := φ.map_rel_iff'.2 h
  show (P.ofLE Q h) ≫ (underlyingMapIso e Q).hom =
      (underlyingMapIso e P).hom ≫ (φ P).ofLE (φ Q) h'
  apply (cancel_mono (φ Q).arrow).1
  simp only [Category.assoc, Subobject.ofLE_arrow]
  rw [underlyingMapIso_arrow e Q, underlyingMapIso_arrow e P]
  simp

/-- Transporting a quotient `Q/P` of subobjects along an isomorphism of the ambient object. -/
def cokernelMapIso {C : Type*} [Category C] [Abelian C] {X Y : C} (e : X ≅ Y)
    (P Q : Subobject X) (h : P ≤ Q) :
    cokernel (P.ofLE Q h) ≅
      cokernel ((Subobject.mapIsoToOrderIso e P).ofLE (Subobject.mapIsoToOrderIso e Q)
        ((Subobject.mapIsoToOrderIso e).map_rel_iff'.2 h)) :=
  cokernel.mapIso (P.ofLE Q h)
    ((Subobject.mapIsoToOrderIso e P).ofLE (Subobject.mapIsoToOrderIso e Q)
      ((Subobject.mapIsoToOrderIso e).map_rel_iff'.2 h))
    (underlyingMapIso e P) (underlyingMapIso e Q)
    (underlyingMapIso_ofLE e P Q h)

end CategoryTheory.Subobject
