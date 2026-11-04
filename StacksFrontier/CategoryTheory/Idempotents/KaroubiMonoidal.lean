module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The Karoubi envelope of a symmetric monoidal category

The Karoubi envelope of a monoidal category is monoidal for the tensor product of formal direct
factors: `(X, p) ⊗ (Y, q) = (X ⊗ Y, p ⊗ q)`, with unit `(𝟙_ C, 𝟙)` and with the associativity,
unit and commutativity constraints of `C` cut down by the idempotents. It is symmetric when `C`
is.

## Main definitions

* `CategoryTheory.Idempotents.Karoubi.ofComm`: a morphism of `C` which intertwines two
  idempotents, as a morphism of the formal direct factors they cut out.
* `CategoryTheory.Idempotents.Karoubi.isoOfIso`: the same for an isomorphism of `C`.

## Main results

* `CategoryTheory.Idempotents.Karoubi.monoidalCategory`,
  `CategoryTheory.Idempotents.Karoubi.braidedCategory` and
  `CategoryTheory.Idempotents.Karoubi.symmetricCategory`: the monoidal, braided and symmetric
  structures on `Karoubi C`.
* `CategoryTheory.Idempotents.Karoubi.tensorObj_X`,
  `CategoryTheory.Idempotents.Karoubi.tensorObj_p`,
  `CategoryTheory.Idempotents.Karoubi.tensorUnit_X` and
  `CategoryTheory.Idempotents.Karoubi.tensorUnit_p`: the tensor product and the unit are the
  stated ones.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category

universe v u

namespace CategoryTheory.Idempotents.Karoubi

variable {C : Type u} [Category.{v} C]

/-- A morphism `g : P.X ⟶ Q.X` of `C` intertwining the idempotents of `P` and `Q`, as a
morphism `P ⟶ Q` of formal direct factors. -/
def ofComm {P Q : Karoubi C} (g : P.X ⟶ Q.X) (h : P.p ≫ g = g ≫ Q.p) : P ⟶ Q :=
  ⟨P.p ≫ g, by simp [← h]⟩

/-- The underlying morphism of `ofComm g h` is `P.p ≫ g`. -/
theorem ofComm_f {P Q : Karoubi C} (g : P.X ⟶ Q.X) (h : P.p ≫ g = g ≫ Q.p) :
    (ofComm g h).f = P.p ≫ g :=
  rfl

/-- Composing into an `ofComm` morphism absorbs the idempotent. -/
theorem comp_ofComm_f {P Q R : Karoubi C} (k : P ⟶ Q) (g : Q.X ⟶ R.X)
    (h : Q.p ≫ g = g ≫ R.p) : (k ≫ ofComm g h).f = k.f ≫ g := by
  simp only [Karoubi.comp_f, ofComm_f, ← assoc, Karoubi.comp_p]

/-- `ofComm` depends only on the underlying morphism of `C`. -/
theorem ofComm_congr {P Q : Karoubi C} {g g' : P.X ⟶ Q.X} (h : P.p ≫ g = g ≫ Q.p)
    (h' : P.p ≫ g' = g' ≫ Q.p) (e : g = g') : ofComm g h = ofComm g' h' := by
  subst e; rfl

/-- A composite of two intertwining morphisms intertwines. -/
theorem comm_comp {P Q R : Karoubi C} {g : P.X ⟶ Q.X} {g' : Q.X ⟶ R.X}
    (h : P.p ≫ g = g ≫ Q.p) (h' : Q.p ≫ g' = g' ≫ R.p) :
    P.p ≫ (g ≫ g') = (g ≫ g') ≫ R.p := by
  rw [← assoc, h, assoc, h', assoc]

/-- `ofComm` takes a composite of intertwining morphisms to the composite. -/
theorem ofComm_comp {P Q R : Karoubi C} (g : P.X ⟶ Q.X) (h : P.p ≫ g = g ≫ Q.p)
    (g' : Q.X ⟶ R.X) (h' : Q.p ≫ g' = g' ≫ R.p) :
    ofComm g h ≫ ofComm g' h' = ofComm (g ≫ g') (comm_comp h h') := by
  apply Karoubi.hom_ext
  simp only [comp_ofComm_f, ofComm_f, assoc]

/-- `ofComm` of the identity of `P.X` is the identity of `P`. -/
theorem ofComm_id (P : Karoubi C) : ofComm (𝟙 P.X) (by simp) = 𝟙 P := by
  apply Karoubi.hom_ext
  simp [ofComm_f]

/-- An isomorphism of `C` intertwining the idempotents of `P` and `Q` induces an isomorphism
of the formal direct factors they cut out. -/
def isoOfIso {P Q : Karoubi C} (e : P.X ≅ Q.X) (h : P.p ≫ e.hom = e.hom ≫ Q.p) : P ≅ Q where
  hom := ofComm e.hom h
  inv := ofComm e.inv (by rw [Iso.comp_inv_eq, assoc, h, ← assoc, Iso.inv_hom_id, id_comp])
  hom_inv_id := by
    rw [ofComm_comp]
    exact (ofComm_congr _ (by simp) (by simp)).trans (ofComm_id _)
  inv_hom_id := by
    rw [ofComm_comp]
    exact (ofComm_congr _ (by simp) (by simp)).trans (ofComm_id _)

/-- The forward morphism of `isoOfIso e h` is `ofComm e.hom h`. -/
@[simp] theorem isoOfIso_hom {P Q : Karoubi C} (e : P.X ≅ Q.X)
    (h : P.p ≫ e.hom = e.hom ≫ Q.p) : (isoOfIso e h).hom = ofComm e.hom h :=
  rfl

/-- The inverse morphism of `isoOfIso e h` is `ofComm e.inv`. -/
@[simp] theorem isoOfIso_inv {P Q : Karoubi C} (e : P.X ≅ Q.X)
    (h : P.p ≫ e.hom = e.hom ≫ Q.p) : (isoOfIso e h).inv = ofComm e.inv
      (by rw [Iso.comp_inv_eq, assoc, h, ← assoc, Iso.inv_hom_id, id_comp]) :=
  rfl

section Monoidal

variable [MonoidalCategory C]

/-- The tensor product of formal direct factors: `(X, p) ⊗ (Y, q) = (X ⊗ Y, p ⊗ q)`, with unit
`(𝟙_ C, 𝟙)` and with the constraints of `C` cut down by the idempotents. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (Karoubi C) where
  tensorObj P Q := ⟨P.X ⊗ Q.X, P.p ⊗ₘ Q.p, by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, P.idem, Q.idem]⟩
  whiskerLeft P _ _ f := ⟨P.p ⊗ₘ f.f, by
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, P.idem, Karoubi.p_comp, Karoubi.comp_p]⟩
  whiskerRight f Q := ⟨f.f ⊗ₘ Q.p, by
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Q.idem, Karoubi.p_comp, Karoubi.comp_p]⟩
  tensorHom f g := ⟨f.f ⊗ₘ g.f, by
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Karoubi.p_comp, Karoubi.comp_p]⟩
  tensorUnit := ⟨𝟙_ C, 𝟙 _, by simp⟩
  associator P Q R := isoOfIso (α_ P.X Q.X R.X) (associator_naturality P.p Q.p R.p)
  leftUnitor P := isoOfIso (λ_ P.X)
    (by simpa only [MonoidalCategory.id_tensorHom] using leftUnitor_naturality P.p)
  rightUnitor P := isoOfIso (ρ_ P.X)
    (by simpa only [MonoidalCategory.tensorHom_id] using rightUnitor_naturality P.p)

/-- The underlying object of `P ⊗ Q` is `P.X ⊗ Q.X`. -/
@[simp] theorem tensorObj_X (P Q : Karoubi C) : (P ⊗ Q).X = P.X ⊗ Q.X := rfl

/-- The idempotent of `P ⊗ Q` is `P.p ⊗ Q.p`. -/
@[simp] theorem tensorObj_p (P Q : Karoubi C) : (P ⊗ Q).p = P.p ⊗ₘ Q.p := rfl

/-- The underlying object of the monoidal unit of `Karoubi C` is `𝟙_ C`. -/
@[simp] theorem tensorUnit_X : (𝟙_ (Karoubi C)).X = 𝟙_ C := rfl

/-- The idempotent of the monoidal unit of `Karoubi C` is the identity of `𝟙_ C`. -/
@[simp] theorem tensorUnit_p : (𝟙_ (Karoubi C)).p = 𝟙 (𝟙_ C) := rfl

/-- The underlying morphism of `f ⊗ g` is `f.f ⊗ g.f`. -/
@[simp] theorem tensorHom_f {P Q P' Q' : Karoubi C} (f : P ⟶ Q) (g : P' ⟶ Q') :
    (f ⊗ₘ g).f = f.f ⊗ₘ g.f :=
  rfl

/-- The underlying morphism of `P ◁ f` is `P.p ⊗ f.f`. -/
@[simp] theorem whiskerLeft_f (P : Karoubi C) {Q R : Karoubi C} (f : Q ⟶ R) :
    (P ◁ f).f = P.p ⊗ₘ f.f :=
  rfl

/-- The underlying morphism of `f ▷ R` is `f.f ⊗ R.p`. -/
@[simp] theorem whiskerRight_f {P Q : Karoubi C} (f : P ⟶ Q) (R : Karoubi C) :
    (f ▷ R).f = f.f ⊗ₘ R.p :=
  rfl

/-- A tensor product of intertwining morphisms intertwines. -/
theorem comm_tensor {P Q P' Q' : Karoubi C} {g : P.X ⟶ Q.X} {g' : P'.X ⟶ Q'.X}
    (h : P.p ≫ g = g ≫ Q.p) (h' : P'.p ≫ g' = g' ≫ Q'.p) :
    (P ⊗ P').p ≫ (g ⊗ₘ g') = (g ⊗ₘ g') ≫ (Q ⊗ Q').p := by
  simp only [tensorObj_p, MonoidalCategory.tensorHom_comp_tensorHom, h, h']

/-- `ofComm` takes a tensor product of intertwining morphisms to the tensor product. -/
theorem ofComm_tensor {P Q P' Q' : Karoubi C} (g : P.X ⟶ Q.X) (h : P.p ≫ g = g ≫ Q.p)
    (g' : P'.X ⟶ Q'.X) (h' : P'.p ≫ g' = g' ≫ Q'.p) :
    ofComm g h ⊗ₘ ofComm g' h' = ofComm (g ⊗ₘ g') (comm_tensor h h') := by
  apply Karoubi.hom_ext
  exact (MonoidalCategory.tensorHom_comp_tensorHom P.p P'.p g g').symm

/-- The left unit constraint of `C` intertwines the idempotents. -/
theorem comm_leftUnitor (P : Karoubi C) :
    (𝟙_ (Karoubi C) ⊗ P).p ≫ (λ_ P.X).hom = (λ_ P.X).hom ≫ P.p := by
  show (𝟙 (𝟙_ C) ⊗ₘ P.p) ≫ (λ_ P.X).hom = (λ_ P.X).hom ≫ P.p
  rw [MonoidalCategory.id_tensorHom]
  exact leftUnitor_naturality P.p

/-- The right unit constraint of `C` intertwines the idempotents. -/
theorem comm_rightUnitor (P : Karoubi C) :
    (P ⊗ 𝟙_ (Karoubi C)).p ≫ (ρ_ P.X).hom = (ρ_ P.X).hom ≫ P.p := by
  show (P.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ P.X).hom = (ρ_ P.X).hom ≫ P.p
  rw [MonoidalCategory.tensorHom_id]
  exact rightUnitor_naturality P.p

/-- The associator of `Karoubi C` is `ofComm` of the associator of `C`. -/
theorem associator_hom (P Q R : Karoubi C) :
    (α_ P Q R).hom = ofComm (α_ P.X Q.X R.X).hom (associator_naturality P.p Q.p R.p) :=
  rfl

/-- The inverse associator of `Karoubi C` is `ofComm` of the inverse associator of `C`. -/
theorem associator_inv (P Q R : Karoubi C) :
    (α_ P Q R).inv = ofComm (α_ P.X Q.X R.X).inv
      (by simp only [Iso.comp_inv_eq, assoc, tensorObj_p, associator_naturality,
        Iso.inv_hom_id_assoc]) :=
  rfl

/-- The left unitor of `Karoubi C` is `ofComm` of the left unitor of `C`. -/
theorem leftUnitor_hom (P : Karoubi C) :
    (λ_ P).hom = ofComm (λ_ P.X).hom (comm_leftUnitor P) :=
  rfl

/-- The right unitor of `Karoubi C` is `ofComm` of the right unitor of `C`. -/
theorem rightUnitor_hom (P : Karoubi C) :
    (ρ_ P).hom = ofComm (ρ_ P.X).hom (comm_rightUnitor P) :=
  rfl

/-- The Karoubi envelope of a monoidal category is monoidal, with
`(X, p) ⊗ (Y, q) = (X ⊗ Y, p ⊗ q)` and unit `(𝟙_ C, 𝟙)`. -/
instance monoidalCategory : MonoidalCategory (Karoubi C) :=
  .ofTensorHom
    (id_tensorHom_id := fun _ _ => by apply Karoubi.hom_ext; rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => by
      apply Karoubi.hom_ext
      exact MonoidalCategory.tensorHom_comp_tensorHom f₁.f f₂.f g₁.f g₂.f)
    (associator_naturality := fun f₁ f₂ f₃ => by
      apply Karoubi.hom_ext
      simp only [associator_hom, ofComm_f, Karoubi.comp_f, tensorHom_f, tensorObj_p, assoc]
      rw [← MonoidalCategory.associator_naturality f₁.f f₂.f f₃.f]
      simp only [← assoc, MonoidalCategory.tensorHom_comp_tensorHom, Karoubi.p_comp,
        Karoubi.comp_p])
    (leftUnitor_naturality := fun f => by
      apply Karoubi.hom_ext
      simp only [leftUnitor_hom, ofComm_f, Karoubi.comp_f, tensorHom_f, Karoubi.id_f,
        tensorUnit_p, tensorObj_p, assoc]
      rw [← MonoidalCategory.leftUnitor_naturality f.f, ← MonoidalCategory.id_tensorHom]
      simp only [← assoc, MonoidalCategory.tensorHom_comp_tensorHom, Karoubi.p_comp,
        Karoubi.comp_p])
    (rightUnitor_naturality := fun f => by
      apply Karoubi.hom_ext
      simp only [rightUnitor_hom, ofComm_f, Karoubi.comp_f, tensorHom_f, Karoubi.id_f,
        tensorUnit_p, tensorObj_p, assoc]
      rw [← MonoidalCategory.rightUnitor_naturality f.f, ← MonoidalCategory.tensorHom_id]
      simp only [← assoc, MonoidalCategory.tensorHom_comp_tensorHom, Karoubi.p_comp,
        Karoubi.comp_p])
    (pentagon := fun W X Y Z => by
      rw [associator_hom, associator_hom, associator_hom, associator_hom, associator_hom,
        ← ofComm_id Z, ← ofComm_id W, ofComm_tensor, ofComm_tensor, ofComm_comp, ofComm_comp,
        ofComm_comp]
      refine ofComm_congr _ _ ?_
      simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom, tensorObj_X] using
        MonoidalCategory.pentagon W.X X.X Y.X Z.X)
    (triangle := fun X Y => by
      rw [associator_hom, leftUnitor_hom, rightUnitor_hom, ← ofComm_id X, ← ofComm_id Y,
        ofComm_tensor, ofComm_tensor, ofComm_comp]
      refine ofComm_congr _ _ ?_
      simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom, tensorObj_X,
        tensorUnit_X] using MonoidalCategory.triangle X.X Y.X)

end Monoidal

section Braided

variable [MonoidalCategory C] [BraidedCategory C]

/-- The Karoubi envelope of a braided monoidal category is braided, for the commutativity
constraint of `C` cut down by the idempotents. -/
instance braidedCategory : BraidedCategory (Karoubi C) where
  braiding P Q := isoOfIso (β_ P.X Q.X) (BraidedCategory.braiding_naturality P.p Q.p)
  braiding_naturality_right P _ _ f := by
    apply Karoubi.hom_ext
    simp only [isoOfIso_hom, ofComm_f, Karoubi.comp_f, whiskerLeft_f, whiskerRight_f, tensorObj_p,
      assoc]
    rw [← BraidedCategory.braiding_naturality P.p f.f]
    simp only [← assoc, MonoidalCategory.tensorHom_comp_tensorHom, Karoubi.p_comp, Karoubi.comp_p,
      Karoubi.idem]
  braiding_naturality_left f R := by
    apply Karoubi.hom_ext
    simp only [isoOfIso_hom, ofComm_f, Karoubi.comp_f, whiskerLeft_f, whiskerRight_f, tensorObj_p,
      assoc]
    rw [← BraidedCategory.braiding_naturality f.f R.p]
    simp only [← assoc, MonoidalCategory.tensorHom_comp_tensorHom, Karoubi.p_comp, Karoubi.comp_p,
      Karoubi.idem]
  hexagon_forward P Q R := by
    simp only [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id, isoOfIso_hom,
      associator_hom]
    rw [← ofComm_id R, ← ofComm_id Q, ofComm_tensor, ofComm_tensor, ofComm_comp, ofComm_comp,
      ofComm_comp, ofComm_comp]
    refine ofComm_congr _ _ ?_
    simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom, tensorObj_X] using
      BraidedCategory.hexagon_forward P.X Q.X R.X
  hexagon_reverse P Q R := by
    simp only [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id, isoOfIso_hom,
      associator_inv]
    rw [← ofComm_id P, ← ofComm_id Q, ofComm_tensor, ofComm_tensor, ofComm_comp, ofComm_comp,
      ofComm_comp, ofComm_comp]
    refine ofComm_congr _ _ ?_
    simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom, tensorObj_X] using
      BraidedCategory.hexagon_reverse P.X Q.X R.X

/-- The braiding of `Karoubi C` is `ofComm` of the braiding of `C`. -/
theorem braiding_hom (P Q : Karoubi C) :
    (β_ P Q).hom = ofComm (β_ P.X Q.X).hom (BraidedCategory.braiding_naturality P.p Q.p) :=
  rfl

end Braided

section Symmetric

variable [MonoidalCategory C] [SymmetricCategory C]

/-- The Karoubi envelope of a symmetric monoidal category is symmetric. -/
instance symmetricCategory : SymmetricCategory (Karoubi C) where
  symmetry P Q := by
    rw [braiding_hom, braiding_hom, ofComm_comp]
    refine (ofComm_congr _ (by simp) ?_).trans (ofComm_id _)
    exact SymmetricCategory.symmetry P.X Q.X

end Symmetric

end CategoryTheory.Idempotents.Karoubi

end
