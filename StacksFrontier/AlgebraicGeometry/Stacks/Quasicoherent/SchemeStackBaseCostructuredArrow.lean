module

public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism

/-!
# Arrows into an object of the stack of the base

The algebraic stack of the base `S` of a big fppf site is the slice of the site over its final
object `S`, and the structure morphism `𝒳 ⟶ S` of an algebraic stack is the structure functor of
`𝒳` followed by the inverse `E⁻¹` of the iterated-slice equivalence
(`AlgebraicGeometry.Stack.structureMorphism`). A morphism `E⁻¹(Z) ⟶ y` in the stack of the base is
the same as a morphism `Z ⟶ y.left` in the site (`AlgebraicGeometry.Stack.baseSliceHomEquiv`).
Consequently, for any functor `P : 𝒯 ⥤ (Sch/S)`, a terminal object of
`CostructuredArrow P y.left` gives a terminal object of `CostructuredArrow (P ⋙ E⁻¹) y`
(`AlgebraicGeometry.Stack.isTerminalBaseSliceCostructuredArrow`).

## Main definitions

* `AlgebraicGeometry.Stack.baseSliceHom` and `AlgebraicGeometry.Stack.baseSliceHomEquiv`.
* `AlgebraicGeometry.Stack.baseSliceCostructuredArrow`: the transported arrow.
* `AlgebraicGeometry.Stack.isTerminalBaseSliceCostructuredArrow`: its terminality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inverse of the iterated-slice equivalence of the base: the functor identifying the site
with the stack of the base. -/
abbrev baseSliceInverse :
    BigFppfOver B S hS ⥤ Over (Over.mk (𝟙 (B.obj hS))) :=
  (Over.iteratedSliceEquiv (Over.mk (𝟙 (B.obj hS)))).inverse

/-- **A morphism `Z ⟶ y.left` of the site, read as a morphism `E⁻¹(Z) ⟶ y` of the stack of the
base.** -/
def baseSliceHom {Z : BigFppfOver B S hS} (y : Over (Over.mk (𝟙 (B.obj hS))))
    (h : Z ⟶ y.left) : baseSliceInverse.obj Z ⟶ y :=
  Over.homMk (Over.homMk h.left ((Over.w h).trans (Category.comp_id _).symm))
    (Over.mkIdTerminal.hom_ext _ _)

/-- **A morphism `E⁻¹(Z) ⟶ y` of the stack of the base, read as a morphism `Z ⟶ y.left` of the
site.** -/
def baseSliceUnhom {Z : BigFppfOver B S hS} (y : Over (Over.mk (𝟙 (B.obj hS))))
    (φ : baseSliceInverse.obj Z ⟶ y) : Z ⟶ y.left :=
  Over.homMk φ.left.left ((Over.w φ.left).trans (Category.comp_id _))

@[simp]
theorem baseSliceHom_left_left {Z : BigFppfOver B S hS} (y : Over (Over.mk (𝟙 (B.obj hS))))
    (h : Z ⟶ y.left) : (baseSliceHom y h).left.left = h.left :=
  rfl

@[simp]
theorem baseSliceUnhom_left {Z : BigFppfOver B S hS} (y : Over (Over.mk (𝟙 (B.obj hS))))
    (φ : baseSliceInverse.obj Z ⟶ y) : (baseSliceUnhom y φ).left = φ.left.left :=
  rfl

/-- Two morphisms into an object of the stack of the base agree when their underlying morphisms
of schemes agree. -/
theorem baseSlice_hom_ext {y y' : Over (Over.mk (𝟙 (B.obj hS)))} (φ φ' : y ⟶ y')
    (h : φ.left.left = φ'.left.left) : φ = φ' :=
  Over.OverMorphism.ext (Over.OverMorphism.ext h)

@[simp]
theorem baseSliceUnhom_baseSliceHom {Z : BigFppfOver B S hS}
    (y : Over (Over.mk (𝟙 (B.obj hS)))) (h : Z ⟶ y.left) :
    baseSliceUnhom y (baseSliceHom y h) = h :=
  Over.OverMorphism.ext rfl

@[simp]
theorem baseSliceHom_baseSliceUnhom {Z : BigFppfOver B S hS}
    (y : Over (Over.mk (𝟙 (B.obj hS)))) (φ : baseSliceInverse.obj Z ⟶ y) :
    baseSliceHom y (baseSliceUnhom y φ) = φ :=
  baseSlice_hom_ext _ _ rfl

/-- **Morphisms `E⁻¹(Z) ⟶ y` are morphisms `Z ⟶ y.left`.** -/
def baseSliceHomEquiv (Z : BigFppfOver B S hS) (y : Over (Over.mk (𝟙 (B.obj hS)))) :
    (Z ⟶ y.left) ≃ (baseSliceInverse.obj Z ⟶ y) where
  toFun := baseSliceHom y
  invFun := baseSliceUnhom y
  left_inv := baseSliceUnhom_baseSliceHom y
  right_inv := baseSliceHom_baseSliceUnhom y

/-- `baseSliceHom` is natural in the source. -/
theorem baseSliceInverse_map_comp_baseSliceHom {Z Z' : BigFppfOver B S hS} (k : Z' ⟶ Z)
    (y : Over (Over.mk (𝟙 (B.obj hS)))) (h : Z ⟶ y.left) :
    baseSliceInverse.map k ≫ baseSliceHom y h = baseSliceHom y (k ≫ h) :=
  baseSlice_hom_ext _ _ rfl

/-- `baseSliceHom` is natural in the target. -/
theorem baseSliceHom_comp {Z : BigFppfOver B S hS} {y y' : Over (Over.mk (𝟙 (B.obj hS)))}
    (h : Z ⟶ y.left) (g : y ⟶ y') :
    baseSliceHom y h ≫ g = baseSliceHom y' (h ≫ g.left) :=
  baseSlice_hom_ext _ _ rfl

variable {𝒯 : Type*} [Category* 𝒯] (P : 𝒯 ⥤ BigFppfOver B S hS)
  (y : Over (Over.mk (𝟙 (B.obj hS))))

/-- An arrow `P(a) ⟶ y.left` of the site, read as an object of
`CostructuredArrow (P ⋙ E⁻¹) y`. -/
abbrev baseSliceCostructuredArrow (X : CostructuredArrow P y.left) :
    CostructuredArrow (P ⋙ baseSliceInverse) y :=
  CostructuredArrow.mk (Y := X.left) (baseSliceHom y X.hom)

/-- An object of `CostructuredArrow (P ⋙ E⁻¹) y`, read as an object of
`CostructuredArrow P y.left`. -/
abbrev baseSliceCostructuredArrowUnmk (X : CostructuredArrow (P ⋙ baseSliceInverse) y) :
    CostructuredArrow P y.left :=
  CostructuredArrow.mk (Y := X.left) (baseSliceUnhom y X.hom)

variable {P y}

/-- The morphism into the transported terminal object. -/
def baseSliceFromTerminal {t : CostructuredArrow P y.left} (ht : IsTerminal t)
    (X : CostructuredArrow (P ⋙ baseSliceInverse) y) :
    X ⟶ baseSliceCostructuredArrow P y t :=
  CostructuredArrow.homMk (ht.from (baseSliceCostructuredArrowUnmk P y X)).left (by
    have hw := CostructuredArrow.w (ht.from (baseSliceCostructuredArrowUnmk P y X))
    dsimp at hw ⊢
    rw [baseSliceInverse_map_comp_baseSliceHom, hw, baseSliceHom_baseSliceUnhom])

/-- **Terminality transports to the stack of the base.** -/
def isTerminalBaseSliceCostructuredArrow {t : CostructuredArrow P y.left} (ht : IsTerminal t) :
    IsTerminal (baseSliceCostructuredArrow P y t) :=
  IsTerminal.ofUniqueHom (baseSliceFromTerminal ht) fun X g => by
    refine CostructuredArrow.hom_ext _ _ ?_
    have hw := CostructuredArrow.w g
    dsimp at hw
    rw [baseSliceInverse_map_comp_baseSliceHom] at hw
    have hw' : P.map g.left ≫ t.hom = baseSliceUnhom y X.hom := by
      rw [← hw, baseSliceUnhom_baseSliceHom]
    have key := ht.hom_ext (CostructuredArrow.homMk (S := P) (T := y.left)
        (f := baseSliceCostructuredArrowUnmk P y X) (f' := t) g.left hw')
        (ht.from (baseSliceCostructuredArrowUnmk P y X))
    have key' := congrArg CommaMorphism.left key
    exact key'

/-- The morphism into the transported terminal object has, as its component, the morphism into
the terminal object of `CostructuredArrow P y.left`. -/
theorem isTerminalBaseSliceCostructuredArrow_from_left {t : CostructuredArrow P y.left}
    (ht : IsTerminal t) (X : CostructuredArrow (P ⋙ baseSliceInverse) y) :
    ((isTerminalBaseSliceCostructuredArrow ht).from X).left =
      (ht.from (baseSliceCostructuredArrowUnmk P y X)).left :=
  rfl

end AlgebraicGeometry.Stack

end
