module

public import StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreBoundary

/-!
# The lifts of an object of a 2-fibre product are the 2-fibre product of the lifts

Let `P : 𝒳 ⟶ 𝒴` and `Q : 𝒵 ⟶ 𝒴` be `1`-morphisms of categories fibred in groupoids over the
big fppf site of a scheme `S` and let `w = (x, z, φ)` be an object of `𝒲 = 𝒳 ×_𝒴 𝒵` over
`Spec A`.  A lift of `w` to `Spec A[M]` is, by the very construction of the `2`-fibre product,
the same thing as a lift `s` of `x`, a lift `t` of `z` and an isomorphism `P s ≅ Q t` of `𝒴`
which is vertical and compatible with `φ` and the two structure arrows; and a morphism of
lifts of `w` is the same thing as a pair of morphisms of lifts of `x` and of `z` making the
comparison square commute.

`Deformation.Artin.twoFibreLiftGlue` builds a lift of `w` out of the data, and
`Deformation.Artin.twoFibreLiftHom` builds a morphism of lifts out of a compatible pair, both
with the equations identifying their components; those equations all hold by `rfl`.

The one identification that is *not* formal is `Deformation.Artin.twoFibreTrivComparison_eq`,
which says that the comparison isomorphism carried by the *chosen* trivial deformation of `w` is
the composite of the comparison isomorphisms of the trivial deformations of `x`, of `z` and of
`y = P x`.  Both sides are morphisms of lifts of `y` out of the trivial deformation of `y`, and
both become the retraction of that trivial deformation after composing with the arrow down to
`y` carried by the chosen trivial deformation of `w`; since that arrow is strongly cartesian,
they agree.  Equivalently, the chosen trivial deformation of `w` *is* the boundary deformation
at the identity automorphism.

## Main definitions

* `Deformation.Artin.twoFibreLiftGlueObject`, `Deformation.Artin.twoFibreLiftGlueArrow`,
  `Deformation.Artin.twoFibreLiftGlue`: the lift of `w` glued from a lift of `x`, a lift of
  `z` and a comparison isomorphism.
* `Deformation.Artin.twoFibreLiftHomArrow`, `Deformation.Artin.twoFibreLiftHom`: the morphism
  of lifts of `w` built from a compatible pair of morphisms of lifts.
* `Deformation.Artin.twoFibreCompP`, `Deformation.Artin.twoFibreCompQ`,
  `Deformation.Artin.twoFibreCompTr`, `Deformation.Artin.twoFibreCompFst`,
  `Deformation.Artin.twoFibreCompSnd`: the five comparison arrows of the trivial
  deformations.

## Main results

* `Deformation.Artin.twoFibreLiftIso_isHomLift`: the comparison isomorphism of a lift of `w`
  is vertical over `Spec A[M]`.
* `Deformation.Artin.twoFibreLiftGlue_fst`, `Deformation.Artin.twoFibreLiftGlue_snd`: the two
  components of a glued lift are the two lifts it was glued from, on the nose.
* `Deformation.Artin.twoFibreLiftHom_fst`, `Deformation.Artin.twoFibreLiftHom_snd`: the two
  components of a glued morphism of lifts are the two morphisms it was glued from, on the
  nose.
* `Deformation.Artin.twoFibreTrivComparison_eq`: the comparison isomorphism of the chosen
  trivial deformation of `w`, read through the comparison isomorphisms of the components.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0DNN](https://stacks.math.columbia.edu/tag/0DNN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

/-! ### Composites of vertical arrows -/

section Vertical
open Functor
universe u₁ v₁' u₂ v₂'

variable {C : Type u₁} [Category.{v₁'} C] {X : Type u₂} [Category.{v₂'} X]

/-- The composite of two vertical arrows is vertical. -/
public theorem isHomLift_comp_vertical (p : X ⥤ C) (R : C) {a b c : X} {φ : a ⟶ b} {ψ : b ⟶ c}
    (hφ : p.IsHomLift (𝟙 R) φ) (hψ : p.IsHomLift (𝟙 R) ψ) : p.IsHomLift (𝟙 R) (φ ≫ ψ) := by
  have := hφ
  have := hψ
  infer_instance

/-- Two arrows into the source of a strongly cartesian arrow that lie over one and the same
base arrow and agree after composing with it are equal. -/
public theorem eq_of_comp_isStronglyCartesian (p : X ⥤ C) {R S T : C} (f : R ⟶ S) {a b : X}
    (φ : a ⟶ b) (hφ : p.IsStronglyCartesian f φ) (g : T ⟶ R) {c : X} (ψ ψ' : c ⟶ a)
    (hψ : p.IsHomLift g ψ) (hψ' : p.IsHomLift g ψ') (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  have := hφ
  have := hψ
  have := hψ'
  exact IsStronglyCartesian.ext p f φ g h

/-- An arrow over `f` followed by a vertical arrow lies over `f`. -/
public theorem isHomLift_comp_vertical_right (p : X ⥤ C) {R S : C} (f : R ⟶ S) (T : C)
    {a b c : X} {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : p.IsHomLift f φ)
    (hψ : p.IsHomLift (𝟙 T) ψ) : p.IsHomLift f (φ ≫ ψ) := by
  have := hφ
  have := hψ
  exact IsHomLift.comp_lift_id_right' p f φ T ψ

end Vertical

section TwoFibreLiftGroupoid
open Functor CategoryTheory.TwoFibreProductOver
universe u v₁ w₁ v₂ w₂ v₃ w₃

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒵 : Type v₂} [Category.{w₂} 𝒵]
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  {p𝒳 : 𝒳 ⥤ BigFppfOver B S hS} {p𝒵 : 𝒵 ⥤ BigFppfOver B S hS}
  {p𝒴 : 𝒴 ⥤ BigFppfOver B S hS} {P : 𝒳 ⥤ 𝒴} {Q : 𝒵 ⥤ 𝒴}
  (hP : P ⋙ p𝒴 = p𝒳) (hQ : Q ⋙ p𝒴 = p𝒵)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒵 : p𝒵.IsFiberedInGroupoids)
  (h𝒴 : p𝒴.IsFiberedInGroupoids)
  (w : TwoFibreProductOver p𝒳 p𝒵 p𝒴 P Q)
  (hw : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).obj w = algebraOver A B S hS toS hA)

/-- The lifts of `w` over the trivial square-zero extension `A[M]`. -/
public abbrev TwoFibreLift (M : SiteModule A B) :=
  (Under.post (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)).Fiber
    (Under.mk (eqToHom hw ≫ squareZeroArrow A B S hS toS hA M) :
      Under ((TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).obj w))

/-- The lifts of the `𝒳`-component `x` of `w` over `A[M]`. -/
public abbrev TwoFibreLiftFst (M : SiteModule A B) :=
  (Under.post p𝒳).Fiber (Under.mk (eqToHom (twoFibreFstOver A B S hS toS hA w hw) ≫
    squareZeroArrow A B S hS toS hA M) : Under (p𝒳.obj w.x))

/-- The lifts of the `𝒵`-component `z` of `w` over `A[M]`. -/
public abbrev TwoFibreLiftSnd (M : SiteModule A B) :=
  (Under.post p𝒵).Fiber (Under.mk (eqToHom (twoFibreSndOver A B S hS toS hA w hw) ≫
    squareZeroArrow A B S hS toS hA M) : Under (p𝒵.obj w.y))

/-- The base of a lift of `w` is `Spec A[M]`. -/
public theorem twoFibreLift_base (M : SiteModule A B)
    (d : TwoFibreLift A B S hS toS hA w hw M) :
    (d.1.right).base = squareZeroOver A B S hS toS M :=
  underFiber_right_obj (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) hw
    (squareZeroArrow A B S hS toS hA M) d

include hP hQ in
/-- The comparison isomorphism of a lift of `w` is vertical over `Spec A[M]`. -/
public theorem twoFibreLiftIso_isHomLift (M : SiteModule A B)
    (d : TwoFibreLift A B S hS toS hA w hw M) :
    p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) (d.1.right).iso.hom := by
  have := (d.1.right).vertical
  refine IsHomLift.of_fac' p𝒴 (𝟙 _) (d.1.right).iso.hom ?_ ?_ ?_
  · exact (Functor.congr_obj hP (d.1.right).x).trans
      ((d.1.right).hx.trans (twoFibreLift_base A B S hS toS hA w hw M d))
  · exact (Functor.congr_obj hQ (d.1.right).y).trans
      ((d.1.right).hy.trans (twoFibreLift_base A B S hS toS hA w hw M d))
  · rw [IsHomLift.fac' p𝒴 (𝟙 (d.1.right).base) (d.1.right).iso.hom]
    simp

/-! ### Gluing a lift of `w` -/

/-- **The lift of `w` glued from a lift of `x`, a lift of `z` and a comparison
isomorphism**, as an object of the `2`-fibre product. -/
public def twoFibreLiftGlueObject (M : SiteModule A B)
    (s : TwoFibreLiftFst A B S hS toS hA w hw M) (t : TwoFibreLiftSnd A B S hS toS hA w hw M)
    (ψ : P.obj (s.1.right) ≅ Q.obj (t.1.right))
    (hψ : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) ψ.hom) :
    TwoFibreProductOver p𝒳 p𝒵 p𝒴 P Q where
  base := squareZeroOver A B S hS toS M
  x := s.1.right
  y := t.1.right
  hx := underFiber_right_obj p𝒳 (twoFibreFstOver A B S hS toS hA w hw)
    (squareZeroArrow A B S hS toS hA M) s
  hy := underFiber_right_obj p𝒵 (twoFibreSndOver A B S hS toS hA w hw)
    (squareZeroArrow A B S hS toS hA M) t
  iso := ψ
  vertical := hψ

/-- The structure arrow of a glued lift of `w`: the two structure arrows of the lifts it was
glued from. -/
public def twoFibreLiftGlueArrow (M : SiteModule A B)
    (s : TwoFibreLiftFst A B S hS toS hA w hw M) (t : TwoFibreLiftSnd A B S hS toS hA w hw M)
    (ψ : P.obj (s.1.right) ≅ Q.obj (t.1.right))
    (hψ : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) ψ.hom)
    (hsq : P.map s.1.hom ≫ ψ.hom = w.iso.hom ≫ Q.map t.1.hom) :
    w ⟶ twoFibreLiftGlueObject A B S hS toS hA w hw M s t ψ hψ where
  hbase := eqToHom (twoFibreBaseEq A B S hS toS hA w hw) ≫
    squareZeroArrow A B S hS toS hA M
  a := s.1.hom
  b := t.1.hom
  ha := by
    change p𝒳.IsHomLift (eqToHom (twoFibreBaseEq A B S hS toS hA w hw) ≫
      squareZeroArrow A B S hS toS hA M) s.1.hom
    rw [IsHomLift.lift_eqToHom_comp_iff]
    exact underFiber_isHomLift p𝒳 (twoFibreFstOver A B S hS toS hA w hw)
      (squareZeroArrow A B S hS toS hA M) s
  hb := by
    change p𝒵.IsHomLift (eqToHom (twoFibreBaseEq A B S hS toS hA w hw) ≫
      squareZeroArrow A B S hS toS hA M) t.1.hom
    rw [IsHomLift.lift_eqToHom_comp_iff]
    exact underFiber_isHomLift p𝒵 (twoFibreSndOver A B S hS toS hA w hw)
      (squareZeroArrow A B S hS toS hA M) t
  w := hsq

include hw in
/-- The structure arrow of a glued lift lies over the square-zero immersion. -/
public theorem twoFibreLiftGlueArrow_isHomLift (M : SiteModule A B)
    (s : TwoFibreLiftFst A B S hS toS hA w hw M) (t : TwoFibreLiftSnd A B S hS toS hA w hw M)
    (ψ : P.obj (s.1.right) ≅ Q.obj (t.1.right))
    (hψ : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) ψ.hom)
    (hsq : P.map s.1.hom ≫ ψ.hom = w.iso.hom ≫ Q.map t.1.hom) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).IsHomLift
      (squareZeroArrow A B S hS toS hA M)
      (twoFibreLiftGlueArrow A B S hS toS hA w hw M s t ψ hψ hsq) := by
  refine IsHomLift.of_fac' _ (squareZeroArrow A B S hS toS hA M) _ hw rfl ?_
  change eqToHom hw ≫ squareZeroArrow A B S hS toS hA M =
    eqToHom hw ≫ squareZeroArrow A B S hS toS hA M ≫ eqToHom rfl
  simp

/-- **The lift of `w` glued from a lift of `x`, a lift of `z` and a comparison
isomorphism.** -/
public def twoFibreLiftGlue (M : SiteModule A B)
    (s : TwoFibreLiftFst A B S hS toS hA w hw M) (t : TwoFibreLiftSnd A B S hS toS hA w hw M)
    (ψ : P.obj (s.1.right) ≅ Q.obj (t.1.right))
    (hψ : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) ψ.hom)
    (hsq : P.map s.1.hom ≫ ψ.hom = w.iso.hom ≫ Q.map t.1.hom) :
    TwoFibreLift A B S hS toS hA w hw M :=
  ⟨Under.mk (twoFibreLiftGlueArrow A B S hS toS hA w hw M s t ψ hψ hsq),
    underPost_mem_fiber_of_isHomLift (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) hw
      (squareZeroArrow A B S hS toS hA M) _
      (twoFibreLiftGlueArrow_isHomLift A B S hS toS hA w hw M s t ψ hψ hsq)⟩

/-- The image under the first projection of a glued lift of `w` is the given lift of `x`. -/
@[simp]
public theorem twoFibreLiftGlue_fst (M : SiteModule A B)
    (s : TwoFibreLiftFst A B S hS toS hA w hw M) (t : TwoFibreLiftSnd A B S hS toS hA w hw M)
    (ψ : P.obj (s.1.right) ≅ Q.obj (t.1.right))
    (hψ : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) ψ.hom)
    (hsq : P.map s.1.hom ≫ ψ.hom = w.iso.hom ≫ Q.map t.1.hom) :
    (squareZeroLiftPost A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw M).obj
      (twoFibreLiftGlue A B S hS toS hA w hw M s t ψ hψ hsq) = s := rfl

/-- The image under the second projection of a glued lift of `w` is the given lift of `z`. -/
@[simp]
public theorem twoFibreLiftGlue_snd (M : SiteModule A B)
    (s : TwoFibreLiftFst A B S hS toS hA w hw M) (t : TwoFibreLiftSnd A B S hS toS hA w hw M)
    (ψ : P.obj (s.1.right) ≅ Q.obj (t.1.right))
    (hψ : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) ψ.hom)
    (hsq : P.map s.1.hom ≫ ψ.hom = w.iso.hom ≫ Q.map t.1.hom) :
    (squareZeroLiftPost A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
        (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw M).obj
      (twoFibreLiftGlue A B S hS toS hA w hw M s t ψ hψ hsq) = t := rfl

/-! ### Gluing a morphism of lifts of `w` -/

/-- **The morphism of `2`-fibre products built from a compatible pair of vertical
morphisms.** -/
public def twoFibreLiftHomArrow (M : SiteModule A B)
    (d d' : TwoFibreLift A B S hS toS hA w hw M)
    (α : (d.1.right).x ⟶ (d'.1.right).x) (β : (d.1.right).y ⟶ (d'.1.right).y)
    (hα : p𝒳.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) α)
    (hβ : p𝒵.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) β)
    (hsq : P.map α ≫ (d'.1.right).iso.hom = (d.1.right).iso.hom ≫ Q.map β) :
    d.1.right ⟶ d'.1.right where
  hbase := eqToHom (twoFibreLift_base A B S hS toS hA w hw M d) ≫
    𝟙 (squareZeroOver A B S hS toS M) ≫
      eqToHom (twoFibreLift_base A B S hS toS hA w hw M d').symm
  a := α
  b := β
  ha := by
    have := hα
    infer_instance
  hb := by
    have := hβ
    infer_instance
  w := hsq

include hw in
/-- The glued morphism of `2`-fibre products is vertical. -/
public theorem twoFibreLiftHomArrow_isHomLift (M : SiteModule A B)
    (d d' : TwoFibreLift A B S hS toS hA w hw M)
    (α : (d.1.right).x ⟶ (d'.1.right).x) (β : (d.1.right).y ⟶ (d'.1.right).y)
    (hα : p𝒳.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) α)
    (hβ : p𝒵.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) β)
    (hsq : P.map α ≫ (d'.1.right).iso.hom = (d.1.right).iso.hom ≫ Q.map β) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).IsHomLift
      (𝟙 (squareZeroOver A B S hS toS M))
      (twoFibreLiftHomArrow A B S hS toS hA w hw M d d' α β hα hβ hsq) :=
  IsHomLift.of_fac' _ (𝟙 (squareZeroOver A B S hS toS M)) _
    (twoFibreLift_base A B S hS toS hA w hw M d)
    (twoFibreLift_base A B S hS toS hA w hw M d') rfl

/-- **The morphism of lifts of `w` built from a compatible pair of morphisms of lifts.** -/
public def twoFibreLiftHom (M : SiteModule A B)
    (d d' : TwoFibreLift A B S hS toS hA w hw M)
    (α : (d.1.right).x ⟶ (d'.1.right).x) (β : (d.1.right).y ⟶ (d'.1.right).y)
    (hα : p𝒳.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) α)
    (hβ : p𝒵.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) β)
    (hsq : P.map α ≫ (d'.1.right).iso.hom = (d.1.right).iso.hom ≫ Q.map β)
    (hda : (d.1.hom).a ≫ α = (d'.1.hom).a) (hdb : (d.1.hom).b ≫ β = (d'.1.hom).b) : d ⟶ d' :=
  underFiberHomMk (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) hw
    (squareZeroArrow A B S hS toS hA M)
    (twoFibreLiftHomArrow A B S hS toS hA w hw M d d' α β hα hβ hsq)
    (twoFibreLiftHomArrow_isHomLift A B S hS toS hA w hw M d d' α β hα hβ hsq)
    (TwoFibreProductOver.Hom.ext' hda hdb)

/-- The first projection of a glued morphism of lifts of `w` is `α`. -/
@[simp]
public theorem twoFibreLiftHom_fst (M : SiteModule A B)
    (d d' : TwoFibreLift A B S hS toS hA w hw M)
    (α : (d.1.right).x ⟶ (d'.1.right).x) (β : (d.1.right).y ⟶ (d'.1.right).y)
    (hα : p𝒳.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) α)
    (hβ : p𝒵.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) β)
    (hsq : P.map α ≫ (d'.1.right).iso.hom = (d.1.right).iso.hom ≫ Q.map β)
    (hda : (d.1.hom).a ≫ α = (d'.1.hom).a) (hdb : (d.1.hom).b ≫ β = (d'.1.hom).b) :
    ((squareZeroLiftPost A B S hS toS hA
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw M).map
      (twoFibreLiftHom A B S hS toS hA w hw M d d' α β hα hβ hsq hda hdb)).1.right =
    α := rfl

/-- The second projection of a glued morphism of lifts of `w` is `β`. -/
@[simp]
public theorem twoFibreLiftHom_snd (M : SiteModule A B)
    (d d' : TwoFibreLift A B S hS toS hA w hw M)
    (α : (d.1.right).x ⟶ (d'.1.right).x) (β : (d.1.right).y ⟶ (d'.1.right).y)
    (hα : p𝒳.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) α)
    (hβ : p𝒵.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) β)
    (hsq : P.map α ≫ (d'.1.right).iso.hom = (d.1.right).iso.hom ≫ Q.map β)
    (hda : (d.1.hom).a ≫ α = (d'.1.hom).a) (hdb : (d.1.hom).b ≫ β = (d'.1.hom).b) :
    ((squareZeroLiftPost A B S hS toS hA
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
        (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw M).map
      (twoFibreLiftHom A B S hS toS hA w hw M d d' α β hα hβ hsq hda hdb)).1.right =
    β := rfl

/-! ### The chosen trivial deformation of `w` -/

/-- The chosen trivial deformation of `w` over `A[M]`. -/
public abbrev twoFibreTrivW (M : SiteModule A B) :=
  trivialDeformation A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) M

/-- The arrow exhibiting the chosen trivial deformation of `w` as a pullback of `w` along the
retraction `Spec A[M] ⟶ Spec A`. -/
public abbrev twoFibreRetractW (M : SiteModule A B) :=
  trivialRetract A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) M

/-- The comparison arrow between the chosen trivial deformation of `x` and the `𝒳`-component
of the chosen trivial deformation of `w`. -/
public abbrev twoFibreCompFst (M : SiteModule A B) :
    (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right ⟶
      ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).x :=
  trivialComparison A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M

/-- The comparison arrow between the chosen trivial deformation of `z` and the `𝒵`-component
of the chosen trivial deformation of `w`. -/
public abbrev twoFibreCompSnd (M : SiteModule A B) :
    (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right ⟶
      ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).y :=
  trivialComparison A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
    (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M

/-- The comparison arrow between the trivial deformation of `y = P x` and the image under `P`
of the trivial deformation of `x`. -/
public abbrev twoFibreCompP (M : SiteModule A B) :
    (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ⟶
      P.obj ((twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right) :=
  trivialComparison A B S hS toS hA p𝒳 p𝒴 P hP w.x
    (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M

/-- The comparison arrow between the trivial deformation of `Q z` and the image under `Q` of
the trivial deformation of `z`. -/
public abbrev twoFibreCompQ (M : SiteModule A B) :
    (twoFibreTrivSndImage A B S hS toS hA hQ h𝒴 w hw M).1.right ⟶
      Q.obj ((twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right) :=
  trivialComparison A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
    (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M

/-- The comparison arrow between the trivial deformations of `y = P x` and of `Q z`, across
the comparison isomorphism of `w`. -/
public abbrev twoFibreCompTr (M : SiteModule A B) :
    (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ⟶
      (twoFibreTrivSndImage A B S hS toS hA hQ h𝒴 w hw M).1.right :=
  trivialTransportComparison A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
    (twoFibreFstImageOver A B S hS toS hA hP w hw)
    (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
    (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M

/-- The retraction of the trivial deformation of `y = P x`. -/
public abbrev twoFibreRetImg (M : SiteModule A B) :
    (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ⟶ P.obj w.x :=
  trivialRetract A B S hS toS hA p𝒴 (P.obj w.x)
    (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 M

/-- The retraction of the trivial deformation of `Q z`. -/
public abbrev twoFibreRetQz (M : SiteModule A B) :
    (twoFibreTrivSndImage A B S hS toS hA hQ h𝒴 w hw M).1.right ⟶ Q.obj w.y :=
  trivialRetract A B S hS toS hA p𝒴 (Q.obj w.y)
    (twoFibreSndImageOver A B S hS toS hA hQ w hw) h𝒴 M

/-- The `𝒵`-component of the retraction of the chosen trivial deformation of `w`, read in `𝒴`
and composed with the inverse of the comparison isomorphism of `w`. -/
public abbrev twoFibreRetractImage (M : SiteModule A B) :
    Q.obj (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).y) ⟶ P.obj w.x :=
  Q.map (twoFibreRetractW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).b ≫ w.iso.inv

/-- `Deformation.Artin.twoFibreRetractImage` lies over the retraction `Spec A[M] ⟶ Spec A`. -/
public theorem twoFibreRetractImage_isHomLift (M : SiteModule A B) :
    p𝒴.IsHomLift (squareZeroRetraction A B S hS toS hA M)
      (twoFibreRetractImage A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) := by
  have hρ := trivialRetract_isHomLift A B S hS toS hA
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) M
  have hρb := lift_map_isHomLift (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
    (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq
    (squareZeroRetraction A B S hS toS hA M)
    (twoFibreLift_base A B S hS toS hA w hw M
      (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)) hw
    (twoFibreRetractW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) hρ
  have h1 := lift_map_isHomLift p𝒵 p𝒴 Q hQ (squareZeroRetraction A B S hS toS hA M)
    (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).hy.trans
      (twoFibreLift_base A B S hS toS hA w hw M
        (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)))
    (twoFibreSndOver A B S hS toS hA w hw) _ hρb
  have h2 := transportIso_inv_isHomLift A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y) w.iso
    (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw)
  exact isHomLift_comp_vertical_right p𝒴 (squareZeroRetraction A B S hS toS hA M)
    (algebraOver A B S hS toS hA) h1 h2

/-- `Deformation.Artin.twoFibreRetractImage` is strongly cartesian. -/
public theorem twoFibreRetractImage_isStronglyCartesian (M : SiteModule A B) :
    p𝒴.IsStronglyCartesian (squareZeroRetraction A B S hS toS hA M)
      (twoFibreRetractImage A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) := by
  have := twoFibreRetractImage_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M
  exact h𝒴.isStronglyCartesian_homLift _ _

/-- The `𝒳`-side composite, after composing with the arrow down to `y`, is the retraction of
the trivial deformation of `y`. -/
public theorem twoFibreTrivComparison_fst_fac (M : SiteModule A B) :
    (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M ≫
          P.map (twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) ≫
            (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom) ≫
        twoFibreRetractImage A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M =
      twoFibreRetImg A B S hS toS hA hP h𝒴 w hw M := by
  have hρw := (twoFibreRetractW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).w
  have r := reassoc_of% hρw
  have hfacFst : twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M ≫
        (twoFibreRetractW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).a =
      trivialRetract A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw) h𝒳 M :=
    trivialComparison_fac A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M
  have hfacP := trivialComparison_fac A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M
  change (_ ≫ _ ≫ _) ≫ Q.map (twoFibreRetractW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).b ≫
    w.iso.inv = _
  simp only [Category.assoc]
  rw [← r, Iso.hom_inv_id, Category.comp_id, ← P.map_comp, hfacFst, hfacP]

/-- The `𝒵`-side composite, after composing with the arrow down to `y`, is the retraction of
the trivial deformation of `y`. -/
public theorem twoFibreTrivComparison_snd_fac (M : SiteModule A B) :
    (twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M ≫
          twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M ≫
            Q.map (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)) ≫
        twoFibreRetractImage A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M =
      twoFibreRetImg A B S hS toS hA hP h𝒴 w hw M := by
  have hfacSnd : twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M ≫
      (twoFibreRetractW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).b =
      trivialRetract A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw) h𝒵 M :=
    trivialComparison_fac A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
      (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M
  have hfacQ : twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M ≫
        Q.map (trivialRetract A B S hS toS hA p𝒵 w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 M) = _ :=
    trivialComparison_fac A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
      (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M
  have hfacτ := trivialTransportComparison_fac A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
      (twoFibreFstImageOver A B S hS toS hA hP w hw)
      (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
      (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M
  have q1 := reassoc_of% (Q.map_comp
    (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
    (twoFibreRetractW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).b)
  have q2 := reassoc_of% hfacQ
  change (_ ≫ _ ≫ _) ≫ Q.map (twoFibreRetractW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).b ≫
    w.iso.inv = _
  simp only [Category.assoc]
  rw [← q1, hfacSnd, q2]
  exact hfacτ

/-- A vertical arrow out of a lift of `x` under `a` stays vertical after applying `F`. -/
private theorem map_isHomLift_of_underFiber {C X Y : Type*} [Category C] [Category X]
    [Category Y] (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p) {U V : C} {x v : X}
    (hx : p.obj x = U) (a : U ⟶ V) (t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a)))
    (hv : p.obj v = V) (c : t.1.right ⟶ v) (hc : p.IsHomLift (𝟙 V) c) :
    q.IsHomLift (𝟙 V) (F.map c) :=
  lift_map_isHomLift p q F hF _ (underFiber_right_obj p hx a t) hv c hc

/-- **The comparison isomorphism of the chosen trivial deformation of `w`.** Read through the
comparison arrows of the trivial deformations of `x`, of `z` and of `y = P x`, it is the
composite of the latter two. -/
public theorem twoFibreTrivComparison_eq (M : SiteModule A B) :
    twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M ≫
        P.map (twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) ≫
          (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom =
      twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M ≫
        twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M ≫
          Q.map (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) := by
  have hcP := trivialComparison_isHomLift A B S hS toS hA p𝒳 p𝒴 P hP w.x
    (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M
  have hcQ := trivialComparison_isHomLift A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
    (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M
  have hτ := trivialTransportComparison_isHomLift A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
    (twoFibreFstImageOver A B S hS toS hA hP w hw)
    (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
    (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M
  have hiso := twoFibreLiftIso_isHomLift A B S hS toS hA hP hQ w hw M
    (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
  have hPc := map_isHomLift_of_underFiber p𝒳 p𝒴 P hP (twoFibreFstOver A B S hS toS hA w hw)
    (squareZeroArrow A B S hS toS hA M) (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M)
    (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).hx.trans
      (twoFibreLift_base A B S hS toS hA w hw M
        (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M))) _
    (trivialComparison_isHomLift A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M)
  have hQc := map_isHomLift_of_underFiber p𝒵 p𝒴 Q hQ (twoFibreSndOver A B S hS toS hA w hw)
    (squareZeroArrow A B S hS toS hA M) (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M)
    (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).hy.trans
      (twoFibreLift_base A B S hS toS hA w hw M
        (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M))) _
    (trivialComparison_isHomLift A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
      (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M)
  refine eq_of_comp_isStronglyCartesian p𝒴 (squareZeroRetraction A B S hS toS hA M)
    (twoFibreRetractImage A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
    (twoFibreRetractImage_isStronglyCartesian A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
    (𝟙 (squareZeroOver A B S hS toS M)) _ _
    (isHomLift_comp_vertical p𝒴 (squareZeroOver A B S hS toS M) hcP
      (isHomLift_comp_vertical p𝒴 (squareZeroOver A B S hS toS M) hPc hiso))
    (isHomLift_comp_vertical p𝒴 (squareZeroOver A B S hS toS M) hτ
      (isHomLift_comp_vertical p𝒴 (squareZeroOver A B S hS toS M) hcQ hQc))
    ((twoFibreTrivComparison_fst_fac A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).trans
      (twoFibreTrivComparison_snd_fac A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).symm)

end TwoFibreLiftGroupoid

end Deformation.Artin

end
