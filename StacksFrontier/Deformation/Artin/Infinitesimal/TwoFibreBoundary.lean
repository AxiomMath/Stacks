module

public import StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreSideMaps

/-!
# The boundary map of the six-term sequence of a 2-fibre product

Let `P : 𝒳 ⟶ 𝒴` and `Q : 𝒵 ⟶ 𝒴` be `1`-morphisms of categories fibred in groupoids over the
big fppf site of a scheme `S`, let `A` be an `S`-algebra and let `w = (x, z, φ)` be an object
of the `2`-fibre product `𝒲 = 𝒳 ×_𝒴 𝒵` over `Spec A`, with `φ : P x ≅ Q z` the comparison
isomorphism.  Writing `y = P x`, the six-term sequence of Stacks 0DNN has a boundary map

`δ : Inf_y(M) ⟶ T_w(M)`

defined as follows: an element of `Inf_y(M)` is an automorphism `α`
of the trivial deformation `y'` of `y` over `A[M]` restricting to the identity on `y`, and
`δ(α)` is the deformation of `w` given by the pair of trivial deformations `x'`, `z'` of `x`
and `z` with comparison isomorphism

`P x' ⟶ y' --α--> y' ⟶ Q z'`,

the outer two arrows being the comparison isomorphisms of the trivial deformations supplied by
`Deformation.Artin.trivialComparison` and `Deformation.Artin.trivialTransportComparison`.
That this *is* a deformation of `w` — i.e. that the two structure arrows `x ⟶ x'`, `z ⟶ z'`
make the comparison square commute — is exactly the statement that `α` restricts to the
identity on `y`.

## Main definitions

* `Deformation.Artin.fiberEndRightIso`: a morphism of lifts read as an isomorphism of the
  ambient category.
* `Deformation.Artin.trivialComparisonIso`,
  `Deformation.Artin.trivialTransportComparisonIso`: the two comparison arrows of
  `Deformation.Artin.trivialComparison` and `Deformation.Artin.trivialTransportComparison`,
  as isomorphisms.
* `Deformation.Artin.boundaryIso`: the comparison isomorphism `P x' ≅ Q z'` built from `α`.
* `Deformation.Artin.boundaryObject`, `Deformation.Artin.boundaryArrow`,
  `Deformation.Artin.boundaryLift`: the deformation `δ(α)` of `w` as an object of the
  `2`-fibre product, the structure arrow `w ⟶ δ(α)`, and the pair read as a lift of `w` over
  `Spec A[M]`.
* `Deformation.Artin.boundaryClass`, `Deformation.Artin.twoFibreBoundaryMap`,
  `Deformation.Artin.boundaryLinearMap`: its isomorphism class, the boundary map
  `Inf_y(M) ⟶ T_w(M)` read through the two defining bijections, and that map packaged as an
  `A`-linear map.
* `Deformation.Artin.twoFibreInfSideMap`, `Deformation.Artin.twoFibreTangentSideMap`: the two
  `𝒵`-side maps `Inf_z(M) ⟶ Inf_y(M)` and `T_z(M) ⟶ T_y(M)` of the sequence at `w`.

## Main results

* `Deformation.Artin.isIso_of_isHomLift_id_fibered`: a vertical arrow of a category fibred in
  groupoids is invertible.
* `Deformation.Artin.underPost_mem_fiber_of_isHomLift`: an arrow out of `x` lying over an
  arrow of the base out of `p x` is a lift of `x`.
* `Deformation.Artin.boundaryIso_hom_fac`: the comparison square of `δ(α)` commutes, because
  `α` restricts to the identity on `y`.
* `Deformation.Artin.boundaryIso_naturality`, `Deformation.Artin.boundaryClass_isPullback`:
  the boundary deformation over `A[N]` is the pullback of the one over `A[M]` along a module
  map, the cartesian arrow being the pair of transition arrows of the trivial deformations.
* `Deformation.Artin.twoFibreBoundaryMap_natural`,
  `Deformation.Artin.isLinearMap_twoFibreBoundaryMap`: the boundary map is natural in `M` and
  `A`-linear.
* `Deformation.Artin.tangentMap_twoFibreBoundaryMap_fst`,
  `Deformation.Artin.tangentMap_twoFibreBoundaryMap_snd`,
  `Deformation.Artin.tangentProj_twoFibreBoundaryMap_eq_zero`: the two components of `δ(α)`
  are the trivial deformations of `x` and of `z`, so the sequence is a complex at `T_w(M)`.

## References

* [Stacks Project, Tag 0DNN](https://stacks.math.columbia.edu/tag/0DNN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

/-! ### Vertical arrows of a category fibred in groupoids -/

section Vertical
open Functor
universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]

/-- A morphism of a category fibred in groupoids lying over an identity is invertible: it is
strongly cartesian over an isomorphism. -/
public theorem isIso_of_isHomLift_id_fibered (p : X ⥤ C) (hp : p.IsFiberedInGroupoids)
    {U : C} {a b : X} (φ : a ⟶ b) (hφ : p.IsHomLift (𝟙 U) φ) : IsIso φ := by
  have := hφ
  have := hp.isStronglyCartesian_homLift (𝟙 U) φ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := 𝟙 U) φ

/-- An arrow out of `x` lying over an arrow `a` of the base out of `p x` is a lift of `x`
along `a`. -/
public theorem underPost_mem_fiber_of_isHomLift (p : X ⥤ C) {U V : C} {x x' : X}
    (hx : p.obj x = U) (a : U ⟶ V) (φ : x ⟶ x') (hφ : p.IsHomLift a φ) :
    (Under.post p).obj (Under.mk φ) = Under.mk (eqToHom hx ≫ a) := by
  have := hφ
  refine StructuredArrow.obj_ext _ _ (IsHomLift.codomain_eq p a φ) ?_
  show p.map φ ≫ eqToHom (IsHomLift.codomain_eq p a φ) = eqToHom hx ≫ a
  rw [IsHomLift.fac' p a φ]
  simp

/-- The underlying arrow of `X` of a morphism of lifts of `x` is invertible. -/
public theorem isIso_fiberEnd_right (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) {x : X}
    {U : Under (p.obj x)} {s t : (Under.post p).Fiber U} (m : s ⟶ t) : IsIso m.1.right :=
  isIso_of_isHomLift_id_fibered p hp m.1.right
    (underPost_isHomLift_right p (𝟙 U) m.1 m.2)

/-- A morphism of lifts of `x`, read as an isomorphism of `X`. -/
public def fiberEndRightIso (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) {x : X}
    {U : Under (p.obj x)} {s t : (Under.post p).Fiber U} (m : s ⟶ t) :
    s.1.right ≅ t.1.right :=
  haveI := isIso_fiberEnd_right p hp m
  asIso m.1.right

/-- The forward arrow of `fiberEndRightIso p hp m` is `m.1.right`. -/
@[simp]
public theorem fiberEndRightIso_hom (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) {x : X}
    {U : Under (p.obj x)} {s t : (Under.post p).Fiber U} (m : s ⟶ t) :
    (fiberEndRightIso p hp m).hom = m.1.right := rfl

end Vertical

/-! ### The comparison arrow of a 1-morphism as an isomorphism -/

section ComparisonIso
open Functor
universe u v₁ w₁ v₂ w₂

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v₁} [Category.{w₁} X] {Y : Type v₂} [Category.{w₂} Y]
  (p : X ⥤ BigFppfOver B S hS) (q : Y ⥤ BigFppfOver B S hS)
  (F : X ⥤ Y) (hF : F ⋙ q = p)
  (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)

/-- The comparison arrow of the two trivial deformations is invertible: it is vertical. -/
public theorem isIso_trivialComparison (M : SiteModule A B) :
    IsIso (trivialComparison A B S hS toS hA p q F hF x hx hp hq M) :=
  isIso_of_isHomLift_id_fibered q hq _
    (trivialComparison_isHomLift A B S hS toS hA p q F hF x hx hp hq M)

/-- The comparison arrow of the two trivial deformations, as an isomorphism. -/
public def trivialComparisonIso (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M).1.right ≅
      F.obj ((trivialDeformation A B S hS toS hA p x hx hp M).1.right) :=
  haveI := isIso_trivialComparison A B S hS toS hA p q F hF x hx hp hq M
  asIso (trivialComparison A B S hS toS hA p q F hF x hx hp hq M)

/-- The forward arrow of `trivialComparisonIso` is `trivialComparison`. -/
@[simp]
public theorem trivialComparisonIso_hom (M : SiteModule A B) :
    (trivialComparisonIso A B S hS toS hA p q F hF x hx hp hq M).hom =
      trivialComparison A B S hS toS hA p q F hF x hx hp hq M := rfl

/-- The comparison isomorphism is compatible with the structure arrows of the two trivial
deformations. -/
public theorem trivialComparisonIso_comp (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA q (F.obj x)
          (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M).1.hom ≫
        (trivialComparisonIso A B S hS toS hA p q F hF x hx hp hq M).hom =
      F.map (trivialDeformation A B S hS toS hA p x hx hp M).1.hom :=
  trivialComparison_comp A B S hS toS hA p q F hF x hx hp hq M

end ComparisonIso

/-! ### The transport comparison arrow as an isomorphism -/

section TransportComparisonIso
open Functor
universe u v w

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {Y : Type v} [Category.{w} Y] (p : Y ⥤ BigFppfOver B S hS) (y₁ y₂ : Y)
  (hy₁ : p.obj y₁ = algebraOver A B S hS toS hA)
  (hy₂ : p.obj y₂ = algebraOver A B S hS toS hA)
  (ι : y₁ ≅ y₂) (hι : p.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) ι.hom)
  (hp : p.IsFiberedInGroupoids)

/-- The comparison arrow across a vertical isomorphism is invertible: it is vertical. -/
public theorem isIso_trivialTransportComparison (M : SiteModule A B) :
    IsIso (trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M) :=
  isIso_of_isHomLift_id_fibered p hp _
    (trivialTransportComparison_isHomLift A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M)

/-- The comparison arrow across a vertical isomorphism, as an isomorphism. -/
public def trivialTransportComparisonIso (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA p y₁ hy₁ hp M).1.right ≅
      (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M).1.right :=
  haveI := isIso_trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M
  asIso (trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M)

/-- The forward arrow of `trivialTransportComparisonIso` is `trivialTransportComparison`. -/
@[simp]
public theorem trivialTransportComparisonIso_hom (M : SiteModule A B) :
    (trivialTransportComparisonIso A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).hom =
      trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M := rfl

/-- The comparison isomorphism across a vertical isomorphism is compatible with the structure
arrows of the two trivial deformations. -/
public theorem trivialTransportComparisonIso_comp (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA p y₁ hy₁ hp M).1.hom ≫
        (trivialTransportComparisonIso A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).hom =
      ι.hom ≫ (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M).1.hom :=
  trivialTransportComparison_comp A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M

end TransportComparisonIso

/-! ### The boundary map -/

section Boundary
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

include hw in
/-- The base of an object of the `2`-fibre product lying over `Spec A` is `Spec A`. -/
public theorem twoFibreBaseEq : w.base = algebraOver A B S hS toS hA := hw

include hw in
/-- The `𝒳`-component of an object of the `2`-fibre product over `Spec A` lies over
`Spec A`. -/
public theorem twoFibreFstOver : p𝒳.obj w.x = algebraOver A B S hS toS hA := w.hx.trans hw

include hw in
/-- The `𝒵`-component of an object of the `2`-fibre product over `Spec A` lies over
`Spec A`. -/
public theorem twoFibreSndOver : p𝒵.obj w.y = algebraOver A B S hS toS hA := w.hy.trans hw

include hP hw in
/-- The image in `𝒴` of the `𝒳`-component lies over `Spec A`. -/
public theorem twoFibreFstImageOver : p𝒴.obj (P.obj w.x) = algebraOver A B S hS toS hA :=
  oneMorphism_obj_eq A B S hS toS hA p𝒳 p𝒴 P hP w.x (twoFibreFstOver A B S hS toS hA w hw)

include hQ hw in
/-- The image in `𝒴` of the `𝒵`-component lies over `Spec A`. -/
public theorem twoFibreSndImageOver : p𝒴.obj (Q.obj w.y) = algebraOver A B S hS toS hA :=
  oneMorphism_obj_eq A B S hS toS hA p𝒵 p𝒴 Q hQ w.y (twoFibreSndOver A B S hS toS hA w hw)

include hP hQ hw in
/-- The comparison isomorphism of an object of the `2`-fibre product over `Spec A` is
vertical over `Spec A`. -/
public theorem twoFibreIso_isHomLift :
    p𝒴.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) w.iso.hom := by
  have := w.vertical
  refine IsHomLift.of_fac' p𝒴 (𝟙 _) w.iso.hom
    (twoFibreFstImageOver A B S hS toS hA hP w hw)
    (twoFibreSndImageOver A B S hS toS hA hQ w hw) ?_
  rw [IsHomLift.fac' p𝒴 (𝟙 w.base) w.iso.hom]
  simp

/-- The trivial deformation of the `𝒳`-component of `w` over `Spec A[M]`. -/
public abbrev twoFibreTrivFst (M : SiteModule A B) :=
  trivialDeformation A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw) h𝒳 M

/-- The trivial deformation of the `𝒵`-component of `w` over `Spec A[M]`. -/
public abbrev twoFibreTrivSnd (M : SiteModule A B) :=
  trivialDeformation A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw) h𝒵 M

/-- The trivial deformation of `y = P x` over `Spec A[M]`; its automorphisms over the
identity of `y` are the elements of `Inf_y(M)`. -/
public abbrev twoFibreTrivFstImage (M : SiteModule A B) :=
  trivialDeformation A B S hS toS hA p𝒴 (P.obj w.x)
    (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 M

/-- The trivial deformation of `Q z` over `Spec A[M]`. -/
public abbrev twoFibreTrivSndImage (M : SiteModule A B) :=
  trivialDeformation A B S hS toS hA p𝒴 (Q.obj w.y)
    (twoFibreSndImageOver A B S hS toS hA hQ w hw) h𝒴 M

/-- **The comparison isomorphism of the deformation `δ(α)` of `w`**: the trivial deformations
of `x` and of `z`, compared through the infinitesimal automorphism `α` of the trivial
deformation of `y = P x`. -/
public def boundaryIso (M : SiteModule A B)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) :
    P.obj ((twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right) ≅
      Q.obj ((twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right) :=
  (trivialComparisonIso A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M).symm ≪≫
    fiberEndRightIso p𝒴 h𝒴 α ≪≫
    trivialTransportComparisonIso A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
      (twoFibreFstImageOver A B S hS toS hA hP w hw)
      (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
      (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M ≪≫
    trivialComparisonIso A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
      (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M

/-- The forward arrow of `boundaryIso` is the composite of the inverse comparison arrow on
the `𝒳`-side, `α.1.right`, the transport comparison along `w.iso`, and the comparison arrow
on the `𝒵`-side. -/
@[simp]
public theorem boundaryIso_hom (M : SiteModule A B)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) :
    (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α).hom =
      (trivialComparisonIso A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M).inv ≫
        α.1.right ≫
        (trivialTransportComparisonIso A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
            (twoFibreFstImageOver A B S hS toS hA hP w hw)
            (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
            (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M).hom ≫
          (trivialComparisonIso A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
            (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M).hom := rfl

/-- **The comparison square of `δ(α)` commutes**, because `α` restricts to the identity on
`y`. -/
public theorem boundaryIso_hom_fac (M : SiteModule A B)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) :
    P.map (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom ≫
        (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α).hom =
      w.iso.hom ≫ Q.map (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom := by
  have hcP := trivialComparisonIso_comp A B S hS toS hA p𝒳 p𝒴 P hP w.x
    (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M
  have hcQ := trivialComparisonIso_comp A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
    (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M
  have hτ := trivialTransportComparisonIso_comp A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
    (twoFibreFstImageOver A B S hS toS hA hP w hw)
    (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
    (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M
  have hα := Under.w α.1
  rw [boundaryIso_hom, ← hcP, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hα,
    ← Category.assoc, hτ, Category.assoc, hcQ]

/-- **The deformation `δ(α)` of `w` over `Spec A[M]`**: the pair of trivial deformations of
`x` and of `z`, with the comparison isomorphism twisted by `α`. -/
public def boundaryObject (M : SiteModule A B)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) :
    TwoFibreProductOver p𝒳 p𝒵 p𝒴 P Q where
  base := squareZeroOver A B S hS toS M
  x := (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right
  y := (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right
  hx := underFiber_right_obj p𝒳 (twoFibreFstOver A B S hS toS hA w hw)
    (squareZeroArrow A B S hS toS hA M) (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M)
  hy := underFiber_right_obj p𝒵 (twoFibreSndOver A B S hS toS hA w hw)
    (squareZeroArrow A B S hS toS hA M) (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M)
  iso := boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α
  vertical := by
    have h1 : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
        (trivialComparisonIso A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M).hom :=
      trivialComparison_isHomLift A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M
    have h2 : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
        (trivialComparisonIso A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M).inv :=
      IsHomLift.lift_id_inv (p := p𝒴) (squareZeroOver A B S hS toS M) _
    have h3 : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) α.1.right :=
      underPost_isHomLift_right p𝒴 (𝟙 _) α.1 α.2
    have h4 : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
        (trivialTransportComparisonIso A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
          (twoFibreFstImageOver A B S hS toS hA hP w hw)
          (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
          (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M).hom :=
      trivialTransportComparison_isHomLift A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
        (twoFibreFstImageOver A B S hS toS hA hP w hw)
        (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
        (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M
    have h5 : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
        (trivialComparisonIso A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M).hom :=
      trivialComparison_isHomLift A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
        (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M
    rw [boundaryIso_hom]
    infer_instance

/-- **The structure arrow `w ⟶ δ(α)`**: the two structure arrows of the trivial deformations
of `x` and of `z`, which make the comparison square commute by
`Deformation.Artin.boundaryIso_hom_fac`. -/
public def boundaryArrow (M : SiteModule A B)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) :
    w ⟶ boundaryObject A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α where
  hbase := eqToHom (twoFibreBaseEq A B S hS toS hA w hw) ≫
    squareZeroArrow A B S hS toS hA M
  a := (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom
  b := (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom
  ha := by
    change p𝒳.IsHomLift (eqToHom (twoFibreBaseEq A B S hS toS hA w hw) ≫
      squareZeroArrow A B S hS toS hA M)
      (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom
    rw [IsHomLift.lift_eqToHom_comp_iff]
    exact underFiber_isHomLift p𝒳 (twoFibreFstOver A B S hS toS hA w hw)
      (squareZeroArrow A B S hS toS hA M) (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M)
  hb := by
    change p𝒵.IsHomLift (eqToHom (twoFibreBaseEq A B S hS toS hA w hw) ≫
      squareZeroArrow A B S hS toS hA M)
      (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom
    rw [IsHomLift.lift_eqToHom_comp_iff]
    exact underFiber_isHomLift p𝒵 (twoFibreSndOver A B S hS toS hA w hw)
      (squareZeroArrow A B S hS toS hA M) (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M)
  w := boundaryIso_hom_fac A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α

include hw in
/-- The structure arrow of `δ(α)` lies over the square-zero immersion
`Spec A ⟶ Spec A[M]`. -/
public theorem boundaryArrow_isHomLift (M : SiteModule A B)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).IsHomLift
      (squareZeroArrow A B S hS toS hA M)
      (boundaryArrow A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α) := by
  refine IsHomLift.of_fac' _ (squareZeroArrow A B S hS toS hA M) _ hw rfl ?_
  show eqToHom hw ≫ squareZeroArrow A B S hS toS hA M =
    eqToHom hw ≫ squareZeroArrow A B S hS toS hA M ≫ eqToHom rfl
  simp

/-- **The deformation `δ(α)` read as a lift of `w` over `Spec A[M]`.** -/
public def boundaryLift (M : SiteModule A B)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) :
    (Under.post (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)).Fiber
      (Under.mk (eqToHom hw ≫ squareZeroArrow A B S hS toS hA M)) :=
  ⟨Under.mk (boundaryArrow A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α),
    underPost_mem_fiber_of_isHomLift (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) hw
      (squareZeroArrow A B S hS toS hA M) _
      (boundaryArrow_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α)⟩

/-- **The isomorphism class of `δ(α)`**, an element of the tangent space of `w`. -/
public def boundaryClass (M : SiteModule A B)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) :
    squareZeroLiftClasses A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw M :=
  Quotient.mk _ (boundaryLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α)

include hw in
/-- **The comparison isomorphisms of the boundary deformations are natural in the module**:
if `β` over `A[N]` restricts to `α` over `A[M]` along the transition arrow of the trivial
deformations of `y`, then the transition arrows of the trivial deformations of `x` and of `z`
make the comparison square between `δ(β)` and `δ(α)` commute. -/
public theorem boundaryIso_naturality {M N : SiteModule A B} (f : M ⟶ N)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M)
    (β : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw N ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw N)
    (hβ : β.1.right ≫ trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f =
        trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f ≫ α.1.right) :
    P.map (trivialTransition A B S hS toS hA p𝒳 w.x
          (twoFibreFstOver A B S hS toS hA w hw) h𝒳 f) ≫
        (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α).hom =
      (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw N β).hom ≫
        Q.map (trivialTransition A B S hS toS hA p𝒵 w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 f) := by
  have hnat1 :=
    trivialComparison_naturality A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 f
  have hnat2 :=
    trivialComparison_naturality A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
      (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 f
  have hnat3 :=
    trivialTransportComparison_naturality A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
      (twoFibreFstImageOver A B S hS toS hA hP w hw)
      (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
      (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 f
  simp only [← trivialComparisonIso_hom, ← trivialTransportComparisonIso_hom] at hnat1 hnat2 hnat3
  simp only [boundaryIso_hom, Category.assoc]
  rw [Iso.eq_inv_comp, ← reassoc_of% hnat1, Iso.hom_inv_id_assoc, ← reassoc_of% hβ,
    reassoc_of% hnat3, hnat2]

include hw in
/-- **The transition map of `Inf_y` is restriction along the transition arrow of the trivial
deformations**, read as a square in `𝒴`. -/
public theorem twoFibreInfTransition_fac {M N : SiteModule A B} (f : M ⟶ N)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) :
    ((infinitesimalAutomorphismSetFunctor A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴).map f α).1.right ≫
        trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f =
      trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f ≫ α.1.right := by
  rw [infAutSetFunctor_map_eq A B S hS toS hA p𝒴 (P.obj w.x)
    (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f α]
  exact congrArg Under.Hom.right (fiberEndRestrict_fac (Under.post p𝒴)
    (underPost_isFiberedInGroupoids p𝒴 h𝒴 (P.obj w.x))
    (trivialTransitionUnder A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f)
    (trivialTransitionUnder_isHomLift A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f) α)

/-- **The transition arrow `δ(β) ⟶ δ(α)` of the boundary deformations** along a module map
`f : M ⟶ N`: the transition arrows of the trivial deformations of `x` and of `z`. -/
public def boundaryTransition {M N : SiteModule A B} (f : M ⟶ N)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M)
    (β : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw N ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw N)
    (hβ : β.1.right ≫ trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f =
        trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f ≫ α.1.right) :
    boundaryObject A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw N β ⟶
      boundaryObject A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α where
  hbase := squareZeroOverMap A B S hS toS f
  a := trivialTransition A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw) h𝒳 f
  b := trivialTransition A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw) h𝒵 f
  ha := trivialTransition_isHomLift A B S hS toS hA p𝒳 w.x
    (twoFibreFstOver A B S hS toS hA w hw) h𝒳 f
  hb := trivialTransition_isHomLift A B S hS toS hA p𝒵 w.y
    (twoFibreSndOver A B S hS toS hA w hw) h𝒵 f
  w := boundaryIso_naturality A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw f α β hβ

include hw in
/-- The transition arrow of the boundary deformations lies over the map of trivial
square-zero extensions. -/
public theorem boundaryTransition_isHomLift {M N : SiteModule A B} (f : M ⟶ N)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M)
    (β : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw N ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw N)
    (hβ : β.1.right ≫ trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f =
        trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f ≫ α.1.right) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).IsHomLift
      (squareZeroOverMap A B S hS toS f)
      (boundaryTransition A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw f α β hβ) :=
  IsHomLift.map (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
    (boundaryTransition A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw f α β hβ)

include hw in
/-- **The boundary deformation over `A[N]` is the pullback of the one over `A[M]`.**  The
cartesian arrow is the pair of transition arrows of the trivial deformations of `x` and of
`z`; it is cartesian because the `2`-fibre product is fibred in groupoids. -/
public theorem boundaryClass_isPullback {M N : SiteModule A B} (f : M ⟶ N)
    (α : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M)
    (β : twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw N ⟶
      twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw N)
    (hβ : β.1.right ≫ trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f =
        trivialTransition A B S hS toS hA p𝒴 (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴 f ≫ α.1.right) :
    IsPullbackOfSquareZeroLift A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw f
      (boundaryClass A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α)
      (boundaryClass A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw N β) := by
  refine ⟨boundaryLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M α,
    boundaryLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw N β, rfl, rfl,
    boundaryTransition A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw f α β hβ, ?_, ?_⟩
  · show (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).IsStronglyCartesian
      (squareZeroOverMap A B S hS toS f)
      (boundaryTransition A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw f α β hβ)
    let := boundaryTransition_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw f α β hβ
    exact (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP
      hQ).isStronglyCartesian_homLift _ _
  · refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · exact Under.w (trivialTransitionUnder A B S hS toS hA p𝒳 w.x
        (twoFibreFstOver A B S hS toS hA w hw) h𝒳 f)
    · exact Under.w (trivialTransitionUnder A B S hS toS hA p𝒵 w.y
        (twoFibreSndOver A B S hS toS hA w hw) h𝒵 f)

/-- **The `𝒵`-side map `Inf_z(M) ⟶ Inf_y(M)` of the six-term sequence of Stacks 0DNN**: the
map induced by `q` on infinitesimal automorphisms, followed by the identification of the
invariants of `q z` with those of `y = p x` along the comparison isomorphism of `w`. -/
@[stacks 0DNN "the map `Inf_z(M) → Inf_y(M)` of the six-term sequence -- the map of Remark \
  07YA induced by q, followed by the transport along the comparison isomorphism of w. The \
  sequence and its exactness are Deformation.Artin.twoFibre_sixTermExact."]
public def twoFibreInfSideMap
    (InfZ : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒵 w.y
      (twoFibreSndOver A B S hS toS hA w hw) h𝒵)
    (InfY' : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴)
    (M : SiteModule A B) : InfZ.functor.obj M →ₗ[A] InfY'.functor.obj M :=
  infLinearMapOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
    (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
    (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
    (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒵 h𝒴 InfZ InfY' M

/-- `twoFibreInfSideMap` sends `u` to `infFunctorMapOfOneMorphismTransport` applied to `u`. -/
@[simp]
public theorem twoFibreInfSideMap_apply
    (InfZ : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒵 w.y
      (twoFibreSndOver A B S hS toS hA w hw) h𝒵)
    (InfY' : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴)
    (M : SiteModule A B) (u : InfZ.functor.obj M) :
    twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY' M u =
      infFunctorMapOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
        (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
        (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
        (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒵 h𝒴 InfZ InfY' M u := rfl

/-- **The `𝒵`-side map `T_z(M) ⟶ T_y(M)` of the six-term sequence of Stacks 0DNN**: the map
induced by `q` on tangent spaces, followed by the identification of the invariants of `q z`
with those of `y = p x` along the comparison isomorphism of `w`. -/
@[stacks 0DNN "the map `T_z(M) → T_y(M)` of the six-term sequence -- the map of Remark 07YA \
  induced by q, followed by the transport along the comparison isomorphism of w. The \
  sequence and its exactness are Deformation.Artin.twoFibre_sixTermExact."]
public def twoFibreTangentSideMap
    (TZ : TangentFunctorData A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw))
    (TY : TangentFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw))
    (M : SiteModule A B) : TZ.functor.obj M →ₗ[A] TY.functor.obj M :=
  tangentLinearMapOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
    (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
    (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
    (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 TZ TY M

variable (InfY : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
    (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴)
  (TW : TangentFunctorData A B S hS toS hA
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw)

/-- **The boundary map `δ : Inf_y(M) ⟶ T_w(M)` of Stacks 0DNN**, read through the two
defining bijections. -/
public def twoFibreBoundaryMap (M : SiteModule A B) :
    InfY.functor.obj M → TW.functor.obj M :=
  fun α => (TW.liftEquiv M).symm
    (boundaryClass A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M α))

/-- The boundary map read back through the bijection of `TW` is the class of `δ(α)`. -/
public theorem liftEquiv_twoFibreBoundaryMap (M : SiteModule A B) (α : InfY.functor.obj M) :
    TW.liftEquiv M (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α) =
      boundaryClass A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M α) :=
  (TW.liftEquiv M).apply_symm_apply _

include hw in
/-- **The boundary map is natural in the module.** -/
public theorem twoFibreBoundaryMap_natural {M N : SiteModule A B} (f : M ⟶ N)
    (α : InfY.functor.obj M) :
    twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW N (InfY.functor.map f α) =
      TW.functor.map f (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α) := by
  apply (TW.liftEquiv N).injective
  rw [liftEquiv_twoFibreBoundaryMap]
  have h2 := boundaryClass_isPullback A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw f
    (InfY.autEquiv M α)
    ((infinitesimalAutomorphismSetFunctor A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴).map f (InfY.autEquiv M α))
    (twoFibreInfTransition_fac A B S hS toS hA hP h𝒴 w hw f (InfY.autEquiv M α))
  rw [← InfY.autEquiv_natural f α] at h2
  have h3 := TW.liftEquiv_natural f
    (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α)
  rw [liftEquiv_twoFibreBoundaryMap] at h3
  exact isPullbackOfSquareZeroLift_unique A B S hS toS hA
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) f h2 h3

include hw in
/-- **The boundary map `δ : Inf_y(M) ⟶ T_w(M)` is `A`-linear.** -/
public theorem isLinearMap_twoFibreBoundaryMap (M : SiteModule A B) :
    IsLinearMap A (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M) :=
  isLinearMap_of_natural_siteModule A B hA InfY.functor TW.functor
    (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW)
    (fun g u => twoFibreBoundaryMap_natural A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW g u) M

/-- **The boundary map `δ : Inf_y(M) ⟶ T_w(M)` of Stacks 0DNN, as an `A`-linear map.** -/
@[stacks 0DNN "the boundary map `δ : Inf_y(M) → T_w(M)` of the six-term sequence, as an \
  A-linear map: an automorphism α of the trivial deformation y' of y = p x over A[M] is sent \
  to the deformation (x', z', p x' → y' --α--> y' → q z') of w, exactly as in the source. The \
  sequence and its exactness at all five places are \
  Deformation.Artin.twoFibre_sixTermExact."]
public def boundaryLinearMap (M : SiteModule A B) :
    InfY.functor.obj M →ₗ[A] TW.functor.obj M :=
  IsLinearMap.mk' (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M)
    (isLinearMap_twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M)

/-- `boundaryLinearMap` sends `α` to `twoFibreBoundaryMap` applied to `α`. -/
@[simp]
public theorem boundaryLinearMap_apply (M : SiteModule A B) (α : InfY.functor.obj M) :
    boundaryLinearMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α =
      twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α := rfl

include hw in
/-- **The `𝒳`-component of `δ(α)` is the trivial deformation of `x`**, so the composite
`Inf_y(M) ⟶ T_w(M) ⟶ T_x(M)` of the six-term sequence is zero. -/
public theorem tangentMap_twoFibreBoundaryMap_fst
    (TX : TangentFunctorData A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw))
    (M : SiteModule A B) (α : InfY.functor.obj M) :
    tangentMapOfOneMorphism A B S hS toS hA
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw TW TX M
        (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α) = 0 := by
  have h1 := liftEquiv_tangentMapOfOneMorphism A B S hS toS hA
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw TW TX M
    (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α)
  rw [liftEquiv_twoFibreBoundaryMap] at h1
  apply (TX.liftEquiv M).injective
  rw [liftEquiv_zero A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw) h𝒳 TX M]
  exact h1.trans rfl

include hw in
/-- **The `𝒵`-component of `δ(α)` is the trivial deformation of `z`**, so the composite
`Inf_y(M) ⟶ T_w(M) ⟶ T_z(M)` of the six-term sequence is zero. -/
public theorem tangentMap_twoFibreBoundaryMap_snd
    (TZ : TangentFunctorData A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw))
    (M : SiteModule A B) (α : InfY.functor.obj M) :
    tangentMapOfOneMorphism A B S hS toS hA
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
        (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw TW TZ M
        (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α) = 0 := by
  have h1 := liftEquiv_tangentMapOfOneMorphism A B S hS toS hA
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
    (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw TW TZ M
    (twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α)
  rw [liftEquiv_twoFibreBoundaryMap] at h1
  apply (TZ.liftEquiv M).injective
  rw [liftEquiv_zero A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw) h𝒵 TZ M]
  exact h1.trans rfl

include hw in
/-- **The six-term sequence of Stacks 0DNN is a complex at `T_w(M)`**: the boundary map
followed by the pair of projections to the tangent spaces of `x` and of `z` is zero, because
the two components of `δ(α)` are the trivial deformations. -/
@[stacks 0DNN "one inclusion of exactness at T_w(M): the composite \
  Inf_y(M) → T_w(M) → T_x(M) ⊕ T_z(M) of the six-term sequence is zero, the two components \
  of δ(α) being by construction the trivial deformations of x and of z. The exactness \
  assertion itself is Deformation.Artin.exact_boundary_tangentProj, and the whole sequence is \
  Deformation.Artin.twoFibre_sixTermExact."]
public theorem tangentProj_twoFibreBoundaryMap_eq_zero
    (TX : TangentFunctorData A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw))
    (TZ : TangentFunctorData A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw))
    (M : SiteModule A B) (α : InfY.functor.obj M) :
    LinearMap.prod
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw TW TX
          h𝒳 M)
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
          (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw TW TZ
          h𝒵 M)
        (boundaryLinearMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M α) = 0 := by
  refine Prod.ext ?_ ?_
  · exact tangentMap_twoFibreBoundaryMap_fst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW TX M α
  · exact tangentMap_twoFibreBoundaryMap_snd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW TZ M α

/-- `twoFibreTangentSideMap` sends `z` to `tangentMapOfOneMorphismTransport` applied to `z`. -/
@[simp]
public theorem twoFibreTangentSideMap_apply
    (TZ : TangentFunctorData A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw))
    (TY : TangentFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw))
    (M : SiteModule A B) (z : TZ.functor.obj M) :
    twoFibreTangentSideMap A B S hS toS hA hP hQ h𝒴 w hw TZ TY M z =
      tangentMapOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
        (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
        (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
        (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) TZ TY M z := rfl

end Boundary

end Deformation.Artin

end
