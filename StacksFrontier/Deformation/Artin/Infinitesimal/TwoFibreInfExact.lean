module

public import StacksFrontier.Deformation.Artin.Infinitesimal.AdditivityOfInf
public import StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreTangentExact

/-!
# Exactness of the infinitesimal half of the six-term sequence of a 2-fibre product

Let `P : 𝒳 ⟶ 𝒴` and `Q : 𝒵 ⟶ 𝒴` be `1`-morphisms of categories fibred in groupoids over the
big fppf site of a scheme `S` and let `w = (x, z, φ)` be an object of `𝒲 = 𝒳 ×_𝒴 𝒵` over
`Spec A`.  This file proves the two exactness assertions of Stacks 0DNN that live in the
infinitesimal half of the sequence

`0 ⟶ Inf_w(M) ⟶ Inf_x(M) ⊕ Inf_z(M) ⟶ Inf_y(M) --δ--> T_w(M) ⟶ …`,

namely exactness at `Inf_x(M) ⊕ Inf_z(M)` and at `Inf_y(M)`.

Both rest on one computation.  Write `U` for the composite comparison arrow
`Deformation.Artin.twoFibreU` from the trivial deformation of `y = P x` to the image under `Q`
of the `𝒵`-component of the *chosen* trivial deformation of `w`; by
`Deformation.Artin.twoFibreTrivComparison_eq` it can be read along either leg of the square,
and it is an isomorphism.  Conjugating by `U` turns both outer legs of the sequence into one
and the same operation on the `𝒵`-component of an automorphism of the trivial deformation of
`w` (`Deformation.Artin.infFst_comp_twoFibreU`,
`Deformation.Artin.infSnd_comp_twoFibreU`), which is exactly the statement that the two legs
agree on the image of `Inf_w(M)`; and running the same computation backwards builds an
automorphism of the trivial deformation of `w`, resp. an isomorphism of the boundary
deformation with the trivial one, out of a pair on which the legs agree.

Exactness at `Inf_y(M)` uses the additivity of infinitesimal automorphisms: the groupoid
argument produces a *composite* of automorphisms, and `Deformation.Artin.autEquiv_add` turns
that into the difference of the two legs.

## Main results

* `Deformation.Artin.infFst_comp_twoFibreU`, `Deformation.Artin.infSnd_comp_twoFibreU`: the
  two outer legs of the sequence, conjugated by `U`, are the same operation.
* `Deformation.Artin.exact_infProj_infLegDiff`: **Stacks 0DNN, exactness at
  `Inf_x(M) ⊕ Inf_z(M)`**.
* `Deformation.Artin.exact_infLegDiff_boundary`: **Stacks 0DNN, exactness at `Inf_y(M)`**.
* `Deformation.Artin.twoFibre_sixTermExact`: **Stacks 0DNN**, the whole six-term exact
  sequence.

## References

* [Stacks Project, Tag 06I7](https://stacks.math.columbia.edu/tag/06I7)
* [Stacks Project, Tag 0DNN](https://stacks.math.columbia.edu/tag/0DNN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

/-! ### The defining squares of the induced maps, read in the ambient category -/

section InfSquares
open Functor
universe u v₁ w₁ v₂ w₂

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v₁} [Category.{w₁} X] {Y : Type v₂} [Category.{w₂} Y]
  (p : X ⥤ BigFppfOver B S hS) (q : Y ⥤ BigFppfOver B S hS)
  (F : X ⥤ Y) (hF : F ⋙ q = p)
  (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)

/-- The defining square of the map induced by a `1`-morphism on infinitesimal automorphisms,
read as an equation of arrows of `Y`. -/
public theorem infMapOfOneMorphism_fac_right (M : SiteModule A B)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    (infMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq M θ).1.right ≫
        trivialComparison A B S hS toS hA p q F hF x hx hp hq M =
      trivialComparison A B S hS toS hA p q F hF x hx hp hq M ≫ F.map (θ.1.right) :=
  congrArg Under.Hom.right (infMapOfOneMorphism_fac A B S hS toS hA p q F hF x hx hp hq M θ)

end InfSquares

section TransportSquares
open Functor
universe u v w

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {Y : Type v} [Category.{w} Y] (p : Y ⥤ BigFppfOver B S hS) (y₁ y₂ : Y)
  (hy₁ : p.obj y₁ = algebraOver A B S hS toS hA)
  (hy₂ : p.obj y₂ = algebraOver A B S hS toS hA)
  (ι : y₁ ≅ y₂) (hι : p.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) ι.hom)
  (hp : p.IsFiberedInGroupoids)

/-- The defining square of the map induced by a vertical isomorphism on infinitesimal
automorphisms, read as an equation of arrows of `Y`. -/
public theorem infMapOfTransport_fac_right (M : SiteModule A B)
    (θ : trivialDeformation A B S hS toS hA p y₂ hy₂ hp M ⟶
      trivialDeformation A B S hS toS hA p y₂ hy₂ hp M) :
    (infMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M θ).1.right ≫
        trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M =
      trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M ≫ θ.1.right :=
  congrArg Under.Hom.right (fiberEndRestrict_fac (Under.post p)
    (underPost_isFiberedInGroupoids p hp y₁)
    (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).1
    (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).2
    ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).map θ))

end TransportSquares

section TwoFibreInfExact
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

/-- The comparison arrow of the trivial deformations of `y = P x` and of `x`, as an
isomorphism. -/
public abbrev twoFibreCompPIso (M : SiteModule A B) :
    (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ≅
      P.obj ((twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right) :=
  trivialComparisonIso A B S hS toS hA p𝒳 p𝒴 P hP w.x
    (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M

/-- The comparison arrow of the trivial deformation of `x` with the `𝒳`-component of the
chosen trivial deformation of `w`, as an isomorphism. -/
public abbrev twoFibreCompFstIso (M : SiteModule A B) :
    (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right ≅
      (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.x :=
  trivialComparisonIso A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M

/-- The comparison arrow of the trivial deformation of `z` with the `𝒵`-component of the
chosen trivial deformation of `w`, as an isomorphism. -/
public abbrev twoFibreCompSndIso (M : SiteModule A B) :
    (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right ≅
      (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.y :=
  trivialComparisonIso A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
    (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M

/-- The comparison arrow of the trivial deformations of `Q z` and of `z`, as an
isomorphism. -/
public abbrev twoFibreCompQIso (M : SiteModule A B) :
    (twoFibreTrivSndImage A B S hS toS hA hQ h𝒴 w hw M).1.right ≅
      Q.obj ((twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right) :=
  trivialComparisonIso A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
    (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M

/-- The comparison arrow of the trivial deformations of `y = P x` and of `Q z`, as an
isomorphism. -/
public abbrev twoFibreCompTrIso (M : SiteModule A B) :
    (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ≅
      (twoFibreTrivSndImage A B S hS toS hA hQ h𝒴 w hw M).1.right :=
  trivialTransportComparisonIso A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
    (twoFibreFstImageOver A B S hS toS hA hP w hw)
    (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
    (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M

/-- **The composite comparison isomorphism `U`**: from the trivial deformation of `y = P x`
to the image under `Q` of the `𝒵`-component of the chosen trivial deformation of `w`, read
along the `𝒳`-leg.  By `Deformation.Artin.twoFibreU_eq` it can be read along the `𝒵`-leg as
well, and conjugation by it identifies the two outer legs of the six-term sequence. -/
public abbrev twoFibreUIso (M : SiteModule A B) :
    (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ≅
      Q.obj ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.y) :=
  twoFibreCompPIso A B S hS toS hA hP h𝒳 h𝒴 w hw M ≪≫
    P.mapIso (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) ≪≫
      ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso

/-- The forward map of `twoFibreUIso` is the composite of `twoFibreCompP`, the image under
`P` of `twoFibreCompFst`, and the comparison isomorphism of the chosen trivial deformation. -/
@[simp]
public theorem twoFibreUIso_hom (M : SiteModule A B) :
    (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫
        P.map (twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) ≫
        (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom := rfl

/-- `U` read along the `𝒵`-leg. -/
public theorem twoFibreU_eq (M : SiteModule A B) :
    (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M) ≫
        (twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M) ≫
        Q.map (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) :=
  twoFibreTrivComparison_eq A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M

/-- The first two factors of `U`, as an isomorphism: the comparison of the trivial
deformation of `y = P x` with the image under `P` of the `𝒳`-component of the chosen trivial
deformation of `w`. -/
public abbrev twoFibreVIso (M : SiteModule A B) :
    (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ≅
        P.obj ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.x) :=
  twoFibreCompPIso A B S hS toS hA hP h𝒳 h𝒴 w hw M ≪≫
    P.mapIso (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)

/-- The forward map of `twoFibreVIso` is `twoFibreCompP` followed by the image under `P` of
`twoFibreCompFst`. -/
@[simp]
public theorem twoFibreVIso_hom (M : SiteModule A B) :
    (twoFibreVIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫
        P.map (twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) := rfl

/-- `U` is `V` followed by the comparison isomorphism of the chosen trivial deformation. -/
public theorem twoFibreU_eq_V (M : SiteModule A B) :
    (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreVIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom ≫
        (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom := by
  simp only [twoFibreUIso_hom, twoFibreVIso_hom, Category.assoc]

/-- **Half of the conjugation along the `𝒳`-leg**: the `𝒳`-leg read through `V`, without the
comparison isomorphism of `w`. -/
public theorem twoFibreU_fst_half (M : SiteModule A B)
    (χ : (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ⟶
        (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right)
            (α : (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right ⟶
                (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right)
    (a : (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.x ⟶
        (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.x)
    (h1 : χ ≫ (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) =
        (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫ P.map α) (h2 : α ≫
        (twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) =
        (twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) ≫ a) :
    (twoFibreVIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom ≫ P.map a ≫
        (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom = χ ≫
        (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom := by
  rw [twoFibreVIso_hom, twoFibreUIso_hom, Category.assoc, ← P.map_comp_assoc, ← h2,
    P.map_comp_assoc, ← reassoc_of% h1]

/-- **Conjugation along the `𝒵`-leg.** -/
public theorem twoFibreU_snd_conj (M : SiteModule A B)
    (χ : (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ⟶
        (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right)
            (ε : (twoFibreTrivSndImage A B S hS toS hA hQ h𝒴 w hw M).1.right ⟶
                (twoFibreTrivSndImage A B S hS toS hA hQ h𝒴 w hw M).1.right)
    (σ : (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right ⟶
        (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right)
            (b : (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.y ⟶
                (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.y)
    (h1 : χ ≫ (twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M) =
        (twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M) ≫ ε) (h2 : ε ≫
        (twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M) =
        (twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M) ≫ Q.map σ)
    (h3 : σ ≫ (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) =
        (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) ≫ b) :
    χ ≫ (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom ≫ Q.map b := by
  rw [twoFibreU_eq, reassoc_of% h1, reassoc_of% h2, ← Q.map_comp, h3, Q.map_comp]
  simp only [Category.assoc]

/-- **Conjugation along the `𝒳`-leg.** -/
public theorem twoFibreU_fst_conj (M : SiteModule A B)
    (χ : (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ⟶
        (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right)
            (α : (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right ⟶
                (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right)
    (a : (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.x ⟶
        (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.x)
    (b : (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.y ⟶
        (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.y)
    (h1 : χ ≫ (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) =
        (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫ P.map α) (h2 : α ≫
        (twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) =
        (twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) ≫ a)
    (hab : P.map a ≫ (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom =
        (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom ≫ Q.map b) :
    χ ≫ (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom ≫ Q.map b := by
  rw [← twoFibreU_fst_half A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M χ α a h1 h2, twoFibreU_eq_V]
  simp only [Category.assoc, hab]

variable (InfW : InfinitesimalAutomorphismFunctorData A B S hS toS hA
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ))
  (InfX : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒳 w.x
    (twoFibreFstOver A B S hS toS hA w hw) h𝒳)
  (InfZ : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒵 w.y
    (twoFibreSndOver A B S hS toS hA w hw) h𝒵)
  (InfY : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
    (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴)

/-- The `𝒳`-leg evaluated against `U`, with no reference to the comparison isomorphism of
`w`. -/
public theorem twoFibreU_fst_eval (M : SiteModule A B)
    (χ : (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ⟶ (twoFibreTrivFstImage A B S
        hS toS hA hP h𝒴 w hw M).1.right) (α : (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right
        ⟶ (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right)
    (h1 : χ ≫ (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) = (twoFibreCompP A B S hS toS hA hP
        h𝒳 h𝒴 w hw M) ≫ P.map α) :
    χ ≫ (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom = (twoFibreCompP A B S hS toS hA
        hP h𝒳 h𝒴 w hw M) ≫ P.map (α ≫ (twoFibreCompFst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)) ≫
        (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom := by
  rw [twoFibreUIso_hom, reassoc_of% h1, P.map_comp_assoc]

/-- The `𝒵`-leg evaluated against `U`. -/
public theorem twoFibreU_snd_eval (M : SiteModule A B)
    (χ : (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.right ⟶ (twoFibreTrivFstImage A B S
        hS toS hA hP h𝒴 w hw M).1.right) (ε : (twoFibreTrivSndImage A B S hS toS hA hQ h𝒴 w hw
        M).1.right ⟶ (twoFibreTrivSndImage A B S hS toS hA hQ h𝒴 w hw M).1.right)
    (σ : (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right ⟶ (twoFibreTrivSnd A B S hS toS hA h𝒵
        w hw M).1.right)
    (h1 : χ ≫ (twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M) = (twoFibreCompTr A B S hS toS hA
        hP hQ h𝒴 w hw M) ≫ ε) (h2 : ε ≫ (twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M) =
        (twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M) ≫ Q.map σ) :
    χ ≫ (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom = (twoFibreCompTr A B S hS toS hA
        hP hQ h𝒴 w hw M) ≫ (twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M) ≫ Q.map (σ ≫
        (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)) := by
  rw [twoFibreU_eq, reassoc_of% h1, reassoc_of% h2, Q.map_comp]

/-- The comparison isomorphism of a boundary deformation, read after the comparison of the
trivial deformations of `y` and of `x`: the twisting automorphism followed by the `𝒵`-leg. -/
public theorem twoFibreCompP_comp_boundaryIso (M : SiteModule A B)
    (Bo : (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) ⟶ (twoFibreTrivFstImage A B S hS toS
        hA hP h𝒴 w hw M)) :
    (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫ (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴
        w hw M Bo).hom =
      Bo.1.right ≫ (twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M) ≫ (twoFibreCompQ A B S hS toS
          hA hQ h𝒵 h𝒴 w hw M) := by
  rw [boundaryIso_hom]
  exact Iso.hom_inv_id_assoc (twoFibreCompPIso A B S hS toS hA hP h𝒳 h𝒴 w hw M) _

/-- The comparison of the trivial deformation of `x` with that of `w` is compatible with the
structure arrows, `𝒳`-component. -/
private theorem twoFibreTrivFst_hom_comp_compFstIso (M : SiteModule A B) :
    (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom ≫
        (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
      ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).a :=
  trivialComparison_comp A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
    p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M

/-- The comparison of the trivial deformation of `z` with that of `w` is compatible with the
structure arrows, `𝒵`-component. -/
private theorem twoFibreTrivSnd_hom_comp_compSndIso (M : SiteModule A B) :
    (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom ≫
        (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
      ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).b :=
  trivialComparison_comp A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
    p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M

/-- The `𝒳`-comparison isomorphism lies over the identity. -/
private theorem twoFibreCompFstIso_isHomLift (M : SiteModule A B) :
    p𝒳.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
      (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom :=
  trivialComparison_isHomLift A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
    p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M

/-- The `𝒵`-comparison isomorphism lies over the identity. -/
private theorem twoFibreCompSndIso_isHomLift (M : SiteModule A B) :
    p𝒵.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
      (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom :=
  trivialComparison_isHomLift A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
    p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M

/-- The inverse of the `𝒳`-comparison isomorphism lies over the identity. -/
private theorem twoFibreCompFstIso_inv_isHomLift (M : SiteModule A B) :
    p𝒳.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
      (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv :=
  isHomLift_inv_vertical p𝒳 (squareZeroOver A B S hS toS M) _
    (twoFibreCompFstIso_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)

/-- The inverse of the `𝒵`-comparison isomorphism lies over the identity. -/
private theorem twoFibreCompSndIso_inv_isHomLift (M : SiteModule A B) :
    p𝒵.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
      (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv :=
  isHomLift_inv_vertical p𝒵 (squareZeroOver A B S hS toS M) _
    (twoFibreCompSndIso_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)

/-- The `𝒳`-leg into `Inf_y(M)` is compatible with the comparison of the trivial deformations
of `y` and of `x`. -/
private theorem twoFibre_infFst_fac (M : SiteModule A B) (u : InfX.functor.obj M) :
    (InfY.autEquiv M ((infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u)).1.right ≫
        twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M =
      twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M ≫ P.map (InfX.autEquiv M u).1.right := by
  refine (congrArg (fun m => m.1.right ≫ twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M)
    (autEquiv_infFunctorMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M u)).trans ?_
  exact infMapOfOneMorphism_fac_right A B S hS toS hA p𝒳 p𝒴 P hP w.x
    (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M (InfX.autEquiv M u)

/-- The `𝒵`-leg into `Inf_y(M)` is compatible with the comparison of the trivial deformations
of `y` and of `Q z`. -/
private theorem twoFibre_infSide_fac (M : SiteModule A B) (v : InfZ.functor.obj M) :
    (InfY.autEquiv M
        ((twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M) v)).1.right ≫
        twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M =
      twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M ≫
        (infMapOfOneMorphism A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M (InfZ.autEquiv M v)).1.right := by
  refine (congrArg (fun m => m.1.right ≫ twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M)
    (autEquiv_infFunctorMapOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
      (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
      (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒵 h𝒴 InfZ InfY M v)).trans ?_
  exact infMapOfTransport_fac_right A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
    (twoFibreFstImageOver A B S hS toS hA hP w hw)
    (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
    (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M
    (infMapOfOneMorphism A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
      (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M (InfZ.autEquiv M v))

/-- **Stacks 0DNN, exactness at `Inf_x(M) ⊕ Inf_z(M)`.**  A pair of infinitesimal
automorphisms of the trivial deformations of `x` and of `z` on which the two legs into
`Inf_y(M)` agree is, after conjugating by the comparison arrows, the pair of components of an
automorphism of the chosen trivial deformation of `w`: the comparison square of that
automorphism is exactly the agreement of the two legs, read through the isomorphism `U`. -/
public theorem exact_infProj_infLegDiff (M : SiteModule A B) :
    Function.Exact
      (LinearMap.prod
        (infLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳
          InfW InfX M)
        (infLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
          (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵
          InfW InfZ M))
      (LinearMap.coprod (infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M)
        (-(twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M))) := by
  refine exact_prod_coprod_neg _ _ _ _ (fun u v => ?_)
  have h1 := twoFibre_infFst_fac A B S hS toS hA hP h𝒳 h𝒴 w hw InfX InfY M u
  have h2a := twoFibre_infSide_fac A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M v
  have h2b := infMapOfOneMorphism_fac_right A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
    (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M (InfZ.autEquiv M v)
  constructor
  · intro huv
    have hA2 : (InfX.autEquiv M u).1.right ≫
        (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom ≫
            ((twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv ≫
            (InfX.autEquiv M u).1.right ≫
            (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) := by
      rw [Iso.hom_inv_id_assoc]
    have hC3 : (InfZ.autEquiv M v).1.right ≫
        (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom ≫
            ((twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv ≫
            (InfZ.autEquiv M v).1.right ≫
            (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) := by
      rw [Iso.hom_inv_id_assoc]
    have hchi : (InfY.autEquiv M ((infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u)).1.right =
        (InfY.autEquiv M
            ((twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M) v)).1.right :=
      congrArg (fun m => m.1.right) (congrArg (InfY.autEquiv M) huv)
    have hsnd := twoFibreU_snd_conj A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M
        ((twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M) v)).1.right
      (infMapOfOneMorphism A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M (InfZ.autEquiv M v)).1.right
              (InfZ.autEquiv M v).1.right ((twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
              M).inv ≫ (InfZ.autEquiv M v).1.right ≫ (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳
              h𝒵 h𝒴 w hw M).hom) h2a h2b hC3
    have hfst := twoFibreU_fst_half A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M
        ((infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u)).1.right (InfX.autEquiv M
            u).1.right
      ((twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv ≫
          (InfX.autEquiv M u).1.right ≫
          (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) h1 hA2
    have hsq : P.map ((twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv ≫
        (InfX.autEquiv M u).1.right ≫
        (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) ≫
        (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom =
        (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom ≫
            Q.map ((twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv ≫
            (InfZ.autEquiv M v).1.right ≫
            (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) := by
      refine ((twoFibreVIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).cancel_iso_hom_left _ _).mp ?_
      rw [hfst, hchi, hsnd, twoFibreU_eq_V]
      simp only [Category.assoc]
    have hva := isHomLift_comp_vertical p𝒳 (squareZeroOver A B S hS toS M)
      (twoFibreCompFstIso_inv_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
      (isHomLift_comp_vertical p𝒳 (squareZeroOver A B S hS toS M)
        (underPost_isHomLift_right p𝒳 (𝟙 _) (InfX.autEquiv M u).1 (InfX.autEquiv M u).2)
        (twoFibreCompFstIso_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M))
    have hvb := isHomLift_comp_vertical p𝒵 (squareZeroOver A B S hS toS M)
      (twoFibreCompSndIso_inv_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
      (isHomLift_comp_vertical p𝒵 (squareZeroOver A B S hS toS M)
        (underPost_isHomLift_right p𝒵 (𝟙 _) (InfZ.autEquiv M v).1 (InfZ.autEquiv M v).2)
        (twoFibreCompSndIso_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M))
    have hca := twoFibreTrivFst_hom_comp_compFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M
    have hcb := twoFibreTrivSnd_hom_comp_compSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M
    have hda : ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).a ≫
        ((twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv ≫
        (InfX.autEquiv M u).1.right ≫
        (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) =
        ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).a := by
      rw [← hca]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, Under.w (InfX.autEquiv M u).1]
    have hdb : ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).b ≫
        ((twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv ≫
        (InfZ.autEquiv M v).1.right ≫
        (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) =
        ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).b := by
      rw [← hcb]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, Under.w (InfZ.autEquiv M v).1]
    refine ⟨(InfW.autEquiv M).symm (twoFibreLiftHom A B S hS toS hA w hw M (twoFibreTrivW A B S hS
        toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
      ((twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv ≫
          (InfX.autEquiv M u).1.right ≫
          (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) ((twoFibreCompSndIso A B
              S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv ≫ (InfZ.autEquiv M v).1.right ≫
              (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) hva hvb hsq hda
      hdb), ?_, ?_⟩
    · apply (InfX.autEquiv M).injective
      refine Eq.trans (autEquiv_infFunctorMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴
          P Q)
        TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 InfW InfX M _) ?_
      rw [Equiv.apply_symm_apply]
      refine (fiberEndRestrict_eq (Under.post p𝒳)
        (underPost_isFiberedInGroupoids p𝒳 h𝒳 w.x)
        (trivialComparisonHom A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
            p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q)
          TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴
              P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M).1
        (trivialComparisonHom A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
            p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q)
          TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴
              P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M).2 _ (InfX.autEquiv M u) ?_).symm
      exact Under.UnderMorphism.ext hA2
    · apply (InfZ.autEquiv M).injective
      refine Eq.trans (autEquiv_infFunctorMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴
          P Q)
        TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 InfW InfZ M _) ?_
      rw [Equiv.apply_symm_apply]
      refine (fiberEndRestrict_eq (Under.post p𝒵)
        (underPost_isFiberedInGroupoids p𝒵 h𝒵 w.y)
        (trivialComparisonHom A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
            p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q)
          TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴
              P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M).1
        (trivialComparisonHom A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
            p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q)
          TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴
              P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M).2 _ (InfZ.autEquiv M v) ?_).symm
      exact Under.UnderMorphism.ext hC3
  · rintro ⟨θ, hu, hv⟩
    have hAfst : InfX.autEquiv M u =
        infMapOfOneMorphism A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
            (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q)
        TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M (InfW.autEquiv M θ) := by
      rw [← hu]
      exact autEquiv_infFunctorMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴
          P Q)
        TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 InfW InfX M θ
    have hCsnd : InfZ.autEquiv M v =
        infMapOfOneMorphism A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
            (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q)
        TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M (InfW.autEquiv M θ) := by
      rw [← hv]
      exact autEquiv_infFunctorMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴
          P Q)
        TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 InfW InfZ M θ
    have hA2 : (InfX.autEquiv M u).1.right ≫
        (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom ≫
        ((InfW.autEquiv M θ).1.right).a := by
      rw [hAfst]
      exact infMapOfOneMorphism_fac_right A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳
          p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q)
        TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 M (InfW.autEquiv M θ)
    have hC3 : (InfZ.autEquiv M v).1.right ≫
        (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom =
        (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom ≫
        ((InfW.autEquiv M θ).1.right).b := by
      rw [hCsnd]
      exact infMapOfOneMorphism_fac_right A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳
          p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q)
        TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 M (InfW.autEquiv M θ)
    apply (InfY.autEquiv M).injective
    refine Functor.Fiber.hom_ext (Under.UnderMorphism.ext ?_)
    refine ((twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).cancel_iso_hom_right _ _).mp ?_
    exact Eq.trans (twoFibreU_fst_conj A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M
        ((infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u)).1.right (InfX.autEquiv M
            u).1.right
        ((InfW.autEquiv M θ).1.right).a ((InfW.autEquiv M θ).1.right).b h1 hA2 ((InfW.autEquiv M
            θ).1.right).w)
      (twoFibreU_snd_conj A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M
          ((twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M) v)).1.right
          (infMapOfOneMorphism A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M (InfZ.autEquiv M v)).1.right
              (InfZ.autEquiv M v).1.right
        ((InfW.autEquiv M θ).1.right).b h2a h2b hC3).symm

/-- **Stacks 0DNN, exactness at `Inf_y(M)`.**  The boundary deformation attached to an
infinitesimal automorphism `β` of the trivial deformation of `y` is trivial exactly when `β`
is the difference of the two legs on a pair: an isomorphism of `δ(β)` with the chosen trivial
deformation of `w` is a pair of automorphisms of the trivial deformations of `x` and of `z`
whose comparison square says, after conjugating by `U`, that the automorphism attached to the
first is the composite of `β` with the one attached to the second — and by
`Deformation.Artin.autEquiv_add` that composite is the sum. -/
public theorem exact_infLegDiff_boundary (hRS𝒴 : SatisfiesRSStar B S hS p𝒴 h𝒴)
    (TW : TangentFunctorData A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w
        hw) (M : SiteModule A B) :
    Function.Exact (LinearMap.coprod (infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) (-(twoFibreInfSideMap A B S hS toS
          hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M)))
      (boundaryLinearMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M) := by
  refine exact_coprod_neg _ _ _ (fun β => ?_)
  have hca := twoFibreTrivFst_hom_comp_compFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M
  have hcb := twoFibreTrivSnd_hom_comp_compSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M
  have hdelta := liftEquiv_twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M β
  have hzero : TW.liftEquiv M 0 = Quotient.mk _ (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
      M) :=
    liftEquiv_zero A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) TW M
  have hcpb := reassoc_of% (twoFibreCompP_comp_boundaryIso A B S hS toS hA hP hQ h𝒳
    h𝒵 h𝒴 w hw M (InfY.autEquiv M β))
  constructor
  · intro hb
    have hq : boundaryClass A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M β) =
        Quotient.mk _ (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) :=
      Eq.trans hdelta.symm (Eq.trans (congrArg (TW.liftEquiv M) hb) hzero)
    obtain ⟨Θ⟩ := Quotient.exact hq
    obtain ⟨al, hal⟩ : ∃ e : (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right ⟶ (twoFibreTrivW
        A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.x, e = (Θ.hom.1.right).a :=
      ⟨_, rfl⟩
    obtain ⟨bl, hbl⟩ : ∃ e : (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right ⟶ (twoFibreTrivW
        A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right.y, e = (Θ.hom.1.right).b :=
      ⟨_, rfl⟩
    have hvert : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).IsHomLift (𝟙 (squareZeroOver
        A B S hS toS M)) (Θ.hom.1.right) :=
      underPost_isHomLift_right (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) (𝟙 _) Θ.hom.1
          Θ.hom.2
    have hval : p𝒳.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) al := by
      rw [hal]
      exact lift_map_isHomLift (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq
        (𝟙 (squareZeroOver A B S hS toS M)) (u := (boundaryLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w
            hw M (InfY.autEquiv M β)).1.right) (v := (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴
            w hw M).1.right)
        (twoFibreLift_base A B S hS toS hA w hw M (boundaryLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w
            hw M (InfY.autEquiv M β)))
        (twoFibreLift_base A B S hS toS hA w hw M (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w
            hw M)) _ hvert
    have hvbl : p𝒵.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) bl := by
      rw [hbl]
      exact lift_map_isHomLift (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
          (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq
        (𝟙 (squareZeroOver A B S hS toS M)) (u := (boundaryLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w
            hw M (InfY.autEquiv M β)).1.right) (v := (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴
            w hw M).1.right)
        (twoFibreLift_base A B S hS toS hA w hw M (boundaryLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w
            hw M (InfY.autEquiv M β)))
        (twoFibreLift_base A B S hS toS hA w hw M (twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w
            hw M)) _ hvert
    have hwa : (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom ≫ al = ((twoFibreTrivW A B S hS
        toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).a := by
      rw [hal]
      exact congrArg TwoFibreProductOver.Hom.a (Under.w Θ.hom.1)
    have hwb : (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom ≫ bl = ((twoFibreTrivW A B S hS
        toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).b := by
      rw [hbl]
      exact congrArg TwoFibreProductOver.Hom.b (Under.w Θ.hom.1)
    have hΘw : P.map al ≫ (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
        M).1.right).iso).hom = (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M
        β)).hom ≫ Q.map bl := by
      rw [hal, hbl]
      exact (Θ.hom.1.right).w
    have hAu : (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom ≫ (al ≫ (twoFibreCompFstIso A B S
        hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv) = (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom
        := by
      rw [← Category.assoc, hwa, ← hca, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hCv : (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom ≫ (bl ≫ (twoFibreCompSndIso A B S
        hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).inv) = (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom
        := by
      rw [← Category.assoc, hwb, ← hcb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hvA := isHomLift_comp_vertical p𝒳 (squareZeroOver A B S hS toS M) hval
      (twoFibreCompFstIso_inv_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
    have hvC := isHomLift_comp_vertical p𝒵 (squareZeroOver A B S hS toS M) hvbl
      (twoFibreCompSndIso_inv_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
    obtain ⟨u, hu⟩ : ∃ u : InfX.functor.obj M,
        (InfX.autEquiv M u).1.right = al ≫ (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
            M).inv :=
      ⟨(InfX.autEquiv M).symm (underFiberHomMk p𝒳 (twoFibreFstOver A B S hS toS hA w hw)
        (squareZeroArrow A B S hS toS hA M) _ hvA hAu), by rw [Equiv.apply_symm_apply,
            underFiberHomMk_right]⟩
    obtain ⟨v, hv⟩ : ∃ v : InfZ.functor.obj M,
        (InfZ.autEquiv M v).1.right = bl ≫ (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
            M).inv :=
      ⟨(InfZ.autEquiv M).symm (underFiberHomMk p𝒵 (twoFibreSndOver A B S hS toS hA w hw)
        (squareZeroArrow A B S hS toS hA M) _ hvC hCv), by rw [Equiv.apply_symm_apply,
            underFiberHomMk_right]⟩
    have h1 := twoFibre_infFst_fac A B S hS toS hA hP h𝒳 h𝒴 w hw InfX InfY M u
    have h2a := twoFibre_infSide_fac A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M v
    have h2b := infMapOfOneMorphism_fac_right A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
      (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M (InfZ.autEquiv M v)
    have hpa : (InfX.autEquiv M u).1.right ≫ (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w
        hw M).hom = al := by
      rw [hu, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hpc : (InfZ.autEquiv M v).1.right ≫
        (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) = bl := by
      show (InfZ.autEquiv M v).1.right ≫
        (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom = bl
      rw [hv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hkey : (InfY.autEquiv M ((infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u)).1.right =
        (InfY.autEquiv M β).1.right ≫ (InfY.autEquiv M ((twoFibreInfSideMap A B S hS toS hA hP hQ
            h𝒵 h𝒴 w hw InfZ InfY M) v)).1.right := by
      refine ((twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).cancel_iso_hom_right _ _).mp ?_
      calc (InfY.autEquiv M ((infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u)).1.right ≫ (twoFibreUIso A B S
          hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom
          = (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫ P.map ((InfX.autEquiv M u).1.right ≫
              (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) ≫ (((twoFibreTrivW A
              B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom :=
            twoFibreU_fst_eval A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M _ _ h1
        _ = (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫ P.map al ≫ (((twoFibreTrivW A B S hS
            toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom := by rw [hpa]
        _ = (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫
              (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M
                (InfY.autEquiv M β)).hom ≫ Q.map bl := by rw [hΘw]
        _ = (InfY.autEquiv M β).1.right ≫ (twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M) ≫
              (twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M) ≫ Q.map bl := by rw [hcpb]
        _ = (InfY.autEquiv M β).1.right ≫ (twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M) ≫
              (twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M) ≫
                Q.map ((InfZ.autEquiv M v).1.right ≫
                  (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)) := by rw [hpc]
        _ = (InfY.autEquiv M β).1.right ≫
              ((InfY.autEquiv M ((twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw
                  InfZ InfY M) v)).1.right ≫
                (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) := by
            rw [twoFibreU_snd_eval A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M _ _ _ h2a h2b]
        _ = ((InfY.autEquiv M β).1.right ≫
              (InfY.autEquiv M ((twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw
                  InfZ InfY M) v)).1.right) ≫
                (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom :=
            (Category.assoc _ _ _).symm
    refine ⟨u, v, ?_⟩
    have hsum : (infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u = β + (twoFibreInfSideMap A B S
          hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M) v := by
      apply (InfY.autEquiv M).injective
      rw [autEquiv_add A B S hS toS hA p𝒴 (P.obj w.x) (twoFibreFstImageOver A B S hS toS hA hP w
          hw) h𝒴 hRS𝒴 InfY M β ((twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M)
          v)]
      exact Functor.Fiber.hom_ext (Under.UnderMorphism.ext hkey)
    rw [hsum, add_sub_cancel_right]
  · rintro ⟨u, v, huv⟩
    have h1 := twoFibre_infFst_fac A B S hS toS hA hP h𝒳 h𝒴 w hw InfX InfY M u
    have h2a := twoFibre_infSide_fac A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M v
    have h2b := infMapOfOneMorphism_fac_right A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
      (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M (InfZ.autEquiv M v)
    have hkey : (InfY.autEquiv M β).1.right ≫ (InfY.autEquiv M ((twoFibreInfSideMap A B S hS toS
        hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M) v)).1.right =
        (InfY.autEquiv M ((infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u)).1.right := by
      have hs := autEquiv_sub_comp A B S hS toS hA p𝒴 (P.obj w.x) (twoFibreFstImageOver A B S hS
          toS hA hP w hw) h𝒴 hRS𝒴 InfY M ((infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u) ((twoFibreInfSideMap A B S hS
          toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M) v)
      rw [huv] at hs
      exact congrArg (fun m => m.1.right) hs
    have hsq : P.map ((InfX.autEquiv M u).1.right ≫ (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳
        h𝒵 h𝒴 w hw M).hom) ≫ (((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
        M).1.right).iso).hom =
        (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M β)).hom ≫ Q.map
            ((InfZ.autEquiv M v).1.right ≫ (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
            M).hom) := by
      refine ((twoFibreCompPIso A B S hS toS hA hP h𝒳 h𝒴 w hw M).cancel_iso_hom_left _ _).mp ?_
      calc (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫ P.map ((InfX.autEquiv M u).1.right ≫
          (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) ≫ (((twoFibreTrivW A B S
          hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.right).iso).hom
          = (InfY.autEquiv M ((infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) u)).1.right ≫ (twoFibreUIso A B S
          hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom :=
            (twoFibreU_fst_eval A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M _ _ h1).symm
        _ = ((InfY.autEquiv M β).1.right ≫
              (InfY.autEquiv M ((twoFibreInfSideMap A B S hS toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M)
                  v)).1.right) ≫ (twoFibreUIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom := by
            rw [hkey]
        _ = (InfY.autEquiv M β).1.right ≫ (twoFibreCompTr A B S hS toS hA hP hQ h𝒴 w hw M) ≫
              (twoFibreCompQ A B S hS toS hA hQ h𝒵 h𝒴 w hw M) ≫
                Q.map ((InfZ.autEquiv M v).1.right ≫
                  (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)) := by
            rw [Category.assoc,
              twoFibreU_snd_eval A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M _ _ _ h2a h2b]
        _ = (twoFibreCompP A B S hS toS hA hP h𝒳 h𝒴 w hw M) ≫
              (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M β)).hom ≫
                Q.map ((InfZ.autEquiv M v).1.right ≫
                  (twoFibreCompSnd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)) := by rw [hcpb]
    have hda : (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom ≫ ((InfX.autEquiv M u).1.right ≫
        (twoFibreCompFstIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) =
        ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).a := by
      rw [← hca, ← Category.assoc, Under.w (InfX.autEquiv M u).1]
    have hdb : (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom ≫ ((InfZ.autEquiv M v).1.right ≫
        (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom) =
        ((twoFibreTrivW A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).1.hom).b := by
      rw [← hcb, ← Category.assoc, Under.w (InfZ.autEquiv M v).1]
    have hvA := isHomLift_comp_vertical p𝒳 (squareZeroOver A B S hS toS M)
      (underPost_isHomLift_right p𝒳 (𝟙 _) (InfX.autEquiv M u).1 (InfX.autEquiv M u).2)
      (twoFibreCompFstIso_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
    have hvC := isHomLift_comp_vertical p𝒵 (squareZeroOver A B S hS toS M)
      (underPost_isHomLift_right p𝒵 (𝟙 _) (InfZ.autEquiv M v).1 (InfZ.autEquiv M v).2)
      (twoFibreCompSndIso_isHomLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M)
    apply (TW.liftEquiv M).injective
    refine Eq.trans hdelta (Eq.trans ?_ hzero.symm)
    exact Quotient.sound ⟨liftHomIso (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q)
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) (twoFibreLiftHom A
        B S hS toS hA w hw M
      (boundaryLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M (InfY.autEquiv M β)) (twoFibreTrivW A B
          S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M) ((InfX.autEquiv M u).1.right ≫ (twoFibreCompFstIso A
          B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M).hom)
      ((InfZ.autEquiv M v).1.right ≫ (twoFibreCompSndIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw
          M).hom) hvA hvC hsq hda hdb)⟩

/-- The six-term sequence of Stacks 0DNN, for an arbitrary choice of the linear functors
`Inf_?` and `T_?`. For `𝒳`, `𝒴`, `𝒵` fibred in groupoids over the big fppf site of `S`
satisfying condition (RS\*), `1`-morphisms `p : 𝒳 ⟶ 𝒴` and `q : 𝒵 ⟶ 𝒴`, an object `w` of
`𝒲 = 𝒳 ×_𝒴 𝒵` over `Spec A` with components `x`, `z` and `y = p x`, and an `A`-module `M`,
the six-term sequence

`0 ⟶ Inf_w(M) ⟶ Inf_x(M) ⊕ Inf_z(M) ⟶ Inf_y(M) --δ--> T_w(M) ⟶ T_x(M) ⊕ T_z(M) ⟶ T_y(M)`

of `A`-modules is exact.  Its horizontal maps are the ones Remark 07YA attaches to the four
`1`-morphisms, the two out of the `𝒵`-side composed with the identification along the
comparison isomorphism of `w`; its boundary map is `Deformation.Artin.boundaryLinearMap`,
which sends an automorphism `α` of the trivial deformation of `y` to the deformation
`(x', z', p x' → y' --α--> y' → q z')` of `w`.  Exactness at the five places is asserted as
the injectivity of the first map together with four `Function.Exact`s. -/
public theorem twoFibre_sixTermExact (hRS𝒴 : SatisfiesRSStar B S hS p𝒴 h𝒴)
    (TW : TangentFunctorData A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w
        hw)
    (TX : TangentFunctorData A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw))
    (TZ : TangentFunctorData A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw))
    (TY : TangentFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw))
    (M : SiteModule A B) :
    Function.Injective (LinearMap.prod (infLinearMapOfOneMorphism A B S hS toS hA
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P
        Q)
        TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 InfW InfX M) (infLinearMapOfOneMorphism A B S hS toS hA
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵
            p𝒴 P Q)
        TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 InfW InfZ M)) ∧
      Function.Exact (LinearMap.prod (infLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴
          P Q)
        TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳 InfW InfX M) (infLinearMapOfOneMorphism A B S hS toS hA
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵
            p𝒴 P Q)
        TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P
            Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵 InfW InfZ M))
        (LinearMap.coprod (infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) (-(twoFibreInfSideMap A B S hS
            toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M))) ∧
      Function.Exact (LinearMap.coprod (infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 InfX InfY M) (-(twoFibreInfSideMap A B S hS
            toS hA hP hQ h𝒵 h𝒴 w hw InfZ InfY M))) (boundaryLinearMap A B S hS toS hA hP hQ h𝒳 h𝒵
            h𝒴 w hw InfY TW M) ∧
      Function.Exact (boundaryLinearMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M)
          (LinearMap.prod (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴
          P Q)
        TwoFibreProductOver.fst_comp_eq w hw TW TX h𝒳 M) (tangentLinearMapOfOneMorphism A B S hS
            toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd
            p𝒳 p𝒵 p𝒴 P Q)
        TwoFibreProductOver.snd_comp_eq w hw TW TZ h𝒵 M)) ∧
      Function.Exact (LinearMap.prod (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴
          P Q)
        TwoFibreProductOver.fst_comp_eq w hw TW TX h𝒳 M) (tangentLinearMapOfOneMorphism A B S hS
            toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd
            p𝒳 p𝒵 p𝒴 P Q)
        TwoFibreProductOver.snd_comp_eq w hw TW TZ h𝒵 M))
        (LinearMap.coprod (tangentLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) TX TY h𝒴 M) (-(twoFibreTangentSideMap A B S hS toS
            hA hP hQ h𝒴 w hw TZ TY M))) :=
  ⟨injective_twoFibreInfProj A B S hS toS hA p𝒳 p𝒵 p𝒴 P Q hP hQ h𝒳 h𝒵 h𝒴 w hw InfW InfX
      InfZ M,
    exact_infProj_infLegDiff A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfW InfX InfZ InfY M,
    exact_infLegDiff_boundary A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfX InfZ InfY hRS𝒴 TW M,
    exact_boundary_tangentProj A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw TW TX TZ InfY M,
    exact_tangentProj_tangentLegDiff A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw TW TX TZ TY M⟩

end TwoFibreInfExact

end Deformation.Artin

end
