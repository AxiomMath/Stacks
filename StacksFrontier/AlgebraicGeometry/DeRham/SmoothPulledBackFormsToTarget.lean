module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTargetMixedTensorUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFiltrationExteriorStep
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageUnitSections
public import StacksFrontier.AlgebraicGeometry.DeRham.CoefficientRingChange

/-!
# The pulled-back forms of Section 50.12 read over `f^{-1}𝒪_Y`

Section 50.12 filters `Ω^•_{X/S}` by the forms pulled back from `Y` along the
`(f∘g)^{-1}𝒪_S`-linear inverse image `f^{-1}Ω^k_{Y/S}` of `Ω^k_{Y/S}` read over `g^{-1}𝒪_S`
(`Stacks.DeRhamSmooth.pulledBackDeRhamComplex`), while the target of the identification of the
graded pieces is built from the `f^{-1}𝒪_Y`-linear inverse image
`Stacks.DeRhamSmooth.pulledBackTargetForms`. **This file compares the two**: it constructs

`θ : f^{-1}Ω^k_{Y/S} ⟶ (f^{-1}Ω^k_{Y/S})|_{(f∘g)^{-1}𝒪_S}`

from the first to the second read over `(f∘g)^{-1}𝒪_S`, and proves that it is compatible with the
two comparisons into `f^*Ω^k_{Y/S}`: followed by
`Stacks.DeRhamSmooth.targetFormsToPullback` it is
`Stacks.DeRhamDirectImage.relativeInverseImageToPullback`.

## Main definitions

* `Stacks.DeRhamSmooth.pulledBackFormsToTarget`: the comparison `θ`.

## Main results

* `Stacks.DeRhamDirectImage.inverseImageBaseProjection_comp_toInverseImageBase`: the square of
  ringed spaces along which `θ` is transposed.
* `Stacks.DeRhamSmooth.pulledBackFormsToTarget_comp_targetFormsToPullback`: **`θ` followed by the
  comparison into `f^*Ω^k_{Y/S}` is the comparison of the pulled-back forms into it.**
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpace

/-- **A morphism into an inverse-image ringed space is determined by its underlying map and its
composite with the projection.** -/
theorem inverseImage_hom_ext (X : RingedSpace.{u, u}) {Z : TopCat.{u}} (i : Z ⟶ X.carrier)
    {W : RingedSpace.{u, u}} (a b : W ⟶ inverseImage X i) (hbase : a.hom.base = b.hom.base)
    (hcomp : a ≫ inverseImageProjection X i = b ≫ inverseImageProjection X i) : a = b := by
  rcases a with ⟨⟨ka, ca⟩⟩
  rcases b with ⟨⟨kb, cb⟩⟩
  change ka = kb at hbase
  subst kb
  have hc' : (⟨ca⟩ : (TopCat.Sheaf.pullback CommRingCat.{u} i).obj X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} ka).obj W.sheaf) = ⟨cb⟩ := by
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i).homEquiv
      X.sheaf ((TopCat.Sheaf.pushforward CommRingCat.{u} ka).obj W.sheaf)).injective
    apply Sheaf.hom_ext
    injection congrArg InducedCategory.Hom.hom hcomp with hb hc
  obtain rfl : ca = cb := congrArg (fun a => a.hom) hc'
  rfl

end AlgebraicGeometry.RingedSpace

namespace Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The square of ringed spaces over `(Y, g^{-1}𝒪_S)`**: the projection
`(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)` followed by `(Y, 𝒪_Y) ⟶ (Y, g^{-1}𝒪_S)` is the change of
coefficients `(X, f^{-1}𝒪_Y) ⟶ (X, (f∘g)^{-1}𝒪_S)` followed by
`Stacks.DeRhamSmooth.relativeBase`. -/
theorem inverseImageBaseProjection_comp_toInverseImageBase :
    inverseImageBaseProjection f ≫ toInverseImageBase g =
      coefficientRingChange f g ≫ Stacks.DeRhamSmooth.relativeBase f g := by
  refine AlgebraicGeometry.RingedSpace.inverseImage_hom_ext S.toRingedSpace g.base _ _ rfl ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (inverseImageBaseProjection f ≫ ·) (toInverseImageBase_comp g)) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (coefficientRingChange f g ≫ ·)
    (relativeInverseImageProjection_comp f g).symm)
  exact (coefficientRingChange_comp_inverseImageBaseProjection f g).symm

end Stacks.DeRhamDirectImage

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The transpose of `θ`**: the unit of the pullback along `(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)` at
`Ω^k_{Y/S}`, read over `g^{-1}𝒪_S` and carried along the square
`Stacks.DeRhamDirectImage.inverseImageBaseProjection_comp_toInverseImageBase`. -/
def pulledBackFormsToTargetLeg (k : ℕ) :
    (pushforward (toInverseImageBase g)).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) ⟶
      (pushforward (relativeBase f g)).obj
        ((coefficientRestriction f g).obj (pulledBackTargetForms f g k)) :=
  (pushforward (toInverseImageBase g)).map
      ((pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) ≫
    (pushforwardComp (inverseImageBaseProjection f) (toInverseImageBase g)).inv.app _ ≫
    eqToHom (congrArg (fun m : inverseImageBase f ⟶ inverseImageBase g =>
      (pushforward m).obj (pulledBackTargetForms f g k))
      (inverseImageBaseProjection_comp_toInverseImageBase f g)) ≫
    (pushforwardComp (coefficientRingChange f g) (relativeBase f g)).hom.app _

/-- **The comparison `θ : f^{-1}Ω^k_{Y/S} ⟶ (f^{-1}Ω^k_{Y/S})|_{(f∘g)^{-1}𝒪_S}`** of the two
inverse images of `Ω^k_{Y/S}`: from the one along `(X, (f∘g)^{-1}𝒪_S) ⟶ (Y, g^{-1}𝒪_S)` to the
one along `(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)`, read over `(f∘g)^{-1}𝒪_S`. It is the transpose of
`Stacks.DeRhamSmooth.pulledBackFormsToTargetLeg`. -/
def pulledBackFormsToTarget (k : ℕ) :
    (pulledBackDeRhamComplex f g).X k ⟶
      (coefficientRestriction f g).obj (pulledBackTargetForms f g k) :=
  ((pullbackPushforwardAdjunction (relativeBase f g)).homEquiv _ _).symm
    (pulledBackFormsToTargetLeg f g k)

/-- A composite of four morphisms of sheaves of modules on a local section, with the four one-step
evaluations supplied as hypotheses. -/
theorem comp4_val_app_apply_of' (Z : RingedSpace.{u}) {A B C D E : Modules Z} (a : A ⟶ B)
    (k : B ⟶ C) (l : C ⟶ D) (m : D ⟶ E) (V : (Opens Z.carrier)ᵒᵖ) (s : A.val.obj V)
    {b : B.val.obj V} (hb : (a.val.app V).hom s = b)
    {c : C.val.obj V} (hc : (k.val.app V).hom b = c)
    {d : D.val.obj V} (hd : (l.val.app V).hom c = d)
    {e : E.val.obj V} (he : (m.val.app V).hom d = e) :
    ((a ≫ k ≫ l ≫ m).val.app V).hom s = e := by
  subst hb hc hd he
  rfl

/-- A transport of sheaves of modules between equal objects is the identity on a local section,
up to the heterogeneous equality that the two spellings of the object require. -/
theorem eqToHom_val_app_heq {Z : RingedSpace.{u}} {A B : Modules Z} (h : A = B)
    (V : (Opens Z.carrier)ᵒᵖ) (s : A.val.obj V) : HEq (((eqToHom h).val.app V).hom s) s := by
  subst h
  rfl

/-- The pullback-unit section of `s`, in the direct image to `(Y, g^{-1}𝒪_S)` of the direct image
along `(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)`. -/
def thetaLegStep₁ (k : ℕ) (V : (Opens Y.carrier)ᵒᵖ)
    (s : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)).val.obj V) :
    ((pushforward (toInverseImageBase g)).obj ((pushforward (inverseImageBaseProjection f)).obj
      (pulledBackTargetForms f g k))).val.obj V :=
  (((pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))).val.app V).hom s

/-- The same section, in the direct image along the composite. -/
def thetaLegStep₂ (k : ℕ) (V : (Opens Y.carrier)ᵒᵖ)
    (s : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)).val.obj V) :
    ((pushforward (inverseImageBaseProjection f ≫ toInverseImageBase g)).obj
      (pulledBackTargetForms f g k)).val.obj V :=
  (((pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))).val.app V).hom s

/-- The same section, in the direct image along the other side of the square. -/
def thetaLegStep₃ (k : ℕ) (V : (Opens Y.carrier)ᵒᵖ)
    (s : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)).val.obj V) :
    ((pushforward (coefficientRingChange f g ≫ relativeBase f g)).obj
      (pulledBackTargetForms f g k)).val.obj V :=
  (((pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))).val.app V).hom s

/-- The same section, in the target of `Stacks.DeRhamSmooth.pulledBackFormsToTargetLeg`. -/
def thetaLegStep₄ (k : ℕ) (V : (Opens Y.carrier)ᵒᵖ)
    (s : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)).val.obj V) :
    ((pushforward (relativeBase f g)).obj
        ((coefficientRestriction f g).obj (pulledBackTargetForms f g k))).val.obj V :=
  (((pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))).val.app V).hom s

/-- The two spellings of the pullback-unit section on either side of the square agree. -/
theorem thetaLegStep₂_heq (k : ℕ) (V : (Opens Y.carrier)ᵒᵖ)
    (s : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)).val.obj V) :
    HEq (thetaLegStep₂ f g k V s) (thetaLegStep₃ f g k V s) :=
  HEq.rfl

/-- **The transpose of `θ` is the unit of the pullback along `(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)` on
sections.** -/
theorem pulledBackFormsToTargetLeg_val_app (k : ℕ) (V : (Opens Y.carrier)ᵒᵖ)
    (s : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)).val.obj V) :
    ((pulledBackFormsToTargetLeg f g k).val.app V).hom s = thetaLegStep₄ f g k V s := by
  have e₃ : ((eqToHom (congrArg (fun m : inverseImageBase f ⟶ inverseImageBase g =>
      (pushforward m).obj (pulledBackTargetForms f g k))
      (inverseImageBaseProjection_comp_toInverseImageBase f g))).val.app V).hom
        (thetaLegStep₂ f g k V s) = thetaLegStep₃ f g k V s :=
    eq_of_heq ((eqToHom_val_app_heq (Z := inverseImageBase g)
      (congrArg (fun m : inverseImageBase f ⟶ inverseImageBase g =>
        (pushforward m).obj (pulledBackTargetForms f g k))
        (inverseImageBaseProjection_comp_toInverseImageBase f g)) V
      (thetaLegStep₂ f g k V s)).trans (thetaLegStep₂_heq f g k V s))
  exact comp4_val_app_apply_of' (inverseImageBase g)
    ((pushforward (toInverseImageBase g)).map
      ((pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))))
    ((pushforwardComp (inverseImageBaseProjection f) (toInverseImageBase g)).inv.app
      (pulledBackTargetForms f g k))
    (eqToHom (congrArg (fun m : inverseImageBase f ⟶ inverseImageBase g =>
      (pushforward m).obj (pulledBackTargetForms f g k))
      (inverseImageBaseProjection_comp_toInverseImageBase f g)))
    ((pushforwardComp (coefficientRingChange f g) (relativeBase f g)).hom.app
      (pulledBackTargetForms f g k)) V s rfl rfl e₃ rfl

/-- **The triangle of restrictions of scalars acts trivially on sections**:
`Stacks.DeRhamDirectImage.coefficientRestrictionToInverseImageBaseIso` carries a section to one
heterogeneously equal to it. -/
theorem coefficientRestrictionToInverseImageBaseIso_hom_app_val_app_heq
    (M : Modules X.toRingedSpace) (W : (Opens X.carrier)ᵒᵖ)
    (y : ((pushforward (toInverseImageBase f) ⋙ coefficientRestriction f g).obj M).val.obj W) :
    HEq ((((coefficientRestrictionToInverseImageBaseIso f g).hom.app M).val.app W).hom y) y := by
  have e : (coefficientRestrictionToInverseImageBaseIso f g).hom.app M =
      (pushforwardComp (toInverseImageBase f) (coefficientRingChange f g)).inv.app M ≫
        eqToHom (congrArg (fun m : X.toRingedSpace ⟶ inverseImageBase (f ≫ g) =>
          (pushforward m).obj M) (toInverseImageBase_comp_coefficientRingChange f g)) := by
    simp only [coefficientRestrictionToInverseImageBaseIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  rw [e]
  exact (eqToHom_val_app_heq (congrArg (fun m : X.toRingedSpace ⟶ inverseImageBase (f ≫ g) =>
      (pushforward m).obj M) (toInverseImageBase_comp_coefficientRingChange f g)) W
    ((((pushforwardComp (toInverseImageBase f) (coefficientRingChange f g)).inv.app M).val.app
      W).hom y)).trans HEq.rfl

/-- **The transpose of `θ`, followed by the comparison of [Stacks, Tag 08DE], is the transpose of
the comparison of the pulled-back forms into `f^*Ω^k_{Y/S}`**, as morphisms out of `Ω^k_{Y/S}`
read over `g^{-1}𝒪_S`. -/
theorem pulledBackFormsToTargetLeg_comp (k : ℕ) :
    pulledBackFormsToTargetLeg f g k ≫
        (pushforward (relativeBase f g)).map
          ((coefficientRestriction f g).map (targetFormsToPullback f g k) ≫
            (coefficientRestrictionToInverseImageBaseIso f g).hom.app _) =
      relativeToPullbackLeg f g
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) := by
  ext V s
  refine (relativeToPullbackLeg_val_app f g _ V s _ ?_).symm
  refine HEq.trans (heq_of_eq
      (Stacks.Cohomology.MixedDerivedTensor.inverseImageToPullbackTopos_val_app_unit
    (Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.ringedToposSiteHom f.toLRSHom.toShHom)
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) V s).symm) ?_
  refine HEq.trans ?_ (heq_of_eq (congrArg (fun x => (((pushforward (relativeBase f g)).map
      ((coefficientRestriction f g).map (targetFormsToPullback f g k) ≫
        (coefficientRestrictionToInverseImageBaseIso f g).hom.app
          ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))))).val.app V).hom
      x) (pulledBackFormsToTargetLeg_val_app f g k V s)).symm)
  exact (coefficientRestrictionToInverseImageBaseIso_hom_app_val_app_heq f g
    ((Scheme.Modules.pullback f).obj
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))
    (Opposite.op ((Opens.map (relativeBase f g).hom.base).obj V.unop)) _).symm

/-- **`θ` followed by the comparison of [Stacks, Tag 08DE] is the comparison of the pulled-back
forms into `f^*Ω^k_{Y/S}`**:

`θ ≫ c|_{(f∘g)^{-1}𝒪_S} = (f^{-1}Ω^k_{Y/S} ⟶ (f^*Ω^k_{Y/S})|_{(f∘g)^{-1}𝒪_S})`,

`c` being `Stacks.DeRhamSmooth.targetFormsToPullback`, the left-hand side read through the
triangle `Stacks.DeRhamDirectImage.coefficientRestrictionToInverseImageBaseIso`, and the
right-hand side `Stacks.DeRhamDirectImage.relativeInverseImageToPullback`. -/
theorem pulledBackFormsToTarget_comp_targetFormsToPullback (k : ℕ) :
    pulledBackFormsToTarget f g k ≫
        (coefficientRestriction f g).map (targetFormsToPullback f g k) ≫
          (coefficientRestrictionToInverseImageBaseIso f g).hom.app _ =
      relativeInverseImageToPullback f g
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) := by
  apply ((pullbackPushforwardAdjunction (relativeBase f g)).homEquiv _ _).injective
  refine Eq.trans ((pullbackPushforwardAdjunction (relativeBase f g)).homEquiv_naturality_right
    (pulledBackFormsToTarget f g k)
    ((coefficientRestriction f g).map (targetFormsToPullback f g k) ≫
      (coefficientRestrictionToInverseImageBaseIso f g).hom.app _)) ?_
  refine Eq.trans (congrArg (· ≫ (pushforward (relativeBase f g)).map
    ((coefficientRestriction f g).map (targetFormsToPullback f g k) ≫
      (coefficientRestrictionToInverseImageBaseIso f g).hom.app _))
    (Equiv.apply_symm_apply _ (pulledBackFormsToTargetLeg f g k))) ?_
  exact (pulledBackFormsToTargetLeg_comp f g k).trans
    (homEquiv_relativeInverseImageToPullback f g _).symm

end Stacks.DeRhamSmooth

end
