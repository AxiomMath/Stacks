module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposIsoComp
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism

/-!
# Isomorphisms of ringed topoi from an isomorphism of inverse images

Let `g₁ : (Sh(C), O_C) ⟶ (Sh(D₁), O₁)` and `g₂ : (Sh(C), O_C) ⟶ (Sh(D₂), O₂)` be morphisms of
ringed topoi out of the same ringed topos whose direct images are equivalences, and let
`d : g₁⁻¹O₁ ≅ g₂⁻¹O₂` be an isomorphism of sheaves of commutative rings on `C` compatible with the
two inverse-image forms `g_i⁻¹O_i ⟶ O_C` of the structure maps. Then
`Φ = (g₂, id) ∘ (g₁, d)⁻¹ : (Sh(D₁), O₁) ⟶ (Sh(D₂), O₂)` is an isomorphism of ringed topoi, and
`Φ ∘ g₁` is 2-isomorphic to `g₂`.

This is how an isomorphism of the structure sheaves of two thickenings of the same space, read on
the small étale site of that space, becomes an isomorphism of the small étale ringed topoi of the
two thickenings (Stacks 05ZM), to which Stacks 05YZ then applies.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.pulledBackStructureRingedTopos`: `(Sh(C), g⁻¹O_D)`.
* `AlgebraicGeometry.RingedToposHom.transferOfInverseImageIso`: the isomorphism `Φ`.
* `AlgebraicGeometry.RingedToposHom.transferOfInverseImageIsoCompTwoIso`: `Φ ∘ g₁ ≅ g₂`.
* `AlgebraicGeometry.RingedToposHom.transferOfInverseImageIsoBaseTwoIso`: `σ₂ ∘ Φ ≅ σ₁` for
  morphisms `σ_j` out of `(Sh(D_j), O_j)` compatible with `d`.

## Main results

* `isIso_fSharp_of_isEquivalence_pushforward_of_isIso_fSharpInverseImage`: a morphism of ringed
  topoi whose direct image is an equivalence and whose inverse-image form `f⁻¹O_Y ⟶ O_X` is an
  isomorphism has invertible structure map `O_Y ⟶ f_*O_X`.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe v u w

section IsIso

variable {X Y : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- On underlying sheaves of sets, the structure map of `f` is the unit of `f⁻¹ ⊣ f_*` followed by
the direct image of the inverse-image form. -/
private theorem forgetFSharp_eq_unit_comp (f : RingedToposHom X Y) :
    forgetFSharp f = f.toToposHom.adj.unit.app (Y.forgetRing.obj Y.O) ≫
      f.toToposHom.pushforward.map (X.forgetRing.map f.fSharpInverseImage) :=
  (forgetFSharp_eq_homEquiv f).trans (Adjunction.homEquiv_unit _ _ _ _)

/-- The structure map of a morphism of ringed topoi whose direct image is an equivalence is
invertible as soon as its inverse-image form is: on underlying sheaves of sets it is the unit of
`f⁻¹ ⊣ f_*`, an isomorphism, followed by the direct image of the inverse-image form. -/
theorem isIso_fSharp_of_isEquivalence_pushforward_of_isIso_fSharpInverseImage
    (f : RingedToposHom X Y) [f.toToposHom.pushforward.IsEquivalence]
    [IsIso f.fSharpInverseImage] : IsIso f.fSharp := by
  have h₁ : IsIso (f.toToposHom.adj.unit.app (Y.forgetRing.obj Y.O)) :=
    NatIso.isIso_app_of_isIso _ _
  have h₂ : IsIso (f.toToposHom.pushforward.map (X.forgetRing.map f.fSharpInverseImage)) :=
    Functor.map_isIso _ _
  have h₃ : IsIso (forgetFSharp f) := by
    rw [forgetFSharp_eq_unit_comp]; exact IsIso.comp_isIso' h₁ h₂
  have : IsIso (Y.forgetRing.map f.fSharp) := h₃
  exact isIso_of_reflects_iso f.fSharp Y.forgetRing

end IsIso

section Transfer

variable {X Y₁ Y₂ : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The ringed topos `(Sh(C), g⁻¹O_D)`** of a morphism of ringed topoi
`g : (Sh(C), O_C) ⟶ (Sh(D), O_D)`: the site of the source with the inverse image of the
structure sheaf of the target. -/
abbrev pulledBackStructureRingedTopos {Y : RingedTopos.{v, u, w}} (g : RingedToposHom X Y) :
    RingedTopos.{v, u, w} :=
  ⟨X.C, X.J, (inverseImageCommRingFunctor g.toToposHom).obj Y.O⟩

/-- The forgetful functor from rings to types preserves sheaves on the site of
`(Sh(C), g⁻¹O_D)`. -/
instance hasSheafCompose_forget_pulledBackStructureRingedTopos {Y : RingedTopos.{v, u, w}}
    (g : RingedToposHom X Y) :
    (pulledBackStructureRingedTopos g).J.HasSheafCompose (forget RingCat.{w}) :=
  inferInstanceAs (X.J.HasSheafCompose (forget RingCat.{w}))

/-- The forgetful functor from commutative rings to rings preserves sheaves on the site of
`(Sh(C), g⁻¹O_D)`. -/
instance hasSheafCompose_forget₂_pulledBackStructureRingedTopos {Y : RingedTopos.{v, u, w}}
    (g : RingedToposHom X Y) :
    (pulledBackStructureRingedTopos g).J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
  inferInstanceAs (X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}))

variable (g₁ : RingedToposHom X Y₁) (g₂ : RingedToposHom X Y₂)
  [g₁.toToposHom.pushforward.IsEquivalence] [g₂.toToposHom.pushforward.IsEquivalence]
  (d : (inverseImageCommRingFunctor g₁.toToposHom).obj Y₁.O ≅
    (inverseImageCommRingFunctor g₂.toToposHom).obj Y₂.O)

/-- `(g₂, id) : (Sh(C), g₂⁻¹O₂) ⟶ (Sh(D₂), O₂)`. -/
abbrev transferTarget : RingedToposHom (pulledBackStructureRingedTopos g₂) Y₂ :=
  ofInverseImageIso (X := pulledBackStructureRingedTopos g₂) g₂.toToposHom (Iso.refl _)

/-- `(g₁, d) : (Sh(C), g₂⁻¹O₂) ⟶ (Sh(D₁), O₁)`. -/
abbrev transferSource : RingedToposHom (pulledBackStructureRingedTopos g₂) Y₁ :=
  ofInverseImageIso (X := pulledBackStructureRingedTopos g₂) g₁.toToposHom d

/-- The direct image of `(g₂, id)` is an equivalence. -/
instance isEquivalence_transferTarget_pushforward :
    (transferTarget g₂).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs g₂.toToposHom.pushforward.IsEquivalence

/-- The direct image of `(g₁, d)` is an equivalence. -/
instance isEquivalence_transferSource_pushforward :
    (transferSource g₁ g₂ d).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs g₁.toToposHom.pushforward.IsEquivalence

/-- The structure map of `(g₂, id)` is an isomorphism. -/
instance isIso_transferTarget_fSharp : IsIso (transferTarget g₂).fSharp :=
  haveI := isIso_fSharpInverseImage_ofInverseImageIso (X := pulledBackStructureRingedTopos g₂)
    g₂.toToposHom (Iso.refl _)
  isIso_fSharp_of_isEquivalence_pushforward_of_isIso_fSharpInverseImage _

/-- The structure map of `(g₁, d)` is an isomorphism. -/
instance isIso_transferSource_fSharp : IsIso (transferSource g₁ g₂ d).fSharp :=
  haveI := isIso_fSharpInverseImage_ofInverseImageIso (X := pulledBackStructureRingedTopos g₂)
    g₁.toToposHom d
  isIso_fSharp_of_isEquivalence_pushforward_of_isIso_fSharpInverseImage _

/-- The direct image of `(g₁, d)⁻¹` is an equivalence. -/
instance isEquivalence_transferSource_inverse_pushforward :
    (transferSource g₁ g₂ d).inverse.toToposHom.pushforward.IsEquivalence :=
  MorphismOfTopoi.isEquivalence_inverseImage (transferSource g₁ g₂ d).toToposHom

/-- The structure map of `(g₁, d)⁻¹` is an isomorphism. -/
instance isIso_transferSource_inverse_fSharp : IsIso (transferSource g₁ g₂ d).inverse.fSharp :=
  inferInstanceAs (IsIso (inv (transferSource g₁ g₂ d).fSharpInverseImage))

/-- **The isomorphism of ringed topoi `Φ = (g₂, id) ∘ (g₁, d)⁻¹ : (Sh(D₁), O₁) ⟶ (Sh(D₂), O₂)`**
determined by an isomorphism `d : g₁⁻¹O₁ ≅ g₂⁻¹O₂`. -/
def transferOfInverseImageIso : RingedToposHom Y₁ Y₂ :=
  (transferTarget g₂).comp (transferSource g₁ g₂ d).inverse

/-- The direct image of `Φ` is an equivalence. -/
instance isEquivalence_transferOfInverseImageIso_pushforward :
    (transferOfInverseImageIso g₁ g₂ d).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs
    ((transferTarget g₂).comp (transferSource g₁ g₂ d).inverse).toToposHom.pushforward.IsEquivalence

/-- The structure map of `Φ` is an isomorphism. -/
instance isIso_transferOfInverseImageIso_fSharp :
    IsIso (transferOfInverseImageIso g₁ g₂ d).fSharp :=
  inferInstanceAs (IsIso ((transferTarget g₂).comp (transferSource g₁ g₂ d).inverse).fSharp)

section TwoIso

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- The direct image of `Φ ∘ g₁` is `g₁_* ⋙ g₁⁻¹ ⋙ g₂_*`, identified with `g₂_*` by the counit of
`g₁⁻¹ ⊣ g₁_*`, an isomorphism since `g₁_*` is an equivalence. -/
def transferCompPushforwardIso :
    ((transferOfInverseImageIso g₁ g₂ d).comp g₁).toToposHom.pushforward ≅
      g₂.toToposHom.pushforward :=
  (Functor.associator g₁.toToposHom.pushforward g₁.toToposHom.inverseImage
      g₂.toToposHom.pushforward).symm ≪≫
    Functor.isoWhiskerRight (asIso g₁.toToposHom.adj.counit) g₂.toToposHom.pushforward ≪≫
    Functor.leftUnitor g₂.toToposHom.pushforward

omit [g₂.toToposHom.pushforward.IsEquivalence] in
/-- The component of `transferCompPushforwardIso` at `Z` is the direct image under `g₂_*` of the
counit of `g₁⁻¹ ⊣ g₁_*` at `Z`. -/
theorem transferCompPushforwardIso_hom_app (Z : X.Topos) :
    (transferCompPushforwardIso g₁ g₂ d).hom.app Z =
      g₂.toToposHom.pushforward.map (g₁.toToposHom.adj.counit.app Z) := by
  change 𝟙 _ ≫ g₂.toToposHom.pushforward.map (g₁.toToposHom.adj.counit.app Z) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

omit [g₂.toToposHom.pushforward.IsEquivalence] in
/-- On underlying sheaves of sets, the structure map of `(g₂, id)` is the unit of `g₂⁻¹ ⊣ g₂_*`
at `O₂`. -/
theorem forgetFSharp_transferTarget :
    forgetFSharp (transferTarget g₂) = g₂.toToposHom.adj.unit.app (Y₂.forgetRing.obj Y₂.O) := by
  rw [forgetFSharp_eq_unit_comp, ofInverseImageIso_fSharpInverseImage,
    Iso.refl_hom]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

omit [g₂.toToposHom.pushforward.IsEquivalence] in
/-- The structure map of `(g₁, d)⁻¹` is `d⁻¹ : g₂⁻¹O₂ ⟶ g₁⁻¹O₁`. -/
theorem transferSource_inverse_fSharp : (transferSource g₁ g₂ d).inverse.fSharp = d.inv :=
  IsIso.inv_eq_of_hom_inv_id ((congrArg (· ≫ d.inv)
    (ofInverseImageIso_fSharpInverseImage _ _)).trans d.hom_inv_id)

omit [g₂.toToposHom.pushforward.IsEquivalence] in
/-- On underlying sheaves of sets, the structure map of `(g₁, d)⁻¹` is the image of `d⁻¹`. -/
theorem forgetFSharp_transferSource_inverse :
    forgetFSharp (transferSource g₁ g₂ d).inverse = X.forgetRing.map d.inv :=
  congrArg X.forgetRing.map (transferSource_inverse_fSharp g₁ g₂ d)

/-- **`Φ ∘ g₁` is 2-isomorphic to `g₂`** when `d` is compatible with the two inverse-image forms
of the structure maps. -/
def transferOfInverseImageIsoCompTwoIso
    (hd : d.hom ≫ g₂.fSharpInverseImage = g₁.fSharpInverseImage) :
    TwoIso ((transferOfInverseImageIso g₁ g₂ d).comp g₁) g₂ where
  e := transferCompPushforwardIso g₁ g₂ d
  commutes := by
    have hd' : d.inv ≫ g₁.fSharpInverseImage = g₂.fSharpInverseImage := by
      rw [← hd, Iso.inv_hom_id_assoc]
    have hΦ : forgetFSharp (transferOfInverseImageIso g₁ g₂ d) =
        forgetFSharp (transferTarget g₂) ≫ g₂.toToposHom.pushforward.map
          (forgetFSharp (transferSource g₁ g₂ d).inverse) :=
      forgetFSharp_comp _ _
    rw [forgetFSharp_comp, transferCompPushforwardIso_hom_app, hΦ]
    change ((forgetFSharp (transferTarget g₂) ≫ g₂.toToposHom.pushforward.map
      (forgetFSharp (transferSource g₁ g₂ d).inverse)) ≫ g₂.toToposHom.pushforward.map
        (g₁.toToposHom.inverseImage.map (forgetFSharp g₁))) ≫
      g₂.toToposHom.pushforward.map (g₁.toToposHom.adj.counit.app (X.forgetRing.obj X.O)) = _
    have key : X.forgetRing.map d.inv ≫ X.forgetRing.map g₁.fSharpInverseImage =
        X.forgetRing.map g₂.fSharpInverseImage := by
      rw [← Functor.map_comp, hd']
    have key₂ : g₁.toToposHom.inverseImage.map (forgetFSharp g₁) ≫
        g₁.toToposHom.adj.counit.app (X.forgetRing.obj X.O) =
          X.forgetRing.map g₁.fSharpInverseImage := by
      rw [forgetFSharp_eq_homEquiv g₁]
      exact (g₁.toToposHom.adj.homEquiv_counit _ _ _).symm.trans
        ((g₁.toToposHom.adj.homEquiv _ _).symm_apply_apply _)
    rw [forgetFSharp_transferTarget, forgetFSharp_transferSource_inverse]
    calc _ = g₂.toToposHom.adj.unit.app (Y₂.forgetRing.obj Y₂.O) ≫ g₂.toToposHom.pushforward.map
          (X.forgetRing.map d.inv ≫ g₁.toToposHom.inverseImage.map (forgetFSharp g₁) ≫
            g₁.toToposHom.adj.counit.app (X.forgetRing.obj X.O)) :=
          (Category.assoc _ _ _).trans (congrArg
            (fun m => g₂.toToposHom.adj.unit.app (Y₂.forgetRing.obj Y₂.O) ≫ m)
            ((congrArg (fun m => g₂.toToposHom.pushforward.map (X.forgetRing.map d.inv) ≫ m)
              (g₂.toToposHom.pushforward.map_comp _ _).symm).trans
              (g₂.toToposHom.pushforward.map_comp _ _).symm))
      _ = _ := (congrArg (fun m => g₂.toToposHom.adj.unit.app (Y₂.forgetRing.obj Y₂.O) ≫
            g₂.toToposHom.pushforward.map m)
          ((congrArg (fun m => X.forgetRing.map d.inv ≫ m) key₂).trans key)).trans
          ((forgetFSharp_eq_homEquiv g₂).trans (Adjunction.homEquiv_unit _ _ _ _)).symm

end TwoIso

end Transfer

section Cancel

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

variable {X Y T : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [T.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (σ : RingedToposHom Y T) (h : RingedToposHom X Y) [h.toToposHom.pushforward.IsEquivalence]
  [IsIso h.fSharp]

/-- **Precomposing `σ ∘ h` with the inverse of an isomorphism `h` of ringed topoi gives back
`σ`**, up to the unit of `h⁻¹ ⊣ h_*`. -/
def compCompInverseTwoIso : TwoIso ((σ.comp h).comp h.inverse) σ where
  e := (Functor.associator h.toToposHom.inverseImage h.toToposHom.pushforward
      σ.toToposHom.pushforward).symm ≪≫
    Functor.isoWhiskerRight (asIso h.toToposHom.adj.unit).symm σ.toToposHom.pushforward ≪≫
    Functor.leftUnitor σ.toToposHom.pushforward
  commutes := by
    have hu : forgetFSharp h ≫ h.toToposHom.pushforward.map (forgetFSharp h.inverse) =
        h.toToposHom.adj.unit.app (Y.forgetRing.obj Y.O) :=
      (forgetFSharp_comp h h.inverse).symm.trans (forgetRing_map_comp_inverse_fSharp h)
    have he : ((Functor.associator h.toToposHom.inverseImage h.toToposHom.pushforward
        σ.toToposHom.pushforward).symm ≪≫
      Functor.isoWhiskerRight (asIso h.toToposHom.adj.unit).symm σ.toToposHom.pushforward ≪≫
      Functor.leftUnitor σ.toToposHom.pushforward).hom.app (Y.forgetRing.obj Y.O) =
        σ.toToposHom.pushforward.map
          ((asIso h.toToposHom.adj.unit).inv.app (Y.forgetRing.obj Y.O)) := by
      change 𝟙 _ ≫ σ.toToposHom.pushforward.map _ ≫ 𝟙 _ = _
      rw [Category.id_comp, Category.comp_id]
      rfl
    rw [he, forgetFSharp_comp, forgetFSharp_comp]
    change ((forgetFSharp σ ≫ σ.toToposHom.pushforward.map (forgetFSharp h)) ≫
      σ.toToposHom.pushforward.map (h.toToposHom.pushforward.map (forgetFSharp h.inverse))) ≫
        σ.toToposHom.pushforward.map
          ((asIso h.toToposHom.adj.unit).inv.app (Y.forgetRing.obj Y.O)) = _
    exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
      ((congrArg (forgetFSharp σ ≫ ·)
        ((congrArg (σ.toToposHom.pushforward.map (forgetFSharp h) ≫ ·)
          (σ.toToposHom.pushforward.map_comp _ _).symm).trans
          ((σ.toToposHom.pushforward.map_comp _ _).symm.trans
            ((congrArg σ.toToposHom.pushforward.map ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ (asIso h.toToposHom.adj.unit).inv.app (Y.forgetRing.obj Y.O))
                  hu).trans
                ((asIso h.toToposHom.adj.unit).hom_inv_id_app _)))).trans
              (σ.toToposHom.pushforward.map_id _))))).trans (Category.comp_id _)))

end Cancel

section Base

variable {X Y₁ Y₂ T : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})] [T.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (g₁ : RingedToposHom X Y₁) (g₂ : RingedToposHom X Y₂)
  [g₁.toToposHom.pushforward.IsEquivalence] [g₂.toToposHom.pushforward.IsEquivalence]
  (d : (inverseImageCommRingFunctor g₁.toToposHom).obj Y₁.O ≅
    (inverseImageCommRingFunctor g₂.toToposHom).obj Y₂.O)
  (σ₁ : RingedToposHom Y₁ T) (σ₂ : RingedToposHom Y₂ T)

/-- **`Φ` is compatible with morphisms `σ_j : (Sh(D_j), O_j) ⟶ T`** as soon as `σ₂ ∘ (g₂, id)`
and `σ₁ ∘ (g₁, d)` are 2-isomorphic, both read on `(Sh(C), g₂⁻¹O₂)`. -/
def transferOfInverseImageIsoBaseTwoIso
    (t : TwoIso (σ₂.comp (transferTarget g₂)) (σ₁.comp (transferSource g₁ g₂ d))) :
    TwoIso (σ₂.comp (transferOfInverseImageIso g₁ g₂ d)) σ₁ :=
  ((TwoIso.associator (transferSource g₁ g₂ d).inverse (transferTarget g₂) σ₂).trans
    (TwoIso.whiskerLeft (transferSource g₁ g₂ d).inverse t)).trans
    (compCompInverseTwoIso σ₁ (transferSource g₁ g₂ d))

end Base

end AlgebraicGeometry.RingedToposHom

end
