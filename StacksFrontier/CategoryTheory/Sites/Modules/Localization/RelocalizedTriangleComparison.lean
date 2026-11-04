module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedMorphismInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableRelocalizationCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 04J9: the two relocalization triangles, and the comparison they identify

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites given by a continuous functor
`u`, let `V` be an object of `D`, `U` an object of `C` and `c : U ⟶ u(V)` a morphism of `C`.
Stacks 04J1 relocalizes the morphism of ringed *sites* to `f_c`, and Stacks 04J8 relocalizes the
morphism of ringed *topoi* to `f_s` along the map `s : h_U^# ⟶ f^{-1}h_V^#` that `c` induces.
Stacks 04J9 asserts that the two resulting commutative diagrams agree via the identifications of
Stacks 04J3.

## Main definitions

* `AlgebraicGeometry.RingedSite.Hom.relocCompareTwoIso`: Stacks 04J5's comparison of the two
  relocalizations, in the sheaf-morphism description, as a 2-isomorphism of morphisms of ringed
  topoi.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.relocTriangleCompareSite_eq_relocTriangleCompareTopos`:
  Stacks 04J9's compatibility of the relocalization triangle of Stacks 04IY with that of
  Stacks 04J4, under that 2-isomorphism.
* `AlgebraicGeometry.RingedSite.Hom.relocalizedComparison`: **Stacks 04J9.**

## References

* [Stacks Project, Tag 04J9](https://stacks.math.columbia.edu/tag/04J9)
* [Stacks Project, Tag 04J5](https://stacks.math.columbia.edu/tag/04J5)
* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04J7](https://stacks.math.columbia.edu/tag/04J7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- Vertical composition of two conjugates, with each factor identified. -/
theorem conjugateEquiv_comp₂_eq {L₁ L₂ L₃ : A ⥤ B} {R₁ R₂ R₃ : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (α : L₂ ⟶ L₁) (β : L₃ ⟶ L₂)
    {a : R₁ ⟶ R₂} {b : R₂ ⟶ R₃}
    (ha : conjugateEquiv adj₁ adj₂ α = a) (hb : conjugateEquiv adj₂ adj₃ β = b) :
    conjugateEquiv adj₁ adj₃ (β ≫ α) = a ≫ b := by
  rw [← ha, ← hb, conjugateEquiv_comp]

/-- **The component of the inverse of the isomorphism attached to an equality of functors.** It
is the morphism attached to the equality of the values. -/
theorem eqToIso_inv_app_eq_eqToHom {F G : A ⥤ B} (h : F = G) (Z : A) (hZ : G.obj Z = F.obj Z) :
    (eqToIso h).inv.app Z = eqToHom hZ :=
  Eq.trans (congrArg (fun τ ↦ NatTrans.app τ Z) (eqToIso.inv h)) (eqToHom_app h.symm Z)

/-- The value at an object of a functor that an equality presents as a composite, with the value
of the first factor named. -/
theorem obj_eq_of_eq_comp {C : Type u₃} [Category.{v₃} C] {P : A ⥤ C} (F : A ⥤ B) {G : B ⥤ C}
    (h : P = F ⋙ G) (Z : A) (W : B) (hW : F.obj Z = W) : G.obj W = P.obj Z := by
  subst hW
  subst h
  rfl

/-- `obj_eq_of_eq_comp` for an equality of functors read in the other direction. -/
theorem obj_eq_of_comp_eq {C : Type u₃} [Category.{v₃} C] {Q : A ⥤ C} (F : A ⥤ B) {H : B ⥤ C}
    (h : F ⋙ H = Q) (Z : A) (W : B) (hW : F.obj Z = W) : Q.obj Z = H.obj W := by
  subst hW
  subst h
  rfl

/-- **The inverse of a left-whiskered isomorphism of functors flanked by two equalities of
functors, read at an object.** It is the component of the whiskered isomorphism at the whiskering
functor's value, between the two morphisms attached to the equalities of the values. -/
theorem eqToIso_trans_isoWhiskerLeft_trans_eqToIso_inv_app {C : Type u₃} [Category.{v₃} C]
    {P Q : A ⥤ C} (F : A ⥤ B) {G H : B ⥤ C} (δ : G ≅ H)
    (h₁ : P = F ⋙ G) (h₂ : F ⋙ H = Q) (Z : A) (W : B) (hW : F.obj Z = W) :
    (eqToIso h₁ ≪≫ Functor.isoWhiskerLeft F δ ≪≫ eqToIso h₂).inv.app Z =
      eqToHom (obj_eq_of_comp_eq F h₂ Z W hW) ≫ δ.inv.app W ≫
        eqToHom (obj_eq_of_eq_comp F h₁ Z W hW) := by
  subst hW
  subst h₁
  subst h₂
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  rfl

/-- A morphism flanked by two transports along equalities of an object with itself is that
morphism. -/
theorem eqToHom_comp_comp_eqToHom {o p : B} (g : o ⟶ p) (h₁ : o = o) (h₂ : p = p) :
    eqToHom h₁ ≫ g ≫ eqToHom h₂ = g := by
  simp

/-- Two equal isomorphisms of functors have equal inverses at every object. -/
theorem inv_app_of_eq {F G : A ⥤ B} {x y : F ≅ G} (h : x = y) (Z : A) :
    x.inv.app Z = y.inv.app Z := by
  rw [h]

/-- A triangle of isomorphisms, read on the inverse of its diagonal. -/
theorem inv_comp_eq_of_comp₂ {o₁ o₂ o₃ : A} (x : o₁ ≅ o₂) (y : o₂ ≅ o₃) (z : o₁ ≅ o₃)
    (h : x.hom ≫ y.hom = z.hom) : z.inv = y.inv ≫ x.inv :=
  (congrArg Iso.inv (Iso.ext (α := x ≪≫ y) (β := z) h)).symm

end Stacks.CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

section Pieces

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp

variable {P Q R S : RingedTopos.{u, u, u}}
  [P.J.HasSheafCompose (forget RingCat.{u})] [Q.J.HasSheafCompose (forget RingCat.{u})]
  [R.J.HasSheafCompose (forget RingCat.{u})] [S.J.HasSheafCompose (forget RingCat.{u})]
  [P.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Q.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [R.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The inverse of a 2-isomorphism built from a comparison of inverse images is the conjugate of
the inverted comparison. -/
theorem conjugateEquiv_ofInverseImageIso_symm_e_hom {p q : RingedToposHom P Q}
    (α : q.toToposHom.inverseImage ≅ p.toToposHom.inverseImage)
    (h : α.hom.app (Q.forgetRing.obj Q.O) ≫ P.forgetRing.map p.fSharpInverseImage =
      P.forgetRing.map q.fSharpInverseImage) :
    conjugateEquiv q.toToposHom.adj p.toToposHom.adj α.inv =
      (TwoIso.ofInverseImageIso α h).symm.e.hom := rfl

omit [Q.J.HasSheafCompose (forget RingCat.{u})]
  [Q.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The relocalization triangle of Stacks 04J4, whiskered, as a conjugate.** -/
theorem conjugateEquiv_whiskerLeft_toposRelocalizationTriangle {H K : Q.Topos} (a : H ⟶ K)
    (Φ : RingedToposHom P (Q.localizedRingedTopos H)) :
    conjugateEquiv
        ((Q.localizationMorphism H).toToposHom.adj.comp Φ.toToposHom.adj)
        (((Q.localizationMorphism K).toToposHom.adj.comp
            (Q.relocalizationMorphism a).toToposHom.adj).comp Φ.toToposHom.adj)
        (Functor.whiskerRight
          (𝟙 (Q.localizationMorphism H).toToposHom.inverseImage)
          Φ.toToposHom.inverseImage) =
      (TwoIso.whiskerLeft Φ (toposRelocalizationTriangle Q a)).e.hom :=
  conjugateEquiv_whiskerRight _ _ _ _

/-- `conjugateEquiv_twoIso_whiskerLeft` for a 2-isomorphism out of a composite, with that
composite adjunction split. -/
theorem conjugateEquiv_twoIso_whiskerLeft_comp_source (g : RingedToposHom P Q)
    {p₁ : RingedToposHom Q R} {q₁ : RingedToposHom R S} {q : RingedToposHom Q S}
    (s : TwoIso (comp q₁ p₁) q)
    {τ : q.toToposHom.inverseImage ⟶
      q₁.toToposHom.inverseImage ⋙ p₁.toToposHom.inverseImage}
    (h : conjugateEquiv (q₁.toToposHom.adj.comp p₁.toToposHom.adj) q.toToposHom.adj τ =
      s.e.hom) :
    conjugateEquiv ((q₁.toToposHom.adj.comp p₁.toToposHom.adj).comp g.toToposHom.adj)
        (q.toToposHom.adj.comp g.toToposHom.adj)
        (Functor.whiskerRight τ g.toToposHom.inverseImage) =
      (TwoIso.whiskerLeft g s).e.hom :=
  (conjugateEquiv_whiskerRight _ _ g.toToposHom.adj τ).trans
    (congrArg (fun z ↦ Functor.whiskerLeft g.toToposHom.pushforward z) h)

end Pieces

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp
  MorphismOfTopoi.comp

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) {V : Y.C} {U : X.C}
  (c : U ⟶ f.u.obj V)

/-- **Stacks 04J5's comparison at the map Stacks 04J9 relocalizes at, as it is built**: Stacks
04J5's comparison at the representable map `h_c^#`, whiskered by the relocalization along Stacks
04D3's isomorphism and transported across two equalities of functors. -/
theorem Hom.relocCompareInverseImageIso_eq :
    f.relocCompareInverseImageIso c =
      eqToIso (f.compareMid_relocalization_inverseImage_eq c) ≪≫
        Functor.isoWhiskerLeft
          (X.ringedTopos.relocalizationMorphism
            (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage
          (representableRelocalizationSheafMapCompInverseImageIso X c).symm ≪≫
        eqToIso (f.relocalizationSheafMap_inverseImage_eq c).symm :=
  rfl

/-- **Restricting a sheaf to `f^{-1}h_V^#` and relocalizing along Stacks 04D3's isomorphism is
restricting it to `h_{u(V)}^#`.** The two localizations differ by that isomorphism, and
relocalizing a restriction along it is the restriction to the other object on the nose. -/
theorem Hom.relocalization_localization_inverseImage_obj (A : Sheaf X.J (Type u)) :
    (X.ringedTopos.relocalizationMorphism
        (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.obj
      ((RingedTopos.localizationMorphism X.ringedTopos
        (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage.obj A) =
      (RingedTopos.localizationMorphism X.ringedTopos
        (representableSheaf X (f.u.obj V))).toToposHom.inverseImage.obj A :=
  rfl

/-- **The component of the inverse of Stacks 04J5's comparison, transported.** The comparison is
Stacks 04J5's comparison at the representable map `h_c^#`, whiskered by the relocalization along
Stacks 04D3's isomorphism and transported across two equalities of towers of localization data;
this reads its component as the component of Stacks 04J5's comparison between the two transports.
-/
theorem Hom.relocCompareInverseImageIso_inv_app_transport (A : Sheaf X.J (Type u)) :
    (f.relocCompareInverseImageIso c).inv.app
        ((RingedTopos.localizationMorphism X.ringedTopos
          (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage.obj A) =
      eqToHom (Stacks.CategoryTheory.obj_eq_of_comp_eq _
          (f.relocalizationSheafMap_inverseImage_eq c).symm _ _
          (f.relocalization_localization_inverseImage_obj A)) ≫
        (representableRelocalizationSheafMapCompInverseImageIso X c).symm.inv.app _ ≫
        eqToHom (Stacks.CategoryTheory.obj_eq_of_eq_comp _
          (f.compareMid_relocalization_inverseImage_eq c) _ _
          (f.relocalization_localization_inverseImage_obj A)) :=
  Eq.trans
    (Stacks.CategoryTheory.inv_app_of_eq (f.relocCompareInverseImageIso_eq c) _)
    (Stacks.CategoryTheory.eqToIso_trans_isoWhiskerLeft_trans_eqToIso_inv_app _ _ _ _ _ _
      (f.relocalization_localization_inverseImage_obj A))

/-- **The two transports of `Hom.relocCompareInverseImageIso_inv_app_transport` are identities.**
Both equalities of towers of localization data are the identity at the object in question, so the
flanking morphisms are. -/
theorem Hom.relocCompareInverseImageIso_inv_app_eqToHom (A : Sheaf X.J (Type u)) :
    eqToHom (Stacks.CategoryTheory.obj_eq_of_comp_eq _
          (f.relocalizationSheafMap_inverseImage_eq c).symm _ _
          (f.relocalization_localization_inverseImage_obj A)) ≫
        (representableRelocalizationSheafMapCompInverseImageIso X c).symm.inv.app _ ≫
        eqToHom (Stacks.CategoryTheory.obj_eq_of_eq_comp _
          (f.compareMid_relocalization_inverseImage_eq c) _ _
          (f.relocalization_localization_inverseImage_obj A)) =
      (representableRelocalizationSheafMapCompInverseImageIso X c).hom.app
        ((RingedTopos.localizationMorphism X.ringedTopos
          (representableSheaf X (f.u.obj V))).toToposHom.inverseImage.obj A) :=
  Stacks.CategoryTheory.eqToHom_comp_comp_eqToHom _ rfl rfl

/-- **The component of the inverse of Stacks 04J5's comparison at the map Stacks 04J9
relocalizes at.** The comparison is Stacks 04J5's comparison at the representable map `h_c^#`,
whiskered by the relocalization along Stacks 04D3's isomorphism and transported across two
equalities of towers of localization data; the two transports are the identity at every object,
so the component is the component of Stacks 04J5's comparison alone. -/
theorem Hom.relocCompareInverseImageIso_inv_app (A : Sheaf X.J (Type u)) :
    (f.relocCompareInverseImageIso c).inv.app
        ((RingedTopos.localizationMorphism X.ringedTopos
          (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage.obj A) =
      (representableRelocalizationSheafMapCompInverseImageIso X c).hom.app
        ((RingedTopos.localizationMorphism X.ringedTopos
          (representableSheaf X (f.u.obj V))).toToposHom.inverseImage.obj A) :=
  Eq.trans (f.relocCompareInverseImageIso_inv_app_transport c A)
    (f.relocCompareInverseImageIso_inv_app_eqToHom c A)

/-- **The Stacks 04IE coherence behind Stacks 04J5's structure-map compatibility.** Stacks 04J5's
comparison of the two relocalizations, inverted, followed by Stacks 04J3's identification at
`u(V)` restricted along the relocalization of the ringed site, is Stacks 04J3's identification at
`U`. It is the coherence of the three identifications of Stacks 04IE, at `h_U^#`, at `h_{u(V)}^#`
and at `h_U^#/h_{u(V)}^#`. -/
theorem Hom.relocKeyNat (A : Sheaf X.J (Type u)) :
    (f.relocCompareInverseImageIso c).inv.app
          ((RingedTopos.localizationMorphism X.ringedTopos
            (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage.obj A) ≫
        (X.relocalizationRingedToposHom c).toToposHom.inverseImage.map
          ((X.representableLocalizationInverseImageIso (f.u.obj V)).hom.app A) =
      (X.representableLocalizationInverseImageIso U).hom.app A :=
  Eq.trans
    (CategoryTheory.comp_right_of_eq (f.relocCompareInverseImageIso_inv_app c A) _)
    (X.representableRelocalizationSheafMapCompInverseImageIso_hom_app_comp c A)

/-! ### The structure maps of the two composites -/

/-- **The structure map of the 04J1 side, in inverse-image form and on underlying sheaves of
sets.** The middle identification of Stacks 04J3 preceded by the relocalization of the ringed
site along `c` has for structure map the relocalization applied to Stacks 04J3's identification
at `u(V)`: the relocalization of a ringed site contributes the identity. -/
theorem Hom.forgetRing_relocSiteComp_fSharpInverseImage :
    (ringedTopos (X.over U)).forgetRing.map
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
          (Y := ringedTopos (X.over (f.u.obj V)))
          (Z := RingedTopos.localizedRingedTopos X.ringedTopos
            (f.inverseImageRepresentableSheaf V))
          (f.compareMid V) (X.relocalizationRingedToposHom c)).fSharpInverseImage =
      (X.relocalizationRingedToposHom c).toToposHom.inverseImage.map
        ((X.representableLocalizationInverseImageIso (f.u.obj V)).hom.app
          ((ringedTopos X).forgetRing.obj X.O)) := by
  refine Eq.trans (comp_fSharpInverseImage_forget
    (X := ringedTopos (X.over U)) (Y := ringedTopos (X.over (f.u.obj V)))
    (Z := RingedTopos.localizedRingedTopos X.ringedTopos
      (f.inverseImageRepresentableSheaf V))
    (f.compareMid V) (X.relocalizationRingedToposHom c)) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (X.forgetRing_relocalizationRingedToposHom_fSharpInverseImage c)) ?_
  refine (Category.comp_id _).trans ?_
  exact CategoryTheory.map_of_eq
    (X.relocalizationRingedToposHom c).toToposHom.inverseImage
    (f.forgetRing_compareMid_fSharpInverseImage V)

/-- **The structure map of the 04J8 side, in inverse-image form and on underlying sheaves of
sets.** The relocalization of the ringed topos along `s` preceded by Stacks 04J3's identification
at `U` has for structure map Stacks 04J3's identification at `U`: the relocalization of a ringed
topos contributes the identity. -/
theorem Hom.forgetRing_relocToposComp_fSharpInverseImage :
    (ringedTopos (X.over U)).forgetRing.map
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
          (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
          (Z := RingedTopos.localizedRingedTopos X.ringedTopos
            (f.inverseImageRepresentableSheaf V))
          (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
          (representableLocalizationRingedMorphism X U)).fSharpInverseImage =
      (X.representableLocalizationInverseImageIso U).hom.app
        ((ringedTopos X).forgetRing.obj X.O) := by
  refine Eq.trans (comp_fSharpInverseImage_forget
    (X := ringedTopos (X.over U))
    (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
    (Z := RingedTopos.localizedRingedTopos X.ringedTopos
      (f.inverseImageRepresentableSheaf V))
    (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
    (representableLocalizationRingedMorphism X U)) ?_
  refine Eq.trans (congrArg (fun z =>
      (representableLocalizationRingedMorphism X U).toToposHom.inverseImage.map z ≫
        (ringedTopos (X.over U)).forgetRing.map
          (representableLocalizationRingedMorphism X U).fSharpInverseImage)
    (forgetRing_relocalizationMorphism_fSharpInverseImage X.ringedTopos
      (f.relocalizationSheafMap c))) ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (ringedTopos (X.over U)).forgetRing.map
        (representableLocalizationRingedMorphism X U).fSharpInverseImage)
    ((representableLocalizationRingedMorphism X U).toToposHom.inverseImage.map_id _)) ?_
  exact (Category.id_comp _).trans
    (forgetRing_representableLocalizationRingedMorphism_fSharpInverseImage X U)

/-! ### Stacks 04J5 as a 2-isomorphism of ringed topoi

Below this point Stacks 04J5's comparison of inverse images is an atom. -/

attribute [local irreducible]
  AlgebraicGeometry.RingedSite.Hom.relocCompareInverseImageIso

/-- **Stacks 04J5 in the sheaf-morphism description, as a 2-isomorphism of morphisms of ringed
topoi.** The middle identification of Stacks 04J3 preceded by the relocalization of the ringed
site along `c` *is* the relocalization of the ringed topos along `s : h_U^# ⟶ f^{-1}h_V^#`
preceded by Stacks 04J3's identification at `U`. -/
noncomputable def Hom.relocCompareTwoIso :
    AlgebraicGeometry.RingedToposHom.TwoIso
      (A := ringedTopos (X.over U))
      (B := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (X.over (f.u.obj V)))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (f.compareMid V) (X.relocalizationRingedToposHom c))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
        (representableLocalizationRingedMorphism X U)) :=
  TwoIso.ofInverseImageIso
    (A := ringedTopos (X.over U))
    (B := RingedTopos.localizedRingedTopos X.ringedTopos
      (f.inverseImageRepresentableSheaf V))
    (p := AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
      (Y := ringedTopos (X.over (f.u.obj V)))
      (Z := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (f.compareMid V) (X.relocalizationRingedToposHom c))
    (q := AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
      (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
      (Z := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
      (representableLocalizationRingedMorphism X U))
    (f.relocCompareInverseImageIso c).symm (by
      rw [f.forgetRing_relocSiteComp_fSharpInverseImage c,
        f.forgetRing_relocToposComp_fSharpInverseImage c]
      exact f.relocKeyNat c ((ringedTopos X).forgetRing.obj X.O))

/-! ### The two relocalization triangles, as conjugates -/

/-- The 2-isomorphism of Stacks 04IY's relocalization triangle is, by construction, the canonical
comparison of two right adjoints of the same functor. -/
theorem relocalizationTriangle_e_hom_rightAdjointUniq (Z : RingedSite.{u, u, u}) {W W' : Z.C}
    (a : W ⟶ W') :
    (relocalizationTriangle Z a).e.hom =
      (Adjunction.rightAdjointUniq
        ((Z.localizationRingedToposHom W).toToposHom.adj.ofNatIsoLeft
          (eqToIso (inverseImage_eq Z.J a (Type u))))
        ((Z.localizationRingedToposHom W').toToposHom.adj.comp
          (Z.relocalizationRingedToposHom a).toToposHom.adj)).hom := rfl

/-- **The relocalization triangle of Stacks 04IY, as a conjugate.** -/
theorem relocalizationTriangle_e_hom_eq (Z : RingedSite.{u, u, u}) {W W' : Z.C} (a : W ⟶ W') :
    conjugateEquiv (Z.localizationRingedToposHom W).toToposHom.adj
        ((Z.localizationRingedToposHom W').toToposHom.adj.comp
          (Z.relocalizationRingedToposHom a).toToposHom.adj)
        (eqToIso (inverseImage_eq Z.J a (Type u))).inv =
      (relocalizationTriangle Z a).e.hom :=
  (Stacks.CategoryTheory.rightAdjointUniq_ofNatIsoLeft_left_hom _ _ _).symm.trans
    (relocalizationTriangle_e_hom_rightAdjointUniq Z a).symm

/-- The 04IY side of Stacks 04J9's compatibility of the two relocalization triangles, unfolded:
Stacks 04J3's identification at `U` followed by the relocalization triangle of Stacks 04IY. -/
theorem Hom.relocTriangleCompareSite_e_hom_comp :
    (f.relocTriangleCompareSite c).e.hom =
      (localizationTwoIso X U).e.hom ≫ (relocalizationTriangle X c).e.hom := rfl

/-- **The 04IY side of Stacks 04J9's compatibility of the two relocalization triangles, as a
conjugate.** -/
theorem Hom.relocTriangleCompareSite_e_hom_eq :
    conjugateEquiv
        ((RingedTopos.localizationMorphism X.ringedTopos
            (representableSheaf X U)).toToposHom.adj.comp
          (representableLocalizationRingedMorphism X U).toToposHom.adj)
        ((X.localizationRingedToposHom (f.u.obj V)).toToposHom.adj.comp
          (X.relocalizationRingedToposHom c).toToposHom.adj)
        ((eqToIso (inverseImage_eq X.J c (Type u))).inv ≫
          (X.representableLocalizationInverseImageIso U).inv) =
      (f.relocTriangleCompareSite c).e.hom :=
  Eq.trans
    (Stacks.CategoryTheory.conjugateEquiv_comp₂_eq _ _ _ _ _
      (localizationTwoIso_e_hom_eq X U)
      (relocalizationTriangle_e_hom_eq X c))
    (f.relocTriangleCompareSite_e_hom_comp c).symm

/-- The 04J4 side of Stacks 04J9's compatibility of the two relocalization triangles, unfolded
into its five factors: Stacks 04J4's relocalization triangle whiskered by Stacks 04J3's
identification at `U`, an associator, `Hom.relocCompareTwoIso` inverted and whiskered by the
localization at `f^{-1}h_V^#`, the opposite associator, and the middle identification whiskered
by the relocalization of the ringed site. -/
theorem Hom.relocTriangleCompareTopos_e_hom_comp :
    (f.relocTriangleCompareTopos c (f.relocCompareTwoIso c)).e.hom =
      (TwoIso.whiskerLeft (representableLocalizationRingedMorphism X U)
            (toposRelocalizationTriangle X.ringedTopos
              (f.relocalizationSheafMap c))).e.hom ≫
        (TwoIso.associator (representableLocalizationRingedMorphism X U)
              (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
              (RingedTopos.localizationMorphism X.ringedTopos
                (f.inverseImageRepresentableSheaf V))).symm.e.hom ≫
          ((f.relocCompareTwoIso c).symm.whiskerRight
                (RingedTopos.localizationMorphism X.ringedTopos
                  (f.inverseImageRepresentableSheaf V))).e.hom ≫
            (TwoIso.associator (X.relocalizationRingedToposHom c) (f.compareMid V)
                  (RingedTopos.localizationMorphism X.ringedTopos
                    (f.inverseImageRepresentableSheaf V))).e.hom ≫
              (TwoIso.whiskerLeft (X.relocalizationRingedToposHom c)
                (f.kapMid V)).e.hom := rfl


/-- `Hom.kapMid_e_hom_eq'` with the relocalization triangle's identity contracted away: the
middle identification is the conjugate of Stacks 04J3's comparison at `u(V)` alone. -/
theorem Hom.kapMid_e_hom_eq'' :
    conjugateEquiv
        ((RingedTopos.localizationMorphism X.ringedTopos
            (f.inverseImageRepresentableSheaf V)).toToposHom.adj.comp
          (f.compareMid V).toToposHom.adj)
        (X.localizationRingedToposHom (f.u.obj V)).toToposHom.adj
        (X.representableLocalizationInverseImageIso (f.u.obj V)).inv =
      (f.kapMid V).e.hom :=
  Eq.trans
    (Stacks.CategoryTheory.conjugateEquiv_of_eq _ _
      (f.representableLocalizationInverseImageIso_inv_comp_triangle V).symm)
    (f.kapMid_e_hom_eq' V)

/-- **The inverse-image identity behind Stacks 04J9's compatibility of the two relocalization
triangles.** Read on inverse images, the 04J4 side — Stacks 04J3's identification at `u(V)`
restricted along the relocalization of Stacks 04IY, followed by Stacks 04J5's comparison
restricted along `j_{f^{-1}h_V^#}` — is the 04IY side: the strict identity of Stacks 03EH
followed by Stacks 04J3's identification at `U`. -/
theorem Hom.relocTriangleInverseImageIdentity :
    Functor.whiskerRight (X.representableLocalizationInverseImageIso (f.u.obj V)).inv
          (X.relocalizationRingedToposHom c).toToposHom.inverseImage ≫
        Functor.whiskerLeft
            (RingedTopos.localizationMorphism X.ringedTopos
              (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage
            (f.relocCompareInverseImageIso c).hom ≫
          Functor.whiskerRight
            (𝟙 (RingedTopos.localizationMorphism X.ringedTopos
              (representableSheaf X U)).toToposHom.inverseImage)
            (representableLocalizationRingedMorphism X U).toToposHom.inverseImage =
      (eqToIso (inverseImage_eq X.J c (Type u))).inv ≫
        (X.representableLocalizationInverseImageIso U).inv := by
  refine NatTrans.ext (funext fun A ↦ ?_)
  refine Eq.trans (NatTrans.comp_app _ _ A) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (NatTrans.comp_app _ _ A)) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
    (Eq.trans (Functor.whiskerRight_app _ _ _)
      (Eq.trans (CategoryTheory.map_of_eq _ (NatTrans.id_app _ _))
        ((representableLocalizationRingedMorphism X
          U).toToposHom.inverseImage.map_id _))))) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.comp_id _)) ?_
  refine Eq.trans ?_ (Eq.trans (NatTrans.comp_app _ _ A)
    (Eq.trans (CategoryTheory.comp_right_of_eq
        (show (eqToIso (inverseImage_eq X.J c (Type u))).inv.app A = 𝟙 _ from rfl) _)
      (Category.id_comp _))).symm
  exact (Stacks.CategoryTheory.inv_comp_eq_of_comp₂
    ((f.relocCompareInverseImageIso c).app
      ((RingedTopos.localizationMorphism X.ringedTopos
        (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage.obj A)).symm
    ((X.relocalizationRingedToposHom c).toToposHom.inverseImage.mapIso
      ((X.representableLocalizationInverseImageIso (f.u.obj V)).app A))
    ((X.representableLocalizationInverseImageIso U).app A)
    (f.relocKeyNat c A)).symm

/-- **Stacks 04J9's compatibility of the two relocalization triangles.** -/
theorem Hom.relocTriangleCompareSite_eq_relocTriangleCompareTopos :
    f.relocTriangleCompareSite c =
      f.relocTriangleCompareTopos c (f.relocCompareTwoIso c) := by
  apply AlgebraicGeometry.RingedToposHom.TwoIso.ext_hom
  have hT := Stacks.CategoryTheory.conjugateEquiv_comp₅_eq _ _ _ _ _ _ _ _ _ _ _
    (conjugateEquiv_whiskerLeft_toposRelocalizationTriangle (f.relocalizationSheafMap c)
      (representableLocalizationRingedMorphism X U))
    (conjugateEquiv_associator_symm_e_hom (representableLocalizationRingedMorphism X U)
      (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
      (RingedTopos.localizationMorphism X.ringedTopos
        (f.inverseImageRepresentableSheaf V)))
    (conjugateEquiv_twoIso_whiskerRight_comp (f.relocCompareTwoIso c).symm
      (RingedTopos.localizationMorphism X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (conjugateEquiv_ofInverseImageIso_symm_e_hom
        (f.relocCompareInverseImageIso c).symm _))
    (conjugateEquiv_associator_e_hom (X.relocalizationRingedToposHom c) (f.compareMid V)
      (RingedTopos.localizationMorphism X.ringedTopos
        (f.inverseImageRepresentableSheaf V)))
    (conjugateEquiv_twoIso_whiskerLeft_comp_source (X.relocalizationRingedToposHom c)
      (f.kapMid V) f.kapMid_e_hom_eq'')
  refine Eq.trans (f.relocTriangleCompareSite_e_hom_eq c).symm ?_
  refine Eq.trans (Stacks.CategoryTheory.conjugateEquiv_of_eq _ _ ?_)
    (Eq.trans hT (f.relocTriangleCompareTopos_e_hom_comp c).symm)
  symm
  simp only [Stacks.CategoryTheory.associator_hom_eq_id,
    Stacks.CategoryTheory.associator_inv_eq_id, Category.id_comp]
  erw [Category.id_comp]
  exact f.relocTriangleInverseImageIdentity c

/-- **Stacks 04J9.** The commutative diagram of Stacks 04J1 and the commutative diagram of
Stacks 04J8 agree via the identifications of Stacks 04J3: there is a 2-isomorphism
`β : ι_V ∘ f_c ≅ f_s ∘ ι_U` of morphisms of ringed topoi under which the localization square of
Stacks 04J1 *is* the localization square of Stacks 04J8. -/
@[stacks 04J9 "the commutative diagrams of 04J1 and of 04J8 agree via the identifications of
  04J3"]
theorem Hom.relocalizedComparison : f.RelocalizedComparisonStatement c :=
  f.exists_relocalizedComparison_of_relocTriangles V c (f.relocCompareTwoIso c)
    (f.relocTriangleCompareSite_eq_relocTriangleCompareTopos c)

end AlgebraicGeometry.RingedSite

end
