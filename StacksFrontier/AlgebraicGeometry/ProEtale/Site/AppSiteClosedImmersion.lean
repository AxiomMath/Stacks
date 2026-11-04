module

public import StacksFrontier.AlgebraicGeometry.Pushout.ClosedImmersionIntegral
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteTransport
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change along a closed immersion of affine schemes on the site of ind-étale affines

For a closed immersion `i : Z ⟶ X` of affine schemes, pulling back along `i` carries an affine
object of the small pro-étale site of `X` with ind-étale ring of global sections to one over `Z`,
and the resulting functor `X_app ⥤ Z_app` is extension of scalars along `𝒪(X) → 𝒪(Z)` read
through the identification of each site with the opposite of a category of ind-étale algebras.

## Main definitions

* `AlgebraicGeometry.ProEtale.indEtaleAlgebraTransport` — the equivalence of categories of
  ind-étale algebras induced by an isomorphism of base rings.
* `AlgebraicGeometry.ProEtale.appAlgOp` — global sections as a functor from `X_app` to the
  opposite of the category of ind-étale algebras over the global sections of `X`.
* `AlgebraicGeometry.ProEtale.appProetaleBaseChange` — the base change functor
  `X_app ⥤ Z_app`, `U ↦ U ×_X Z`.

## Main results

* `AlgebraicGeometry.ProEtale.isPullback_specMap_pushout_appTop` — for affine `U`, `X` and `Z`
  the spectrum of the pushout of the rings of global sections is the fibre product `U ×_X Z`.
* `AlgebraicGeometry.ProEtale.appProetaleBaseChangeIso` — base change on the sites is
  extension of scalars on ind-étale algebras.
* `AlgebraicGeometry.ProEtale.indEtaleAlgebraBaseChange_hasFullyFaithfulRightAdjoint` —
  extension of scalars along a surjection of commutative rings has a fully faithful right
  adjoint.
* `AlgebraicGeometry.ProEtale.appProetaleBaseChange_hasLeftAdjoint`,
  `AlgebraicGeometry.ProEtale.appProetaleLift_fullyFaithful` and
  `AlgebraicGeometry.ProEtale.appProetaleLift_baseChangeIso` — base change along a closed
  immersion of affine schemes has a fully faithful left adjoint `v`, and the unit identifies
  an object `V` of `Z_app` with `v(V) ×_X Z`.

## Implementation notes

The fibre product `U ×_X Z` of affine schemes is identified with the spectrum of the pushout
of the rings of global sections by `AlgebraicGeometry.isPullback_SpecMap_pushout` transported
along `AlgebraicGeometry.Scheme.isoSpec` of the three schemes; this is what makes the pullback
of an object of `X_app` again affine with ind-étale global sections, since extension of scalars
on ind-étale algebras is defined by exactly that pushout.

Stacks 097P is stated for the quotient of a ring by an ideal, while the global sections of a
closed subscheme are only isomorphic to such a quotient. The gap is closed by transporting
ind-étale algebras along an isomorphism of base rings, which is possible because the object
property defining them is the inverse image of itself along restriction of scalars and
`CategoryTheory.ObjectProperty.ind` commutes with inverse image along an equivalence.

## References

* [Stacks Project, Tag 097P](https://stacks.math.columbia.edu/tag/097P)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProEtale

/-- **Ind-étaleness through restriction of scalars along an isomorphism.** Restricting an
algebra along an isomorphism of base rings does not change whether it is a filtered colimit of
étale algebras. -/
public theorem ind_underObj_map_iff {A B : CommRingCat.{u}} (E : A ⟶ B) [IsIso E]
    (f : Under B) :
    ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := A)) ((Under.map E).obj f) ↔
      ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := B)) f := by
  have h : (CommRingCat.etale.{u}.underObj (X := A)).inverseImage (Under.map E) =
      CommRingCat.etale.{u}.underObj (X := B) := by
    ext g
    exact CommRingCat.etale.cancel_left_of_respectsIso E g.hom
  rw [← h, ObjectProperty.ind_inverseImage_eq_of_isEquivalence]
  exact Iff.rfl

/-- **Extension of scalars on a morphism of algebras, read through `Spec`.** Composing the
description of a pushout with the structure map coming from the algebra is the structure map
coming from the other algebra followed by the morphism. -/
public theorem specMap_pushout_desc_inl {A C C' B : CommRingCat.{u}} (f : A ⟶ C) (f' : A ⟶ C')
    (φ : A ⟶ B) (ψ : C' ⟶ C)
    (w : f' ≫ ψ ≫ pushout.inl f φ = φ ≫ pushout.inr f φ) :
    Spec.map (pushout.desc (ψ ≫ pushout.inl f φ) (pushout.inr f φ) w) ≫
        Spec.map (pushout.inl f' φ) =
      Spec.map (pushout.inl f φ) ≫ Spec.map ψ := by
  rw [← Spec.map_comp, ← Spec.map_comp, pushout.inl_desc]

/-- Composing the description of a pushout with the structure map coming from the base change
is again that structure map. -/
public theorem specMap_pushout_desc_inr {A C C' B : CommRingCat.{u}} (f : A ⟶ C) (f' : A ⟶ C')
    (φ : A ⟶ B) (ψ : C' ⟶ C)
    (w : f' ≫ ψ ≫ pushout.inl f φ = φ ≫ pushout.inr f φ) :
    Spec.map (pushout.desc (ψ ≫ pushout.inl f φ) (pushout.inr f φ) w) ≫
        Spec.map (pushout.inr f' φ) =
      Spec.map (pushout.inr f φ) := by
  rw [← Spec.map_comp, pushout.inr_desc]

section Transport

variable {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)

/-- Restriction of scalars along the inverse of an isomorphism of base rings, as a functor
between the categories of ind-étale algebras. -/
public noncomputable def indEtaleAlgebraTransportFunctor :
    IndEtaleAlgebra A ⥤ IndEtaleAlgebra B :=
  (ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
    (X := CommRingCat.of B))).lift
    (ObjectProperty.ι _ ⋙ Under.map e.toCommRingCatIso.inv)
    (fun f ↦ (ind_underObj_map_iff e.toCommRingCatIso.inv f.obj).mpr f.property)

/-- The transport of an ind-étale algebra along an isomorphism of base rings has the same
underlying ring. -/
public theorem indEtaleAlgebraTransportFunctor_obj_right (V : IndEtaleAlgebra A) :
    ((indEtaleAlgebraTransportFunctor e).obj V).obj.right = V.obj.right :=
  rfl

/-- Transport of ind-étale algebras along an isomorphism of base rings is faithful. -/
instance : (indEtaleAlgebraTransportFunctor e).Faithful :=
  Functor.Faithful.of_comp_eq (G := ObjectProperty.ι _)
    (F := indEtaleAlgebraTransportFunctor e)
    (H := ObjectProperty.ι _ ⋙ Under.map e.toCommRingCatIso.inv) rfl

/-- Transport of ind-étale algebras along an isomorphism of base rings is full. -/
instance : (indEtaleAlgebraTransportFunctor e).Full :=
  Functor.Full.of_comp_faithful_iso (G := ObjectProperty.ι _)
    (F := indEtaleAlgebraTransportFunctor e)
    (H := ObjectProperty.ι _ ⋙ Under.map e.toCommRingCatIso.inv) (Iso.refl _)

/-- Transport of ind-étale algebras along an isomorphism of base rings is essentially
surjective. -/
instance : (indEtaleAlgebraTransportFunctor e).EssSurj where
  mem_essImage V := by
    refine ⟨⟨(Under.map e.toCommRingCatIso.hom).obj V.obj,
      (ind_underObj_map_iff e.toCommRingCatIso.hom V.obj).mpr V.property⟩, ⟨?_⟩⟩
    refine ObjectProperty.isoMk _ (Under.isoMk (Iso.refl _) ?_)
    change (e.toCommRingCatIso.inv ≫ e.toCommRingCatIso.hom ≫ V.obj.hom) ≫ 𝟙 _ = V.obj.hom
    rw [e.toCommRingCatIso.inv_hom_id_assoc, Category.comp_id]

/-- Transport of ind-étale algebras along an isomorphism of base rings is an equivalence. -/
instance : (indEtaleAlgebraTransportFunctor e).IsEquivalence where

/-- **Transport of ind-étale algebras along an isomorphism of base rings.** An isomorphism
`A ≃+* B` induces an equivalence between the category of ind-étale `A`-algebras and the
category of ind-étale `B`-algebras. -/
public noncomputable def indEtaleAlgebraTransport : IndEtaleAlgebra A ≌ IndEtaleAlgebra B :=
  (indEtaleAlgebraTransportFunctor e).asEquivalence

end Transport

section Surjection

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
  (hφ : Function.Surjective φ)

/-- The isomorphism of the quotient by the kernel of a surjection with its target, read in the
category of commutative rings. -/
public noncomputable def kerQuotIso :
    CommRingCat.of (A ⧸ RingHom.ker φ) ≅ CommRingCat.of B :=
  (φ.quotientKerEquivOfSurjective hφ).toCommRingCatIso

/-- A surjection factors as the quotient map onto the quotient by its kernel followed by the
induced isomorphism. -/
public theorem quotientMk_comp_kerQuotIso :
    CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ)) ≫ (kerQuotIso φ hφ).hom =
      CommRingCat.ofHom φ := by
  ext a
  exact φ.quotientKerEquivOfSurjective_apply_mk hφ a

/-- Restriction of scalars along a surjection is restriction along the isomorphism onto the
quotient by its kernel followed by restriction along the quotient map. -/
public theorem map_kerQuotIso_comp :
    Under.map (kerQuotIso φ hφ).hom ⋙
        Under.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ))) =
      Under.map (CommRingCat.ofHom φ) := by
  rw [← Under.mapComp_eq, quotientMk_comp_kerQuotIso]

/-- Extension of scalars along the quotient map followed by restriction of scalars along the
inverse of the induced isomorphism, as a left adjoint to restriction of scalars along the
surjection. -/
public noncomputable def pushoutSurjectiveAdj :
    Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ))) ⋙
        Under.map (kerQuotIso φ hφ).inv ⊣
      Under.map (CommRingCat.ofHom φ) :=
  ((Under.mapPushoutAdj
      (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ)))).comp
    (Under.mapIso (kerQuotIso φ hφ)).symm.toAdjunction).ofNatIsoRight
    (eqToIso (map_kerQuotIso_comp φ hφ))

/-- Extension of scalars along a surjection is extension of scalars along the quotient by its
kernel followed by restriction along the induced isomorphism, read on the categories of all
algebras under the base ring. -/
public noncomputable def pushoutSurjectiveIso :
    Under.pushout (CommRingCat.ofHom φ) ≅
      Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ))) ⋙
        Under.map (kerQuotIso φ hφ).inv :=
  (Under.mapPushoutAdj (CommRingCat.ofHom φ)).leftAdjointUniq (pushoutSurjectiveAdj φ hφ)

/-- **Extension of scalars along a surjection factors through the quotient by its kernel.** -/
public noncomputable def indEtaleAlgebraBaseChange_surjectiveIso :
    indEtaleAlgebraBaseChange φ ≅
      indEtaleQuotientBaseChange A (RingHom.ker φ) ⋙
        indEtaleAlgebraTransportFunctor (φ.quotientKerEquivOfSurjective hφ) :=
  NatIso.ofComponents
    (fun V ↦ ObjectProperty.isoMk _ ((pushoutSurjectiveIso φ hφ).app V.obj))
    (fun f ↦ ObjectProperty.hom_ext _ ((pushoutSurjectiveIso φ hφ).hom.naturality f.hom))

/-- **Extension of scalars along a surjection has a fully faithful right adjoint.** This is the
form of Stacks 097P needed when the quotient is presented as an abstract surjection, as happens
for the ring of global sections of a closed subscheme. -/
public noncomputable def indEtaleAlgebraBaseChange_rightAdjoint :
    IndEtaleAlgebra B ⥤ IndEtaleAlgebra A :=
  (indEtaleAlgebraTransport (φ.quotientKerEquivOfSurjective hφ)).inverse ⋙
    indEtaleQuotientLift A (RingHom.ker φ)

/-- The right adjoint of extension of scalars along a surjection is fully faithful. -/
public theorem indEtaleAlgebraBaseChange_rightAdjoint_fullyFaithful :
    Nonempty (indEtaleAlgebraBaseChange_rightAdjoint φ hφ).FullyFaithful := by
  obtain ⟨hl⟩ := indEtaleQuotientLift_fullyFaithful A (RingHom.ker φ)
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful (indEtaleAlgebraTransport
    (φ.quotientKerEquivOfSurjective hφ)).inverse).comp hl⟩

/-- **Stacks 097P for a surjection.** Extension of scalars along a surjection of commutative
rings is left adjoint to a fully faithful functor. -/
public theorem indEtaleAlgebraBaseChange_hasFullyFaithfulRightAdjoint :
    Nonempty (indEtaleAlgebraBaseChange φ ⊣ indEtaleAlgebraBaseChange_rightAdjoint φ hφ) := by
  obtain ⟨adj⟩ := indEtaleBaseChange_hasFullyFaithfulRightAdjoint A (RingHom.ker φ)
  exact ⟨(adj.comp (indEtaleAlgebraTransport
    (φ.quotientKerEquivOfSurjective hφ)).toAdjunction).ofNatIsoLeft
    (indEtaleAlgebraBaseChange_surjectiveIso φ hφ).symm⟩

end Surjection

section GlobalSections

variable {X : Scheme.{u}}

/-- The scheme underlying an object of `X_app` is affine. -/
instance isAffine_obj_left (U : AppSmallProetale X) : IsAffine U.obj.left :=
  U.property.1

/-- The image under the identity functor of the scheme underlying an object of `X_app` is
affine. -/
instance isAffine_id_obj_left (U : AppSmallProetale X) :
    IsAffine ((𝟭 Scheme.{u}).obj U.obj.left) :=
  U.property.1

/-- The underlying morphism of schemes of a composite in `X_app`. -/
public theorem appProetale_comp_hom_left {U U' U'' : AppSmallProetale X} (a : U ⟶ U')
    (b : U' ⟶ U'') :
    (a ≫ b).hom.left = a.hom.left ≫ b.hom.left :=
  rfl

/-- The ind-étale algebra over the global sections of `X` determined by an object of `X_app`. -/
public noncomputable def appAlg (U : AppSmallProetale X) : IndEtaleAlgebra Γ(X, ⊤) :=
  ⟨Under.mk U.obj.hom.appTop,
    (@indEtale_iff_ind_underObj _ _ _ _ U.obj.hom.appTop.hom.toAlgebra).mp U.property.2⟩

/-- The triangle expressing that a morphism of `X_app` is a morphism of algebras over the
global sections of `X`. -/
public theorem appAlg_w {U U' : AppSmallProetale X} (h : U ⟶ U') :
    U'.obj.hom.appTop ≫ h.hom.left.appTop = U.obj.hom.appTop := by
  rw [← Scheme.Hom.comp_appTop, MorphismProperty.Over.w h.hom]

/-- Global sections of a morphism of `X_app`, as a morphism of ind-étale algebras over the
global sections of `X`. -/
public noncomputable def appAlgMap {U U' : AppSmallProetale X} (h : U ⟶ U') :
    appAlg U' ⟶ appAlg U :=
  ObjectProperty.homMk (Under.homMk h.hom.left.appTop (appAlg_w h))

/-- **Global sections on the site of ind-étale affines.** Taking global sections is a functor
from `X_app` to the opposite of the category of ind-étale algebras over the global sections of
`X`; it is inverse to `AlgebraicGeometry.ProEtale.appSpec`. -/
public noncomputable def appAlgOp : AppSmallProetale X ⥤ (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ where
  obj U := op (appAlg U)
  map h := (appAlgMap h).op
  map_id _ := rfl
  map_comp _ _ := rfl

variable [IsAffine X]

/-- Taking `Spec` of the global sections of an object of `X_app` recovers that object. -/
public noncomputable def appSpecAppAlgIso (U : AppSmallProetale X) :
    (appSpec X).obj (op (appAlg U)) ≅ U :=
  ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk U.obj.left.isoSpec.symm
    (Scheme.isoSpec_inv_naturality (X := U.obj.left) (Y := X) U.obj.hom).symm)

/-- **Global sections and `Spec` are inverse on the site of ind-étale affines.** -/
public noncomputable def appAlgOpCompAppSpec : appAlgOp ⋙ appSpec X ≅ 𝟭 (AppSmallProetale X) :=
  NatIso.ofComponents appSpecAppAlgIso (fun {U U'} h ↦
    ObjectProperty.hom_ext _ (MorphismProperty.Over.Hom.ext (by
      change Spec.map h.hom.left.appTop ≫ U'.obj.left.isoSpec.inv =
        U.obj.left.isoSpec.inv ≫ h.hom.left
      exact Scheme.isoSpec_inv_naturality h.hom.left)))

/-- Global sections is the inverse of the equivalence given by `Spec`. -/
public noncomputable def appAlgOpIso : appAlgOp ≅ (appSpecEquivalence X).inverse :=
  calc appAlgOp
      ≅ appAlgOp ⋙ 𝟭 _ := (Functor.rightUnitor _).symm
    _ ≅ appAlgOp ⋙ appSpec X ⋙ (appSpecEquivalence X).inverse :=
          Functor.isoWhiskerLeft _ (appSpecEquivalence X).unitIso
    _ ≅ (appAlgOp ⋙ appSpec X) ⋙ (appSpecEquivalence X).inverse := (Functor.associator _ _ _).symm
    _ ≅ 𝟭 _ ⋙ (appSpecEquivalence X).inverse :=
          Functor.isoWhiskerRight appAlgOpCompAppSpec _
    _ ≅ (appSpecEquivalence X).inverse := Functor.leftUnitor _

/-- Global sections is an equivalence from `X_app` to the opposite of the category of ind-étale
algebras over the global sections of `X`. -/
instance : appAlgOp.IsEquivalence (C := AppSmallProetale X) :=
  Functor.isEquivalence_of_iso (appAlgOpIso (X := X)).symm

/-- **`Spec` is right adjoint to global sections on the site of ind-étale affines.** -/
public noncomputable def appSpecAppAlgOpAdjunction : appSpec X ⊣ appAlgOp :=
  (appSpecEquivalence X).toAdjunction.ofNatIsoRight appAlgOpIso.symm

end GlobalSections

section Pushout

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- The compatibility exhibiting extension of scalars on a morphism of `X_app` as a pushout
description. -/
public theorem appAlg_pushout_w {U U' : AppSmallProetale X} (h : U ⟶ U') :
    U'.obj.hom.appTop ≫ h.hom.left.appTop ≫ pushout.inl U.obj.hom.appTop i.appTop =
      i.appTop ≫ pushout.inr U.obj.hom.appTop i.appTop := by
  rw [← Category.assoc, appAlg_w h]
  exact pushout.condition

section
variable [IsAffine Z]

/-- Extension of scalars on a morphism of `X_app` commutes with the structure map of the
pushout coming from `U`. -/
public theorem appSpecBaseChange_map_left_inl {U U' : AppSmallProetale X} (h : U ⟶ U') :
    ((appAlgOp ⋙ (indEtaleAlgebraBaseChange i.appTop.hom).op ⋙ appSpec Z).map h).hom.left ≫
        Spec.map (pushout.inl U'.obj.hom.appTop i.appTop) =
      Spec.map (pushout.inl U.obj.hom.appTop i.appTop) ≫ Spec.map h.hom.left.appTop :=
  specMap_pushout_desc_inl U.obj.hom.appTop U'.obj.hom.appTop i.appTop h.hom.left.appTop
    (appAlg_pushout_w i h)

/-- Extension of scalars on a morphism of `X_app` commutes with the structure map of the
pushout coming from `Z`. -/
public theorem appSpecBaseChange_map_left_inr {U U' : AppSmallProetale X} (h : U ⟶ U') :
    ((appAlgOp ⋙ (indEtaleAlgebraBaseChange i.appTop.hom).op ⋙ appSpec Z).map h).hom.left ≫
        Spec.map (pushout.inr U'.obj.hom.appTop i.appTop) =
      Spec.map (pushout.inr U.obj.hom.appTop i.appTop) :=
  specMap_pushout_desc_inr U.obj.hom.appTop U'.obj.hom.appTop i.appTop h.hom.left.appTop
    (appAlg_pushout_w i h)

end

end Pushout

section BaseChange

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X)

/-- **The fibre product of affine schemes is the spectrum of the pushout of global sections.**
For affine `U`, `X` and `Z` and morphisms `g : U ⟶ X` and `i : Z ⟶ X`, the spectrum of the
pushout of `𝒪(X) → 𝒪(U)` along `𝒪(X) → 𝒪(Z)` is the fibre product `U ×_X Z`. -/
public theorem isPullback_specMap_pushout_appTop {U : Scheme.{u}} [IsAffine U] (g : U ⟶ X) :
    IsPullback (Spec.map (pushout.inl g.appTop i.appTop) ≫ U.isoSpec.inv)
      (Spec.map (pushout.inr g.appTop i.appTop) ≫ Z.isoSpec.inv) g i :=
  (isPullback_SpecMap_pushout g.appTop i.appTop).of_iso' (Iso.refl _) U.isoSpec Z.isoSpec
    X.isoSpec (by simp) (by simp) (Scheme.isoSpec_hom_naturality g)
    (Scheme.isoSpec_hom_naturality i)

/-- **Naturality of the identification of a fibre product of affine schemes with the spectrum
of a pushout.** For `k : U ⟶ U'` over `X`, the description of the pushout induced by the
global sections of `k` corresponds to the morphism of fibre products induced by `k`. -/
public theorem isoPullback_specMap_pushout_naturality {U U' : Scheme.{u}} [IsAffine U]
    [IsAffine U'] (g : U ⟶ X) (g' : U' ⟶ X) (k : U ⟶ U') (hk : k ≫ g' = g)
    (w : g'.appTop ≫ k.appTop ≫ pushout.inl g.appTop i.appTop =
      i.appTop ≫ pushout.inr g.appTop i.appTop) :
    Spec.map (pushout.desc (k.appTop ≫ pushout.inl g.appTop i.appTop)
          (pushout.inr g.appTop i.appTop) w) ≫
        (isPullback_specMap_pushout_appTop i g').isoPullback.hom =
      (isPullback_specMap_pushout_appTop i g).isoPullback.hom ≫
        pullback.lift (pullback.fst g i ≫ k) (pullback.snd g i)
          (by rw [Category.assoc, hk]; exact pullback.condition) := by
  have h1 := specMap_pushout_desc_inl g.appTop g'.appTop i.appTop k.appTop w
  have h2 := specMap_pushout_desc_inr g.appTop g'.appTop i.appTop k.appTop w
  refine pullback.hom_ext ?_ ?_
  · conv_lhs => rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc, h1,
      Category.assoc, Scheme.isoSpec_inv_naturality]
    conv_rhs => rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
      IsPullback.isoPullback_hom_fst, Category.assoc]
  · conv_lhs => rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Category.assoc, h2]
    conv_rhs => rw [Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd]

/-- The ind-étale algebra over the global sections of `Z` obtained from an object of `X_app` by
extension of scalars along `𝒪(X) → 𝒪(Z)`. -/
public noncomputable abbrev bcAlg (U : AppSmallProetale X) : IndEtaleAlgebra Γ(Z, ⊤) :=
  (indEtaleAlgebraBaseChange i.appTop.hom).obj (appAlg U)

/-- Base change along `i` as a functor from `X_app` to the small pro-étale site of `Z`. -/
public noncomputable def appBaseChangeProEt : AppSmallProetale X ⥤ Z.ProEt :=
  MorphismProperty.Comma.lift
    (AppSmallProetale.inclusion X ⋙ Scheme.ProEt.forget X ⋙ Over.pullback i)
    (fun U ↦ by
      have : IsAffine ((𝟭 Scheme.{u}).obj U.obj.left) := U.property.1
      exact inferInstanceAs (WeaklyEtale (pullback.snd U.obj.hom i)))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- The comparison in the small pro-étale site of `Z` between the spectrum of the extension of
scalars of the global sections of `U` and the fibre product `U ×_X Z`. -/
public noncomputable def appBaseChangeProEtIso (U : AppSmallProetale X) :
    (appSpecProEt Z).obj (op (bcAlg i U)) ≅ (appBaseChangeProEt i).obj U :=
  MorphismProperty.Over.isoMk (isPullback_specMap_pushout_appTop i U.obj.hom).isoPullback
    (IsPullback.isoPullback_hom_snd _)

/-- The fibre product of an object of `X_app` with `Z` over `X` is an object of `Z_app`. -/
public theorem isAppSmall_appBaseChangeProEt (U : AppSmallProetale X) :
    IsAppSmall Z ((appBaseChangeProEt i).obj U) :=
  ObjectProperty.prop_of_iso _ (appBaseChangeProEtIso i U)
    (isAppSmall_appSpecProEt Z (op (bcAlg i U)))

/-- **The base change functor.** For a morphism `i : Z ⟶ X` of affine schemes,
pulling back along `i` carries an affine object of the small pro-étale site of `X` with
ind-étale ring of global sections to one over `Z`, giving a functor `X_app ⥤ Z_app`,
`U ↦ U ×_X Z`. -/
@[stacks 09BK "the base change functor"]
public noncomputable def appProetaleBaseChange : AppSmallProetale X ⥤ AppSmallProetale Z :=
  (IsAppSmall Z).lift (appBaseChangeProEt i) (isAppSmall_appBaseChangeProEt i)

/-- The scheme underlying the base change of an object of `X_app` is the fibre product. -/
public theorem appProetaleBaseChange_obj_left (U : AppSmallProetale X) :
    ((appProetaleBaseChange i).obj U).obj.left = pullback U.obj.hom i :=
  rfl

/-- The structure morphism of the base change of an object of `X_app` is the second projection
of the fibre product. -/
public theorem appProetaleBaseChange_obj_hom (U : AppSmallProetale X) :
    ((appProetaleBaseChange i).obj U).obj.hom = pullback.snd U.obj.hom i :=
  rfl

/-- The comparison in `Z_app` between the spectrum of the extension of scalars of the global
sections of an object of `X_app` and its fibre product with `Z` over `X`. -/
public noncomputable def appBaseChangeIso (U : AppSmallProetale X) :
    (appSpec Z).obj (op (bcAlg i U)) ≅ (appProetaleBaseChange i).obj U :=
  ObjectProperty.isoMk _ (appBaseChangeProEtIso i U)

/-- The underlying morphism of schemes of the comparison isomorphism. -/
public theorem appBaseChangeIso_hom_left (U : AppSmallProetale X) :
    (appBaseChangeIso i U).hom.hom.left =
      (isPullback_specMap_pushout_appTop i U.obj.hom).isoPullback.hom :=
  rfl

/-- The base change of a morphism of `X_app` commutes with the first projection. -/
public theorem appProetaleBaseChange_map_left_fst {U U' : AppSmallProetale X} (h : U ⟶ U') :
    ((appProetaleBaseChange i).map h).hom.left ≫ pullback.fst U'.obj.hom i =
      pullback.fst U.obj.hom i ≫ h.hom.left := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- The base change of a morphism of `X_app` is a morphism over `Z`. -/
public theorem appProetaleBaseChange_map_left_snd {U U' : AppSmallProetale X} (h : U ⟶ U') :
    ((appProetaleBaseChange i).map h).hom.left ≫ pullback.snd U'.obj.hom i =
      pullback.snd U.obj.hom i := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

/-- **Base change on the sites is extension of scalars on ind-étale algebras.** The functor
`U ↦ U ×_X Z` of Stacks 09BK corresponds, under the identification of each site with the
opposite of a category of ind-étale algebras, to extension of scalars along `𝒪(X) → 𝒪(Z)`. -/
public noncomputable def appProetaleBaseChangeIso :
    appAlgOp ⋙ (indEtaleAlgebraBaseChange i.appTop.hom).op ⋙ appSpec Z ≅
      appProetaleBaseChange i :=
  NatIso.ofComponents (appBaseChangeIso i) (fun {U U'} h ↦
    ObjectProperty.hom_ext _ (MorphismProperty.Over.Hom.ext
      (isoPullback_specMap_pushout_naturality i U.obj.hom U'.obj.hom h.hom.left
        (MorphismProperty.Over.w h.hom) (appAlg_pushout_w i h))))

end BaseChange

section ClosedImmersion

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The closed immersion `V → v(V)`.** The first projection of the fibre product
`U ×_X Z` is a closed immersion, being the base change of `i`; combined with the identification
of `V` with `v(V) ×_X Z` this exhibits `V → v(V)` as a closed immersion. -/
@[stacks 09BK "the closed immersion V → v(V)"]
public theorem isClosedImmersion_pullback_fst (U : AppSmallProetale X) :
    IsClosedImmersion (pullback.fst U.obj.hom i) :=
  inferInstance

variable [IsAffine X]

/-- The global sections of a closed immersion with affine target form a surjection. -/
public theorem surjective_appTop_hom : Function.Surjective i.appTop.hom :=
  Stacks.Pushout.surjective_appTop_of_isClosedImmersion i

variable [IsAffine Z]

/-- **The left adjoint `v` of base change.** For a closed immersion `i : Z ⟶ X` of affine
schemes, the lift of an object of `Z_app` to `X_app`: it is the right-adjoint lift of
Stacks 097P on ind-étale algebras, read through the identification of each site with the
opposite of a category of ind-étale algebras. -/
@[stacks 09BK "the left adjoint"]
public noncomputable def appProetaleLift : AppSmallProetale Z ⥤ AppSmallProetale X :=
  (appSpecEquivalence Z).inverse ⋙
    (indEtaleAlgebraBaseChange_rightAdjoint i.appTop.hom (surjective_appTop_hom i)).op ⋙
      appSpec X

/-- **The adjunction.** The base change functor `U ↦ U ×_X Z` along a closed
immersion of affine schemes has a left adjoint. -/
@[stacks 09BK "the adjunction"]
public theorem appProetaleBaseChange_hasLeftAdjoint :
    Nonempty (appProetaleLift i ⊣ appProetaleBaseChange i) := by
  obtain ⟨adj⟩ :=
    indEtaleAlgebraBaseChange_hasFullyFaithfulRightAdjoint i.appTop.hom (surjective_appTop_hom i)
  exact ⟨((((appSpecEquivalence Z).symm.toAdjunction.comp adj.op).comp
    (appSpecAppAlgOpAdjunction (X := X))).ofNatIsoRight (appProetaleBaseChangeIso i))⟩

/-- **Full faithfulness of the left adjoint.** -/
@[stacks 09BK "full faithfulness of the left adjoint"]
public theorem appProetaleLift_fullyFaithful :
    Nonempty (appProetaleLift i).FullyFaithful := by
  obtain ⟨hR⟩ := indEtaleAlgebraBaseChange_rightAdjoint_fullyFaithful i.appTop.hom
    (surjective_appTop_hom i)
  exact ⟨((Functor.FullyFaithful.ofFullyFaithful (appSpecEquivalence Z).inverse).comp
    hR.op).comp (Functor.FullyFaithful.ofFullyFaithful (appSpec X))⟩

/-- **The identification of `V` with `u(v(V))`.** For `V` in `Z_app` the unit of
the adjunction identifies `V` with the fibre product `v(V) ×_X Z`. -/
@[stacks 09BK "the identification of V with u(v(V))"]
public theorem appProetaleLift_baseChangeIso :
    Nonempty (𝟭 (AppSmallProetale Z) ≅ appProetaleLift i ⋙ appProetaleBaseChange i) := by
  obtain ⟨adj⟩ := appProetaleBaseChange_hasLeftAdjoint i
  obtain ⟨hv⟩ := appProetaleLift_fullyFaithful i
  have : (appProetaleLift i).Full := hv.full
  have : (appProetaleLift i).Faithful := hv.faithful
  exact ⟨asIso adj.unit⟩

end ClosedImmersion

end AlgebraicGeometry.ProEtale

end
