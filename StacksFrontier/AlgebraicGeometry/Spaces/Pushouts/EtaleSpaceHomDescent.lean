module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairCechDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleInverseImageUnitors

/-!
# Descent of morphisms between spaces étale over the target

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` along which descent of sheaves on the
spaces-étale sites is effective, i.e. the comparison functor of
`AlgebraicGeometry.Space.spacesEtalePseudofunctor` from sheaves on `X` to descent data for the
one-member family `{f}` is an equivalence. For algebraic spaces `V`, `W` étale over `X`, the
morphisms `V ⟶ W` over `X` are then exactly the morphisms of the fibre descent data
`Y ×_X V ⟶ Y ×_X W` relative to `f`. This is the fully faithful half of the étale descent of
algebraic spaces (Stacks 0GG0).

The proof is the passage through the Yoneda embedding of the spaces-étale site. The objects
`V`, `W` of that site represent sheaves `h_V`, `h_W`, and morphisms `V ⟶ W` are morphisms
`h_V ⟶ h_W` because the spaces-étale topology is subcanonical. The inverse image along a
morphism `g` of the sheaf represented by `V` is the sheaf represented by the base change
`g^* V` (Stacks 04D3, `AlgebraicGeometry.Space.baseChangeYonedaIso`), compatibly with the
composition isomorphisms
(`AlgebraicGeometry.Space.spacesEtaleInverseImage_comp_inv_app_comp_baseChangeYonedaIso_hom`).
So a morphism `ψ` of fibre descent data, which is a morphism `Y ×_X V ⟶ Y ×_X W` over `Y`
commuting with the move operations, gives a morphism `f⁻¹ h_V ⟶ f⁻¹ h_W` whose pullbacks along
any two maps `f₁, f₂ : Y' ⟶ Y` with `f₁ ≫ f = f₂ ≫ f` are identified by the descent data of the
two sheaves (`AlgebraicGeometry.Space.SpacesEtaleHomDescent.descentHom`). Full faithfulness of
the comparison functor then hands back a morphism `h_V ⟶ h_W`, hence a morphism `V ⟶ W`.

## Main results

* `AlgebraicGeometry.Space.bijective_fibreDescentMap_of_isEquivalence`: the statement above.
* `AlgebraicGeometry.Space.EtaleSpaceHomDescentAlongProperSurjective`: descent of morphisms of
  spaces étale over the target of a proper surjective morphism.
* `AlgebraicGeometry.Space.etaleSpaceHomDescentAlongProperSurjective_of_descentEffective`: it
  follows from the proper case of Stacks 0GFW,
  `AlgebraicGeometry.Space.DescentEffectiveAlongProperSurjective`.

## References

* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
* [Stacks Project, Tag 0GFW](https://stacks.math.columbia.edu/tag/0GFW)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace SpacesEtaleHomDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_EtaleSpaceHomDescent
    {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Spaces étale over `X` as objects of the spaces-étale site -/

/-- An algebraic space over `X` whose structure morphism is étale, as an object of the
spaces-étale site of `X`. -/
def siteObj (V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj)
    (hV : IsEtale B S hS V.obj.hom) : SpacesEtale B S hS X :=
  ⟨Over.mk (ObjectProperty.homMk V.obj.hom :
    (⟨V.obj.left, V.property⟩ : AlgebraicSpaces B S hS) ⟶ X), hV⟩

variable {V W : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj}
  (hV : IsEtale B S hS V.obj.hom) (hW : IsEtale B S hS W.obj.hom)

/-- A morphism of algebraic spaces over `X`, as a morphism of the spaces-étale site. -/
def siteMap (φ : V ⟶ W) : siteObj V hV ⟶ siteObj W hW :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk φ.hom.left)
    (ObjectProperty.hom_ext _ (Over.w φ.hom)))

/-- A morphism of the spaces-étale site, as a morphism of algebraic spaces over `X`. -/
def ofSiteMap (g : siteObj V hV ⟶ siteObj W hW) : V ⟶ W :=
  ObjectProperty.homMk (Over.homMk g.hom.left.hom (congrArg (fun k => k.hom) (Over.w g.hom)))

/-- `siteMap` is a left inverse of `ofSiteMap`. -/
theorem siteMap_ofSiteMap (g : siteObj V hV ⟶ siteObj W hW) :
    siteMap hV hW (ofSiteMap hV hW g) = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl))

/-- Distinct morphisms over `X` give distinct morphisms of the spaces-étale site. -/
theorem siteMap_injective : Function.Injective (siteMap hV hW) := fun _ _ h =>
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (congrArg (fun k => k.hom.left.hom) h))

/-! ### Base change on the site and fibre products of presheaves -/

variable (f : Y ⟶ X)

/-- The base change of `V` along `f` on the spaces-étale site has, as underlying presheaf, the
fibre product `V ×_X Y` of presheaves. -/
def baseChangeIso (V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj)
    (hV : IsEtale B S hS V.obj.hom) :
    ((spacesBaseChange B S hS f).functor.obj (siteObj V hV)).obj.left.obj ≅
      pullback V.obj.hom f.hom :=
  (AlgebraicSpaces.isPullback_hom B S hS
    ((spacesBaseChange B S hS f).isPullback (siteObj V hV))).isoPullback

/-- `baseChangeIso` followed by the first projection is the projection of the base change. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst :
    (baseChangeIso f V hV).hom ≫ pullback.fst V.obj.hom f.hom =
      ((spacesBaseChange B S hS f).projection.app (siteObj V hV)).hom :=
  IsPullback.isoPullback_hom_fst _

/-- `baseChangeIso` followed by the second projection is the structure morphism of the base
change over `Y`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd :
    (baseChangeIso f V hV).hom ≫ pullback.snd V.obj.hom f.hom =
      ((spacesBaseChange B S hS f).functor.obj (siteObj V hV)).obj.hom.hom :=
  IsPullback.isoPullback_hom_snd _

/-- The inverse of `baseChangeIso` followed by the projection of the base change is the first
projection. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_inv_fst :
    (baseChangeIso f V hV).inv ≫ ((spacesBaseChange B S hS f).projection.app (siteObj V hV)).hom =
      pullback.fst V.obj.hom f.hom :=
  IsPullback.isoPullback_inv_fst _

/-- The inverse of `baseChangeIso` followed by the structure morphism of the base change over `Y`
is the second projection. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_inv_snd :
    (baseChangeIso f V hV).inv ≫
        ((spacesBaseChange B S hS f).functor.obj (siteObj V hV)).obj.hom.hom =
      pullback.snd V.obj.hom f.hom :=
  IsPullback.isoPullback_inv_snd _

/-- A morphism `Y ×_X V ⟶ Y ×_X W` of fibre components over `Y`, as a morphism of the base
changes of `V` and `W` on the spaces-étale site of `Y`. -/
def transfer (ψ : Descent.fibreComponent (fun _ : PUnit.{1} => f.hom) V.obj PUnit.unit ⟶
      Descent.fibreComponent (fun _ : PUnit.{1} => f.hom) W.obj PUnit.unit) :
    (spacesBaseChange B S hS f).functor.obj (siteObj V hV) ⟶
      (spacesBaseChange B S hS f).functor.obj (siteObj W hW) :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
    ((baseChangeIso f V hV).hom ≫ ψ.left ≫ (baseChangeIso f W hW).inv))
    (ObjectProperty.hom_ext _ (by
      change ((baseChangeIso f V hV).hom ≫ ψ.left ≫ (baseChangeIso f W hW).inv) ≫
          ((spacesBaseChange B S hS f).functor.obj (siteObj W hW)).obj.hom.hom =
        ((spacesBaseChange B S hS f).functor.obj (siteObj V hV)).obj.hom.hom
      have hψ : ψ.left ≫ pullback.snd W.obj.hom f.hom = pullback.snd V.obj.hom f.hom := Over.w ψ
      simp only [Category.assoc, baseChangeIso_inv_snd, hψ, baseChangeIso_hom_snd])))

/-- The underlying morphism of `transfer ψ` is `ψ` conjugated by `baseChangeIso`. -/
theorem transfer_hom_left_hom (ψ : Descent.fibreComponent (fun _ : PUnit.{1} => f.hom) V.obj
      PUnit.unit ⟶ Descent.fibreComponent (fun _ : PUnit.{1} => f.hom) W.obj PUnit.unit) :
    (transfer hV hW f ψ).hom.left.hom =
      (baseChangeIso f V hV).hom ≫ ψ.left ≫ (baseChangeIso f W hW).inv :=
  rfl

/-- Distinct morphisms of fibre components give distinct morphisms of base changes. -/
theorem transfer_injective :
    Function.Injective (transfer (V := V) (W := W) hV hW f) := by
  intro ψ ψ' h
  have h1 := congrArg (fun k => k.hom.left.hom) h
  rw [transfer_hom_left_hom, transfer_hom_left_hom] at h1
  exact Over.OverMorphism.ext
    ((Iso.cancel_iso_inv_right _ _ _).1 ((Iso.cancel_iso_hom_left _ _ _).1 h1))

/-- The projection of a base change is natural in the object. -/
theorem baseChange_map_projection {T T' : AlgebraicSpaces B S hS} (k : T ⟶ T')
    {A A' : SpacesEtale B S hS T'} (g : A ⟶ A') :
    ((spacesBaseChange B S hS k).functor.map g).hom.left ≫
        (spacesBaseChange B S hS k).projection.app A' =
      (spacesBaseChange B S hS k).projection.app A ≫ g.hom.left :=
  (spacesBaseChange B S hS k).projection.naturality g

/-- The morphism of fibre components induced by a morphism `φ : V ⟶ W` is the base change of
`φ` on the spaces-étale site. -/
theorem transfer_fibreComponentMap (φ : V ⟶ W) :
    transfer hV hW f (Descent.fibreComponentMap (fun _ : PUnit.{1} => f.hom) φ.hom PUnit.unit) =
      (spacesBaseChange B S hS f).functor.map (siteMap hV hW φ) := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
  change (baseChangeIso f V hV).hom ≫
      (Descent.fibreComponentMap (fun _ : PUnit.{1} => f.hom) φ.hom PUnit.unit).left ≫
        (baseChangeIso f W hW).inv =
    ((spacesBaseChange B S hS f).functor.map (siteMap hV hW φ)).hom.left.hom
  rw [← Category.assoc, Iso.comp_inv_eq]
  apply pullback.hom_ext
  · simp only [Category.assoc, Descent.fibreComponentMap_left_fst, baseChangeIso_hom_fst_assoc,
      baseChangeIso_hom_fst]
    exact (congrArg (fun k => k.hom) (baseChange_map_projection f (siteMap hV hW φ))).symm
  · simp only [Category.assoc, Descent.fibreComponentMap_left_snd, baseChangeIso_hom_snd]
    exact (congrArg (fun k => k.hom)
      (Over.w ((spacesBaseChange B S hS f).functor.map (siteMap hV hW φ)).hom)).symm

/-! ### Two descriptions of a base change along a composite -/

section Composite

variable {T : AlgebraicSpaces B S hS} (q : T ⟶ X) (g : T ⟶ Y) (hg : g ≫ f = q)

include hg in
/-- For `g ≫ f = q`, the base change along `g` of the base change along `f` of `A` is a fibre
product of `A` and `T` over `X`, with the composite projection. -/
theorem isPullback_paste (A : SpacesEtale B S hS X) :
    IsPullback ((spacesBaseChange B S hS g).projection.app
        ((spacesBaseChange B S hS f).functor.obj A) ≫ (spacesBaseChange B S hS f).projection.app A)
      ((spacesBaseChange B S hS g).functor.obj ((spacesBaseChange B S hS f).functor.obj A)).obj.hom
      A.obj.hom q := by
  have h := ((spacesBaseChange B S hS g).isPullback
    ((spacesBaseChange B S hS f).functor.obj A)).paste_horiz
      ((spacesBaseChange B S hS f).isPullback A)
  rwa [hg] at h

include hg in
/-- The base change of `A` along `q = g ≫ f` is the base change along `g` of its base change
along `f`: both are fibre products of the same cospan, by pasting. -/
def compIso (A : SpacesEtale B S hS X) :
    (spacesBaseChange B S hS q).functor.obj A ≅
      (spacesBaseChange B S hS g).functor.obj ((spacesBaseChange B S hS f).functor.obj A) :=
  (IsEtaleOver B S hS T).isoMk (Over.isoMk
    (((spacesBaseChange B S hS q).isPullback A).isoIsPullback _ _ (isPullback_paste f q g hg A))
    (IsPullback.isoIsPullback_hom_snd _ _ _ _))

/-- `compIso` followed by the composite projection to `A` is the projection of the base change
along `q`. -/
theorem compIso_hom_fst (A : SpacesEtale B S hS X) :
    (compIso f q g hg A).hom.hom.left ≫
        (spacesBaseChange B S hS g).projection.app ((spacesBaseChange B S hS f).functor.obj A) ≫
          (spacesBaseChange B S hS f).projection.app A =
      (spacesBaseChange B S hS q).projection.app A :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The inverse of `compIso` followed by the projection of the base change along `q` is the
composite projection to `A`. -/
theorem compIso_inv_fst (A : SpacesEtale B S hS X) :
    (compIso f q g hg A).inv.hom.left ≫ (spacesBaseChange B S hS q).projection.app A =
      (spacesBaseChange B S hS g).projection.app ((spacesBaseChange B S hS f).functor.obj A) ≫
        (spacesBaseChange B S hS f).projection.app A :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

/-- For `q = g ≫ f` on the nose, the comparison is the inverse of the composition isomorphism
of the base changes of Stacks 03G2, part (2). -/
theorem compIso_self (A : SpacesEtale B S hS X) :
    (compIso f (g ≫ f) g rfl A).hom = ((spacesBaseChange_comp B S hS g f).app A).inv := by
  have h : (compIso f (g ≫ f) g rfl A).hom ≫ ((spacesBaseChange_comp B S hS g f).app A).hom =
      𝟙 _ := by
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext
      (((spacesBaseChange B S hS (g ≫ f)).isPullback A).hom_ext ?_ ?_))
    · change (compIso f (g ≫ f) g rfl A).hom.hom.left ≫
          ((spacesBaseChange_comp B S hS g f).hom.app A).hom.left ≫
            (spacesBaseChange B S hS (g ≫ f)).projection.app A =
        𝟙 _ ≫ (spacesBaseChange B S hS (g ≫ f)).projection.app A
      rw [spacesBaseChange_comp_projection, compIso_hom_fst, Category.id_comp]
    · exact (Over.w _).trans (Over.w _).symm
  calc (compIso f (g ≫ f) g rfl A).hom
      = (compIso f (g ≫ f) g rfl A).hom ≫ ((spacesBaseChange_comp B S hS g f).app A).hom ≫
          ((spacesBaseChange_comp B S hS g f).app A).inv := by simp
    _ = ((spacesBaseChange_comp B S hS g f).app A).inv := by
      rw [← Category.assoc, h, Category.id_comp]

/-- The inverse image along `g` of the inverse image along `f` of the sheaf represented by `A`
is the sheaf represented by the iterated base change. -/
abbrev pullIso (A : SpacesEtale B S hS X) :
    (spacesEtaleInverseImage B S hS g).obj ((spacesEtaleInverseImage B S hS f).obj
        ((SpacesEtale.topology B S hS X).yoneda.obj A)) ≅
      (SpacesEtale.topology B S hS T).yoneda.obj
        ((spacesBaseChange B S hS g).functor.obj ((spacesBaseChange B S hS f).functor.obj A)) :=
  (spacesEtaleInverseImage B S hS g).mapIso (baseChangeYonedaIso B S hS f A) ≪≫
    baseChangeYonedaIso B S hS g ((spacesBaseChange B S hS f).functor.obj A)

include hg in
/-- The composition comparison `q⁻¹ ⟶ g⁻¹ ∘ f⁻¹` of the pseudofunctor at the sheaf represented
by `A`, for `g ≫ f = q`. -/
def compApp (A : SpacesEtale B S hS X) :
    (spacesEtaleInverseImage B S hS q).obj ((SpacesEtale.topology B S hS X).yoneda.obj A) ⟶
      (spacesEtaleInverseImage B S hS g).obj ((spacesEtaleInverseImage B S hS f).obj
        ((SpacesEtale.topology B S hS X).yoneda.obj A)) :=
  ((spacesEtalePseudofunctor B S hS).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
    (by rw [← hg]; rfl)).hom.toNatTrans.app ((SpacesEtale.topology B S hS X).yoneda.obj A)

include hg in
/-- The inverse of `AlgebraicGeometry.Space.SpacesEtaleHomDescent.compApp`. -/
def compAppInv (A : SpacesEtale B S hS X) :
    (spacesEtaleInverseImage B S hS g).obj ((spacesEtaleInverseImage B S hS f).obj
        ((SpacesEtale.topology B S hS X).yoneda.obj A)) ⟶
      (spacesEtaleInverseImage B S hS q).obj ((SpacesEtale.topology B S hS X).yoneda.obj A) :=
  ((spacesEtalePseudofunctor B S hS).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
    (by rw [← hg]; rfl)).inv.toNatTrans.app ((SpacesEtale.topology B S hS X).yoneda.obj A)

/-- `compAppInv` followed by `compApp` is the identity. -/
theorem compAppInv_comp_compApp (A : SpacesEtale B S hS X) :
    compAppInv f q g hg A ≫ compApp f q g hg A = 𝟙 _ :=
  Cat.Hom.inv_hom_id_toNatTrans_app _ _

/-- For `q = g ≫ f` on the nose, `compApp` is the composition isomorphism
`spacesEtaleInverseImage_comp` at the sheaf represented by `A`. -/
theorem compApp_self (A : SpacesEtale B S hS X) :
    compApp f (g ≫ f) g rfl A =
      (spacesEtaleInverseImage_comp B S hS g f).hom.app
        ((SpacesEtale.topology B S hS X).yoneda.obj A) := by
  unfold compApp
  have hc : (spacesEtalePseudofunctor B S hS).mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc
      (by rfl) = (spacesEtalePseudofunctor B S hS).mapComp f.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  rw [hc, spacesEtalePseudofunctor_mapComp]
  rfl

/-- **The composition comparison of the pseudofunctor on representable sheaves.** Through the
isomorphisms of Stacks 04D3, the comparison `q⁻¹ ≅ g⁻¹ ∘ f⁻¹` for `q = g ≫ f` at the sheaf
represented by `A` is the Yoneda image of `compIso`. -/
theorem compApp_comp_pullIso_hom (A : SpacesEtale B S hS X) :
    compApp f q g hg A ≫ (pullIso f g A).hom =
      (baseChangeYonedaIso B S hS q A).hom ≫
        (SpacesEtale.topology B S hS T).yoneda.map (compIso f q g hg A).hom := by
  subst hg
  rw [compApp_self, compIso_self]
  have hb := spacesEtaleInverseImage_comp_inv_app_comp_baseChangeYonedaIso_hom B S hS g f A
  rw [← cancel_epi ((spacesEtaleInverseImage_comp B S hS g f).inv.app _),
    Iso.inv_hom_id_app_assoc, reassoc_of% hb]
  simp [← Functor.map_comp]

/-- The composition comparison at the sheaf represented by `A`, written through the
isomorphisms `baseChangeYonedaIso` and `pullIso` as the Yoneda image of `compIso`. -/
theorem compApp_eq (A : SpacesEtale B S hS X) :
    compApp f q g hg A =
      (baseChangeYonedaIso B S hS q A).hom ≫
        (SpacesEtale.topology B S hS T).yoneda.map (compIso f q g hg A).hom ≫
          (pullIso f g A).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact compApp_comp_pullIso_hom f q g hg A

/-- The inverse composition comparison at the sheaf represented by `A`, written through the
isomorphisms `pullIso` and `baseChangeYonedaIso` as the Yoneda image of the inverse of
`compIso`. -/
theorem compAppInv_eq (A : SpacesEtale B S hS X) :
    compAppInv f q g hg A =
      (pullIso f g A).hom ≫
        (SpacesEtale.topology B S hS T).yoneda.map (compIso f q g hg A).inv ≫
          (baseChangeYonedaIso B S hS q A).inv := by
  have h1 : compApp f q g hg A ≫ (pullIso f g A).hom ≫
      (SpacesEtale.topology B S hS T).yoneda.map (compIso f q g hg A).inv ≫
        (baseChangeYonedaIso B S hS q A).inv = 𝟙 _ := by
    rw [reassoc_of% (compApp_comp_pullIso_hom f q g hg A)]
    simp [← Functor.map_comp_assoc]
  calc compAppInv f q g hg A
      = compAppInv f q g hg A ≫ compApp f q g hg A ≫ (pullIso f g A).hom ≫
          (SpacesEtale.topology B S hS T).yoneda.map (compIso f q g hg A).inv ≫
            (baseChangeYonedaIso B S hS q A).inv := by rw [h1, Category.comp_id]
    _ = _ := by rw [reassoc_of% (compAppInv_comp_compApp f q g hg A)]

/-- The inverse image along `g` of a morphism `f⁻¹ h_A ⟶ f⁻¹ h_{A'}` coming from a morphism of
base changes is, through Stacks 04D3, the Yoneda image of its base change along `g`. -/
theorem map_baseChangeYoneda {A A' : SpacesEtale B S hS X}
    (ψ : (spacesBaseChange B S hS f).functor.obj A ⟶ (spacesBaseChange B S hS f).functor.obj A') :
    (spacesEtaleInverseImage B S hS g).map ((baseChangeYonedaIso B S hS f A).hom ≫
        (SpacesEtale.topology B S hS Y).yoneda.map ψ ≫ (baseChangeYonedaIso B S hS f A').inv) =
      (pullIso f g A).hom ≫
        (SpacesEtale.topology B S hS T).yoneda.map ((spacesBaseChange B S hS g).functor.map ψ) ≫
          (pullIso f g A').inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [← Adjunction.map_yoneda_map_comp_yonedaIso_hom_assoc (spacesEtaleAdjunction B S hS g) ψ,
    Iso.hom_inv_id_assoc]

end Composite

/-! ### Morphisms of fibre descent data as morphisms of sheaf descent data -/

/-- Two points of `Y ×_X V` with the same image in `V` have the same image in `W` under a
morphism of fibre descent data: this is commutation with the move operations. -/
theorem fst_eq_of_fibreDescentData_hom
    {F G : Descent.SheavesWithSpaceFibres (fun _ : PUnit.{1} => f.hom)}
    (ψ : Descent.fibreDescentData (fun _ : PUnit.{1} => f.hom) X.property (fun _ => Y.property) F ⟶
      Descent.fibreDescentData (fun _ : PUnit.{1} => f.hom) X.property (fun _ => Y.property) G)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : Q ⟶ pullback F.obj.hom f.hom)
    (hab : a ≫ pullback.fst F.obj.hom f.hom = b ≫ pullback.fst F.obj.hom f.hom) :
    a ≫ (ψ.hom PUnit.unit).left ≫ pullback.fst G.obj.hom f.hom =
      b ≫ (ψ.hom PUnit.unit).left ≫ pullback.fst G.obj.hom f.hom := by
  let Z : Over X.obj := Over.mk (a ≫ pullback.fst F.obj.hom f.hom ≫ F.obj.hom)
  let v : Z ⟶ (Over.map f.hom).obj (Descent.fibreComponent (fun _ : PUnit.{1} => f.hom) F.obj
      PUnit.unit) :=
    Over.homMk a (by simp [Z, pullback.condition])
  let y : Z ⟶ Over.mk f.hom := Over.homMk (b ≫ pullback.snd F.obj.hom f.hom) (by
    simp only [Z, Over.mk_hom, Category.assoc, ← pullback.condition, reassoc_of% hab])
  have h := Descent.DescentData.move_naturality ψ (i := PUnit.unit) (j := PUnit.unit) v y
  rw [fibreDescentData_transport_move f F v y, fibreDescentData_transport_move f G _ y] at h
  have hb : (Descent.fibreMove (fun _ : PUnit.{1} => f.hom) F.obj (i := PUnit.unit)
      (j := PUnit.unit) v y).left = b := by
    apply pullback.hom_ext
    · simp [v, hab]
    · simp [y]
  have e1 : (Descent.fibreMove (fun _ : PUnit.{1} => f.hom) F.obj (i := PUnit.unit)
      (j := PUnit.unit) v y ≫ (Over.map f.hom).map (ψ.hom PUnit.unit)).left ≫
        pullback.fst G.obj.hom f.hom =
      b ≫ (ψ.hom PUnit.unit).left ≫ pullback.fst G.obj.hom f.hom := by
    rw [Over.comp_left, hb]
    exact Category.assoc _ _ _
  have e2 : (Descent.fibreMove (fun _ : PUnit.{1} => f.hom) G.obj (i := PUnit.unit)
      (j := PUnit.unit) (v ≫ (Over.map f.hom).map (ψ.hom PUnit.unit)) y).left ≫
        pullback.fst G.obj.hom f.hom =
      a ≫ (ψ.hom PUnit.unit).left ≫ pullback.fst G.obj.hom f.hom := by
    rw [Descent.fibreMove_left_fst, Over.comp_left]
    exact Category.assoc _ _ _
  exact e2.symm.trans ((congrArg (fun k => k.left ≫ pullback.fst G.obj.hom f.hom) h).symm.trans e1)

variable {f}

/-- **The compatibility of a morphism of fibre descent data with pullbacks.** Let
`ψ₀ : Y ×_X V ⟶ Y ×_X W` be a morphism over `Y` under which two points of `Y ×_X V` with the
same image in `V` have the same image in `W`. For two maps `f₁, f₂ : T ⟶ Y` with the same
composite `q` to `X`, the base changes of `ψ₀` along `f₁` and along `f₂` agree as morphisms
`T ×_X V ⟶ T ×_X W`, through `compIso`. -/
theorem compIso_conj_eq
    (ψ₀ : Descent.fibreComponent (fun _ : PUnit.{1} => f.hom) V.obj PUnit.unit ⟶
      Descent.fibreComponent (fun _ : PUnit.{1} => f.hom) W.obj PUnit.unit)
    (hψ₀ : ∀ {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : Q ⟶ pullback V.obj.hom f.hom),
      a ≫ pullback.fst V.obj.hom f.hom = b ≫ pullback.fst V.obj.hom f.hom →
        a ≫ ψ₀.left ≫ pullback.fst W.obj.hom f.hom = b ≫ ψ₀.left ≫ pullback.fst W.obj.hom f.hom)
    {T : AlgebraicSpaces B S hS} (q : T ⟶ X) (f₁ f₂ : T ⟶ Y) (h₁ : f₁ ≫ f = q)
    (h₂ : f₂ ≫ f = q) :
    (compIso f q f₁ h₁ (siteObj V hV)).hom ≫
        (spacesBaseChange B S hS f₁).functor.map (transfer hV hW f ψ₀) ≫
          (compIso f q f₁ h₁ (siteObj W hW)).inv =
      (compIso f q f₂ h₂ (siteObj V hV)).hom ≫
        (spacesBaseChange B S hS f₂).functor.map (transfer hV hW f ψ₀) ≫
          (compIso f q f₂ h₂ (siteObj W hW)).inv := by
  have side : ∀ (g : T ⟶ Y) (hg : g ≫ f = q),
      ((compIso f q g hg (siteObj V hV)).hom ≫
          (spacesBaseChange B S hS g).functor.map (transfer hV hW f ψ₀) ≫
            (compIso f q g hg (siteObj W hW)).inv).hom.left ≫
          (spacesBaseChange B S hS q).projection.app (siteObj W hW) =
        ((compIso f q g hg (siteObj V hV)).hom.hom.left ≫
          (spacesBaseChange B S hS g).projection.app
            ((spacesBaseChange B S hS f).functor.obj (siteObj V hV))) ≫
          (transfer hV hW f ψ₀).hom.left ≫
            (spacesBaseChange B S hS f).projection.app (siteObj W hW) := by
    intro g hg
    change (compIso f q g hg (siteObj V hV)).hom.hom.left ≫
        ((spacesBaseChange B S hS g).functor.map (transfer hV hW f ψ₀)).hom.left ≫
          (compIso f q g hg (siteObj W hW)).inv.hom.left ≫
            (spacesBaseChange B S hS q).projection.app (siteObj W hW) = _
    rw [compIso_inv_fst, reassoc_of% (baseChange_map_projection g (transfer hV hW f ψ₀))]
    simp only [Category.assoc]
  have hψ : (transfer hV hW f ψ₀).hom.left.hom ≫
      ((spacesBaseChange B S hS f).projection.app (siteObj W hW)).hom =
      (baseChangeIso f V hV).hom ≫ ψ₀.left ≫ pullback.fst W.obj.hom f.hom := by
    rw [transfer_hom_left_hom, Category.assoc, Category.assoc, baseChangeIso_inv_fst]
    rfl
  have e : ∀ (g : T ⟶ Y) (hg : g ≫ f = q),
      (((compIso f q g hg (siteObj V hV)).hom.hom.left).hom ≫
        ((spacesBaseChange B S hS g).projection.app
          ((spacesBaseChange B S hS f).functor.obj (siteObj V hV))).hom ≫
            (baseChangeIso f V hV).hom) ≫ pullback.fst V.obj.hom f.hom =
        ((spacesBaseChange B S hS q).projection.app (siteObj V hV)).hom := fun g hg => by
    have h := congrArg (fun k => k.hom) (compIso_hom_fst f q g hg (siteObj V hV))
    simp only [ObjectProperty.FullSubcategory.comp_hom] at h
    simp only [Category.assoc, baseChangeIso_hom_fst]
    exact h
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (((spacesBaseChange B S hS q).isPullback (siteObj W hW)).hom_ext ?_ ?_))
  · rw [side f₁ h₁, side f₂ h₂]
    refine ObjectProperty.hom_ext _ ?_
    simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, hψ]
    have key := hψ₀ _ _ ((e f₁ h₁).trans (e f₂ h₂).symm)
    simp only [Category.assoc] at key
    exact key
  · exact (Over.w _).trans (Over.w _).symm

/-- **A morphism of fibre descent data is a morphism of the descent data of the represented
sheaves.** For a morphism `ψ : Y ×_X V ⟶ Y ×_X W` of fibre descent data relative to `f`, the
morphism `f⁻¹ h_V ⟶ f⁻¹ h_W` it induces through Stacks 04D3 is compatible with the canonical
descent data of `h_V` and `h_W` for the one-member family `{f}`. -/
def descentHom (ψ : fibreDatum f V ⟶ fibreDatum f W) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).obj
        ((SpacesEtale.topology B S hS X).yoneda.obj (siteObj V hV)) ⟶
      ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).obj
        ((SpacesEtale.topology B S hS X).yoneda.obj (siteObj W hW)) where
  hom _ := (baseChangeYonedaIso B S hS f (siteObj V hV)).hom ≫
    (SpacesEtale.topology B S hS Y).yoneda.map (transfer hV hW f (ψ.hom PUnit.unit)) ≫
      (baseChangeYonedaIso B S hS f (siteObj W hW)).inv
  comm Y' q _ _ f₁ f₂ hf₁ hf₂ := by
    have h₁ : f₁ ≫ f = q := hf₁
    have h₂ : f₂ ≫ f = q := hf₂
    change (spacesEtaleInverseImage B S hS f₁).map
          ((baseChangeYonedaIso B S hS f (siteObj V hV)).hom ≫
            (SpacesEtale.topology B S hS Y).yoneda.map (transfer hV hW f (ψ.hom PUnit.unit)) ≫
              (baseChangeYonedaIso B S hS f (siteObj W hW)).inv) ≫
        (compAppInv f q f₁ h₁ (siteObj W hW) ≫ compApp f q f₂ h₂ (siteObj W hW)) =
      (compAppInv f q f₁ h₁ (siteObj V hV) ≫ compApp f q f₂ h₂ (siteObj V hV)) ≫
        (spacesEtaleInverseImage B S hS f₂).map ((baseChangeYonedaIso B S hS f (siteObj V hV)).hom ≫
          (SpacesEtale.topology B S hS Y).yoneda.map (transfer hV hW f (ψ.hom PUnit.unit)) ≫
            (baseChangeYonedaIso B S hS f (siteObj W hW)).inv)
    rw [map_baseChangeYoneda f f₁, map_baseChangeYoneda f f₂,
      compAppInv_eq f q f₁ h₁ (siteObj W hW), compApp_eq f q f₂ h₂ (siteObj W hW),
      compAppInv_eq f q f₁ h₁ (siteObj V hV), compApp_eq f q f₂ h₂ (siteObj V hV)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have key := compIso_conj_eq hV hW (ψ.hom PUnit.unit)
      (fun a b hab => fst_eq_of_fibreDescentData_hom f ψ a b hab) q f₁ f₂ h₁ h₂
    have key₂ : (spacesBaseChange B S hS f₁).functor.map (transfer hV hW f (ψ.hom PUnit.unit)) ≫
        (compIso f q f₁ h₁ (siteObj W hW)).inv ≫ (compIso f q f₂ h₂ (siteObj W hW)).hom =
        (compIso f q f₁ h₁ (siteObj V hV)).inv ≫ (compIso f q f₂ h₂ (siteObj V hV)).hom ≫
          (spacesBaseChange B S hS f₂).functor.map (transfer hV hW f (ψ.hom PUnit.unit)) := by
      rw [← cancel_epi (compIso f q f₁ h₁ (siteObj V hV)).hom, Iso.hom_inv_id_assoc,
        reassoc_of% key, Iso.inv_hom_id, Category.comp_id]
    have key₃ := congrArg (fun k => (SpacesEtale.topology B S hS Y').yoneda.map k) key₂
    simp only [Functor.map_comp] at key₃
    rw [reassoc_of% key₃]

end SpacesEtaleHomDescent

open SpacesEtaleHomDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Descent of morphisms between spaces étale over the target.** Let `f : Y ⟶ X` be a
morphism of algebraic spaces over `S` along which descent of spaces-étale sheaves is effective.
For algebraic spaces `V`, `W` étale over `X`, morphisms `V ⟶ W` over `X` are exactly the
morphisms of the fibre descent data `Y ×_X V ⟶ Y ×_X W` relative to `f`. -/
theorem bijective_fibreDescentMap_of_isEquivalence {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hdesc : ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence)
    (V W : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj)
    (hV : IsEtale B S hS V.obj.hom) (hW : IsEtale B S hS W.obj.hom) :
    Function.Bijective (fun φ : V ⟶ W =>
      (Descent.fibreDescentFunctor (fun _ : PUnit.{1} => f.hom) X.property
        (fun _ => Y.property)).map ((Descent.algebraicSpacesOverToSheaves
          (fun _ : PUnit.{1} => f.hom) X.property (fun _ => Y.property)).map φ)) := by
  let Φ := (spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)
  have hfac : ∀ φ : V ⟶ W, descentHom hV hW ((Descent.fibreDescentFunctor
      (fun _ : PUnit.{1} => f.hom) X.property (fun _ => Y.property)).map
        ((Descent.algebraicSpacesOverToSheaves (fun _ : PUnit.{1} => f.hom) X.property
          (fun _ => Y.property)).map φ)) =
      Φ.map ((SpacesEtale.topology B S hS X).yoneda.map (siteMap hV hW φ)) := by
    intro φ
    refine Pseudofunctor.DescentData.hom_ext (fun _ => ?_)
    change (baseChangeYonedaIso B S hS f (siteObj V hV)).hom ≫
        (SpacesEtale.topology B S hS Y).yoneda.map (transfer hV hW f
          (Descent.fibreComponentMap (fun _ : PUnit.{1} => f.hom) φ.hom PUnit.unit)) ≫
          (baseChangeYonedaIso B S hS f (siteObj W hW)).inv =
      (spacesEtaleInverseImage B S hS f).map
        ((SpacesEtale.topology B S hS X).yoneda.map (siteMap hV hW φ))
    rw [transfer_fibreComponentMap, ← Adjunction.map_yoneda_map_comp_yonedaIso_hom_assoc
      (spacesEtaleAdjunction B S hS f), Iso.hom_inv_id, Category.comp_id]
  have hinj : Function.Injective (descentHom (f := f) hV hW) := by
    intro ψ₁ ψ₂ h
    have h1 : (baseChangeYonedaIso B S hS f (siteObj V hV)).hom ≫
        (SpacesEtale.topology B S hS Y).yoneda.map (transfer hV hW f (ψ₁.hom PUnit.unit)) ≫
          (baseChangeYonedaIso B S hS f (siteObj W hW)).inv =
        (baseChangeYonedaIso B S hS f (siteObj V hV)).hom ≫
        (SpacesEtale.topology B S hS Y).yoneda.map (transfer hV hW f (ψ₂.hom PUnit.unit)) ≫
          (baseChangeYonedaIso B S hS f (siteObj W hW)).inv :=
      congrArg (fun k => k.hom PUnit.unit) h
    rw [cancel_epi, cancel_mono] at h1
    have h3 := transfer_injective hV hW f
      ((SpacesEtale.topology B S hS Y).yoneda.map_injective h1)
    exact Descent.DescentData.Hom.ext (funext fun i => by cases i; exact h3)
  refine ⟨fun φ₁ φ₂ h => siteMap_injective hV hW
    ((SpacesEtale.topology B S hS X).yoneda.map_injective (Φ.map_injective ?_)), fun ψ => ?_⟩
  · rw [← hfac, ← hfac]
    exact congrArg (descentHom hV hW) h
  · obtain ⟨α, hα⟩ := Φ.map_surjective (descentHom hV hW ψ)
    obtain ⟨g, hg⟩ := (SpacesEtale.topology B S hS X).yoneda.map_surjective α
    refine ⟨ofSiteMap hV hW g, hinj ?_⟩
    change descentHom hV hW ((Descent.fibreDescentFunctor (fun _ : PUnit.{1} => f.hom)
      X.property (fun _ => Y.property)).map ((Descent.algebraicSpacesOverToSheaves
        (fun _ : PUnit.{1} => f.hom) X.property (fun _ => Y.property)).map
          (ofSiteMap hV hW g))) = descentHom hV hW ψ
    rw [hfac, siteMap_ofSiteMap, hg, hα]

variable (B S hS) in
/-- **Descent of morphisms between algebraic spaces étale over the target of a proper
surjective morphism**: for a proper surjective morphism `f : Y ⟶ X` of algebraic spaces over
`S` and algebraic spaces `V`, `W` étale over `X`, morphisms `V ⟶ W` over `X` are the morphisms
of the fibre descent data of `V` and `W` relative to `f`. -/
def EtaleSpaceHomDescentAlongProperSurjective : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X), IsSurjective B S hS f.hom →
    IsProper B S hS f.hom →
      ∀ V W : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj,
        IsEtale B S hS V.obj.hom → IsEtale B S hS W.obj.hom →
          Function.Bijective (fun φ : V ⟶ W =>
            (Descent.fibreDescentFunctor (fun _ : PUnit.{1} => f.hom) X.property
              (fun _ => Y.property)).map ((Descent.algebraicSpacesOverToSheaves
                (fun _ : PUnit.{1} => f.hom) X.property (fun _ => Y.property)).map φ))

/-- **Descent of morphisms of spaces étale over the target of a proper surjective morphism,
from the proper case of Stacks 0GFW.** -/
theorem etaleSpaceHomDescentAlongProperSurjective_of_descentEffective
    (hproper : DescentEffectiveAlongProperSurjective B S hS) :
    EtaleSpaceHomDescentAlongProperSurjective B S hS := fun f hs hp V W hV hW =>
  bijective_fibreDescentMap_of_isEquivalence f (hproper f hs hp) V W hV hW

end AlgebraicGeometry.Space
