module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompChart
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite

/-!
# The composition comparison on colimit generators

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be locally quasi-finite morphisms of a big étale site and let

```
X' --f'--> Y'
|jX        |jY
X  --f-->  Y
```

be a cartesian square of open immersions with `jY ≫ g` separated. For an abelian sheaf `F` on
the small étale site of `X` and an object `W` of the small étale site of `Z`, a section of
`F|_{X'}` supported on a support `T ⊆ W ×_Z X'` finite over `W` is, through the chart
identification `W ×_Z X' = X ×_Y (W ×_Z Y')` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekCompChart`, a section of `F` supported on a support
finite over `W ×_Z Y'`: finiteness passes from `W` to `W ×_Z Y'` because `W ×_Z Y' ⟶ W` is
separated. This file builds that transport on the colimit generators of the finite-support direct
images, and the resulting morphism of presheaves

`((jX ≫ f ≫ g)_{p!}(F|_{X'}))(W) ⟶ (f_! F)(W ×_Z Y')`,

natural in `W`, which is the first half of the comparison `(f ≫ g)_! ⟶ g_! f_!` of Stacks 0F6T
on the open piece `X'` of `X`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.supportedSectionsPullback` — restriction of sections supported on
  a locally closed subset along a morphism of the small étale site.
* `AlgebraicGeometry.SmallEtale.compChartSupport` — the support finite over `W ×_Z Y'` attached to
  a support finite over `W`.
* `AlgebraicGeometry.SmallEtale.compChartGenMap` — the transport of supported sections.
* `AlgebraicGeometry.SmallEtale.compChartPresheafMap` — the morphism of presheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Pullback

/-- Two composites of restriction maps of a presheaf agree when the underlying morphisms do. -/
private theorem presheaf_map_comp_eq {C : Type*} [Category C] (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {A A₁ A₂ A₃ : C} {a : A ⟶ A₁} {b : A₁ ⟶ A₃} {c : A ⟶ A₂} {d : A₂ ⟶ A₃} (h : a ≫ b = c ≫ d)
    (x : P.obj (op A₃)) : P.map a.op (P.map b.op x) = P.map c.op (P.map d.op x) := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← ConcreteCategory.comp_apply, ← P.map_comp,
    ← op_comp, ← op_comp, h]

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- Morphisms into an open of an object of the small étale site agree when they agree after
composing with the inclusion of the open. -/
private theorem openObject_hom_ext {P A : SmallEtale B S hS}
    (U : ((SmallEtale.toScheme B S hS).obj P).Opens) {u w : A ⟶ openObject B S hS P U}
    (h : (SmallEtale.toScheme B S hS).map u ≫ U.ι = (SmallEtale.toScheme B S hS).map w ≫ U.ι) :
    u = w :=
  (SmallEtale.toScheme B S hS).map_injective ((cancel_mono U.ι).1 h)

/-- The canonical open of the inverse image of a locally closed subset along a morphism of the
small étale site lies in the inverse image of the canonical open. -/
public theorem supportOpen_preimage_le {P Q : SmallEtale B S hS} (k : P ⟶ Q)
    (T : Set ((SmallEtale.toScheme B S hS).obj Q)) (hT : IsLocallyClosed T)
    (T' : Set ((SmallEtale.toScheme B S hS).obj P)) (hT' : IsLocallyClosed T')
    (hTT' : T' = ((SmallEtale.toScheme B S hS).map k).base ⁻¹' T) :
    (supportOpen B S hS P T' hT' : Set ((SmallEtale.toScheme B S hS).obj P)) ⊆
      ((SmallEtale.toScheme B S hS).map k).base ⁻¹' (supportOpen B S hS Q T hT) := by
  have : Etale ((SmallEtale.toScheme B S hS).map k) := etale_toScheme_map k
  intro x hx
  have hx' : x ∈ coborder T' := hx
  rw [hTT'] at hx'
  exact ((SmallEtale.toScheme B S hS).map k).isOpenMap.coborder_preimage_subset T hx'

/-- The morphism of canonical support opens induced by a morphism of the small étale site. -/
public def supportOpenMap {P Q : SmallEtale B S hS} (k : P ⟶ Q)
    (T : Set ((SmallEtale.toScheme B S hS).obj Q)) (hT : IsLocallyClosed T)
    (T' : Set ((SmallEtale.toScheme B S hS).obj P)) (hT' : IsLocallyClosed T')
    (hTT' : T' = ((SmallEtale.toScheme B S hS).map k).base ⁻¹' T) :
    openObject B S hS P (supportOpen B S hS P T' hT') ⟶
      openObject B S hS Q (supportOpen B S hS Q T hT) :=
  openObjectMap B S hS k _ _ (supportOpen_preimage_le B S hS k T hT T' hT' hTT')

public theorem supportOpenMap_map {P Q : SmallEtale B S hS} (k : P ⟶ Q)
    (T : Set ((SmallEtale.toScheme B S hS).obj Q)) (hT : IsLocallyClosed T)
    (T' : Set ((SmallEtale.toScheme B S hS).obj P)) (hT' : IsLocallyClosed T')
    (hTT' : T' = ((SmallEtale.toScheme B S hS).map k).base ⁻¹' T) :
    (SmallEtale.toScheme B S hS).map (supportOpenMap B S hS k T hT T' hT' hTT') ≫
        (supportOpen B S hS Q T hT).ι =
      (supportOpen B S hS P T' hT').ι ≫ (SmallEtale.toScheme B S hS).map k :=
  openObjectMap_map B S hS k _ _ _

/-- **Restriction of supported sections** along a morphism `k : P ⟶ Q` of the small étale site:
a section supported on `T` restricts to a section supported on `k⁻¹ T`. -/
public def supportedSectionsPullback {P Q : SmallEtale B S hS} (k : P ⟶ Q)
    (T : Set ((SmallEtale.toScheme B S hS).obj Q)) (hT : IsLocallyClosed T)
    (T' : Set ((SmallEtale.toScheme B S hS).obj P)) (hT' : IsLocallyClosed T')
    (hTT' : T' = ((SmallEtale.toScheme B S hS).map k).base ⁻¹' T) :
    supportedSections B S hS F Q T hT →+ supportedSections B S hS F P T' hT' where
  toFun s := ⟨F.obj.map (supportOpenMap B S hS k T hT T' hT' hTT').op s.val, by
    have hres := supportSection_restrict_subset_preimage B S hS F _ _
      (supportOpenMap B S hS k T hT T' hT' hTT') s.val
    intro x hx
    have hx' := (hres.trans (Set.preimage_mono s.property)) hx
    have hc := congrArg (fun m => m.base x) (supportOpenMap_map B S hS k T hT T' hT' hTT')
    simp only [Scheme.Hom.comp_apply] at hc
    change (supportOpen B S hS P T' hT').ι.base x ∈ T'
    have hmem : (SmallEtale.toScheme B S hS).map k ((supportOpen B S hS P T' hT').ι x) ∈ T :=
      hc ▸ hx'
    exact hTT' ▸ hmem⟩
  map_zero' := Subtype.ext ((F.obj.map (supportOpenMap B S hS k T hT T' hT' hTT').op).hom.map_zero)
  map_add' s t := Subtype.ext
    ((F.obj.map (supportOpenMap B S hS k T hT T' hT' hTT').op).hom.map_add s.val t.val)

public theorem supportedSectionsPullback_val {P Q : SmallEtale B S hS} (k : P ⟶ Q)
    (T : Set ((SmallEtale.toScheme B S hS).obj Q)) (hT : IsLocallyClosed T)
    (T' : Set ((SmallEtale.toScheme B S hS).obj P)) (hT' : IsLocallyClosed T')
    (hTT' : T' = ((SmallEtale.toScheme B S hS).map k).base ⁻¹' T)
    (s : supportedSections B S hS F Q T hT) :
    (supportedSectionsPullback B S hS F k T hT T' hT' hTT' s).val =
      F.obj.map (supportOpenMap B S hS k T hT T' hT' hTT').op s.val :=
  rfl

/-- Restriction of supported sections commutes with the transitions along inclusions of
supports. -/
public theorem supportedSectionsPullback_transition {P Q : SmallEtale B S hS} (k : P ⟶ Q)
    (T T₂ : Set ((SmallEtale.toScheme B S hS).obj Q)) (hT : IsLocallyClosed T)
    (hT₂ : IsLocallyClosed T₂) (h : T ⊆ T₂) (hc : IsClosed ((Subtype.val : T₂ → _) ⁻¹' T))
    (T' T₂' : Set ((SmallEtale.toScheme B S hS).obj P)) (hT' : IsLocallyClosed T')
    (hT₂' : IsLocallyClosed T₂') (h' : T' ⊆ T₂')
    (hc' : IsClosed ((Subtype.val : T₂' → _) ⁻¹' T'))
    (hTT' : T' = ((SmallEtale.toScheme B S hS).map k).base ⁻¹' T)
    (hTT₂' : T₂' = ((SmallEtale.toScheme B S hS).map k).base ⁻¹' T₂) :
    (supportedSectionsPullback B S hS F k T₂ hT₂ T₂' hT₂' hTT₂').comp
        (supportedSectionsMap B S hS F Q T T₂ hT hT₂ h hc) =
      (supportedSectionsMap B S hS F P T' T₂' hT' hT₂' h' hc').comp
        (supportedSectionsPullback B S hS F k T hT T' hT' hTT') := by
  have hgeom : supportOpenMap B S hS k T₂ hT₂ T₂' hT₂' hTT₂' ≫
        openObjectHomOfLE B S hS Q (supportOpen_antitone B S hS Q T T₂ hT hT₂ h hc) =
      openObjectHomOfLE B S hS P (supportOpen_antitone B S hS P T' T₂' hT' hT₂' h' hc') ≫
        supportOpenMap B S hS k T hT T' hT' hTT' := by
    apply openObject_hom_ext
    simp only [Functor.map_comp]
    rw [Category.assoc, openObjectHomOfLE_map, Scheme.homOfLE_ι, supportOpenMap_map,
      Category.assoc, supportOpenMap_map, openObjectHomOfLE_map, Scheme.homOfLE_ι_assoc]
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  show F.obj.map _ (supportedSectionsMap B S hS F Q T T₂ hT hT₂ h hc s).val =
    (supportedSectionsMap B S hS F P T' T₂' hT' hT₂' h' hc'
      (supportedSectionsPullback B S hS F k T hT T' hT' hTT' s)).val
  rw [supportedSectionsMap_apply, supportedSectionsMap_apply, supportedSectionsPullback_val]
  exact presheaf_map_comp_eq F.obj hgeom _

/-- Restriction of supported sections is compatible with a commutative square of morphisms of
the small étale site, the two sides of the square acting through given morphisms of canonical
support opens. -/
public theorem supportedSectionsPullback_square {P P' Q Q' : SmallEtale B S hS}
    (k : P ⟶ Q) (k' : P' ⟶ Q') (b : Q' ⟶ Q) (c : P' ⟶ P) (hkc : k' ≫ b = c ≫ k)
    (T : Set ((SmallEtale.toScheme B S hS).obj Q)) (hT : IsLocallyClosed T)
    (TQ : Set ((SmallEtale.toScheme B S hS).obj Q')) (hTQ : IsLocallyClosed TQ)
    (TP : Set ((SmallEtale.toScheme B S hS).obj P)) (hTP : IsLocallyClosed TP)
    (TP' : Set ((SmallEtale.toScheme B S hS).obj P')) (hTP' : IsLocallyClosed TP')
    (hk : TP = ((SmallEtale.toScheme B S hS).map k).base ⁻¹' T)
    (hk' : TP' = ((SmallEtale.toScheme B S hS).map k').base ⁻¹' TQ)
    (ob : openObject B S hS Q' (supportOpen B S hS Q' TQ hTQ) ⟶
      openObject B S hS Q (supportOpen B S hS Q T hT))
    (hob : (SmallEtale.toScheme B S hS).map ob ≫ (supportOpen B S hS Q T hT).ι =
      (supportOpen B S hS Q' TQ hTQ).ι ≫ (SmallEtale.toScheme B S hS).map b)
    (oc : openObject B S hS P' (supportOpen B S hS P' TP' hTP') ⟶
      openObject B S hS P (supportOpen B S hS P TP hTP))
    (hoc : (SmallEtale.toScheme B S hS).map oc ≫ (supportOpen B S hS P TP hTP).ι =
      (supportOpen B S hS P' TP' hTP').ι ≫ (SmallEtale.toScheme B S hS).map c)
    (x : F.obj.obj (op (openObject B S hS Q (supportOpen B S hS Q T hT)))) :
    F.obj.map (supportOpenMap B S hS k' TQ hTQ TP' hTP' hk').op (F.obj.map ob.op x) =
      F.obj.map oc.op (F.obj.map (supportOpenMap B S hS k T hT TP hTP hk).op x) := by
  have hm : supportOpenMap B S hS k' TQ hTQ TP' hTP' hk' ≫ ob =
      oc ≫ supportOpenMap B S hS k T hT TP hTP hk := by
    apply openObject_hom_ext
    simp only [Functor.map_comp]
    rw [Category.assoc, hob, ← Category.assoc, supportOpenMap_map, Category.assoc,
      ← Functor.map_comp, hkc, Functor.map_comp, Category.assoc, supportOpenMap_map,
      ← Category.assoc, ← Category.assoc, hoc, Category.assoc]
  exact presheaf_map_comp_eq F.obj hm x

end Pullback

section Generator

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  [IsSeparated (B.inclusion.map (jY ≫ g))]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)

/-- The morphism `W' ×_Z Y' ⟶ W ×_Z Y'` of the small étale site of `Y` induced by `W' ⟶ W`. -/
public abbrev compChartBaseMap {W W' : SmallEtale B Z.obj Z.property} (φ : W' ⟶ W) :
    compChartBase B g jY W' ⟶ compChartBase B g jY W :=
  (openPostcompose B jY).map ((smallEtaleBaseChange B (jY ≫ g)).map φ)

/-- The support finite over `W ×_Z Y'` attached to a support `T ⊆ W ×_Z X'` finite over `W`: the
inverse image along the chart inclusion of the image of `T` in `W ×_Z X`, which is `T` itself
read through the chart isomorphism. It is finite over `W ×_Z Y'` because it is finite over `W`
and `W ×_Z Y' ⟶ W` is separated. -/
public theorem isFiniteSupport_compChartSupport (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) :
    IsFiniteSupport B f (compChartBase B g jY W)
      (((SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W)).base ⁻¹'
        (imageFiniteSupport B jX (f ≫ g) W T).1) := by
  rw [imageFiniteSupport_coe, compChartInclusion_preimage_image]
  obtain ⟨Zs, i, hi, hfin, hrange⟩ := T.property
  have : IsImmersion i := hi
  let κs : (SmallEtale.toScheme B X'.obj X'.property).obj (baseChange B (jX ≫ f ≫ g) W) ⟶
      (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f (compChartBase B g jY W)) :=
    (SmallEtale.toScheme B X.obj X.property).map (compChartIso B g sq hsq W).hom
  have : IsIso κs :=
    inferInstanceAs (IsIso ((SmallEtale.toScheme B X.obj X.property).map
      (compChartIso B g sq hsq W).hom))
  have : IsImmersion κs := inferInstance
  refine ⟨Zs, i ≫ κs, inferInstance, ?_, ?_⟩
  · have hc : (i ≫ κs) ≫
        B.inclusion.map (pullback.fst (compChartBase B g jY W).obj.hom f) =
        i ≫ B.inclusion.map (compChartMap B g sq W) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun m => i ≫ m)
          ((B.inclusion.map_comp _ _).symm.trans
            (congrArg B.inclusion.map (compChartHom_proj B g sq W))))
    rw [hc]
    have hsep : IsSeparated (B.inclusion.map (fiberProjection B (jY ≫ g) W)) :=
      MorphismProperty.of_isPullback
        ((isPullback_fiberProjection B (jY ≫ g) W).map B.inclusion).flip inferInstance
    have hfin' : IsFinite ((i ≫ B.inclusion.map (compChartMap B g sq W)) ≫
        B.inclusion.map (fiberProjection B (jY ≫ g) W)) := by
      have he : (i ≫ B.inclusion.map (compChartMap B g sq W)) ≫
          B.inclusion.map (fiberProjection B (jY ≫ g) W) =
          i ≫ B.inclusion.map (fiberProjection B (jX ≫ f ≫ g) W) :=
        (Category.assoc _ _ _).trans (congrArg (fun m => i ≫ m)
          ((B.inclusion.map_comp _ _).symm.trans
            (congrArg B.inclusion.map (compChartMap_fst B g sq W))))
      rw [he]
      exact hfin
    exact @IsFinite.of_comp _ _ _ _ (B.inclusion.map (fiberProjection B (jY ≫ g) W)) hfin' hsep
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
    rfl

/-- The support finite over `W ×_Z Y'` attached to a support finite over `W`. -/
public def compChartSupport (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) : FiniteSupport B f (compChartBase B g jY W) :=
  ⟨_, isFiniteSupport_compChartSupport B g sq hsq W T⟩

public theorem compChartSupport_coe (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) :
    (compChartSupport B g sq hsq W T).1 =
      ((SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W)).base ⁻¹'
        (imageFiniteSupport B jX (f ≫ g) W T).1 :=
  rfl

/-- The attached support is monotone. -/
public theorem compChartSupport_mono (W : SmallEtale B Z.obj Z.property)
    {T T₂ : FiniteSupport B (jX ≫ f ≫ g) W} (h : T ≤ T₂) :
    compChartSupport B g sq hsq W T ≤ compChartSupport B g sq hsq W T₂ :=
  Set.preimage_mono (imageFiniteSupport_mono B jX (f ≫ g) W h)

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- **The transport of supported sections.** A section of `F|_{X'}` supported on `T` is extended
by zero to a section of `F` on `W ×_Z X` supported on the image of `T` (Stacks 0F6S), and then
restricted along the chart inclusion to a section of `F` supported on a support `E` finite over
`W ×_Z Y'`; any `E` with the right underlying set may be used. -/
public def compChartGenMap (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) (D : FiniteSupport B (f ≫ g) W)
    (hD : D.1 = (openBaseChangeHom B jX (f ≫ g) W).base '' T.1)
    (E : FiniteSupport B f (compChartBase B g jY W))
    (hE : E.1 = ((SmallEtale.toScheme B X.obj X.property).map
      (compChartInclusion B g sq hsq W)).base ⁻¹' D.1) :
    supportedSections B X'.obj X'.property ((openRestriction.{u, v} B jX).obj F)
        (baseChange B (jX ≫ f ≫ g) W) T.1 (finiteSupport_isLocallyClosed B _ W T) →+
      supportedSections B X.obj X.property F (baseChange B f (compChartBase B g jY W)) E.1
        (finiteSupport_isLocallyClosed B f _ E) :=
  (supportedSectionsPullback B X.obj X.property F (compChartInclusion B g sq hsq W)
      D.1 (finiteSupport_isLocallyClosed B _ W _) E.1
      (finiteSupport_isLocallyClosed B f _ E) hE).comp
    (covarianceSectionMap B jX (f ≫ g) F W T D hD)

end Generator

section Presheaf

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  [IsSeparated (B.inclusion.map (jY ≫ g))]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)] in
/-- The transport of supported sections commutes with the transitions along inclusions of
supports. -/
public theorem compChartGenMap_transition (W : SmallEtale B Z.obj Z.property)
    {T T₂ : FiniteSupport B (jX ≫ f ≫ g) W} (h : T ⟶ T₂) :
    (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) W).map h ≫
        AddCommGrpCat.ofHom (compChartGenMap B g sq hsq F W T₂
          _ (imageFiniteSupport_coe B jX (f ≫ g) W T₂) (compChartSupport B g sq hsq W T₂)
          (compChartSupport_coe B g sq hsq W T₂)) =
      AddCommGrpCat.ofHom (compChartGenMap B g sq hsq F W T
          _ (imageFiniteSupport_coe B jX (f ≫ g) W T) (compChartSupport B g sq hsq W T)
          (compChartSupport_coe B g sq hsq W T)) ≫
        (finiteSupportDiagram B f F (compChartBase B g jY W)).map
          (homOfLE (compChartSupport_mono B g sq hsq W (leOfHom h))) := by
  have hcov := covarianceSectionMap_transition B jX (f ≫ g) F W h
  have hpb := supportedSectionsPullback_transition B X.obj X.property F
    (compChartInclusion B g sq hsq W)
    (imageFiniteSupport B jX (f ≫ g) W T).1 (imageFiniteSupport B jX (f ≫ g) W T₂).1
    (finiteSupport_isLocallyClosed B _ W _) (finiteSupport_isLocallyClosed B _ W _)
    (imageFiniteSupport_mono B jX (f ≫ g) W (leOfHom h))
    (finiteSupport_closedWithin B _ W _ _ (imageFiniteSupport_mono B jX (f ≫ g) W (leOfHom h)))
    (compChartSupport B g sq hsq W T).1 (compChartSupport B g sq hsq W T₂).1
    (finiteSupport_isLocallyClosed B f _ _) (finiteSupport_isLocallyClosed B f _ _)
    (compChartSupport_mono B g sq hsq W (leOfHom h))
    (finiteSupport_closedWithin B f _ _ _ (compChartSupport_mono B g sq hsq W (leOfHom h)))
    (compChartSupport_coe B g sq hsq W T) (compChartSupport_coe B g sq hsq W T₂)
  refine ConcreteCategory.hom_ext _ _ fun a => ?_
  have h1 := ConcreteCategory.congr_hom hcov a
  have h2 := congrArg (fun φ => φ (covarianceSectionMap B jX (f ≫ g) F W T _
    (imageFiniteSupport_coe B jX (f ≫ g) W T) a)) hpb
  simp only at h1
  exact (congrArg (supportedSectionsPullback B X.obj X.property F
    (compChartInclusion B g sq hsq W) _ (finiteSupport_isLocallyClosed B _ W _) _
    (finiteSupport_isLocallyClosed B f _ (compChartSupport B g sq hsq W T₂))
    (compChartSupport_coe B g sq hsq W T₂)) h1).trans h2

/-- The cocone of transported generators, with vertex the sections of `f_! F` over
`W ×_Z Y'`. -/
public def compChartCocone (W : SmallEtale B Z.obj Z.property) :
    Cocone (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) W) where
  pt := ((fShriekFunctor.{u, v} B f).obj F).obj.obj (op (compChartBase B g jY W))
  ι :=
    { app T := AddCommGrpCat.ofHom (compChartGenMap B g sq hsq F W T
          _ (imageFiniteSupport_coe B jX (f ≫ g) W T) (compChartSupport B g sq hsq W T)
          (compChartSupport_coe B g sq hsq W T)) ≫
        finiteSupportPushforwardGenerator B f F _ (compChartSupport B g sq hsq W T) ≫
        (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).val.obj F)).app (op (compChartBase B g jY W))
      naturality T T₂ h := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        have ht := compChartGenMap_transition B g sq hsq F W h
        have hw : (finiteSupportDiagram B f F (compChartBase B g jY W)).map
              (homOfLE (compChartSupport_mono B g sq hsq W (leOfHom h))) ≫
            finiteSupportPushforwardGenerator B f F _ (compChartSupport B g sq hsq W T₂) =
            finiteSupportPushforwardGenerator B f F _ (compChartSupport B g sq hsq W T) := by
          simp only [finiteSupportPushforwardGenerator]
          rw [← Category.assoc, colimit.w]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫
                finiteSupportPushforwardGenerator B f F _ (compChartSupport B g sq hsq W T₂) ≫
                (toSheafify (SmallEtale.topology B Y.obj Y.property)
                  ((finiteSupportPushforward.{u, max (u + 1) v} B f
                    (fun _ => inferInstance)).val.obj F)).app (op (compChartBase B g jY W)))
                ht).trans
              ((Category.assoc _ _ _).trans (congrArg (fun z => AddCommGrpCat.ofHom
                (compChartGenMap B g sq hsq F W T _ (imageFiniteSupport_coe B jX (f ≫ g) W T)
                  (compChartSupport B g sq hsq W T) (compChartSupport_coe B g sq hsq W T)) ≫ z)
                ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫
                  (toSheafify (SmallEtale.topology B Y.obj Y.property)
                  ((finiteSupportPushforward.{u, max (u + 1) v} B f
                    (fun _ => inferInstance)).val.obj F)).app (op (compChartBase B g jY W)))
                  hw))))) }

/-- **The transported generators**, as a map from the finite-support sections of `F|_{X'}` along
`jX ≫ f ≫ g` over `W` to the sections of `f_! F` over `W ×_Z Y'`. -/
public def compChartApp (W : SmallEtale B Z.obj Z.property) :
    ((finiteSupportPushforward.{u, max (u + 1) v} B (jX ≫ f ≫ g)
        (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B jX).obj F)).obj (op W) ⟶
      ((fShriekFunctor.{u, v} B f).obj F).obj.obj (op (compChartBase B g jY W)) :=
  colimit.desc _ (compChartCocone B g sq hsq F W)

/-- The transported generators on a colimit generator, for any support realizing the attached
support. -/
public theorem compChartApp_generator (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) (D : FiniteSupport B (f ≫ g) W)
    (hD : D.1 = (openBaseChangeHom B jX (f ≫ g) W).base '' T.1)
    (E : FiniteSupport B f (compChartBase B g jY W))
    (hE : E.1 = ((SmallEtale.toScheme B X.obj X.property).map
      (compChartInclusion B g sq hsq W)).base ⁻¹' D.1) :
    finiteSupportPushforwardGenerator B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F)
        W T ≫ compChartApp B g sq hsq F W =
      AddCommGrpCat.ofHom (compChartGenMap B g sq hsq F W T D hD E hE) ≫
        finiteSupportPushforwardGenerator B f F _ E ≫
        (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).val.obj F)).app (op (compChartBase B g jY W)) := by
  have hd : D = imageFiniteSupport B jX (f ≫ g) W T :=
    Subtype.ext (hD.trans (imageFiniteSupport_coe B jX (f ≫ g) W T).symm)
  subst hd
  have he : E = compChartSupport B g sq hsq W T := Subtype.ext hE
  subst he
  simp only [finiteSupportPushforwardGenerator, compChartApp]
  show colimit.ι _ T ≫ colimit.desc _ (compChartCocone B g sq hsq F W) = _
  rw [colimit.ι_desc]
  rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)] in
/-- The attached support is compatible with base change of the test object. -/
public theorem compChartSupport_baseChange {W W' : SmallEtale B Z.obj Z.property} (φ : W' ⟶ W)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) :
    (finiteSupportBaseChange B f F (compChartBaseMap B g φ)
        (compChartSupport B g sq hsq W T)).support.1 =
      ((SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W')).base ⁻¹'
        (finiteSupportBaseChange B (f ≫ g) F φ
          (imageFiniteSupport B jX (f ≫ g) W T)).support.1 := by
  rw [FiniteSupportBaseChange.support_eq, FiniteSupportBaseChange.support_eq,
    compChartSupport_coe]
  ext x
  simp only [Set.mem_preimage]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
    compChartInclusion_naturality B g sq hsq φ]

/-- **The transported generators are natural in the test object.** -/
public theorem compChartApp_naturality {W W' : SmallEtale B Z.obj Z.property} (φ : W' ⟶ W) :
    ((finiteSupportPushforward.{u, max (u + 1) v} B (jX ≫ f ≫ g)
        (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B jX).obj F)).map φ.op ≫
        compChartApp B g sq hsq F W' =
      compChartApp B g sq hsq F W ≫
        ((fShriekFunctor.{u, v} B f).obj F).obj.map (compChartBaseMap B g φ).op := by
  apply finiteSupportPushforwardGenerator_hom_ext B (jX ≫ f ≫ g)
    ((openRestriction.{u, v} B jX).obj F) W
  intro T
  let D := imageFiniteSupport B jX (f ≫ g) W T
  let dT := finiteSupportBaseChange B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) φ T
  let dD := finiteSupportBaseChange B (f ≫ g) F φ D
  let dE := finiteSupportBaseChange B f F (compChartBaseMap B g φ)
    (compChartSupport B g sq hsq W T)
  have hD'' : dD.support.1 = (openBaseChangeHom B jX (f ≫ g) W').base '' dT.support.1 :=
    baseChange_image_support B jX (f ≫ g) F φ T D (imageFiniteSupport_coe B jX (f ≫ g) W T)
  have hE' : dE.support.1 = ((SmallEtale.toScheme B X.obj X.property).map
      (compChartInclusion B g sq hsq W')).base ⁻¹' dD.support.1 :=
    compChartSupport_baseChange B g sq hsq F φ T
  have hc := covarianceTargetOpenMap_square B jX (f ≫ g) φ T dT.support D dD.support
    (imageFiniteSupport_coe B jX (f ≫ g) W T) hD'' dT.openMap dD.openMap
    dT.openMap_commutes dD.openMap_commutes
  have hcov := covarianceSectionMap_map B jX (f ≫ g) F W W' T dT.support D dD.support
    (imageFiniteSupport_coe B jX (f ≫ g) W T) hD'' _ _ hc _ _ dT.sectionsMap_apply
    dD.sectionsMap_apply
  have hs : AddCommGrpCat.ofHom dT.sectionsMap ≫
      AddCommGrpCat.ofHom (compChartGenMap B g sq hsq F W' dT.support dD.support hD''
        dE.support hE') =
      AddCommGrpCat.ofHom (compChartGenMap B g sq hsq F W T D
        (imageFiniteSupport_coe B jX (f ≫ g) W T) (compChartSupport B g sq hsq W T)
        (compChartSupport_coe B g sq hsq W T)) ≫ AddCommGrpCat.ofHom dE.sectionsMap := by
    refine ConcreteCategory.hom_ext _ _ fun a => Subtype.ext ?_
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hcov a)
    show (supportedSectionsPullback B X.obj X.property F (compChartInclusion B g sq hsq W')
        _ _ _ _ hE' (covarianceSectionMap B jX (f ≫ g) F W' dT.support dD.support hD''
          (dT.sectionsMap a))).val =
      (dE.sectionsMap (supportedSectionsPullback B X.obj X.property F
        (compChartInclusion B g sq hsq W) _ _ _ _ (compChartSupport_coe B g sq hsq W T)
        (covarianceSectionMap B jX (f ≫ g) F W T D
          (imageFiniteSupport_coe B jX (f ≫ g) W T) a))).val
    rw [supportedSectionsPullback_val, dE.sectionsMap_apply, supportedSectionsPullback_val]
    change _ = (covarianceSectionMap B jX (f ≫ g) F W' dT.support dD.support hD''
      (dT.sectionsMap a)).val at h1
    rw [← h1]
    show F.obj.map _ (dD.sectionsMap (covarianceSectionMap B jX (f ≫ g) F W T D
      (imageFiniteSupport_coe B jX (f ≫ g) W T) a)).val = _
    rw [dD.sectionsMap_apply]
    exact supportedSectionsPullback_square B X.obj X.property F
      (compChartInclusion B g sq hsq W) (compChartInclusion B g sq hsq W')
      ((smallEtaleBaseChange B (f ≫ g)).map φ)
      ((smallEtaleBaseChange B f).map (compChartBaseMap B g φ))
      (compChartInclusion_naturality B g sq hsq φ).symm _ _ _ _ _ _ _ _ _ _
      dD.openMap dD.openMap_commutes dE.openMap dE.openMap_commutes _
  have hl := finiteSupportPushforwardGenerator_restrict B (jX ≫ f ≫ g)
    ((openRestriction.{u, v} B jX).obj F) φ T
  have hg' := compChartApp_generator B g sq hsq F W' dT.support dD.support hD'' dE.support hE'
  have hg := compChartApp_generator B g sq hsq F W T D
    (imageFiniteSupport_coe B jX (f ≫ g) W T) (compChartSupport B g sq hsq W T)
    (compChartSupport_coe B g sq hsq W T)
  have hr := finiteSupportPushforwardGenerator_restrict B f F (compChartBaseMap (jY := jY) B g φ)
    (compChartSupport B g sq hsq W T)
  have hn := (toSheafify (SmallEtale.topology B Y.obj Y.property)
    ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).val.obj F)).naturality (compChartBaseMap (jY := jY) B g φ).op
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ compChartApp B g sq hsq F W') hl).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (AddCommGrpCat.ofHom dT.sectionsMap ≫ ·) hg').trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hs).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _) hg.symm)
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (AddCommGrpCat.ofHom (compChartGenMap B g sq hsq F W T D
    (imageFiniteSupport_coe B jX (f ≫ g) W T) (compChartSupport B g sq hsq W T)
    (compChartSupport_coe B g sq hsq W T)) ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hr.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (finiteSupportPushforwardGenerator B f F _
    (compChartSupport B g sq hsq W T) ≫ ·) hn).trans ?_
  exact (Category.assoc _ _ _).symm

end Presheaf

end AlgebraicGeometry.SmallEtale

end
