module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Higher direct images on the small étale site

Let `f : X ⟶ Y` be a morphism in a big étale site. Stacks 03Q8 says that `R^p f_* F` is the
sheaf associated to the presheaf `V ↦ H^p_ét(X ×_Y V, F)` on the small étale site of `Y`, and
likewise for an unbounded complex `K`.

This file supplies the vocabulary in which that assertion is stated, and the canonical
comparison maps that pin it down — so that the assertion is about a specific map rather than
about the existence of some isomorphism.

On the sheaf side, `preimageSectionsPresheaf` is the presheaf of sections over the étale base
changes, `sheafifySectionsIso` identifies its sheafification with `f_*` *through the
sheafification counit*, `preimageCohomologyPresheafEvaluationIso` identifies the value of the
derived presheaf at `V` with the cohomology over `X ×_Y V`, and
`higherDirectImageSheafificationIso` is the resulting objectwise comparison. The structure
`HigherDirectImageComparison` then asks for a *natural* isomorphism whose components are that
objectwise comparison, together with the statement that the restriction maps of the cohomology
presheaf are the derived restriction maps of sections. Both requirements are needed: without
them the comparison could be replaced by its negative, or the presheaf by one with the same
values and different restrictions.

On the unbounded side, `derivedSheafificationComparison` is the unique derived descent of the
same sheafification counit, and `DerivedPushforwardComparison` records its invertibility
together with the universal property of evaluation over the fibre products.

The sheaf-level assertion itself is proved here: `higherDirectImageComparison` inhabits
`HigherDirectImageComparison`, both of its normalizations coming from the naturality of
`Stacks.DerivedFunctor.rightDerivedEvaluationIso` — in the sheaf for the components, and in the
exact functor moved through the right derived functor for the restriction maps. That
`DerivedPushforwardComparison` is inhabited is not proved here.

## Main definitions

* `Stacks.HigherDirectImage.pushforward`, `.preimageSectionsPresheaf`, `.sectionsOnPreimage`,
  `.sectionsRestriction` — the functors of the statement.
* `Stacks.HigherDirectImage.sheafifySectionsIso` — the counit normalization.
* `Stacks.HigherDirectImage.higherDirectImageSheafificationIso` — the objectwise comparison.
* `Stacks.HigherDirectImage.HigherDirectImageComparison` — the sheaf-level assertion.
* `Stacks.HigherDirectImage.higherDirectImageComparison` — **[Stacks, Tag 03Q8]** for abelian
  sheaves: that assertion holds.
* `Stacks.HigherDirectImage.derivedSheafificationComparison`,
  `Stacks.HigherDirectImage.DerivedPushforwardComparison` — the unbounded assertion.

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace Stacks.HigherDirectImage

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The small étale topology of the source of `f`. -/
public abbrev JX := SmallEtale.topology B X.obj X.property

/-- The small étale topology of the target of `f`. -/
public abbrev JY := SmallEtale.topology B Y.obj Y.property

/-- Direct image of abelian sheaves along `f`, for the small étale topologies. -/
public abbrev pushforward :
    Sheaf (JX B (X := X)) AddCommGrpCat.{w} ⥤
      Sheaf (JY B (Y := Y)) AddCommGrpCat.{w} :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{w}
    (JY B (Y := Y)) (JX B (X := X))

/-- Sections over all étale base changes `X ×_Y V`, with their actual restriction maps. -/
public abbrev preimageSectionsPresheaf :=
  pushforward.{u, w} B f ⋙ sheafToPresheaf (JY B (Y := Y)) AddCommGrpCat.{w}

/-- Direct image of abelian sheaves is additive. -/
public instance pushforward_additive : (pushforward.{u, w} B f).Additive where
  map_add := by intros; rfl

/-- The presheaf of sections over the étale base changes is additive in the sheaf. -/
public instance preimageSectionsPresheaf_additive :
    (preimageSectionsPresheaf.{u, w} B f).Additive where
  map_add := by intros; rfl

/-- The ordinary sections functor on the fibre product `X ×_Y V`. -/
public abbrev sectionsOnPreimage (V : SmallEtale B Y.obj Y.property) :
    Sheaf (JX B (X := X)) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  sheafToPresheaf (JX B (X := X)) AddCommGrpCat.{w} ⋙
    (evaluation _ AddCommGrpCat.{w}).obj (Opposite.op ((smallEtaleBaseChange B f).obj V))

/-- Sections over a fixed fibre product are additive in the sheaf. -/
public instance sectionsOnPreimage_additive (V : SmallEtale B Y.obj Y.property) :
    (sectionsOnPreimage.{u, w} B f V).Additive where
  map_add := by intros; rfl

/-- Restriction of sections along a morphism of étale `Y`-schemes. -/
public def sectionsRestriction {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) :
    sectionsOnPreimage.{u, w} B f V ⟶ sectionsOnPreimage.{u, w} B f U where
  app F := F.obj.map ((smallEtaleBaseChange B f).map g).op
  naturality _ _ h := (h.hom.naturality _).symm

variable [HasSheafify (JX B (X := X)) AddCommGrpCat.{w}]
  [HasSheafify (JY B (Y := Y)) AddCommGrpCat.{w}]

/-- The sheafification counit, rather than an arbitrary isomorphism, identifies the
sheafification of the presheaf of sections over the étale base changes with the direct
image. -/
public def sheafifySectionsIso :
    preimageSectionsPresheaf.{u, w} B f ⋙
        presheafToSheaf (JY B (Y := Y)) AddCommGrpCat.{w} ≅ pushforward.{u, w} B f :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (sheafificationAdjunction
      (JY B (Y := Y)) AddCommGrpCat.{w}).counit) ≪≫ (pushforward B f).rightUnitor

section Sheaves

variable [HasInjectiveResolutions (Sheaf (JX B (X := X)) AddCommGrpCat.{w})]

/-- The cohomology presheaf `V ↦ H^p(X ×_Y V, F)`, computed on an injective resolution. -/
public abbrev preimageCohomologyPresheaf
    (F : Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (p : ℕ) :=
  ((preimageSectionsPresheaf B f).rightDerived p).obj F

/-- Evaluation of the cohomology presheaf at `V` is the cohomology over `X ×_Y V`: the
canonical homology-of-evaluation comparison, using the same injective resolution on both
sides. -/
public def preimageCohomologyPresheafEvaluationIso
    (F : Sheaf (JX B (X := X)) AddCommGrpCat.{w})
    (V : SmallEtale B Y.obj Y.property) (p : ℕ) :
    (preimageCohomologyPresheaf B f F p).obj (Opposite.op V) ≅
      ((sectionsOnPreimage B f V).rightDerived p).obj F :=
  Stacks.DerivedFunctor.rightDerivedEvaluationIso (preimageSectionsPresheaf B f)
    ((evaluation _ AddCommGrpCat.{w}).obj (Opposite.op V)) F p

/-- The objectwise comparison of Stacks 03Q8, normalized by the sheafification counit. -/
public def higherDirectImageSheafificationIso
    (F : Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (p : ℕ) :
    ((pushforward B f).rightDerived p).obj F ≅
      (presheafToSheaf (JY B (Y := Y)) AddCommGrpCat.{w}).obj
        (preimageCohomologyPresheaf B f F p) :=
  (Stacks.DerivedFunctor.rightDerivedIso (sheafifySectionsIso B f) p).symm.app F ≪≫
    (Stacks.DerivedFunctor.rightDerivedEvaluationIso (preimageSectionsPresheaf B f)
      (presheafToSheaf (JY B (Y := Y)) AddCommGrpCat.{w}) F p).symm

/-- A comparison of `R^p f_*` with the sheafified cohomology presheaf, together with its two
normalizations: its components are the objectwise comparison
`higherDirectImageSheafificationIso` (so in particular it cannot be replaced by its negative),
and the restriction maps of the cohomology presheaf are the derived restriction maps of
sections. -/
public structure HigherDirectImageComparison (p : ℕ) where
  /-- The natural isomorphism `R^p f_* ≅ (sheafification of the cohomology presheaf)`. -/
  iso : (pushforward.{u, w} B f).rightDerived p ≅
    (preimageSectionsPresheaf B f).rightDerived p ⋙
      presheafToSheaf (JY B (Y := Y)) AddCommGrpCat.{w}
  /-- Its component at a sheaf is the objectwise counit-normalized comparison. -/
  app_eq (F) : iso.app F = higherDirectImageSheafificationIso B f F p
  /-- The restriction maps of the cohomology presheaf are the derived restriction maps of
  sections over the fibre products. -/
  restriction (F) {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) :
    (preimageCohomologyPresheaf B f F p).map g.op ≫
        (preimageCohomologyPresheafEvaluationIso B f F U p).hom =
      (preimageCohomologyPresheafEvaluationIso B f F V p).hom ≫
        (NatTrans.rightDerived (sectionsRestriction B f g) p).app F

end Sheaves

/-- The sections presheaf on the homotopy category, localized to the derived category. -/
public abbrev homotopyPreimageSectionsPresheaf :=
  (preimageSectionsPresheaf.{u, w} B f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- Direct image on the homotopy category, localized to the derived category. -/
public abbrev homotopyPushforward :=
  (pushforward.{u, w} B f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- Sections over `X ×_Y V` on the homotopy category, localized to the derived category. -/
public abbrev homotopySectionsOnPreimage (V : SmallEtale B Y.obj Y.property) :=
  (sectionsOnPreimage.{u, w} B f V).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- The total right derived functor of the presheaf of sections over the étale base changes. -/
public abbrev derivedPreimageSectionsPresheaf
    [(homotopyPreimageSectionsPresheaf.{u, w} B f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))] :=
  (homotopyPreimageSectionsPresheaf.{u, w} B f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))

/-- The total right derived functor of direct image, i.e. `Rf_*` on unbounded complexes. -/
public abbrev derivedPushforward
    [(homotopyPushforward.{u, w} B f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))] :=
  (homotopyPushforward.{u, w} B f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))

variable [(homotopyPreimageSectionsPresheaf.{u, w} B f).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))]

/-- Hypercohomology of `K` over the étale base changes, as a presheaf on the small étale site
of `Y`. -/
public abbrev preimageHypercohomologyPresheaf
    (K : DerivedCategory (Sheaf (JX B (X := X)) AddCommGrpCat.{w})) (i : ℤ) :=
  (DerivedCategory.homologyFunctor _ i).obj ((derivedPreimageSectionsPresheaf B f).obj K)

/-- Derived sections over a fibre product, obtained by evaluating the derived presheaf of
sections at `V`. The universal property of this evaluation is part of
`DerivedPushforwardComparison`. -/
public abbrev evaluatedDerivedSections (V : SmallEtale B Y.obj Y.property) :=
  derivedPreimageSectionsPresheaf.{u, w} B f ⋙
    ((evaluation _ AddCommGrpCat.{w}).obj (Opposite.op V)).mapDerivedCategory

/-- The unit exhibiting the evaluated derived presheaf of sections as a candidate for the
derived functor of sections over `X ×_Y V`. -/
public def evaluatedDerivedSectionsUnit (V : SmallEtale B Y.obj Y.property) :
    homotopySectionsOnPreimage.{u, w} B f V ⟶
      DerivedCategory.Qh ⋙ evaluatedDerivedSections B f V :=
  (Stacks.DerivedFunctor.postcompHomotopyIso (preimageSectionsPresheaf B f)
    ((evaluation _ AddCommGrpCat.{w}).obj (Opposite.op V))
    (sectionsOnPreimage B f V) (Iso.refl _)).inv ≫
  Functor.whiskerRight ((homotopyPreimageSectionsPresheaf B f).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso
      (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))) _ ≫
  (Functor.associator _ _ _).hom

/-- Evaluation of the hypercohomology presheaf is homology of the evaluated derived
sections. -/
public def preimageHypercohomologyPresheafEvaluationIso
    (V : SmallEtale B Y.obj Y.property) (i : ℤ) :
    derivedPreimageSectionsPresheaf.{u, w} B f ⋙ DerivedCategory.homologyFunctor _ i ⋙
        (evaluation _ AddCommGrpCat.{w}).obj (Opposite.op V) ≅
      evaluatedDerivedSections B f V ⋙ DerivedCategory.homologyFunctor _ i :=
  Functor.isoWhiskerLeft _
      (Stacks.DerivedFunctor.derivedHomologyIso
        ((evaluation _ AddCommGrpCat.{w}).obj (Opposite.op V)) i).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Restriction on hypercohomology, obtained by deriving the restriction of sections with
respect to the specified evaluation units. -/
public def hypercohomologyRestriction
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    (hV : (evaluatedDerivedSections.{u, w} B f V).IsRightDerivedFunctor
      (evaluatedDerivedSectionsUnit B f V)
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ)))
    (i : ℤ) :
    evaluatedDerivedSections B f V ⋙ DerivedCategory.homologyFunctor _ i ⟶
      evaluatedDerivedSections B f U ⋙ DerivedCategory.homologyFunctor _ i :=
  letI := hV
  Functor.whiskerRight
    ((evaluatedDerivedSections B f V).rightDerivedNatTrans
      (evaluatedDerivedSections B f U)
      (evaluatedDerivedSectionsUnit B f V) (evaluatedDerivedSectionsUnit B f U)
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))
      (Functor.whiskerRight ((sectionsRestriction B f g).mapHomotopyCategory (.up ℤ))
        DerivedCategory.Qh)) (DerivedCategory.homologyFunctor _ i)

variable [(homotopyPushforward.{u, w} B f).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))]

/-- The unbounded comparison map: the unique derived descent of the sheafification counit and
the unit of the derived presheaf of sections. Normalizing it this way fixes its compatibility
with maps of sections. -/
public def derivedSheafificationComparison :
    derivedPushforward.{u, w} B f ⟶ derivedPreimageSectionsPresheaf B f ⋙
      (presheafToSheaf (JY B (Y := Y)) AddCommGrpCat.{w}).mapDerivedCategory :=
  (derivedPushforward B f).rightDerivedDesc
    ((homotopyPushforward B f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ)))
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ)) _
    ((Stacks.DerivedFunctor.postcompHomotopyIso (preimageSectionsPresheaf B f)
      (presheafToSheaf (JY B (Y := Y)) AddCommGrpCat.{w})
      (pushforward B f) (sheafifySectionsIso B f)).inv ≫
    Functor.whiskerRight ((homotopyPreimageSectionsPresheaf B f).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso
        (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))) _ ≫
    (Functor.associator _ _ _).hom)

/-- The unbounded clause of Stacks 03Q8: the canonical comparison is invertible, evaluation at
`V` really is the derived functor of sections over `X ×_Y V`, and the restriction maps of the
hypercohomology presheaf are the derived restriction maps. The evaluation clause uses the
ordinary sections functor on the actual fibre product, not a renamed cohomology object. -/
public structure DerivedPushforwardComparison : Prop where
  /-- The canonical comparison is an isomorphism. -/
  isIso : IsIso (derivedSheafificationComparison.{u, w} B f)
  /-- Evaluation at `V` is the total right derived functor of sections over `X ×_Y V`. -/
  evaluation (V : SmallEtale B Y.obj Y.property) :
    (evaluatedDerivedSections B f V).IsRightDerivedFunctor
      (evaluatedDerivedSectionsUnit B f V)
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))
  /-- The restriction maps of the hypercohomology presheaf are the derived restriction maps of
  sections. -/
  restriction {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) (i : ℤ)
      (K : DerivedCategory (Sheaf (JX B (X := X)) AddCommGrpCat.{w})) :
    (preimageHypercohomologyPresheaf B f K i).map g.op ≫
        (preimageHypercohomologyPresheafEvaluationIso B f U i).hom.app K =
      (preimageHypercohomologyPresheafEvaluationIso B f V i).hom.app K ≫
        (hypercohomologyRestriction B f g (evaluation V) i).app K

/-! ### The sheaf clause of Stacks 03Q8

The comparison asked for by `HigherDirectImageComparison` exists: the objectwise comparisons
`higherDirectImageSheafificationIso` are natural in the sheaf, and the restriction maps of the
cohomology presheaf are the derived restriction maps of sections. Both statements come from the
single fact that `Stacks.DerivedFunctor.rightDerivedEvaluationIso` is natural — in the object of
the source category for the first, and in the exact functor being moved for the second.
-/

/-- The component of `Stacks.DerivedFunctor.complexHomologyIso` at a complex `K` is the
comparison of the homologies of the degree-`i` short complex of `K`: every other factor in its
construction is an identity. -/
public lemma complexHomologyIso_app
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (i : ι) (K : HomologicalComplex D c) :
    (Stacks.DerivedFunctor.complexHomologyIso T c i).app K = (K.sc i).mapHomologyIso T := by
  apply Iso.ext
  refine (Category.id_comp _).trans ?_
  refine (Category.id_comp _).trans ?_
  refine (congrArg (fun z ↦ z ≫ _) ((ShortComplex.homologyFunctor E).map_id _)).trans ?_
  change 𝟙 ((K.sc i).map T).homology ≫ 𝟙 _ ≫ ((K.sc i).mapHomologyIso T).hom ≫ 𝟙 _ ≫
      T.map (𝟙 (K.sc i).homology) = ((K.sc i).mapHomologyIso T).hom
  simp

/-- `complexHomologyIso_app` read off in the inverse direction. -/
private lemma complexHomologyIso_inv_app
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (i : ι) (K : HomologicalComplex D c) :
    (Stacks.DerivedFunctor.complexHomologyIso T c i).inv.app K =
      ((K.sc i).mapHomologyIso T).inv :=
  congrArg Iso.inv (complexHomologyIso_app T c i K)

/-- `Stacks.DerivedFunctor.complexHomologyIso` is natural in the functor: a morphism
`τ : T ⟶ S` of homology-preserving functors is carried to the map it induces on the homology of
the images of a complex. -/
private lemma complexHomologyIso_inv_app_natTrans
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    {T S : D ⥤ E} [T.Additive] [T.PreservesHomology] [S.Additive] [S.PreservesHomology]
    (τ : T ⟶ S) {ι : Type*} (c : ComplexShape ι) (i : ι) (K : HomologicalComplex D c) :
    τ.app ((HomologicalComplex.homologyFunctor D c i).obj K) ≫
        (Stacks.DerivedFunctor.complexHomologyIso S c i).inv.app K =
      (Stacks.DerivedFunctor.complexHomologyIso T c i).inv.app K ≫
        (HomologicalComplex.homologyFunctor E c i).map ((τ.mapHomologicalComplex c).app K) := by
  have h : τ.app (K.sc i).homology ≫ ((K.sc i).mapHomologyIso S).inv =
      ((K.sc i).mapHomologyIso T).inv ≫
        ShortComplex.homologyMap ((K.sc i).mapNatTrans τ) := by
    rw [ShortComplex.homologyMap_mapNatTrans, Iso.inv_hom_id_assoc]
  rw [complexHomologyIso_inv_app, complexHomologyIso_inv_app]
  exact h

/-- `Stacks.DerivedFunctor.rightDerivedEvaluationIso` written out on the chosen injective
resolution of `F`. -/
private lemma rightDerivedEvaluationIso_hom
    {A D E : Type*} [Category A] [Category D] [Category E]
    [Abelian A] [Abelian D] [Abelian E] [HasInjectiveResolutions A]
    (P : A ⥤ D) [P.Additive] (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    (F : A) (p : ℕ) :
    (Stacks.DerivedFunctor.rightDerivedEvaluationIso P T F p).hom =
      T.map ((injectiveResolution F).isoRightDerivedObj P p).hom ≫
        (Stacks.DerivedFunctor.complexHomologyIso T (ComplexShape.up ℕ) p).inv.app
            ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution F).cocomplex) ≫
          ((injectiveResolution F).isoRightDerivedObj (P ⋙ T) p).inv :=
  rfl

/-- The objectwise comparison `Stacks.DerivedFunctor.rightDerivedEvaluationIso` is natural in
the object: both sides are computed on the chosen injective resolutions, and a descent of the
morphism between them intertwines the two identifications. -/
private lemma rightDerivedEvaluationIso_naturality_obj
    {A D E : Type*} [Category A] [Category D] [Category E]
    [Abelian A] [Abelian D] [Abelian E] [HasInjectiveResolutions A]
    (P : A ⥤ D) [P.Additive] (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    {F F' : A} (a : F ⟶ F') (p : ℕ) :
    T.map ((P.rightDerived p).map a) ≫
        (Stacks.DerivedFunctor.rightDerivedEvaluationIso P T F' p).hom =
      (Stacks.DerivedFunctor.rightDerivedEvaluationIso P T F p).hom ≫
        ((P ⋙ T).rightDerived p).map a := by
  set φ := InjectiveResolution.desc a (injectiveResolution F') (injectiveResolution F)
  have hcomm : (injectiveResolution F).ι.f 0 ≫ φ.f 0 = a ≫ (injectiveResolution F').ι.f 0 :=
    InjectiveResolution.desc_commutes_zero a (injectiveResolution F') (injectiveResolution F)
  have hT : T.map ((P.rightDerived p).map a) ≫
      T.map ((injectiveResolution F').isoRightDerivedObj P p).hom =
    T.map ((injectiveResolution F).isoRightDerivedObj P p).hom ≫
      T.map ((P.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) p).map φ) := by
    simpa only [Functor.map_comp] using congrArg T.map
      (InjectiveResolution.isoRightDerivedObj_hom_naturality a (injectiveResolution F)
        (injectiveResolution F') φ hcomm P p)
  rw [rightDerivedEvaluationIso_hom, rightDerivedEvaluationIso_hom, reassoc_of% hT,
    reassoc_of% (Stacks.DerivedFunctor.complexHomologyIso T (ComplexShape.up ℕ) p).inv.naturality
      ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)]
  simp only [Category.assoc]
  rw [InjectiveResolution.isoRightDerivedObj_inv_naturality a (injectiveResolution F)
    (injectiveResolution F') φ hcomm (P ⋙ T) p]
  rfl

/-- **An exact functor passes through a right derived functor, naturally.** The objectwise
comparisons `Stacks.DerivedFunctor.rightDerivedEvaluationIso` are the components of a natural
isomorphism `P.rightDerived p ⋙ T ≅ (P ⋙ T).rightDerived p`. -/
private def rightDerivedEvaluationNatIso
    {A D E : Type*} [Category A] [Category D] [Category E]
    [Abelian A] [Abelian D] [Abelian E] [HasInjectiveResolutions A]
    (P : A ⥤ D) [P.Additive] (T : D ⥤ E) [T.Additive] [T.PreservesHomology] (p : ℕ) :
    P.rightDerived p ⋙ T ≅ (P ⋙ T).rightDerived p :=
  NatIso.ofComponents (fun F ↦ Stacks.DerivedFunctor.rightDerivedEvaluationIso P T F p)
    fun a ↦ rightDerivedEvaluationIso_naturality_obj P T a p

/-- The objectwise comparison `Stacks.DerivedFunctor.rightDerivedEvaluationIso` is natural in
the exact functor being moved: a morphism `τ : T ⟶ S` of exact functors is carried to the
derived functor of `Functor.whiskerLeft P τ`. -/
private lemma rightDerivedEvaluationIso_naturality
    {A D E : Type*} [Category A] [Category D] [Category E]
    [Abelian A] [Abelian D] [Abelian E] [HasInjectiveResolutions A]
    (P : A ⥤ D) [P.Additive] {T S : D ⥤ E} [T.Additive] [T.PreservesHomology]
    [S.Additive] [S.PreservesHomology] (τ : T ⟶ S) (F : A) (p : ℕ) :
    τ.app ((P.rightDerived p).obj F) ≫
        (Stacks.DerivedFunctor.rightDerivedEvaluationIso P S F p).hom =
      (Stacks.DerivedFunctor.rightDerivedEvaluationIso P T F p).hom ≫
        (NatTrans.rightDerived (Functor.whiskerLeft P τ) p).app F := by
  rw [rightDerivedEvaluationIso_hom, rightDerivedEvaluationIso_hom,
    InjectiveResolution.rightDerived_app_eq _ (injectiveResolution F), Category.assoc,
    Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, ← τ.naturality, Category.assoc,
    reassoc_of% complexHomologyIso_inv_app_natTrans τ (ComplexShape.up ℕ) p
      ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)]
  rfl

section SheafComparison

omit [(homotopyPreimageSectionsPresheaf.{u, w} B f).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))]
  [(homotopyPushforward.{u, w} B f).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))]

variable [HasInjectiveResolutions (Sheaf (JX B (X := X)) AddCommGrpCat.{w})]

omit [HasSheafify (JY B (Y := Y)) AddCommGrpCat.{w}] in
/-- The restriction maps of the cohomology presheaf are the derived restriction maps of
sections over the fibre products: both are the derived functor of restriction of sections,
read through the evaluation comparison. -/
private lemma preimageCohomologyPresheafEvaluationIso_naturality
    (F : Sheaf (JX B (X := X)) AddCommGrpCat.{w})
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) (p : ℕ) :
    (preimageCohomologyPresheaf B f F p).map g.op ≫
        (preimageCohomologyPresheafEvaluationIso B f F U p).hom =
      (preimageCohomologyPresheafEvaluationIso B f F V p).hom ≫
        (NatTrans.rightDerived (sectionsRestriction B f g) p).app F :=
  rightDerivedEvaluationIso_naturality (preimageSectionsPresheaf B f)
    ((evaluation _ AddCommGrpCat.{w}).map g.op) F p

/-- **Stacks 03Q8 for abelian sheaves.** The higher direct image `R^p f_*` is the sheafification
of the presheaf `V ↦ H^p_ét(X ×_Y V, F)`, by a natural isomorphism whose components are the
counit-normalized objectwise comparison `higherDirectImageSheafificationIso`, and whose
cohomology presheaf has the derived restriction maps of sections. -/
@[stacks 03Q8 "abelian sheaves", no_expose]
public def higherDirectImageComparison (p : ℕ) :
    HigherDirectImageComparison.{u, w} B f p where
  iso := (Stacks.DerivedFunctor.rightDerivedIso (sheafifySectionsIso B f) p).symm ≪≫
    (rightDerivedEvaluationNatIso (preimageSectionsPresheaf B f)
      (presheafToSheaf (JY B (Y := Y)) AddCommGrpCat.{w}) p).symm
  app_eq _ := rfl
  restriction := fun F {_ _} g ↦
    preimageCohomologyPresheafEvaluationIso_naturality B f F g p

end SheafComparison

end Stacks.HigherDirectImage
