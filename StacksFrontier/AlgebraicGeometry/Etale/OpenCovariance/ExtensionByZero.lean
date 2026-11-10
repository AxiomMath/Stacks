module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance.Postcompose

/-!
# Extension by zero along the comparison of canonical support opens

Let `j : X' ⟶ X` be an open immersion in a big étale site and `f : X ⟶ Y`. For a support finite
over an étale test object `V`, living on `X'_V`, this file compares its canonical open with the
canonical open of its image support on `X_V`, and constructs the extension by zero of sections:
a section on `X'_V` supported on the original support gives a section on `X_V` supported on the
image support. This is the sectionwise content of the covariance map of Stacks 0F6S.

## Main definitions

* `AlgebraicGeometry.SmallEtale.covarianceTargetOpenMap` and
  `AlgebraicGeometry.SmallEtale.covarianceOpenMap` — the comparison of the canonical opens of a
  support and of its image, and `AlgebraicGeometry.SmallEtale.covarianceSectionMap` the
  resulting extension by zero on supported sections.
* `AlgebraicGeometry.SmallEtale.openFiniteSupportPushforward` and
  `AlgebraicGeometry.SmallEtale.wholeFiniteSupportPushforward` — the finite-support direct image
  presheaf functors `(j ≫ f)_{p!}((-)|_{X'})` and `f_{p!}`.

## Main results

* `AlgebraicGeometry.SmallEtale.covarianceClosedSupportEquiv` — extension by zero: sections on
  `X_V` supported on the image of a support are exactly the sections on the canonical open of
  the original support which are supported there.
* `AlgebraicGeometry.SmallEtale.covarianceSectionMap_map` and
  `AlgebraicGeometry.SmallEtale.covarianceSectionMap_sheaf` — the extension by zero commutes
  with restriction and with morphisms of abelian sheaves, which is what makes the covariance
  map a natural transformation of functors.

## Implementation notes

The comparison of canonical opens is obtained as an adjoint transpose: the morphism over `X` is
the factorization of the induced open immersion through the canonical open of the image support
(`AlgebraicGeometry.SmallEtale.factorThroughOpenObject`), and its transpose under
`AlgebraicGeometry.SmallEtale.openPostcomposeAdjunction` is
`AlgebraicGeometry.SmallEtale.covarianceOpenMap`. Extension by zero is then the inverse of the
canonical bijection of Stacks 0F6F between sections supported on corresponding closed
subschemes, applied to the reduced closed subscheme of the original support.

## References

* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)]

section TargetOpenMap

variable (f : X ⟶ Y) (V : SmallEtale B Y.obj Y.property)
  (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
  (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1)

/-- The canonical open of the original support, viewed over `X`, maps to the canonical open of
the image support: it is the factorization of the induced open immersion through that open. -/
public def covarianceTargetOpenMap :
    (openPostcompose B j).obj (openCovarianceSupportObject B (j ≫ f) V E) ⟶
      openCovarianceSupportObject B f V D :=
  factorThroughOpenObject B X.obj X.property _ (baseChange B f V)
    ((openPostcompose B j).map
        (openObjectι B X'.obj X'.property (baseChange B (j ≫ f) V)
          (openCovarianceSupportOpen B (j ≫ f) V E)) ≫
      (openBaseChangeMap B j f).app V)
    (openCovarianceSupportOpen B f V D)
    (by
      rintro x ⟨y, rfl⟩
      have hy : ((SmallEtale.toScheme B X.obj X.property).map
            ((openPostcompose B j).map
              (openObjectι B X'.obj X'.property (baseChange B (j ≫ f) V)
                (openCovarianceSupportOpen B (j ≫ f) V E)) ≫
              (openBaseChangeMap B j f).app V)).base y =
          (openBaseChangeHom B j f V).base
            ((openCovarianceSupportOpen B (j ≫ f) V E).ι.base y) := by
        rw [Functor.map_comp, openPostcompose_toScheme_map, openObjectι_map,
          openBaseChangeMap_toScheme]
        rfl
      have hmem : (openCovarianceSupportOpen B (j ≫ f) V E).ι.base y ∈
          ((openCovarianceSupportOpen B (j ≫ f) V E) :
            Set ((SmallEtale.toScheme B X'.obj X'.property).obj
              (baseChange B (j ≫ f) V))) := by
        rw [← Scheme.Opens.range_ι]
        exact Set.mem_range_self y
      rw [← openBaseChangeHom_supportOpen_preimage B j f V E D hD] at hmem
      rw [hy]
      exact hmem)

/-- The canonical map of supported opens is a factorization of the induced open immersion. -/
public theorem covarianceTargetOpenMap_fac :
    covarianceTargetOpenMap B j f V E D hD ≫
        openObjectι B X.obj X.property (baseChange B f V)
          (openCovarianceSupportOpen B f V D) =
      (openPostcompose B j).map
          (openObjectι B X'.obj X'.property (baseChange B (j ≫ f) V)
            (openCovarianceSupportOpen B (j ≫ f) V E)) ≫
        (openBaseChangeMap B j f).app V :=
  factorThroughOpenObject_fac B X.obj X.property _ (baseChange B f V) _
    (openCovarianceSupportOpen B f V D) _

/-- The map of canonical opens is compatible with the two open inclusions and the induced open
immersion of base changes. -/
public theorem covarianceTargetOpenMap_commutes :
    (SmallEtale.toScheme B X.obj X.property).map (covarianceTargetOpenMap B j f V E D hD) ≫
        (openCovarianceSupportOpen B f V D).ι =
      (openCovarianceSupportOpen B (j ≫ f) V E).ι ≫ openBaseChangeHom B j f V := by
  have h := congrArg (SmallEtale.toScheme B X.obj X.property).map
    (covarianceTargetOpenMap_fac B j f V E D hD)
  rw [Functor.map_comp, Functor.map_comp, openObjectι_map, openPostcompose_toScheme_map,
    openObjectι_map, openBaseChangeMap_toScheme] at h
  exact h

/-- The canonical map of supported opens is an open immersion. -/
public instance covarianceTargetOpenMap_isOpenImmersion :
    IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
      (covarianceTargetOpenMap B j f V E D hD)) := by
  have hcomp : IsOpenImmersion
      ((SmallEtale.toScheme B X.obj X.property).map
        (covarianceTargetOpenMap B j f V E D hD) ≫
        (openCovarianceSupportOpen B f V D).ι) := by
    rw [covarianceTargetOpenMap_commutes]
    exact MorphismProperty.comp_mem @IsOpenImmersion
      (openCovarianceSupportOpen B (j ≫ f) V E).ι (openBaseChangeHom B j f V)
      (inferInstanceAs (IsOpenImmersion (openCovarianceSupportOpen B (j ≫ f) V E).ι))
      inferInstance
  exact IsOpenImmersion.of_comp _ (openCovarianceSupportOpen B f V D).ι

/-- Pointwise form of the compatibility of the map of canonical opens with the open inclusions. -/
private theorem covarianceTargetOpenMap_ι_apply
    (x : (↑(openCovarianceSupportOpen B (j ≫ f) V E) : Scheme)) :
    (openCovarianceSupportOpen B f V D).ι.base
      (((SmallEtale.toScheme B X.obj X.property).map
        (covarianceTargetOpenMap B j f V E D hD)).base x) =
    (openBaseChangeHom B j f V).base ((openCovarianceSupportOpen B (j ≫ f) V E).ι.base x) :=
  congrArg (fun g => g.base x) (covarianceTargetOpenMap_commutes B j f V E D hD)

/-- The canonical map of supported opens pulls the image support back to the original
support. -/
public theorem covarianceTargetOpenMap_support_preimage :
    ((SmallEtale.toScheme B X.obj X.property).map
      (covarianceTargetOpenMap B j f V E D hD)).base ⁻¹'
        ((openCovarianceSupportOpen B f V D).ι.base ⁻¹' D.1) =
      (openCovarianceSupportOpen B (j ≫ f) V E).ι.base ⁻¹' E.1 := by
  have himage : (openBaseChangeHom B j f V).base ⁻¹' D.1 = E.1 := by
    rw [hD]
    exact Set.preimage_image_eq _ (openBaseChangeHom B j f V).isOpenEmbedding.injective
  ext x
  change (openCovarianceSupportOpen B f V D).ι.base
      (((SmallEtale.toScheme B X.obj X.property).map
        (covarianceTargetOpenMap B j f V E D hD)).base x) ∈ D.1 ↔
    (openCovarianceSupportOpen B (j ≫ f) V E).ι.base x ∈ E.1
  exact (Iff.of_eq (congrArg (· ∈ D.1) (covarianceTargetOpenMap_ι_apply B j f V E D hD x))).trans
    (Set.ext_iff.mp himage _)

/-- The image support inside its canonical open is covered by the canonical map. -/
public theorem covarianceTargetOpenMap_support_subset_range :
    (openCovarianceSupportOpen B f V D).ι.base ⁻¹' D.1 ⊆
      Set.range ((SmallEtale.toScheme B X.obj X.property).map
        (covarianceTargetOpenMap B j f V E D hD)).base := by
  have hE : E.1 ⊆ openCovarianceSupportOpen B (j ≫ f) V E :=
    subset_supportOpen B X'.obj X'.property (baseChange B (j ≫ f) V) E.1
      (finiteSupport_isLocallyClosed B (j ≫ f) V E)
  intro t ht
  have htD : (openCovarianceSupportOpen B f V D).ι.base t ∈ D.1 := ht
  rw [hD] at htD
  obtain ⟨x, hxE, hxφ⟩ := htD
  refine ⟨⟨x, hE hxE⟩, ?_⟩
  apply (openCovarianceSupportOpen B f V D).ι.isOpenEmbedding.injective
  exact (covarianceTargetOpenMap_ι_apply B j f V E D hD ⟨x, hE hxE⟩).trans hxφ

/-- The canonical map of supported opens carries the original support onto the image
support. -/
public theorem covarianceTargetOpenMap_support_image :
    ((SmallEtale.toScheme B X.obj X.property).map
      (covarianceTargetOpenMap B j f V E D hD)).base ''
        ((openCovarianceSupportOpen B (j ≫ f) V E).ι.base ⁻¹' E.1) =
      (openCovarianceSupportOpen B f V D).ι.base ⁻¹' D.1 :=
  (congrArg (Set.image ((SmallEtale.toScheme B X.obj X.property).map
      (covarianceTargetOpenMap B j f V E D hD)).base)
    (covarianceTargetOpenMap_support_preimage B j f V E D hD).symm).trans
    (Set.image_preimage_eq_of_subset
      (covarianceTargetOpenMap_support_subset_range B j f V E D hD))

/-- The original support, as a closed subset of its own canonical open. -/
public abbrev covarianceSupportCloseds :
    TopologicalSpace.Closeds (↑(openCovarianceSupportOpen B (j ≫ f) V E) : Scheme) :=
  ⟨(openCovarianceSupportOpen B (j ≫ f) V E).ι.base ⁻¹' E.1,
    isClosed_supportOpen_preimage B X'.obj X'.property (baseChange B (j ≫ f) V) E.1
      (finiteSupport_isLocallyClosed B (j ≫ f) V E)⟩

omit [IsOpenImmersion (B.inclusion.map j)] in
/-- The reduced closed subscheme of the original support has the original support as its
image. -/
public theorem covarianceSupportCloseds_range :
    Set.range (Scheme.IdealSheafData.vanishingIdeal
        (covarianceSupportCloseds B j f V E)).subschemeι.base =
      (openCovarianceSupportOpen B (j ≫ f) V E).ι.base ⁻¹' E.1 := by
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The reduced closed subscheme of the original support has image the image support inside
its canonical open. -/
public theorem covarianceTargetOpenMap_subscheme_range :
    Set.range ((Scheme.IdealSheafData.vanishingIdeal
          (covarianceSupportCloseds B j f V E)).subschemeι ≫
        (SmallEtale.toScheme B X.obj X.property).map
          (covarianceTargetOpenMap B j f V E D hD)).base =
      (openCovarianceSupportOpen B f V D).ι.base ⁻¹' D.1 := by
  let i := (Scheme.IdealSheafData.vanishingIdeal (covarianceSupportCloseds B j f V E)).subschemeι
  let q : (↑(openCovarianceSupportOpen B (j ≫ f) V E) : Scheme) ⟶
      (↑(openCovarianceSupportOpen B f V D) : Scheme) :=
    (SmallEtale.toScheme B X.obj X.property).map (covarianceTargetOpenMap B j f V E D hD)
  change Set.range (i ≫ q).base = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    covarianceSupportCloseds_range B j f V E]
  exact covarianceTargetOpenMap_support_image B j f V E D hD

/-- The reduced closed subscheme of the original support is a closed subscheme of the canonical
open of the image support. -/
public theorem covarianceTargetOpenMap_closedSupport :
    IsClosedImmersion ((Scheme.IdealSheafData.vanishingIdeal
        (covarianceSupportCloseds B j f V E)).subschemeι ≫
      (SmallEtale.toScheme B X.obj X.property).map
        (covarianceTargetOpenMap B j f V E D hD)) := by
  let i := (Scheme.IdealSheafData.vanishingIdeal (covarianceSupportCloseds B j f V E)).subschemeι
  let q : (↑(openCovarianceSupportOpen B (j ≫ f) V E) : Scheme) ⟶
      (↑(openCovarianceSupportOpen B f V D) : Scheme) :=
    (SmallEtale.toScheme B X.obj X.property).map (covarianceTargetOpenMap B j f V E D hD)
  have hclosed : IsClosed ((openCovarianceSupportOpen B f V D).ι.base ⁻¹' D.1) :=
    isClosed_supportOpen_preimage B X.obj X.property (baseChange B f V) D.1
      (finiteSupport_isLocallyClosed B f V D)
  have : IsOpenImmersion q := covarianceTargetOpenMap_isOpenImmersion B j f V E D hD
  have : IsImmersion (i ≫ q) := inferInstance
  exact IsClosedImmersion.of_isPreimmersion (i ≫ q)
    (covarianceTargetOpenMap_subscheme_range B j f V E D hD ▸ hclosed)

/-- The canonical open map of the covariance generator data: the adjoint transpose of
`AlgebraicGeometry.SmallEtale.covarianceTargetOpenMap`. -/
public def covarianceOpenMap :
    openCovarianceSupportObject B (j ≫ f) V E ⟶
      (smallEtaleBaseChange B j).obj (openCovarianceSupportObject B f V D) :=
  (openPostcomposeAdjunction B j).homEquiv _ _ (covarianceTargetOpenMap B j f V E D hD)

/-- The adjoint transpose of the canonical open map recovers it. -/
public theorem covarianceOpenMap_counit :
    (openPostcompose B j).map (covarianceOpenMap B j f V E D hD) ≫
        (openPostcomposeAdjunction B j).counit.app _ =
      covarianceTargetOpenMap B j f V E D hD :=
  ((openPostcomposeAdjunction B j).homEquiv_counit _ _
      (covarianceOpenMap B j f V E D hD)).symm.trans
    (((openPostcomposeAdjunction B j).homEquiv _ _).symm_apply_apply _)

/-- The compatibility of the canonical open map with the two open inclusions, in the form the
covariance generator data records it. -/
public theorem covarianceOpenMap_commutes :
    (SmallEtale.toScheme B X'.obj X'.property).map (covarianceOpenMap B j f V E D hD) ≫
        B.inclusion.map
          (pullback.fst ((openCovarianceSupportObject B f V D).obj.hom) j) ≫
        (openCovarianceSupportOpen B f V D).ι =
      (openCovarianceSupportOpen B (j ≫ f) V E).ι ≫ openBaseChangeHom B j f V := by
  have h := congrArg (SmallEtale.toScheme B X.obj X.property).map
    (covarianceOpenMap_counit B j f V E D hD)
  rw [Functor.map_comp, openPostcompose_toScheme_map,
    openPostcomposeAdjunction_counit_toScheme] at h
  have h3 := congrArg (fun k => k ≫ (openCovarianceSupportOpen B f V D).ι) h
  exact (Category.assoc _ _ _).symm.trans
    (h3.trans (covarianceTargetOpenMap_commutes B j f V E D hD))

end TargetOpenMap

section SupportCriteria

variable (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- A section is supported in a subset exactly when it restricts to zero on an open immersion
of the small étale site whose image is the complement of that subset. -/
public theorem supportSection_subset_iff_zero_on_open {W' W : SmallEtale B S hS} (i : W' ⟶ W)
    [IsOpenImmersion ((SmallEtale.toScheme B S hS).map i)]
    (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (hRange : Set.range ((SmallEtale.toScheme B S hS).map i).base = Zᶜ)
    (s : F.obj.obj (op W)) :
    supportSection B S hS F W s ⊆ Z ↔ F.obj.map i.op s = 0 := by
  rw [map_eq_zero_iff_le_zeroOpen B S hS F W s _ i]
  simp only [supportSection, Set.compl_subset_comm]
  change Zᶜ ⊆ (zeroOpen B S hS F W s : Set _) ↔
    (Scheme.Hom.opensRange ((SmallEtale.toScheme B S hS).map i) :
      Set ((SmallEtale.toScheme B S hS).obj W)) ⊆ _
  rw [Scheme.Hom.coe_opensRange, hRange]

/-- Restriction along a morphism of the small étale site identifies sections supported on a
closed subscheme with sections supported on its inverse image, when the inverse image of the
image of that closed subscheme is the closed subscheme itself. -/
public def closedSupportedSectionsRestriction
    (T A : SmallEtale B S hS) (q : A ⟶ T)
    (C : Set ((SmallEtale.toScheme B S hS).obj A))
    (D : Set ((SmallEtale.toScheme B S hS).obj T))
    (Z : Scheme.{u}) (i : Z ⟶ (SmallEtale.toScheme B S hS).obj A)
    [IsClosedImmersion i] [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map q)]
    (hi : Set.range i.base = C)
    (hiq : Set.range (i ≫ (SmallEtale.toScheme B S hS).map q).base = D)
    (hq : ((SmallEtale.toScheme B S hS).map q).base ⁻¹' D = C) :
    {e : sectionsSupportedOn B S hS F T D ≃+ sectionsSupportedOn B S hS F A C //
      ∀ s, (e s).val = F.obj.map q.op s.val} := by
  subst C D
  let e := supportedSectionsEquiv B S hS F T A q Z i
  have he (s : sectionsSupportedOn B S hS F T
      (Set.range (i ≫ (SmallEtale.toScheme B S hS).map q).base)) :
      (e s).val = F.obj.map q.op s.val := by
    have h := supportedSectionsEquiv_restrict B S hS F T A q Z i A (𝟙 A)
      (by simpa using hq) s
    simpa using h
  refine ⟨{ toEquiv := e, map_add' := ?_ }, he⟩
  intro s t
  apply Subtype.ext
  change (e (s + t)).val = (e s).val + (e t).val
  rw [he, he, he]
  exact map_add _ _ _

end SupportCriteria

section Extension

variable (f : X ⟶ Y)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The direct image along post-composition is restriction along post-composition on each
object of the small étale site. -/
public theorem openPostcompose_sheafPushforward_map
    {W W' : SmallEtale B X'.obj X'.property} (g : W' ⟶ W) :
    (((openPostcompose B j).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property)).obj F).obj.map g.op =
      F.obj.map ((openPostcompose B j).map g).op := rfl

/-- The comparison of the two descriptions of restriction does not enlarge the support of a
section supported in a closed subset. -/
public theorem openRestrictionIso_inv_support_subset (W : SmallEtale B X'.obj X'.property)
    (Z : Set ((SmallEtale.toScheme B X'.obj X'.property).obj W)) (hZ : IsClosed Z)
    (s : ((openRestriction B j).obj F).obj.obj (op W))
    (hs : supportSection B X'.obj X'.property ((openRestriction B j).obj F) W s ⊆ Z) :
    supportSection B X.obj X.property F ((openPostcompose B j).obj W)
      (((openRestrictionIso.{u, v} B j).inv.app F).hom.app (op W) s) ⊆ Z := by
  let U : ((SmallEtale.toScheme B X'.obj X'.property).obj W).Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  let i := openObjectι B X'.obj X'.property W U
  have hRange : Set.range ((SmallEtale.toScheme B X'.obj X'.property).map i).base = Zᶜ := by
    rw [openObjectι_map, Scheme.Opens.range_ι]
    rfl
  have hs0 := (supportSection_subset_iff_zero_on_open B X'.obj X'.property
    ((openRestriction B j).obj F) i Z hRange s).mp hs
  have hiX : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
      ((openPostcompose B j).map i)) := by
    rw [openPostcompose_toScheme_map]
    exact isOpenImmersion_openObjectι B X'.obj X'.property W U
  have hRangeX : Set.range ((SmallEtale.toScheme B X.obj X.property).map
      ((openPostcompose B j).map i)).base = Zᶜ := by
    rw [openPostcompose_toScheme_map]
    exact hRange
  refine (supportSection_subset_iff_zero_on_open B X.obj X.property F
    ((openPostcompose B j).map i) Z hRangeX _).mpr ?_
  have hn := ((openRestrictionIso.{u, v} B j).inv.app F).hom.naturality i.op
  rw [openPostcompose_sheafPushforward_map B j F i] at hn
  rw [← openPostcompose_sheafPushforward_map B j F i]
  calc
    _ = (((openRestrictionIso.{u, v} B j).inv.app F).hom.app (op W) ≫
        (((openPostcompose B j).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X'.obj X'.property)
          (SmallEtale.topology B X.obj X.property)).obj F).obj.map i.op) s :=
      (ConcreteCategory.comp_apply _ _ s).symm
    _ = (((openRestriction B j).obj F).obj.map i.op ≫
        ((openRestrictionIso.{u, v} B j).inv.app F).hom.app (op _)) s :=
      (ConcreteCategory.congr_hom hn s).symm
    _ = 0 := by rw [ConcreteCategory.comp_apply, hs0, map_zero]

/-- On a closed support, the comparison of the two descriptions of restriction is an additive
map of supported sections. -/
public def openRestrictionSupportedSectionsMap (W : SmallEtale B X'.obj X'.property)
    (Z : Set ((SmallEtale.toScheme B X'.obj X'.property).obj W)) (hZ : IsClosed Z) :
    sectionsSupportedOn B X'.obj X'.property ((openRestriction B j).obj F) W Z →+
      sectionsSupportedOn B X.obj X.property F ((openPostcompose B j).obj W) Z where
  toFun s := ⟨((openRestrictionIso.{u, v} B j).inv.app F).hom.app (op W) s.val,
    openRestrictionIso_inv_support_subset B j F W Z hZ s.val s.property⟩
  map_zero' := Subtype.ext
    (((openRestrictionIso.{u, v} B j).inv.app F).hom.app (op W)).hom.map_zero
  map_add' _ _ := Subtype.ext
    ((((openRestrictionIso.{u, v} B j).inv.app F).hom.app (op W)).hom.map_add _ _)

/-- Extension by zero across the comparison of canonical support opens: sections of `F` on
`X_V` supported on the image support are exactly the sections on the canonical open of the
original support which are supported there. -/
public def covarianceClosedSupportEquiv (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    {e : supportedSections B X.obj X.property F (baseChange B f V) D.1
          (finiteSupport_isLocallyClosed B f V D) ≃+
        sectionsSupportedOn B X.obj X.property F
          ((openPostcompose B j).obj (openCovarianceSupportObject B (j ≫ f) V E))
          ((openCovarianceSupportOpen B (j ≫ f) V E).ι.base ⁻¹' E.1) //
      ∀ s, (e s).val = F.obj.map (covarianceTargetOpenMap B j f V E D hD).op s.val} := by
  refine @closedSupportedSectionsRestriction B X.obj X.property F
    (openCovarianceSupportObject B f V D)
    ((openPostcompose B j).obj (openCovarianceSupportObject B (j ≫ f) V E))
    (covarianceTargetOpenMap B j f V E D hD) _ _ _
    (Scheme.IdealSheafData.vanishingIdeal
      (covarianceSupportCloseds B j f V E)).subschemeι
    (IsClosedImmersion.instSubschemeι _)
    (covarianceTargetOpenMap_closedSupport B j f V E D hD)
    (covarianceSupportCloseds_range B j f V E)
    (covarianceTargetOpenMap_subscheme_range B j f V E D hD)
    (covarianceTargetOpenMap_support_preimage B j f V E D hD)

/-- Extension by zero through the comparison of canonical support opens. -/
public def covarianceClosedSupportExtension (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    sectionsSupportedOn B X.obj X.property F
        ((openPostcompose B j).obj (openCovarianceSupportObject B (j ≫ f) V E))
        ((openCovarianceSupportOpen B (j ≫ f) V E).ι.base ⁻¹' E.1) →+
      supportedSections B X.obj X.property F (baseChange B f V) D.1
        (finiteSupport_isLocallyClosed B f V D) :=
  (covarianceClosedSupportEquiv B j f F V E D hD).val.symm.toAddMonoidHom

/-- Extension by zero restricts back to the original section. -/
public theorem covarianceClosedSupportExtension_restrict (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1)
    (s : sectionsSupportedOn B X.obj X.property F
      ((openPostcompose B j).obj (openCovarianceSupportObject B (j ≫ f) V E))
      ((openCovarianceSupportOpen B (j ≫ f) V E).ι.base ⁻¹' E.1)) :
    F.obj.map (covarianceTargetOpenMap B j f V E D hD).op
      (covarianceClosedSupportExtension B j f F V E D hD s).val = s.val := by
  rw [← (covarianceClosedSupportEquiv B j f F V E D hD).property]
  exact congrArg Subtype.val
    ((covarianceClosedSupportEquiv B j f F V E D hD).val.apply_symm_apply s)

/-- Restriction to the canonical open of the original support is injective on sections
supported on the image support. -/
public theorem covarianceTargetOpenMap_restrict_injective (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    Function.Injective (fun s : supportedSections B X.obj X.property F (baseChange B f V) D.1
      (finiteSupport_isLocallyClosed B f V D) =>
        F.obj.map (covarianceTargetOpenMap B j f V E D hD).op s.val) := by
  intro s t h
  apply (covarianceClosedSupportEquiv B j f F V E D hD).val.injective
  apply Subtype.ext
  simpa only [(covarianceClosedSupportEquiv B j f F V E D hD).property] using h

/-- The canonical map on supported sections: regard a section on the open subscheme supported
on a finite support as a section on the whole source supported on the image of that support. -/
public def covarianceSectionMap (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    supportedSections B X'.obj X'.property ((openRestriction B j).obj F)
        (baseChange B (j ≫ f) V) E.1 (finiteSupport_isLocallyClosed B (j ≫ f) V E) →+
      supportedSections B X.obj X.property F (baseChange B f V) D.1
        (finiteSupport_isLocallyClosed B f V D) :=
  (covarianceClosedSupportExtension B j f F V E D hD).comp
    (openRestrictionSupportedSectionsMap B j F _ _
      (isClosed_supportOpen_preimage B X'.obj X'.property (baseChange B (j ≫ f) V) E.1
        (finiteSupport_isLocallyClosed B (j ≫ f) V E)))

/-- The canonical map on supported sections restricts back, through the comparison of the two
descriptions of restriction, to the original section. -/
public theorem covarianceSectionMap_restrict (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1)
    (s : supportedSections B X'.obj X'.property ((openRestriction B j).obj F)
      (baseChange B (j ≫ f) V) E.1 (finiteSupport_isLocallyClosed B (j ≫ f) V E)) :
    F.obj.map (covarianceTargetOpenMap B j f V E D hD).op
        (covarianceSectionMap B j f F V E D hD s).val =
      ((openRestrictionIso.{u, v} B j).inv.app F).hom.app _ s.val :=
  covarianceClosedSupportExtension_restrict B j f F V E D hD _

/-- Compatibility of the canonical maps of supported opens with a morphism of étale test
objects. -/
public theorem covarianceTargetOpenMap_square {V V' : SmallEtale B Y.obj Y.property}
    (g : V' ⟶ V) (E : FiniteSupport B (j ≫ f) V) (E' : FiniteSupport B (j ≫ f) V')
    (D : FiniteSupport B f V) (D' : FiniteSupport B f V')
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1)
    (hD' : D'.1 = (openBaseChangeHom B j f V').base '' E'.1)
    (a : openCovarianceSupportObject B (j ≫ f) V' E' ⟶
      openCovarianceSupportObject B (j ≫ f) V E)
    (b : openCovarianceSupportObject B f V' D' ⟶ openCovarianceSupportObject B f V D)
    (ha : (SmallEtale.toScheme B X'.obj X'.property).map a ≫
        (openCovarianceSupportOpen B (j ≫ f) V E).ι =
      (openCovarianceSupportOpen B (j ≫ f) V' E').ι ≫
        (SmallEtale.toScheme B X'.obj X'.property).map
          ((smallEtaleBaseChange B (j ≫ f)).map g))
    (hb : (SmallEtale.toScheme B X.obj X.property).map b ≫
        (openCovarianceSupportOpen B f V D).ι =
      (openCovarianceSupportOpen B f V' D').ι ≫
        (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g)) :
    covarianceTargetOpenMap B j f V' E' D' hD' ≫ b =
      (openPostcompose B j).map a ≫ covarianceTargetOpenMap B j f V E D hD := by
  apply (SmallEtale.toScheme B X.obj X.property).map_injective
  apply (cancel_mono (openCovarianceSupportOpen B f V D).ι).mp
  have hlhs : (SmallEtale.toScheme B X.obj X.property).map
        (covarianceTargetOpenMap B j f V' E' D' hD' ≫ b) ≫
        (openCovarianceSupportOpen B f V D).ι =
      (openCovarianceSupportOpen B (j ≫ f) V' E').ι ≫ openBaseChangeHom B j f V' ≫
        (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g) := by
    rw [Functor.map_comp, Category.assoc, hb, ← Category.assoc,
      covarianceTargetOpenMap_commutes]
    exact Category.assoc _ _ _
  have hrhs : (SmallEtale.toScheme B X.obj X.property).map
        ((openPostcompose B j).map a ≫ covarianceTargetOpenMap B j f V E D hD) ≫
        (openCovarianceSupportOpen B f V D).ι =
      (openCovarianceSupportOpen B (j ≫ f) V' E').ι ≫ openBaseChangeHom B j f V' ≫
        (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g) := by
    rw [Functor.map_comp, openPostcompose_toScheme_map]
    refine (Category.assoc _ _ _).trans ?_
    rw [covarianceTargetOpenMap_commutes]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ openBaseChangeHom B j f V) ha).trans ?_
    exact (Category.assoc _ _ _).trans
      (congrArg (fun k => (openCovarianceSupportOpen B (j ≫ f) V' E').ι ≫ k)
        (openBaseChangeHom_naturality B j f g).symm)
  exact hlhs.trans hrhs.symm

/-- The canonical map on supported sections commutes with any pair of restrictions that is
compatible with the canonical maps of supported opens. -/
public theorem covarianceSectionMap_map (V V' : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (E' : FiniteSupport B (j ≫ f) V')
    (D : FiniteSupport B f V) (D' : FiniteSupport B f V')
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1)
    (hD' : D'.1 = (openBaseChangeHom B j f V').base '' E'.1)
    (a : openCovarianceSupportObject B (j ≫ f) V' E' ⟶
      openCovarianceSupportObject B (j ≫ f) V E)
    (b : openCovarianceSupportObject B f V' D' ⟶ openCovarianceSupportObject B f V D)
    (hcomm : covarianceTargetOpenMap B j f V' E' D' hD' ≫ b =
      (openPostcompose B j).map a ≫ covarianceTargetOpenMap B j f V E D hD)
    (k : supportedSections B X'.obj X'.property ((openRestriction B j).obj F)
        (baseChange B (j ≫ f) V) E.1 (finiteSupport_isLocallyClosed B (j ≫ f) V E) →+
      supportedSections B X'.obj X'.property ((openRestriction B j).obj F)
        (baseChange B (j ≫ f) V') E'.1 (finiteSupport_isLocallyClosed B (j ≫ f) V' E'))
    (l : supportedSections B X.obj X.property F (baseChange B f V) D.1
        (finiteSupport_isLocallyClosed B f V D) →+
      supportedSections B X.obj X.property F (baseChange B f V') D'.1
        (finiteSupport_isLocallyClosed B f V' D'))
    (hk : ∀ s, (k s).val = ((openRestriction B j).obj F).obj.map a.op s.val)
    (hl : ∀ s, (l s).val = F.obj.map b.op s.val) :
    l.comp (covarianceSectionMap B j f F V E D hD) =
      (covarianceSectionMap B j f F V' E' D' hD').comp k := by
  apply AddMonoidHom.ext
  intro s
  apply covarianceTargetOpenMap_restrict_injective B j f F V' E' D' hD'
  change F.obj.map (covarianceTargetOpenMap B j f V' E' D' hD').op
    (l (covarianceSectionMap B j f F V E D hD s)).val =
      F.obj.map (covarianceTargetOpenMap B j f V' E' D' hD').op
        (covarianceSectionMap B j f F V' E' D' hD' (k s)).val
  rw [hl, covarianceSectionMap_restrict, hk]
  have hc := congrArg (fun m => F.obj.map m.op) hcomm
  simp only [op_comp, Functor.map_comp] at hc
  have hc' := ConcreteCategory.congr_hom hc
    (covarianceSectionMap B j f F V E D hD s).val
  simp only [ConcreteCategory.comp_apply] at hc'
  rw [hc', covarianceSectionMap_restrict]
  exact (ConcreteCategory.congr_hom
    (((openRestrictionIso.{u, v} B j).inv.app F).hom.naturality a.op) s.val).symm

/-- The canonical map on supported sections is natural in the abelian sheaf. -/
public theorem covarianceSectionMap_sheaf
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (φ : F ⟶ G) (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    (supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V) D.1
      (finiteSupport_isLocallyClosed B f V D)).comp
        (covarianceSectionMap B j f F V E D hD) =
    (covarianceSectionMap B j f G V E D hD).comp
      (supportedSectionsSheafMap B X'.obj X'.property ((openRestriction B j).map φ)
        (baseChange B (j ≫ f) V) E.1 (finiteSupport_isLocallyClosed B (j ≫ f) V E)) := by
  apply AddMonoidHom.ext
  intro s
  apply covarianceTargetOpenMap_restrict_injective B j f G V E D hD
  change G.obj.map (covarianceTargetOpenMap B j f V E D hD).op
    (φ.hom.app _ (covarianceSectionMap B j f F V E D hD s).val) =
    G.obj.map (covarianceTargetOpenMap B j f V E D hD).op
      (covarianceSectionMap B j f G V E D hD
        (supportedSectionsSheafMap B X'.obj X'.property ((openRestriction B j).map φ)
          (baseChange B (j ≫ f) V) E.1
          (finiteSupport_isLocallyClosed B (j ≫ f) V E) s)).val
  rw [← ConcreteCategory.comp_apply, ← φ.hom.naturality,
    ConcreteCategory.comp_apply, covarianceSectionMap_restrict,
    covarianceSectionMap_restrict]
  exact (ConcreteCategory.congr_hom
    (congrArg (fun m => m.hom.app (op (openCovarianceSupportObject B (j ≫ f) V E)))
      ((openRestrictionIso.{u, v} B j).inv.naturality φ)) s.val).symm

end Extension

section Assembly

variable (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]

/-- The composite of an open immersion with a morphism locally of finite type is locally of
finite type. -/
public instance locallyOfFiniteType_openComp :
    LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
  change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
  infer_instance

/-- The composite of an open immersion with a locally quasi-finite morphism is locally
quasi-finite. -/
public instance locallyQuasiFinite_openComp :
    LocallyQuasiFinite (B.inclusion.map (j ≫ f)) := by
  change LocallyQuasiFinite (B.inclusion.map j ≫ B.inclusion.map f)
  infer_instance

/-- Restricting an abelian sheaf to the open subscheme and forming the finite-support direct
image along the composite. -/
public abbrev openFiniteSupportPushforward :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v} ⥤
      ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) :=
  openRestriction B j ⋙
    (finiteSupportPushforward.{u, max (u + 1) v} B (j ≫ f) (fun _ => inferInstance)).val

/-- The finite-support direct image presheaf functor on the whole source. -/
public abbrev wholeFiniteSupportPushforward :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v} ⥤
      ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) :=
  (finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).val

end Assembly

end AlgebraicGeometry.SmallEtale

end
