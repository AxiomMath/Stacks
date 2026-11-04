module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteBase
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.DirectImage
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleRelativeAmpleTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProjectiveSpaceContracted
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceHypotheses

/-!
# The Quot situation of `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ` on the big fppf site

Stacks 0DPA is a statement about the algebraic space `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}`: the subfunctor,
cut out by the Hilbert polynomial of the fibres, of the Quot functor of Stacks 09TR attached to the
free module of rank `r` on projective `n`-space over `Spec ℤ`.  This file builds that situation
on the big fppf site over `Spec ℤ` and the scheme models of its base changes.

* The base is `Spec ℤ`, the terminal object `AlgebraicGeometry.ProjectiveQuot.siteBase` of the
  site.
* The source is `ℙⁿ_ℤ`, read as the algebraic space it represents, and its morphism to the base is
  the structure morphism, of finite presentation.
* The module is `𝒪^{⊕ r}`, transported from the Zariski site of `ℙⁿ_ℤ` to the small étale site
  of the algebraic space by Stacks 03DX
  (`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`).

For a scheme `T` of the site over the base, the base change `X_T` of the situation is identified
with the algebraic space represented by `ℙⁿ_T`
(`AlgebraicGeometry.ProjectiveQuot.projectiveSiteSpaceIso`), and its projection to `T` is proper,
so that the proper-support condition of Stacks 09TR holds for every quotient of finite presentation
(`AlgebraicGeometry.ProjectiveQuot.isProperlySupportedOver_of_isFinitePresentationOnSite`).

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.projectiveSite`: `ℙⁿ_T` as an object of the site.
* `AlgebraicGeometry.ProjectiveQuot.quotSituation`: the Quot situation of `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ`.
* `AlgebraicGeometry.ProjectiveQuot.projectiveSiteSpaceIso`: `h_{ℙⁿ_T} ≅ X_T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuot

universe u

variable (B : BigFppfSite.{u}) (n r : ℕ)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-! ### Projective space over an object of the site -/

/-- `ℙⁿ_T` over an object `T` of the big fppf site over `Spec ℤ`, as an object of that site. -/
abbrev projectiveSite (T : BigFppfOver B integerBase B.contains_integerBase) :
    BigFppfOver B integerBase B.contains_integerBase :=
  CurveFamily.ofScheme (hZ := B.contains_integerBase) (projectiveSpaceOver n ((𝒯).obj T))
    (Space.contains_projectiveSpaceOver B _ T.left.property n)

/-- The structure morphism `ℙⁿ_T ⟶ T`, as a morphism of the site. -/
abbrev projectiveSiteStructure (T : BigFppfOver B integerBase B.contains_integerBase) :
    projectiveSite B n T ⟶ T :=
  CurveFamily.homOfScheme (projectiveSpaceOver n ((𝒯).obj T) ↘ (𝒯).obj T)

/-- The morphism `ℙⁿ_{T'} ⟶ ℙⁿ_T` induced by a morphism `T' ⟶ T` of the site. -/
abbrev projectiveSiteMap {T' T : BigFppfOver B integerBase B.contains_integerBase} (g : T' ⟶ T) :
    projectiveSite B n T' ⟶ projectiveSite B n T :=
  CurveFamily.homOfScheme (projectiveSpaceOverMap n ((𝒯).map g))

/-- **`ℙⁿ_{T'}` is the base change of `ℙⁿ_T` along `T' ⟶ T`, in the site.** -/
theorem isPullback_projectiveSite {T' T : BigFppfOver B integerBase B.contains_integerBase}
    (g : T' ⟶ T) :
    IsPullback (projectiveSiteMap B n g) (projectiveSiteStructure B n T')
      (projectiveSiteStructure B n T) g := by
  have H := isPullback_projectiveSpaceOverMap n ((𝒯).map g)
  refine CurveFamily.isPullback_of_isPullback_toScheme_map ?_ H
  exact (𝒯).map_injective (by simp only [Functor.map_comp]; exact H.w)

/-- The unique morphism of an object of the site to the base `Spec ℤ`. -/
abbrev toSiteBase (T : BigFppfOver B integerBase B.contains_integerBase) : T ⟶ siteBase B :=
  (isTerminal_siteBase B).from T

/-! ### The situation -/

/-- `ℙⁿ_ℤ`, as an object of the site. -/
abbrev projectiveSiteBase : BigFppfOver B integerBase B.contains_integerBase :=
  projectiveSite B n (siteBase B)

/-- The free module `𝒪^{⊕ r}` on `ℙⁿ_ℤ` is quasi-coherent. -/
theorem isQuasicoherent_freeModule (T : Scheme.{u}) :
    SheafOfModules.IsQuasicoherent (freeModule n r T) :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit _
    fun _ => Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _

/-- `𝒪^{⊕ r}` on the algebraic space represented by `ℙⁿ_ℤ`, as a quasi-coherent module: the
free module of the Zariski site of `ℙⁿ_ℤ` transported by Stacks 03DX. -/
abbrev siteFreeModuleQcoh :=
  (Space.representedQuasicoherentSchemeEquivalence B integerBase B.contains_integerBase
    (projectiveSiteBase B n)).functor.obj
      ⟨freeModule n r integerBase, isQuasicoherent_freeModule n r _⟩

/-- **The Quot situation of `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ`** (Stacks 09TR at the data of Stacks 0DPA): the
structure morphism `ℙⁿ_ℤ ⟶ Spec ℤ` of algebraic spaces, of finite presentation, with the free
module of rank `r`. -/
def quotSituation : Space.QuotSituation B integerBase B.contains_integerBase where
  X := schemeSpace (projectiveSiteBase B n)
  Y := schemeSpace (siteBase B)
  f := schemeSpaceMap (projectiveSiteStructure B n (siteBase B))
  F := (siteFreeModuleQcoh B n r).obj
  quasicoherent := (siteFreeModuleQcoh B n r).property
  finitePresentation := Space.isFinitePresentation_yoneda_map B integerBase B.contains_integerBase
    _ (finitePresentation_projectiveSpaceOver n integerBase)

/-! ### The base changes of the situation are projective spaces -/

variable {B n r}

/-- The morphism of a test scheme of the situation to the base is the one its object of the site
represents: there is only one. -/
theorem hom_eq_schemeSpaceMap (T : Space.SchemesOver (quotSituation B n r).Y) :
    T.hom = schemeSpaceMap (toSiteBase B T.left) :=
  (subsingleton_hom_schemeSpace_siteBase B _).elim _ _

/-- A morphism of the site represents the composite of the represented morphisms. -/
@[deprecated AlgebraicGeometry.schemeSpaceMap_comp (since := "2026-10-27")]
theorem schemeSpaceMap_comp {T'' T' T : BigFppfOver B integerBase B.contains_integerBase}
    (a : T'' ⟶ T') (b : T' ⟶ T) :
    schemeSpaceMap (a ≫ b) = schemeSpaceMap a ≫ schemeSpaceMap b :=
  AlgebraicGeometry.schemeSpaceMap_comp a b

/-- The morphisms of projective spaces compose. -/
theorem projectiveSiteMap_comp {T'' T' T : BigFppfOver B integerBase B.contains_integerBase}
    (a : T'' ⟶ T') (b : T' ⟶ T) :
    projectiveSiteMap B n (a ≫ b) = projectiveSiteMap B n a ≫ projectiveSiteMap B n b :=
  (𝒯).map_injective (by
    simp only [Functor.map_comp]
    exact (projectiveSpaceOverMap_comp n _ _).symm)

/-- The base change `X_T` of the situation is the fibre product of the algebraic spaces, with its
two projections. -/
theorem isPullback_space (T : Space.SchemesOver (quotSituation B n r).Y) :
    IsPullback ((quotSituation B n r).sourceProjection T) ((quotSituation B n r).projection T)
      (quotSituation B n r).f (schemeSpaceMap (toSiteBase B T.left)) := by
  rw [← hom_eq_schemeSpaceMap T]
  exact AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase
    (quotSituation B n r).f T.hom

/-- `ℙⁿ_T` over `T`, read as algebraic spaces, is the base change of `ℙⁿ_ℤ` along `T ⟶ Spec ℤ`. -/
theorem isPullback_projectiveSiteSpace (T : BigFppfOver B integerBase B.contains_integerBase) :
    IsPullback (schemeSpaceMap (projectiveSiteMap B n (toSiteBase B T)))
      (schemeSpaceMap (projectiveSiteStructure B n T))
      (quotSituation B n r).f (schemeSpaceMap (toSiteBase B T)) :=
  CurveFamily.isPullback_schemeSpaceMap_of_isPullback (isPullback_projectiveSite B n _)

variable (r) in
/-- **The base change `X_T` of the situation is the algebraic space of `ℙⁿ_T`.** -/
def projectiveSiteSpaceIso (T : Space.SchemesOver (quotSituation B n r).Y) :
    schemeSpace (projectiveSite B n T.left) ≅ (quotSituation B n r).space T :=
  (isPullback_projectiveSiteSpace (r := r) T.left).isoIsPullback _ _ (isPullback_space T)

/-- The isomorphism `h_{ℙⁿ_T} ≅ X_T` followed by the projection `X_T ⟶ ℙⁿ_ℤ` is the morphism
`ℙⁿ_T ⟶ ℙⁿ_ℤ` induced by `T ⟶ Spec ℤ`. -/
@[reassoc (attr := simp)]
theorem projectiveSiteSpaceIso_hom_sourceProjection
    (T : Space.SchemesOver (quotSituation B n r).Y) :
    (projectiveSiteSpaceIso r T).hom ≫ (quotSituation B n r).sourceProjection T =
      schemeSpaceMap (projectiveSiteMap B n (toSiteBase B T.left)) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The isomorphism `h_{ℙⁿ_T} ≅ X_T` followed by the projection `X_T ⟶ T` is the structure
morphism `ℙⁿ_T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem projectiveSiteSpaceIso_hom_projection (T : Space.SchemesOver (quotSituation B n r).Y) :
    (projectiveSiteSpaceIso r T).hom ≫ (quotSituation B n r).projection T =
      schemeSpaceMap (projectiveSiteStructure B n T.left) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **The morphisms of base changes are the morphisms of projective spaces.** -/
theorem projectiveSiteSpaceIso_hom_relativeMap
    {T' T : Space.SchemesOver (quotSituation B n r).Y} (h : T' ⟶ T) :
    (projectiveSiteSpaceIso r T').hom ≫ (quotSituation B n r).relativeMap h =
      schemeSpaceMap (projectiveSiteMap B n h.left) ≫ (projectiveSiteSpaceIso r T).hom := by
  refine Space.baseChange_hom_ext (quotSituation B n r).f ?_ ?_
  · rw [Category.assoc, Space.baseChangeMap_comp_projection, Category.assoc,
      projectiveSiteSpaceIso_hom_sourceProjection, projectiveSiteSpaceIso_hom_sourceProjection]
    rw [(isTerminal_siteBase B).hom_ext (toSiteBase B T'.left) (h.left ≫ toSiteBase B T.left),
      projectiveSiteMap_comp]
    exact AlgebraicGeometry.schemeSpaceMap_comp _ _
  · rw [Category.assoc, Space.baseChangeMap_comp_inclusion, Category.assoc,
      projectiveSiteSpaceIso_hom_projection, ← Category.assoc,
      projectiveSiteSpaceIso_hom_projection]
    exact ((AlgebraicGeometry.schemeSpaceMap_comp _ _).symm.trans
      (congrArg schemeSpaceMap (isPullback_projectiveSite B n h.left).w.symm)).trans
      (AlgebraicGeometry.schemeSpaceMap_comp _ _)

/-! ### Proper support is automatic -/

/-- The projection `X_T ⟶ T` of every base change of the situation is proper, being a base change
of `ℙⁿ_ℤ ⟶ Spec ℤ`. -/
theorem isProper_projection (T : Space.SchemesOver (quotSituation B n r).Y) :
    Space.IsProper B integerBase B.contains_integerBase
      ((quotSituation B n r).projection T).hom := by
  have hf : Space.IsProper B integerBase B.contains_integerBase (quotSituation B n r).f.hom :=
    (Space.isProper_yoneda_map_iff B integerBase B.contains_integerBase _).2
      (inferInstanceAs (IsProper (projectiveSpaceOver n integerBase ↘ integerBase)))
  exact (Space.isProper_isStableUnderBaseChange B integerBase B.contains_integerBase).of_isPullback
    (isPullback_space T) hf

/-- **Every quotient of finite presentation has support proper over the test scheme**: the
support is closed (Stacks 07TZ) and `X_T ⟶ T` is proper, so every closed subset of `|X_T|` is
proper over `T`. -/
theorem isProperlySupportedOver_of_isFinitePresentationOnSite
    (T : Space.SchemesOver (quotSituation B n r).Y)
    (G : Space.Modules.{u, u} B integerBase B.contains_integerBase
      ((quotSituation B n r).space T).1 ((quotSituation B n r).space T).2)
    [G.IsFinitePresentationOnSite] : (quotSituation B n r).IsProperlySupportedOver T G := by
  have hcl := Space.isClosed_supportOfSheaf_of_isFiniteTypeOnSite B integerBase
    B.contains_integerBase ((quotSituation B n r).space T).1 ((quotSituation B n r).space T).2 G
  exact ⟨hcl, Space.isProperOver_of_isProper B integerBase B.contains_integerBase _ _ _ _
    (isProper_projection T) _ hcl⟩

end AlgebraicGeometry.ProjectiveQuot

end
