module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionInSitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChangeFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Examples.GroupSchemes.NonSeparated
public import StacksFrontier.Examples.GroupSchemes.TrivialDoubleCover

/-!
# The doubled-origin line and `(ℤ/2)_S` as group algebraic spaces

Let `S` be the affine line over a field and `H` the affine line with its origin doubled, a group
scheme over `S` whose two charts multiply by adding their labels modulo two
(`Stacks.Examples.doubledAffineLine`). This module reads `H`, the constant group scheme
`(ℤ/2)_S = S ⊔ S` (`Stacks.Examples.trivialDoubleCover`) and the homomorphism `q : (ℤ/2)_S ⟶ H`
carrying the two sections onto the two charts as group algebraic spaces over `S` in the big fppf
site, and records the properties of their structure morphisms that the counterexample to the
published form of Stacks 0CPQ uses.

## Main definitions

* `Stacks.Examples.SectionCoverData.siteObject` and `Stacks.Examples.SectionCoverData.groupSpace`
  — a section cover whose total space lies in the site, as an object of the site and as a group
  algebraic space over `S`.
* `Stacks.Examples.SectionCoverData.groupSpaceMap` — a morphism of section covers matching the
  charts, as a homomorphism of group algebraic spaces.
* `Stacks.Examples.doubledOriginGroupSpace`, `Stacks.Examples.constantZ2GroupSpace` and
  `Stacks.Examples.doubledOriginQuotientMap` — `H`, `(ℤ/2)_S` and `q`.

## Main results

* `Stacks.Examples.isProper_constantZ2GroupSpace` and the étale-chart properties of
  `(ℤ/2)_S ⟶ S`: flat, locally of finite presentation, smooth.
* `Stacks.Examples.not_isSeparated_doubledOriginGroupSpace` and the étale-chart properties of
  `H ⟶ S`.
* `Stacks.Examples.exists_lift_doubledOriginQuotientMap` — field-valued points of `H` lift
  along `q`.
* `Stacks.Examples.contains_doubledAffineLine_total` and `contains_trivialDoubleCover_total`:
  every big fppf site containing `S` contains `H` and `(ℤ/2)_S`.

## Implementation notes

The underlying algebraic space of the group algebraic space attached to a group scheme `G` over
`S` is the product `S ⨯ G` of presheaves, which is isomorphic to the presheaf represented by `G`
because `S` is terminal (`AlgebraicGeometry.Space.terminalSpaceProdIso`). Its structure morphism
is that isomorphism followed by the image under Yoneda of the structure morphism of `G`, both
having the terminal presheaf as target, and every property of morphisms of algebraic spaces used
here is read off the image under Yoneda (`AlgebraicGeometry.Space.isFlat_yoneda_map` and its
companions) and transported along the isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Examples

section General

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} (hS : 𝒞.Contains S)

namespace SectionCoverData

/-- The total space of a section cover, as an object of the big fppf site over `S`. -/
public noncomputable def siteObject (D : SectionCoverData S) (hD : 𝒞.Contains D.total) :
    BigFppfOver 𝒞 S hS :=
  Over.mk (ObjectProperty.homMk D.proj (X := 𝒞.obj hD) (Y := 𝒞.obj hS))

/-- The structure morphism of the site object of a section cover, as a morphism to the base. -/
public noncomputable def siteObjectToBase (D : SectionCoverData S) (hD : 𝒞.Contains D.total) :
    D.siteObject hS hD ⟶ Space.baseTerminal 𝒞 S hS :=
  Over.homMk (D.siteObject hS hD).hom (Category.comp_id _)

/-- **A section cover lying in the site, as a group algebraic space over `S`**: the group
algebraic space attached by Stacks 043I to the group scheme of
`Stacks.Examples.SectionCoverData.grpObj`. -/
public noncomputable def groupSpace (D : SectionCoverData S) (hD : 𝒞.Contains D.total) :
    Space.GroupAlgebraicSpace 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
      (Space.terminalSpace 𝒞 S hS).property :=
  Space.GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS _ _ (D.siteObject hS hD) D.grpObj

/-- **A morphism of section covers matching the charts, as a homomorphism of group algebraic
spaces over `S`.** -/
public noncomputable def groupSpaceMap {D D' : SectionCoverData S} (hD : 𝒞.Contains D.total)
    (hD' : 𝒞.Contains D'.total) (f : D.total ⟶ D'.total) (hf : f ≫ D'.proj = D.proj)
    (hc : ∀ b, D.chart b ≫ f = D'.chart b) :
    D.groupSpace hS hD ⟶ D'.groupSpace hS hD' :=
  Space.GroupAlgebraicSpace.ofGroupSchemeInSiteMap 𝒞 S hS _ _
    (G := D.siteObject hS hD) (H := D'.siteObject hS hD') D.grpObj D'.grpObj
    (overHom f hf) (isMonHom_overHom f hf hc)

/-- The underlying algebraic space of the group algebraic space of a section cover is the
presheaf represented by its total space. -/
public noncomputable def groupSpaceIso (D : SectionCoverData S) (hD : 𝒞.Contains D.total) :
    (D.groupSpace hS hD).obj.X.left ≅ yoneda.obj (D.siteObject hS hD) :=
  Space.terminalSpaceProdIso 𝒞 S hS _ ≪≫
    (Space.pointsOnSiteRepresentableBy 𝒞 S hS (D.siteObject hS hD) D.grpObj).toIso.symm

/-- The structure morphism of the group algebraic space of a section cover is the image under
Yoneda of its structure morphism, read through `Stacks.Examples.SectionCoverData.groupSpaceIso`:
both are morphisms to the terminal presheaf. -/
public lemma groupSpace_hom_eq (D : SectionCoverData S) (hD : 𝒞.Contains D.total) :
    (D.groupSpace hS hD).obj.X.hom =
      (D.groupSpaceIso hS hD).hom ≫ yoneda.map (D.siteObjectToBase hS hD) :=
  (Space.baseTerminal_yonedaIsTerminal 𝒞 S hS).hom_ext _ _

/-- A property of morphisms of schemes which holds on every étale chart of the image under
Yoneda of the structure morphism holds on every étale chart of the structure morphism of the
group algebraic space. -/
public lemma holdsOnEveryEtaleChart_groupSpace_hom (D : SectionCoverData S)
    (hD : 𝒞.Contains D.total) {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) (hproj : P D.proj) :
    Space.HoldsOnEveryEtaleChart 𝒞 S hS P (D.groupSpace hS hD).obj.X.hom := by
  rw [groupSpace_hom_eq]
  exact (Space.holdsOnEveryEtaleChart_precomp_iso 𝒞 S hS P _ _).1
    (Space.holdsOnEveryEtaleChart_yoneda_map 𝒞 S hS hP _ hproj)

/-- The structure morphism of the group algebraic space of a section cover is flat. -/
public theorem isFlat_groupSpace_hom (D : SectionCoverData S) (hD : 𝒞.Contains D.total) :
    Space.IsFlat 𝒞 S hS (D.groupSpace hS hD).obj.X.hom :=
  D.holdsOnEveryEtaleChart_groupSpace_hom hS hD Flat.isEtaleLocalOnSourceAndTarget
    (D.proj_prop _ (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)) inferInstance)

/-- The structure morphism of the group algebraic space of a section cover is locally of finite
presentation. -/
public theorem isLocallyOfFinitePresentation_groupSpace_hom (D : SectionCoverData S)
    (hD : 𝒞.Contains D.total) :
    Space.IsLocallyOfFinitePresentation 𝒞 S hS (D.groupSpace hS hD).obj.X.hom :=
  D.holdsOnEveryEtaleChart_groupSpace_hom hS hD
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    (D.proj_prop _
      (HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation))
      inferInstance)

/-- The structure morphism of the group algebraic space of a section cover is smooth. -/
public theorem isSmooth_groupSpace_hom (D : SectionCoverData S) (hD : 𝒞.Contains D.total) :
    Space.IsSmooth 𝒞 S hS (D.groupSpace hS hD).obj.X.hom :=
  D.holdsOnEveryEtaleChart_groupSpace_hom hS hD Smooth.isEtaleLocalOnSourceAndTarget
    (D.proj_prop _ (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)) inferInstance)

/-- The structure morphism of the group algebraic space of a section cover is proper as soon as
the structure morphism of the section cover is. -/
public theorem isProper_groupSpace_hom (D : SectionCoverData S) (hD : 𝒞.Contains D.total)
    (h : IsProper D.proj) : Space.IsProper 𝒞 S hS (D.groupSpace hS hD).obj.X.hom := by
  rw [groupSpace_hom_eq]
  exact (Space.isProper_isIso_comp_iff 𝒞 S hS (D.groupSpaceIso hS hD).hom _).2
    (Space.isProper_yoneda_map 𝒞 S hS _ h)

/-- The structure morphism of the group algebraic space of a section cover is separated only if
the structure morphism of the section cover is. -/
public theorem isSeparated_proj_of_isSeparated_groupSpace_hom (D : SectionCoverData S)
    (hD : 𝒞.Contains D.total) (h : Space.IsSeparated 𝒞 S hS (D.groupSpace hS hD).obj.X.hom) :
    IsSeparated D.proj := by
  rw [groupSpace_hom_eq] at h
  have h' : Space.IsSeparated 𝒞 S hS (yoneda.map (D.siteObjectToBase hS hD)) :=
    Space.isSeparated_of_arrowIso 𝒞 S hS _ _ (D.groupSpaceIso hS hD).hom (𝟙 _) (by simp) h
  exact (Space.isSeparated_yoneda_map_iff 𝒞 S hS _).1 h'


/-- **Points lift along the homomorphism of group algebraic spaces as soon as they lift along
the morphism of section covers.** If every morphism over `S` from a scheme `T` of the site to
`D'` lifts along `f : D ⟶ D'`, then every `T`-point of the group algebraic space of `D'` lifts
along `Stacks.Examples.SectionCoverData.groupSpaceMap`. -/
public theorem exists_lift_groupSpaceMap {D D' : SectionCoverData S} (hD : 𝒞.Contains D.total)
    (hD' : 𝒞.Contains D'.total) (f : D.total ⟶ D'.total) (hf : f ≫ D'.proj = D.proj)
    (hc : ∀ b, D.chart b ≫ f = D'.chart b) (T : BigFppfOver 𝒞 S hS)
    (hlift : ∀ h : (Space.toSchemeOver 𝒞 S hS).obj T ⟶ D'.over,
      ∃ z : (Space.toSchemeOver 𝒞 S hS).obj T ⟶ D.over, z ≫ overHom f hf = h)
    (x : yoneda.obj T ⟶ (D'.groupSpace hS hD').obj.X.left) :
    ∃ z : yoneda.obj T ⟶ (D.groupSpace hS hD).obj.X.left,
      z ≫ (groupSpaceMap hS hD hD' f hf hc).hom.hom.hom.left = x := by
  obtain ⟨z₀, hz₀⟩ := hlift (yonedaEquiv (x ≫ prod.snd))
  refine ⟨prod.lift (x ≫ prod.fst) (yonedaEquiv.symm z₀), ?_⟩
  show _ ≫ prod.map _ _ = x
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prod.map_fst, Category.comp_id, prod.lift_fst]
    rfl
  · rw [Category.assoc, prod.map_snd, prod.lift_snd_assoc]
    refine (yonedaEquiv_symm_naturality_right
      (F := Space.pointsOnSite 𝒞 S hS (D.siteObject hS hD) D.grpObj ⋙ forget GrpCat)
      T _ z₀).trans ?_
    rw [Equiv.symm_apply_eq]
    exact hz₀

end SectionCoverData

end General

/-! ### The two group schemes over the affine line -/

variable {𝒞 : BigFppfSite.{u}} (k : Type u) [Field k]
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))

/-- Every big fppf site containing the affine line contains the line with doubled origin: it is
of finite type over the affine line. -/
public theorem contains_doubledAffineLine_total (hS : 𝒞.Contains (Spec (.of (Polynomial k)))) :
    𝒞.Contains (doubledAffineLine k).total := by
  have : CompactSpace (Spec (.of (Polynomial k))) := PrimeSpectrum.compactSpace
  have : LocallyOfFiniteType (doubledAffineLine k).proj :=
    (doubledAffineLine k).proj_prop _
      (HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)) inferInstance
  have : QuasiCompact (doubledAffineLine k).proj := (doubledAffineLine k).quasiCompact_proj
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (doubledAffineLine k).proj hS

/-- Every big fppf site containing a scheme `S` contains `S ⊔ S`. -/
public theorem contains_trivialDoubleCover_total {S : Scheme.{u}} (hS : 𝒞.Contains S) :
    𝒞.Contains (trivialDoubleCover S).total :=
  𝒞.contains_coprod_self hS

/-- There is a big fppf site containing the affine line, hence also the line with doubled
origin and `(ℤ/2)` over the affine line. -/
public theorem exists_bigFppfSite_contains :
    ∃ 𝒞 : BigFppfSite.{u}, 𝒞.Contains (Spec (.of (Polynomial k))) ∧
      𝒞.Contains (doubledAffineLine k).total ∧
        𝒞.Contains (trivialDoubleCover (Spec (.of (Polynomial k)))).total := by
  obtain ⟨𝒞, h⟩ := BigFppfSite.exists_contains (Spec (.of (Polynomial k)))
  exact ⟨𝒞, h, contains_doubledAffineLine_total k h, contains_trivialDoubleCover_total h⟩

/-- **The affine line with doubled origin, as a group algebraic space over the affine line.** -/
public noncomputable def doubledOriginGroupSpace :
    Space.GroupAlgebraicSpace 𝒞 (Spec (.of (Polynomial k))) hS
      (Space.terminalSpace 𝒞 (Spec (.of (Polynomial k))) hS).obj
      (Space.terminalSpace 𝒞 (Spec (.of (Polynomial k))) hS).property :=
  (doubledAffineLine k).groupSpace hS (contains_doubledAffineLine_total k hS)

/-- **The constant group `(ℤ/2)` over the affine line, as a group algebraic space.** -/
public noncomputable def constantZ2GroupSpace :
    Space.GroupAlgebraicSpace 𝒞 (Spec (.of (Polynomial k))) hS
      (Space.terminalSpace 𝒞 (Spec (.of (Polynomial k))) hS).obj
      (Space.terminalSpace 𝒞 (Spec (.of (Polynomial k))) hS).property :=
  (trivialDoubleCover _).groupSpace hS (contains_trivialDoubleCover_total hS)

/-- **The homomorphism `q : (ℤ/2) ⟶ H`** carrying the two sections of `(ℤ/2)` onto the two
charts of the line with doubled origin. -/
public noncomputable def doubledOriginQuotientMap :
    constantZ2GroupSpace k hS ⟶ doubledOriginGroupSpace k hS :=
  SectionCoverData.groupSpaceMap hS _ _ (doubledAffineLine k).fromTrivial
    (doubledAffineLine k).fromTrivial_comp_proj (doubledAffineLine k).chart_comp_fromTrivial

/-- `(ℤ/2) ⟶ S` is proper. -/
public theorem isProper_constantZ2GroupSpace :
    Space.IsProper 𝒞 _ hS (constantZ2GroupSpace k hS).obj.X.hom :=
  SectionCoverData.isProper_groupSpace_hom hS _ _ inferInstance

/-- `(ℤ/2) ⟶ S` is flat. -/
public theorem isFlat_constantZ2GroupSpace :
    Space.IsFlat 𝒞 _ hS (constantZ2GroupSpace k hS).obj.X.hom :=
  SectionCoverData.isFlat_groupSpace_hom hS _ _

/-- `(ℤ/2) ⟶ S` is locally of finite presentation. -/
public theorem isLocallyOfFinitePresentation_constantZ2GroupSpace :
    Space.IsLocallyOfFinitePresentation 𝒞 _ hS (constantZ2GroupSpace k hS).obj.X.hom :=
  SectionCoverData.isLocallyOfFinitePresentation_groupSpace_hom hS _ _

/-- `(ℤ/2) ⟶ S` is smooth. -/
public theorem isSmooth_constantZ2GroupSpace :
    Space.IsSmooth 𝒞 _ hS (constantZ2GroupSpace k hS).obj.X.hom :=
  SectionCoverData.isSmooth_groupSpace_hom hS _ _

/-- `H ⟶ S` is flat. -/
public theorem isFlat_doubledOriginGroupSpace :
    Space.IsFlat 𝒞 _ hS (doubledOriginGroupSpace k hS).obj.X.hom :=
  SectionCoverData.isFlat_groupSpace_hom hS _ _

/-- `H ⟶ S` is locally of finite presentation. -/
public theorem isLocallyOfFinitePresentation_doubledOriginGroupSpace :
    Space.IsLocallyOfFinitePresentation 𝒞 _ hS (doubledOriginGroupSpace k hS).obj.X.hom :=
  SectionCoverData.isLocallyOfFinitePresentation_groupSpace_hom hS _ _

/-- `H ⟶ S` is smooth. -/
public theorem isSmooth_doubledOriginGroupSpace :
    Space.IsSmooth 𝒞 _ hS (doubledOriginGroupSpace k hS).obj.X.hom :=
  SectionCoverData.isSmooth_groupSpace_hom hS _ _

/-- **`H ⟶ S` is not separated**: the complement of the origin is not closed in the affine
line. -/
public theorem not_isSeparated_doubledOriginGroupSpace :
    ¬ Space.IsSeparated 𝒞 _ hS (doubledOriginGroupSpace k hS).obj.X.hom := fun h =>
  doubleSectionCover_not_isSeparated _ _ (not_isClosed_puncturedAffineLine k)
    (SectionCoverData.isSeparated_proj_of_isSeparated_groupSpace_hom hS _ _ h)

/-- **Field-valued points of `H` lift along `q : (ℤ/2) ⟶ H`.** For a scheme `T` of the site which
is the spectrum of a field, every `T`-point of the line with doubled origin is the image under
`q` of a `T`-point of `(ℤ/2)`: a field-valued point factors through one of the two charts. -/
public theorem exists_lift_doubledOriginQuotientMap
    (T : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS) (K : Type u) [Field K]
    (e : (BigFppfOver.toScheme 𝒞 _ hS).obj T ≅ Spec (.of K))
    (x : yoneda.obj T ⟶ (doubledOriginGroupSpace k hS).obj.X.left) :
    ∃ z : yoneda.obj T ⟶ (constantZ2GroupSpace k hS).obj.X.left,
      z ≫ (doubledOriginQuotientMap k hS).hom.hom.hom.left = x := by
  refine SectionCoverData.exists_lift_groupSpaceMap hS _ _ _ _ _ T (fun h => ?_) x
  obtain ⟨z, hz⟩ := (doubledAffineLine k).exists_comp_fromTrivial_eq K (e.inv ≫ h.left)
  refine ⟨Over.homMk (e.hom ≫ z) ?_, ?_⟩
  · have hz' : z ≫ (trivialDoubleCover _).proj = e.inv ≫ h.left ≫ (doubledAffineLine k).proj := by
      rw [← (doubledAffineLine k).fromTrivial_comp_proj, ← Category.assoc, hz]
      exact Category.assoc _ _ _
    show (e.hom ≫ z) ≫ (trivialDoubleCover _).proj = _
    rw [Category.assoc, hz']
    exact (Iso.hom_inv_id_assoc e _).trans (Over.w h)
  · refine Over.OverMorphism.ext ?_
    show (e.hom ≫ z) ≫ (doubledAffineLine k).fromTrivial = h.left
    exact (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hz).trans (Iso.hom_inv_id_assoc e _))

end Stacks.Examples

end
