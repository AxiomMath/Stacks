module

public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.CechAmitsurSmallSites
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# `Fᵃ` on the size-bounded small étale site is `Fᵃ` on Mathlib's

A scheme `S` carries two small étale sites in this development, and the quasi-coherent
comparison results are split between them.

* `AlgebraicGeometry.Scheme.Etale` with `AlgebraicGeometry.Scheme.smallEtaleTopology` is the
  choice-free site of *all* étale schemes over `S`.  This is where the positive-degree
  vanishing of the cohomology of the associated module on an affine object lives:
  `AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`, and with it
  `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`, the carrier of
  [Stacks, Tag 03P2] at `𝒞 = S_étale` and of [Stacks, Tag 03DW] clause (2).
* `AlgebraicGeometry.SmallEtale B S hS` of [Stacks, Tag 021B] is the full subcategory of a big
  étale site `B` on the objects étale over `S`; it is *essentially small*, which is what makes
  the associated-module functor `AlgebraicGeometry.SmallEtale.associatedModule` and the
  equivalence `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'` — Descent,
  Proposition 03DX (2) at `τ = étale` — available there and nowhere else.

The two sites are already related as sites: `AlgebraicGeometry.SmallEtale.toEtaleSite` is fully
faithful, `AlgebraicGeometry.SmallEtale.topology_eq_restrictedTopology` identifies the
topologies, and `AlgebraicGeometry.SmallEtale.sheafEquiv` is the resulting equivalence of
categories of abelian sheaves.  What was **not** related is the *coefficients*: nothing said
that the associated module of a quasi-coherent module on the size-bounded site is the
restriction of the associated sheaf on Mathlib's.  That is what this file supplies.

## Main results

* `AlgebraicGeometry.SmallEtale.toOver_eq_toEtaleSite_comp_forget`: the canonical functor from
  the size-bounded small étale site to the schemes over `S` factors through Mathlib's small
  étale site, on the nose.
* `AlgebraicGeometry.SmallEtale.associatedModulePresheafIsoRestriction`: **the abelian presheaf
  underlying `Fᵃ` on the size-bounded small étale site is the restriction along
  `AlgebraicGeometry.SmallEtale.toEtaleSite` of the abelian sheaf `Fᵃ` on Mathlib's.**
* `AlgebraicGeometry.SmallEtale.associatedModuleSheafIsoRestriction`: the same identification
  read in the category of abelian sheaves on the size-bounded site, where the right-hand side is
  the sheaf pushforward along the continuous functor `toEtaleSite`.
* `AlgebraicGeometry.SmallEtale.preservesLimitsOfShape_walkingCospan_toEtaleSite` and
  `AlgebraicGeometry.SmallEtale.isIso_cechProductMapOfFunctor_toEtaleSite`: the comparison of
  the iterated fibre products of a family with those of its image, which is what identifies the
  two Čech complexes.
* `AlgebraicGeometry.SmallEtale.cechComplexIsoImageToEtaleSite`: **the Čech complex of a family
  of the size-bounded small étale site with coefficients in `Fᵃ` is the Čech complex of its
  image family on Mathlib's.**
* `AlgebraicGeometry.SmallEtale.isZero_cechCohomology_succ_associatedModule`: **the
  positive-degree Čech cohomology of `Fᵃ` on the size-bounded small étale site vanishes on a
  family whose image is a small-étale-standard covering** — the first positive-degree vanishing
  for the associated module on that site.

## Implementation notes

Both identifications are isomorphisms rather than equalities only because the left-hand side is
spelled through the associated-module functor: once that functor's sections are unfolded by
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` the two presheaves are *equal*, and
`AlgebraicGeometry.SmallEtale.associatedModulePresheaf_restriction_eq` records that equality.
It holds because `AlgebraicGeometry.SmallEtale.toOver` and the composite
`toEtaleSite ⋙ Scheme.Etale.forget S` are the same functor and the abelian presheaf underlying
`AlgebraicGeometry.smallEtaleAssociatedSheaf` is `AlgebraicGeometry.quasiCoherentPresheafFunctor`
restricted along `Scheme.Etale.forget S`; so no comparison of sections is computed here, and
none is owed.

The Čech vanishing is transported along `AlgebraicGeometry.SmallEtale.toEtaleSite` and not along
`AlgebraicGeometry.SmallEtale.toOver`, so that the statement it rests on is the small-étale case
(b) of [Stacks, Tag 03FJ] — the theorem
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf_smallEtale` — rather than
its big-site case.  The hypothesis is therefore stated on the image
family: a family of the size-bounded site is as good as a standard covering exactly when its
image is one, and nothing is assumed of the family itself.

That `toEtaleSite` preserves the fibre products the Čech complex is built from is not an
instance and is proved here, twice through
`CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves`: the composite
`toEtaleSite ⋙ Scheme.Etale.forget S` is `AlgebraicGeometry.SmallEtale.toOver`, whose composite
with `CategoryTheory.Over.forget` is the functor to all schemes, and the two forgetful functors
each reflect the limits in question.

**What this does not give, and what would be needed.**  It does not transport the vanishing of
`AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine` — *sheaf* cohomology, not Čech
cohomology — to the size-bounded site.  `CategoryTheory.Sheaf.H'` is an `Ext`-group *over an
object*, and the dense-subsite transports available in this tree —
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` and
`Stacks.Cohomology.DenseSubsiteConstant.subsingleton_H_constantSheaf_of_isDenseSubsite` — move
*global* cohomology, that is cohomology over a terminal object, and the latter only for a
constant sheaf.  Transporting cohomology over an arbitrary object needs the slices of the two
sites to be a dense subsite pair as well, which is `Stacks.Cohomology.BiggerSite` territory and
is not proved here.

Nor does the Čech vanishing above by itself give [Stacks, Tag 03DW] on the size-bounded site.
Two things are still owed for that.  First, a *cofinal* supply of standard coverings: every
covering sieve of an affine object has to be refined by a family whose image is a
small-étale-standard covering, which on this site is the business of
`AlgebraicGeometry.SmallEtale.affineImageCover` and is not assembled into that shape anywhere.
Second, the passage from Čech cohomology to sections, for which the tool is
`SheafOfModules.detectsRange_of_cechH1Vanishing` — it asks for the vanishing along a *single*
covering morphism, so it wants the disjoint union of a finite family as an object of the site,
and the Čech statement above is indexed by a family.  Those two, followed by
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and
`AlgebraicGeometry.Space.chartLocalizationEquivalence`, are what would carry Tag 03DW to the
small étale site of an algebraic space, where it is carried as the hypothesis `h03DW` at fifteen
binder sites.

No `@[stacks]` attribute is claimed.  Nothing here is a clause of a tag: the content is the
identification of two spellings of one presheaf.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The canonical functor from the size-bounded small étale site of `S` to the schemes over
`S` factors through Mathlib's small étale site.**  Both sides forget the size bound and keep the
structure morphism, so this is a definitional identity. -/
public theorem toOver_eq_toEtaleSite_comp_forget :
    toOver B S hS = toEtaleSite B S hS ⋙ Scheme.Etale.forget S :=
  rfl

variable (F : S.Modules) [F.IsQuasicoherent]

/-- **The presheaf of Stacks 03DS on the size-bounded small étale site is the restriction along
`AlgebraicGeometry.SmallEtale.toEtaleSite` of the abelian sheaf `Fᵃ` on Mathlib's small étale
site.**  An equality, not merely an isomorphism: the two sides are the same composite of
`AlgebraicGeometry.quasiCoherentPresheafFunctor` with a forgetful functor, by
`AlgebraicGeometry.SmallEtale.toOver_eq_toEtaleSite_comp_forget`. -/
public theorem associatedModulePresheaf_restriction_eq :
    (toEtaleSite B S hS).op ⋙ (smallEtaleAssociatedSheaf S F).obj =
      (toOver B S hS).op ⋙ quasiCoherentPresheafFunctor S F :=
  rfl

/-- **The abelian presheaf underlying `Fᵃ` on the size-bounded small étale site is the
restriction of `Fᵃ` on Mathlib's.**  This is
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso`, which unfolds the sections of the
associated-module functor, composed with the equality
`AlgebraicGeometry.SmallEtale.associatedModulePresheaf_restriction_eq`. -/
public def associatedModulePresheafIsoRestriction :
    ((associatedModule B S hS).obj F).val.presheaf ≅
      (toEtaleSite B S hS).op ⋙ (smallEtaleAssociatedSheaf S F).obj :=
  associatedModulePresheafIso B S hS F ≪≫
    eqToIso (associatedModulePresheaf_restriction_eq B S hS F).symm

/-- `Fᵃ` on the size-bounded small étale site, as an abelian sheaf there. -/
public def associatedModuleAbelianSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  ⟨((associatedModule B S hS).obj F).val.presheaf, ((associatedModule B S hS).obj F).isSheaf⟩

/-- **`Fᵃ` on the size-bounded small étale site is the restriction of `Fᵃ` on Mathlib's, as
abelian sheaves.**  The underlying presheaf identification is
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIsoRestriction`; the right-hand side is the
sheaf pushforward along the continuous functor `AlgebraicGeometry.SmallEtale.toEtaleSite`, whose
underlying presheaf is the restriction on the nose. -/
public def associatedModuleSheafIsoRestriction :
    associatedModuleAbelianSheaf B S hS F ≅
      ((toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u}
        (topology B S hS) (Scheme.smallEtaleTopology S)).obj (smallEtaleAssociatedSheaf S F) where
  hom := ⟨(associatedModulePresheafIsoRestriction B S hS F).hom⟩
  inv := ⟨(associatedModulePresheafIsoRestriction B S hS F).inv⟩
  hom_inv_id := Sheaf.hom_ext (associatedModulePresheafIsoRestriction B S hS F).hom_inv_id
  inv_hom_id := Sheaf.hom_ext (associatedModulePresheafIsoRestriction B S hS F).inv_hom_id

/-! ### Čech cohomology -/

/-- **The functor from the size-bounded small étale site to Mathlib's preserves fibre
products.**  Composed with `AlgebraicGeometry.Scheme.Etale.forget` it is
`AlgebraicGeometry.SmallEtale.toOver`, and composed once more with `CategoryTheory.Over.forget`
it is the functor to all schemes, which preserves them; the two forgetful functors reflect
them. -/
public theorem preservesLimitsOfShape_walkingCospan_toEtaleSite :
    PreservesLimitsOfShape WalkingCospan (toEtaleSite B S hS) := by
  have h0 : PreservesLimitsOfShape WalkingCospan (toOver B S hS ⋙ Over.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (toScheme B S hS))
  have h1 : PreservesLimitsOfShape WalkingCospan (toOver B S hS) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)
  have h2 : PreservesLimitsOfShape WalkingCospan
      (toEtaleSite B S hS ⋙ Scheme.Etale.forget S) := h1
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Scheme.Etale.forget S)

/-- **The comparison of the iterated fibre products of a family of the size-bounded small
étale site with those of its image family on Mathlib's is invertible.**  This is the hypothesis
`hComparison` of `Stacks.CechSite.cechComplexIsoOfFunctor`. -/
public theorem isIso_cechProductMapOfFunctor_toEtaleSite {T : SmallEtale B S hS}
    (𝒱 : PreZeroHypercover.{u} T) (n : ℕ) (i : Fin (n + 1) → 𝒱.I₀) :
    IsIso (Stacks.CechSite.cechProductMapOfFunctor (toEtaleSite B S hS) 𝒱 n i) :=
  let := preservesLimitsOfShape_walkingCospan_toEtaleSite B S hS
  let : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (𝒱.f (i a))))
      (Over.post (X := T) (toEtaleSite B S hS)) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost (toEtaleSite B S hS) 𝒱
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  Stacks.CechSite.isIso_cechProductMapOfFunctor (toEtaleSite B S hS) 𝒱 n i

/-- **The Čech complex of a family of the size-bounded small étale site with coefficients in
`Fᵃ` is the Čech complex of its image family on Mathlib's small étale site.**  The coefficients
on the left are the restriction of `AlgebraicGeometry.smallEtaleAssociatedSheaf`, which is `Fᵃ`
on the size-bounded site by
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIsoRestriction`. -/
public def cechComplexIsoImageToEtaleSite {T : SmallEtale B S hS}
    (𝒱 : PreZeroHypercover.{u} T) :
    Stacks.CechSite.cechComplex 𝒱
        ((toEtaleSite B S hS).op ⋙ (smallEtaleAssociatedSheaf S F).obj) ≅
      Stacks.CechSite.cechComplex (𝒱.map (toEtaleSite B S hS))
        (smallEtaleAssociatedSheaf S F).obj :=
  (Stacks.CechSite.cechComplexIsoOfFunctor (toEtaleSite B S hS) 𝒱
    (smallEtaleAssociatedSheaf S F).obj
    (fun n i ↦ isIso_cechProductMapOfFunctor_toEtaleSite B S hS 𝒱 n i)).symm

/-- **The positive-degree Čech cohomology of `Fᵃ` on the size-bounded small étale site vanishes
on a family whose image is a small-étale-standard covering.**

This is [Stacks, Tag 03FJ] case (b) —
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf_smallEtale` — read on the
site of [Stacks, Tag 021B] through `AlgebraicGeometry.SmallEtale.cechComplexIsoImageToEtaleSite`
and `AlgebraicGeometry.SmallEtale.associatedModulePresheafIsoRestriction`.  It is the first
positive-degree vanishing for the associated module on that site; what it is *not* is Tag 03DW
there, for which see the implementation notes. -/
public theorem isZero_cechCohomology_succ_associatedModule {T : SmallEtale B S hS}
    (𝒱 : PreZeroHypercover.{u} T)
    (h𝒱 : IsSmallEtaleStandardCovering S (𝒱.map (toEtaleSite B S hS))) (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology 𝒱
      ((associatedModule B S hS).obj F).val.presheaf p) :=
  (isZero_cechCohomology_succ_quasiCoherentPresheaf_smallEtale S F
      (𝒱.map (toEtaleSite B S hS)) h𝒱 p hp).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).mapIso
      (((Stacks.CechSite.cechComplexFunctor 𝒱).mapIso
        (associatedModulePresheafIsoRestriction B S hS F)) ≪≫
        cechComplexIsoImageToEtaleSite B S hS F 𝒱))

end AlgebraicGeometry.SmallEtale

end
