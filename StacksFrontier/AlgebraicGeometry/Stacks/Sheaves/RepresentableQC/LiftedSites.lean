module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.ChartCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.ChartFunctor
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekTypeExactness
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.DenseSubsiteMorphism
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismCriteria
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSite

/-!
# The lifted ringed sites of Stacks 0H0K and the morphism between them

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be fibred in groupoids and representable by an algebraic space `F`
through an equivalence `e` over `(Sch/S)_{fppf}`. The proof of Stacks 0H0K compares the
étale affine site `𝒳_{affine, étale}` of `𝒳` (Stacks 0H0A, 0H0D) with the affine étale site
`F_{affine, étale}` of `F` (Stacks 04JS) along the functor of affine étale charts
`F_{affine, étale} ⥤ 𝒳_{affine}` (`AlgebraicGeometry.Stack.affineEtaleInclusion`).

The derived machinery for morphisms of ringed sites in this library is stated for ringed sites
in a single universe (`AlgebraicGeometry.RingedSite.{M, M, M}`), while `𝒳_{affine}` has objects in
`v`, morphisms in `w` and rings in `u`, and `F_{affine, étale}` has objects in `u + 1`. This file
lifts both ringed sites to the single universe `M = max v w u t`, which is the universe of the
modules of `quasiCoherentDerived.{u, v, w, t}`, and constructs the morphism of ringed sites
between the lifts.

## Main definitions

* `AlgebraicGeometry.Space.affineEtaleRingedSite`: the affine étale site of `F` with the
  restriction of the structure sheaf of `F`.
* `AlgebraicGeometry.Space.affineEtaleLiftedSite`: its lift to the universe `max u m`, along the
  small model of the affine étale site.
* `AlgebraicGeometry.Stack.affineLiftedSite`: the lift of `(𝒳_{affine, étale}, 𝒪)` to the
  universe `max v w u t`.
* `AlgebraicGeometry.Stack.liftedAffineEtaleHom`: the morphism of ringed sites from the lift of
  `𝒳_{affine, étale}` to the lift of `F_{affine, étale}` (for `m = max v w t`).

## Main results

* `AlgebraicGeometry.Space.restrictionFunctor_isMorphismOfSites_max`: Stacks 073M for sheaves of
  sets in every universe above that of the schemes.
* `AlgebraicGeometry.Stack.affineEtaleInclusion_isMorphismOfSites`: the functor of affine étale
  charts defines a morphism of sites.
* The functor of `liftedAffineEtaleHom` is full, faithful, continuous and cocontinuous, and its
  structure map is an isomorphism (`liftedAffineEtaleHom_fsharp_isIso`).

## Implementation notes

**Universes.** `𝒳_{affine}` is lifted by `AlgebraicGeometry.RingedSite.lift`, i.e. along
`AsSmall`. The affine étale site of `F` is *not* lifted along `AsSmall`, which would keep its
objects in `u + 1` and force the single universe, hence the universe of the modules, to be at
least `u + 1`; instead it is transported (`AlgebraicGeometry.RingedSite.transport`) to its small
model at `max u m`, which exists because it is essentially small at `u`
(`AlgebraicGeometry.Space.AffineEtale.instEssentiallySmall`). Both lifts are therefore ringed
sites in exactly `max v w u t` when `m = max v w t`.

**The site condition.** `F_{affine, étale}` has fibre products but no binary products, so the
criterion `Stacks.Sites.LowerShriek.isMorphismOfSites_of_coversTop` used for Stacks 073M does not
apply to the functor of affine étale charts. Instead, followed by the dense subsite inclusion
`𝒳_{affine} ⥤ 𝒳` of Stacks 0H0B it is the composite of the dense subsite inclusion
`F_{affine, étale} ⥤ F_{étale}` of Stacks 04JS with the morphism of sites of Stacks 073M, and
`IsMorphismOfSites.of_comp_isDenseSubsite` cancels the dense subsite inclusion. Stacks 073M is
needed for sheaves of sets in `Type M` rather than `Type u`, which is
`AlgebraicGeometry.Space.restrictionFunctor_isMorphismOfSites_max`.

## References

* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t m

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The affine étale ringed site of an algebraic space** `F`: the affine étale site of
Stacks 04JS with the restriction of the structure sheaf of the small étale site of `F`. Its ring
of sections at an affine chart is the ring of global functions of that chart,
`AlgebraicGeometry.Space.affineEtaleChartRings`. -/
noncomputable abbrev affineEtaleRingedSite : RingedSite.{u + 1, u, u} :=
  haveI := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  affineRingedSite (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F) (structureSheaf B S hS F hF)

/-- The structure sheaf of the affine étale ringed site is the presheaf of chart rings. -/
theorem affineEtaleRingedSite_O_obj :
    (affineEtaleRingedSite B S hS F hF).O.obj = affineEtaleChartRings B S hS F :=
  rfl

/-- **The lift of the affine étale ringed site of `F` to a single universe** `max u m`: its
transport along the comparison of the affine étale site with its small model at `max u m`,
with the section rings raised to `max u m`. Since the affine étale site is essentially small at
the universe of the schemes, the underlying category, its morphisms, the section rings and the
modules all live in the universe `max u m`, with no shift to `u + 1`. -/
noncomputable abbrev affineEtaleLiftedSite : RingedSite.{max u m, max u m, max u m} :=
  haveI := essentiallySmall_lift.{m, u} (AffineEtale B S hS F)
  (affineEtaleRingedSite B S hS F hF).transport.{m}
    (equivSmallModel.{max u m} (AffineEtale B S hS F))

section MorphismOfSites

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

include hF hp in
/-- **Stacks 073M at every universe of sheaves of sets above that of the schemes.** The functor
`F_étale ⥤ 𝒳` of Stacks 073M defines a morphism of sites for sheaves of sets valued in
`Type (max u t)`: lower shriek along it is left exact, by the argument of
`AlgebraicGeometry.Space.restrictionFunctor_isMorphismOfSites` (the case `t = u`), both sites
being essentially small at `u` and hence at `max u t`. -/
theorem restrictionFunctor_isMorphismOfSites_max :
    IsMorphismOfSites.{max u t} (restrictionFunctor B S hS F p e)
      (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale) := by
  let := restrictionFunctor_isContinuous B S hS F p hp e
  let : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
  let : EssentiallySmall.{max u t} 𝒳 := essentiallySmall_lift.{t, u} 𝒳
  let : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) (Type (max u t)) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} _ _
  let : (BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective
      (Type (max u t)) :=
    .ofEssentiallySmall.{_, _, _, _, max u t} _
  let (Y : 𝒳ᵒᵖ) : EssentiallySmall.{max u t}
      (CostructuredArrow (restrictionFunctor B S hS F p e).op Y) :=
    essentiallySmall_lift.{t, u} _
  let (Q : (SmallEtale B S hS F)ᵒᵖ ⥤ Type (max u t)) :
      (restrictionFunctor B S hS F p e).op.HasLeftKanExtension Q := by
    let (Y : 𝒳ᵒᵖ) : HasColimitsOfShape
        (CostructuredArrow (restrictionFunctor B S hS F p e).op Y) (Type (max u t)) :=
      hasColimitsOfShape_of_essentiallySmall.{max u t} _ _
    let : (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension Q :=
      fun _ => inferInstance
    infer_instance
  exact Stacks.Sites.LowerShriek.isMorphismOfSites_of_coversTop
    (restrictionFunctor B S hS F p e) _ _ (restrictionFunctor_coversTop B S hS F p hF hp e)

end MorphismOfSites

end Space

namespace Stack

open AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The lift of the étale affine ringed site of `𝒳` to a single universe**: the ringed site
`(𝒳_{affine, étale}, 𝒪)` of Stacks 0H0D lifted, by `AlgebraicGeometry.RingedSite.lift`, to the
universe `max v w u t`, in which its underlying category, morphisms, section rings and modules
all live. -/
noncomputable abbrev affineLiftedSite : RingedSite.{max v w u t, max v w u t, max v w u t} :=
  RingedSite.lift.{t} (AffineCategory.siteKindRingedSite B S hS p hp .etale)

section Morphism

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

include hF hp in
/-- **The affine étale charts of `F` inside `𝒳_{affine}` define a morphism of sites**
`𝒳_{affine, étale} ⟶ F_{affine, étale}`, for sheaves of sets in every universe above that of
the schemes. The functor `F_{affine, étale} ⥤ 𝒳_{affine}` has no binary products to work with,
so this is deduced from Stacks 073M through the two dense subsite inclusions of Stacks 04JS and
Stacks 0H0B: followed by `𝒳_{affine} ⥤ 𝒳` it is the composite `F_{affine, étale} ⥤ F_{étale} ⥤ 𝒳`
of two morphisms of sites, and a functor which becomes a morphism of sites after a dense subsite
inclusion is one. -/
theorem affineEtaleInclusion_isMorphismOfSites :
    IsMorphismOfSites.{max u t} (affineEtaleInclusion B S hS F p e)
      (AffineEtale.topology B S hS F)
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale)) := by
  let : (affineEtaleInclusion B S hS F p e).IsContinuous (AffineEtale.topology B S hS F)
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale)) :=
    affineEtaleInclusion_isContinuous B S hS F p e hF hp
  let : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
  let := AffineCategory.isDenseSubsite_inclusion_siteKind B S hS p hp .etale
  let := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  let (X : (Space.SmallEtale B S hS F)ᵒᵖ) : HasLimitsOfShape
      (StructuredArrow X (AffineEtale.inclusion B S hS F).op) (Type (max u t)) :=
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  let (X : 𝒳ᵒᵖ) : HasLimitsOfShape
      (StructuredArrow X (AffineCategory.inclusion B S hS p).op) (Type (max u t)) :=
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  let := IsMorphismOfSites.ofIsDenseSubsite.{max u t} (AffineEtale.inclusion B S hS F)
    (J := AffineEtale.topology B S hS F) (K := Space.SmallEtale.topology B S hS F)
  let := restrictionFunctor_isMorphismOfSites_max.{u, v, w, t} B S hS F hF p hp e
  exact IsMorphismOfSites.of_comp_isDenseSubsite (affineEtaleInclusion B S hS F p e)
    (AffineCategory.inclusion B S hS p)
    (isMorphismOfSites_comp.{max u t} (BigFppfOver.associatedTopology B S hS p .etale)
      (Space.SmallEtale.topology B S hS F) (AffineEtale.topology B S hS F)
      (AffineEtale.inclusion B S hS F) (restrictionFunctor B S hS F p e))

/-- **The functor underlying the morphism of lifted ringed sites**: the functor
`F_{affine, étale} ⥤ 𝒳_{affine}` of the affine étale charts, read on the lifted sites, i.e.
preceded by the comparison of the affine étale site with its small model and followed by
`AsSmall.up`. -/
noncomputable def liftedAffineEtaleInclusion :
    (affineEtaleLiftedSite.{u, max v w t} B S hS F hF).C ⥤
      (affineLiftedSite.{u, v, w, t} B S hS p hp).C :=
  haveI := essentiallySmall_lift.{max v w t, u} (AffineEtale B S hS F)
  (equivSmallModel.{max u (max v w t)} (AffineEtale B S hS F)).inverse ⋙
    affineEtaleInclusion B S hS F p e ⋙ AsSmall.equiv.functor

/-- The functor of the lifted sites is full. -/
instance liftedAffineEtaleInclusion_full :
    (liftedAffineEtaleInclusion B S hS p hp F hF e).Full := by
  unfold liftedAffineEtaleInclusion
  infer_instance

/-- The functor of the lifted sites is faithful. -/
instance liftedAffineEtaleInclusion_faithful :
    (liftedAffineEtaleInclusion B S hS p hp F hF e).Faithful := by
  unfold liftedAffineEtaleInclusion
  infer_instance

/-- The functor of the lifted sites is continuous. -/
instance liftedAffineEtaleInclusion_isContinuous :
    (liftedAffineEtaleInclusion B S hS p hp F hF e).IsContinuous
      (affineEtaleLiftedSite.{u, max v w t} B S hS F hF).J
      (affineLiftedSite.{u, v, w, t} B S hS p hp).J := by
  have := essentiallySmall_lift.{max v w t, u} (AffineEtale B S hS F)
  let : (affineEtaleInclusion B S hS F p e).IsContinuous (AffineEtale.topology B S hS F)
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale)) :=
    affineEtaleInclusion_isContinuous B S hS F p e hF hp
  let : (affineEtaleInclusion B S hS F p e ⋙ AsSmall.equiv.functor).IsContinuous
      (AffineEtale.topology B S hS F) (affineLiftedSite.{u, v, w, t} B S hS p hp).J :=
    Functor.isContinuous_comp _ _ _
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale)) _
  unfold liftedAffineEtaleInclusion
  exact Functor.isContinuous_comp _ _ _ (AffineEtale.topology B S hS F) _

/-- The functor of the lifted sites is cocontinuous. -/
instance liftedAffineEtaleInclusion_isCocontinuous :
    (liftedAffineEtaleInclusion B S hS p hp F hF e).IsCocontinuous
      (affineEtaleLiftedSite.{u, max v w t} B S hS F hF).J
      (affineLiftedSite.{u, v, w, t} B S hS p hp).J := by
  have := essentiallySmall_lift.{max v w t, u} (AffineEtale B S hS F)
  let : (affineEtaleInclusion B S hS F p e).IsCocontinuous (AffineEtale.topology B S hS F)
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale)) :=
    affineEtaleInclusion_isCocontinuous B S hS F p e hF hp
  let : (affineEtaleInclusion B S hS F p e ⋙ AsSmall.equiv.functor).IsCocontinuous
      (AffineEtale.topology B S hS F) (affineLiftedSite.{u, v, w, t} B S hS p hp).J :=
    isCocontinuous_comp _ _ _
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale))
  unfold liftedAffineEtaleInclusion
  exact isCocontinuous_comp _ _ _ (AffineEtale.topology B S hS F)

/-- The functor of the lifted sites defines a morphism of sites. -/
theorem liftedAffineEtaleInclusion_isMorphismOfSites :
    (liftedAffineEtaleInclusion B S hS p hp F hF e).IsMorphismOfSites
      (affineEtaleLiftedSite.{u, max v w t} B S hS F hF).J
      (affineLiftedSite.{u, v, w, t} B S hS p hp).J := by
  have := essentiallySmall_lift.{max v w t, u} (AffineEtale B S hS F)
  let E := equivSmallModel.{max u (max v w t)} (AffineEtale B S hS F)
  let := rootMorphismOfSites_of_equivalence_inverse.{max v w u t} E
    (AffineEtale.topology B S hS F) (affineEtaleLiftedSite.{u, max v w t} B S hS F hF).J
  let := affineEtaleInclusion_isMorphismOfSites.{u, v, w, max v w t} B S hS p hp F hF e
  let := rootMorphismOfSites_of_equivalence.{max v w u t}
    (AsSmall.equiv : AffineCategory B S hS p ≌ (affineLiftedSite.{u, v, w, t} B S hS p hp).C)
    (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale))
    (affineLiftedSite.{u, v, w, t} B S hS p hp).J
  let := isMorphismOfSites_comp.{max v w u t} (affineLiftedSite.{u, v, w, t} B S hS p hp).J
    (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale))
    (AffineEtale.topology B S hS F) (affineEtaleInclusion B S hS F p e) AsSmall.equiv.functor
  exact (isMorphismOfSites_comp.{max v w u t} (affineLiftedSite.{u, v, w, t} B S hS p hp).J
    (AffineEtale.topology B S hS F) (affineEtaleLiftedSite.{u, max v w t} B S hS F hF).J
    E.inverse (affineEtaleInclusion B S hS F p e ⋙ AsSmall.equiv.functor)).toSmallIsMorphismOfSites

/-- The structure map of the morphism of lifted ringed sites, as an isomorphism: the
structure sheaf of the lifted affine étale site of `F` is the restriction along the functor of
the lifted sites of the structure sheaf of the lifted `𝒳_{affine, étale}`. On sections both are
the ring of global functions of an affine étale chart of `F`, by
`AlgebraicGeometry.Stack.affineEtaleInclusion_op_comp_affineStructureCommPresheaf`. -/
noncomputable def liftedAffineEtaleStructureIso :
    (affineEtaleLiftedSite.{u, max v w t} B S hS F hF).O ≅
      ((liftedAffineEtaleInclusion B S hS p hp F hF e).sheafPushforwardContinuous
        CommRingCat.{max v w u t} (affineEtaleLiftedSite.{u, max v w t} B S hS F hF).J
        (affineLiftedSite.{u, v, w, t} B S hS p hp).J).obj
        (affineLiftedSite.{u, v, w, t} B S hS p hp).O :=
  haveI := essentiallySmall_lift.{max v w t, u} (AffineEtale B S hS F)
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft (equivSmallModel.{max u (max v w t)} (AffineEtale B S hS F)).inverse.op
      (Functor.isoWhiskerRight
        (eqToIso (affineEtaleInclusion_op_comp_affineStructureCommPresheaf B S hS F p e).symm)
        SheafOfModules.commRingCatULift.{u, max v w t}))

/-- **The morphism of lifted ringed sites of Stacks 0H0K**, from the lifted `𝒳_{affine, étale}`
to the lifted affine étale site of `F`. Its functor is the functor of affine étale charts
`AlgebraicGeometry.Stack.liftedAffineEtaleInclusion`, which defines a morphism of sites by
`AlgebraicGeometry.Stack.liftedAffineEtaleInclusion_isMorphismOfSites`, and its structure map
is the isomorphism `AlgebraicGeometry.Stack.liftedAffineEtaleStructureIso`. -/
noncomputable def liftedAffineEtaleHom :
    RingedSite.Hom (affineLiftedSite.{u, v, w, t} B S hS p hp)
      (affineEtaleLiftedSite.{u, max v w t} B S hS F hF) where
  u := liftedAffineEtaleInclusion B S hS p hp F hF e
  isMorphismOfSites := liftedAffineEtaleInclusion_isMorphismOfSites B S hS p hp F hF e
  fsharp := (liftedAffineEtaleStructureIso B S hS p hp F hF e).hom

/-- The functor of the morphism of lifted ringed sites. -/
@[simp]
theorem liftedAffineEtaleHom_u :
    (liftedAffineEtaleHom B S hS p hp F hF e).u = liftedAffineEtaleInclusion B S hS p hp F hF e :=
  rfl

/-- The structure map of the morphism of lifted ringed sites is an isomorphism. -/
instance liftedAffineEtaleHom_fsharp_isIso :
    IsIso (liftedAffineEtaleHom B S hS p hp F hF e).fsharp :=
  inferInstanceAs (IsIso (liftedAffineEtaleStructureIso B S hS p hp F hF e).hom)

/-- **Every object of the lifted `𝒳_{affine, étale}` is covered by finitely many objects mapping
to the image of the functor of the lifted sites.** For every object `x` there is a finite family
`x_i ⟶ x` generating a covering sieve, each `x_i` admitting an arrow to the image of an object
of the lifted affine étale site of `F`; the family lies over a finite étale covering of affine
schemes (Stacks 073M with Stacks 0H0B,
`AlgebraicGeometry.Stack.exists_finite_etale_covering_affineEtaleInclusion`). -/
theorem exists_finite_covering_liftedAffineEtaleHom
    (x : (affineLiftedSite.{u, v, w, t} B S hS p hp).C) :
    ∃ (n : ℕ) (obj : Fin n → (affineLiftedSite.{u, v, w, t} B S hS p hp).C)
      (π : ∀ i, obj i ⟶ x),
      Sieve.ofArrows obj π ∈ (affineLiftedSite.{u, v, w, t} B S hS p hp).J x ∧
      (∀ i, ∃ y, Nonempty (obj i ⟶ (liftedAffineEtaleHom B S hS p hp F hF e).u.obj y)) ∧
      ((PreZeroHypercover.mk (Fin n) (fun i => AsSmall.down.obj (obj i))
        (fun i => AsSmall.down.map (π i))).map (AffineCategory.toScheme B S hS p)).presieve₀ ∈
        Scheme.precoverage @Etale
          ((AffineCategory.toScheme B S hS p).obj (AsSmall.down.obj x)) := by
  have := essentiallySmall_lift.{max v w t, u} (AffineEtale B S hS F)
  obtain ⟨E, hfin, het, hcov, hhom, -⟩ :=
    exists_finite_etale_covering_affineEtaleInclusion.{u, v, w, 0} B S hS F p e hF hp
      (AsSmall.down.obj x)
  let ε : Fin (Nat.card E.I₀) ≃ E.I₀ := (Finite.equivFin E.I₀).symm
  let E' := E.reindex ε
  have hs : E'.sieve₀ = E.sieve₀ := congrArg Sieve.generate (E.presieve₀_reindex ε)
  refine ⟨Nat.card E.I₀, fun i => AsSmall.up.obj (E'.X i), fun i => AsSmall.up.map (E'.f i),
    ?_, fun i => ?_, ?_⟩
  · refine (RingedSite.lift_asSmallDown_isDenseSubsite.{t}
      (AffineCategory.siteKindRingedSite B S hS p hp .etale)).functorPushforward_mem_iff.1 ?_
    refine GrothendieckTopology.superset_covering _ ?_ (hs ▸ hcov)
    rintro Z g ⟨Y, a, b, ⟨i⟩, rfl⟩
    exact ⟨_, AsSmall.up.map (E'.f i), a, Sieve.ofArrows_mk _ _ i, rfl⟩
  · obtain ⟨y, ⟨g⟩⟩ := hhom (ε i)
    let E₀ := equivSmallModel.{max u (max v w t)} (AffineEtale B S hS F)
    exact ⟨E₀.functor.obj y, ⟨AsSmall.up.map
      (g ≫ (affineEtaleInclusion B S hS F p e).map (E₀.unitIso.hom.app y))⟩⟩
  · have hpr : (E'.map (AffineCategory.toScheme B S hS p)).presieve₀ =
        (E.map (AffineCategory.toScheme B S hS p)).presieve₀ := by
      rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_map,
        E.presieve₀_reindex ε]
    exact hpr ▸ het

end Morphism

end Stack

end AlgebraicGeometry
