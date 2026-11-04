module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKind
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Glueing.AbsoluteGlueingAnySite

/-!
# The two inputs of Stacks 0EM8 for a fibred category, reduced to the big site of a scheme

The source's proof of Stacks 0EM8 for a category `𝒳` fibred in groupoids over the big fppf
category of schemes over `S` has two inputs,
`AlgebraicGeometry.FibredSite.IsSheafFppfOfQuasicoherentOnSite`, that a `τ`-sheaf of modules
which is quasi-coherent on `(𝒳_τ, 𝒪_𝒳)` is a sheaf for the inherited fppf topology, and
`AlgebraicGeometry.FibredSite.QuasicoherentOnSiteOfLeFppf`, that quasi-coherence passes from
the inherited fppf topology to a coarser one.  **Both are theorems**, at every one of the five
topologies, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine`
(`AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_siteKind` and
`AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_siteKind`), and Stacks 0EM8 itself is
proved there with nothing assumed, on
`AlgebraicGeometry.FibredSite.tfae_isQuasicoherentClause'`.

This file **reduces both of them to the corresponding statements at the big `τ` site of a
scheme**, in which no fibred category appears.  The route is the localization at an object:
`𝒳_τ/x` *is* the big `τ` site `(Sch/U)_τ` of the scheme `U = p(x)` as an equivalence of ringed
sites, which
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKind`
supplies at every `AlgebraicGeometry.SiteKind`, and both inputs may be tested one slice at a
time — the fppf sheaf condition by
`CategoryTheory.SiteGlueing.isSheaf_of_isSheaf_over'` and quasi-coherence by
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImageKind`.  That is
the sense in which the two facts are local on coverings pulled back along `p`.

It is the same reduction that
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteColimits` performs for the
colimit clause of Stacks 06WN, and the hypotheses quantify over *every* scheme of `B` for the
same reason: the objects of `𝒳` lie over arbitrary schemes of `(Sch/S)_fppf`, not over `S`.

## Main results

* `AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_of_base`: the first input of
  the source's proof of Stacks 0EM8 for `𝒳`, granted that a quasi-coherent module on the big `τ`
  site of every scheme of `B` is a sheaf for the fppf topology.
* `AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_of_base`: the second input of the
  source's proof of Stacks 0EM8 for `𝒳`, granted that quasi-coherence on the big fppf site of
  every scheme of `B` survives being read for the coarser topology `τ`.
* `AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_of_surjective`: **the second input
  of Stacks 0EM8 for `𝒳`, over essential surjectivity of `𝓕 ↦ 𝓕^a` at every scheme of `B`
  alone** — the surjectivity half of Descent, Proposition 03DX (1) at `τ = fppf`, which is the
  one hypothesis this library already carries for that proposition.

## What this reduction is, now that the two inputs are theorems

The reduction below is **the source's own route**, and it is not what discharges the two inputs.
The source checks the two assertions after restricting to a slice `𝒳/x = (Sch/U)_τ` and then
appeals to the essential-surjectivity half of Descent, Proposition 03DX at the big `τ` site of
the scheme `U`; the three theorems below are exactly that passage, carried out for an arbitrary
`𝒳` and leaving the statement at the big site of a scheme as the hypothesis.  They are kept
because they say precisely which statement about a *scheme* the source's argument needs, which
nothing else in the tree records.

What actually proves the two inputs is a different route, through the affine subcategory
`𝒳_affine` of Stacks 0H0A rather than the slices: the affine inclusion is a cocontinuous dense
subsite inclusion at each of the five topologies (Stacks 0H0B,
`AlgebraicGeometry.Stack.AffineCategory.isDenseSubsite_inclusion_siteKind` and
`AlgebraicGeometry.Stack.AffineCategory.isCocontinuous_inclusion_siteKind`), restriction along
it is an equivalence of sheaf topoi (Stacks 0H0C), and on `𝒳_affine` quasi-coherence for any one
of the five topologies is the *cartesian* condition, which names no topology (Stacks 0H0E,
`AlgebraicGeometry.Stack.AffineCategory.tfae_isQuasicoherent`, whose
quasi-coherent-implies-cartesian half,
`AlgebraicGeometry.Stack.AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`,
is the content of Descent, Proposition 03DX that the source's proof of Stacks 0EM8 uses).  The
derivation is in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine`.

In the source's route all four hypotheses funnel into the essential-surjectivity half of
Descent, Proposition 03DX **at the big site**.  In the library, 03DX enters instead through
Stacks 0GZV and the cartesian criterion on the affine subcategory, not through essential
surjectivity of `𝓕 ↦ 𝓕^a`.  Two related facts:

* `AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum` rests on
  the effectivity half of Descent, Proposition 023T, which is a theorem with no hypothesis,
  `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`
  (`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcEffectiveUnconditional.lean:63`), and
  `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule_of_descentDatum`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/QcohGlueEffectivity.lean:136`) already
  has it discharged.  What that reduction still carries is the descent datum itself.
* `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleCounit.lean:332`) and
  `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'` are Descent,
  Proposition 03DX clause (2) at `τ = étale` **with no hypothesis**, registered against the tag
  by `add_to_stacks` at the end of that file.  The first of them is the genuine
  clause (2), for the *small* étale site.  It is nevertheless not a route to the two inputs here: `𝓕 ↦ 𝓕^a` out of `QCoh(𝒪_S)` onto the quasi-coherent
  modules of the big site `(Sch/S)_τ` is a different functor
  (`AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule`), and composing
  the two equivalences needs it, which is why
  `AlgebraicGeometry.smallEtaleBigSiteQuasicoherentEquivalence` carries both as hypotheses.

So essential surjectivity of `𝓕 ↦ 𝓕^a` at the big site is not available, and the
hypothesis of
`AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_of_surjective` below is
undischarged; it is not needed for Stacks 0EM8.

The statements are made for `𝒳 : Type (u + 1)` with `Category.{u} 𝒳`, which is the universe
shape of the localization at an object; the two inputs and Stacks 0EM8 itself are stated for
an arbitrary `𝒳` and are not narrowed by anything here.

## References

* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 0H0A](https://stacks.math.columbia.edu/tag/0H0A)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The first input of Stacks 0EM8 for a fibred category, from the same statement at the big
`τ` site of a scheme.**  Granted that every quasi-coherent module on the big `τ` site of a
scheme of `B` is a sheaf for the fppf topology, a `τ`-sheaf of modules on `𝒳` which is
quasi-coherent on `(𝒳_τ, 𝒪_𝒳)` is a sheaf for the inherited fppf topology.

The fppf sheaf condition may be tested on the slices `𝒳/x`
(`CategoryTheory.SiteGlueing.isSheaf_of_isSheaf_over'`), which is what makes this reduction
possible with no covering argument of its own.  On the slice at `x` the module becomes `x^*𝓕`,
quasi-coherent on `(Sch/U)_τ` by
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImageKind`, so the
hypothesis applies to it at the scheme `U = p(x)`; the equivalence of sites
`𝒳_fppf/x ≌ (Sch/U)_fppf` carries the sheaf condition back. -/
public theorem isSheafFppfOfQuasicoherentOnSite_of_base (τ : SiteKind)
    (hbase : ∀ (T : Scheme.{u}) (hT : B.Contains T)
      (G : SheafOfModules.{u} (baseRingStructureSheaf B T hT τ)),
      G.IsQuasicoherentOnSite →
        Presheaf.IsSheaf (BigFppfOver.topology B T hT) G.val.presheaf) :
    IsSheafFppfOfQuasicoherentOnSite B S hS p hp τ := by
  intro M hM
  refine SiteGlueing.isSheaf_of_isSheaf_over'
    (BigFppfOver.associatedTopology B S hS p .fppf) M.val.presheaf fun x => ?_
  have : (localizationEquivalence B S hS p hp x).functor.IsDenseSubsite
      (localizedTopologyKind B S hS p .fppf x)
      (BigFppfOver.topology B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x)) :=
    isDenseSubsite_localizationEquivalence_functor_kind B S hS p hp .fppf x
  have hsh := hbase (baseScheme B S hS p x) (contains_baseScheme B S hS p x)
    (objectInverseImageKind B S hS p hp τ x M)
    ((isQuasicoherentOnSite_iff_forall_objectInverseImageKind B S hS p hp τ M).1 hM x)
  have hc := (localizationEquivalence B S hS p hp x).functor.op_comp_isSheaf
    (localizedTopologyKind B S hS p .fppf x)
    (BigFppfOver.topology B (baseScheme B S hS p x)
      (contains_baseScheme B S hS p x))
    (⟨_, hsh⟩ : Sheaf (BigFppfOver.topology B (baseScheme B S hS p x)
      (contains_baseScheme B S hS p x)) AddCommGrpCat.{u})
  exact (Presheaf.isSheaf_of_iso_iff
    (Functor.isoWhiskerRight (localizationEquivalence B S hS p hp x).op.unitIso
      ((Over.forget x).op ⋙ M.val.presheaf))).mpr hc

/-- **The second input of Stacks 0EM8 for a fibred category, from the same statement at the big
site of a scheme.**  Granted that quasi-coherence on the big fppf site of a scheme of `B`
survives being read for the coarser topology `τ`, quasi-coherence on the inherited fppf site of
`𝒳` survives being read for the inherited `τ`-topology.

Both sides are tested object by object through
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImageKind`, at `τ`
and at `.fppf` respectively, and on the slice at `x` reading a module for the coarser topology
is `AlgebraicGeometry.BigFppfOver.restrictTopology` at the scheme `U = p(x)`: the underlying
presheaf of modules is the same on both sides, so the two readings of `x^*𝓕` are equal. -/
public theorem quasicoherentOnSiteOfLeFppf_of_base (τ : SiteKind)
    (hbase : ∀ (T : Scheme.{u}) (hT : B.Contains T)
      (N : SheafOfModules.{u} (BigFppfOver.structureSheaf B T hT)),
      N.IsQuasicoherentOnSite →
        ((BigFppfOver.restrictTopology B T hT τ).obj N).IsQuasicoherentOnSite) :
    QuasicoherentOnSiteOfLeFppf B S hS p hp τ := by
  intro M hM
  refine (isQuasicoherentOnSite_iff_forall_objectInverseImageKind B S hS p hp τ
    ((Stacks.SheafOfModules.comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
      (ringStructureSheafCore B S hS p hp .fppf)).obj M)).2 fun x => ?_
  exact hbase (baseScheme B S hS p x) (contains_baseScheme B S hS p x)
    (objectInverseImageKind B S hS p hp .fppf x M)
    ((isQuasicoherentOnSite_iff_forall_objectInverseImageKind B S hS p hp .fppf M).1 hM x)

/-- **The second input of Stacks 0EM8 for a fibred category, over essential surjectivity of
`𝓕 ↦ 𝓕^a` at every scheme of `B` alone.**

At the big fppf site of a scheme the input is Descent, Proposition 03DX read backwards: the
module is `𝓕^a` for a quasi-coherent `𝒪_T`-module `𝓕`, the two readings of `𝓕^a` have the same
underlying presheaf of modules by Stacks 0GNE, and `𝓕^a` on `(Sch/T)_τ` is quasi-coherent by
Descent, Lemma 03DV (1), which this library proves at every `AlgebraicGeometry.SiteKind`. -/
public theorem quasicoherentOnSiteOfLeFppf_of_surjective (τ : SiteKind)
    (hsurj : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      BigFppfOver.QuasicoherentIsEssImageAssociatedModule B T hT) :
    QuasicoherentOnSiteOfLeFppf B S hS p hp τ :=
  quasicoherentOnSiteOfLeFppf_of_base B S hS p hp τ fun T hT N hN => by
    obtain ⟨F, ⟨e⟩⟩ := hsurj T hT N hN
    have := F.property
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((BigFppfOver.restrictTopologyAssociatedModuleIso B T hT τ F.obj).symm ≪≫
        (BigFppfOver.restrictTopology B T hT τ).mapIso e)
      (BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B T hT τ F.obj
        F.property)

end AlgebraicGeometry.FibredSite

end
