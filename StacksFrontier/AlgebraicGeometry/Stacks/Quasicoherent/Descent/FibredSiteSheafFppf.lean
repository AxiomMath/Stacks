module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKind
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKindExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalence

/-!
# The first input of Stacks 0EM8, discharged

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids.
`AlgebraicGeometry.FibredSite.IsSheafFppfOfQuasicoherentOnSite` — the first of the two inputs of
Stacks 0EM8 — asks that a sheaf of modules on the associated `τ`-site of `𝒳` which is
quasi-coherent there in the sense of Stacks 03DL (6) be a sheaf for the inherited **fppf**
topology.  **This file proves it, with no hypothesis, at every `AlgebraicGeometry.SiteKind`.**

It is the source's own argument.  Restrict the module to `𝒳/x` for an object `x` of `𝒳` lying
over a scheme `U`, where `𝒳_τ/x = (Sch/U)_τ`; there it is quasi-coherent, so by the
essential-surjectivity half of Descent, Proposition 03DX (1) at `τ` — which is
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule` — it is an `𝓗^a`,
and `𝓗^a` is a sheaf for the fppf topology by Descent, Lemma 03DT.  Those two steps are packaged
together as `AlgebraicGeometry.BigFppfOver.isSheaf_fppf_of_isQuasicoherentOnSite`.  What is left
is bookkeeping: the equivalence of sites `𝒳_τ/x ≌ (Sch/U)_τ` of Stacks 06WI carries the fppf
sheaf condition back to `𝒳/x`, and the family of *all* objects of `𝒳` covers the final object,
so `CategoryTheory.SiteGlueing.isSheaf_of_coversTop_of_isSheaf_over'` assembles the slice-wise
statements into the statement on `𝒳`.

## Main results

* `AlgebraicGeometry.FibredSite.isSheaf_fppf_over_of_isQuasicoherentOnSite`: the inherited fppf
  sheaf condition for the restriction of a quasi-coherent module to `𝒳/x`.

## Relation to Stacks 0EM8

The first input of Stacks 0EM8 itself, that a `τ`-sheaf of modules quasi-coherent on
`(𝒳_τ, 𝒪_𝒳)` is a sheaf for the inherited fppf topology, is the base's
`AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_siteKind`, and the three-way
equivalence is `AlgebraicGeometry.FibredSite.tfae_isQuasicoherentClause'`; this file keeps only
the slice-wise statement.

## Implementation notes

No `stacks` attribute.  This is one input of Stacks 0EM8 and not the equivalence the tag names;
the equivalence is `AlgebraicGeometry.FibredSite.tfae_isQuasicoherentClause`, which already
carries it.

The covering family used is the family of *all* objects of `𝒳`, indexed by
`ULift.{v} 𝒳`: `Stacks.SheafOfModules.coversTop_ulift_self` says it covers the final object
for any topology, since the sieve it generates at an object contains that object's identity.  No
smaller family would do without a choice, and none is needed — the slice-wise statement is
available at every object.

## References

* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The restriction of a quasi-coherent module on `𝒳_τ` to `𝒳/x` is a sheaf for the localized
inherited fppf topology.**  Its inverse image on `(Sch/U)_τ`, `U` the scheme `x` lies over, is
quasi-coherent by `AlgebraicGeometry.FibredSite`
`.isQuasicoherentOnSite_iff_forall_objectInverseImageKind`, hence an fppf sheaf by
`AlgebraicGeometry.BigFppfOver.isSheaf_fppf_of_isQuasicoherentOnSite`; and the equivalence of
sites `𝒳_τ/x ≌ (Sch/U)_τ` of Stacks 06WI carries that back, its functor being continuous for the
two localized fppf topologies. -/
public theorem isSheaf_fppf_over_of_isQuasicoherentOnSite (τ : SiteKind)
    {M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)}
    (hM : M.IsQuasicoherentOnSite) (x : 𝒳) :
    Presheaf.IsSheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      ((Over.forget x).op ⋙ M.val.presheaf) := by
  have hbig : Presheaf.IsSheaf (BigFppfOver.topology B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x))
      (objectInverseImageKind' B S hS p hp τ x M).val.presheaf :=
    BigFppfOver.isSheaf_fppf_of_isQuasicoherentOnSite B (baseScheme' B S hS p x)
      (contains_baseScheme' B S hS p x) τ _
      ((isQuasicoherentOnSite_iff_forall_objectInverseImageKind' B S hS p hp τ M).1 hM x)
  have key : Presheaf.IsSheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      ((localizationEquivalence' B S hS p hp x).functor.op ⋙
        ((localizationEquivalence' B S hS p hp x).inverse.op ⋙
          ((Over.forget x).op ⋙ M.val.presheaf))) :=
    Functor.op_comp_isSheaf (localizationEquivalence' B S hS p hp x).functor
      ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      (BigFppfOver.topology B (baseScheme' B S hS p x) (contains_baseScheme' B S hS p x))
      ⟨_, hbig⟩
  refine (Presheaf.isSheaf_of_iso_iff (Functor.leftUnitor _)).mp ?_
  refine (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerRight
    (localizationEquivalence' B S hS p hp x).op.unitIso
    ((Over.forget x).op ⋙ M.val.presheaf))).mpr ?_
  exact (Presheaf.isSheaf_of_iso_iff (Functor.associator _ _ _)).2 key

end AlgebraicGeometry.FibredSite

end
