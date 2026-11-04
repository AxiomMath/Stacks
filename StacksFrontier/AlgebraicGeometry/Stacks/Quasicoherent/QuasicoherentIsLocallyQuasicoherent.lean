module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleRestrictionFunctorialComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfQuasicoherentCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LocallyQuasiCoherentModulesAndAffines

/-!
# A quasi-coherent module on a category fibred in groupoids is locally quasi-coherent

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. **Clause (a) of the forward
direction of Stacks 06WK** says that a quasi-coherent `𝒪_𝒳`-module in the sense of Stacks 06WG,
that is a quasi-coherent module on the ringed site `(𝒳_{fppf}, 𝒪_𝒳)`, is locally quasi-coherent in
the sense of Stacks 06WJ: it is a sheaf for the étale topology, and for every object `x` of `𝒳`
lying over `U = p(x)` the restriction `x^*𝓕|_{U_{étale}}` is a quasi-coherent sheaf on the small
étale site of `U`. This file proves it with no hypothesis, at the module universe of the schemes.

The library carries that statement as
`AlgebraicGeometry.Stack.ForallQuasicoherentIsLocallyQuasicoherent` (the residue of Stacks 0GQD
between Stacks 0GQC and the hypothesis `hres` of
`AlgebraicGeometry.Space.restrictionPreservesQuasicoherent_of_forallIsLocallyQuasicoherent`), and
`AlgebraicGeometry.Stack.forallQuasicoherentIsLocallyQuasicoherent` discharges it.

## Main results

* `AlgebraicGeometry.Stack.isEtaleCartesian_of_isQuasicoherentOnSite`: the restriction to the
  affine subcategory `𝒳_{affine}` of Stacks 0H0A of a quasi-coherent module on `𝒳_{fppf}` satisfies
  condition (1) of Stacks 0H0F: it is cartesian over every arrow lying over an étale morphism (in
  fact over every arrow).
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isQuasicoherentFppf`: **a quasi-coherent
  module on `(𝒳_{fppf}, 𝒪_𝒳)` is locally quasi-coherent**
  (`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isQuasicoherentOnSite`), in the
  spelling `AlgebraicGeometry.Stack.IsQuasicoherentFppf` of the left-hand side of Stacks 06WK
  used by `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfQuasicoherentCriterion`.
* `AlgebraicGeometry.Stack.forallQuasicoherentIsLocallyQuasicoherent`: the library's predicate
  `AlgebraicGeometry.Stack.ForallQuasicoherentIsLocallyQuasicoherent` at module universe `u`.

## The proof

The source's proof restricts `𝓕` to `𝒳/x = (Sch/U)_{fppf}`, writes the restriction as `𝓕_U^a` for
a quasi-coherent `𝒪_U`-module `𝓕_U` by Descent, Proposition 03DX — whose essential surjectivity
half rests on the effectivity of fpqc descent of quasi-coherent modules, Descent,
Proposition 023T — and reads off `𝓕_U^a|_{U_{étale}}`. Both of those are theorems of the library
(`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'` and
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`); the route taken here is
the one through the affine subcategory, where the content of 03DX sits as the statement that a
quasi-coherent module is cartesian:

1. the restriction of `𝓕` to `𝒳_{affine, fppf}` is quasi-coherent, the affine inclusion being a
   cocontinuous dense subsite inclusion (Stacks 0H0B), and so it is cartesian over every arrow,
   `AlgebraicGeometry.Stack.AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`
   (the step of Stacks 0EM8 in
   `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine`);
2. hence for every object `x` the restriction `x^*𝓕|_{U_{étale}}` is cartesian between affine
   objects, `AlgebraicGeometry.Stack.isCartesianOnAffines_restrictModuleToSmallEtale` (the step
   (1) ⇒ (3) of Stacks 0H0F), and therefore quasi-coherent on `U_{étale}`,
   `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines` (Descent,
   Proposition 03DX (2));
3. the étale sheaf condition is the fppf one read for the coarser inherited étale topology.

## References

* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

open AffineCategory in
/-- **A quasi-coherent module on `𝒳_{fppf}` satisfies condition (1) of Stacks 0H0F.** The
restriction of a quasi-coherent module on `(𝒳_{fppf}, 𝒪_𝒳)` to the affine subcategory `𝒳_{affine}`
is cartesian over every arrow lying over an étale morphism: the restriction is quasi-coherent on
`𝒳_{affine, fppf}` by Stacks 0H0B, and a quasi-coherent module there is cartesian over every
arrow. -/
theorem isEtaleCartesian_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) :
    IsEtaleCartesian B S hS p
      ((PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj M.val) := by
  have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have := isCocontinuous_inclusion_siteKind B S hS p hp .fppf
  have hres := Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite
    (J := associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf))
    (K := BigFppfOver.associatedTopology B S hS p .fppf)
    (AffineCategory.inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf) M hM
  intro y y' f _
  exact AlgebraicGeometry.Stack.AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite
    B S hS p _ rfl hp .fppf _ _ hres f.op

/-- **Clause (a) of the forward direction of Stacks 06WK**, for a presheaf of modules satisfying
the left-hand side `AlgebraicGeometry.Stack.IsQuasicoherentFppf` of Stacks 06WK. -/
theorem isLocallyQuasicoherent_of_isQuasicoherentFppf
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : IsQuasicoherentFppf B S hS p hp F) :
    IsLocallyQuasicoherent B E h S hS p hp F :=
  hF.elim fun hs hq =>
    isLocallyQuasicoherent_of_isQuasicoherentOnSite B E h S hS p hp ⟨F, hs⟩ hq

/-- **`AlgebraicGeometry.Stack.ForallQuasicoherentIsLocallyQuasicoherent`, with no hypothesis**,
at the module universe of the schemes: every object of
`AlgebraicGeometry.FibredSite.quasicoherentModules` (Stacks 06WG) is locally quasi-coherent
(Stacks 06WJ) for the canonical big étale site. -/
theorem forallQuasicoherentIsLocallyQuasicoherent :
    ForallQuasicoherentIsLocallyQuasicoherent.{u, v, w, u} B S hS p hp :=
  fun M => isLocallyQuasicoherent_of_isQuasicoherentOnSite B (associatedBigEtaleSite B) rfl
    S hS p hp M.obj M.property

end AlgebraicGeometry.Stack
