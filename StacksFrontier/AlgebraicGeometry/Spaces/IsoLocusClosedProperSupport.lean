module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapIsoLocusRepresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupportUnconditional

/-!
# The isomorphism locus is a closed subspace when the support is proper

In Situation Stacks 083F — a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` and a
map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — Stacks 083N says that if (1) `f` is locally of
finite presentation, (2) `ℱ` is locally of finite presentation and flat over `B`, (3) the
support of `ℱ` is proper over `B`, and (4) `u` is surjective, then `F_iso` is an algebraic space
and `F_iso ⟶ B` is a closed immersion, which is of finite presentation as soon as `𝒢` is of
finite presentation.

The proof is the source's.  With `𝒦 = Ker(u)` and `v : 𝒦 ⟶ ℱ` the inclusion, Stacks 0CVM gives
`F_{u,iso} = F_{v,zero}`; Stacks 083M applied to `v`, whose target `ℱ` satisfies the hypotheses
of 083M by (1)–(3), represents `F_{v,zero}` by a closed subspace of `B`; and `𝒦` is of finite
type when `𝒢` is of finite presentation (Stacks 082T), which gives the last statement.  The
first and last steps are
`AlgebraicGeometry.Space.ModuleMapSituation.isoLocusRepresentation_of_kernelSituation`.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isoLocusRepresentation_of_hasProperSupport`:
  **Stacks 083N**.

## References

* [Stacks Project, Tag 083N](https://stacks.math.columbia.edu/tag/083N)
* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
* [Stacks Project, Tag 0CVM](https://stacks.math.columbia.edu/tag/0CVM)
* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 083N.**  In Situation 083F, assume that
1. `f` is locally of finite presentation,
2. `ℱ` is locally of finite presentation and flat over `B`,
3. the support of `ℱ` is proper over `B`, and
4. `u` is surjective.

Then the functor `F_iso` is an algebraic space and `F_iso ⟶ B` is a closed immersion; if `𝒢` is
of finite presentation, then `F_iso ⟶ B` is of finite presentation.

The conclusion `AlgebraicGeometry.Space.ModuleMapSituation.IsoLocusRepresentation` is the
existence of a subfunctor `Z` of `B` which is a closed subspace (an algebraic space whose
inclusion is a closed immersion), whose inclusion is of finite presentation when `𝒢` is of finite
presentation, and which represents `F_iso`.  Being of finite presentation is a local condition
for modules on a site, so `SheafOfModules.IsFinitePresentationOnSite` is the source's "locally
of finite presentation".  The hypotheses are exactly the source's.

The proof is the source's: Stacks 083M applied to the kernel inclusion `Ker(u) ⟶ ℱ`
(`AlgebraicGeometry.Space.ModuleMapSituation.zeroLocusRepresentation_of_hasProperSupport` on
`AlgebraicGeometry.Space.ModuleMapSituation.kernelSituation`), transported to `F_iso` by
Stacks 0CVM and Stacks 082T
(`AlgebraicGeometry.Space.ModuleMapSituation.isoLocusRepresentation_of_kernelSituation`). -/
@[stacks 083N "the full statement at the source's hypotheses alone: f locally of finite \
presentation, F locally of finite presentation and flat over B with support proper over B, u \
surjective; F_iso is represented by a closed subspace of B, of finite presentation over B when G \
is of finite presentation"]
theorem isoLocusRepresentation_of_hasProperSupport (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsLocallyOfFinitePresentation B S hS D.f.hom)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hFflat : IsFlatOver B S hS D.X.property D.f.hom D.F)
    (hproper : HasProperSupport B S hS D.X.property D.Y.property D.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf)
      ((SheafOfModules.toSheaf _).obj D.F))
    (hu : Epi D.u) :
    D.IsoLocusRepresentation :=
  D.isoLocusRepresentation_of_kernelSituation
    (SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite D.F)
    (D.kernelSituation.zeroLocusRepresentation_of_hasProperSupport hf hFfp hFflat hproper)

end ModuleMapSituation

end AlgebraicGeometry.Space

end
