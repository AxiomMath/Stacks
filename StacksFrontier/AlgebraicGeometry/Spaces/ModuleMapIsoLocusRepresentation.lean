module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupport

/-!
# Representability of the isomorphism locus `F_iso` by a closed subspace of the base

In Situation Stacks 083F — a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` and a
map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — the isomorphism locus `F_iso` is the
subterminal functor `AlgebraicGeometry.Space.ModuleMapSituation.isoFunctor` on the schemes
over `B`.  Stacks 0CWD and Stacks 083N both conclude that, for a *surjective* `u`, `F_iso` is an
algebraic space whose map to `B` is a closed immersion, of finite presentation as soon as `𝒢`
is.  Both deduce this the same way: with `𝒦 = Ker(u)` and `v : 𝒦 ⟶ ℱ` the inclusion, Stacks 0CVM
gives `F_{u,iso} = F_{v,zero}`, a theorem about the vanishing locus of `v` represents
`F_{v,zero}` by a closed subspace of `B`, and Stacks 082T makes `𝒦` of finite type when `ℱ` is
of finite type and `𝒢` of finite presentation, which carries the finite-presentation clause.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.IsoLocusRepresentation`: the conclusion of
  Stacks 0CWD and of Stacks 083N — a closed subspace of `B` representing `F_iso`, whose
  inclusion is of finite presentation when `𝒢` is of finite presentation.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.zeroLocusRepresentation_of_isClosedSubspace`:
  closedness of the vanishing subfunctor `zeroSubfunctor`, and finite presentation of its
  inclusion when `ℱ` is of finite type, give the representation of `F_zero`.
* `AlgebraicGeometry.Space.ModuleMapSituation.isoLocusRepresentation_of_kernelSituation`: for a
  surjective `u` with `ℱ` of finite type, a representation of the vanishing locus of the kernel
  inclusion `Ker(u) ⟶ ℱ` is a representation of `F_iso`.

## References

* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 0CVM](https://stacks.math.columbia.edu/tag/0CVM)
* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
* [Stacks Project, Tag 0CWD](https://stacks.math.columbia.edu/tag/0CWD)
* [Stacks Project, Tag 083N](https://stacks.math.columbia.edu/tag/083N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The conclusion of Stacks 0CWD and of Stacks 083N.**  There is a subfunctor `Z` of `B`
which is a closed subspace, Stacks 02YU part (4), whose inclusion is of finite presentation as
soon as `𝒢` is of finite presentation, and which represents `F_iso`: a test scheme over `B` lies
in `F_iso` exactly when its structure morphism factors through `Z`.

The first conjunct of `AlgebraicGeometry.Space.IsClosedSubspace` is that `Z` is an algebraic
space and the second is that `Z ⟶ B` is a closed immersion, so this says exactly that `F_iso`
is an algebraic space and that `F_iso ⟶ B` is a closed immersion, of finite presentation when
`𝒢` is of finite presentation. -/
def IsoLocusRepresentation (D : ModuleMapSituation.{u, u} B S hS) : Prop :=
  ∃ Z : Subfunctor D.Y.1, IsClosedSubspace B S hS Z ∧
    (SheafOfModules.IsFinitePresentationOnSite D.G → IsFinitePresentation B S hS Z.ι) ∧
    ∀ T : D.SchemesOver, D.IsIsoAt (modulePullbackSystem B S hS) T ↔
      ∃ k : yoneda.obj T.left ⟶ Z.toFunctor, k ≫ Z.ι = T.hom.hom

/-- **The vanishing subfunctor, once closed, represents `F_zero`.**  If the subfunctor
`AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor` of `B` is a closed subspace, with
finitely presented inclusion when `ℱ` is of finite type, then it witnesses
`AlgebraicGeometry.Space.ModuleMapSituation.ZeroLocusRepresentation`: it represents `F_zero` by
`AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_iff_exists_factor_zeroSubfunctor`. -/
theorem zeroLocusRepresentation_of_isClosedSubspace (D : ModuleMapSituation.{u, u} B S hS)
    (hZ : IsClosedSubspace B S hS D.zeroSubfunctor)
    (hfp : SheafOfModules.IsFiniteTypeOnSite D.F →
      IsFinitePresentation B S hS D.zeroSubfunctor.ι) :
    D.ZeroLocusRepresentation :=
  ⟨D.zeroSubfunctor, hZ, hfp, D.isZeroAt_iff_exists_factor_zeroSubfunctor⟩

/-- **The reduction shared by Stacks 0CWD and Stacks 083N.**  Let `u : ℱ ⟶ 𝒢` be surjective with
`ℱ` of finite type, and let `v : Ker(u) ⟶ ℱ` be the kernel inclusion, the map of
`AlgebraicGeometry.Space.ModuleMapSituation.kernelSituation`.  A closed subspace of `B`
representing the vanishing locus `F_{v,zero}` represents `F_{u,iso}`, and its inclusion is of
finite presentation when `𝒢` is. -/
theorem isoLocusRepresentation_of_kernelSituation (D : ModuleMapSituation.{u, u} B S hS)
    [Epi D.u] (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (h : D.kernelSituation.ZeroLocusRepresentation) :
    D.IsoLocusRepresentation := by
  obtain ⟨Z, hZ, hfp, hzero⟩ := h
  exact ⟨Z, hZ, fun hGfp => hfp (D.isFiniteTypeOnSite_kernelSituation_F hFft hGfp),
    fun T => (D.isIsoAt_iff_kernelSituation_isZeroAt T).trans (hzero T)⟩

end ModuleMapSituation

end AlgebraicGeometry.Space

end
