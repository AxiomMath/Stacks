module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.FreeOfRankDescent

/-!
# Freeness of a fixed finite rank of a stalk descends along a flat morphism

Let `f : X ⟶ Y` be a flat morphism of schemes and let `F` be an `𝒪_Y`-module of finite type. For
`x : X` the stalk of `f^*F` at `x` is the extension of scalars `𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} F_{f(x)}`
along a flat local — hence faithfully flat — homomorphism of local rings, and `F_{f(x)}` is a
finite module. So if the stalk of `f^*F` at `x` is free of rank `p`, then the stalk of `F` at
`f(x)` is free of rank `p`.

This is the first step of the proof of the first assertion of Stacks 05MS: freeness of a fixed
rank at the generic point of a fibre upstairs forces freeness of that rank at the generic point
of the fibre downstairs, for a member of an fpqc covering of the base.

## Main definitions

* `AlgebraicGeometry.StalkFreeOfRank`: the stalk of a module at a point is free of a given finite
  rank over the local ring there.

## Main results

* `AlgebraicGeometry.StalkFreeOfRank.of_modulePullback`: the descent along a flat morphism.
* `AlgebraicGeometry.StalkFreeOfRank.of_isFiniteLocallyFreeOfRank_restrict`: a module which is
  finite locally free of rank `p` on an open neighbourhood of a point has free stalk of rank `p`
  there.

## Implementation notes

The stalk of a sheaf of modules on a scheme is spelled
`TopCat.Presheaf.stalk (C := AddCommGrpCat) F.val.presheaf x`, a module over the `CommRingCat`
stalk `X.presheaf.stalk x` through
`AlgebraicGeometry.Scheme.Modules.moduleStalk`; this is the spelling in which the
identification of the stalk of a pullback with an extension of scalars,
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, is stated, and the one in
which the `Algebra` instance on the pair of stalks lives.

Faithful flatness of the homomorphism of stalks is
`AlgebraicGeometry.faithfullyFlat_stalkMap`, finiteness of the stalk of a module of
finite type is `Stacks.StalkFiniteType.finite_stalk`, and the descent of freeness of a fixed rank
along a faithfully flat extension of a local ring is
`Module.nonempty_linearEquiv_finsupp_of_faithfullyFlat`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The stalk of a module at a point is free of rank `p` over the local ring at that point. -/
def StalkFreeOfRank {X : Scheme.{u}} (F : X.Modules) (x : X) (p : ℕ) : Prop :=
  Nonempty (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x
    ≃ₗ[X.presheaf.stalk x] (Fin p →₀ (X.presheaf.stalk x)))

/-- **Freeness of a fixed finite rank of a stalk descends along a flat morphism.** If the stalk
at `x` of the pullback of a module of finite type along a flat morphism is free of rank `p`, then
the stalk of the module at the image of `x` is free of rank `p`.

The stalk of the pullback is `𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} F_{f(x)}`, the homomorphism of stalks is
flat and local hence faithfully flat, and `F_{f(x)}` is a finite module because `F` is of finite
type. -/
theorem StalkFreeOfRank.of_modulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (F : Y.Modules) [F.IsFiniteType] (x : X) (p : ℕ)
    (h : StalkFreeOfRank ((Scheme.Modules.pullback f).obj F) x p) :
    StalkFreeOfRank F (f.base x) p := by
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have hff : RingHom.FaithfullyFlat (f.stalkMap x).hom :=
    faithfullyFlat_stalkMap f x
  have hffm : Module.FaithfullyFlat (Y.presheaf.stalk (f.base x))
      (X.presheaf.stalk x) := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    simpa [RingHom.algebraMap_toAlgebra] using hff
  have hfin : Module.Finite (Y.presheaf.stalk (f.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf
        (f.base x)) :=
    Stacks.StalkFiniteType.finite_stalk F (f.base x)
  obtain ⟨e⟩ := exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom F x
  obtain ⟨g⟩ := h
  have key : Nonempty ((X.presheaf.stalk x ⊗[(Y.presheaf.stalk (f.base x))]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf (f.base x)))
      ≃ₗ[X.presheaf.stalk x] (Fin p →₀ (X.presheaf.stalk x))) := ⟨e.symm.trans g⟩
  exact Module.nonempty_linearEquiv_finsupp_of_faithfullyFlat _ _ _ p key

/-- **A module finite locally free of rank `p` near a point has free stalk of rank `p` there.**
The stalk of the restriction to a neighbourhood is free of rank `p` because the restriction is
finite locally free of that rank, and the inclusion of an open is flat, so
`AlgebraicGeometry.StalkFreeOfRank.of_modulePullback` carries that back to the ambient
scheme. -/
theorem StalkFreeOfRank.of_isFiniteLocallyFreeOfRank_restrict {X : Scheme.{u}} (F : X.Modules)
    [F.IsFiniteType] {U : X.Opens} {x : X} (hx : x ∈ U) (p : ℕ)
    (hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) p) :
    StalkFreeOfRank F x p := by
  have hst : StalkFreeOfRank ((Scheme.Modules.pullback U.ι).obj F) ⟨x, hx⟩ p :=
    Stacks.SheafOfModules.TopWedge.nonempty_stalkLinearEquiv_finsupp
      (F := (Scheme.Modules.pullback U.ι).obj F) (r := p) (hF := hrank) (x := ⟨x, hx⟩)
  exact StalkFreeOfRank.of_modulePullback U.ι F ⟨x, hx⟩ p hst

end AlgebraicGeometry

end
