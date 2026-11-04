module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExtTildeIso
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafAffineModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafAffineTransport
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafStalkFormula

/-!
# The stalk of the Ext sheaves of a dualizing complex

Let `X` be a locally Noetherian scheme, `K` a dualizing complex on `X`, `F` a coherent
`𝒪_X`-module and `𝓔ⁱ = 𝓔xt^{-i}_{𝒪_X}(F, K)` the Ext sheaves of `Stacks.Duality.extSheafOf`.
This file computes the stalk of `𝓔ⁱ` at a point, which is the stalk reading of
[Stacks, Tag 0A6H] that the four clauses of [Stacks, Tag 0ECM] consume.

The route is the source's. Pass to an affine open `U ∋ x`, where `F` is `M~` and `K` is `ω~` for
a finite `Γ(X, U)`-module `M` and a dualizing complex `ω` over `Γ(X, U)`; there part (3)(a) of
[Stacks, Tag 0A6H] identifies `R𝓗om(M~, ω~)` with `(RHom_{Γ(X,U)}(M, ω))~`, so `𝓔ⁱ|_U` is the
sheaf associated to the `Ext` module, and the stalk of an associated sheaf is a localization.

## Main results

* `Stacks.Duality.nonempty_stalk_extSheafOf_iso_extendScalars` — the stalk of `𝓔ⁱ` at `x ∈ U` is
  `𝒪_{X,x} ⊗_{Γ(X,U)} H^{-i}(RHom_{Γ(X,U)}(M, ω))`, for affine models `M` of `F` and `ω` of `K`.

## Implementation notes

The intermediate types of every composite are written out. Left to inference, the elaborator has
to compute the objects of composite functors through `AlgebraicGeometry.Scheme.Modules`, which is
a `def` rather than an `abbrev`, and that exceeds the 200000-heartbeat `whnf` budget.

## References

* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

-- Standard model only: `StacksDraft.DerivedHom.derivedHomAdjunction`.
attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- **The stalk of `𝓔xt^{-i}(F, K)` is the base change of the affine Ext module.** On an affine
open `U ∋ x` carrying an affine model `M` of `F` and `ω` of `K`, the stalk at `x` of the Ext sheaf
is `𝒪_{X,x} ⊗_{Γ(X,U)} H^{-i}(RHom_{Γ(X,U)}(M, ω))`.

This is the affine transport `Stacks.Duality.nonempty_restrict_extSheafOf_iso` composed with part
(3)(a) of [Stacks, Tag 0A6H] in the form `AlgebraicGeometry.AffineExt.cohomologySheafIsoTilde`,
fed to `Stacks.Duality.nonempty_stalk_iso_extendScalars_of_affineModel`. -/
theorem nonempty_stalk_extSheafOf_iso_extendScalars (F : X.Modules)
    (K : DerivedCategory X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (M : ModuleCat.{u} Γ(X, U)) (ω : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hM : Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj F ≅
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj M))
    (hω : Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω))
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj M))
    (hplus : (DerivedCategory.TStructure.t).plus ω) (i : ℤ) :
    Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (extSheafOf F K i) ≅
      (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) (-i)).obj
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := Γ(X, U))).hom.obj
            (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj M),
              ω)))) := by
  obtain ⟨eT⟩ := nonempty_restrict_extSheafOf_iso F K hU M ω hM hω i
  refine nonempty_stalk_iso_extendScalars_of_affineModel hU x hx (extSheafOf F K i) _ ⟨?_⟩
  have eB : AlgebraicGeometry.AffineExt.cohomologySheaf Γ(X, U)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj M) ω (-i) ≅
      (tilde.functor Γ(X, U)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) (-i)).obj
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := Γ(X, U))).hom.obj
            (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj M),
              ω))) :=
    AlgebraicGeometry.AffineExt.cohomologySheafIsoTilde Γ(X, U)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj M) ω hpc hplus (-i)
  exact eT ≪≫ (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso eB

end Stacks.Duality

end
