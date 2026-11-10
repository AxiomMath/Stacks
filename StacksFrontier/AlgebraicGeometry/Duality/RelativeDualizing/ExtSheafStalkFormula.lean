module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafDepthDimension
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.StalkFunctorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Ext sheaves of a dualizing complex and its normalized derived stalks

For an `𝒪_X`-module `F` and an object `K` of `D(𝒪_X)` this file defines the Ext sheaves
`𝓔ⁱ = 𝓔xt^{-i}_{𝒪_X}(F, K)` of [Stacks, Tag 0ECM]. For a dualizing complex `K` on a locally
Noetherian scheme `X` it produces, at every point `x`, the datum that [Stacks, Tag 0AWF] attaches
to `K`: a complex `ω` over `𝒪_{X,x}` which is a *normalized* dualizing complex and which is the
derived stalk of a representative of `K` shifted by `-δ(x)`, for
`δ = Stacks.Duality.associatedShiftFunction K`.

## Main definitions

* `Stacks.Duality.extSheafOf`: the Ext sheaf `𝓔xt^{-i}_{𝒪_X}(F, K)`, the `(-i)`-th cohomology
  sheaf of the derived internal Hom from `F` to `K` ([Stacks, Tag 0BQP]).

## Main results

* `Stacks.Duality.nonempty_stalk_iso_extendScalars_of_affineModel`: if the restriction of `G` to
  an affine open `U` is the sheaf associated to a `Γ(X, U)`-module `N`, then the stalk of `G` at
  `x ∈ U` is `𝒪_{X,x} ⊗_{Γ(X,U)} N`.
* `Stacks.Duality.exists_normalized_shifted_derivedStalk`: the `ω`-datum of
  [Stacks, Tag 0AWF] at a point, for the shift function of the dualizing complex itself.
* `Stacks.Duality.isStalkwiseDualExt_extSheafOf`: the Ext sheaves of a dualizing complex satisfy
  `Stacks.Duality.IsStalkwiseDualExt` for its shift function, given the stalk formula of
  [Stacks, Tag 0A6H].

## References

* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
* [Stacks Project, Tag 0AX1](https://stacks.math.columbia.edu/tag/0AX1)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

section ExtSheaf

-- Standard model only: `Stacks.Duality.associatedShiftFunction`,
--   `Dualizing.IsNormalizedDualizingComplex`.
attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **The Ext sheaves `𝓔ⁱ = 𝓔xt^{-i}_{𝒪_X}(F, K)` of [Stacks, Tag 0ECM].** For a sheaf of
`𝒪_X`-modules `F` and an object `K` of `D(𝒪_X)`, this is the `(-i)`-th cohomology sheaf of the
derived internal Hom out of `F`, placed in degree `0`.

This is `Stacks.SheafOfModules.derivedSheafExt` ([Stacks, Tag 0BQP]) at the single complex on `F`
and at degree `-i`; the sign is the source's, which indexes the family by `𝓔xt^{-i}`. -/
@[ega "0 12.3.1" "special case", sga "4 V 6.0" "6.0.1, special case"]
def extSheafOf (F : X.Modules) (K : DerivedCategory X.Modules) (i : ℤ) : X.Modules :=
  Stacks.SheafOfModules.derivedSheafExt X.sheaf
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) K (-i)

end ExtSheaf

section AffineStalk

variable {X : Scheme.{u}}

/-- **The stalk of a sheaf with a known affine model is the base change of that model.** If `G`
restricted to an affine open `U` is the `U`-pullback of `N~` for an `Γ(X, U)`-module `N`, then the
stalk of `G` at `x ∈ U` is `𝒪_{X,x} ⊗_{Γ(X,U)} N`. -/
theorem nonempty_stalk_iso_extendScalars_of_affineModel
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (G : X.Modules) (N : ModuleCat.{u} Γ(X, U))
    (hG : Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj G ≅
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj N)) :
    Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj G ≅
      (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx)).obj N) := by
  obtain ⟨e⟩ := hG
  let S : U.toScheme.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
    modulesStalkFunctor (⟨x, hx⟩ : U.toScheme) ⋙
      ModuleCat.restrictScalars.{u} (affineStalkMap x hx).hom
  exact ⟨((schemeStalkModuleFunctorIso x).app G).symm ≪≫
    ((affineRestrictStalkNatIso x hx).app G).symm ≪≫ S.mapIso e ≪≫
      (affineStalkNatIso hU x hx).app N⟩

end AffineStalk

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

attribute [local instance] HasDerivedCategory.standard

/-- **The `ω`-datum of [Stacks, Tag 0AWF] at a point.** Let `K` be a dualizing complex on a
locally Noetherian scheme `X` and let `δ = Stacks.Duality.associatedShiftFunction K` be its shift
function. At every `x : X` there is a complex `ω` over `𝒪_{X,x}` which is a normalized dualizing
complex and which is the derived stalk at `x` of a representative of `K`, shifted by `-δ(x)`. -/
theorem exists_normalized_shifted_derivedStalk {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) :
    ∃ ω : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)),
      Dualizing.IsNormalizedDualizingComplex ω ∧
        ∃ C : CochainComplex X.Modules ℤ, Nonempty (DerivedCategory.Q.obj C ≅ K) ∧
          Nonempty (ω ≅ (derivedStalkOfComplex x C)⟦-associatedShiftFunction K x⟧) :=
  ⟨(derivedStalkOfComplex x (DerivedCategory.Q.objPreimage K))⟦
      -associatedShiftFunction K x⟧,
    ((isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hK).2.1 x
      (DerivedCategory.Q.objPreimage K) ⟨DerivedCategory.Q.objObjPreimageIso K⟩
      (associatedShiftFunction K x)).mpr rfl,
    DerivedCategory.Q.objPreimage K, ⟨DerivedCategory.Q.objObjPreimageIso K⟩, ⟨Iso.refl _⟩⟩

section Stalkwise

-- Standard model only: `Stacks.Duality.IsStalkwiseDualExt`,
--   `Stacks.Duality.associatedShiftFunction`.
attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **The bundle `Stacks.Duality.IsStalkwiseDualExt` for the actual Ext sheaves, given the stalk
formula.** Let `K` be a dualizing complex on a locally Noetherian scheme `X`, with shift function
`δ = Stacks.Duality.associatedShiftFunction K`, and let `ω` be the derived stalk at `x` of the
canonical representative of `K`, shifted by `-δ(x)`. If for every `x` and `i` the stalk of
`𝓔ⁱ = 𝓔xt^{-i}(F, K)` at `x` is `Ext^{δ(x) - i}_{𝒪_{X,x}}(F_x, ω)` (the stalk reading of
[Stacks, Tag 0A6H], the hypothesis `hstalk`), then `IsStalkwiseDualExt F K δ 𝓔` holds. -/
theorem isStalkwiseDualExt_extSheafOf (F : X.Modules)
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (hstalk : ∀ (x : X) (i : ℤ),
      Nonempty ((extSheafOf F K i).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
        Dualizing.moduleExtInto (F.presheaf.stalk x)
          ((derivedStalkOfComplex x
            (DerivedCategory.Q.objPreimage K))⟦-associatedShiftFunction K x⟧)
          (associatedShiftFunction K x - i))) :
    IsStalkwiseDualExt F K (associatedShiftFunction K) (extSheafOf F K) := by
  refine ⟨hK, fun x => ?_⟩
  refine ⟨(derivedStalkOfComplex x (DerivedCategory.Q.objPreimage K))⟦
      -associatedShiftFunction K x⟧, ?_,
    ⟨DerivedCategory.Q.objPreimage K, ⟨DerivedCategory.Q.objObjPreimageIso K⟩, ⟨Iso.refl _⟩⟩,
    fun i => hstalk x i⟩
  exact ((isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hK).2.1 x
    (DerivedCategory.Q.objPreimage K) ⟨DerivedCategory.Q.objObjPreimageIso K⟩
    (associatedShiftFunction K x)).mpr rfl

end Stalkwise

end Stacks.Duality

end
