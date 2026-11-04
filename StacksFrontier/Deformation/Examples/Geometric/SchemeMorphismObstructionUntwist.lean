module

public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSequenceTerms

/-!
# The sixth term of the sequence of Stacks 0E3V at the rank-one coefficient module

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`. The tangent spaces of the deformation
categories of `X`, `Y` and `f` are read at a finite-dimensional coefficient module `M`, the
square-zero base being `k ⊕ M`, and the obstruction to deforming `f` along a pair of
deformations over that base lies in the twisted group
`Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X ⊗_k M)`
(`Deformation.Examples.schemeMorphismObstructionExtTwisted`). The source's sequence of
[Stacks Project, Tag 0E3V] is the case of the rank-one module, whose sixth term is the untwisted
`Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X)` (`Deformation.Examples.schemeMorphismObstructionExt`). This file
builds the identification of the two, as `k`-vector spaces.

The rank-one coefficient module of the library's tangent spaces is
`FGModuleCat.of k (ULift k)` (it is the module at which
`Deformation.associatedTangentSpaceModuleStructure_carrier` identifies the tangent module with
the tangent space of Tag 06I9), so that is the module the identification is stated at.

## Main definitions

* `Deformation.Examples.schemeMorphismCoefficientSheafRankOneIso`: the coefficient sheaf
  `𝒪_X ⊗_k k` at the rank-one module is the structure sheaf `𝒪_X`.
* `Deformation.Examples.schemeMorphismObstructionExtRankOneEquiv`: the twisted sixth term at the
  rank-one module is the source's sixth term `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X)`, as a `k`-linear
  equivalence for the two `k`-vector space structures
  `Deformation.Examples.schemeMorphismObstructionExtTwistedModule` and
  `Deformation.Examples.schemeMorphismObstructionExtModule`.

## Implementation notes

The coefficient sheaf is the pullback along the structure morphism `f ≫ pY` of `X` of the
quasi-coherent sheaf `M^~` on the spectrum of `k`. At `M = ULift k` the module `M` is `k` itself
up to `ULift.moduleEquiv`, `k^~` is the structure sheaf of `Spec k` (`AlgebraicGeometry.tildeSelf`)
and the pullback of a structure sheaf is the structure sheaf
(`Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso`).

Both `Ext¹` groups are groups of morphisms of the derived category of `𝒪_X`-modules, and their
`k`-vector space structures are the ones of the `k`-linear structure that `f ≫ pY` induces on
that derived category; postcomposition with an isomorphism is `k`-linear there
(`CategoryTheory.Linear.homCongr`), which is the equivalence.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-- **The coefficient sheaf at the rank-one module is the structure sheaf.** The sheaf
`𝒪_X ⊗_k M` of `Deformation.Examples.schemeMorphismCoefficientSheaf` at
`M = FGModuleCat.of k (ULift k)`, the rank-one coefficient module of the tangent spaces, is `𝒪_X`:
`ULift k` is `k`, `k^~` is the structure sheaf of `Spec k`, and its pullback along the structure
morphism of `X` is the structure sheaf of `X`. -/
def schemeMorphismCoefficientSheafRankOneIso :
    schemeMorphismCoefficientSheaf f pY (FGModuleCat.of k (ULift.{u} k)) ≅
      SheafOfModules.unit (structureSheafRing X.toRingedSpace) :=
  (Scheme.Modules.pullback (f ≫ pY)).mapIso
      ((tilde.functor (CommRingCat.of k)).mapIso
          (ULift.moduleEquiv (R := k) (M := k)).toModuleIso ≪≫ tildeSelf) ≪≫
    Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso (f ≫ pY)

/-- **Stacks 0E3V, the sixth term at the rank-one coefficient module.** The twisted group
`Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X ⊗_k M)` at the rank-one module `M = FGModuleCat.of k (ULift k)` is
the source's sixth term `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X)`, as `k`-vector spaces: the equivalence
is postcomposition with the shifted single complex of
`Deformation.Examples.schemeMorphismCoefficientSheafRankOneIso`, which is `k`-linear for the
`k`-linear structure that the structure morphism `f ≫ pY` of `X` induces on the derived category
of `𝒪_X`-modules — the structure both `k`-vector spaces carry. -/
def schemeMorphismObstructionExtRankOneEquiv :
    letI := schemeMorphismObstructionExtTwistedModule f pY (FGModuleCat.of k (ULift.{u} k))
    letI := schemeMorphismObstructionExtModule f pY
    schemeMorphismObstructionExtTwisted f pY (FGModuleCat.of k (ULift.{u} k)) ≃ₗ[k]
      schemeMorphismObstructionExt f pY :=
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
  Linear.homCongr k (Iso.refl _)
    ((shiftFunctor _ (1 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
      (schemeMorphismCoefficientSheafRankOneIso f pY)))

/-- The rank-one identification of the sixth term is postcomposition with the shifted single
complex of the identification of the coefficient sheaf with `𝒪_X`. -/
theorem schemeMorphismObstructionExtRankOneEquiv_apply
    (e : schemeMorphismObstructionExtTwisted f pY (FGModuleCat.of k (ULift.{u} k))) :
    schemeMorphismObstructionExtRankOneEquiv f pY e =
      e ≫ ((DerivedCategory.singleFunctor _ 0).map
        (schemeMorphismCoefficientSheafRankOneIso f pY).hom)⟦(1 : ℤ)⟧' := by
  simp [schemeMorphismObstructionExtRankOneEquiv, Linear.homCongr]

end Deformation.Examples

end
