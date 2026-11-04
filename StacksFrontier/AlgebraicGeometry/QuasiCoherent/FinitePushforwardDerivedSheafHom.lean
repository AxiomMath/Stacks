module

public import
  StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FiniteMorphism
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.DerivedQuasiCoherenceOverPushforwardRing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sheaf Hom out of the direct image of the structure sheaf of a finite morphism

[Stacks, Tag 0AX2] says, for a finite pseudo-coherent morphism of schemes `f : Y ⟶ X`, that
`R𝓗om_{𝒪_X}(f_* 𝒪_Y, -)` maps `D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(f_* 𝒪_Y)`, and that over a
quasi-compact quasi-separated `X` it agrees with the right adjoint of pushforward followed by
the affine derived direct-image equivalence.  This file proves the first assertion.

## Main results

* `AlgebraicGeometry.derivedCategoryBPlus_derivedSheafHom_of_isPseudoCoherent`: on any scheme
  `Z`, for `E` pseudo-coherent *and cohomologically bounded above* and `F` in `D⁺_QCoh(𝒪_Z)`, the
  derived internal Hom `R𝓗om_{𝒪_Z}(E, F)` lies in `D⁺_QCoh(𝒪_Z)`.
* `AlgebraicGeometry.derivedCategoryBPlus_derivedSheafHom_pushforwardStructureSheaf`: for `f`
  finite and pseudo-coherent, `R𝓗om_{𝒪_X}(f_* 𝒪_Y, -)` carries `D⁺_QCoh(𝒪_X)` into
  `D⁺_QCoh(𝒪_X)`.
* `AlgebraicGeometry.derivedCategoryBPlus_derivedSheafHom_of_pseudoCoherent`: a functor
  `D(𝒪_X) ⥤ D(f_* 𝒪_Y)` whose scalar restriction is the derived internal Hom carries
  `D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(f_* 𝒪_Y)`; this is the preservation clause of [Stacks, Tag 0AX2].

## Implementation notes

The lower bound comes from `Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom`, the
boundedness clause of [Stacks, Tag 0D0C], which holds on any ringed space once the *first*
argument is bounded above; hence the `DerivedCategoryB.IsBoundedAbove` hypothesis of
`AlgebraicGeometry.derivedCategoryBPlus_derivedSheafHom_of_isPseudoCoherent`.

The functor `D(𝒪_X) ⥤ D(f_* 𝒪_Y)` of the last result is not constructed here; it is taken as
given together with the isomorphism identifying its composite with restriction of scalars as the
derived internal Hom over `𝒪_X`, which is [Stacks, Tag 0BV1].

`HasDerivedCategory.standard` is a local instance of priority `10000`, as
`StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard` requires of its
importers; the model-generic results of
`StacksFrontier.AlgebraicGeometry.QuasiCoherent.DerivedQuasiCoherenceOverPushforwardRing` are used
here at the standard model.

## References

* [Stacks Project, Tag 0AX2](https://stacks.math.columbia.edu/tag/0AX2)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0AVX](https://stacks.math.columbia.edu/tag/0AVX)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
* [Stacks Project, Tag 0BV1](https://stacks.math.columbia.edu/tag/0BV1)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.DerivedAffinePushforward
open Stacks.SheafOfModules (StructureSheafModules)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- Let `Z` be a scheme, let `E` be an object of `D(𝒪_Z)` which is pseudo-coherent and
cohomologically bounded above, and let `F` lie in `D⁺_QCoh(𝒪_Z)`.  Then `R𝓗om_{𝒪_Z}(E, F)` lies
in `D⁺_QCoh(𝒪_Z)`. -/
@[stacks 0A6H "part (1) with the lower bound, on an arbitrary scheme, for a cohomologically \
bounded-above pseudo-coherent first argument"]
theorem derivedCategoryBPlus_derivedSheafHom_of_isPseudoCoherent (Z : Scheme.{u})
    (E F : DerivedCategory (StructureSheafModules Z.sheaf))
    (hE : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace) E)
    (hE' : DerivedCategoryB.IsBoundedAbove E)
    (hF : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryBPlus (SheafOfModules.isQuasicoherent Z.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op E)).obj F) :=
  ⟨Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom Z.sheaf E F hE' hF.1,
    derivedCategoryB_derivedSheafHom_of_isPseudoCoherent Z E F hE hF⟩

variable {Y X : Scheme.{u}}

/-- For a finite pseudo-coherent morphism `f : Y ⟶ X`, the derived internal Hom
`R𝓗om_{𝒪_X}(f_* 𝒪_Y, -)` carries `D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(𝒪_X)`. -/
@[stacks 0AX2 "the preservation clause with quasi-coherence read over 𝒪_X rather than over \
f_* 𝒪_Y; the commutative-diagram clause is not proved"]
theorem derivedCategoryBPlus_derivedSheafHom_pushforwardStructureSheaf (f : Y ⟶ X) [IsFinite f]
    (hf : PseudoCoherent f) (K : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryBPlus (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op ((DerivedCategory.singleFunctor X.Modules 0).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))))).obj K) := by
  have hE' : DerivedCategoryB.IsBoundedAbove
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))) :=
    ⟨0, (DerivedCategory.isLE_iff _ 0).1 inferInstance⟩
  exact derivedCategoryBPlus_derivedSheafHom_of_isPseudoCoherent X _ K
    ((pseudoCoherent_iff_isPseudoCoherent_pushforward_unit f).1 hf) hE' hK

/-- Let `f : Y ⟶ X` be a finite pseudo-coherent morphism of schemes and let
`derivedSheafHom : D(𝒪_X) ⥤ D(f_* 𝒪_Y)` be a functor whose composite with restriction of scalars
along `𝒪_X ⟶ f_* 𝒪_Y` is the derived internal Hom `R𝓗om_{𝒪_X}(f_* 𝒪_Y, -)`, which is what
[Stacks, Tag 0BV1] says of the derived sheaf-Hom functor.  Then `derivedSheafHom` maps
`D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(f_* 𝒪_Y)`. -/
@[stacks 0AX2 "the preservation clause, for a derived sheaf-Hom functor given together with its \
identification of Tag 0BV1; the commutative-diagram clause is not proved"]
theorem derivedCategoryBPlus_derivedSheafHom_of_pseudoCoherent (f : Y ⟶ X) [IsFinite f]
    (hf : PseudoCoherent f)
    (derivedSheafHom : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base Y.ringCatSheaf)))
    (hsplit : derivedSheafHom ⋙ (scalarRestriction f).mapDerivedCategory ≅
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op ((DerivedCategory.singleFunctor X.Modules 0).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)))))
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent (pushforwardRing f.base Y.ringCatSheaf))
      (derivedSheafHom.obj K) := by
  have h := derivedCategoryBPlus_derivedSheafHom_pushforwardStructureSheaf f hf K hK
  refine derivedCategoryBPlus_of_derivedCategoryBPlus_scalarRestriction f _ ?_
  refine ⟨DerivedCategoryB.isBoundedBelow_of_iso (hsplit.app K).symm h.1, fun n ↦ ?_⟩
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso (hsplit.app K).symm) (h.2 n)

end AlgebraicGeometry

end
