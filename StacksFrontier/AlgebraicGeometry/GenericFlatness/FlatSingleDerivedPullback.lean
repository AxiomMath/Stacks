module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatPullback

/-!
# Derived pullback of a flat module placed in degree zero

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `F` be a flat `𝒪_Y`-module. Then `F`,
viewed as a complex concentrated in degree `0`, is K-flat, so the canonical comparison from the
derived pullback to the degreewise pullback is invertible on it and `Lf^*(F[0])` is the ordinary
pullback `f^*F` placed in degree `0`. Since `f^*F` is again flat, the class of objects of the
derived category isomorphic to a flat module in degree `0` is preserved by `Lf^*`.

For a surjective morphism of schemes of finite presentation and an object of `D_QCoh(𝒪_S)` with
no positive cohomology this is one of the two implications of the equivalence of Stacks 0H89; the
equivalence itself is `AlgebraicGeometry.exists_isFlat_iff_exists_isFlat_derivedPullback` in
`StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullbackConverse`.

## Main results

* `Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso` — the isomorphism
  `Lf^*(F[0]) ≅ (f^*F)[0]` for a flat `𝒪_Y`-module `F`.
* `Stacks.Cohomology.FlatSingleDerivedPullback.exists_isFlat_derivedPullback` — the derived
  pullback of an object isomorphic to a flat module in degree `0` is again isomorphic to a flat
  module in degree `0`, for an arbitrary morphism of ringed spaces.
* `AlgebraicGeometry.exists_isFlat_derivedPullback_of_exists_isFlat` — the implication (1) ⇒ (2)
  of Stacks 0H89, at the hypotheses of that tag.

## Implementation notes

The comparison `Lf^* ⟶ f^*` is invertible on K-flat complexes by Stacks 06YJ, and a flat module
in a single degree is K-flat by Stacks 06YQ. Those two inputs are
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` and
`Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat`; the latter produces K-flatness at
the `CochainComplex.singleFunctor` spelling of the single complex while the former wants the
`HomotopyCategory.quotient` spelling, so the invertibility is restated once at the
`HomotopyCategory.singleFunctor` spelling that the comparison's component needs. That restatement
is the only step of `derivedPullbackSingleIso` that is not a Mathlib identity between the single
functors and the localization functors.

*The model of the derived categories.* The statements here are at `HasDerivedCategory.standard`,
because the Stacks 06YJ comparison is, and `HasDerivedCategory` carries the localized category as
data, so a result at one model does not transport to another. Consequently the categories of
modules are spelled `SheafOfModules (structureSheafRing S.toRingedSpace)`
rather than `S.Modules`, and the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` is deliberately not imported: the two
spellings are the same type, so importing it would put two instances at different morphism
universes in range of one goal. For the same reason `D_QCoh(𝒪_S)` appears as the condition that
every cohomology sheaf be quasi-coherent rather than as the full subcategory
`Stacks.Duality.quasiCoherentDerivedCategory`, which is fixed at the locally small model.

Only the implication (1) ⇒ (2) of Stacks 0H89 is proved here; the converse, which is the
substance of that tag, is `exists_isFlat_of_exists_isFlat_derivedPullback` in the namespace
`Stacks.Cohomology.FlatSingleDerivedPullbackConverse`, and the tag is registered on the
equivalence. Neither the surjectivity of `f`, nor its finite presentation, nor the
quasi-coherence and vanishing hypotheses on `M` are used in the direction proved here; they are
carried in `AlgebraicGeometry.exists_isFlat_derivedPullback_of_exists_isFlat` so that it states
the implication at the hypotheses of the tag, while `exists_isFlat_derivedPullback` records the
same conclusion for an arbitrary morphism of ringed spaces.

## References

* [The Stacks Project, Lemma 37.54.3 (0H89)](https://stacks.math.columbia.edu/tag/0H89)
* [The Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [The Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [The Stacks Project, Tag 0H97](https://stacks.math.columbia.edu/tag/0H97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Cohomology.FlatSingleDerivedPullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The derived pullback of a flat module placed in degree zero.** For `F` a flat
`𝒪_Y`-module, `Lf^*(F[0])` is the degreewise pullback `f^*F` placed in degree `0`: the complex
`F[0]` is K-flat, so the comparison `Lf^* ⟶ f^*` is invertible on it. -/
def derivedPullbackSingleIso (F : SheafOfModules.{u} (structureSheafRing Y))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((modulePullback f).obj F) := by
  haveI : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F)) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf F hF 0)
  exact (derivedPullback f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (structureSheafRing Y)) 0).app F) ≪≫
    asIso ((derivedPullbackComparison f).app _) ≪≫
    DerivedCategory.Qh.mapIso (((modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app _) ≪≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback f) (ComplexShape.up ℤ) 0).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) 0).app
      ((modulePullback f).obj F)).symm

/-- **The derived pullback preserves the flat modules placed in degree zero.** If an object of
`D(𝒪_Y)` is isomorphic to a flat `𝒪_Y`-module in degree `0`, then its derived pullback along an
arbitrary morphism of ringed spaces is isomorphic to a flat `𝒪_X`-module in degree `0`, namely
to the degreewise pullback of the given one. -/
theorem exists_isFlat_derivedPullback
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hE : ∃ F : SheafOfModules.{u} (structureSheafRing Y),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F ∧
        Nonempty (E ≅
          (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F)) :
    ∃ G : SheafOfModules.{u} (structureSheafRing X),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) G ∧
        Nonempty ((derivedPullback f).obj E ≅
          (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := hE
  exact ⟨(modulePullback f).obj F, Stacks.SheafOfModules.modulePullback_isFlat f F hF,
    ⟨(derivedPullback f).mapIso e ≪≫ derivedPullbackSingleIso f F hF⟩⟩

end Stacks.Cohomology.FlatSingleDerivedPullback

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks 0H89, the implication (1) ⇒ (2).** Let `f : X ⟶ S` be a surjective morphism of
finite presentation and let `M` be an object of `D_QCoh(𝒪_S)` with `H^i(M) = 0` for `i > 0`. If
`M` is isomorphic to a flat `𝒪_S`-module placed in degree `0`, then `Lf^*M` is isomorphic to a
flat `𝒪_X`-module placed in degree `0`. -/
theorem exists_isFlat_derivedPullback_of_exists_isFlat [Surjective f]
    (_hf : FinitePresentation f)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (_hQCoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i).obj M).IsQuasicoherent)
    (_hM : ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i).obj M))
    (h₁ : ∃ F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      SheafOfModules.IsFlat.{u, u, u, u} (O := S.toRingedSpace.sheaf) F ∧
        Nonempty (M ≅ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) 0).obj F)) :
    ∃ G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace),
      SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) G ∧
        Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj M ≅
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj G) :=
  Stacks.Cohomology.FlatSingleDerivedPullback.exists_isFlat_derivedPullback
    f.toLRSHom.toShHom M h₁

end AlgebraicGeometry

end
