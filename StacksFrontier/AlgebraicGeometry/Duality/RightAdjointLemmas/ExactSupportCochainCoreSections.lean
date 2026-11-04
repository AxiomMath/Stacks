module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedUnitSource
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportUnitSourceLeftAdjoint

/-!
# The cochain-level core of Stacks 0E2I at the structure sheaf, from one identity of sections

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that `i_*` is left adjoint to
sheaf Hom with exact support `ℰom(𝒪_Z, -)` ([Stacks, Tag 0A75]).

`…ClosedQuotientMorphismOfRingedSpaces.derivedCore_of_cochainCore` reduces the derived identity
of [Stacks, Tag 0E2I] at the source `𝒪_Z[0]` to an identity of morphisms of cochain complexes.
**This file reduces that cochain identity further, to a single identity of sections of sheaves**:
no complex, no cochain and no lifted adjunction appears in the hypothesis any more.

## Main definitions

* `…ClosedQuotientMorphismOfRingedSpaces.SheafHomPushforwardSectionsCore`: for a sheaf of
  `𝒪_X`-modules `F`, an open `U ⊆ X` and a morphism
  `z : 𝒪_Z|_{i^{-1}U} ⟶ ℰom(𝒪_Z, F)|_{i^{-1}U}` on the slice site, the morphism
  `(i_* 𝒪_Z)|_U ⟶ F|_U` that the underived [Stacks, Tag 0E2I] identification attaches to `z`
  takes the unit section of `i_* 𝒪_Z` to the value at the unit section of the trace of
  [Stacks, Tag 0A75] on `z` evaluated at the unit section of `𝒪_Z`.

  This is the underived core
  `…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_comp_unitIso_comp_counit`
  read on sections, with each of the two trivialisations of `ℰom(𝒪, -)` spelled as evaluation at
  the unit section.

## Main results

* `…ClosedQuotientMorphismOfRingedSpaces.cochainCore_of_sectionsCore`: **the identity of sections
  gives the cochain-level identity** that `…derivedCore_of_cochainCore` consumes, for any
  morphism of complexes `cu : 𝒪_X[0] ⟶ i_*(𝒪_Z[0])` whose degree-zero component is the unit
  `𝒪_X ⟶ i_* 𝒪_Z`.

## Implementation notes

The reduction is exactly the two sections computations the cochain identity is made of, and both
are definitional once the right form is written down:

* on the `Z` side, sections over `U` of a pushforward are sections over `i^{-1}U`, and the
  degreewise component of the counit of the adjunction of [Stacks, Tag 0A75] lifted to complexes
  (`CategoryTheory.Adjunction.mapHomologicalComplexAdjunction`) is the underived counit at the
  degreewise term — so the left-hand side is the underived counit applied to evaluation at the
  unit section over `i^{-1}U`, by `show` alone;
* on the `X` side, evaluation at the unit section is
  `AlgebraicGeometry.RingedSite.structureSheafHomEvaluation_apply`, the map of internal Hom
  complexes is `AlgebraicGeometry.RingedSite.applyHomSection_homMap`, and the cochain component
  of the complex-level [Stacks, Tag 0E2I] identification is
  `…ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomComplexIso_sections_v`, which
  produces the inverse of `…PushforwardInternalHom.sliceEquiv` — the morphism of restrictions the
  hypothesis is stated about.

Only the degree-zero component of `cu` enters: the source of the identity is the structure sheaf
complex, whose terms vanish away from degree zero, so the only cochain component that survives is
the one at `(0, n)`.

The statement is made with no scheme in it, for the same reason as `…derivedCore_of_cochainCore`:
at an effective Cartier divisor the goal mixes the spellings `X.sheaf` and
`(closedQuotient D).X.sheaf` of one sheaf of rings, which makes it ill-typed at `implicit`
transparency and so beyond `rw`.  Here `AlgebraicGeometry.SheafedSpace.sheaf` and
`CategoryTheory.sheafCompose` are additionally made `instance_reducible`, which identifies the
spelling `structureSheafRing X` with `structureSheaf X.sheaf` for instance search; without it even
`CategoryTheory.Iso.inv_comp_eq` fails to find its pattern in the goal.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (ringedSite)

universe u

attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
  CategoryTheory.sheafCompose

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **The underived core of [Stacks, Tag 0E2I] at the source `𝒪_Z`, read on sections.**

A section over `U ⊆ X` of `ℰom_{𝒪_X}(i_* 𝒪_Z, F)` is a morphism `(i_* 𝒪_Z)|_U ⟶ F|_U` on the
slice site, and the underived identification of [Stacks, Tag 0E2I] presents it as a morphism
`z : 𝒪_Z|_{i^{-1}U} ⟶ ℰom(𝒪_Z, F)|_{i^{-1}U}` through
`…PushforwardInternalHom.sliceEquiv`.  This says that the two ways of extracting a section of
`F` over `U` from `z` agree: evaluate the morphism `(i_* 𝒪_Z)|_U ⟶ F|_U` at the unit section of
`i_* 𝒪_Z`, or evaluate `z` at the unit section of `𝒪_Z` over `i^{-1}U` and apply the trace of
[Stacks, Tag 0A75].

This is
`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_comp_unitIso_comp_counit` with
both trivialisations of `ℰom(𝒪, -)` spelled as evaluation at the unit section. -/
def SheafHomPushforwardSectionsCore : Prop :=
  ∀ (F : SheafOfModules.{u} (structureSheafRing S.X)) (U : Opens S.X)
    (z : ((RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)).X 0).over
        (S.openPreimage U) ⟶
      (S.sheafHomExactSupport.obj F).over (S.openPreimage U)),
    ((S.pushforwardInternalHom.sliceEquiv
            ((RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)).X 0) F U).symm
          z).val.app (op (Over.mk (𝟙 U)))
        ((structureSheafModuleHom S.i).val.app (op U)
          (RingedSite.structureSheafOne (ringedSite S.X.sheaf) U)) =
      (S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F).val.app (op U)
        (z.val.app (op (Over.mk (𝟙 (S.openPreimage U))))
          (RingedSite.structureSheafOne (ringedSite S.Z.sheaf) (S.openPreimage U)))

/-- **The identity of sections gives the cochain-level core of [Stacks, Tag 0E2I] at the source
`𝒪_Z[0]`**, in the form that
`…ClosedQuotientMorphismOfRingedSpaces.derivedCore_of_cochainCore` consumes: for every cochain
complex `I` of `𝒪_X`-modules, the complex-level identification of [Stacks, Tag 0E2I] at the
source `𝒪_Z[0]`, read backwards and followed by the pushforward of evaluation at the unit section
on `Z` and by the degreewise trace of [Stacks, Tag 0A75], is restriction along `cu` followed by
evaluation at the unit section on `X`.

Only the degree-zero component of `cu` is used, through the hypothesis that it is the unit
`𝒪_X ⟶ i_* 𝒪_Z`. -/
theorem cochainCore_of_sectionsCore (hs : S.SheafHomPushforwardSectionsCore)
    (cu : RingedSite.structureSheafComplex (ringedSite S.X.sheaf) ⟶
      ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)))
    (hcu : cu.f 0 = structureSheafModuleHom S.i)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    (S.pushforwardSheafHomComplex.iso
            (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) I).inv ≫
          ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
                ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
            (Adjunction.mapHomologicalComplexAdjunction
              S.modulePushforwardSheafHomExactSupportAdjunction
                (ComplexShape.up ℤ)).counit.app I =
        sheafHomComplexHomMap S.X cu (𝟙 I) ≫
          RingedSite.structureSheafHomEvaluation (ringedSite S.X.sheaf) I := by
  rw [Iso.inv_comp_eq]
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun ⟨U⟩ => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  show (S.modulePushforwardSheafHomExactSupportAdjunction.counit.app (I.X n)).val.app (op U)
        (RingedSite.applyHomSection (ringedSite S.Z.sheaf)
          (RingedSite.sheafHomComplex (ringedSite S.Z.sheaf)
            (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
          (S.openPreimage U) n 0 n (zero_add n) s
          (RingedSite.structureSheafOne (ringedSite S.Z.sheaf) (S.openPreimage U))) =
      RingedSite.applyHomSection (ringedSite S.X.sheaf)
        (RingedSite.sheafHomComplex (ringedSite S.X.sheaf)
          (RingedSite.structureSheafComplex (ringedSite S.X.sheaf)) I)
        U n 0 n (zero_add n)
        (((RingedSite.homMap (ringedSite S.X.sheaf) cu (𝟙 I)).f n).val.app (op U)
          ((((pushforwardSheafHomComplexIso S.pushforwardInternalHom
            (Stacks.SheafOfModules.sheafHomComplexComparison _)
            (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) I)).hom.f n).val.app
              (op U) s))
        (RingedSite.structureSheafOne (ringedSite S.X.sheaf) U)
  refine Eq.trans ?_
    (RingedSite.applyHomSection_homMap (ringedSite S.X.sheaf) cu (𝟙 I) U n 0 n
      (zero_add n) _ _).symm
  rw [hcu]
  have hv := pushforwardSheafHomComplexIso_sections_v S.pushforwardInternalHom
    (Stacks.SheafOfModules.sheafHomComplexComparison _)
    (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) I U n s 0 n (zero_add n)
  exact ((hs (I.X n) U _).symm).trans
    (congrArg (fun t => t.val.app (op (Over.mk (𝟙 U)))
      ((structureSheafModuleHom S.i).val.app (op U)
        (RingedSite.structureSheafOne (ringedSite S.X.sheaf) U))) hv).symm

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
