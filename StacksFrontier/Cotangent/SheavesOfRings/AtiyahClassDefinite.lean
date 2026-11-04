module

public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahTriangleFirstTerm
import StacksCore.Tactic.StacksAttribute

/-!
# The Atiyah class of a sheaf of modules, as a definite morphism

Let `C` be a site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on it and let
`ℱ` be a sheaf of `ℬ`-modules. [Stacks, Tag 09DI] calls the last arrow

`ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)[1]`

of the distinguished triangle (92.19.0.2) of [Stacks, Tag 09DH] the *Atiyah class* of `ℱ`. This
file defines that arrow, `CategoryTheory.Sheaf.sheafAtiyahClass`, as one definite morphism of
`D(ℬ)`, and proves that it is the last arrow of the displayed distinguished triangle.

## Main definitions

* `Stacks.SimplicialModules.derivedProjectionLowerShriekAugmentationBaseChangeIso`: the isomorphism
  `Lπ_!(Lε^*(ε_* X)) ≅ Lπ_!(X)` of [Stacks, Tag 09D2] for a complex `X` bounded above by `0`, as a
  constructed isomorphism: the explicit composite of the steps of the proof of
  `Stacks.SimplicialModules.nonempty_derivedProjectionLowerShriek_augmentationBaseChange_iso`, at
  the flat resolution `Stacks.SimplicialModules.augmentationFlatResolution`.
* `CategoryTheory.Sheaf.atiyahTriangleFirstTermIso`: the identification of the first term of the
  Atiyah triangle with `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`.
* `CategoryTheory.Sheaf.atiyahTriangleThirdTermIso`: the identification of its third term with `ℱ`.
* `CategoryTheory.Sheaf.sheafAtiyahTriangle`: the triangle of [Stacks, Tag 09DH] as the source
  displays it, with terms `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`, `Lπ_!(P¹_{𝒫/π^{-1}𝒜}(ℱ))` and `ℱ`.
* `CategoryTheory.Sheaf.sheafAtiyahClass`: the Atiyah class of [Stacks, Tag 09DI].

## Main results

* `CategoryTheory.Sheaf.sheafAtiyahTriangle_distinguished`: the displayed triangle is
  distinguished, [Stacks, Tag 09DH].
* `CategoryTheory.Sheaf.sheafAtiyahClass_mem_distinguished`: the Atiyah class is the last arrow of
  that distinguished triangle.

## Implementation notes

The identifications of the outer terms are composites of named isomorphisms: the comparisons
`CategoryTheory.Sheaf.resolutionCoefficientsSingleIso` and
`CategoryTheory.Sheaf.resolutionDifferentialsSingleIso` of the outer terms with an `ε_*(-)`, the
Tag 09D2 step `Stacks.SimplicialModules.derivedProjectionLowerShriekAugmentationBaseChangeIso`, and
the computations `Stacks.SimplicialModules.derivedProjectionLowerShriekRestrictionIso` and
`CategoryTheory.Sheaf.derivedLowerShriekSimplicialDifferentialsIso` of the remaining `Lπ_!` of
Remark 09CY. The Tag 09D2 step is computed on the flat resolution
`Stacks.SimplicialModules.augmentationFlatResolution` of the coefficient complex, as the
module-coefficient computation of Section 09D0,
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplexModules`, is computed on a
fixed resolution.

The site is a small category `C : Type u` with sheaves of rings valued in `CommRingCat.{u}`: a site
in the sense of [Stacks, Tag 00VH] has a *set* of coverings, each object having its identity
covering, so its objects form a set, and its sheaves take values in the same universe of sets. The
two instance arguments are the ones every statement about the functor `Lπ_!` of Remark 09CY
carries: cocontinuity of the projection `π : Δ × C ⥤ C`, which instance search supplies
(`Stacks.SimplicialModules.isCocontinuous_projection`), and the covering-pullback clause
`Stacks.Sites.PreservesCoveringPullbacks` for `π`, which is axiom (3) of [Stacks, Tag 00VH] for the
site `C` transcribed to `Δ × C`.

## References

* [Stacks Project, Tag 09DI](https://stacks.math.columbia.edu/tag/09DI), Definition 92.19.1, the
  Atiyah class.
* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), Equation 92.19.0.2, the
  displayed triangle.
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2), the lemma that removes the
  derived base change along the augmentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.PresheafOfModules.ChangeOfRings (unitMap')
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open AlgebraicGeometry.SheafOfModules (moduleSheaves)

universe u

namespace Stacks.SimplicialModules

section AugmentationBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A : SimplicialObject (Sheaf J CommRingCat.{u})} {O : Sheaf J CommRingCat.{u}}
  (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O)

/-- **A flat resolution of `ε_* X`.** For a complex `X` of sheaves of `π^{-1}O`-modules bounded
above by `0`, a complex of simplicial `A_•`-modules bounded above by `0`, with flat terms, together
with a quasi-isomorphism to `ε_* X` (chosen by
`Stacks.SimplicialModules.exists_augExtendScalars_quasiIso_total`). -/
def augmentationFlatResolution
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0] :
    CochainComplex (SheafOfModules.{u} (augSrcRing J (A := A))) ℤ :=
  (exists_augExtendScalars_quasiIso_total J ε hθ X).choose

/-- The flat resolution is bounded above by `0`. -/
instance augmentationFlatResolution_isStrictlyLE
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0] :
    (augmentationFlatResolution J ε hθ X).IsStrictlyLE 0 :=
  (exists_augExtendScalars_quasiIso_total J ε hθ X).choose_spec.choose

/-- The terms of the flat resolution are flat. -/
theorem augmentationFlatResolution_isFlat
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0]
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := simplicialCommRingSheaf J A) ((augmentationFlatResolution J ε hθ X).X i) :=
  (exists_augExtendScalars_quasiIso_total J ε hθ X).choose_spec.choose_spec.choose i

/-- The quasi-isomorphism from the flat resolution to `ε_* X`. -/
def augmentationFlatResolutionπ
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0] :
    augmentationFlatResolution J ε hθ X ⟶ (augPushforwardC J ε).obj X :=
  (exists_augExtendScalars_quasiIso_total J ε hθ X).choose_spec.choose_spec.choose_spec.choose

/-- The map from the flat resolution to `ε_* X` is a quasi-isomorphism. -/
instance quasiIso_augmentationFlatResolutionπ
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0] :
    QuasiIso (augmentationFlatResolutionπ J ε hθ X) :=
  (exists_augExtendScalars_quasiIso_total J ε hθ X).choose_spec.choose_spec.choose_spec.choose_spec
    |>.1

/-- The column/row conclusion at the flat resolution: the adjoint `ε^* M ⟶ X` of the resolution map
induces a quasi-isomorphism of the total complexes of the Moore double complexes. -/
theorem quasiIso_total_map_augmentationFlatResolution
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0] :
    QuasiIso (HomologicalComplex₂.total.map
      ((mooreModBicomplexFunctor C J (augBaseRing J (O := O))).map
        (((augExtendRestrictAdjC J ε).homEquiv (augmentationFlatResolution J ε hθ X) X).symm
          (augmentationFlatResolutionπ J ε hθ X))) (ComplexShape.up ℤ)) :=
  (exists_augExtendScalars_quasiIso_total J ε hθ X).choose_spec.choose_spec.choose_spec.choose_spec
    |>.2

/-- **[Stacks, Tag 09D2] for a complex bounded above by `0`, as a constructed isomorphism:
`Lπ_!(Lε^*(ε_* X)) ≅ Lπ_!(X)`.** The explicit composite of the steps of
`Stacks.SimplicialModules.nonempty_derivedProjectionLowerShriek_augmentationBaseChange_iso`, at the
flat resolution `Stacks.SimplicialModules.augmentationFlatResolution`: replace `ε_* X` by the
resolution, compute `Lε^*` degreewise there (Tag 06YY), compute `Lπ_!` on both sides by the total
complex of the Moore double complex (Section 09D0), and compare those by the column/row
quasi-isomorphism. -/
def derivedProjectionLowerShriekAugmentationBaseChangeIso
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0] :
    (derivedProjectionLowerShriek C J (augBaseRing J (O := O))).obj
        ((derivedBaseChangeToProjectionRing J ε).obj
          (DerivedCategory.Q.obj ((augPushforwardC J ε).obj X))) ≅
      (derivedProjectionLowerShriek C J (augBaseRing J (O := O))).obj
        (DerivedCategory.Q.obj X) :=
  (derivedProjectionLowerShriek C J (augBaseRing J (O := O))).mapIso
      ((derivedBaseChangeToProjectionRing J ε).mapIso
          (CochainComplex.derivedIsoOfQuasiIso (augmentationFlatResolutionπ J ε hθ X)
            inferInstance).symm ≪≫
        augmentationBaseChangeFlatIso J ε (augmentationFlatResolution J ε hθ X) 0
          (augmentationFlatResolution_isStrictlyLE J ε hθ X)
          (augmentationFlatResolution_isFlat J ε hθ X) ≪≫
        DerivedCategory.Q.mapIso
          ((augmentationBaseChangeComplexIso J ε).app (augmentationFlatResolution J ε hθ X))) ≪≫
    derivedProjectionLowerShriekIsoMooreBicomplexTotalModules C J (augBaseRing J (O := O))
      ((augExtendScalarsC J ε).obj (augmentationFlatResolution J ε hθ X)) ≪≫
    CochainComplex.derivedIsoOfQuasiIso _
      (quasiIso_total_map_augmentationFlatResolution J ε hθ X) ≪≫
    (derivedProjectionLowerShriekIsoMooreBicomplexTotalModules C J
      (augBaseRing J (O := O)) X).symm

end AugmentationBaseChange

end Stacks.SimplicialModules

namespace CategoryTheory.Sheaf

open Stacks.SimplicialModules (projection projectionTopology projectionRing
  derivedProjectionLowerShriek derivedProjectionLowerShriekAugmentationBaseChangeIso)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- **The third term of the Atiyah triangle is `ℱ`**, as a constructed isomorphism. The third term
is the `Lπ_!` of Remark 09D3 of `ε_*(π^{-1}ℱ)`; the derived base change along the augmentation is
dropped by `Stacks.SimplicialModules.derivedProjectionLowerShriekAugmentationBaseChangeIso`
(Tag 09D2, whose hypothesis is discharged for the standard resolution by
`CategoryTheory.Sheaf.quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap`), and
`Lπ_!(π^{-1}ℱ[0]) ≅ ℱ[0]` is `CategoryTheory.Sheaf.resolutionAtiyahTriangleThirdTermIso`. -/
def atiyahTriangleThirdTermIso (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (resolutionAtiyahTriangle J f F).obj₃ ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
          (ComplexShape.up ℤ) 0).obj F) :=
  resolutionAtiyahTriangleThirdTermIso J f F
    ((resolutionLowerShriek J f).mapIso
        (DerivedCategory.Q.mapIso (resolutionCoefficientsSingleIso J f F)) ≪≫
      derivedProjectionLowerShriekAugmentationBaseChangeIso J (resolutionCommAugmentation J f)
        (quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap J f)
        ((HomologicalComplex.single
          (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
          (ComplexShape.up ℤ) 0).obj (projectionCoefficients J (B := B) F)))

/-- **The first term of the Atiyah triangle is `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`**, as a constructed isomorphism.
The first term is the `Lπ_!` of Remark 09D3 of `Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ε_*(π^{-1}ℱ)`, which
`CategoryTheory.Sheaf.resolutionDifferentialsSingleIso` writes as `ε_*` of
`(Ω_{P_•/𝒜} ⊗_{P_•} ℱ)[0]`; the derived base change is dropped by
`Stacks.SimplicialModules.derivedProjectionLowerShriekAugmentationBaseChangeIso` (Tag 09D2), and
`CategoryTheory.Sheaf.derivedLowerShriekSimplicialDifferentialsIso` computes what remains as
`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`. -/
def atiyahTriangleFirstTermIso (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (resolutionAtiyahTriangle J f F).obj₁ ≅
      ((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)) :=
  (resolutionLowerShriek J f).mapIso
      (DerivedCategory.Q.mapIso (resolutionDifferentialsSingleIso J f F)) ≪≫
    derivedProjectionLowerShriekAugmentationBaseChangeIso J (resolutionCommAugmentation J f)
      (quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap J f)
      ((HomologicalComplex.single
        (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
        (ComplexShape.up ℤ) 0).obj (simplicialDifferentialsCoefficients J f F)) ≪≫
    derivedLowerShriekSimplicialDifferentialsIso J f F

/-- **[Stacks, Tag 09DI], Definition 92.19.1: the Atiyah class of a sheaf of modules.** For a
homomorphism `f : 𝒜 ⟶ ℬ` of sheaves of commutative rings on a site and a sheaf of `ℬ`-modules `ℱ`,
the *Atiyah class* of `ℱ` is the morphism

`ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)[1]`

of `D(ℬ)` which is the last arrow of the triangle (92.19.0.2) of [Stacks, Tag 09DH]: the image
under the `Lπ_!` of Remark 09D3 of the short exact sequence of first principal parts of the
standard resolution (Tag 09DG), read through the identifications
`CategoryTheory.Sheaf.atiyahTriangleFirstTermIso` and
`CategoryTheory.Sheaf.atiyahTriangleThirdTermIso` of its outer terms. -/
@[stacks 09DI]
def sheafAtiyahClass (F : SheafOfModules.{u} (targetRing J (B := B))) :
    DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
          (ComplexShape.up ℤ) 0).obj F) ⟶
      (((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)))⟦(1 : ℤ)⟧ :=
  resolutionAtiyahClass J f F (atiyahTriangleFirstTermIso J f F) (atiyahTriangleThirdTermIso J f F)

/-- **The triangle (92.19.0.2) of [Stacks, Tag 09DH], as the source displays it:**

`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ ⟶ Lπ_!(P¹_{𝒫/π^{-1}𝒜}(ℱ)) ⟶ ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)[1]`,

the Atiyah triangle `CategoryTheory.Sheaf.resolutionAtiyahTriangle` read through the
identifications of its outer terms; its last arrow is the Atiyah class. -/
def sheafAtiyahTriangle (F : SheafOfModules.{u} (targetRing J (B := B))) :
    Triangle (DerivedCategory (SheafOfModules.{u} (targetRing J (B := B)))) :=
  Triangle.mk ((atiyahTriangleFirstTermIso J f F).inv ≫ (resolutionAtiyahTriangle J f F).mor₁)
    ((resolutionAtiyahTriangle J f F).mor₂ ≫ (atiyahTriangleThirdTermIso J f F).hom)
    (sheafAtiyahClass J f F)

/-- **[Stacks, Tag 09DH], Equation 92.19.0.2.** For a homomorphism `f : 𝒜 ⟶ ℬ` of sheaves of
commutative rings on a site and a sheaf of `ℬ`-modules `ℱ`,

`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ ⟶ Lπ_!(P¹_{𝒫/π^{-1}𝒜}(ℱ)) ⟶ ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)[1]`

is a distinguished triangle in `D(ℬ)`. -/
@[stacks 09DH]
theorem sheafAtiyahTriangle_distinguished (F : SheafOfModules.{u} (targetRing J (B := B))) :
    sheafAtiyahTriangle J f F ∈ distinguishedTriangles :=
  resolutionAtiyahClass_mem_distinguished J f F _ _

/-- **The Atiyah class of [Stacks, Tag 09DI] is the last arrow of the distinguished triangle of
[Stacks, Tag 09DH]**, whose first two arrows are those of the Atiyah triangle read through the
identifications of its outer terms. -/
theorem sheafAtiyahClass_mem_distinguished (F : SheafOfModules.{u} (targetRing J (B := B))) :
    Triangle.mk ((atiyahTriangleFirstTermIso J f F).inv ≫ (resolutionAtiyahTriangle J f F).mor₁)
        ((resolutionAtiyahTriangle J f F).mor₂ ≫ (atiyahTriangleThirdTermIso J f F).hom)
        (sheafAtiyahClass J f F) ∈ distinguishedTriangles :=
  sheafAtiyahTriangle_distinguished J f F

end CategoryTheory.Sheaf

end
