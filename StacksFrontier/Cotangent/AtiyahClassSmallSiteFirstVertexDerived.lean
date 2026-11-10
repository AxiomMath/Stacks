module

public import StacksFrontier.Cotangent.AtiyahClassSmallSiteFirstVertex
public import StacksFrontier.Cotangent.AtiyahClassSmallSiteMoore

/-!
# The first vertex of the Atiyah triangle is the Moore complex of `M ⊗_{B̲} i^*Ω_{𝒪/A}`

The triangle of [Stacks, Tag 09DD] is displayed with its first term identified as
`L_{B/A} ⊗^𝐋_B M`. This file carries that identification through the whole derived chain and
completes it:

`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲) ≅ Q(Moore((M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A}))(P_•, ε))) ≅ L_{B/A} ⊗^𝐋_B M`.

The first isomorphism has four steps, each one already available:

1. the first vertex as the plain objectwise tensor product,
   `CommAlgCat.smallAtiyahFirstVertexTensorIso`, which undoes the sheafification and the
   corepresenting-object spelling;
2. that tensor product as the `𝒪`-module underlying a `B̲`-module,
   `CommAlgCat.smallAtiyahFirstVertexRestrictionIso`, which is the projection formula;
3. the replacement of `Lπ_! : D(𝒪) ⟶ D(B)` of [Stacks, Tag 09CZ] by `Lπ_! : D(B̲) ⟶ D(B)` at a
   module of that form, `Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso`,
   which rests on the change of coefficients of [Stacks, Tag 08QJ];
4. the computation of the latter as an extended Moore complex on a point resolution,
   `Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`, which is the derived form of
   [Stacks, Tag 08PT] — the standard resolution being a point resolution of the small model by
   `CommAlgCat.isPointResolution_standardResolutionSmallCosimplicialObject`.

## Main results

* `CommAlgCat.smallAtiyahFirstVertexMooreIso`: **the first vertex of the Atiyah triangle on the
  small model of `C_{B/A}` is the extended Moore complex of `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})` evaluated
  on the standard resolution.**
* `CommAlgCat.nonempty_smallAtiyahFirstVertexDerivedTensorIso`: **that vertex is
  `L_{B/A} ⊗^𝐋_B M`**, the first displayed term of [Stacks, Tag 09DD].

## Implementation notes

**Why the last step needed a construction and not a `rfl`.** The step from
`CommAlgCat.smallAtiyahFirstVertexMooreIso` to the displayed term is the comparison of the two
diagrams of `B`-modules

`(Stacks.ChaoticSite.constantModulePresheafEquivalence B).functor.obj
  (CommAlgCat.smallAtiyahFirstVertexConstantModule A B M)`  and
`CommAlgCat.smallPolynomialCotangentModulePresheaf A B κ ⋙ tensorLeft M`,

both of which have sections `M ⊗_B (B ⊗_P Ω[P⁄A])`; it is
`CommAlgCat.smallAtiyahFirstVertexDiagramIso`. Its differentials half is
`CommAlgCat.extendScalarsDifferentialsObjIso` with
`CommAlgCat.extendScalarsDifferentialsObjIso_naturality`, which apply without bridging because
`(Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
(CommAlgCat.smallAtiyahAugmentationComm A B κ).hom).obj Ω_{𝒪/A}` and
`(Stacks.PullbackModel.extendScalars (CommAlgCat.smallPolynomialAugmentationComm A B κ)).obj
Ω_{𝒪/A}` are the same presheaf of modules on the nose
(`CommAlgCat.smallAtiyahChangeOfRingsDifferentialsIso`).

What had to be arranged is the ability to *see* the sections of the first diagram from outside
the module that defines the equivalence.
`Stacks.ChaoticSite.constantModulePresheafEquivalence` lives in a section that is not
`@[expose]` (`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedLowerShriek.lean`),
and the factor carrying its `functor`, `Stacks.ChaoticSite.constantModuleDiagram`, is a
`private def` built by `rcases`/`subst` in another non-exposed section (
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedLowerShriekOfInverseImage.lean`),
so `((...).functor.obj G).obj V` does not reduce to `G.obj V` outside those files. Exposing the
two sections unblocks the reduction but breaks the existing proof at
`StacksFrontier/Cotangent/DerivedLowerShriekRestrictedCoefficients.lean:325`, whose `IsIso`
argument typechecks only against the folded form of
`Stacks.CategoryHomology.totalDerivedColimit`. Nor can the reduction be stated *there* as a
`rfl` lemma: a theorem exported from a module may not unfold a definition the module does not
expose, so both the statement and the proof of such a lemma are rejected in the very file that
gives the equivalence. What a `def` may do is use those bodies in its own construction, and that
is the repair taken: `Stacks.ChaoticSite.constantModuleSheafEquivalenceFunctorObjIso` and
`Stacks.ChaoticSite.constantModulePresheafEquivalenceFunctorObjIso` build an isomorphism onto
any diagram with the same sections and the same restriction maps, which is all a consumer needs
and carries no exposure change. `CommAlgCat.smallAtiyahModuleOverConstantIso` is the companion
on the other side of the equivalence: the `B̲`-module attached to `M` is
`Stacks.ChaoticSite.constantSectionsModulePresheaf`, obtained from the unit of the equivalence
rather than from a reduction.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.SheafOfModules (moduleSheaves)
open Stacks.ChaoticSite.ModuleValued

universe u

namespace CommAlgCat

attribute [local instance 2000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (M : ModuleCat.{u} (B : Type u))

/-- **The `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`**, whose `𝒪`-module of restricted scalars is the
first vertex of the Atiyah triangle before `Lπ_!`. Its sections over `(P, α)` are
`M ⊗_B (B ⊗_P Ω[P⁄A])`. -/
abbrev smallAtiyahFirstVertexConstantModule :
    PresheafOfModules.{u} ((Functor.const (smallBoundedPolynomialSite A B
      (standardResolutionVarCardinal A B))ᵒᵖ).obj (RingCat.of (B : Type u))) :=
  (Stacks.tensorRight
      (O := (smallAtiyahConstantSheaf A B (standardResolutionVarCardinal A B)).obj)
      ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
        (smallAtiyahAugmentationComm A B (standardResolutionVarCardinal A B)).hom).obj
          (smallAtiyahRelativeDifferentialsPresheaf A B
            (standardResolutionVarCardinal A B)))).obj
    (smallAtiyahModuleOverConstant A B M (standardResolutionVarCardinal A B))

/-- **The first vertex of the Atiyah triangle on the small model of `C_{B/A}` is the extended
Moore complex of `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})` evaluated on the standard resolution.**

`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲) ≅ Q(Moore((M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A}))(P_•, ε)))` in `D(B)`.

The four steps are listed in the module documentation: the vertex is first stripped of the
sheafification and of the corepresenting-object spelling of its tensor factor
(`CommAlgCat.smallAtiyahFirstVertexTensorIso`), then recognised as the `𝒪`-module underlying a
`B̲`-module by the projection formula (`CommAlgCat.smallAtiyahFirstVertexRestrictionIso`), after
which `Lπ_!` of [Stacks, Tag 09CZ] is replaced by `Lπ_! : D(B̲) ⟶ D(B)`
(`Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso`) and the latter computed
by the derived form of [Stacks, Tag 08PT] on the standard resolution
(`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`).

The passage from here to the displayed first term `L_{B/A} ⊗^𝐋_B M` is
`CommAlgCat.smallAtiyahFirstVertexDiagramIso` followed by
`CommAlgCat.nonempty_smallAtiyahMooreDerivedTensorIso`, assembled as
`CommAlgCat.nonempty_smallAtiyahFirstVertexDerivedTensorIso`. -/
def smallAtiyahFirstVertexMooreIso :
    (smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).obj₁ ≅
      DerivedCategory.Q.obj
        ((mooreCochainComplex (standardResolutionSmallCosimplicialObject A B)).obj
          ((Stacks.ChaoticSite.constantModulePresheafEquivalence (B : Type u)).functor.obj
            (smallAtiyahFirstVertexConstantModule A B M))) :=
  (Stacks.Atiyah.lowerShriek (O₂ := smallAtiyahStructureSheaf A B
          (standardResolutionVarCardinal A B)) (B : Type u)
        (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))).mapIso
      ((DerivedCategory.singleFunctor (PresheafOfModules.{u}
            (smallPolynomialStructurePresheaf A B
              (standardResolutionVarCardinal A B))) 0).mapIso
        (smallAtiyahFirstVertexTensorIso A B M (standardResolutionVarCardinal A B) ≪≫
          smallAtiyahFirstVertexRestrictionIso A B M
            (standardResolutionVarCardinal A B))) ≪≫
    (Stacks.Atiyah.lowerShriek (O₂ := smallAtiyahStructureSheaf A B
          (standardResolutionVarCardinal A B)) (B : Type u)
        (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (PresheafOfModules.{u}
        (smallPolynomialStructurePresheaf A B
          (standardResolutionVarCardinal A B))) 0).app _) ≪≫
    Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso
      (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))
      (standardResolutionSmallCosimplicialObject A B)
      (isPointResolution_standardResolutionSmallCosimplicialObject A B)
      (isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian A B)
      (smallAtiyahFirstVertexConstantModule A B M) ≪≫
    (mooreCochainQIsoDerivedColimit (standardResolutionSmallCosimplicialObject A B)
      ((Stacks.ChaoticSite.constantModulePresheafEquivalence (B : Type u)).functor.obj
        (smallAtiyahFirstVertexConstantModule A B M))
      (isPointResolution_standardResolutionSmallCosimplicialObject A B)).symm

/-- **The first vertex of the Atiyah triangle on the small model of `C_{B/A}` is
`L_{B/A} ⊗^𝐋_B M`**, which is the first displayed term of the triangle of [Stacks, Tag 09DD]:

`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲) ≅ L_{B/A} ⊗^𝐋_B M` in `D(B)`.

`CommAlgCat.smallAtiyahFirstVertexMooreIso` computes the vertex as the extended Moore complex of
the `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})` on the standard resolution,
`CommAlgCat.smallAtiyahFirstVertexDiagramIso` reads that `B̲`-module as the diagram
`M ⊗_B i^*Ω_{𝒪/A}`, and `CommAlgCat.nonempty_smallAtiyahMooreDerivedTensorIso` computes the
extended Moore complex of that diagram to be `L_{B/A} ⊗^𝐋_B M`.

`Nonempty` is inherited from the last of the three, where it records the non-canonical choice of
a K-flat resolution; it is the same idiom as
`CommAlgCat.nonempty_derivedExtensionScalars_cotangentTriangle_obj₁_iso` for the analogous first
vertex of [Stacks, Tag 08SD]. -/
theorem nonempty_smallAtiyahFirstVertexDerivedTensorIso :
    Nonempty ((smallPolynomialAtiyahTriangle A B (standardResolutionVarCardinal A B) M).obj₁ ≅
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor (B : Type u)).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u} A B))).obj
        (DerivedCategory.Q.obj (moduleSingleComplex A B M))) :=
  (nonempty_smallAtiyahMooreDerivedTensorIso A B M).map fun e =>
    smallAtiyahFirstVertexMooreIso A B M ≪≫
      DerivedCategory.Q.mapIso
          ((mooreCochainComplex (standardResolutionSmallCosimplicialObject A B)).mapIso
            (smallAtiyahFirstVertexDiagramIso A B M
              (standardResolutionVarCardinal A B))) ≪≫
        e

end CommAlgCat

end
