module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CoefficientQuasiIsomorphismUnbounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitForgetNatIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriek
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
import StacksCore.Tactic.StacksAttribute
-- the bodies of `constantModulePresheafEquivalence`, `constantModuleSheafEquivalence` and
-- `derivedColimitWithCoefficients` are not exposed by the modules defining them; the
-- identifications below that read them are definitional
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriek
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfInverseImage

/-!
# The `B`-module structure on `Lπ_!(K)`

Let `C` be a small category carrying the chaotic topology, let `B` be a ring and let `O` be a
sheaf of rings on `C` together with a map `φ : O ⟶ B̲` to the constant sheaf of rings — the data
of Example 08PF. Assume `C` admits a cosimplicial object which is a point resolution, the
hypothesis of Lemma 08Q9, and assume that `φ` **induces an isomorphism `Lπ_!O ⟶ Lπ_!B̲`**, the
remaining hypothesis of [Stacks, Tag 09CZ].

The exact functor `Lπ_! : D(O) ⟶ D(B)` of the tag is
`Stacks.ChaoticSite.derivedColimitWithCoefficients`, the composite of derived extension of
scalars `- ⊗^L_O B̲` with derived lower shriek `D(B̲) ⟶ D(B)`; it and its exactness exist for
every `φ`. What the tag's hypothesis on `φ` buys is the last assertion of the remark: the
`B`-module structure on `Lπ_!(K)`, that is, the identification of `Lπ^{Ab}_!(K)` with the
underlying object of `D(Ab)` of `Lπ_!(K)` read in `D(B)`. That identification is built here, as
`Stacks.ChaoticSite.derivedColimitWithCoefficientsForgetNatIso`.

## Main definitions

* `Stacks.ChaoticSite.derivedConstantModulePresheafEquivalence`: the equivalence of derived
  categories induced by `Stacks.ChaoticSite.constantModulePresheafEquivalence`.
* `Stacks.ChaoticSite.derivedCoefficientExtensionIso`: derived extension of scalars along the
  coefficient map is derived extension of scalars followed by the identification of modules over
  the constant sheaf of rings with diagrams of modules.
* `Stacks.ChaoticSite.derivedColimitWithCoefficientsIso`: the functor `Lπ_! : D(O) ⟶ D(B)` of
  the tag is the composite it is defined as.
* `Stacks.ChaoticSite.derivedColimitWithCoefficientsForgetNatIso`: **Stacks 09CZ**, the
  `B`-module structure on `Lπ_!(K)`.

## How the identification is assembled

Three steps, of which only the first two have content.

* [Stacks, Tag 08RX], `Stacks.ChaoticSite.derivedColimitTensorNatIso`, identifies
  `Lπ^{Ab}_!(K)` with `Lπ^{Ab}_!(K ⊗^L_O B̲)` for every object `K` of `D(Mod(O))`. **This is the
  one place the tag's hypothesis that `Lπ_!O ⟶ Lπ_!B̲` be invertible is used**, and it is the
  justification the remark itself gives.
* `Stacks.ChaoticSite.derivedColimitForgetComparisonNatIso` identifies `Lπ_!` of the underlying
  abelian diagram of a diagram of `B`-modules with the underlying object of `D(Ab)` of `Lπ_!`
  read in `D(B)`. This is where the cosimplicial point resolution is used.
* The two are glued by `Stacks.ChaoticSite.derivedCoefficientExtensionIso` and by
  `Stacks.ChaoticSite.toPresheaf_eq_constantModulePresheafEquivalence_comp_forgetModuleDiagrams`,
  which says that on a chaotic site the underlying abelian presheaf of a module over the constant
  sheaf of rings *is* the underlying abelian diagram of the corresponding diagram of modules. That
  holds on the nose, so this step costs only the comparison of the degreewise action of a composite
  with the composite of the degreewise actions.

## Implementation notes

`Stacks.ChaoticSite.derivedCoefficientExtensionIso` is uniqueness of left adjoints: both sides
are left adjoint to the degreewise derived functor of
`Stacks.ChaoticSite.coefficientRestriction`, which is by definition the inverse of the
equivalence followed by restriction of scalars. The adjunction for the equivalence's derived
functor is `StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence`, which takes the two
functors and the two isomorphisms rather than a `CategoryTheory.Equivalence`.

The bodies of `Stacks.ChaoticSite.constantModulePresheafEquivalence`,
`Stacks.ChaoticSite.constantModuleSheafEquivalence` and
`Stacks.ChaoticSite.derivedColimitWithCoefficients` are not exposed by the modules defining them,
so those modules are imported with `import all`, and the declarations below that unfold them are
not exposed either.

## References

* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C : Type u} [SmallCategory C] (B : Type u) [Ring B]

/-- **On a chaotic site the underlying abelian presheaf of a module over the constant sheaf of
rings is the underlying abelian diagram of the corresponding diagram of modules**, on the nose. -/
theorem toPresheaf_eq_constantModulePresheafEquivalence_comp_forgetModuleDiagrams :
    PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of B)) =
      (constantModulePresheafEquivalence (C := C) B).functor ⋙
        forgetModuleDiagrams (C := C) (B := B) :=
  by rfl

/-- The derived form of
`Stacks.ChaoticSite.toPresheaf_eq_constantModulePresheafEquivalence_comp_forgetModuleDiagrams`. -/
def derivedToPresheafConstantIso :
    (PresheafOfModules.toPresheaf
        ((Functor.const Cᵒᵖ).obj (RingCat.of B))).mapDerivedCategory ≅
      (constantModulePresheafEquivalence (C := C) B).functor.mapDerivedCategory ⋙
        (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (constantModulePresheafEquivalence (C := C) B).functor (forgetModuleDiagrams (C := C) (B := B))

/-- The equivalence of derived categories induced by
`Stacks.ChaoticSite.constantModulePresheafEquivalence`. -/
def derivedConstantModulePresheafEquivalence :
    DerivedCategory (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B))) ≌
      DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{u} B) :=
  StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence
    (constantModulePresheafEquivalence (C := C) B).functor
    (constantModulePresheafEquivalence (C := C) B).inverse
    (constantModulePresheafEquivalence (C := C) B).unitIso
    (constantModulePresheafEquivalence (C := C) B).counitIso

variable (O : Cᵒᵖ ⥤ RingCat.{u}) (φ : O ⟶ (Functor.const Cᵒᵖ).obj (RingCat.of B))

/-- **Derived extension of scalars along the coefficient map is derived extension of scalars
followed by the identification of modules over the constant sheaf of rings with diagrams of
modules.** Both are left adjoint to the degreewise derived functor of
`Stacks.ChaoticSite.coefficientRestriction`. -/
def derivedCoefficientExtensionIso :
    derivedCoefficientExtension B O φ ≅
      derivedExtendScalars φ ⋙
        (constantModulePresheafEquivalence (C := C) B).functor.mapDerivedCategory :=
  Adjunction.leftAdjointUniq (derivedCoefficientExtensionAdjunction B O φ)
    (((derivedExtendScalarsAdjunction φ).comp
        (derivedConstantModulePresheafEquivalence (C := C) B).toAdjunction).ofNatIsoRight
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (constantModulePresheafEquivalence (C := C) B).inverse
        (PresheafOfModules.restrictScalars.{u} φ)).symm)

/-- **Derived lower shriek with coefficients is the composite it is defined as**, derived extension
of scalars followed by derived lower shriek on diagrams of `B`-modules; the identity. -/
def derivedColimitWithCoefficientsIso :
    derivedColimitWithCoefficients B O φ ≅
      derivedCoefficientExtension B O φ ⋙ totalDerivedColimit C (ModuleCat.{u} B) :=
  Iso.refl _

/-- **Stacks 09CZ: the `B`-module structure on `Lπ_!(K)`.** Let `C` and `B` be as in Example
08PF, let `U_•` be a cosimplicial object of `C` which is a point resolution (Lemma 08Q9), and let
`φ : O ⟶ B̲` be a map to the constant sheaf of rings which induces an isomorphism
`Lπ_!O ⟶ Lπ_!B̲`. Then derived lower shriek with coefficients in `O` on underlying abelian
sheaves is derived lower shriek with coefficients in `B`, read on underlying abelian groups:

`Lπ^{Ab}_!(K) ≅ Lπ_!(K)` in `D(Ab)`, naturally in `K ∈ D(Mod(O))`,

where the right-hand side is `Stacks.ChaoticSite.derivedColimitWithCoefficients`, the functor
`D(O) ⟶ D(B)` of the tag. This is the remark's closing assertion, that `Lπ_!(K)` carries a
`B`-module structure "coming from the (canonical, functorial) identification of `Lπ_!(K)` with
`Lπ_!(K ⊗_O^L B̲)` of the lemma".

The remark is covered by this declaration together with the three that state the functor and
its exactness: `Stacks.ChaoticSite.derivedColimitWithCoefficients` (the functor
`Lπ_! : D(O) ⟶ D(B)`, defined as `- ⊗^L_O B̲` followed by `Lπ_! : D(B̲) ⟶ D(B)`),
`Stacks.ChaoticSite.derivedColimitWithCoefficients_commShift` and
`Stacks.ChaoticSite.derivedColimitWithCoefficients_isTriangulated` (it is an exact functor of
triangulated categories), all in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedLowerShriek.lean`. Those exist
for every `φ`; the hypotheses of the remark enter only here, through Stacks 08RX
(`Stacks.ChaoticSite.derivedColimitTensorNatIso`), and they are what makes the functor a lift of
`Lπ^{Ab}_!`. -/
@[stacks 09CZ "the B-module structure on `Lpi_!(K)`: the identification of `Lpi^{Ab}_!(K)` with \
  the underlying object of `D(Ab)` of `Lpi_!(K)` read in `D(B)`, for a cosimplicial point \
  resolution and a coefficient map `O -> B` inducing an isomorphism `Lpi_!O -> Lpi_!B`. The \
  functor `Lpi_! : D(O) -> D(B)` and its exactness, which need no hypothesis on the coefficient \
  map, are `Stacks.ChaoticSite.derivedColimitWithCoefficients`, \
  `Stacks.ChaoticSite.derivedColimitWithCoefficients_commShift` and \
  `Stacks.ChaoticSite.derivedColimitWithCoefficients_isTriangulated`"]
def derivedColimitWithCoefficientsForgetNatIso (U : CosimplicialObject C)
    (hU : IsPointResolution U)
    (ha : IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map
        (Functor.whiskerRight φ (forget₂ RingCat.{u} AddCommGrpCat.{u}))))) :
    abelianDerivedColimitOfModules O ≅
      derivedColimitWithCoefficients B O φ ⋙
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory :=
  derivedColimitTensorNatIso U φ hU ha ≪≫
    Functor.isoWhiskerLeft (derivedExtendScalars φ)
      (Functor.isoWhiskerRight (derivedToPresheafConstantIso (C := C) B)
          (totalDerivedColimit C AddCommGrpCat.{u}) ≪≫
        Functor.isoWhiskerLeft
          (constantModulePresheafEquivalence (C := C) B).functor.mapDerivedCategory
          (derivedColimitForgetComparisonNatIso C B hU)) ≪≫
    (Functor.associator (derivedExtendScalars φ)
        (constantModulePresheafEquivalence (C := C) B).functor.mapDerivedCategory
        (totalDerivedColimit C (ModuleCat.{u} B) ⋙
          (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory)).symm ≪≫
    Functor.isoWhiskerRight (derivedCoefficientExtensionIso B O φ).symm
      (totalDerivedColimit C (ModuleCat.{u} B) ⋙
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory) ≪≫
    (Functor.associator (derivedCoefficientExtension B O φ)
      (totalDerivedColimit C (ModuleCat.{u} B))
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory).symm ≪≫
    Functor.isoWhiskerRight (derivedColimitWithCoefficientsIso B O φ).symm
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory

end Stacks.ChaoticSite

end
