module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerPresheafComparison
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamUniqueness

/-!
# Local injectivity of the exact-wedge comparison

Let `φ : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space, with `B` the
structure sheaf of a ringed space `X`, let `Ω = Ω_{B/A}` be the sheaf of relative differentials and
let `B` also denote a package of the three algebras of Stacks Section 17.21 for `Ω`. The comparison
morphism

`AlgebraicGeometry.SheafOfModules.exactWedgeComparison : ⋀ᵖ(Ω_{B(U)/A(U)}) ⟶ (⋀ᵖ Ω)(U)`

is a sheafification unit followed by a degreewise isomorphism, hence locally injective. Together
with its local surjectivity, this shows that `⋀ᵖ Ω` is the sheafification of the presheaf
`U ↦ ⋀ᵖ(Ω_{B(U)/A(U)})`, with `exactWedgeComparison` as the sheafification map.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.exteriorGeneratorSectionwise`: the degree-one generator of the
  chosen package, read on the sheafification of the presheaf of sectionwise Kähler differentials
  through `moduleOfDifferentialsIsoSectionwise`.

## Main results

* `AlgebraicGeometry.SheafOfModules.exteriorGeneratorSectionwise_isExteriorAlgebra`: the chosen
  package's exterior algebra is an exterior algebra of the sheafification of the sectionwise Kähler
  differentials, with that generator.
* `AlgebraicGeometry.SheafOfModules.exactWedgeComparison_eq_extCmp`: the comparison is the
  comparison morphism of Tag 01CG for the degree-one generator precomposed by
  `toModuleOfDifferentials`.
* `AlgebraicGeometry.SheafOfModules.exactWedgeComparison_eq`: the comparison is the sheafification
  unit followed by a degreewise isomorphism.
* `AlgebraicGeometry.SheafOfModules.isLocallyInjective_exactWedgeComparison`: the comparison is
  locally injective, and `equalizerSieve_exactWedgeComparison_mem` is that statement with the
  covering sieve written out: two local sections of `⋀ᵖ(Ω_{B(U)/A(U)})` with the same image agree
  on a covering sieve.
* `AlgebraicGeometry.SheafOfModules.isLocallySurjective_exactWedgeComparison`: the comparison is
  locally surjective, as a `CategoryTheory.Presheaf.IsLocallySurjective` statement.
* `AlgebraicGeometry.SheafOfModules.isIso_sheafificationHomEquiv_symm_exactWedgeComparison`: `⋀ᵖ Ω`
  is the sheafification of the presheaf of sectionwise exterior powers of the sectionwise Kähler
  differentials, with the comparison as the sheafification map.

## References

* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 08TD](https://stacks.math.columbia.edu/tag/08TD)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace PresheafOfModules

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### The chosen exterior algebra as an exterior algebra of the sheafified sectionwise
differentials -/

/-- The degree-one generator of the chosen package, read on the sheafification of the presheaf of
sectionwise Kähler differentials: the inverse of
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise` followed by the
generator. -/
noncomputable def exteriorGeneratorSectionwise :
    (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology X.carrier)
        (𝟙 X.sheaf.obj)).obj
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom) ⟶
      B.exterior.piece 1 :=
  (moduleOfDifferentialsIsoSectionwise.{u, u} φ).inv ≫ B.exteriorGenerator

/-- The chosen package's exterior algebra is an exterior algebra of the sheafification of the
presheaf of sectionwise Kähler differentials, with generator
`AlgebraicGeometry.SheafOfModules.exteriorGeneratorSectionwise`. -/
theorem exteriorGeneratorSectionwise_isExteriorAlgebra :
    _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra B.exterior
      (exteriorGeneratorSectionwise B) :=
  B.exterior_isExteriorAlgebra.comp_iso (moduleOfDifferentialsIsoSectionwise.{u, u} φ).symm.hom
    (moduleOfDifferentialsIsoSectionwise.{u, u} φ).symm.isIso_hom

/-- The generator read on the unit-image of a local section of the sectionwise Kähler differentials
is the generator read through `AlgebraicGeometry.SheafOfModules.toModuleOfDifferentials`. -/
theorem exteriorGeneratorSectionwise_sheafifyUnit (U : (Opens X.carrier)ᵒᵖ)
    (m : (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
      φ.hom).obj U) :
    (exteriorGeneratorSectionwise B).val.app U
        (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
          (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology X.carrier)
            (𝟙 X.sheaf.obj))
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom))
          U m) =
      (toModuleOfDifferentials φ ≫ B.exteriorGenerator.val).app U m :=
  rfl

/-! ### The comparison as a sheafification unit, and its local injectivity -/

/-- The square-zero hypothesis for the degree-one generator precomposed with
`toModuleOfDifferentials`. -/
theorem genSquareZero_toModuleOfDifferentials_comp :
    Stacks.GradedAlgebra.GenSquareZero B.exterior.toPresheafGradedAlgebra
      (toModuleOfDifferentials φ ≫ B.exteriorGenerator.val) :=
  Stacks.GradedAlgebra.GenSquareZero.comp _ _
    (fun Y x ↦ B.squareZero_exteriorGenerator Y x) (toModuleOfDifferentials φ)

/-- The exact-wedge comparison is the comparison morphism of Tag 01CG for the degree-one generator
precomposed with `toModuleOfDifferentials`. -/
theorem exactWedgeComparison_eq_extCmp (p : ℕ) :
    exactWedgeComparison B p =
      B.exterior.toPresheafGradedAlgebra.extCmp
        (toModuleOfDifferentials φ ≫ B.exteriorGenerator.val)
        (genSquareZero_toModuleOfDifferentials_comp B) p :=
  Stacks.GradedAlgebra.extPowMap_comp_extCmp _ _ _ p _

/-- The exact-wedge comparison is the sheafification unit followed by a degreewise isomorphism. -/
theorem exactWedgeComparison_eq (p : ℕ) :
    exactWedgeComparison B p =
      PresheafOfModules.sheafifyUnit
          (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology X.carrier)
            (𝟙 X.sheaf.obj))
          (PresheafOfModules.extPow.{u, u, u, u} p
            (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)) ≫
        (_root_.SheafOfModules.forget (CategoryTheory.Sheaf.toRingCat
            (Opens.grothendieckTopology X.carrier) X.sheaf)).map
          (_root_.SheafOfModules.exteriorPieceIsoPresheaf
            (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)
            B.exterior
            (exteriorGeneratorSectionwise B)
            (exteriorGeneratorSectionwise_isExteriorAlgebra B) (p : ℤ)).hom :=
  (exactWedgeComparison_eq_extCmp B p).trans
    (_root_.SheafOfModules.extCmp_eq_sheafifyUnit_comp
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)
      B.exterior
      (exteriorGeneratorSectionwise B) (toModuleOfDifferentials φ ≫ B.exteriorGenerator.val)
      (genSquareZero_toModuleOfDifferentials_comp B)
      (exteriorGeneratorSectionwise_isExteriorAlgebra B)
      (exteriorGeneratorSectionwise_sheafifyUnit B) p)

/-- The exact-wedge comparison is locally injective. -/
theorem isLocallyInjective_exactWedgeComparison (p : ℕ) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
      ((PresheafOfModules.toPresheaf (CategoryTheory.Sheaf.toRingCat
        (Opens.grothendieckTopology X.carrier) X.sheaf).obj).map
          (exactWedgeComparison B p)) := by
  rw [exactWedgeComparison_eq_extCmp B p]
  exact _root_.SheafOfModules.isLocallyInjective_extCmp
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom) B.exterior
    (exteriorGeneratorSectionwise B) (toModuleOfDifferentials φ ≫ B.exteriorGenerator.val)
    (genSquareZero_toModuleOfDifferentials_comp B)
    (exteriorGeneratorSectionwise_isExteriorAlgebra B)
    (exteriorGeneratorSectionwise_sheafifyUnit B) p

/-- Two local sections of the sectionwise exterior powers of the sectionwise Kähler differentials
with the same image under the exact-wedge comparison agree on a covering sieve. -/
theorem equalizerSieve_exactWedgeComparison_mem (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (z z' : (PresheafOfModules.extPow.{u, u, u, u} p
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)).obj U)
    (h : (exactWedgeComparison B p).app U z = (exactWedgeComparison B p).app U z') :
    Presheaf.equalizerSieve (F := (PresheafOfModules.toPresheaf
        (CategoryTheory.Sheaf.toRingCat
          (Opens.grothendieckTopology X.carrier) X.sheaf).obj).obj
        (PresheafOfModules.extPow.{u, u, u, u} p
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
            φ.hom))) z z' ∈
      Opens.grothendieckTopology X.carrier U.unop :=
  have := isLocallyInjective_exactWedgeComparison B p
  Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X.carrier)
    ((PresheafOfModules.toPresheaf (CategoryTheory.Sheaf.toRingCat
      (Opens.grothendieckTopology X.carrier) X.sheaf).obj).map
        (exactWedgeComparison B p)) z z' h

/-- The exact-wedge comparison is locally surjective. -/
theorem isLocallySurjective_exactWedgeComparison (p : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      ((PresheafOfModules.toPresheaf (CategoryTheory.Sheaf.toRingCat
        (Opens.grothendieckTopology X.carrier) X.sheaf).obj).map
          (exactWedgeComparison B p)) :=
  ⟨fun {U} ξ ↦ mem_imageSieve_exactWedgeComparison B p (op U) ξ⟩

/-- `⋀ᵖ Ω` is the sheafification of the presheaf of sectionwise exterior powers of the sectionwise
Kähler differentials, with the exact-wedge comparison as the sheafification map. -/
theorem isIso_sheafificationHomEquiv_symm_exactWedgeComparison (p : ℕ) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv
      (𝟙 (CategoryTheory.Sheaf.toRingCat
        (Opens.grothendieckTopology X.carrier) X.sheaf).obj)).symm
          (exactWedgeComparison B p)) :=
  Stacks.TensorCoherence.isIso_sheafificationHomEquiv_symm _ _
    (isLocallyInjective_exactWedgeComparison B p)
    (isLocallySurjective_exactWedgeComparison B p)

end AlgebraicGeometry.SheafOfModules

end
