module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGoodModuleDataConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionPinning
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionRestrictionMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionTower
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction

/-!
# The section datum of a sheaf of differential graded algebras on a chaotic site

`SheafOfModules.DifferentialGradedModule.SectionData` packages everything the quasi-coherence
condition of Tag 0GZ9 is stated in terms of: the differential graded algebras `A(U)` of sections
with their restriction homomorphisms, pinned degreewise to `A`; the differential graded
`A(U)`-modules `M(U)` of sections of a differential graded `A`-module, as a functor, pinned the
same way; the derived sections functors `RΓ(U, -)` with their derived restriction maps, pinned on
the images of differential graded modules; and the derived base changes along the restriction
homomorphisms, pinned by their adjunctions to derived restriction of scalars.

This file assembles that datum on a site carrying the chaotic topology, over a sheaf of
commutative rings. Every field is a construction:

* the section algebras and modules are the direct sums `⨁ₙ Aⁿ(U)` and `⨁ₙ Mⁿ(U)`;
* the derived sections are the descent of taking sections through the localization of the
  homotopy category at the quasi-isomorphisms, which exists because evaluation at an object of a
  chaotic site is exact;
* the derived restriction maps are the descent of restriction of sections;
* the derived base changes are the derived tensor products with the regular bimodules of the
  restriction homomorphisms, which are left adjoint to derived restriction of scalars by
  Tag 0BYX.

The flat-resolution theory the datum is indexed by is taken at conditions (1) and (2) of the
definition of a good module in Tag 0FSA — flat as a graded module, and K-flat — which is what the
resolution of Tag 0FSH produces. That is all `GoodModuleData.ofExistsGood` asks of a notion of
goodness: K-flatness, so that the tensor product with an acyclic left module is acyclic, and the
existence of resolutions.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.chaoticGoodModuleData`: the flat-resolution theory of
  `(A, d)` on `derivedCategory A`, with goodness at conditions (1) and (2) of Tag 0FSA.
* `SheafOfModules.DifferentialGradedModule.sectionDatum`: **the section datum of `(A, d)` on a
  chaotic site.**

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Lemma 24.23.7 (Tag 0FSH)](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}}
  (A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-- **The flat-resolution theory of `(A, d)` at conditions (1) and (2) of Tag 0FSA.** The good
modules are those flat as graded modules and K-flat; K-flatness is what makes the tensor product
with an acyclic left differential graded module acyclic, and `exists_flat_quasiIso` of Tag 0FSH
resolves every right differential graded `A`-module by such a one. -/
def chaoticGoodModuleData :
    GoodModuleData.{t, m, m, v, u} A (derivedCategory.{t, m, m} A) :=
  GoodModuleData.ofExistsGood
    (fun P => RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
      RelativeTensor.IsKFlat P)
    (fun hP => hP.2)
    (fun M => by
      obtain ⟨Q, f, hf, hgf, hkf⟩ := exists_flat_quasiIso (A := A) M
      exact ⟨Q, f, ⟨hgf, hkf⟩, (acyclic_cone_iff_quasiIso A f).2 hf⟩)

/-- The localization of `chaoticGoodModuleData A` is the localization functor
`toDerivedCategory A` to the derived category of `(A, d)`. -/
@[simp] theorem chaoticGoodModuleData_localization :
    (chaoticGoodModuleData A).localization = toDerivedCategory.{t, m, m} A := rfl

/-- A differential graded `A`-module is good for `chaoticGoodModuleData A` if and only if it is
flat as a graded module and K-flat. -/
@[simp] theorem chaoticGoodModuleData_isGood :
    (chaoticGoodModuleData A).IsGood =
      fun P => RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
        RelativeTensor.IsKFlat P := rfl

/-- **The section datum of a sheaf of differential graded algebras on a chaotic site.** Every
field is constructed: the section algebras and modules are direct sums of groups of sections, the
derived sections and their restriction maps descend from taking sections, and the derived base
changes are the derived tensor products with the regular bimodules of the restriction
homomorphisms. -/
def sectionDatum : SectionData (ULift.{m} ℤ) (chaoticGoodModuleData A) where
  algebra U := A.sectionAlgebra U
  degree U n := A.sectionDegree U n
  degree_d U n x := A.sectionDegree_d U n x
  degree_mul U n i x y z hz := A.sectionDegree_mul U n i x y z hz
  degree_one U z hz := A.sectionDegree_one U z hz
  restriction a := A.sectionRestriction a
  restriction_degree a n x := A.sectionRestriction_degree a n x
  moduleSections U := sectionModuleFunctor A U
  moduleDegree U M n := M.sectionModuleDegree U n
  moduleDegree_d U M n x := M.sectionModuleDegree_d U n x
  moduleDegree_mul U M n i x y z hz := M.sectionModuleDegree_mul U n i x y z hz
  moduleDegree_naturality := fun U {M _} f n x => sectionModuleDegree_naturality M U f n x
  derivedSections U := derivedSections A U
  derivedSectionsIso U := derivedSectionsIso A U
  moduleRestriction a M := M.sectionModuleRestriction a
  moduleRestriction_degree a M n x := M.sectionModuleRestriction_degree a n x
  restrictionMap a := derivedRestrictionMap A a
  restrictionMap_moduleSections a M := derivedRestrictionMap_app_toDerivedCategory A a M
  baseChange a := DifferentialGraded.Bimodule.derivedTensorFunctor
    (DifferentialGraded.Bimodule.regular (A.sectionRestriction a))
  baseChangeAdj a :=
    DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
      (A.sectionRestriction a)

/-- The section algebra of `sectionDatum A` at `U` is the direct sum `A.sectionAlgebra U` of the
groups of sections `Aⁿ(U)`. -/
@[simp] theorem sectionDatum_algebra (U : Cᵒᵖ) :
    (sectionDatum A).algebra U = A.sectionAlgebra U := rfl

/-- The derived sections functor of `sectionDatum A` at `U` is `derivedSections A U`, the descent
of taking sections to the derived category. -/
@[simp] theorem sectionDatum_derivedSections (U : Cᵒᵖ) :
    (sectionDatum A).derivedSections U = derivedSections A U := rfl

end SheafOfModules.DifferentialGradedModule

end
