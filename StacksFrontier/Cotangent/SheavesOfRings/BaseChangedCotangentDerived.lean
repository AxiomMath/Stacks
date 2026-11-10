module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import
StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.CoefficientMorphismModules
public import StacksFrontier.Cotangent.BaseChangeQuasiIso
public import StacksFrontier.Cotangent.CotangentDerivedTensorModule
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# The first vertex of the fundamental triangle is a derived tensor product

Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a site. The first vertex
of the distinguished triangle of Tag 08SZ is `L_{B/A} ⊗^L_B D`. This file shows that the complex
`CategoryTheory.Sheaf.baseChangedCotangentComplex`, the degreewise base change `L_{B/A} ⊗_B D`
of the cotangent complex, represents it: the derived base change along `h : B ⟶ D` of
`L_{B/A}` is the class of that complex.

The derived base change is the derived pullback `Lh^*` of Tag 06YY along the morphism of ringed
topoi `(Sh(C), D) ⟶ (Sh(C), B)` with identity geometric morphism and structure map `h`,
`AlgebraicGeometry.RingedToposHom.coefficientMorphism`. That derived pullback exists with the
object, morphism and section universes of the site independent, so the statements here hold for
any site, with no smallness condition.

## Main definitions

* `CategoryTheory.Sheaf.towerDerivedBaseChange`: the derived base change
  `- ⊗^L_B D : D(B) ⥤ D(D)`.
* `CategoryTheory.Sheaf.baseChangedCotangentComplexDerivedIso`: `L_{B/A} ⊗^L_B D` is the class
  of the degreewise base change `L_{B/A} ⊗_B D`.

## Main results

* `CategoryTheory.Sheaf.isFlat_cotangentComplex_X'`: the terms of `L_{B/A}` are flat
  `B`-modules.
* `CategoryTheory.Sheaf.isKFlat_cotangentComplex'`: `L_{B/A}` is K-flat with flat terms.

## Implementation notes

The terms of `L_{B/A}` are flat because, by Tag 08SX, the degree-`j` term is the sheafification
of the presheaf `U ↦ L^j_{B(U)/A(U)}`, whose sections `Ω_{P_n/A(U)} ⊗_{P_n} B(U)` are projective
`B(U)`-modules, the terms `P_n` of the standard resolution being polynomial algebras. A bounded
above complex of flat modules is K-flat (Tag 06YQ), so the comparison `Lh^* ⟶ h^*` is
invertible at `L_{B/A}` (Tag 06YY), and the degreewise pullback `h^*` is extension of scalars,
both being left adjoint to restriction of scalars along `h`
(`AlgebraicGeometry.RingedToposHom.pullbackModulesCoefficientMorphismIso`).

The derived categories are the standard models `HasDerivedCategory.standard`, which are the
models the derived pullback of Tag 06YY is stated for.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section Flatness

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- **The terms of the cotangent complex of a homomorphism of sheaves of rings are flat.** By
Tag 08SX the degree-`j` term of `L_{B/A}` is the sheafification of the presheaf
`U ↦ L^j_{B(U)/A(U)}`, whose sections are flat `B(U)`-modules; a presheaf of modules with flat
sections is flat (Tag 03ES) and the sheafification of a flat presheaf of modules is flat
(Tag 03ET). -/
theorem isFlat_cotangentComplex_X' (j : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v w, max u v w} (O := B)
      ((cotangentComplex.{u, v, w} J f).X j) := by
  have hpre : AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat
      (sectionwiseCotangentTerm.{u, v, w} J f j) :=
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat _
      (fun U => CommAlgCat.flat_cotangentComplex_X.{max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) j)
  have hsh := Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J (O := B.obj)
    (Osharp := B) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)
    (sectionwiseCotangentTerm.{u, v, w} J f j) hpre
  have := isIso_sheafify_sectionwiseCotangentTermComparison.{u, v, w} J f j
  exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize B
    (asIso ((PresheafOfModules.sheafificationHomEquiv.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm
        (sectionwiseCotangentTermComparison J f j))) hsh

/-- The cotangent complex is concentrated in nonpositive cohomological degrees. -/
instance isStrictlyLE_cotangentComplex' : (cotangentComplex.{u, v, w} J f).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => cotangentComplex_isZero_pos J f i hi

/-- **The cotangent complex is K-flat with flat terms**: it is bounded above with flat terms
(Tag 06YQ), so the derived pullback of Tag 06YY is computed on it degreewise. -/
theorem isKFlat_cotangentComplex' :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ({ C := C, J := J, O := B } : AlgebraicGeometry.RingedTopos.{v, u, max u v w}))
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v, w} J f)) :=
  ⟨Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat B _ ⟨0, isStrictlyLE_cotangentComplex' J f⟩
      (isFlat_cotangentComplex_X' J f),
    isFlat_cotangentComplex_X' J f⟩

end Flatness

section DerivedBaseChange

variable {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

open AlgebraicGeometry.RingedToposHom

/-- The pullback of sheaves of modules along the change of coefficient rings `h` is additive. -/
instance additive_pullbackModules_coefficientMorphism :
    (coefficientMorphism.{max u v w} J h).toModulesHom.pullbackModules.Additive :=
  pullbackModules_additive (coefficientMorphism.{max u v w} J h)

/-- The pullback of sheaves of modules along the change of coefficient rings `h : B ⟶ D` is the
extension of scalars `- ⊗_B D` of the tower. -/
abbrev towerPullbackModulesIso :
    (coefficientMorphism.{max u v w} J h).toModulesHom.pullbackModules ≅
      towerExtendScalars.{u, v, w} J h :=
  pullbackModulesCoefficientMorphismIso J h

/-- The degreewise pullback of `L_{B/A}` along the change of coefficient rings `h : B ⟶ D` is
the complex `L_{B/A} ⊗_B D` of the first vertex of the triangle of Tag 08SZ: degreewise
pullback is degreewise extension of scalars. -/
def baseChangedCotangentComplexPullbackIso :
    (((coefficientMorphism.{max u v w} J h).toModulesHom.pullbackModules).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v, w} J g) ≅
      baseChangedCotangentComplex.{u, v, w} J g h :=
  (HomologicalComplex.mapHomologicalComplexExtendIso
      ((coefficientMorphism.{max u v w} J h).toModulesHom.pullbackModules)
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (cotangentSimplicialModule.{u, v, w} J g).object)
      (ComplexShape.embeddingUpIntLE 0)).symm ≪≫
    ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor _).mapIso
      ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
          ((coefficientMorphism.{max u v w} J h).toModulesHom.pullbackModules)).app
          (cotangentSimplicialModule.{u, v, w} J g).object ≪≫
        (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
          (Functor.isoWhiskerLeft (cotangentSimplicialModule.{u, v, w} J g).object
            (towerPullbackModulesIso J h)))

attribute [local instance 10000] HasDerivedCategory.standard
/-- The derived pullback along the change of coefficient rings `h` exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_coefficientMorphism :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy
      (coefficientMorphism.{max u v w} J h)).HasLeftDerivedFunctor
        (Stacks.Cohomology.DerivedPullbackOfToposHom.quasiIsoTarget
          (Y := ({ C := C, J := J, O := B } : AlgebraicGeometry.RingedTopos.{v, u, max u v w}))) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (coefficientMorphism.{max u v w} J h)

/-- **The derived base change** `- ⊗^L_B D : D(B) ⥤ D(D)` along a homomorphism `h : B ⟶ D` of
sheaves of rings: the derived pullback of Tag 06YY along the change of coefficient rings that
`h` presents. -/
abbrev towerDerivedBaseChange :
    DerivedCategory (targetModules.{u, v, w} J B) ⥤ DerivedCategory (targetModules.{u, v, w} J D) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
    (X := ({ C := C, J := J, O := D } : AlgebraicGeometry.RingedTopos.{v, u, max u v w}))
    (Y := ({ C := C, J := J, O := B } : AlgebraicGeometry.RingedTopos.{v, u, max u v w}))
    (coefficientMorphism.{max u v w} J h)

/-- **The first vertex of the triangle of Tag 08SZ is `L_{B/A} ⊗^L_B D`.** The complex
`L_{B/A} ⊗_B D`, the degreewise base change of the cotangent complex of `A ⟶ B`, represents the
derived base change of `L_{B/A}` along `h : B ⟶ D`: the cotangent complex is K-flat with flat
terms, so its derived pullback is computed degreewise (Tag 06YY), and degreewise pullback along
the change of coefficient rings is extension of scalars. -/
@[stacks 08SZ "the first vertex: `L_{B/A} ⊗^L_B D`, the derived pullback along `h : B ⟶ D` of
the cotangent complex, is the class of its degreewise base change, the first vertex of the
triangle of `CategoryTheory.Sheaf.exists_distTriang_towerCotangent`; on any site"]
def baseChangedCotangentComplexDerivedIso :
    (towerDerivedBaseChange.{u, v, w} J h).obj
        (DerivedCategory.Q.obj (cotangentComplex.{u, v, w} J g)) ≅
      DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h) :=
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app
    (coefficientMorphism.{max u v w} J h)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ({ C := C, J := J, O := B } : AlgebraicGeometry.RingedTopos.{v, u, max u v w})))
    (fun N ↦ by
      obtain ⟨K, hK, t, ht⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
          (Y := ({ C := C, J := J, O := B } : AlgebraicGeometry.RingedTopos.{v, u, max u v w})) N
      exact ⟨K, hK, t, ht⟩)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
      (coefficientMorphism.{max u v w} J h))
    _ (isKFlat_cotangentComplex' J g)
  (towerDerivedBaseChange.{u, v, w} J h).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
    asIso ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison
      (coefficientMorphism.{max u v w} J h)).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (cotangentComplex.{u, v, w} J g))) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso (baseChangedCotangentComplexPullbackIso J g h)

end DerivedBaseChange

end CategoryTheory.Sheaf
