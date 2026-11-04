module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.TensorProduct
public import StacksFrontier.Cotangent.Triangle.Distinguished

/-!
# The first vertex of the differential sequence triangle is a derived base change

Let `A → B → C` be ring maps with `B → C` injective. The triangle
`CommAlgCat.cotangentTriangle` of Tag 08SD has for its first vertex the complex of `C`-modules
obtained from the cotangent simplicial module of `B` over `A` by extending scalars along `B → C`
in each simplicial degree. This complex is the degreewise extension of scalars of the cotangent
complex `L_{B/A}`, and hence, the terms of `L_{B/A}` being projective `B`-modules, the derived
base change `L_{B/A} ⊗^L_B C`, which is the first vertex of the fundamental triangle of
Proposition 08QX.

## Main definitions

* `CommAlgCat.cotangentDifferentialComplexesX₁Iso`: the first term of the short complex of
  cochain complexes of Tag 08SD is the degreewise extension of scalars along `B → C` of
  `L_{B/A}`.
* `CommAlgCat.cotangentTriangle_obj₁DerivedBaseChangeIso`: the first vertex of the triangle of
  Tag 08SD is `L_{B/A} ⊗^L_B C` in `D(C)`.

## References

* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicTopology Opposite Simplicial

universe t u v w

namespace CommAlgCat

/-- **The first term of the differential short complex of Tag 08SD is the degreewise extension
of scalars of `L_{B/A}`.** Both are extensions along `ComplexShape.embeddingUpIntLE 0`: the
left-hand side of the alternating face map complex of the cotangent simplicial module of `B`
over `A` with scalars extended along `f` in each simplicial degree, the right-hand side of the
same complex with scalars extended afterwards. -/
noncomputable def cotangentDifferentialComplexesX₁Iso (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    (cotangentDifferentialComplexes A f).X₁ ≅
      ((ModuleCat.extendScalars f.hom.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex A B) :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{max u v} C)).mapIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso
        (ModuleCat.extendScalars f.hom.toRingHom)).app
          (cotangentSimplicialModule A B).object).symm ≪≫
    HomologicalComplex.mapHomologicalComplexExtendIso
      (ModuleCat.extendScalars f.hom.toRingHom)
      ((alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
        (cotangentSimplicialModule A B).object)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))

attribute [local instance] cotangentComplex_isStrictlyLE_zero projective_cotangentComplex_X

/-- **The first vertex of the triangle of Tag 08SD is the derived base change
`L_{B/A} ⊗^L_B C`**, the first vertex of the fundamental triangle of Proposition 08QX. -/
noncomputable def cotangentTriangle_obj₁DerivedBaseChangeIso (A : Type u) [CommRing A]
    {B C : CommAlgCat.{u} A} [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{t} (ModuleCat.{u} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    (cotangentTriangle A f hf).obj₁ ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
        f.hom.toRingHom).functor.obj (cotangentComplexDerived A B) :=
  have h := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
    f.hom.toRingHom).comparison_isIso_of_projective (cotangentComplex.{u, u} A B) 0
  DerivedCategory.Q.mapIso (cotangentDifferentialComplexesX₁Iso A f) ≪≫
    (@asIso _ _ _ _ _ h).symm

end CommAlgCat

end
