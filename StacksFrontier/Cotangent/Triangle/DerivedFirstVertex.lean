module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Triangulated.DistinguishedOfIso
public import StacksFrontier.Cotangent.DerivedBaseChange
public import StacksFrontier.Cotangent.Triangle.Distinguished
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# The derived base change as the first vertex of the cotangent triangle

For an injective map `f : B ⟶ C` of commutative `A`-algebras,
`StacksFrontier/Cotangent/Triangle/Distinguished.lean` produces a distinguished triangle in
`D(ModuleCat C)` whose first vertex is the *degreewise* extension of scalars along `f` of the
cotangent simplicial module of `B` over `A`, whose middle vertex is `L_{C/A}`, and whose third
vertex is the complex of the base-changed relative differentials.

This file upgrades the first vertex to the genuine derived base change: the triangle reads
`L_{B/A} ⊗ᴸ_B C → L_{C/A} → (third vertex) → (L_{B/A} ⊗ᴸ_B C)[1]`.

## Main definitions

* `ComplexShape.Embedding.extendFunctorCompMapHomologicalComplexIso`: applying an additive
  functor degreewise commutes with extension of a complex by zero along an embedding of complex
  shapes, read as an isomorphism of functors.
* `AlgebraicTopology.alternatingFaceMapCochainComplexCompMapHomologicalComplexIso`: an additive
  functor applied degreewise to a simplicial object commutes with the reindexed alternating face
  map complex.

## Main results

* `CommAlgCat.nonempty_derivedExtensionScalars_cotangentTriangle_obj₁_iso`: the first vertex of
  the triangle of Tag 08SD is isomorphic to the derived base change
  `L_{B/A} ⊗ᴸ_B C` of the cotangent complex of `B` over `A`.
* `CommAlgCat.exists_distinguished_derivedBaseChange_cotangentTriangle`: the triangle of Tag 08SD
  can therefore be presented with the derived base change as its first vertex.

## Implementation notes

The first vertex of the triangle of Tag 08SD is the reindexed alternating face map complex *of*
the degreewise extended simplicial module, while `CommAlgCat.cotangentComplex` base changed is
the degreewise extension of scalars *of* the reindexed alternating face map complex. The two
agree because extension of scalars is additive. Mathlib's
`AlgebraicTopology.map_alternatingFaceMapComplex` is exactly that statement before reindexing;
what is missing, and is supplied here, is the corresponding commutation with the extension
functor of an embedding of complex shapes. Extension by zero does not commute with an additive
functor on the nose — `F.obj 0` is only *a* zero object — so the comparison is an isomorphism and
not an equality, in contrast to the unreindexed statement.

With that comparison in hand, the degreewise first vertex is identified with the derived base
change by `CommAlgCat.nonempty_derivedExtensionScalars_cotangentComplex_iso`, which rests on the
freeness of the terms of the cotangent complex, and the triangle is transported along the
resulting isomorphism by `CategoryTheory.Pretriangulated.isomorphic_distinguished`.

The `Algebra B C` structure used by the derived base change is the one induced by `f`; its
`algebraMap` is `f.hom.toRingHom`, which is how the statements below spell it, so that no
instance has to be assumed on `B` and `C` beyond the morphism `f` itself.

### Relation to `@[stacks 08QX]`

As in `StacksFrontier/Cotangent/Triangle/Distinguished.lean`, this is not yet Tag 08QX: `f` is
still assumed injective here, and the third vertex is still the complex of the base-changed
resolution. The one discrepancy of the three that is removed here is the third one listed
there, namely that the first vertex was the degreewise rather than the derived extension of
scalars. The other two are removed in
`StacksFrontier/Cotangent/Triangle/BaseChangeLegTensor.lean` and
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, and Tag 08QX for arbitrary ring maps
`A → B → C` is `CommAlgCat.productFundamentalTriangle_distinguished` of the latter.

## References

* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicTopology Opposite Simplicial

universe u v wB wC

namespace ComplexShape.Embedding

/-- **Applying an additive functor degreewise commutes with the extension functor** of an
embedding of complex shapes. This is `Stacks.DerivedIndexing.mapExtendNatIsoSymm`, for a functor
that is additive rather than merely preserving of zero morphisms. -/
def extendFunctorCompMapHomologicalComplexIso {V W : Type*} [Category* V] [Category* W]
    [Preadditive V] [Preadditive W] [HasZeroObject V] [HasZeroObject W] {ι ι' : Type*}
    {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') (F : V ⥤ W) [F.Additive] :
    e.extendFunctor V ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor W :=
  Stacks.DerivedIndexing.mapExtendNatIsoSymm F e

end ComplexShape.Embedding

namespace AlgebraicTopology

/-- **An additive functor commutes with the reindexed alternating face map complex.** Applying
`F` degreewise to a simplicial object and then forming the reindexed alternating face map complex
of `AlgebraicTopology.alternatingFaceMapCochainComplex` gives the same result, up to a canonical
isomorphism, as forming that complex first and then applying `F` degreewise.

Before reindexing this is the equality `AlgebraicTopology.map_alternatingFaceMapComplex` of
Mathlib; the reindexing contributes the isomorphism
`ComplexShape.Embedding.extendFunctorCompMapHomologicalComplexIso`. -/
def alternatingFaceMapCochainComplexCompMapHomologicalComplexIso {V W : Type*} [Category* V]
    [Category* W] [Preadditive V] [Preadditive W] [HasZeroObject V] [HasZeroObject W]
    (F : V ⥤ W) [F.Additive] :
    alternatingFaceMapCochainComplex V ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (SimplicialObject.whiskering V W).obj F ⋙ alternatingFaceMapCochainComplex W :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (alternatingFaceMapComplex V)
      ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctorCompMapHomologicalComplexIso F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (map_alternatingFaceMapComplex F))
      ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor W) ≪≫
    Functor.associator _ _ _

end AlgebraicTopology

namespace CommAlgCat

/-- **The first vertex of the triangle of Tag 08SD is the derived base change of `L_{B/A}`.**

For an injective map `f : B ⟶ C` of `A`-algebras, the first vertex of
`CommAlgCat.cotangentTriangle` — the reindexed alternating face map complex of the degreewise
extension of scalars of the cotangent simplicial module — is isomorphic to
`L_{B/A} ⊗ᴸ_B C`, the image of `L_{B/A}` under derived extension of scalars along `f`. -/
theorem nonempty_derivedExtensionScalars_cotangentTriangle_obj₁_iso (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
    [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    Nonempty
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            f.hom.toRingHom).functor.obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, v} A B)) ≅
        (cotangentTriangle A f hf).obj₁) := by
  let : Algebra (B : Type (max u v)) (C : Type (max u v)) := f.hom.toRingHom.toAlgebra
  let : (ModuleCat.extendScalars.{max u v, max u v, max u v} f.hom.toRingHom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v, max u v, max u v}
      f.hom.toRingHom).left_adjoint_additive
  obtain ⟨e⟩ := nonempty_derivedExtensionScalars_cotangentComplex_iso.{u, v, wB, wC} A
    (B : Type (max u v)) (C : Type (max u v))
  exact ⟨e ≪≫ DerivedCategory.Q.mapIso
    ((alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
      (ModuleCat.extendScalars f.hom.toRingHom)).app (cotangentSimplicialModule A B).object)⟩

/-- **Stacks Project, Tag 08SD, with the derived base change as first vertex.**

For an injective map `f : B ⟶ C` of `A`-algebras there is a distinguished triangle in
`D(ModuleCat C)`
`L_{B/A} ⊗ᴸ_B C → L_{C/A} → (third vertex of CommAlgCat.cotangentTriangle) → (L_{B/A} ⊗ᴸ_B C)[1]`
whose first vertex is literally the derived base change of `L_{B/A}` along `f`, whose second
vertex is `L_{C/A}` and whose third vertex is the third vertex of
`CommAlgCat.cotangentTriangle`, the complex of the base-changed relative differentials.

This statement leaves the third vertex as the complex of base-changed relative differentials. Its
identification with `L_{C/B}`, and the passage to arbitrary `A → B → C` through `B × C` and Tag
08SC, are the two paragraphs of Remark 08SD stated whole in
`StacksFrontier/Cotangent/Triangle/BaseChangedResolutionTriangle.lean`:
`CommAlgCat.fundamentalTriangle_of_injective` and
`CommAlgCat.fundamentalTriangle_of_productDescent`. -/
@[stacks 08SD "differential_sequence triangle, derived first vertex"]
theorem exists_distinguished_derivedBaseChange_cotangentTriangle (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
    [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    ∃ (α : (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            f.hom.toRingHom).functor.obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, v} A B)) ⟶
        DerivedCategory.Q.obj (cotangentComplex.{u, v} A C))
      (β : DerivedCategory.Q.obj (cotangentComplex.{u, v} A C) ⟶
        (cotangentTriangle A f hf).obj₃)
      (δ : (cotangentTriangle A f hf).obj₃ ⟶
        ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            f.hom.toRingHom).functor.obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, v} A B)))⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang (DerivedCategory (ModuleCat.{max u v} C)) := by
  obtain ⟨e⟩ := nonempty_derivedExtensionScalars_cotangentTriangle_obj₁_iso.{u, v, wB, wC} A f hf
  let e₂ : DerivedCategory.Q.obj (cotangentComplex.{u, v} A C) ≅
      (cotangentTriangle A f hf).obj₂ := eqToIso (cotangentTriangle_obj₂ A f hf).symm
  refine ⟨e.hom ≫ (cotangentTriangle A f hf).mor₁ ≫ e₂.inv,
    e₂.hom ≫ (cotangentTriangle A f hf).mor₂, ?_⟩
  exact exists_distinguished_of_iso _ _ _ (cotangentTriangle_distinguished A f hf) e e₂
    (Iso.refl _) (by simp) (by simp)

end CommAlgCat

end
