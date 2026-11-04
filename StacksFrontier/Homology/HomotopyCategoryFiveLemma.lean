module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Four and five lemmas for distinguished triangles in the homotopy category

Let `C` be an abelian category and let `φ : S ⟶ T` be a morphism of distinguished triangles in
the homotopy category of cochain complexes in `C`. Each of the two triangles has a long exact
cohomology sequence, and `φ` induces a morphism between them. Splicing those sequences into
exact `CategoryTheory.ComposableArrows` and applying the four and five lemmas for an abelian
category reads off `Hⁱ(φ₃)` from `Hⁱ(φ₁)`, `Hⁱ(φ₂)` and their counterparts in degree `i + 1`.

Mapping cones are the main source of such morphisms. If
```
P --γ--> E
|        |
α        β
v        v
A --f--> B
```
is a square of cochain complexes commuting up to a homotopy `H`, then
`CochainComplex.mappingCone.mapOfHomotopy` turns `H` into a morphism
`mappingCone γ ⟶ mappingCone f` and `CochainComplex.mappingCone.trianglehMapOfHomotopy` turns it
into a morphism of the two mapping-cone triangles. The last two results say in which degrees that
map of cones is an isomorphism, resp. an epimorphism, on cohomology, in terms of the degrees in
which `α` and `β` are.

These are the homological input of [Stacks, Tag 08CD], stated for an arbitrary abelian category.

## Main results

* `CategoryTheory.isIso_homology_of_homotopyTriangleMorphism`: the four lemma for a morphism of
  distinguished triangles in the homotopy category.
* `CategoryTheory.epi_homology_of_homotopyTriangleMorphism`: the surjectivity half of the five
  lemma for such a morphism.
* `CategoryTheory.isIso_homologyMap_mappingCone_of_homotopy` and
  `CategoryTheory.epi_homologyMap_mappingCone_of_homotopy`: the same two statements for the map of
  mapping cones induced by a homotopy-commutative square, phrased with
  `HomologicalComplex.homologyMap`.

## Implementation notes

The exact rows are assembled from `CategoryTheory.Functor.homologySequence_exact₁`,
`homologySequence_exact₂` and `homologySequence_exact₃` with
`CategoryTheory.ComposableArrows.exact_of_δ₀`. The commutativity conditions that the
`ComposableArrows.homMk` constructors ask for are the naturality squares of the connecting
morphism and of the two maps of the triangles; each is opened with `change` to a pair of
composites of functor images, because as `homMk` states it the goal mentions the arrows of the
`ComposableArrows` rather than the functor applications they are made of.

Passing between `HomologicalComplex.homologyMap` and the homotopy category is
`HomotopyCategory.homologyFunctorFactors`, through `CategoryTheory.NatIso.isIso_map_iff` for the
isomorphism hypotheses and through the arrow isomorphism that natural isomorphism provides,
against `CategoryTheory.MorphismProperty.epimorphisms` and
`CategoryTheory.MorphismProperty.monomorphisms`, for the epimorphism and monomorphism ones.

## References

* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- The cohomology sequence of a distinguished triangle is exact at the two spots around
the connecting morphism from degree `i` to degree `i + 1`. -/
private theorem exact_mk₃_homologySequence
    {S : Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hS : S ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C) (i : ℤ) :
    (ComposableArrows.mk₃ ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map S.mor₂)
      ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ S i (i + 1)
        rfl)
      ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (i + 1)).map S.mor₁)).Exact :=
  ComposableArrows.exact_of_δ₀
    ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequence_exact₃
      S hS i (i + 1) rfl).exact_toComposableArrows
    ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequence_exact₁
      S hS i (i + 1) rfl).exact_toComposableArrows

/-- **The four lemma for a morphism of distinguished triangles in the homotopy category.** In a
fixed degree `i`, cohomology of the third component is an isomorphism when cohomology of the
first component is an epimorphism in degree `i` and an isomorphism in degree `i + 1`, and
cohomology of the second component is an isomorphism in degree `i` and a monomorphism in degree
`i + 1`.

The two long exact cohomology sequences of the triangles supply the two exact rows and `φ`
supplies the morphism between them. This is part of the homological input of Stacks 08CD. -/
public theorem isIso_homology_of_homotopyTriangleMorphism
    {S T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hS : S ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C)
    (hT : T ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C)
    (φ : S ⟶ T) (i : ℤ)
    (h1 : Epi ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map φ.hom₁))
    (h2 : IsIso ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map φ.hom₂))
    (h1' : IsIso ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (i + 1)).map φ.hom₁))
    (h2' : Mono ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (i + 1)).map φ.hom₂)) :
    IsIso ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map φ.hom₃) := by
  let F := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  let G := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i
  let G' := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (i + 1)
  let rowS : ComposableArrows C 4 :=
    ComposableArrows.mk₄ (G.map S.mor₁) (G.map S.mor₂) (F.homologySequenceδ S i (i + 1) rfl)
      (G'.map S.mor₁)
  let rowT : ComposableArrows C 4 :=
    ComposableArrows.mk₄ (G.map T.mor₁) (G.map T.mor₂) (F.homologySequenceδ T i (i + 1) rfl)
      (G'.map T.mor₁)
  have exS : rowS.Exact :=
    ComposableArrows.exact_of_δ₀ (F.homologySequence_exact₂ S hS i).exact_toComposableArrows
      (exact_mk₃_homologySequence hS i)
  have exT : rowT.Exact :=
    ComposableArrows.exact_of_δ₀ (F.homologySequence_exact₂ T hT i).exact_toComposableArrows
      (exact_mk₃_homologySequence hT i)
  let φ' : rowS ⟶ rowT :=
    ComposableArrows.homMk₄ (G.map φ.hom₁) (G.map φ.hom₂) (G.map φ.hom₃) (G'.map φ.hom₁)
      (G'.map φ.hom₂)
      (by
        show G.map S.mor₁ ≫ G.map φ.hom₂ = G.map φ.hom₁ ≫ G.map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
      (by
        show G.map S.mor₂ ≫ G.map φ.hom₃ = G.map φ.hom₂ ≫ G.map T.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
      (by
        show F.homologySequenceδ S i (i + 1) rfl ≫ G'.map φ.hom₁
          = G.map φ.hom₃ ≫ F.homologySequenceδ T i (i + 1) rfl
        exact (F.homologySequenceδ_naturality φ i (i + 1) rfl).symm)
      (by
        show G'.map S.mor₁ ≫ G'.map φ.hom₂ = G'.map φ.hom₁ ≫ G'.map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono exS exT φ' h1 h2 h1' h2'

/-- **The five lemma for a morphism of distinguished triangles in the homotopy category,
surjectivity half.** In a fixed degree `i`, cohomology of the third component is an epimorphism
when cohomology of the second component is an epimorphism in degree `i` and a monomorphism in
degree `i + 1`, and cohomology of the first component is an epimorphism in degree `i + 1`.

This is part of the homological input of Stacks 08CD. -/
public theorem epi_homology_of_homotopyTriangleMorphism
    {S T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hS : S ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C)
    (hT : T ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C)
    (φ : S ⟶ T) (i : ℤ)
    (h2 : Epi ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map φ.hom₂))
    (h1' : Epi ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (i + 1)).map φ.hom₁))
    (h2' : Mono ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (i + 1)).map φ.hom₂)) :
    Epi ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map φ.hom₃) := by
  let F := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  let G := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i
  let G' := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (i + 1)
  let rowS : ComposableArrows C 3 :=
    ComposableArrows.mk₃ (G.map S.mor₂) (F.homologySequenceδ S i (i + 1) rfl) (G'.map S.mor₁)
  let rowT : ComposableArrows C 3 :=
    ComposableArrows.mk₃ (G.map T.mor₂) (F.homologySequenceδ T i (i + 1) rfl) (G'.map T.mor₁)
  have exS : rowS.Exact := exact_mk₃_homologySequence hS i
  have exT : rowT.Exact := exact_mk₃_homologySequence hT i
  let φ' : rowS ⟶ rowT :=
    ComposableArrows.homMk₃ (G.map φ.hom₂) (G.map φ.hom₃) (G'.map φ.hom₁) (G'.map φ.hom₂)
      (by
        show G.map S.mor₂ ≫ G.map φ.hom₃ = G.map φ.hom₂ ≫ G.map T.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
      (by
        show F.homologySequenceδ S i (i + 1) rfl ≫ G'.map φ.hom₁
          = G.map φ.hom₃ ≫ F.homologySequenceδ T i (i + 1) rfl
        exact (F.homologySequenceδ_naturality φ i (i + 1) rfl).symm)
      (by
        show G'.map S.mor₁ ≫ G'.map φ.hom₂ = G'.map φ.hom₁ ≫ G'.map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
  exact Abelian.epi_of_epi_of_epi_of_mono φ' exS exT h2 h1' h2'

/-- A morphism property that respects isomorphisms holds for `Hⁱ` of a morphism of the
homotopy category coming from a map of complexes iff it holds for `homologyMap` of that map. -/
private theorem homologyFunctor_map_quotient_iff {P A : CochainComplex C ℤ} (W : MorphismProperty C)
    [W.RespectsIso] (g : P ⟶ A) (i : ℤ) :
    W ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g)) ↔
      W (HomologicalComplex.homologyMap g i) :=
  W.arrow_mk_iso_iff (Arrow.isoMk
    ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app P)
    ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app A)
    ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).hom.naturality g).symm)

variable [HasZeroObject C] {P E A B : CochainComplex C ℤ} {γ : P ⟶ E} {f : A ⟶ B}
  {α : P ⟶ A} {β : E ⟶ B}

/-- **Cohomology of the map of mapping cones induced by a homotopy-commutative square is an
isomorphism in degree `i`** when `Hⁱ(α)` is an epimorphism, `Hⁱ(β)` an isomorphism, `Hⁱ⁺¹(α)` an
isomorphism and `Hⁱ⁺¹(β)` a monomorphism.

This is the four lemma `CategoryTheory.isIso_homology_of_homotopyTriangleMorphism` applied to the
morphism of mapping-cone triangles induced by the homotopy, and is part of the homological input
of Stacks 08CD. -/
public theorem isIso_homologyMap_mappingCone_of_homotopy
    (H : Homotopy (γ ≫ β) (α ≫ f)) (i : ℤ)
    (hα : Epi (HomologicalComplex.homologyMap α i))
    (hβ : IsIso (HomologicalComplex.homologyMap β i))
    (hα' : IsIso (HomologicalComplex.homologyMap α (i + 1)))
    (hβ' : Mono (HomologicalComplex.homologyMap β (i + 1))) :
    IsIso (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.mapOfHomotopy H) i) := by
  exact (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i)
    (CochainComplex.mappingCone.mapOfHomotopy H)).mp
    (isIso_homology_of_homotopyTriangleMorphism
      (HomotopyCategory.mappingCone_triangleh_distinguished γ)
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (CochainComplex.mappingCone.trianglehMapOfHomotopy H) i
      ((homologyFunctor_map_quotient_iff (MorphismProperty.epimorphisms C) α i).mpr hα)
      ((homologyFunctor_map_quotient_iff (MorphismProperty.isomorphisms C) β i).mpr hβ)
      ((homologyFunctor_map_quotient_iff (MorphismProperty.isomorphisms C) α (i + 1)).mpr hα')
      ((homologyFunctor_map_quotient_iff (MorphismProperty.monomorphisms C) β (i + 1)).mpr hβ'))

/-- **Cohomology of the map of mapping cones induced by a homotopy-commutative square is an
epimorphism in degree `i`** when `Hⁱ(β)` is an epimorphism, `Hⁱ⁺¹(α)` an epimorphism and
`Hⁱ⁺¹(β)` a monomorphism.

This is the five lemma `CategoryTheory.epi_homology_of_homotopyTriangleMorphism` applied to the
morphism of mapping-cone triangles induced by the homotopy, and is part of the homological input
of Stacks 08CD. -/
public theorem epi_homologyMap_mappingCone_of_homotopy
    (H : Homotopy (γ ≫ β) (α ≫ f)) (i : ℤ)
    (hβ : Epi (HomologicalComplex.homologyMap β i))
    (hα' : Epi (HomologicalComplex.homologyMap α (i + 1)))
    (hβ' : Mono (HomologicalComplex.homologyMap β (i + 1))) :
    Epi (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.mapOfHomotopy H) i) := by
  exact (homologyFunctor_map_quotient_iff (MorphismProperty.epimorphisms C)
    (CochainComplex.mappingCone.mapOfHomotopy H) i).mp
    (epi_homology_of_homotopyTriangleMorphism
      (HomotopyCategory.mappingCone_triangleh_distinguished γ)
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (CochainComplex.mappingCone.trianglehMapOfHomotopy H) i
      ((homologyFunctor_map_quotient_iff (MorphismProperty.epimorphisms C) β i).mpr hβ)
      ((homologyFunctor_map_quotient_iff (MorphismProperty.epimorphisms C) α (i + 1)).mpr hα')
      ((homologyFunctor_map_quotient_iff (MorphismProperty.monomorphisms C) β (i + 1)).mpr hβ'))

end CategoryTheory

end
