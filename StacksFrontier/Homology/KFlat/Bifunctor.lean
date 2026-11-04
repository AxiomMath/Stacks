module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# K-flatness relative to an additive bifunctor

Let `A`, `B` and `D` be additive categories with binary biproducts and a zero object, with
`D` abelian, and let `F : A ⥤ B ⥤ D` be a bifunctor which is additive in each variable and
for which the total complexes `Tot(F(K₁, K₂))` of cochain complexes exist.  A cochain
complex `K` of objects of `B` is *K-flat for `F`* when `Tot(F(G, K))` is acyclic for every
acyclic cochain complex `G` of objects of `A`.

This is the shape of K-flatness that the Stacks project uses on a ringed site `(C, O)`: there
`A = B = D = Mod(O)` and `F = ⊗_O` is `Stacks.SheafOfModules.Tensor.sheafTensor`, so `Tot(F(G, K))`
  is
`Stacks.SheafOfModules.Tensor.tensorComplex` and the predicate is Stacks Tag 06YN.  Nothing in the
  two-out-of
-three property below uses more than additivity of `F`, which is why it is proved here once for
an arbitrary bifunctor.

## Main definitions

* `CochainComplex.KFlatBifunctor.KFlat`: K-flatness of a complex relative to `F`.

## Main results

* `CochainComplex.KFlatBifunctor.kFlat_obj₁_of_distTriang`,
  `CochainComplex.KFlatBifunctor.kFlat_obj₂_of_distTriang`,
  `CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang`: the two-out-of-three property of
  K-flatness in a distinguished triangle of `K(B)`, one implication per vertex.
* `CochainComplex.KFlatBifunctor.acyclic_mappingCone_of_kFlat`,
  `CochainComplex.KFlatBifunctor.quasiIso_of_kFlat`: `Tot(F(-, K))` for a K-flat `K` takes a
  morphism with acyclic mapping cone to one with acyclic mapping cone, hence preserves
  quasi-isomorphisms.

## Implementation notes

The three vertices of the triangle are given as cochain complexes rather than as objects of
`K(B)`, because the objects of the homotopy category are definitionally those complexes and
this is the form in which the Stacks statement is applied.

The proof applies the functor `Φ_G = Tot(F(G, -)) : K(B) ⥤ K(D)` for a fixed acyclic `G` to
the triangle.  That `Φ_G` is an exact functor of triangulated categories is
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated` (Stacks Tag 0G6E), relative to
  the
commutation-with-shift datum `Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi`.  By
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors`, the vertex `Φ_G(K ᵢ)` of the image
  triangle is
isomorphic to the image in `K(D)` of `Tot(F(G, Kᵢ))`, so K-flatness of a vertex is exactly the
statement that the corresponding vertex of the image triangle lies in
`HomotopyCategory.subcategoryAcyclic D`.  The three implications are then the three closure
properties `ObjectProperty.ext_of_isTriangulatedClosed₁`, `₂`, `₃` of that triangulated
subcategory.

## References

* [The Stacks Project, Tag 07A3](https://stacks.math.columbia.edu/tag/07A3)
* [The Stacks Project, Tag 0G6E](https://stacks.math.columbia.edu/tag/0G6E)
-/

open CategoryTheory CategoryTheory.Limits Pretriangulated

noncomputable section

namespace CochainComplex.KFlatBifunctor

/-- A morphism of cochain complexes in an abelian category is a quasi-isomorphism exactly when
its mapping cone is acyclic: the two conditions are the two readings of the distinguished
mapping-cone triangle against the triangulated subcategory of acyclic objects. -/
theorem quasiIso_iff_acyclic_mappingCone {E : Type*} [Category E] [Abelian E]
    {K L : CochainComplex E ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic E).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

section Triangle

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [HasZeroObject B] [HasBinaryBiproducts B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- `Tot(F(K₁, K₂))`, the total complex of the double complex `(p, q) ↦ F(K₁ᵖ, K₂ᑫ)` built
with the Koszul sign convention.  This is `Functor.map₂HomologicalComplex` applied to `F`. -/
@[ega "0 11.3.1" "special case", sga "4 XVII 1.1.6" "special case"]
abbrev totalComplex (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ) : CochainComplex D ℤ :=
  ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj K₁).obj K₂

/-- A cochain complex `K` of objects of `B` is **K-flat for `F`** when the total complex
`Tot(F(G, K))` is acyclic for every acyclic cochain complex `G` of objects of `A`.  For
`F = ⊗_O` on a ringed site this is Stacks Tag 06YN. -/
def KFlat (K : CochainComplex B ℤ) : Prop :=
  ∀ G : CochainComplex A ℤ, G.Acyclic → (totalComplex F G K).Acyclic

omit [HasZeroObject B] [HasBinaryBiproducts B] in
/-- The image in `K(D)` of the total complex `Tot(F(G, K))` is acyclic exactly when the vertex
`Φ_G(K)` of `K(D)` obtained by applying the descended functor to the image of `K` is: the two
objects are isomorphic by `Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors`. -/
theorem mem_subcategoryAcyclic_bifunctorPhi_iff
    (G : CochainComplex A ℤ) (K : CochainComplex B ℤ) :
    HomotopyCategory.subcategoryAcyclic D
        ((Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F G).obj
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K)) ↔
      (totalComplex F G K).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact (HomotopyCategory.subcategoryAcyclic D).prop_iff_of_iso
    ((Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors F G).app K)

/-- The image under `Φ_G` of a distinguished triangle of `K(B)` is a distinguished triangle of
`K(D)`, by Stacks Tag 0G6E. -/
theorem bifunctorPhi_mapTriangle_distinguished (G : CochainComplex A ℤ)
    (T : Triangle (HomotopyCategory B (ComplexShape.up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory B (ComplexShape.up ℤ))) :
    letI := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F G
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F G).mapTriangle.obj T ∈
      distTriang (HomotopyCategory D (ComplexShape.up ℤ)) := by
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F G
  have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated F G
  exact (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F G).map_distinguished T hT

variable {K₁ K₂ K₃ : CochainComplex B ℤ}

/-- In a distinguished triangle of `K(B)`, the first vertex is K-flat for `F` if the second and
third are. -/
theorem kFlat_obj₁_of_distTriang
    (f : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₁ ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂)
    (g : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂ ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₃)
    (h : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₃ ⟶
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (HomotopyCategory B (ComplexShape.up ℤ)))
    (h₂ : KFlat F K₂) (h₃ : KFlat F K₃) : KFlat F K₁ := by
  intro G hG
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F G
  refine (mem_subcategoryAcyclic_bifunctorPhi_iff F G K₁).1
    (ObjectProperty.ext_of_isTriangulatedClosed₁ _ _
      (bifunctorPhi_mapTriangle_distinguished F G _ hT) ?_ ?_)
  · exact (mem_subcategoryAcyclic_bifunctorPhi_iff F G K₂).2 (h₂ G hG)
  · exact (mem_subcategoryAcyclic_bifunctorPhi_iff F G K₃).2 (h₃ G hG)

/-- In a distinguished triangle of `K(B)`, the second vertex is K-flat for `F` if the first and
third are. -/
theorem kFlat_obj₂_of_distTriang
    (f : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₁ ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂)
    (g : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂ ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₃)
    (h : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₃ ⟶
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (HomotopyCategory B (ComplexShape.up ℤ)))
    (h₁ : KFlat F K₁) (h₃ : KFlat F K₃) : KFlat F K₂ := by
  intro G hG
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F G
  refine (mem_subcategoryAcyclic_bifunctorPhi_iff F G K₂).1
    (ObjectProperty.ext_of_isTriangulatedClosed₂ _ _
      (bifunctorPhi_mapTriangle_distinguished F G _ hT) ?_ ?_)
  · exact (mem_subcategoryAcyclic_bifunctorPhi_iff F G K₁).2 (h₁ G hG)
  · exact (mem_subcategoryAcyclic_bifunctorPhi_iff F G K₃).2 (h₃ G hG)

/-- In a distinguished triangle of `K(B)`, the third vertex is K-flat for `F` if the first and
second are. -/
theorem kFlat_obj₃_of_distTriang
    (f : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₁ ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂)
    (g : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂ ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₃)
    (h : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₃ ⟶
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (HomotopyCategory B (ComplexShape.up ℤ)))
    (h₁ : KFlat F K₁) (h₂ : KFlat F K₂) : KFlat F K₃ := by
  intro G hG
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F G
  refine (mem_subcategoryAcyclic_bifunctorPhi_iff F G K₃).1
    (ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
      (bifunctorPhi_mapTriangle_distinguished F G _ hT) ?_ ?_)
  · exact (mem_subcategoryAcyclic_bifunctorPhi_iff F G K₁).2 (h₁ G hG)
  · exact (mem_subcategoryAcyclic_bifunctorPhi_iff F G K₂).2 (h₂ G hG)

end Triangle

section MappingCone

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Preadditive B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- `Tot(F(-, K))` for a complex `K` which is K-flat for `F` takes a morphism with acyclic
mapping cone to a morphism with acyclic mapping cone.  The cone of the image is the image of
the cone, by `Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR`, and the cone of the
  original
morphism is acyclic, so K-flatness applies to it. -/
theorem acyclic_mappingCone_of_kFlat (K : CochainComplex B ℤ) (hK : KFlat F K)
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y)
    (hf : (CochainComplex.mappingCone f).Acyclic) :
    (CochainComplex.mappingCone
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).map f).app K)).Acyclic := by
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hK (CochainComplex.mappingCone f) hf n)
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR F K f)

/-- **The total tensor product with a K-flat complex preserves quasi-isomorphisms.**  A
quasi-isomorphism is a morphism with acyclic mapping cone, and `acyclic_mappingCone_of_kFlat`
preserves that property. -/
theorem quasiIso_of_kFlat (K : CochainComplex B ℤ) (hK : KFlat F K)
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).map f).app K) :=
  (quasiIso_iff_acyclic_mappingCone _).2
    (acyclic_mappingCone_of_kFlat F K hK f ((quasiIso_iff_acyclic_mappingCone f).1 hf))

end MappingCone

end CochainComplex.KFlatBifunctor

end
