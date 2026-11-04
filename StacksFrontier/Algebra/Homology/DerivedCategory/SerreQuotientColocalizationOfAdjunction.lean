module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KernelColocalization
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreQuotientDerivedPullbackAdjunction

/-!
# The colocalization of Stacks 07BA from a left adjoint with invertible unit

Let `A` be an abelian category, `𝒫` and `𝒜` weak Serre subcategories, and let
`G : D(A) ⥤ D'` be a triangulated functor whose kernel is exactly the complexes with cohomology in
`𝒫`, with a left adjoint `Lsh ⊣ G` whose unit is invertible and such that `Lsh ∘ G` preserves
`D_𝒜(A)`. Then every object `K` of `D_𝒜(A)` receives the counit `Lsh G K ⟶ K`, whose cone lies in
`D_{𝒫 ∩ 𝒜}(A)` and whose source is left orthogonal to `D_{𝒫 ∩ 𝒜}(A)`: the hypothesis
`DerivedCategoryB.HasColocalizations 𝒜 (𝒫 ⊓ 𝒜)` of the abstract form of **Stacks 07BE**.

This is the proof of **Stacks 07BA** — `E' = Lg_! g^* E` with `g` the flat-fppf morphism of
**Stacks 0788** — read in the form **Stacks 07BE** consumes; the triangle facts are those of
`DerivedCategory.KernelColocalization`.

## Main results

* `DerivedCategoryB.hasColocalizations_of_adjunction`.

## References

* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 07BE](https://stacks.math.columbia.edu/tag/07BE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategoryB

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (𝒮 𝒜 : ObjectProperty A)
  [𝒮.IsWeakSerreClass] [𝒜.IsWeakSerreClass]
  {D' : Type*} [Category D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  {G : DerivedCategory A ⥤ D'} [G.CommShift ℤ] [G.IsTriangulated]
  {Lsh : D' ⥤ DerivedCategory A} (adj : Lsh ⊣ G)

omit [𝒮.IsWeakSerreClass] in
/-- **The colocalization of Stacks 07BA**: if `G` kills exactly the complexes with cohomology in
`𝒮`, has a left adjoint with invertible unit, and `Lsh ∘ G` preserves `D_𝒜(A)`, then every object
of `D_𝒜(A)` is the target of a morphism with cone in `D_{𝒮 ∩ 𝒜}(A)` out of an object left
orthogonal to `D_{𝒮 ∩ 𝒜}(A)`, namely the counit `Lsh G K ⟶ K`. -/
theorem hasColocalizations_of_adjunction
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝒮 ((DerivedCategory.homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (hshriek : ∀ K, derivedCategoryB 𝒜 K → derivedCategoryB 𝒜 (Lsh.obj (G.obj K))) :
    HasColocalizations 𝒜 (𝒮 ⊓ 𝒜) := by
  intro K
  have hK' := hshriek K.obj K.property
  obtain ⟨P, b, c, hT⟩ := distinguished_cocone_triangle (adj.counit.app K.obj)
  have hP := DerivedCategory.KernelColocalization.derivedInter_obj₃_of_distTriang 𝒮 𝒜 adj hG
    hunit K.obj K.property hK' P b c hT
  refine ⟨⟨_, hK'⟩, ObjectProperty.homMk (adj.counit.app K.obj), ⟨P, b, c, hT, hP⟩, ?_⟩
  intro Y g hY
  exact ObjectProperty.hom_ext _
    (DerivedCategory.KernelColocalization.leftOrthogonal_obj_counit 𝒮 𝒜 adj hG K.obj g.hom hY)

end DerivedCategoryB
