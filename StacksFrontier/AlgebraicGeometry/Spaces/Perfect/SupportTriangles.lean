module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekSupport

/-!
# Supports in exact sequences and in distinguished triangles

Let `X` be an algebraic space over a scheme `S`.  The support of a sheaf on the small étale site of
`X` (Stacks 04KA) is read on the stalks at geometric points, and the stalk functor at a point of a
site is exact.  Hence in an exact sequence `A ⟶ B ⟶ C` of sheaves of abelian groups, or of
`𝒪_X`-modules, the support of `B` lies in the union of the supports of `A` and `C`.  Read on the
long exact cohomology sequence of a distinguished triangle `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` of `D(𝒪_X)`
this gives

* `supp Hⁱ(E₂) ⊆ supp Hⁱ(E₁) ∪ supp Hⁱ(E₃)`, and
* `supp Hⁱ(E₃) ⊆ supp Hⁱ(E₂) ∪ supp Hⁱ⁺¹(E₁)`.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_subset_union_of_exact`: the abelian statement.
* `AlgebraicGeometry.Space.supportOfSheaf_toSheaf_subset_union_of_exact`: the same for modules.
* `AlgebraicGeometry.Space.cohomologySupportedOn_obj₂_of_distinguished`: in a distinguished
  triangle the second object is supported on `T` if the other two are.
* `AlgebraicGeometry.Space.supportOfSheaf_homology_obj₃_subset`: the support of `Hⁱ` of the third
  object, through the connecting map.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CategoryTheory

/-- **A support function subadditive on exact sequences, read on the cohomology sequence of a
distinguished triangle**, at its second object. -/
theorem subset_union_homology_obj₂_of_distinguished {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {α : Type*} (supp : A → Set α)
    (hsupp : ∀ Sc : ShortComplex A, Sc.Exact → supp Sc.X₂ ⊆ supp Sc.X₁ ∪ supp Sc.X₃)
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A)) (i : ℤ) :
    supp ((DerivedCategory.homologyFunctor A i).obj T.obj₂) ⊆
      supp ((DerivedCategory.homologyFunctor A i).obj T.obj₁) ∪
        supp ((DerivedCategory.homologyFunctor A i).obj T.obj₃) :=
  hsupp _ (DerivedCategory.HomologySequence.exact₂ T hT i)

/-- **A support function subadditive on exact sequences, read on the cohomology sequence of a
distinguished triangle**, at its third object, through the connecting map. -/
theorem subset_union_homology_obj₃_of_distinguished {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {α : Type*} (supp : A → Set α)
    (hsupp : ∀ Sc : ShortComplex A, Sc.Exact → supp Sc.X₂ ⊆ supp Sc.X₁ ∪ supp Sc.X₃)
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A)) (i : ℤ) :
    supp ((DerivedCategory.homologyFunctor A i).obj T.obj₃) ⊆
      supp ((DerivedCategory.homologyFunctor A i).obj T.obj₂) ∪
        supp ((DerivedCategory.homologyFunctor A (i + 1)).obj T.obj₁) :=
  hsupp _ (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1))

end CategoryTheory

namespace AlgebraicGeometry.Space


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

include hF in
/-- **The support of the middle term of an exact sequence of abelian sheaves lies in the union of
the supports of the outer terms.**  At a geometric point outside both outer supports the stalks of
the outer terms vanish, and the stalk functor at a point of the small étale site is exact, so the
stalk of the middle term vanishes. -/
theorem supportOfSheaf_subset_union_of_exact
    (Sc : ShortComplex (Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u})) (hSc : Sc.Exact) :
    supportOfSheaf B S hS F Sc.X₂ ⊆
      supportOfSheaf B S hS F Sc.X₁ ∪ supportOfSheaf B S hS F Sc.X₃ := by
  intro y hy
  by_contra hyU
  rw [Set.mem_union, not_or] at hyU
  refine (notMem_supportOfSheaf_iff_forall_isZero_sheafFiber B S hS F hF _ y).2 ?_ hy
  intro p hp
  have h₁ := (notMem_supportOfSheaf_iff_forall_isZero_sheafFiber B S hS F hF _ y).1 hyU.1 p hp
  have h₃ := (notMem_supportOfSheaf_iff_forall_isZero_sheafFiber B S hS F hF _ y).1 hyU.2 p hp
  exact (hSc.map ((etaleSitePoint B S hS F p hF).sheafFiber (A := AddCommGrpCat.{u}))).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

attribute [local instance] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

/-- **The support of the middle term of an exact sequence of `𝒪_X`-modules lies in the union of
the supports of the outer terms.**  The forgetful functor to abelian sheaves is exact. -/
theorem supportOfSheaf_toSheaf_subset_union_of_exact
    (Sc : ShortComplex (Modules.{u, u} B S hS F hF)) (hSc : Sc.Exact) :
    supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          Sc.X₂) ⊆
      supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          Sc.X₁) ∪
      supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          Sc.X₃) := by
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) :=
    Stacks.SheafOfModules.toSheaf_preservesFiniteColimits _
  have : (SheafOfModules.toSheaf.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact supportOfSheaf_subset_union_of_exact B S hS F hF _ (hSc.map (SheafOfModules.toSheaf.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))))

attribute [local instance] HasDerivedCategory.standard

variable (T : Set (points B S hS F))
  (Tri : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF)))
  (hTri : Tri ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)))

include hTri in
/-- In a distinguished triangle, the support of `Hⁱ` of the second object lies in the union of
the supports of `Hⁱ` of the first and of the third. -/
theorem supportOfSheaf_homology_obj₂_subset (i : ℤ) :
    supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj Tri.obj₂)) ⊆
      supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj Tri.obj₁)) ∪
      supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj Tri.obj₃)) :=
  subset_union_homology_obj₂_of_distinguished
    (fun M => supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj M))
    (supportOfSheaf_toSheaf_subset_union_of_exact B S hS F hF) Tri hTri i

include hTri in
/-- In a distinguished triangle, the support of `Hⁱ` of the third object lies in the union of the
supports of `Hⁱ` of the second object and of `Hⁱ⁺¹` of the first. -/
theorem supportOfSheaf_homology_obj₃_subset (i : ℤ) :
    supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj Tri.obj₃)) ⊆
      supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj Tri.obj₂)) ∪
      supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) (i + 1)).obj Tri.obj₁)) :=
  subset_union_homology_obj₃_of_distinguished
    (fun M => supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj M))
    (supportOfSheaf_toSheaf_subset_union_of_exact B S hS F hF) Tri hTri i

include hTri in
/-- **In a distinguished triangle the second object is supported on `T` if the other two are.** -/
theorem cohomologySupportedOn_obj₂_of_distinguished
    (h₁ : CohomologySupportedOn B S hS F hF T Tri.obj₁)
    (h₃ : CohomologySupportedOn B S hS F hF T Tri.obj₃) :
    CohomologySupportedOn B S hS F hF T Tri.obj₂ := fun i =>
  (supportOfSheaf_homology_obj₂_subset B S hS F hF Tri hTri i).trans
    (Set.union_subset (h₁ i) (h₃ i))

end AlgebraicGeometry.Space

end
