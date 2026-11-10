module

public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.AugmentedAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CohomologyZeroCanonical
public import StacksFrontier.CategoryTheory.Sites.Simplicial.VanishingCohomology

/-!
# The free abelian complex of a locally covering augmented simplicial presheaf is a resolution

Let `(C, J)` be a small site and let `A` be an augmented simplicial presheaf of sets on `C` whose
degree-zero augmentation, relation map and matching maps are locally surjective — the three
hypotheses of Stacks 01GE. Stacks 01GE says that the homology sheaves of the complex
`s(ℤ_A^♯)` of free abelian sheaves vanish in positive degrees and that the degree-zero one is
the free abelian sheaf `ℤ_{A.right}^♯` on the presheaf of augmentation points. This module
assembles those two statements into the single statement they amount to: the canonical
augmentation

`s(ℤ_A^♯) ⟶ ℤ_{A.right}^♯[0]`

is a quasi-isomorphism of complexes of abelian sheaves, so `s(ℤ_A^♯)` is a resolution of
`ℤ_{A.right}^♯`.

With that in hand `CochainComplex.quasiIso_resolutionToProductTotal` applies, so the Hom complex
out of `ℤ_{A.right}^♯` into a K-injective complex `I` is computed by the product total complex of
`Hom(ℤ_{A_p}^♯, I^q)` with no boundedness hypothesis, which is the unbounded form of the
comparison of Stacks 01GY.

## Main definitions

* `CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafResolutionAugmentation`: the
  augmentation `s(ℤ_A^♯) ⟶ ℤ_{A.right}^♯[0]`, as a morphism of chain complexes.

## Main results

* `CategoryTheory.SimplicialObject.Augmented.quasiIso_freeAbelianSheafResolutionAugmentation`:
  under the three local surjectivity hypotheses, the augmentation is a quasi-isomorphism.

## Implementation notes

The augmentation is built from `freeAbelianSheafAugZero` by `ChainComplex.toSingle₀Equiv` rather
than taken to be `freeAbelianSheafAugmentation`, whose degree-zero component is
`freeAbelianSheafAugZero` only after the canonical identification
`HomologicalComplex.singleObjXSelf`; the two agree, and
`freeAbelianSheafResolutionAugmentation_f_zero` records the degree-zero component of the one used
here.

Quasi-isomorphy in degree zero is `ShortComplex.exact_of_g_is_cokernel` and
`CategoryTheory.Limits.epi_of_isColimit_cofork` applied to
`isColimitCokernelCoforkFreeAbelianSheafAugZero`, which is the degree-zero half of Stacks 01GE in
its canonical-map form and needs only the first two of the three hypotheses. In positive degrees
it is the vanishing of the homology sheaves, read as exactness through
`HomologicalComplex.exactAt_iff_isZero_homology`, against exactness of the complex concentrated
in degree zero.

The passage from a resolution to the Hom complex out of the object resolved is not repeated here:
it is `CochainComplex.quasiIso_resolutionToProductTotal`, stated for an arbitrary resolution in an
arbitrary abelian category.

## References

* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
* [Stacks Project, Tag 01GB](https://stacks.math.columbia.edu/tag/01GB)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialObject.Augmented

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type u))

/-- The augmentation of the complex `s(ℤ_A^♯)` of free abelian sheaves towards the free abelian
sheaf on the presheaf of augmentation points, placed in degree zero. -/
def freeAbelianSheafResolutionAugmentation :
    (SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left ⟶
      (ChainComplex.single₀ (Sheaf J AddCommGrpCat.{u})).obj
        ((Presheaf.freeAbelianSheaf J).obj A.right) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨freeAbelianSheafAugZero J A, d_comp_freeAbelianSheafAugZero J A 1⟩

/-- The degree-zero component of `freeAbelianSheafResolutionAugmentation` is
`freeAbelianSheafAugZero`. -/
@[simp]
lemma freeAbelianSheafResolutionAugmentation_f_zero :
    (freeAbelianSheafResolutionAugmentation J A).f 0 = freeAbelianSheafAugZero J A := by
  simp [freeAbelianSheafResolutionAugmentation]

/-- For an augmented simplicial presheaf whose degree-zero augmentation, relation map and matching
maps are locally surjective, the augmentation `freeAbelianSheafResolutionAugmentation` is a
quasi-isomorphism, so the complex `s(ℤ_A^♯)` of free abelian sheaves is a resolution of the free
abelian sheaf on the presheaf of augmentation points. -/
theorem quasiIso_freeAbelianSheafResolutionAugmentation
    (h₀ : Presheaf.IsLocallySurjective J (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A))
    (hm : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app A.left).app
        (op (SimplexCategory.mk (n + 1))))) :
    QuasiIso (freeAbelianSheafResolutionAugmentation J A) := by
  refine ⟨fun n => ?_⟩
  match n with
  | 0 =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · rw [ShortComplex.exact_and_epi_g_iff_g_is_cokernel]
      refine ⟨IsColimit.ofIsoColimit (isColimitCokernelCoforkFreeAbelianSheafAugZero J A h₀ h₁)
        (Cofork.ext (Iso.refl _) ?_)⟩
      change freeAbelianSheafAugZero J A ≫ 𝟙 _ =
        (freeAbelianSheafResolutionAugmentation J A).f 0
      simp
    all_goals rfl
  | (n + 1) =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact isZero_sheafHomology_of_isLocallySurjective_matchingMaps J A h₀ h₁ hm (n + 1)
        (by omega)
    · exact ChainComplex.exactAt_succ_single_obj _ _

end CategoryTheory.SimplicialObject.Augmented

end
