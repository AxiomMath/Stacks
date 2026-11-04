module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FreeDirectImage
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence

/-!
# The twist `ℱ ↦ ℱ(d)` on `ℙⁿ_T` is an equivalence

For every scheme `T` and every `d ∈ ℤ`, tensoring with the invertible module `𝒪(d)` on
`ℙⁿ_T = ℙⁿ_ℤ ×_ℤ T` is an autoequivalence of the category of `𝒪_{ℙⁿ_T}`-modules (Stacks 0FFM (1)
for an invertible module). In particular it preserves and reflects monomorphisms, epimorphisms,
kernels and cokernels; this is how `Quot^P` reads a subobject `𝒦(m) ⊆ 𝒪^{⊕ r}(m)` back as a
subobject `𝒦 ⊆ 𝒪^{⊕ r}` in the proof of Stacks 0DPA.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isEquivalence_twistFunctor`: the twist is an equivalence.
* `AlgebraicGeometry.ProjectiveQuot.mono_of_mono_twistMap`,
  `AlgebraicGeometry.ProjectiveQuot.epi_of_epi_twistMap`,
  `AlgebraicGeometry.ProjectiveQuot.isIso_of_isIso_twistMap`: the twist reflects monomorphisms,
  epimorphisms and isomorphisms.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable (n : ℕ)

/-- **The twist `ℱ ↦ ℱ(d)` on `ℙⁿ_T` is an equivalence of categories**: `𝒪(d)` is invertible,
so tensoring on the left with it is an equivalence (Stacks 0FFN ⟹ 0FFM (1)), and tensoring on the
right is isomorphic to tensoring on the left through the braiding. -/
instance isEquivalence_twistFunctor (T : Scheme.{u}) (d : ℤ) :
    (twistFunctor n T d).IsEquivalence := by
  have hL : Stacks.SheafOfModules.IsInvertible (projectiveSpaceOver n T).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver n T))
      (twistingSheaf n T d) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n T d
        |>.toAlgebraicGeometry)
  have hE := (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ _).1 hL
  exact @Functor.isEquivalence_of_iso _ _ _ _ _ _
    (Stacks.SheafOfModules.sheafTensorRightIsoTensorLeftFunctor
      ⟨(projectiveSpaceOver n T).toSheafedSpace.presheaf,
        (projectiveSpaceOver n T).toSheafedSpace.IsSheaf⟩
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver n T))
      (twistingSheaf n T d)).symm hE

variable {n}

/-- The twist reflects monomorphisms. -/
theorem mono_of_mono_twistMap {T : Scheme.{u}} (d : ℤ) {F G : (projectiveSpaceOver n T).Modules}
    (φ : F ⟶ G) (h : Mono ((twistFunctor n T d).map φ)) : Mono φ :=
  (twistFunctor n T d).mono_of_mono_map h

/-- The twist reflects epimorphisms. -/
theorem epi_of_epi_twistMap {T : Scheme.{u}} (d : ℤ) {F G : (projectiveSpaceOver n T).Modules}
    (φ : F ⟶ G) (h : Epi ((twistFunctor n T d).map φ)) : Epi φ :=
  (twistFunctor n T d).epi_of_epi_map h

/-- The twist reflects isomorphisms. -/
theorem isIso_of_isIso_twistMap {T : Scheme.{u}} (d : ℤ) {F G : (projectiveSpaceOver n T).Modules}
    (φ : F ⟶ G) (h : IsIso ((twistFunctor n T d).map φ)) : IsIso φ :=
  isIso_of_fully_faithful (twistFunctor n T d) φ

end AlgebraicGeometry.ProjectiveQuot

end
