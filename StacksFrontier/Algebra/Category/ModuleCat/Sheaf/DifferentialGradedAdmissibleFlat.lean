module

public import StacksFrontier.Algebra.Homology.ShortComplex.SplittingShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelativeTensorAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelativeTensorBifunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness along an admissible short exact sequence of differential graded modules

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras on it and
let `0 → K → L → M → 0` be an admissible short exact sequence of right differential graded
`A`-modules. If two of the three underlying right graded modules are flat, so is the third:
exactness of `N ↦ Q ⊗_A N` on left graded `A`-modules holds for the third term as soon as it
holds for two of them.

The graded splitting makes the degree-`n` short complexes `Q ⊗_A N₁ → Q ⊗_A N₂ → Q ⊗_A N₃`,
for `Q` running through the three terms and `N₁ → N₂ → N₃` a short exact sequence of left
graded modules, into a *split* short complex of short complexes of `O`-modules: the retraction
and the section of the splitting are homomorphisms of graded modules, and the relative tensor
product is a bifunctor, so tensoring them with `N₁`, `N₂` and `N₃` gives morphisms of short
complexes. Two out of three then follows.

## Main results

* `SheafOfModules.DifferentialGradedModule.GradedSplitting.isGradedFlat_left`,
  `isGradedFlat_middle` and `isGradedFlat_right`, with their
  `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact` counterparts: **two out of
  three for flatness of the underlying right graded module along an admissible short exact
  sequence of right differential graded modules.** This is condition (1) in the definition of a
  good right differential graded module.

## Implementation notes

The vanishing of the composite `Q ⊗_A N₁ → Q ⊗_A N₂ → Q ⊗_A N₃` is part of the conclusion of
flatness, not of its hypotheses, so it has to be produced for the third term before the short
complex it belongs to can be formed. For an outer term this is monomorphy: the splitting makes
the comparison with the middle term a split monomorphism in degree `n`, and the composite
becomes zero after it. For the middle term it is the decomposition of the identity, which
factors the composite through the two outer ones.

Only condition (1) is treated here; condition (2), K-flatness, is in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAdmissibleTensor.lean`, and
condition (3) would need the graded splitting to be transported through the pullback of
differential graded modules, which acts only on morphisms of differential graded modules, while
the retraction and the section are merely graded.

## References

* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

namespace RelativeTensor

section ShortComplexes

variable {A' : GradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {N₁ N₂ N₃ : LeftGradedModule.{t, m, m} A'} (a : N₁ ⟶ N₂) (b : N₂ ⟶ N₃)

/-- The degree-`n` short complex `Q ⊗_A N₁ → Q ⊗_A N₂ → Q ⊗_A N₃` of sheaves of `O`-modules
attached to a pair of homomorphisms of left graded `A`-modules with vanishing composite tensor
product. -/
noncomputable def tensorShortComplex (Q : GradedModule.{t, m, m} A') (n : ℤ)
    (z : gradedTensorMap Q a n ≫ gradedTensorMap Q b n = 0) :
    ShortComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :=
  ShortComplex.mk _ _ z

/-- A homomorphism of right graded `A`-modules induces a morphism of the degree-`n` short
complexes, by bifunctoriality of the relative tensor product. -/
noncomputable def tensorShortComplexMap {Q Q' : GradedModule.{t, m, m} A'} (h : Q ⟶ Q') (n : ℤ)
    {z : gradedTensorMap Q a n ≫ gradedTensorMap Q b n = 0}
    {z' : gradedTensorMap Q' a n ≫ gradedTensorMap Q' b n = 0} :
    tensorShortComplex a b Q n z ⟶ tensorShortComplex a b Q' n z' where
  τ₁ := gradedTensorMapRight h N₁ n
  τ₂ := gradedTensorMapRight h N₂ n
  τ₃ := gradedTensorMapRight h N₃ n
  comm₁₂ := gradedTensorMapRight_gradedTensorMap h a n
  comm₂₃ := gradedTensorMapRight_gradedTensorMap h b n

end ShortComplexes

end RelativeTensor

namespace DifferentialGradedModule

open RelativeTensor

namespace GradedSplitting

variable {K L M : DifferentialGradedModule.{t, m, m} A} {f : K ⟶ L} {g : L ⟶ M}
  {N₁ N₂ N₃ : LeftGradedModule.{t, m, m} A.toGradedAlgebra} {a : N₁ ⟶ N₂} {b : N₂ ⟶ N₃}

/-- Tensoring a graded splitting with a short exact sequence of left graded modules splits the
degree-`n` short complex of degree-`n` short complexes. -/
noncomputable def tensorSplitting (S : GradedSplitting f g) (n : ℤ)
    {zK : gradedTensorMap (GradedModule.ofDifferentialGraded K) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded K) b n = 0}
    {zL : gradedTensorMap (GradedModule.ofDifferentialGraded L) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded L) b n = 0}
    {zM : gradedTensorMap (GradedModule.ofDifferentialGraded M) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded M) b n = 0} :
    (ShortComplex.mk
      (tensorShortComplexMap a b (GradedModule.ofDifferentialGradedMap f) n (z := zK) (z' := zL))
      (tensorShortComplexMap a b (GradedModule.ofDifferentialGradedMap g) n (z := zL) (z' := zM))
      (ShortComplex.hom_ext _ _
        (by
          change gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₁ n ≫
            gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₁ n = 0
          rw [← gradedTensorMapRight_comp, S.graded_comp_eq_zero, gradedTensorMapRight_zero])
        (by
          change gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₂ n ≫
            gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₂ n = 0
          rw [← gradedTensorMapRight_comp, S.graded_comp_eq_zero, gradedTensorMapRight_zero])
        (by
          change gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₃ n ≫
            gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₃ n = 0
          rw [← gradedTensorMapRight_comp, S.graded_comp_eq_zero,
            gradedTensorMapRight_zero]))).Splitting where
  r := tensorShortComplexMap a b S.r n (z := zL) (z' := zK)
  s := tensorShortComplexMap a b S.s n (z := zM) (z' := zL)
  f_r := ShortComplex.hom_ext _ _
    (by
      change gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₁ n ≫
        gradedTensorMapRight S.r N₁ n = 𝟙 _
      rw [← gradedTensorMapRight_comp, S.f_r, gradedTensorMapRight_id])
    (by
      change gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₂ n ≫
        gradedTensorMapRight S.r N₂ n = 𝟙 _
      rw [← gradedTensorMapRight_comp, S.f_r, gradedTensorMapRight_id])
    (by
      change gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₃ n ≫
        gradedTensorMapRight S.r N₃ n = 𝟙 _
      rw [← gradedTensorMapRight_comp, S.f_r, gradedTensorMapRight_id])
  s_g := ShortComplex.hom_ext _ _
    (by
      change gradedTensorMapRight S.s N₁ n ≫
        gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₁ n = 𝟙 _
      rw [← gradedTensorMapRight_comp, S.s_g, gradedTensorMapRight_id])
    (by
      change gradedTensorMapRight S.s N₂ n ≫
        gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₂ n = 𝟙 _
      rw [← gradedTensorMapRight_comp, S.s_g, gradedTensorMapRight_id])
    (by
      change gradedTensorMapRight S.s N₃ n ≫
        gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₃ n = 𝟙 _
      rw [← gradedTensorMapRight_comp, S.s_g, gradedTensorMapRight_id])
  id := ShortComplex.hom_ext _ _
    (by
      change gradedTensorMapRight S.r N₁ n ≫
            gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₁ n +
          gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₁ n ≫
            gradedTensorMapRight S.s N₁ n = 𝟙 _
      rw [← gradedTensorMapRight_comp, ← gradedTensorMapRight_comp,
        ← gradedTensorMapRight_add, S.id, gradedTensorMapRight_id])
    (by
      change gradedTensorMapRight S.r N₂ n ≫
            gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₂ n +
          gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₂ n ≫
            gradedTensorMapRight S.s N₂ n = 𝟙 _
      rw [← gradedTensorMapRight_comp, ← gradedTensorMapRight_comp,
        ← gradedTensorMapRight_add, S.id, gradedTensorMapRight_id])
    (by
      change gradedTensorMapRight S.r N₃ n ≫
            gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₃ n +
          gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₃ n ≫
            gradedTensorMapRight S.s N₃ n = 𝟙 _
      rw [← gradedTensorMapRight_comp, ← gradedTensorMapRight_comp,
        ← gradedTensorMapRight_add, S.id, gradedTensorMapRight_id])

/-- The composite of the degree-`n` short complex of `P` is killed by the comparison with `P'`
as soon as that of `P'` vanishes. -/
private theorem comp_gradedTensorMapRight_eq_zero {P P' : GradedModule.{t, m, m} A.toGradedAlgebra}
    (h : P ⟶ P') (n : ℤ)
    (z : gradedTensorMap P' a n ≫ gradedTensorMap P' b n = 0) :
    (gradedTensorMap P a n ≫ gradedTensorMap P b n) ≫ gradedTensorMapRight h N₃ n = 0 := by
  rw [Category.assoc, gradedTensorMap_gradedTensorMap_gradedTensorMapRight h a b n, z, comp_zero]

/-- The composite of the degree-`n` short complex of `P` vanishes as soon as that of `P'` does,
if `P` is a retract of `P'`. -/
private theorem tensorMap_comp_eq_zero_of_comp_eq_id
    {P P' : GradedModule.{t, m, m} A.toGradedAlgebra} (h : P ⟶ P') (k : P' ⟶ P) (hk : h ≫ k = 𝟙 P)
    (n : ℤ) (z : gradedTensorMap P' a n ≫ gradedTensorMap P' b n = 0) :
    gradedTensorMap P a n ≫ gradedTensorMap P b n = 0 :=
  calc gradedTensorMap P a n ≫ gradedTensorMap P b n
      = (gradedTensorMap P a n ≫ gradedTensorMap P b n) ≫
          (gradedTensorMapRight h N₃ n ≫ gradedTensorMapRight k N₃ n) := by
        rw [← gradedTensorMapRight_comp, hk, gradedTensorMapRight_id, Category.comp_id]
    _ = 0 := by rw [← Category.assoc, comp_gradedTensorMapRight_eq_zero h n z, zero_comp]

/-- The composite of the degree-`n` short complex of the first term of an admissible short exact
sequence vanishes as soon as that of the middle term does. -/
theorem tensorMap_comp_eq_zero_left (S : GradedSplitting f g) (n : ℤ)
    (zL : gradedTensorMap (GradedModule.ofDifferentialGraded L) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded L) b n = 0) :
    gradedTensorMap (GradedModule.ofDifferentialGraded K) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded K) b n = 0 :=
  tensorMap_comp_eq_zero_of_comp_eq_id (N₃ := N₃) _ S.r S.f_r n zL

/-- The composite of the degree-`n` short complex of the third term of an admissible short exact
sequence vanishes as soon as that of the middle term does. -/
theorem tensorMap_comp_eq_zero_right (S : GradedSplitting f g) (n : ℤ)
    (zL : gradedTensorMap (GradedModule.ofDifferentialGraded L) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded L) b n = 0) :
    gradedTensorMap (GradedModule.ofDifferentialGraded M) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded M) b n = 0 :=
  tensorMap_comp_eq_zero_of_comp_eq_id (N₃ := N₃) S.s _ S.s_g n zL

/-- The composite of the degree-`n` short complex of the middle term of an admissible short
exact sequence vanishes as soon as those of the two outer terms do. -/
theorem tensorMap_comp_eq_zero_middle (S : GradedSplitting f g) (n : ℤ)
    (zK : gradedTensorMap (GradedModule.ofDifferentialGraded K) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded K) b n = 0)
    (zM : gradedTensorMap (GradedModule.ofDifferentialGraded M) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded M) b n = 0) :
    gradedTensorMap (GradedModule.ofDifferentialGraded L) a n ≫
      gradedTensorMap (GradedModule.ofDifferentialGraded L) b n = 0 := by
  have hr := comp_gradedTensorMapRight_eq_zero (N₃ := N₃) S.r n zK
  have hg := comp_gradedTensorMapRight_eq_zero (N₃ := N₃)
    (GradedModule.ofDifferentialGradedMap g) n zM
  have hid : gradedTensorMapRight S.r N₃ n ≫
        gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₃ n +
      gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₃ n ≫
        gradedTensorMapRight S.s N₃ n = 𝟙 _ := by
    rw [← gradedTensorMapRight_comp, ← gradedTensorMapRight_comp,
      ← gradedTensorMapRight_add, S.id, gradedTensorMapRight_id]
  calc gradedTensorMap (GradedModule.ofDifferentialGraded L) a n ≫
        gradedTensorMap (GradedModule.ofDifferentialGraded L) b n
      = (gradedTensorMap (GradedModule.ofDifferentialGraded L) a n ≫
          gradedTensorMap (GradedModule.ofDifferentialGraded L) b n) ≫ 𝟙 _ :=
        (Category.comp_id _).symm
    _ = ((gradedTensorMap (GradedModule.ofDifferentialGraded L) a n ≫
            gradedTensorMap (GradedModule.ofDifferentialGraded L) b n) ≫
              gradedTensorMapRight S.r N₃ n) ≫
          gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f) N₃ n +
        ((gradedTensorMap (GradedModule.ofDifferentialGraded L) a n ≫
            gradedTensorMap (GradedModule.ofDifferentialGraded L) b n) ≫
              gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g) N₃ n) ≫
          gradedTensorMapRight S.s N₃ n := by
        rw [← hid, Preadditive.comp_add]
        simp only [Category.assoc]
    _ = 0 := by rw [hr, hg, zero_comp, zero_comp, add_zero]

/-- **Two out of three for flatness of the underlying right graded module**: if the middle and
the third term of an admissible short exact sequence of right differential graded modules are
flat, so is the first one. -/
theorem isGradedFlat_left (S : GradedSplitting f g)
    (hL : IsGradedFlat (GradedModule.ofDifferentialGraded L))
    (hM : IsGradedFlat (GradedModule.ofDifferentialGraded M)) :
    IsGradedFlat (GradedModule.ofDifferentialGraded K) := by
  intro P₁ P₂ P₃ u w huw hSE n
  obtain ⟨zL, hLn⟩ := hL P₁ P₂ P₃ u w huw hSE n
  obtain ⟨zM, _⟩ := hM P₁ P₂ P₃ u w huw hSE n
  exact ⟨S.tensorMap_comp_eq_zero_left n zL,
    (S.tensorSplitting n (zK := S.tensorMap_comp_eq_zero_left n zL) (zL := zL)
      (zM := zM)).shortExact_X₁ hLn⟩

/-- **Two out of three for flatness of the underlying right graded module**: if the first and
the middle term of an admissible short exact sequence of right differential graded modules are
flat, so is the third one. -/
theorem isGradedFlat_right (S : GradedSplitting f g)
    (hK : IsGradedFlat (GradedModule.ofDifferentialGraded K))
    (hL : IsGradedFlat (GradedModule.ofDifferentialGraded L)) :
    IsGradedFlat (GradedModule.ofDifferentialGraded M) := by
  intro P₁ P₂ P₃ u w huw hSE n
  obtain ⟨zK, _⟩ := hK P₁ P₂ P₃ u w huw hSE n
  obtain ⟨zL, hLn⟩ := hL P₁ P₂ P₃ u w huw hSE n
  exact ⟨S.tensorMap_comp_eq_zero_right n zL,
    (S.tensorSplitting n (zK := zK) (zL := zL)
      (zM := S.tensorMap_comp_eq_zero_right n zL)).shortExact_X₃ hLn⟩

/-- **Two out of three for flatness of the underlying right graded module**: if the two outer
terms of an admissible short exact sequence of right differential graded modules are flat, so is
the middle one. -/
theorem isGradedFlat_middle (S : GradedSplitting f g)
    (hK : IsGradedFlat (GradedModule.ofDifferentialGraded K))
    (hM : IsGradedFlat (GradedModule.ofDifferentialGraded M)) :
    IsGradedFlat (GradedModule.ofDifferentialGraded L) := by
  intro P₁ P₂ P₃ u w huw hSE n
  obtain ⟨zK, hKn⟩ := hK P₁ P₂ P₃ u w huw hSE n
  obtain ⟨zM, hMn⟩ := hM P₁ P₂ P₃ u w huw hSE n
  exact ⟨S.tensorMap_comp_eq_zero_middle n zK zM,
    (S.tensorSplitting n (zK := zK) (zL := S.tensorMap_comp_eq_zero_middle n zK zM)
      (zM := zM)).shortExact_X₂ hKn hMn⟩

end GradedSplitting

namespace IsAdmissibleShortExact

variable {K L M : DifferentialGradedModule.{t, m, m} A} {f : K ⟶ L} {g : L ⟶ M}

/-- **Two out of three for flatness of the underlying right graded module**: if the middle and
the third term of an admissible short exact sequence of right differential graded modules are
flat, so is the first one. -/
@[stacks 0FSC "condition (1) only — flatness of the underlying right graded module, two out of \
three along an admissible short exact sequence; condition (2) is the `isKFlat_*` lemmas and \
condition (3) the `isGood_*` lemmas, which together give the tag"]
theorem isGradedFlat_left (h : IsAdmissibleShortExact f g)
    (hL : IsGradedFlat (GradedModule.ofDifferentialGraded L))
    (hM : IsGradedFlat (GradedModule.ofDifferentialGraded M)) :
    IsGradedFlat (GradedModule.ofDifferentialGraded K) :=
  Nonempty.elim h fun S ↦ S.isGradedFlat_left hL hM

/-- **Two out of three for flatness of the underlying right graded module**: if the first and
the middle term of an admissible short exact sequence of right differential graded modules are
flat, so is the third one. -/
@[stacks 0FSC "condition (1) only — flatness of the underlying right graded module, two out of \
three along an admissible short exact sequence; condition (2) is the `isKFlat_*` lemmas and \
condition (3) the `isGood_*` lemmas, which together give the tag"]
theorem isGradedFlat_right (h : IsAdmissibleShortExact f g)
    (hK : IsGradedFlat (GradedModule.ofDifferentialGraded K))
    (hL : IsGradedFlat (GradedModule.ofDifferentialGraded L)) :
    IsGradedFlat (GradedModule.ofDifferentialGraded M) :=
  Nonempty.elim h fun S ↦ S.isGradedFlat_right hK hL

/-- **Two out of three for flatness of the underlying right graded module**: if the two outer
terms of an admissible short exact sequence of right differential graded modules are flat, so is
the middle one. -/
@[stacks 0FSC "condition (1) only — flatness of the underlying right graded module, two out of \
three along an admissible short exact sequence; condition (2) is the `isKFlat_*` lemmas and \
condition (3) the `isGood_*` lemmas, which together give the tag"]
theorem isGradedFlat_middle (h : IsAdmissibleShortExact f g)
    (hK : IsGradedFlat (GradedModule.ofDifferentialGraded K))
    (hM : IsGradedFlat (GradedModule.ofDifferentialGraded M)) :
    IsGradedFlat (GradedModule.ofDifferentialGraded L) :=
  Nonempty.elim h fun S ↦ S.isGradedFlat_middle hK hM

end IsAdmissibleShortExact

end DifferentialGradedModule

end SheafOfModules
