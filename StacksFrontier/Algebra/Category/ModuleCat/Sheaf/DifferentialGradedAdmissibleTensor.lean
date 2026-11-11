module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelativeTensorAdditive

/-!
# Tensoring an admissible short exact sequence of differential graded modules

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras on it and
let `N` be a left differential graded `A`-module. Tensoring an admissible short exact sequence
of right differential graded `A`-modules with `N` gives a short exact sequence of complexes of
`O`-modules: the graded splitting is carried along by `- ⊗_A N`, because forgetting the
differentials the relative tensor product is taken in the category of graded modules. The
cohomology long exact sequence then gives two out of three for K-flatness: if two of the three
terms of an admissible short exact sequence are K-flat, so is the third.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GradedSplitting.dgTensorSplitting` is the splitting
  of the degree-`n` short complex of sheaves of modules obtained by tensoring a graded
  splitting.

## Main results

* `SheafOfModules.DifferentialGradedModule.GradedSplitting.dgTensor_shortExact`: the tensored
  sequence is a short exact sequence of complexes of `O`-modules.
* `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.dgTensor_shortExact`: the same
  statement for an admissible short exact sequence.
* `SheafOfModules.DifferentialGradedModule.quasiIso_of_acyclic`: a morphism of acyclic complexes
  of sheaves of modules is a quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.isKFlat_left`, `isKFlat_middle`
  and `isKFlat_right`, with their `GradedSplitting` counterparts: two out of three for
  K-flatness along an admissible short exact sequence.

## Implementation notes

The splitting is transported degreewise rather than through a functor on complexes: the
retraction and the section commute with the module actions but not with the differentials, so
they are homomorphisms of graded modules and `- ⊗_A N` can only be applied to them one degree at
a time, through `SheafOfModules.RelativeTensor.gradedTensorMapRight`. That map is functorial
(`gradedTensorMapRight_id`, `gradedTensorMapRight_comp`) and additive in its homomorphism
(`gradedTensorMapRight_add`), which is exactly what the three splitting identities need. Degree
`n` of the map of complexes induced by a morphism of right differential graded modules *is* that
map, by `SheafOfModules.RelativeTensor.dgTensorFunctor_map_f`, so no comparison isomorphism
appears.

Short exactness of the sequence of complexes then follows degreewise, through
`HomologicalComplex.shortExact_of_degreewise_shortExact`; a split short complex in an abelian
category is short exact.

Two out of three for K-flatness is the cohomology long exact sequence of that short exact
sequence of complexes, in the form of Mathlib's
`CategoryTheory.ShortComplex.ShortExact.acyclic_X₁`, `acyclic_X₂` and `acyclic_X₃`. The first
and the third of those are stated through a quasi-isomorphism rather than through acyclicity of
the two remaining terms, which is why `quasiIso_of_acyclic` is needed: a map between acyclic
complexes joins two zero cohomology objects and is therefore an isomorphism on cohomology.

Only condition (2) of a good differential graded module is treated here. Condition (1) is
exactness of `N ↦ P ⊗_A N` in the *other* variable and is in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAdmissibleFlat.lean`, and
Tag 0FSC itself, with condition (3) of Tag 0FSA over morphisms of ringed topoi, is
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedAdmissibleTopos.lean`.

## References

* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
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

namespace DifferentialGradedModule

variable {K L M : DifferentialGradedModule.{t, m, m} A} {f : K ⟶ L} {g : L ⟶ M}

/-- Tensoring a graded splitting with a left differential graded module splits the degree-`n`
short complex of sheaves of modules. -/
noncomputable def GradedSplitting.dgTensorSplitting (S : GradedSplitting f g)
    (N : LeftDifferentialGradedModule.{t, m, m} A) (n : ℤ) :
    ((S.shortComplex.map (RelativeTensor.dgTensorFunctor N)).map
      (HomologicalComplex.eval _ _ n)).Splitting where
  r := RelativeTensor.gradedTensorMapRight S.r (RelativeTensor.gN N) n
  s := RelativeTensor.gradedTensorMapRight S.s (RelativeTensor.gN N) n
  f_r := by
    change RelativeTensor.gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f)
          (RelativeTensor.gN N) n ≫
        RelativeTensor.gradedTensorMapRight S.r (RelativeTensor.gN N) n = 𝟙 _
    rw [← RelativeTensor.gradedTensorMapRight_comp, S.f_r,
      RelativeTensor.gradedTensorMapRight_id]
  s_g := by
    change RelativeTensor.gradedTensorMapRight S.s (RelativeTensor.gN N) n ≫
        RelativeTensor.gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g)
          (RelativeTensor.gN N) n = 𝟙 _
    rw [← RelativeTensor.gradedTensorMapRight_comp, S.s_g,
      RelativeTensor.gradedTensorMapRight_id]
  id := by
    change RelativeTensor.gradedTensorMapRight S.r (RelativeTensor.gN N) n ≫
          RelativeTensor.gradedTensorMapRight (GradedModule.ofDifferentialGradedMap f)
            (RelativeTensor.gN N) n +
        RelativeTensor.gradedTensorMapRight (GradedModule.ofDifferentialGradedMap g)
            (RelativeTensor.gN N) n ≫
          RelativeTensor.gradedTensorMapRight S.s (RelativeTensor.gN N) n = 𝟙 _
    rw [← RelativeTensor.gradedTensorMapRight_comp, ← RelativeTensor.gradedTensorMapRight_comp,
      ← RelativeTensor.gradedTensorMapRight_add, S.id,
      RelativeTensor.gradedTensorMapRight_id]

/-- **Tensoring an admissible short exact sequence of right differential graded modules with a
left differential graded module gives a short exact sequence of complexes of `O`-modules.** -/
theorem GradedSplitting.dgTensor_shortExact (S : GradedSplitting f g)
    (N : LeftDifferentialGradedModule.{t, m, m} A) :
    (S.shortComplex.map (RelativeTensor.dgTensorFunctor N)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (S.dgTensorSplitting N n).shortExact

/-- **Tensoring an admissible short exact sequence of right differential graded modules with a
left differential graded module gives a short exact sequence of complexes of `O`-modules.** -/
theorem IsAdmissibleShortExact.dgTensor_shortExact (h : IsAdmissibleShortExact f g)
    (N : LeftDifferentialGradedModule.{t, m, m} A) :
    (h.shortComplex.map (RelativeTensor.dgTensorFunctor N)).ShortExact :=
  Nonempty.elim h fun S ↦ S.dgTensor_shortExact N

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A morphism between two acyclic complexes of sheaves of modules is a quasi-isomorphism: the
map it induces on cohomology joins two zero objects. -/
theorem quasiIso_of_acyclic
    {X Y : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) ℤ}
    (φ : X ⟶ Y)
    (hX : X.Acyclic) (hY : Y.Acyclic) : QuasiIso φ where
  quasiIsoAt i := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ⟨⟨0, (hX i).isZero_homology.eq_of_src _ _, (hY i).isZero_homology.eq_of_tgt _ _⟩⟩

namespace GradedSplitting

/-- **Two out of three for K-flatness**: if the two outer terms of an admissible short exact
sequence are K-flat, so is the middle one. -/
theorem isKFlat_middle (S : GradedSplitting f g) (hK : RelativeTensor.IsKFlat K)
    (hM : RelativeTensor.IsKFlat M) : RelativeTensor.IsKFlat L :=
  fun N hN ↦ (S.dgTensor_shortExact N).acyclic_X₂ (hK N hN) (hM N hN)

/-- **Two out of three for K-flatness**: if the middle and the third term of an admissible short
exact sequence are K-flat, so is the first one. -/
theorem isKFlat_left (S : GradedSplitting f g) (hL : RelativeTensor.IsKFlat L)
    (hM : RelativeTensor.IsKFlat M) : RelativeTensor.IsKFlat K :=
  fun N hN ↦ (S.dgTensor_shortExact N).acyclic_X₁
    (quasiIso_of_acyclic _ (hL N hN) (hM N hN))

/-- **Two out of three for K-flatness**: if the first and the middle term of an admissible short
exact sequence are K-flat, so is the third one. -/
theorem isKFlat_right (S : GradedSplitting f g) (hK : RelativeTensor.IsKFlat K)
    (hL : RelativeTensor.IsKFlat L) : RelativeTensor.IsKFlat M :=
  fun N hN ↦ (S.dgTensor_shortExact N).acyclic_X₃
    (quasiIso_of_acyclic _ (hK N hN) (hL N hN))

end GradedSplitting

namespace IsAdmissibleShortExact

/-- **Two out of three for K-flatness**: if the two outer terms of an admissible short exact
sequence are K-flat, so is the middle one. This is
condition (2) of goodness in Tag 0FSC; the tag itself, with all three conditions of Tag 0FSA, is
`IsAdmissibleShortExact.isGoodToposBaseChange_middle`. -/
theorem isKFlat_middle (h : IsAdmissibleShortExact f g) (hK : RelativeTensor.IsKFlat K)
    (hM : RelativeTensor.IsKFlat M) : RelativeTensor.IsKFlat L :=
  Nonempty.elim h fun S ↦ S.isKFlat_middle hK hM

/-- **Two out of three for K-flatness**: if the middle and the third term of an admissible short
exact sequence are K-flat, so is the first one. This is
condition (2) of goodness in Tag 0FSC; the tag itself, with all three conditions of Tag 0FSA, is
`IsAdmissibleShortExact.isGoodToposBaseChange_left`. -/
theorem isKFlat_left (h : IsAdmissibleShortExact f g) (hL : RelativeTensor.IsKFlat L)
    (hM : RelativeTensor.IsKFlat M) : RelativeTensor.IsKFlat K :=
  Nonempty.elim h fun S ↦ S.isKFlat_left hL hM

/-- **Two out of three for K-flatness**: if the first and the middle term of an admissible short
exact sequence are K-flat, so is the third one. This is
condition (2) of goodness in Tag 0FSC; the tag itself, with all three conditions of Tag 0FSA, is
`IsAdmissibleShortExact.isGoodToposBaseChange_right`. -/
theorem isKFlat_right (h : IsAdmissibleShortExact f g) (hK : RelativeTensor.IsKFlat K)
    (hL : RelativeTensor.IsKFlat L) : RelativeTensor.IsKFlat M :=
  Nonempty.elim h fun S ↦ S.isKFlat_right hK hL

end IsAdmissibleShortExact

end DifferentialGradedModule

end SheafOfModules
