module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelativeTensorBifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat

/-!
# Conditions (1) and (2) of goodness transport along an isomorphism

Let `(C, O)` be a ringed site and let `A` be a sheaf of differential graded `O`-algebras on it.
Flatness of a right graded `A`-module and K-flatness of a right differential graded `A`-module
are both properties of the isomorphism class: the relative tensor product is a functor of the
right module, so an isomorphism `P ≅ Q` gives an isomorphism `P ⊗_A N ≅ Q ⊗_A N` natural in `N`,
degreewise in the graded case and as a complex in the differential graded case.

The point of recording this is Tag 0FSG. Conditions (1) and (2) of Tag 0FSA for the free
differential graded module `A[S]` on a sheaf of graded sets are the two theorems tagged in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleFlat.lean`, and the source
discharges condition (3) by identifying the pullback `f^*A[S]` with the free module
`A'[f^{-1}S]` on the inverse image of `S` and then quoting its first two paragraphs over the
target site. The second half of that argument is `freeDGModule_baseChange_of_free` below: at any
base-change datum along which the pullback of `A[S]` is again a free module on a sheaf of graded
sets, the clause of condition (3) holds, by conditions (1) and (2) for that free module.

So the whole of the residual gap in Tag 0FSG is the identification itself, the half the source
disposes of with "it is straightforward to see". It is *not* available at the quantification of
`SheafOfModules.DifferentialGradedModule.IsGood`, and the reason is recorded in the
implementation notes of `FreeGradedModuleFlat.lean`.

## Main results

* `SheafOfModules.RelativeTensor.IsGradedFlat.of_iso`: condition (1) of Tag 0FSA transports
  along an isomorphism of right graded modules.
* `SheafOfModules.RelativeTensor.IsKFlat.of_iso`: condition (2) of Tag 0FSA transports along an
  isomorphism of right differential graded modules.
* `SheafOfModules.isGradedFlat_isKFlat_of_iso_freeDGModule`: **any right differential graded
  module isomorphic to a free module on a sheaf of graded sets is flat as a graded module and
  K-flat.** This is the whole mathematical content of the second half of the source's third
  paragraph for Tag 0FSG, with no base-change interface in it at all: the geometric statement of
  `FreeDifferentialGradedModuleToposPullback.lean` consumes it directly, without passing through
  a site-level `PullbackData`.
* `SheafOfModules.freeDGModule_baseChange_of_free`: **the second half of the source's third
  paragraph for Tag 0FSG**, at a site-level pullback datum. At one along which the pullback of
  `A[S]` is isomorphic to the free differential graded module on some sheaf of graded sets on the
  target site, conditions (1) and (2) of Tag 0FSA hold for that pullback — which is the clause of
  condition (3) at that datum.

## Implementation notes

`SheafOfModules.GradedModule.ofDifferentialGradedIso` is the isomorphism of underlying right
graded modules carried by an isomorphism of right differential graded modules. The forgetful
construction `GradedModule.ofDifferentialGraded` is not packaged as a functor in this
development, only as `ofDifferentialGradedMap` together with its identity and composition
lemmas, which is exactly what building the isomorphism by hand needs.

`SheafOfModules.freeDGModule_baseChange_of_free` carries `HasWeakSheafify J₁ (Type m₁)` on the
target site. That is not an extra mathematical hypothesis: it is what lets
`Stacks.SheafOfGradedSets.{m₁} J₁` be formed at all, so without it the statement cannot be
written down. The same instance on the source site is in the ambient variable block for the same
reason. No hypothesis is placed on the functor `u` of the morphism of ringed sites, and none on
the relation between the module universes of the two sites; the isomorphism is the only input.

The theorem is stated per base-change datum rather than as an implication between quantified
statements, deliberately. Universally quantified over the base changes that condition (3) of
`IsGood` ranges over, the hypothesis would be *false*, not merely unavailable: condition (3) of
`IsGood` quantifies over an arbitrary functor `u` of the underlying categories, and
`SheafOfModules.DifferentialGradedModule.idPullbackData` on a site carrying the trivial topology
makes the pullback of `A[S]` its own underlying presheaf, which is not the free module on any
sheaf of graded sets there. The per-datum form has the identity base change of
`SheafOfModules.freeDGModule_baseChange_id` as an instance and says nothing about data where the
identification fails.

## References

* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u m₁ v₁ u₁

namespace SheafOfModules

namespace GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- The isomorphism of underlying right graded modules carried by an isomorphism of right
differential graded modules. -/
def ofDifferentialGradedIso {M M' : DifferentialGradedModule.{t, m, m} A} (e : M ≅ M') :
    ofDifferentialGraded M ≅ ofDifferentialGraded M' where
  hom := ofDifferentialGradedMap e.hom
  inv := ofDifferentialGradedMap e.inv
  hom_inv_id := by
    rw [← ofDifferentialGradedMap_comp, e.hom_inv_id, ofDifferentialGradedMap_id]
  inv_hom_id := by
    rw [← ofDifferentialGradedMap_comp, e.inv_hom_id, ofDifferentialGradedMap_id]

end GradedModule

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}

section Graded

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : GradedAlgebra.{t, m} (toRingCat J Osharp)} {P Q : GradedModule.{t, m, m} A}

/-- Degree `n` of the relative tensor product with a fixed left graded module, as a functor of
the right graded module, carries an isomorphism to an isomorphism. -/
noncomputable def gradedTensorRightIso (e : P ≅ Q) (N : LeftGradedModule.{t, m, m} A) (n : ℤ) :
    gradedTensor P N n ≅ gradedTensor Q N n where
  hom := gradedTensorMapRight e.hom N n
  inv := gradedTensorMapRight e.inv N n
  hom_inv_id := by rw [← gradedTensorMapRight_comp, e.hom_inv_id, gradedTensorMapRight_id]
  inv_hom_id := by rw [← gradedTensorMapRight_comp, e.inv_hom_id, gradedTensorMapRight_id]

/-- **Condition (1) of Tag 0FSA transports along an isomorphism**: a right graded module
isomorphic to a flat one is flat. The relative tensor product is a bifunctor, so the
isomorphisms `P ⊗_A N ≅ Q ⊗_A N` of each degree are natural in `N`, and the short complex they
compare is the one whose short exactness flatness asserts. -/
theorem IsGradedFlat.of_iso (e : P ≅ Q) (hP : IsGradedFlat P) : IsGradedFlat Q := by
  intro N₁ N₂ N₃ f g hfg hSE n
  obtain ⟨hz, hse⟩ := hP N₁ N₂ N₃ f g hfg hSE n
  have hzQ : gradedTensorMap Q f n ≫ gradedTensorMap Q g n = 0 := by
    refine (cancel_epi (gradedTensorRightIso e N₁ n).hom).mp ?_
    rw [comp_zero]
    change gradedTensorMapRight e.hom N₁ n ≫ gradedTensorMap Q f n ≫
      gradedTensorMap Q g n = 0
    rw [← Category.assoc, gradedTensorMapRight_gradedTensorMap e.hom f n, Category.assoc,
      gradedTensorMapRight_gradedTensorMap e.hom g n, ← Category.assoc, hz, zero_comp]
  refine ⟨hzQ, ShortComplex.shortExact_of_iso (ShortComplex.isoMk
    (gradedTensorRightIso e N₁ n) (gradedTensorRightIso e N₂ n) (gradedTensorRightIso e N₃ n)
    (gradedTensorMapRight_gradedTensorMap e.hom f n)
    (gradedTensorMapRight_gradedTensorMap e.hom g n)) hse⟩

end Graded

section DifferentialGraded

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
  {P Q : DifferentialGradedModule.{t, m, m} A}

/-- **Condition (2) of Tag 0FSA transports along an isomorphism**: a right differential graded
module isomorphic to a K-flat one is K-flat. The relative tensor product with a fixed left
differential graded module is the functor `SheafOfModules.RelativeTensor.dgTensorFunctor` of the
right module, so it carries the isomorphism to an isomorphism of complexes, along which
exactness in each degree transports. -/
theorem IsKFlat.of_iso (e : P ≅ Q) (hP : IsKFlat P) : IsKFlat Q := fun N hN i ↦
  (hP N hN i).of_iso ((dgTensorFunctor N).mapIso e)

end DifferentialGraded

end RelativeTensor

/-! ### The second half of the source's third paragraph for Tag 0FSG -/

section BaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)] [HasSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] {Osharp : Sheaf J CommRingCat.{t}}
  (S : Stacks.SheafOfGradedSets.{m} J)
  (D : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp))

/-- **Conditions (1) and (2) of Tag 0FSA for a pullback of `D[S]` which is again free.** This is
the second half of the third paragraph of the source's proof of Tag 0FSG: the source identifies
the pullback `f^*A[S]` with the free differential graded `A'`-module `A'[f^{-1}S]` on the
inverse image of the sheaf of graded sets, and then the first two paragraphs of the same proof,
applied over the target ringed site, give conditions (1) and (2) for it. Those two paragraphs
are `SheafOfModules.freeDGModule_isGradedFlat` and `SheafOfModules.freeDGModule_isKFlat`, which
carry no hypotheses and in particular hold over the target site; this lemma is the transport of
them along the identification.

This is `SheafOfModules.isGradedFlat_isKFlat_of_iso_freeDGModule` instantiated at
`PD.obj (freeDGModule S D)`; the `PullbackData` plays no part in the argument, which is why the
general form is stated first and is what a *geometric* base change consumes.

The identification itself is the input, as an isomorphism `e`, and it is the half of the
argument which is not available at the quantification of
`SheafOfModules.DifferentialGradedModule.IsGood`. So this lemma is exactly the reduction of the
clause of condition (3) at a base-change datum to that identification, and nothing more: it is
not condition (3), which quantifies over every datum, including data at which the identification
is false. -/
theorem isGradedFlat_isKFlat_of_iso_freeDGModule {C₁ : Type u₁} [Category.{v₁} C₁]
    {J₁ : GrothendieckTopology C₁} [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
    [HasWeakSheafify J₁ (Type m₁)] [HasSheafify J₁ AddCommGrpCat.{m₁}]
    [J₁.WEqualsLocallyBijective AddCommGrpCat.{m₁}] {Osharp₁ : Sheaf J₁ CommRingCat.{t}}
    {A₁ : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁)}
    {P : DifferentialGradedModule.{t, m₁, m₁} A₁} (S₁ : Stacks.SheafOfGradedSets.{m₁} J₁)
    (e : P ≅ freeDGModule S₁ A₁) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
      RelativeTensor.IsKFlat P :=
  ⟨RelativeTensor.IsGradedFlat.of_iso (GradedModule.ofDifferentialGradedIso e).symm
      (freeDGModule_isGradedFlat A₁ S₁),
    RelativeTensor.IsKFlat.of_iso e.symm (freeDGModule_isKFlat S₁ A₁)⟩

/-- If the pullback `PD.obj (freeDGModule S D)` of the free differential graded module `D[S]` is
isomorphic to the free differential graded module `freeDGModule S₁ A₁`, then the pullback is
graded flat and K-flat. -/
theorem freeDGModule_baseChange_of_free {C₁ : Type u₁} [Category.{v₁} C₁]
    {J₁ : GrothendieckTopology C₁} [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
    [HasWeakSheafify J₁ (Type m₁)] [HasSheafify J₁ AddCommGrpCat.{m₁}]
    [J₁.WEqualsLocallyBijective AddCommGrpCat.{m₁}] {Osharp₁ : Sheaf J₁ CommRingCat.{t}}
    {u : C ⥤ C₁} {σ : (toRingCat J Osharp).obj ⟶ u.op ⋙ (toRingCat J₁ Osharp₁).obj}
    {A₁ : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁)}
    {φ : DifferentialGradedAlgebra.SemilinearHom u σ D A₁}
    (PD : DifferentialGradedModule.PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ)
    (S₁ : Stacks.SheafOfGradedSets.{m₁} J₁)
    (e : PD.obj (freeDGModule S D) ≅ freeDGModule S₁ A₁) :
    RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded (PD.obj (freeDGModule S D))) ∧
      RelativeTensor.IsKFlat (PD.obj (freeDGModule S D)) :=
  isGradedFlat_isKFlat_of_iso_freeDGModule S₁ e

end BaseChange

end SheafOfModules

end
