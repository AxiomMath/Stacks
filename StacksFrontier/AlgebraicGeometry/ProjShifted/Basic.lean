module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistGlobalSections
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Tensor
public import StacksFrontier.AlgebraicGeometry.ProjTwists.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace

/-!
# The canonical map `M̃ ⊗ 𝒪(a) → M(a)~` on `Proj(S)`

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ` and let `M` be a
`ℤ`-graded `S`-module with grading `𝒨 : ℤ → τ`. For an integer `a` the shift `M(a)` is the
module `M` with the grading `i ↦ M_{i+a}`, which is `Stacks.GradedModule.shiftedGrading 𝒨 a`.
The shift is again a graded `S`-module; the two instances this amounts to in Lean,
`Stacks.GradedModule.shiftedGradingDecomposition` and
`Stacks.GradedModule.shiftedGradingGradedSMul`, are in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistGlobalSections` and are imported here.
They are inputs to Tag 0AG2 rather than assertions of it: that tag's statement is the map
`Mₐ → Γ(Proj(S), M(a)~)`.

With them available, `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf
𝒮 (shiftedGrading 𝒨 a)` — the sheaf `M(a)~` on `Proj(S)` — can be formed, and so can the
canonical comparison map `M̃ ⊗ 𝒪(a) → M(a)~` of Tag 01MQ, which is `moduleTwistMap` below.
Tag 01MU asserts that it restricts to an isomorphism on the locus where the `d`-divisible
twists are invertible; that is not proved here.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap`: the canonical morphism
  `M̃ ⊗ 𝒪(a) ⟶ M(a)~` of sheaves of modules on `Proj(S)`, which is Tag 01MQ.

## Main results

* `Stacks.GradedModule.isInternal_shiftedGrading`: the shifted homogeneous pieces are an
  internal direct sum decomposition of `M`. Shifting the index is a bijection of `ℤ`, so the
  decomposition transports along it; the content of the proof is the transport bookkeeping.

## Implementation notes

The reindexing is `DirectSum.equivCongrLeft ((Equiv.addRight a).symm)`, whose target family is
`fun k => 𝒨 (((Equiv.addRight a).symm).symm k)`. That family is only *definitionally* the shifted
grading `fun k => 𝒨 (k + a)`, so the transport is a sequence of defeq-crossings rather than
rewrites. Two places need care.

First, `DirectSum.equivCongrLeft_of` is stated at index `h.symm k`, and the extensionality
principle `DirectSum.addHom_ext` hands over an arbitrary index `j`. The two are reconciled by
replacing `j` with `h.symm k` for `k := h j` before any lemma is applied, which `obtain ⟨k, rfl⟩`
does: the substitution carries the dependent `y : 𝒨 j` along with it, whereas a cast of `y`
written by hand would then have to be eliminated again.

Second, the resulting equation and `DirectSum.coeAddMonoidHom_of` speak of the two different
spellings of one family. Supplying them to `congrArg`/`Eq.trans` as already-elaborated
hypotheses lets the elaborator discharge the difference by `whnf`; passing them inline makes the
expected type propagate into the lemma's own family argument, which then has to be solved as a
higher-order unification problem `fun k => ?β (h.symm k) =?= fun i => 𝒨 (i + a)` and fails. That
is why `h1` and `h2` are `have`s.

The two imported shifted-grading instances have a lambda at the head of their conclusion, so the
discrimination tree stores it as a wildcard and each is a candidate for every goal of its class;
in particular `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading 𝒮 n` is literally
`fun i => integerGrading 𝒮 (i + n)` and does unify with `shiftedGrading ?𝒨 ?a`. They are not
interchangeable with the specific `twistGrading` instances: `twistGradingDecomposition` is an
`IsInternal.chooseDecomposition`, whereas `shiftedGradingDecomposition` transports the
decomposition explicitly, so the two are equal only propositionally. Nothing below depends on
which is selected, because `moduleTwistMap` names the instance it wants through `letI`.

The `VAdd ℕ ℤ` action is the scoped `Stacks.GradedLocalization.instVAddNatInt`. Each file that
needs the action declares its own copy, so the one baked into the type of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf` is a different constant from this
one; they have identical bodies and both are `instance_reducible`, which is what lets instance
search cross between them.

`moduleTwistMap` is written with the library grading
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading`, because that is the one
`twistingSheaf 𝒮 a` is the associated sheaf of. Its degree-preservation argument is
`Stacks.GradedModule.rid_mem_shiftedGrading`, which is stated with this repository's own
`Stacks.GradedModule.twistGrading`; the two gradings are definitionally equal, so `exact` accepts
it where `rw` would not relate them.

## What is not done here

The only `stacks` attribute attached is for Tag 01MQ, the displayed equation of the source that
constructs this map. Tag 0AG2's statement is the map `Mₐ → Γ(Proj(S), M(a)~)`, recorded in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjShiftedSectionModule.lean`, and
Tag 01MU's assertions are about the invertible locus, not about this map; the covering set for
01MU spans several files and its tags are placed elsewhere. `moduleTwistMap` is only
*constructed* here — Tag 01MU's assertion that it restricts to an isomorphism on the locus where
the `d`-divisible twists are invertible is not proved, and needs Tag 0B8M exactly as the other
assertions of 01MU recorded in `StacksFrontier/AlgebraicGeometry/ProjInvertibleLocus/Basic.lean`
do. Nothing is claimed about the shifted grading beyond `isInternal_shiftedGrading`: no `simp`
normal form for it, no comparison of `M(a)(b)` with `M(a+b)`, and no statement that `M(0) = M`.

## References

* [Stacks Project, Equation 27.10.0.4, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization
open scoped TensorProduct

namespace Stacks.GradedModule

universe v t

section Decomposition

variable {M : Type v} {τ : Type t} [AddCommGroup M] [SetLike τ M] [AddSubgroupClass τ M]

/-- Shifting a `ℤ`-grading by an integer again decomposes the module: the pieces `M_{i+a}` are
an internal direct sum decomposition of `M` because `i ↦ i + a` is a bijection of `ℤ`. -/
theorem isInternal_shiftedGrading (𝒨 : ℤ → τ) [Decomposition 𝒨] (a : ℤ) :
    DirectSum.IsInternal (shiftedGrading 𝒨 a) := by
  let E : (⨁ i, ↥(𝒨 i)) ≃+ (⨁ i, ↥(shiftedGrading 𝒨 a i)) :=
    DirectSum.equivCongrLeft (Equiv.addRight a).symm
  have hcomp : (DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 a)).comp E.toAddMonoidHom
      = DirectSum.coeAddMonoidHom 𝒨 := by
    refine DirectSum.addHom_ext ?_
    intro j y
    obtain ⟨k, rfl⟩ : ∃ k, (Equiv.addRight a).symm.symm k = j :=
      ⟨(Equiv.addRight a).symm j, (Equiv.addRight a).symm.symm_apply_apply j⟩
    refine .trans ?_ (DirectSum.coeAddMonoidHom_of 𝒨 _ y).symm
    show DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 a)
        (DirectSum.equivCongrLeft (Equiv.addRight a).symm
          (DirectSum.of (fun i => ↥(𝒨 i)) ((Equiv.addRight a).symm.symm k) y)) = (y : M)
    have h1 := DirectSum.equivCongrLeft_of (β := fun i => ↥(𝒨 i)) (Equiv.addRight a).symm k y
    have h2 := DirectSum.coeAddMonoidHom_of (shiftedGrading 𝒨 a) k y
    exact (congrArg (DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 a)) h1).trans h2
  have key : ∀ x, DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 a) (E x)
      = DirectSum.coeAddMonoidHom 𝒨 x := fun x => DFunLike.congr_fun hcomp x
  have hfun : (DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 a) : _ → M)
      = (DirectSum.coeAddMonoidHom 𝒨) ∘ (E.symm : _ → _) := by
    funext x
    exact (congrArg (DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 a))
      (E.apply_symm_apply x)).symm.trans (key (E.symm x))
  have hbij := (Decomposition.isInternal 𝒨).comp E.symm.bijective
  rwa [← hfun] at hbij

end Decomposition

end Stacks.GradedModule

namespace Stacks.AlgebraicGeometry.ProjShifted

open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule (shiftedGrading tensorGrading)

universe u w t

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The sheaf `M(a)~` on `Proj(S)` associated to the shifted graded module, which is the target
of Tag 01MU's comparison map. -/
noncomputable example {M : Type u} [AddCommGroup M] [Module S M] {τ : Type t} [SetLike τ M]
    [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]
    (a : ℤ) :
    SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) :=
  associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 a)

/-- The canonical map `M̃ ⊗ 𝒪(a) → M(a)~` on `Proj(S)`: the associated-sheaf tensor map
followed by the sheaf map induced by the right unitor `M ⊗_S S(a) → M(a)`. This is the third
canonical morphism of the source's section on invertible sheaves on `Proj`. -/
noncomputable def moduleTwistMap
    {M : Type u} [AddCommGroup M] [Module S M]
    {τ : Type t} [SetLike τ M] [AddSubgroupClass τ M]
    (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]
    (a : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((AlgebraicGeometry.Proj
      𝒮).toRingedSpace)).presheaf, (((AlgebraicGeometry.Proj
      𝒮).toRingedSpace)).IsSheaf⟩).obj ((associatedModuleSheaf 𝒮 𝒨))).obj ((twistingSheaf 𝒮 a))) ⟶
      associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 a) := by
  letI := tensorGrading_decomposition (S := S) 𝒮 𝒨
    (twistGrading (S := S) 𝒮 a)
  letI := tensorGrading_gradedSMul (S := S) 𝒮 𝒨
    (twistGrading (S := S) 𝒮 a)
  exact associatedModuleSheafTensorMap 𝒮 𝒨
      (twistGrading (S := S) 𝒮 a) ≫
    associatedModuleSheafMap 𝒮
      (tensorGrading 𝒨
        (twistGrading (S := S) 𝒮 a))
      (shiftedGrading 𝒨 a)
      (TensorProduct.rid S M).toLinearMap
      (Stacks.GradedModule.rid_mem_shiftedGrading 𝒮 𝒨 a)

add_to_stacks 01MQ moduleTwistMap

end Stacks.AlgebraicGeometry.ProjShifted

end
