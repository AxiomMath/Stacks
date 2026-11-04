module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic

/-!
# The twisted sheaf of a graded module, under its two constructions

[Stacks, Tag 01YS] clause (5) and neighbouring results are proved in this development against
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`, the `n`-th twist `ℱ(n) = ℱ ⊗
𝒪_X(n)` of an arbitrary sheaf of `𝒪_X`-modules, built as the sheafification of the sectionwise
tensor product `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`. [Stacks, Tag 01MT]'s
comparison `moduleTwistIso`, proved in `ProjTwistDegreeOneCover/Basic.lean` from the source's own
hypothesis `DegreeOneCover`, instead identifies the shifted graded module's sheaf `M(n)~` with
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, a *different-looking* sectionwise
tensor product built directly on a ringed space rather than on an arbitrary site with a sheaf of
rings. Nothing in either file states that these two notions of "the twist of a graded module's
sheaf" agree.

They do, and not merely up to a canonical isomorphism: once the common ambient ringed space
`Proj 𝒮` is fixed, `TensorSheafification.tensorSheaf` and `TensorStalkRingedSpace.tensorSheaf`
are **definitionally equal** (`twistSheafOfModules_eq_tensorSheaf` below, by `rfl`). Both
sheafify a sectionwise tensor product of presheaves of modules against
`AlgebraicGeometry.Proj.structureSheafRing`-shaped data, and that data coincides on the nose:
`TensorStalkRingedSpace.O`, `.presheafTensorObj`, `.presheafTensor` and `.sheafifyFunctor`
reduce termwise to `TensorSheafification.structureRingPresheaf`, `.tensorPresheaf`'s object map
on the native monoidal tensor product of `Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`,
and `.sheafify`, respectively, so the two sheafified module structures are built from the same
presheaf by the same sheafification functor. Composing `twistSheafOfModules_eq_tensorSheaf`
with `moduleTwistIso` therefore identifies the two apparatuses outright:
`apparatusBridge` below is `M(n)~ ≅ ℱ(n)` with `ℱ = M̃`, under Tag 01MT's hypothesis, with no
extra naturality argument needed — the underlying morphism is `moduleTwistIso`'s own, merely
reinterpreted at an equal type.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistSheafOfModules_eq_tensorSheaf`: for
  every sheaf of `𝒪_X`-modules `F`, `F(n)` in the `twistSheafOfModules` sense is *equal*, not
  merely isomorphic, to `F ⊗ 𝒪_X(n)` in the `TensorStalkRingedSpace.tensorSheaf` sense.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.apparatusBridge`: under Tag 01MT's
  hypothesis `DegreeOneCover`, the shifted graded module's sheaf `M(n)~` is isomorphic to the
  twist `M̃(n)` of the associated module sheaf, in the `twistSheafOfModules` sense.

## References

* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover

universe u w t

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The two sectionwise-tensor-product constructions of the twist of a sheaf of modules on
`Proj 𝒮` agree on the nose.** `twistSheafOfModules`, used throughout this development, and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, the construction `moduleTwistIso`
is stated over, both sheafify a sectionwise tensor product of presheaves of modules against the
same presheaf of rings, by the same sheafification functor; the identification of the module-cat
tensor product `F ⊗ G` with the explicit sectionwise one holds termwise, so the whole comparison
is `rfl`. -/
public theorem twistSheafOfModules_eq_tensorSheaf
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) (n : ℤ) :
    twistSheafOfModules 𝒮 F n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf,
          (AlgebraicGeometry.Proj 𝒮).toRingedSpace.IsSheaf⟩).obj F).obj (twistingSheaf 𝒮 n) :=
  rfl

variable {M : Type u} [AddCommGroup M] [Module S M] {τ : Type t} [SetLike τ M]
  [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- **The bridge between the two spellings of the twist of a graded module's sheaf.** Under
Tag 01MT's hypothesis `DegreeOneCover`, the shifted graded module's sheaf `M(n)~` is isomorphic
to `M̃(n)`, the `n`-th twist of the associated module sheaf `M̃` in the `twistSheafOfModules`
sense used by the rest of this development. The underlying morphism is exactly
`moduleTwistIso`'s; `twistSheafOfModules_eq_tensorSheaf` only reinterprets its codomain at an
equal, differently-spelled type, so this carries every compatibility `moduleTwistIso` itself
carries. -/
@[ega "II 2.5.15" "more general", ega "II 3.2.8" "special case"]
public def apparatusBridge (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n) ≅
      twistSheafOfModules 𝒮 (associatedModuleSheaf 𝒮 𝒨) n :=
  (twistSheafOfModules_eq_tensorSheaf 𝒮 (associatedModuleSheaf 𝒮 𝒨) n) ▸
    (moduleTwistIso 𝒮 𝒨 hcover n).symm

end Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover

end
