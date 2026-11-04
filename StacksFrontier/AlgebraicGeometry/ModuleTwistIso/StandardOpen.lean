module

public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.SheafMultiplication
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic

/-!
# Twisting sheaves on a standard open of `Proj`

Let `S` be a graded ring, `X = Proj(S)` and let `f ∈ S` be homogeneous of degree `d`. On the
standard open `D₊(f)` the twisting sheaves `𝒪_X(nd)` are trivial, hence invertible, and the three
families of canonical multiplication maps built from them are isomorphisms.

## Main results

* `Stacks.AlgebraicGeometry.ModuleTwistIso.twistsOnBasicOpen`: the conjunction of these five
  assertions for one homogeneous `f`, each quantified over the integer indices, over the sheaf of
  modules and over the graded module.

## Implementation notes

The triviality and invertibility conjuncts are stated on the restricted site, where restriction
is `SheafOfModules.over`; the conjuncts on the comparison maps restrict them by
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` along the open immersion of `D₊(f)`. The
former write the multiple of the degree as `n * d`, the latter as `(d : ℤ) * n`.

The degree `d` is not assumed positive.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjShifted
open Stacks.AlgebraicGeometry.ProjTrivialization
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ModuleTwistIso

universe u w t

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The homogeneous prime ideal of a point of `Proj(S)` is prime as an ideal of `S`. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- Let `f ∈ S` be homogeneous of degree `d`. Restricted to the standard open `D₊(f)`, the twisting
sheaf `𝒪_X(nd)` is invertible and in fact trivial for every integer `n`, and the three families of
canonical maps built from it are isomorphisms: `𝒪_X(nd) ⊗ 𝒪_X(m) ⟶ 𝒪_X(nd+m)`,
`𝒪_X(nd) ⊗ ℱ(m) ⟶ ℱ(nd+m)` for every sheaf of `𝒪_X`-modules `ℱ`, and `M̃ ⊗ 𝒪_X(nd) ⟶ M(nd)~` for
every graded `S`-module `M`. The second index is arbitrary throughout, and `d` is not assumed
positive. -/
@[stacks 01MS "the lemma's five assertions in one statement"]
theorem twistsOnBasicOpen {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) :
    (∀ n : ℤ, _root_.AlgebraicGeometry.SheafOfModules.IsInvertible
        ((Over.forget (ProjectiveSpectrum.basicOpen 𝒮 f)).op ⋙
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj)
        ((projRingSheaf 𝒮).over (ProjectiveSpectrum.basicOpen 𝒮 f)).property
        ((twistingSheaf 𝒮 (n * d)).over (ProjectiveSpectrum.basicOpen 𝒮 f))) ∧
      (∀ n : ℤ, _root_.AlgebraicGeometry.SheafOfModules.IsTrivial
        ((Over.forget (ProjectiveSpectrum.basicOpen 𝒮 f)).op ⋙
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj)
        ((projRingSheaf 𝒮).over (ProjectiveSpectrum.basicOpen 𝒮 f)).property
        ((twistingSheaf 𝒮 (n * d)).over (ProjectiveSpectrum.basicOpen 𝒮 f))) ∧
      (∀ n m : ℤ, IsIso
        ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒮 f).ι).map
          (twistMultiplicationMap 𝒮 ((d : ℤ) * n) m))) ∧
      (∀ (F : SheafOfModules.{u}
          ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) (n m : ℤ), IsIso
        ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒮 f).ι).map
          (twistSheafMultiplicationMap 𝒮 F ((d : ℤ) * n) m))) ∧
      (∀ (M : Type u) [AddCommGroup M] [Module S M] (τ : Type t) [SetLike τ M]
          [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
          [SetLike.GradedSMul 𝒮 𝒨] (n : ℤ), IsIso
        ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒮 f).ι).map
          (moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n)))) := by
  refine ⟨fun n => isInvertible_twistingSheafOverBasicOpen 𝒮 hf n,
    fun n => ⟨twistingSheafOverBasicOpenIsoUnit 𝒮 hf n⟩,
    fun n m => isIso_restrict_twistMultiplicationMap_basicOpen 𝒮 hf n m,
    fun F n m => isIso_restrict_twistSheafMultiplicationMap_basicOpen 𝒮 F hf n m,
    fun M _ _ τ _ _ 𝒨 _ _ n => isIso_restrict_moduleTwistMap_basicOpen 𝒮 𝒨 hf n⟩

end Stacks.AlgebraicGeometry.ModuleTwistIso

end
