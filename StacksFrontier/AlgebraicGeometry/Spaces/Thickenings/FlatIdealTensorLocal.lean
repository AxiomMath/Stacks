module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FlatIdealTensorVanishing

/-!
# The action of the ideal of a base change on a module flat over the base is injective

Let `f : X ⟶ T` be a morphism of algebraic spaces, `Z_T ⊆ T` a closed subspace and
`Z = f⁻¹(Z_T)`.  If an `𝒪_X`-module `ℱ'` is flat over `T`, the action of the ideal of `Z` on `ℱ'`
is injective in the local form of `Deformation.ToposThickening.IdealTensorLocallyVanishes`.
The charts carrying an affine commutative square over `f` cover every chart of `X`, and on each of
them the Zariski opens of
`AlgebraicGeometry.Space.exists_open_sum_tmul_eq_zero_of_isFlatOver` cover it.

## Main results

* `AlgebraicGeometry.Space.idealTensorLocallyVanishes_of_isFlatOver`.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sheaves.LocalGeneration (restr restr_restr)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X T : AlgebraicSpaces B S hS}

/-- On a chart carrying an affine square over `f`, the vanishing sieve of a relation with
coefficients in the ideal of `f⁻¹(Z_T)`, pulled back to that chart, is a covering sieve. -/
theorem pullback_kernelTensorVanishingSieve_mem (f : X ⟶ T) (ZT : ClosedSubspaces B S hS T.1)
    (F' : SheafOfModules.{u} (ringSheaf (smallEtaleRingedTopos B S hS X).O))
    (hflat : IsFlatOver B S hS X.2 f.hom F') {W W₁ : SmallEtale B S hS X.1} (a₀ : W₁ ⟶ W)
    (hW₁ : HasAffineChartDiagram B S hS f W₁) {n : ℕ}
    (ε : Fin n → RingHom.ker ((smallEtaleRingedToposHom B S hS
      (subspaceInclusion B S hS X (preimageSubspace B S hS f ZT))).fSharp.hom.app (op W)).hom)
    (s : Fin n → F'.val.obj (op W))
    (hs : ∑ j, (ε j : (smallEtaleRingedTopos B S hS X).O.obj.obj (op W)) • s j = 0) :
    (Deformation.ToposThickening.kernelTensorVanishingSieve.{u, u + 1, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS
        (subspaceInclusion B S hS X (preimageSubspace B S hS f ZT))) F' ε s).pullback a₀ ∈
        SmallEtale.topology B S hS X.1 W₁ := by
  refine hW₁.2.elim fun V h' => h'.elim fun q hq => ?_
  let d : ChartDiagram B S hS X.1 T.1 f.hom :=
    { U := W₁, V := V, g := q, comm := hq.1.symm }
  have : IsAffine (chartScheme d.U) := hW₁.1
  have : IsAffine (chartScheme d.V) := hq.2
  have hs₁ := (Deformation.ToposThickening.sum_kernel_smul_eq_zero_iff.{u, u + 1, u, u + 1, u}
    (smallEtaleRingedToposHom B S hS
      (subspaceInclusion B S hS X (preimageSubspace B S hS f ZT))) F' _ _).1
    (Deformation.ToposThickening.sum_kernelRestr_smul_restr.{u, u + 1, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS
        (subspaceInclusion B S hS X (preimageSubspace B S hS f ZT))) F' a₀.op ε s hs)
  refine smallEtale_sieve_of_pointwise_covering B S hS X.1 W₁ _ (fun z => ?_)
  refine (exists_open_sum_tmul_eq_zero_of_isFlatOver B S hS f ZT F' hflat d
    (fun j => Deformation.ToposThickening.kernelRestr.{u, u + 1, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS
        (subspaceInclusion B S hS X (preimageSubspace B S hS f ZT))) a₀.op (ε j))
    (fun j => restr F' a₀.op (s j)) hs₁ z).elim fun V' hV' => ?_
  exact ⟨(chartOpens B S hS W₁).obj V', chartOpensHom B S hS X W₁ V',
    Deformation.ToposThickening.comp_mem_kernelTensorVanishingSieve.{u, u + 1, u, u + 1, u}
      _ F' ε s a₀ _ hV'.2,
    ⟨z, hV'.1⟩, rfl⟩

/-- **A module flat over `T` has an injective action of the ideal of `f⁻¹(Z_T)`**, in the local
form of `Deformation.ToposThickening.IdealTensorLocallyVanishes`.  This is the consequence of
Stacks 08MQ that the argument of Stacks 08VU uses. -/
theorem idealTensorLocallyVanishes_of_isFlatOver (f : X ⟶ T) (ZT : ClosedSubspaces B S hS T.1)
    (F' : SheafOfModules.{u} (ringSheaf (smallEtaleRingedTopos B S hS X).O))
    (hflat : IsFlatOver B S hS X.2 f.hom F') :
    Deformation.ToposThickening.IdealTensorLocallyVanishes.{u, u + 1, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS
        (subspaceInclusion B S hS X (preimageSubspace B S hS f ZT))) F' := by
  intro W n ε s hs
  refine ⟨Deformation.ToposThickening.kernelTensorVanishingSieve.{u, u + 1, u, u + 1, u} _ F' ε s,
    ?_, fun W' g hg => hg⟩
  have hP : Sieve.generate (fun W₁ (_ : W₁ ⟶ W) => HasAffineChartDiagram B S hS f W₁) ∈
      SmallEtale.topology B S hS X.1 W :=
    mem_topology_of_hasAffineChartDiagram B S hS f W _
      (fun W₁ a ha => ⟨W₁, 𝟙 _, a, ha, Category.id_comp a⟩)
  refine (SmallEtale.topology B S hS X.1).transitive hP _ (fun Y a ha => ?_)
  refine ha.elim fun W₁ h => h.elim fun k h => h.elim fun a₀ h => ?_
  rw [← h.2, Sieve.pullback_comp]
  exact (SmallEtale.topology B S hS X.1).pullback_stable k
    (pullback_kernelTensorVanishingSieve_mem B S hS f ZT F' hflat a₀ h.1 ε s
      ((Deformation.ToposThickening.sum_kernel_smul_eq_zero_iff.{u, u + 1, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS
          (subspaceInclusion B S hS X (preimageSubspace B S hS f ZT))) F' ε s).1 hs))

end AlgebraicGeometry.Space

end
