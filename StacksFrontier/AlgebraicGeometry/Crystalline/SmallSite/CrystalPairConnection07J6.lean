module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineConnectionComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTaylorFirstOrder
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PairLevelForms

/-!
# The connection of [Stacks, Tag 07JG] is the canonical connection of [Stacks, Tag 07J6]

[Stacks, Lemma 60.17.3, Tag 07JG] attaches to a crystal `ℱ` in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)` the pair `(M, ∇)` with `M = lim_e Γ((X, T_e, δ̄), ℱ)`, and says
that `∇` is obtained by evaluating the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6]
on the finite thickenings `(X, T_e, δ̄)`.  The functor `...SmallSite.crystalPairFunctor` reads
`∇` off the Taylor expansion of `ℱ` over `D(1)`; this module proves that this **is** the
evaluation of the canonical connection: under the reduction
`M ⊗̂_D Ω_D ⟶ Γ(T_e, Ω_{T_e/S,δ̄}) ⊗_{Γ(T_e, 𝒪)} Γ(T_e, ℱ)` at the level `e`
(`...SmallSite.pairTensorLevel`, built from the reduction `Ω_D ⟶ Γ(T_e, Ω_{T_e/S,δ̄})` that is
compatible with `d`, `...SmallSite.pairFormsLevel_pairDerivation`), the image of `∇(m)` is the
canonical connection of the crystal at `T_e` applied to the image of `m`.

## Main results

* `...SmallSite.pairTensorLevel_crystalPairFunctor_nabla` — **the image of `∇(m)` at the level
  `e` is the canonical connection of [Stacks, Tag 07J6] on global sections over `T_e`, applied to
  the image of `m`.**
* `...SmallSite.firstOrderTensorInclusion_crystalConnection_crystalPairFunctor` — the same for
  the sheaf-level connection `∇ : ℱ_{T_e} ⟶ ℱ_{T_e} ⊗ Ω_{T_e/S,δ̄}` of
  `...SmallSite.crystalConnection`: read in the sections of `ℱ` over the first-order thickening,
  it is the image of `∇(m)` at the level `e`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- **The connection `∇` of the pair attached to a crystal is obtained by evaluating the canonical
connection of [Stacks, Tag 07J6] on the finite thickenings.**  For a crystal `ℱ` in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)`, an element `m` of `M = lim_e Γ((X, T_e, δ̄), ℱ)` and a level
`e`, the image of `∇(m) ∈ M ⊗̂_D Ω_D` in `Γ(T_e, Ω_{T_e/S,δ̄}) ⊗_{Γ(T_e, 𝒪)} Γ(T_e, ℱ)` is the
canonical connection of `ℱ` on the sections over `(X, T_e, δ̄)`, applied to the image of `m`. -/
@[stacks 07JG "for any surjective polynomial presentation g : A[x_i : i ∈ ι] → C, supplied as \
the WholeSpacePresentation instance (the default instance is the tautological one): the \
connection of the pair attached to a crystal is the canonical connection of 07J6 evaluated on the \
finite thickenings (X, T_e, δ̄): its image at each level e is the 07J6 \
connection of the crystal over T_e applied to the image of m"]
theorem pairTensorLevel_crystalPairFunctor_nabla (Fc : QuasiCoherentCrystal S) (e : ℕ)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    pairTensorLevel hp Fc e (((crystalPairFunctor hp).obj Fc).nabla m) =
      AffineConnection.connection (bijective_crysExtensionSectionsMap_levelObj hp Fc e)
        (pairComponent hp Fc e m) := by
  classical
  let x := pairComponent hp Fc e m
  let T := (pairFirstOrderHom hp Fc e x).support
  have hT : ∀ c ∉ T, levelTheta hp Fc e (Finsupp.single c 1) x = 0 := fun c hc ↦
    (pairFirstOrderHom_apply hp Fc e x c).symm.trans (Finsupp.notMem_support_iff.mp hc)
  exact (pairTensorLevel_pairConnection hp Fc e m T hT).trans
    (connection_levelObj_eq_sum hp Fc e x T hT).symm

/-- **The connection `∇` of the pair attached to a crystal is obtained by evaluating the
sheaf-level canonical connection of [Stacks, Tag 07J6] on the finite thickenings.**  For a crystal
`ℱ` in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`, an element `m` of
`M = lim_e Γ((X, T_e, δ̄), ℱ)` and a level `e`, the canonical connection
`∇ : ℱ_{T_e} ⟶ ℱ_{T_e} ⊗ Ω_{T_e/S,δ̄}` of `...SmallSite.crystalConnection`, applied to the image
of `m` over the whole of `T_e` and read in the sections of `ℱ` over the first-order thickening
`T'_e` through the canonical morphism `ℱ_{T_e} ⊗ Ω ⟶ p₀_* ℱ_{T'_e}`, is the image of `∇(m)` at
the level `e` read there through the canonical map `ω ⊗ s ↦ ω · p₀^* s`. -/
@[stacks 07JG "for any surjective polynomial presentation g : A[x_i : i ∈ ι] → C, supplied as \
the WholeSpacePresentation instance (the default instance is the tautological one): the \
connection of the pair attached to a crystal is the sheaf-level canonical connection of 07J6 \
evaluated on the finite thickenings (X, T_e, δ̄), level by level"]
theorem firstOrderTensorInclusion_crystalConnection_crystalPairFunctor
    (Fc : QuasiCoherentCrystal S) (e : ℕ) (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (firstOrderTensorInclusion Fc.obj (levelObj hp 0 e)).val.app (op ⊤)
        ((crystalConnection (levelObj hp 0 e) Fc.property.2).hom.app (op ⊤)
          (crysSiteRestrict Fc.obj ((levelObj hp 0 e).restrictOpenHom ⊤)
            (show Fc.obj.val.obj (op (levelObj hp 0 e)) from pairComponent hp Fc e m))) =
      crysSiteRestrict Fc.obj
        ((firstOrderThickeningCrysObject S (levelObj hp 0 e)).restrictOpenHom ⊤)
        (AffineConnection.diffAction Fc.obj (levelObj hp 0 e)
          (pairTensorLevel hp Fc e (((crystalPairFunctor hp).obj Fc).nabla m))) := by
  rw [pairTensorLevel_crystalPairFunctor_nabla]
  exact AffineConnection.firstOrderTensorInclusion_crystalConnection_top Fc.property.2 _ _

end Crystalline.GlobalCrystallineSituation.SmallSite

end
