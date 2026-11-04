module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealFiltration
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Homology.DerivedLinear

/-!
# Vanishing of coherent cohomology by dévissage to integral closed subschemes

Let `X` be a Noetherian scheme and `n` a natural number. If `Hⁿ(Z, 𝓘) = 0` for every integral
closed subscheme `i : Z ⟶ X` and every nonzero coherent sheaf of ideals `𝓘 ⊆ 𝒪_Z`, then
`Hⁿ(X, F) = 0` for every coherent `𝒪_X`-module `F`. This is the dévissage step of the proof of
[Stacks, Tag 0G5F], (3) ⇒ (1): choose the filtration of [Stacks, Tag 01YF], whose successive
quotients are direct images `i_* 𝓘`, run up it with the long exact sequences
`Hⁿ(X, F_j) → Hⁿ(X, F_{j+1}) → Hⁿ(X, F_{j+1}/F_j)`, and identify `Hⁿ(X, i_* 𝓘)` with
`Hⁿ(Z, 𝓘)` along the closed immersion `i`, which is affine ([Stacks, Tag 089W]).

## Main results

* `Stacks.Duality.Lichtenbaum.isZero_rightDerived_pushforward_iff`: for an affine morphism
  `i : Z ⟶ X` and a quasi-coherent `G` on `Z`, `Hⁿ(X, i_* G)` vanishes if and only if
  `Hⁿ(Z, G)` does.
* `Stacks.Duality.Lichtenbaum.isZero_rightDerived_of_forall_integral_ideal`: the dévissage.

## Implementation notes

Cohomology is the right derived functor of the global sections functor
`SheafOfModules.evaluation X.ringCatSheaf (op ⊤)` on `X.Modules`, which is the cohomology
`AlgebraicGeometry.cohomologyOverField` of [Stacks, Tag 0FVV] part (6) before restriction of
scalars to the ground field.

## References

* [Stacks Project, Tag 0G5F](https://stacks.math.columbia.edu/tag/0G5F)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Duality.Lichtenbaum

/-- **Cohomology along an affine morphism detects vanishing.** For `i : Z ⟶ X` affine and `G`
quasi-coherent on `Z`, `Hⁿ(X, i_* G) = 0` if and only if `Hⁿ(Z, G) = 0`; the two groups are
isomorphic by [Stacks, Tag 089W]. -/
theorem isZero_rightDerived_pushforward_iff {X Z : Scheme.{u}} (i : Z ⟶ X) [IsAffineHom i]
    (G : Z.Modules) [G.IsQuasicoherent] (n : ℕ) :
    IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived n).obj
        ((Scheme.Modules.pushforward i).obj G)) ↔
      IsZero (((AlgebraicGeometry.moduleGlobalSections Z).rightDerived n).obj G) := by
  have key : ∀ (M : ModuleCat.{u} Γ(Z, ⊤)),
      IsZero ((ModuleCat.restrictScalars i.appTop.hom).obj M) ↔ IsZero M := fun M => by
    simp only [ModuleCat.isZero_iff_subsingleton]
    rfl
  exact (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward i G n).isZero_iff.symm.trans
    (key _)

/-- **Dévissage of top cohomology to integral closed subschemes.** On a Noetherian scheme `X`,
if `Hⁿ(Z, 𝓘)` vanishes for every integral closed subscheme `i : Z ⟶ X` and every nonzero
coherent sheaf of ideals `𝓘 ⊆ 𝒪_Z`, then `Hⁿ(X, F)` vanishes for every coherent `F`.

This is the second paragraph of the proof of [Stacks, Tag 0G5F], read contrapositively: the
filtration of [Stacks, Tag 01YF] has successive quotients `i_* 𝓘`, and the long exact sequences
of cohomology carry vanishing up the filtration. -/
theorem isZero_rightDerived_of_forall_integral_ideal (X : Scheme.{u}) [IsNoetherian X] (n : ℕ)
    (h : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (_root_.SheafOfModules.unit Z.ringCatSheaf).Submodule), I.toSheafOfModules.IsCoherent →
      ¬ IsZero I.toSheafOfModules →
      IsZero (((AlgebraicGeometry.moduleGlobalSections Z).rightDerived n).obj
        I.toSheafOfModules))
    (F : X.Modules) [F.IsCoherent] :
    IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived n).obj F) := by
  obtain ⟨m, G, hG, hbot, htop, -, hquot⟩ :=
    Stacks.AlgebraicGeometry.CoherentDevissage.exists_filtration_by_integral_ideal_pushforwards
      X F
  let Q := (AlgebraicGeometry.moduleGlobalSections X).rightDerived n
  have key : ∀ j : Fin (m + 1), IsZero (Q.obj (G j : X.Modules)) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      rw [hbot]
      have := Stacks.DerivedLinear.rightDerived_additive (moduleGlobalSections X) n
      exact Q.map_isZero (isZero_zero X.Modules |>.of_iso Subobject.botCoeIsoZero)
    | succ j ih =>
      obtain ⟨Z, i, hi, hZ, I, hIc, hI0, ⟨e⟩⟩ := hquot j
      let g := Subobject.ofLE (G j.castSucc) (G j.succ) (hG j.castSucc_le_succ)
      have hS : (ShortComplex.mk g (cokernel.π g) (cokernel.condition g)).ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel g)
          mono_f := inferInstance
          epi_g := inferInstance }
      have := isQuasicoherent_of_isCoherent I.toSheafOfModules
      refine Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂ hS _ n ih ?_
      exact (Q.mapIso e).isZero_iff.mpr
        ((isZero_rightDerived_pushforward_iff i _ n).mpr (h Z i I hIc hI0))
  have hF := key (Fin.last m)
  rw [htop, Subobject.top_eq_id] at hF
  exact hF.of_iso (Q.mapIso (Subobject.underlyingIso (𝟙 F))).symm

end Stacks.Duality.Lichtenbaum
