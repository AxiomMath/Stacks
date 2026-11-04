module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.MemberChart
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 01VR: relative very ampleness is local on the base

Let `f : X ⟶ S` be a quasi-compact morphism of schemes and `L` an invertible `𝒪_X`-module.
[Stacks, Tag 01VR] says that the following are equivalent:

1. `L` is relatively very ample on `X/S` ([Stacks, Tag 01VM]);
2. there is an open covering `S = ⋃ V_j` such that `L|_{f⁻¹(V_j)}` is relatively very ample on
   `f⁻¹(V_j)/V_j` for every `j`;
3. there are a quasi-coherent graded `𝒪_S`-algebra `A` generated in degree one and a map of graded
   `𝒪_X`-algebras `ψ : f^* A ⟶ ⨁_{n ≥ 0} L^{⊗ n}` such that `f^* A_1 ⟶ L` is surjective and
   `r_{L, ψ} : X ⟶ Proj_S(A)` is an immersion;
4. `f` is quasi-separated, the canonical map `f^* f_* L ⟶ L` is surjective and the associated
   morphism `r_{L, ψ} : X ⟶ 𝐏(f_* L)` is an immersion.

The proof is the source's. (1) ⟹ (2) is the restriction of relative very ampleness to an open of
the base, `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_morphismRestrict`, a consequence of
[Stacks, Tag 0B3F]. (4) ⟹ (3) takes `A = Sym(f_* L)`, and (3) ⟹ (1) and (4) ⟹ (1) are
`Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_hasImmersionToRelativeProj` and
`Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_isImmersionDirectImageBundle`. For (2) ⟹ (4):
`f` is separated, being so over each `V_j` ([Stacks, Tag 01VQ]); around every point of `X` some
section of `f_* L` over an affine open of `S` does not vanish and the chart of `r_{L, ψ}` at it is
an immersion (`Stacks.Tag01VMVeryAmple.exists_isImmersion_chart_of_member`), which gives both the
surjectivity of `f^* f_* L ⟶ L` and, by locality on the target, that `r_{L, ψ}` is an immersion.

## Main definitions

* `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmpleLocallyOnBase`: **clause (2) of Tag 01VR.**

Clauses (3) and (4) are `Stacks.Tag01VMVeryAmple.HasImmersionToRelativeProj` and
`Stacks.Tag01VMVeryAmple.IsImmersionDirectImageBundle`.

## Main results

* `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmpleLocallyOnBase_of_isRelativelyVeryAmple`:
  (1) ⟹ (2).
* `Stacks.Tag01VMVeryAmple.isImmersionDirectImageBundle_of_isRelativelyVeryAmpleLocallyOnBase`:
  (2) ⟹ (4).
* `Stacks.Tag01VMVeryAmple.tfae_isRelativelyVeryAmple`: **Stacks Tag 01VR.**

## Implementation notes

**The member of the covering is the open subscheme `V_j` with the restricted morphism
`f ∣_ V_j : f⁻¹(V_j) ⟶ V_j`**, and the module on `f⁻¹(V_j)` is the pullback of `L` along the
inclusion, as in `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_morphismRestrict`.

**The graded maps `ψ` of clauses (3) and (4) are recorded in adjoint form**, as
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap`, the datum of
[Stacks, Tag 01O8] from which [Stacks, Tag 01O9] constructs `r_{L, ψ}`; see
`StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.MorphismToRelativeProj`.

## References

* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VQ](https://stacks.math.columbia.edu/tag/01VQ)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 0B3F](https://stacks.math.columbia.edu/tag/0B3F)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.QuasiProjectiveCompactification
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)

universe u

namespace Stacks.Tag01VMVeryAmple

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X S : Scheme.{u}}

/-! ### Stacks Tag 01VR, clause (2) -/

/-- **Clause (2) of Stacks Tag 01VR.** There is an open covering `S = ⋃ V_j` of the base such
that for every `j` the restriction of `L` to `f⁻¹(V_j)` is relatively very ample for the
restriction `f ∣_ V_j : f⁻¹(V_j) ⟶ V_j` of `f`. -/
def IsRelativelyVeryAmpleLocallyOnBase (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] : Prop :=
  ∃ (ι : Type u) (V : ι → S.Opens), iSup V = ⊤ ∧ ∀ j : ι,
    IsRelativelyVeryAmple (f ∣_ V j) ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L)

/-- **Stacks Tag 01VR, (1) implies (2)**, with the covering by `S` itself. -/
@[ega "II 4.4.5" "Necessity direction"]
theorem isRelativelyVeryAmpleLocallyOnBase_of_isRelativelyVeryAmple (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (h : IsRelativelyVeryAmple f L) :
    IsRelativelyVeryAmpleLocallyOnBase f L :=
  ⟨PUnit.{u + 1}, fun _ => ⊤, by simp only [ciSup_unique],
    fun _ => isRelativelyVeryAmple_morphismRestrict f L h ⊤⟩

/-! ### Stacks Tag 01VR, (2) implies (4) -/

/-- **Stacks Tag 01VR, (2) implies (4).** If `L` is relatively very ample over the members of an
open covering of the base then `f` is quasi-separated, `f^* f_* L ⟶ L` is surjective and
`r_{L, ψ} : X ⟶ 𝐏(f_* L)` is an immersion. -/
theorem isImmersionDirectImageBundle_of_isRelativelyVeryAmpleLocallyOnBase (f : X ⟶ S)
    [QuasiCompact f] (L : X.Modules) [IsInvertibleModule X L]
    (h : IsRelativelyVeryAmpleLocallyOnBase f L) : IsImmersionDirectImageBundle f L := by
  obtain ⟨ι, V, hcov, hV⟩ := h
  have hsep : IsSeparated f :=
    IsZariskiLocalAtTarget.of_iSup_eq_top V hcov fun j =>
      Stacks.Tag01VMRelativeVeryAmple.isSeparated_of_isRelativelyVeryAmple (f ∣_ V j) _
        (isRelativelyVeryAmple_isDegreeOneTwist _ _ (hV j))
  have : QuasiSeparated f := inferInstance
  have key : ∀ x : X, ∃ (W : S.Opens) (_ : IsAffineOpen W) (b : Γ(L, f ⁻¹ᵁ W)),
      x ∈ nonvanishingLocusOn L (f ⁻¹ᵁ W) b ∧
      IsImmersion ((((directImageSymPowerMap f L).affineDatum W).homogeneousRatios
        (genSection_mem _ W (ofSec f L W b)) le_rfl).toSpecAway one_pos) := by
    intro x
    obtain ⟨j, hj⟩ : ∃ j, f x ∈ V j := by
      have hx : f x ∈ (⨆ j, V j) := hcov ▸ trivial
      simpa [Opens.mem_iSup] using hx
    exact exists_isImmersion_chart_of_member f L (V j) (hV j) x hj
  have hepi : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L) := by
    have h := epi_adjoint_of_forall_mem_nonvanishingLocusOn f (N := L)
      (𝟙 ((Scheme.Modules.pushforward f).obj L)) fun x => by
        obtain ⟨W, -, b, hb, -⟩ := key x
        exact ⟨W, ofSec f L W b, hb⟩
    rwa [homEquiv_symm_id] at h
  refine ⟨inferInstance, hepi, ?_⟩
  rw [isImmersion_toRelativeProj_iff]
  refine isImmersion_globalMorphism_of_chartsAreImmersions _ _ fun x => ?_
  obtain ⟨W, hW, b, hb, himm⟩ := key x
  have hmem : (⟨x, hb.1⟩ : (f ⁻¹ᵁ W).toScheme) ∈
      ((directImageSymPowerMap f L).affineDatum W).nonvanishingOpenAt 1
        ⟨genSection _ W (ofSec f L W b), genSection_mem _ W (ofSec f L W b)⟩ := by
    rw [GradedPowerMap.nonvanishingOpenAt_affineDatum]
    have hc : (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
        ((Scheme.Modules.pushforward f).obj L)).componentEquiv W 1
        ⟨genSection _ W (ofSec f L W b), genSection_mem _ W (ofSec f L W b)⟩ =
        Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S
          ((Scheme.Modules.pushforward f).obj L)) W (ofSec f L W b) := by
      rw [Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.componentEquiv_apply]
      exact DirectSum.of_eq_same _ _
    rw [hc]
    exact (mem_nonvanishingOpenAt_directImageSymPowerMap_iff f L W (ofSec f L W b) x).mpr hb
  exact ⟨W, hW, genSection _ W (ofSec f L W b), genSection_mem _ W (ofSec f L W b),
    ⟨⟨x, hb.1⟩, hmem⟩, rfl, himm⟩

/-! ### Stacks Tag 01VR -/

/-- **Stacks Tag 01VR.** Let `f : X ⟶ S` be a quasi-compact morphism of schemes and `L` an
invertible `𝒪_X`-module. The following are equivalent:

1. `L` is relatively very ample on `X/S`;
2. there is an open covering `S = ⋃ V_j` such that `L|_{f⁻¹(V_j)}` is relatively very ample on
   `f⁻¹(V_j)/V_j` for all `j`;
3. there are a quasi-coherent graded `𝒪_S`-algebra `A` generated in degree one and a map of graded
   algebras `ψ : f^* A ⟶ ⨁_{n ≥ 0} L^{⊗ n}` such that `f^* A_1 ⟶ L` is surjective and the
   associated morphism `r_{L, ψ} : X ⟶ Proj_S(A)` is an immersion;
4. `f` is quasi-separated, the canonical map `f^* f_* L ⟶ L` is surjective and the associated
   morphism `r_{L, ψ} : X ⟶ 𝐏(f_* L)` is an immersion. -/
@[stacks 01VR, ega "II 4.4.5"]
theorem tfae_isRelativelyVeryAmple (f : X ⟶ S) [QuasiCompact f] (L : X.Modules)
    [IsInvertibleModule X L] :
    List.TFAE [IsRelativelyVeryAmple f L, IsRelativelyVeryAmpleLocallyOnBase f L,
      HasImmersionToRelativeProj f L, IsImmersionDirectImageBundle f L] := by
  tfae_have 1 → 2 := isRelativelyVeryAmpleLocallyOnBase_of_isRelativelyVeryAmple f L
  tfae_have 2 → 4 := isImmersionDirectImageBundle_of_isRelativelyVeryAmpleLocallyOnBase f L
  tfae_have 4 → 3 := hasImmersionToRelativeProj_of_isImmersionDirectImageBundle f L
  tfae_have 3 → 1 := isRelativelyVeryAmple_of_hasImmersionToRelativeProj L
  tfae_finish

end Stacks.Tag01VMVeryAmple

end
