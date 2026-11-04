module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.FiberIso
public import StacksFrontier.AlgebraicGeometry.AmplePowerImmersionCover.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic

/-!
# Ampleness from a closed subscheme of the base

Let `f : X ⟶ S` be proper, `i : S₀ ⟶ S` a closed immersion through which every closed point of
`S` factors, and `X₀ = X ×_S S₀`. An invertible `ℒ` on `X` whose restriction to `X₀` is ample is
ample when `S` is affine: by [Stacks, Tag 0D2S] it is relatively ample over a neighbourhood of
every closed point of `S`, hence over `S`.

## Main results

* `Stacks.PolarizedAlgebraization.isAmple_of_isPullback`.

## References

* [Stacks Project, Tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S)
* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample (IsAmple IsInvertibleModule)

universe u

namespace Stacks.PolarizedAlgebraization

variable {X S X₀ S₀ : Scheme.{u}} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {j : X₀ ⟶ X} {i : S₀ ⟶ S}

/-- **An invertible module over an affine base whose restriction to the part of `X` over a closed
subscheme of the base containing every closed point is ample, is ample.** -/
theorem isAmple_of_isPullback (h : IsPullback j f₀ f i) [IsClosedImmersion i]
    (hcl : ∀ s : S, IsClosed ({s} : Set S) → s ∈ Set.range i)
    [IsProper f] [IsAffine S] (L : X.Modules) [IsInvertibleModule X L]
    (L₀ : X₀.Modules) [IsInvertibleModule X₀ L₀] (hL₀ : IsAmple X₀ L₀)
    (e : (Scheme.Modules.pullback j).obj L ≅ L₀) :
    IsAmple X L := by
  -- The restriction of `ℒ` to the fibre over every closed point of `S` is ample.
  have hfib : ∀ s : S, IsClosed ({s} : Set S) →
      IsAmple (f.fiber s) (Stacks.AmpleLocallyClosed.pullbackModule (f.fiberι s) L) := by
    intro s hs
    obtain ⟨s₀, rfl⟩ := hcl s hs
    have hpre : i.base ⁻¹' {i s₀} = {s₀} :=
      Set.ext fun x => ⟨fun hx => i.isClosedEmbedding.injective hx, fun hx => hx ▸ rfl⟩
    have hs₀ : IsClosed ({s₀} : Set S₀) := hpre ▸ hs.preimage i.base.hom.continuous
    have := isClosed_singleton_iff_isClosedImmersion.mp hs₀
    have : IsClosedImmersion (f₀.fiberι s₀) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (IsPullback.of_hasPullback f₀ (S₀.fromSpecResidueField s₀)).flip inferInstance
    let φ := fiberIsoOfIsPullback h s₀
    have h₁ := Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion
      (f₀.fiberι s₀) L₀ hL₀
    have h₂ := Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion φ.inv _ h₁
    have hfac : f.fiberι (i s₀) = φ.inv ≫ f₀.fiberι s₀ ≫ j := by
      rw [← fiberIsoOfIsPullback_hom_fiberι h s₀, Iso.inv_hom_id_assoc]
    let e' : Stacks.AmpleLocallyClosed.pullbackModule (f.fiberι (i s₀)) L ≅
        Stacks.AmpleLocallyClosed.pullbackModule φ.inv
          (Stacks.AmpleLocallyClosed.pullbackModule (f₀.fiberι s₀) L₀) :=
      Stacks.RelativeAmpleBaseChange.pullbackModuleCongr hfac L ≪≫
        Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso φ.inv (f₀.fiberι s₀ ≫ j) L ≪≫
        (RingedSpaceModuleAdjunction.modulePullback φ.inv.toLRSHom.toShHom).mapIso
          (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso (f₀.fiberι s₀) j L ≪≫
            (RingedSpaceModuleAdjunction.modulePullback
              (f₀.fiberι s₀).toLRSHom.toShHom).mapIso e)
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e').mpr h₂
  -- `ℒ` is relatively ample over a neighbourhood of every point of `S`: every point specializes
  -- to a closed point, and every open neighbourhood of that closed point contains the point.
  have hloc : ∀ y : S, ∃ V : S.Opens, y ∈ V ∧
      Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V)
        (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V).ι L) := by
    intro y
    obtain ⟨s, hsy, hs⟩ :=
      (isClosed_closure : IsClosed (closure ({y} : Set S))).exists_closed_singleton
        ⟨y, subset_closure rfl⟩
    obtain ⟨V, hsV, hV⟩ :=
      Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre f L s (hfib s hs)
    refine ⟨V, ?_, hV⟩
    by_contra hy
    have hsub : closure ({y} : Set S) ⊆ (V : Set S)ᶜ :=
      closure_minimal (Set.singleton_subset_iff.mpr hy) V.isOpen.isClosed_compl
    exact hsub hsy hsV
  choose V hyV hV using hloc
  have hcov : (⨆ y, V y) = ⊤ :=
    top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyV y⟩
  exact (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mp
    (Stacks.AmplePowerImmersionCover.isRelativelyAmple_of_forall_isRelativelyAmple_morphismRestrict
      f L inferInstance V hcov hV)

end Stacks.PolarizedAlgebraization

end
