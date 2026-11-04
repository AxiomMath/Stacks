module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementFibreProduct
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardPhRefinement

/-!
# Recognising ph coverings by refinement

A family of morphisms of schemes which are locally of finite type is a ph covering exactly
when some ph covering refines it, and exactly when the single morphism from the disjoint
union of its sources is a ph covering.

## Main results

* `AlgebraicGeometry.isPHCovering_tfae`: the three equivalent descriptions.

## References

* [Stacks Project, Tag 0ET9](https://stacks.math.columbia.edu/tag/0ET9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

private theorem isPHCovering_of_refinement {T : Scheme.{u}} {I : Type v} {K : Type w}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (Y : K → Scheme.{u}) (g : ∀ k, Y k ⟶ T)
    (hf : ∀ i, LocallyOfFiniteType (f i)) (hY : IsPHCovering Y g)
    (r : ({ I₀ := K, X := Y, f := g } : PreZeroHypercover T).Hom
      ({ I₀ := I, X := X, f := f } : PreZeroHypercover T)) :
    IsPHCovering X f := by
  rw [isPHCovering_iff] at hY ⊢
  refine ⟨hf, fun U hU => ?_⟩
  obtain ⟨E, hE, ⟨s⟩⟩ := hY.2 U hU
  refine ⟨E, hE, ⟨?_⟩⟩
  let Y₀ : PreZeroHypercover T := ⟨K, Y, g⟩
  let X₀ : PreZeroHypercover T := ⟨I, X, f⟩
  exact PreZeroHypercover.Hom.comp s
    { s₀ := r.s₀
      h₀ := fun k =>
        pullback.map (g k) U.ι (f (r.s₀ k)) U.ι (r.h₀ k) (𝟙 _) (𝟙 _)
          (by simp [r.w₀ k]) (by simp)
      w₀ := fun k => pullback.lift_snd _ _ _ :
      (Y₀.pullback₂ U.ι).Hom (X₀.pullback₂ U.ι) }

/-- A family of locally finite type morphisms is a ph covering if and only if some ph
covering refines it, if and only if its disjoint-union morphism is a ph covering. -/
@[stacks 0ET9]
public theorem isPHCovering_tfae {T : Scheme.{u}} {I : Type v} [Small.{u} I]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : ∀ i, LocallyOfFiniteType (f i)) :
    List.TFAE [
      IsPHCovering X f,
      ∃ (K : Type v) (Y : K → Scheme.{u}) (g : ∀ k, Y k ⟶ T),
        IsPHCovering Y g ∧
          Nonempty
            (({ I₀ := K, X := Y, f := g } : PreZeroHypercover T).Hom
              ({ I₀ := I, X := X, f := f } : PreZeroHypercover T)),
      IsPHCovering
        (fun _ : Unit ↦ ∐ X) (fun _ ↦ Sigma.desc f)] := by
  classical
  tfae_have 1 → 2 := fun h => ⟨I, X, f, h, ⟨PreZeroHypercover.Hom.id _⟩⟩
  tfae_have 2 → 1 := fun ⟨K, Y, g, hY, ⟨r⟩⟩ => isPHCovering_of_refinement X f Y g hf hY r
  tfae_have 1 → 3 := by
    intro h
    refine isPHCovering_of_refinement (fun _ : Unit ↦ ∐ X) (fun _ ↦ Sigma.desc f)
      X f (fun _ => ?_) h
        { s₀ := fun _ => ()
          h₀ := fun i => Sigma.ι X i
          w₀ := fun i => by simp }
    let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) hf
  tfae_have 3 → 1 := by
    intro h
    rw [isPHCovering_iff] at h ⊢
    refine ⟨hf, fun U hU => ?_⟩
    let : IsAffine U.toScheme := hU
    let X₀ : PreZeroHypercover T := ⟨I, X, f⟩
    let Z₀ : PreZeroHypercover T :=
      ⟨Unit, (fun _ : Unit ↦ ∐ X), fun _ ↦ Sigma.desc f⟩
    let ZU := Z₀.pullback₂ U.ι
    obtain ⟨E, hE, ⟨r⟩⟩ := h.2 U hU
    let C₀ : Scheme.OpenCover (∐ X) := sigmaOpenCover X
    have hcidx : C₀.I₀ = I := sigmaOpenCover_I₀ X
    have hCf (i : C₀.I₀) : C₀.f i = Sigma.ι X (hcidx ▸ i) := by cases hcidx; rfl
    let q (j : E.I₀) : E.X j ⟶ ∐ X :=
      r.h₀ j ≫ pullback.fst (Sigma.desc f) U.ι
    let V (j : E.I₀) : (E.X j).OpenCover := C₀.pullback₁ (q j)
    let D (j : E.I₀) : PreZeroHypercover (E.X j) :=
      C₀.toPreZeroHypercover.pullback₁ (q j)
    have hvIdx (j : E.I₀) : (V j).I₀ = C₀.I₀ :=
      PreZeroHypercover.pullback₁_I₀ (q j) C₀.toPreZeroHypercover
    let S (j : E.I₀) : (E.X j).OpenCover.{u} := (V j).ulift
    let τ (j : E.I₀) : (S j).toPreZeroHypercover.Hom (V j).toPreZeroHypercover :=
      { s₀ := fun x => (V j).idx x
        h₀ := fun _ => 𝟙 _
        w₀ := fun _ => rfl }
    let B (j : E.I₀) : PreZeroHypercover.{u} (E.X j) := (S j).toPreZeroHypercover
    let ρ (j : E.I₀) : (B j).Hom (V j).toPreZeroHypercover := τ j
    obtain ⟨G, hG, ⟨ψ⟩⟩ :=
      exists_standardPHCovering_refinement_bind_openCover hE S
    let XU := X₀.pullback₂ U.ι
    have hr (j : E.I₀) : r.h₀ j ≫ pullback.snd (Sigma.desc f) U.ι = E.f j := r.w₀ j
    have hq (j : E.I₀) : q j ≫ Sigma.desc f = E.f j ≫ U.ι := by
      calc q j ≫ Sigma.desc f
          = r.h₀ j ≫ (pullback.fst (Sigma.desc f) U.ι ≫ Sigma.desc f) := Category.assoc _ _ _
        _ = r.h₀ j ≫ (pullback.snd (Sigma.desc f) U.ι ≫ U.ι) :=
          congrArg (r.h₀ j ≫ ·) pullback.condition
        _ = E.f j ≫ U.ι := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.ι) (hr j))
    have hCX (l : C₀.I₀) : C₀.X l = X (hcidx ▸ l) := by cases hcidx; rfl
    have hCcomp (l : C₀.I₀) :
        eqToHom (hCX l) ≫ f (hcidx ▸ l) = C₀.f l ≫ Sigma.desc f := by
      cases hCX l
      rw [hCf]
      exact (Sigma.ι_desc f l).symm
    have hVobj (j : E.I₀) (l : (V j).I₀) :
        (V j).X l = pullback (q j) (C₀.f (hvIdx j ▸ l)) := by
      cases hvIdx j
      show (D j).X l = _
      simpa [D] using
        (PreZeroHypercover.pullback₁_X (q j) C₀.toPreZeroHypercover l)
    have hVfst (j : E.I₀) (l : (V j).I₀) :
        eqToHom (hVobj j l) ≫ pullback.fst (q j) (C₀.f (hvIdx j ▸ l)) =
          (V j).f l := by cases hvIdx j; rfl
    let idx (jk : (E.bind B).I₀) : I :=
      hcidx ▸ (hvIdx jk.1 ▸ (ρ jk.1).s₀ jk.2)
    let a (jk : (E.bind B).I₀) : (E.bind B).X jk ⟶ X (idx jk) :=
      (ρ jk.1).h₀ jk.2 ≫
        eqToHom (hVobj jk.1 ((ρ jk.1).s₀ jk.2)) ≫
        pullback.snd (q jk.1) (C₀.f (hvIdx jk.1 ▸ (ρ jk.1).s₀ jk.2)) ≫
        eqToHom (hCX (hvIdx jk.1 ▸ (ρ jk.1).s₀ jk.2))
    have ha (j : E.I₀) (k : (B j).I₀) :
        a ⟨j, k⟩ ≫ f (idx ⟨j, k⟩) = (B j).f k ≫ E.f j ≫ U.ι := by
      dsimp only [a, idx]
      let l : (V j).I₀ := (ρ j).s₀ k
      let c : C₀.I₀ := hvIdx j ▸ l
      let i : I := hcidx ▸ c
      calc
        _ = (ρ j).h₀ k ≫ eqToHom (hVobj j l) ≫
              pullback.snd (q j) (C₀.f c) ≫ (eqToHom (hCX c) ≫ f i) :=
                Category.assoc _ _ _
        _ = (ρ j).h₀ k ≫ eqToHom (hVobj j l) ≫
              pullback.snd (q j) (C₀.f c) ≫ (C₀.f c ≫ Sigma.desc f) := by
                rw [hCcomp]
        _ = (ρ j).h₀ k ≫ eqToHom (hVobj j l) ≫
              ((pullback.fst (q j) (C₀.f c) ≫ q j) ≫ Sigma.desc f) := by
                simpa [Category.assoc] using congrArg
                  (fun g => ((ρ j).h₀ k ≫ eqToHom (hVobj j l) ≫ g) ≫ Sigma.desc f)
                  (pullback.condition.symm)
        _ = (ρ j).h₀ k ≫ (V j).f l ≫ (q j ≫ Sigma.desc f) := by
              simpa [Category.assoc] using congrArg
                (fun g => ((ρ j).h₀ k ≫ g) ≫ (q j ≫ Sigma.desc f))
                (hVfst j l)
        _ = (ρ j).h₀ k ≫ (V j).f l ≫ (E.f j ≫ U.ι) := by
              simpa [Category.assoc] using congrArg
                (fun g => (ρ j).h₀ k ≫ (V j).f l ≫ g) (hq j)
        _ = (B j).f k ≫ E.f j ≫ U.ι := by
              have hρ : (ρ j).h₀ k ≫ (V j).f l = (B j).f k := by
                simp [l, (ρ j).w₀ k]
              simpa [Category.assoc] using
                congrArg (fun g => g ≫ (E.f j ≫ U.ι)) hρ
    exact ⟨G, hG, ⟨PreZeroHypercover.Hom.comp ψ
      { s₀ := idx
        h₀ := fun jk => pullback.lift (a jk) ((E.bind B).f jk) (ha jk.1 jk.2)
        w₀ := fun jk => pullback.lift_snd _ _ _ : (E.bind B).Hom XU }⟩⟩
  tfae_finish

end AlgebraicGeometry
