module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SplitOver
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Degree

/-!
# The number of sheets of a split finite étale morphism is its degree

Let `f : P ⟶ S` be finite étale and finite locally free of rank `d`, and let sheet data
`Stacks.Etale.IsSplitOver f q` be given over a nonempty `q : N ⟶ S`. Then there are exactly `d`
sheets: at a geometric point `z` of `N` the sheets give the `d` points of the geometric fibre of
`f` above `z ≫ q`, distinct sheets giving distinct points and every point coming from a sheet.

## Main results

* `Stacks.Etale.IsSplitOver.natCard_I_eq`: the number of sheets is the degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Etale.IsSplitOver

/-- **The number of sheets of a split finite étale morphism of degree `d` is `d`.** -/
theorem natCard_I_eq {P S N : Scheme.{u}} {f : P ⟶ S} [IsFinite f] [Etale f] {q : N ⟶ S}
    (h : IsSplitOver f q) (n : N) (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] :
    Nat.card h.I = d := by
  classical
  let Ω := AlgebraicClosure (N.residueField n)
  let z : Spec (.of Ω) ⟶ N :=
    Spec.map (CommRingCat.ofHom (algebraMap (N.residueField n) Ω)) ≫ N.fromSpecResidueField n
  let pt : Spec (.of Ω) := default
  have h₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd f (z ≫ q)) d :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback (IsPullback.of_hasPullback _ _)
  rw [Stacks.Morphisms.IsFiniteLocallyFreeOfRank.rank_eq_of_point _ pt h₁
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_natCard_sections (pullback.snd f (z ≫ q)))]
  let φ : h.I → { σ : Spec (.of Ω) ⟶ pullback f (z ≫ q) // σ ≫ pullback.snd _ _ = 𝟙 _ } :=
    fun i ↦ ⟨pullback.lift (z ≫ h.sheet i) (𝟙 _)
      (by rw [Category.assoc, h.sheet_comp, Category.id_comp]), pullback.lift_snd _ _ _⟩
  refine Nat.card_eq_of_bijective φ ⟨fun i j hij ↦ ?_, fun σ ↦ ?_⟩
  · by_contra hne
    have hfst : z ≫ h.sheet i = z ≫ h.sheet j := by
      have := congrArg (fun σ ↦ σ.1 ≫ pullback.fst f (z ≫ q)) hij
      change pullback.lift _ _ _ ≫ _ = pullback.lift _ _ _ ≫ _ at this
      rwa [pullback.lift_fst, pullback.lift_fst] at this
    exact (h.isEmpty_of_sheet_eq z hne hfst).false pt
  · set b := σ.1 ≫ pullback.fst f (z ≫ q)
    have hb : b ≫ f = z ≫ q := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, σ.2, Category.id_comp]
    obtain ⟨κ, Y, p, hp, i, hcov, hfac⟩ := h.exists_openCover z b hb
    obtain ⟨k, hk⟩ := hcov pt
    have := hp k
    have : IsIso (p k) := isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (top_unique fun x _ ↦ Subsingleton.elim pt x ▸ hk)
    exact ⟨i k, Subtype.ext (pullback.hom_ext
      ((pullback.lift_fst _ _ _).trans ((cancel_epi (p k)).1 (hfac k)).symm)
      ((pullback.lift_snd _ _ _).trans σ.2.symm))⟩

end Stacks.Etale.IsSplitOver

end
