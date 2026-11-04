module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit

/-!
# Directed colimits of formal algebraic spaces along closed immersions

Let `S` be a scheme contained in a big fppf site `B` and let `(X_λ, f_{λμ})` be a directed
system of *formal* algebraic spaces over `S` in which every transition morphism
`f_{λμ} : X_λ ⟶ X_μ` is a closed immersion inducing an isomorphism `X_{λ,red} ⟶ X_{μ,red}`.
**Stacks 0GVN** says that the colimit `X = colim_λ X_λ`, formed among fppf sheaves, is again a
formal algebraic space over `S`.

This file proves the passage from charts on the stages to an atlas of the colimit: given diagrams
`G k` with maps `α k : G k ⟶ E` to the system that are representable étale, cartesian over the
colimit and jointly surjective at every stage, whose colimits are affine formal algebraic spaces,
and given that every scheme-valued point of `colim E` factors through a stage, the colimits
`colim (G k)` form an atlas of `colim E` as in Definition 0AIM.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_chartSystem`: a sheaf isomorphic to
  the colimit of a diagram of fppf sheaves which satisfies the set-theoretic condition of
  Stacks 0AIS and carries a system of charts whose colimits are affine formal algebraic spaces
  is a formal algebraic space.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0GVL](https://stacks.math.columbia.edu/tag/0GVL)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `E` be a diagram of fppf sheaves over `S` indexed by a preorder, and let `G` be a family
of diagrams on the same index with morphisms `α k : G k ⟶ E` such that each `(α k).app i` is
representable étale, each square

```
(G k).obj i ⟶ colim (G k)
     ↓               ↓
   E.obj i    ⟶    colim E
```

is cartesian, and the `(α k).app i` jointly cover `E.obj i` for every `i`. If moreover every
scheme-valued point of `colim E` factors through a stage and each `colim (G k)` is an affine
formal algebraic space, then a sheaf `Z` isomorphic to `colim E` which satisfies the
set-theoretic condition of Stacks 0AIS is a formal algebraic space over `S`: the morphisms
`colim (G k) ⟶ Z` form an atlas as in Definition 0AIM. -/
theorem isFormalAlgebraicSpace_of_chartSystem
    {Λ : Type (u + 1)} [Preorder Λ] (E : Λ ⥤ FppfSheaf B S hS)
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (haff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (colimit (G k)))
    (hαet : ∀ (k : I) (i : Λ), IsRepresentableEtale B S hS ((α k).app i))
    (hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ i : Λ, Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app i)))
    (hfac : ∀ (U : BigFppfOver B S hS)
      (ξ : (uliftYoneda.{u + 1}).obj U ⟶ (colimit E).obj),
      ∃ (i : Λ) (ξ' : (uliftYoneda.{u + 1}).obj U ⟶ (E.obj i).obj),
        ξ = ξ' ≫ (colimit.ι E i).hom)
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨eZ⟩ := hZ
  refine ⟨hZset, I, (fun k ↦ colimit (G k)), (fun k ↦ colimMap (α k) ≫ eZ.inv), haff, ?_, ?_⟩
  · intro k
    refine isRepresentableEtale_of_stageSquares B S hS (colimMap (α k) ≫ eZ.inv)
      (fun i ↦ colimit.ι (G k) i) (fun i ↦ (α k).app i)
      (fun i ↦ colimit.ι E i ≫ eZ.inv) (hαet k) (fun i ↦ ?_) (fun U ξ ↦ ?_)
    · exact (hsq k i).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eZ.symm
        (by simp) (by simp) (by simp) (by simp)
    · obtain ⟨i, ξ', hξ⟩ := hfac U (ξ ≫ eZ.hom.hom)
      refine ⟨i, ξ', ?_⟩
      have h : (colimit.ι E i ≫ eZ.inv).hom = (colimit.ι E i).hom ≫ eZ.inv.hom := rfl
      rw [h, ← Category.assoc, ← hξ]
      simp
  · rw [Sheaf.isLocallySurjective_iff_epi]
    refine ⟨?_⟩
    intro T k l hkl
    have hζkl : ∀ m : I, (colimMap (α m) ≫ eZ.inv) ≫ k = (colimMap (α m) ≫ eZ.inv) ≫ l := by
      intro m
      have h := congrArg (fun t ↦ Sigma.ι (fun m : I ↦ colimit (G m)) m ≫ t) hkl
      simpa using h
    have hcolim : eZ.inv ≫ k = eZ.inv ≫ l := by
      refine colimit.hom_ext (fun i ↦ ?_)
      have hepi : Epi (Sigma.desc (fun m ↦ (α m).app i)) :=
        (Sheaf.isLocallySurjective_iff_epi _).mp (hcov i)
      refine (cancel_epi (Sigma.desc (fun m ↦ (α m).app i))).1 (Sigma.hom_ext _ _ (fun m ↦ ?_))
      have hm := hζkl m
      simp only [Category.assoc] at hm
      have hm2 := congrArg (fun t ↦ colimit.ι (G m) i ≫ t) hm
      simp only [ι_colimMap_assoc] at hm2
      simpa using hm2
    exact (cancel_epi eZ.inv).1 hcolim

end AlgebraicGeometry.FormalSpace

end
