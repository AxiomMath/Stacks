module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CoordinateContractionInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CoordinateProjectionSection

/-!
# The kernel pair of a projection between powers of the projective line

Let `k` be a field, `B` a big fppf site containing `Spec k`, and `J ⊆ I ⊆ Fin n` two finite sets
of coordinates.  The contraction step of [Stacks, Tag 0AEM] has to show that a morphism
`g : (ℙ¹_k)^I ⟶ Z` *factors through* the projection
`AlgebraicGeometry.Space.subsetProjection` onto the coordinates in `J`.  That projection is a
split epimorphism — the complementary coordinates can be given a fixed rational point — and a
split epimorphism is the coequalizer of its own kernel pair in any category whatsoever.  So the
factorization is equivalent to the single identity

`p₁ ≫ g = p₂ ≫ g`

for the two legs `p₁, p₂` of the kernel pair, and no descent, flatness or finite presentation
enters.

This file supplies that reduction together with an explicit model of the kernel pair: the fibre
product of `(ℙ¹_k)^I` with itself over `(ℙ¹_k)^J` is again a power of the projective line,
indexed by the coordinates in `I` outside `J` together with a second full copy of `I`.  A pair of
points of `(ℙ¹_k)^I` agreeing on `J` is exactly: a point of `(ℙ¹_k)^I`, and a choice of the
coordinates outside `J` of the other one.

## Main definitions

* `AlgebraicGeometry.Space.subsetProjectionSection`: the section of the projection which keeps
  the coordinates in `J` and gives every coordinate of `I` outside `J` the rational point all of
  whose homogeneous coordinates are `1`.
* `AlgebraicGeometry.Space.subsetComplIndex`: the coordinates of `I` outside `J`.
* `AlgebraicGeometry.Space.subsetKernelPairFst` and
  `AlgebraicGeometry.Space.subsetKernelPairSnd`: the two legs of the kernel pair.

## Main results

* `AlgebraicGeometry.Space.eq_comp_of_kernelPair_eq`: **a split epimorphism is the coequalizer
  of its own kernel pair.**  Pure category theory, stated for an arbitrary morphism with a
  section and a fibre product with itself.
* `AlgebraicGeometry.Space.isPullback_subsetKernelPair`: **the kernel pair of the projection is
  the power of the projective line indexed by `Iᶜ ⊕ I`.**
* `AlgebraicGeometry.Space.exists_eq_subsetProjection_comp_of_kernelPair_eq`: **the reduction** —
  a morphism out of `(ℙ¹_k)^I` whose two readings on that power agree factors through the
  projection onto the coordinates in `J`.

## References

* [Stacks Project, Tag 0AEL](https://stacks.math.columbia.edu/tag/0AEL)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

/-! ### A split epimorphism is the coequalizer of its own kernel pair -/

/-- **A split epimorphism is the coequalizer of its own kernel pair.**  If `π : X ⟶ Y` has a
section `σ` and `h : X ⟶ Z` takes the same value on the two legs of the fibre product of `π`
with itself, then `h` is `π` followed by `σ ≫ h`.

The pair `(𝟙 X, π ≫ σ)` lands in that fibre product, its two legs are `𝟙 X` and `π ≫ σ`, and
`h` does not distinguish them. -/
theorem eq_comp_of_kernelPair_eq {C : Type*} [Category.{v} C] {X Y Z : C} (π : X ⟶ Y)
    [HasPullback π π] (σ : Y ⟶ X) (hσ : σ ≫ π = 𝟙 Y) (h : X ⟶ Z)
    (hh : pullback.fst π π ≫ h = pullback.snd π π ≫ h) :
    h = π ≫ σ ≫ h := by
  have hw : (𝟙 X) ≫ π = (π ≫ σ) ≫ π := by
    rw [Category.id_comp, Category.assoc, hσ, Category.comp_id]
  calc h = (pullback.lift (𝟙 X) (π ≫ σ) hw ≫ pullback.fst π π) ≫ h := by
        rw [pullback.lift_fst, Category.id_comp]
    _ = (pullback.lift (𝟙 X) (π ≫ σ) hw ≫ pullback.snd π π) ≫ h := by
        rw [Category.assoc, Category.assoc, hh]
    _ = π ≫ σ ≫ h := by rw [pullback.lift_snd, Category.assoc]

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-! ### The projection onto a subset of the coordinates is split -/

/-- The section of the projection `(ℙ¹_k)^I ⟶ (ℙ¹_k)^J` which keeps the coordinates in `J` and
gives every coordinate of `I` outside `J` the rational point
`AlgebraicGeometry.Space.projectiveLinePoint`. -/
noncomputable def subsetProjectionSection {n : ℕ} {I J : Finset (Fin n)} (_h : J ⊆ I) :
    projectiveLinePower k B hk J ⟶ projectiveLinePower k B hk I :=
  Pi.lift fun i : I =>
    if hi : (i : Fin n) ∈ J then
      Pi.π (fun _ : J => projectiveLineFunctor k B hk) ⟨(i : Fin n), hi⟩
    else
      (base_isTerminal k B hk).from (projectiveLinePower k B hk J) ≫
        projectiveLinePoint k B hk

/-- **The projection onto the coordinates in `J ⊆ I` is a split epimorphism.** -/
theorem subsetProjectionSection_comp {n : ℕ} {I J : Finset (Fin n)} (h : J ⊆ I) :
    subsetProjectionSection k B hk h ≫ subsetProjection k B hk h =
      𝟙 (projectiveLinePower k B hk J) := by
  refine Pi.hom_ext _ _ fun j => ?_
  rw [Category.assoc, Pi.map'_comp_π, Category.comp_id, subsetProjectionSection, Pi.lift_comp_π,
    dite_eq_left (show ((⟨(j : Fin n), h j.2⟩ : I) : Fin n) ∈ J from j.2), Category.id_comp]

/-! ### The kernel pair -/

variable {n : ℕ}

/-- The coordinates of `I` lying outside `J`. -/
abbrev subsetComplIndex (I J : Finset (Fin n)) : Type :=
  {i : I // (i : Fin n) ∉ J}

/-- The first leg of the kernel pair of the projection `(ℙ¹_k)^I ⟶ (ℙ¹_k)^J`: it reads the
coordinates in `J` off the second copy of `I` and the coordinates outside `J` off the extra
block. -/
noncomputable def subsetKernelPairFst (I J : Finset (Fin n)) :
    projectiveLinePower k B hk (subsetComplIndex I J ⊕ I) ⟶ projectiveLinePower k B hk I :=
  Pi.map' (fun i : I => if hi : (i : Fin n) ∈ J then Sum.inr i else Sum.inl ⟨i, hi⟩)
    fun _ => 𝟙 _

/-- The second leg of the kernel pair of the projection `(ℙ¹_k)^I ⟶ (ℙ¹_k)^J`: it reads the
second block. -/
noncomputable def subsetKernelPairSnd (I J : Finset (Fin n)) :
    projectiveLinePower k B hk (subsetComplIndex I J ⊕ I) ⟶ projectiveLinePower k B hk I :=
  Pi.map' (Sum.inr : I → subsetComplIndex I J ⊕ I) fun _ => 𝟙 _

/-- For a coordinate `i ∈ I` lying in `J`, the first leg of the kernel pair reads coordinate `i`
off the second copy of `I`. -/
@[reassoc]
theorem subsetKernelPairFst_comp_π_of_mem {I J : Finset (Fin n)} (i : I)
    (hi : (i : Fin n) ∈ J) :
    subsetKernelPairFst k B hk I J ≫
        Pi.π (fun _ : I => projectiveLineFunctor k B hk) i =
      Pi.π (fun _ : subsetComplIndex I J ⊕ I => projectiveLineFunctor k B hk) (Sum.inr i) := by
  rw [subsetKernelPairFst, Pi.map'_comp_π, Category.comp_id, dite_eq_left hi]

/-- For a coordinate `i ∈ I` lying outside `J`, the first leg of the kernel pair reads coordinate
`i` off the block indexed by the coordinates of `I` outside `J`. -/
@[reassoc]
theorem subsetKernelPairFst_comp_π_of_notMem {I J : Finset (Fin n)} (i : I)
    (hi : (i : Fin n) ∉ J) :
    subsetKernelPairFst k B hk I J ≫
        Pi.π (fun _ : I => projectiveLineFunctor k B hk) i =
      Pi.π (fun _ : subsetComplIndex I J ⊕ I => projectiveLineFunctor k B hk)
        (Sum.inl ⟨i, hi⟩) := by
  rw [subsetKernelPairFst, Pi.map'_comp_π, Category.comp_id, dite_eq_right hi]

/-- The second leg of the kernel pair reads coordinate `i ∈ I` off the second copy of `I`. -/
@[reassoc]
theorem subsetKernelPairSnd_comp_π {I J : Finset (Fin n)} (i : I) :
    subsetKernelPairSnd k B hk I J ≫
        Pi.π (fun _ : I => projectiveLineFunctor k B hk) i =
      Pi.π (fun _ : subsetComplIndex I J ⊕ I => projectiveLineFunctor k B hk) (Sum.inr i) := by
  rw [subsetKernelPairSnd, Pi.map'_comp_π, Category.comp_id]

/-- The two legs agree after the projection: both read the coordinates in `J` off the second
block. -/
theorem subsetKernelPair_comp_subsetProjection {I J : Finset (Fin n)} (h : J ⊆ I) :
    subsetKernelPairFst k B hk I J ≫ subsetProjection k B hk h =
      subsetKernelPairSnd k B hk I J ≫ subsetProjection k B hk h := by
  refine Pi.hom_ext _ _ fun j => ?_
  simp only [Category.assoc, Pi.map'_comp_π, Category.comp_id]
  rw [subsetKernelPairFst_comp_π_of_mem k B hk (⟨(j : Fin n), h j.2⟩ : I) j.2,
    subsetKernelPairSnd_comp_π]

/-- **The power of the projective line indexed by the coordinates of `I` outside `J` together
with a second copy of `I` is the kernel pair of the projection onto the coordinates in `J`.**

A pair of points of `(ℙ¹_k)^I` agreeing on the coordinates in `J` is the same datum as one point
of `(ℙ¹_k)^I` and a choice of the coordinates outside `J` of the other point. -/
theorem isPullback_subsetKernelPair {I J : Finset (Fin n)} (h : J ⊆ I) :
    IsPullback (subsetKernelPairFst k B hk I J) (subsetKernelPairSnd k B hk I J)
      (subsetProjection k B hk h) (subsetProjection k B hk h) := by
  classical
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (subsetKernelPair_comp_subsetProjection k B hk h)
    (fun s => Pi.lift (Sum.elim
      (fun a : subsetComplIndex I J =>
        s.fst ≫ Pi.π (fun _ : I => projectiveLineFunctor k B hk) (a : I))
      (fun i : I => s.snd ≫ Pi.π (fun _ : I => projectiveLineFunctor k B hk) i)))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · refine Pi.hom_ext _ _ fun i => ?_
    by_cases hi : (i : Fin n) ∈ J
    · rw [Category.assoc, subsetKernelPairFst_comp_π_of_mem k B hk i hi, Pi.lift_comp_π]
      have hc := congrArg
        (fun a => a ≫ Pi.π (fun _ : J => projectiveLineFunctor k B hk) (⟨(i : Fin n), hi⟩ : J))
        (PullbackCone.condition s)
      simp only [Category.assoc, Pi.map'_comp_π, Category.comp_id] at hc
      refine Eq.trans ?_ (congrArg
        (fun a : I => s.fst ≫ Pi.π (fun _ : I => projectiveLineFunctor k B hk) a)
        (Subtype.ext rfl : (⟨((⟨(i : Fin n), hi⟩ : J) : Fin n), h (⟨(i : Fin n), hi⟩ : J).2⟩ : I)
          = i))
      exact hc.symm
    · rw [Category.assoc, subsetKernelPairFst_comp_π_of_notMem k B hk i hi, Pi.lift_comp_π]
      rfl
  · refine Pi.hom_ext _ _ fun i => ?_
    rw [Category.assoc, subsetKernelPairSnd_comp_π, Pi.lift_comp_π]
    rfl
  · refine Pi.hom_ext _ _ fun b => ?_
    rw [Pi.lift_comp_π]
    cases b with
    | inl a =>
      change m ≫ _ = s.fst ≫ Pi.π (fun _ : I => projectiveLineFunctor k B hk) (a : I)
      rw [← hm₁, Category.assoc, subsetKernelPairFst_comp_π_of_notMem k B hk (a : I) a.2]
    | inr i =>
      change m ≫ _ = s.snd ≫ Pi.π (fun _ : I => projectiveLineFunctor k B hk) i
      rw [← hm₂, Category.assoc, subsetKernelPairSnd_comp_π]

/-! ### The reduction -/

/-- **A morphism out of `(ℙ¹_k)^I` whose two readings on the kernel pair agree factors through
the projection onto the coordinates in `J`.**

The projection is split by `AlgebraicGeometry.Space.subsetProjectionSection`, hence is the
coequalizer of its own kernel pair, and the kernel pair is the power of the projective line
indexed by `Iᶜ ⊕ I` by `AlgebraicGeometry.Space.isPullback_subsetKernelPair`.  This is the only
thing the contraction step of [Stacks, Tag 0AEM] needs of [Stacks, Tag 0AEL]: no descent, no
flatness and no finite presentation. -/
theorem exists_eq_subsetProjection_comp_of_kernelPair_eq
    {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u} {I J : Finset (Fin n)}
    (h : J ⊆ I) (g : projectiveLinePower k B hk I ⟶ Z)
    (hg : subsetKernelPairFst k B hk I J ≫ g = subsetKernelPairSnd k B hk I J ≫ g) :
    ∃ g' : projectiveLinePower k B hk J ⟶ Z, g = subsetProjection k B hk h ≫ g' := by
  have := (isPullback_subsetKernelPair k B hk h).hasPullback
  refine ⟨subsetProjectionSection k B hk h ≫ g,
    eq_comp_of_kernelPair_eq (subsetProjection k B hk h) (subsetProjectionSection k B hk h)
      (subsetProjectionSection_comp k B hk h) g ?_⟩
  refine ((isPullback_subsetKernelPair k B hk h).isoPullback.cancel_iso_hom_left _ _).1 ?_
  rw [← Category.assoc, ← Category.assoc,
    (isPullback_subsetKernelPair k B hk h).isoPullback_hom_fst,
    (isPullback_subsetKernelPair k B hk h).isoPullback_hom_snd]
  exact hg

end AlgebraicGeometry.Space

end
