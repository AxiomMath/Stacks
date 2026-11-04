module

public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringComposition

/-!
# Refining a test space so that it maps to the members of an fpqc covering

Let `(w i : W i ⟶ R)` be an fpqc covering of algebraic spaces over a scheme `S` of a big fppf
site, and let `Z` be an algebraic space carrying one, two or three morphisms to `R`.  This file
produces an fpqc covering of `Z` each member of which maps to a member of the given family
**over each of those morphisms**: a morphism `Z' ⟶ W i` whose composite with `w i` is the
composite of `Z' ⟶ Z` with the given morphism to `R`.

For one morphism this is the base change of Stacks 03MR (3) and nothing more.  For two and three
it is that base change applied once per morphism and the results composed, which is Stacks 03MR
again — the composition clause.  No fibre product of `Z` is formed and none of the members is
identified with one: what is asked for is only the existence of the covering together with its
legs, and that is what the two successive base changes deliver.

This is the geometric input of the transitivity of effective descent: a pairwise isomorphism on
`R ×_X R` is built, and its cocycle condition checked, after pullback along a covering whose
members map to members of the given family over *both* projections, and a covering with that
property cannot be produced by refining `R ×_X R` after the fact.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_isFpqcCovering_leg`: one morphism.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_isFpqcCovering_legPair`: two morphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_isFpqcCovering_legTriple`: three
  morphisms.

## References

* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {R : AlgebraicSpaces B S hS} (W : I → AlgebraicSpaces B S hS)
  (w : ∀ i, W i ⟶ R)

/-- **A test space with one morphism to the target of an fpqc covering is covered, in the fpqc
topology, by spaces mapping to the members of that covering over it.**  This is the base change
of Stacks 03MR (3) of the given covering along the given morphism. -/
theorem exists_isFpqcCovering_leg (hw : IsFpqcCovering B S hS fun i => (w i).hom)
    {Z : AlgebraicSpaces B S hS} (p : Z ⟶ R) :
    ∃ (Z' : I → AlgebraicSpaces B S hS) (c : ∀ i, Z' i ⟶ Z) (a : ∀ i, Z' i ⟶ W i),
      IsFpqcCovering B S hS (fun i => (c i).hom) ∧ ∀ i, a i ≫ w i = c i ≫ p :=
  ⟨fun i => AlgebraicSpaces.fiberProduct B S hS (w i) p,
    fun i => ObjectProperty.homMk (pullback.snd (w i).hom p.hom),
    fun i => ObjectProperty.homMk (pullback.fst (w i).hom p.hom),
    isFpqcCovering_pullback B S hS w p hw,
    fun i => (AlgebraicSpaces.isPullback_fiberProduct B S hS (w i) p).w⟩

/-- Composing an fpqc covering of `Z` with fpqc coverings of its members, indexed by `I`, gives an
fpqc covering of `Z` indexed by the sigma type. -/
private theorem isFpqcCovering_sigma_comp {K : Type v} {Z : AlgebraicSpaces B S hS}
    {Z₁ : K → AlgebraicSpaces B S hS} {Z₂ : K → I → AlgebraicSpaces B S hS}
    {c₁ : ∀ k, Z₁ k ⟶ Z} {c₂ : ∀ k i, Z₂ k i ⟶ Z₁ k}
    (h₁ : IsFpqcCovering B S hS fun k => (c₁ k).hom)
    (h₂ : ∀ k, IsFpqcCovering B S hS fun i => (c₂ k i).hom) :
    IsFpqcCovering B S hS fun k : (Σ _ : K, I) => (c₂ k.1 k.2 ≫ c₁ k.1).hom :=
  isFpqcCovering_comp B S hS (Xij := fun k => (Z₂ k.1 k.2).obj) Z.property
    (fun k => (Z₁ k).property) (fun k i => (Z₂ k i).property) (fun k => (c₁ k).hom)
    (fun k i => (c₂ k i).hom) h₁ h₂

/-- **A test space with two morphisms to the target of an fpqc covering is covered, in the fpqc
topology, by spaces mapping to the members of that covering over each of them.**  The covering is
the base change along the first morphism, composed with the base change of the given covering
along the second morphism read on each member of the first; the composition clause of
Stacks 03MR makes the composite a covering. -/
theorem exists_isFpqcCovering_legPair (hw : IsFpqcCovering B S hS fun i => (w i).hom)
    {Z : AlgebraicSpaces B S hS} (p₁ p₂ : Z ⟶ R) :
    ∃ (K : Type v) (Z' : K → AlgebraicSpaces B S hS) (c : ∀ k, Z' k ⟶ Z) (ι κ : K → I)
      (a : ∀ k, Z' k ⟶ W (ι k)) (b : ∀ k, Z' k ⟶ W (κ k)),
      IsFpqcCovering B S hS (fun k => (c k).hom) ∧
        (∀ k, a k ≫ w (ι k) = c k ≫ p₁) ∧ ∀ k, b k ≫ w (κ k) = c k ≫ p₂ := by
  obtain ⟨Z₁, c₁, a₁, hcov₁, ha₁⟩ := exists_isFpqcCovering_leg B S hS W w hw p₁
  choose Z₂ c₂ b₂ hcov₂ hb₂ using fun i => exists_isFpqcCovering_leg B S hS W w hw (c₁ i ≫ p₂)
  refine ⟨Σ _ : I, I, fun k => Z₂ k.1 k.2, fun k => c₂ k.1 k.2 ≫ c₁ k.1, fun k => k.1,
    fun k => k.2, fun k => c₂ k.1 k.2 ≫ a₁ k.1, fun k => b₂ k.1 k.2, ?_, fun k => ?_,
    fun k => ?_⟩
  · exact isFpqcCovering_sigma_comp B S hS hcov₁ hcov₂
  · rw [Category.assoc, ha₁ k.1, Category.assoc]
  · rw [hb₂ k.1 k.2, Category.assoc]

/-- **A test space with three morphisms to the target of an fpqc covering is covered, in the
fpqc topology, by spaces mapping to the members of that covering over each of them.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_isFpqcCovering_legPair` followed by one more
base change, for the third morphism, and one more appeal to the composition clause of
Stacks 03MR. -/
theorem exists_isFpqcCovering_legTriple (hw : IsFpqcCovering B S hS fun i => (w i).hom)
    {Z : AlgebraicSpaces B S hS} (p₁ p₂ p₃ : Z ⟶ R) :
    ∃ (K : Type v) (Z' : K → AlgebraicSpaces B S hS) (c : ∀ k, Z' k ⟶ Z) (ι κ lam : K → I)
      (a : ∀ k, Z' k ⟶ W (ι k)) (b : ∀ k, Z' k ⟶ W (κ k)) (d : ∀ k, Z' k ⟶ W (lam k)),
      IsFpqcCovering B S hS (fun k => (c k).hom) ∧
        (∀ k, a k ≫ w (ι k) = c k ≫ p₁) ∧ (∀ k, b k ≫ w (κ k) = c k ≫ p₂) ∧
          ∀ k, d k ≫ w (lam k) = c k ≫ p₃ := by
  obtain ⟨K, Z₁, c₁, ι, κ, a₁, b₁, hcov₁, ha₁, hb₁⟩ :=
    exists_isFpqcCovering_legPair B S hS W w hw p₁ p₂
  choose Z₂ c₂ d₂ hcov₂ hd₂ using fun k => exists_isFpqcCovering_leg B S hS W w hw (c₁ k ≫ p₃)
  refine ⟨Σ _ : K, I, fun k => Z₂ k.1 k.2, fun k => c₂ k.1 k.2 ≫ c₁ k.1, fun k => ι k.1,
    fun k => κ k.1, fun k => k.2, fun k => c₂ k.1 k.2 ≫ a₁ k.1, fun k => c₂ k.1 k.2 ≫ b₁ k.1,
    fun k => d₂ k.1 k.2, ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · exact isFpqcCovering_sigma_comp B S hS hcov₁ hcov₂
  · rw [Category.assoc, ha₁ k.1, Category.assoc]
  · rw [Category.assoc, hb₁ k.1, Category.assoc]
  · rw [hd₂ k.1 k.2, Category.assoc]

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
