module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Slices
public import StacksCore.Tactic.StacksAttribute

/-!
# The small and affine pro-étale sites

Let `B` be a big pro-étale site containing a scheme `S`. The induced
covering families on the small pro-étale category and the standard
covering families on the affine pro-étale category satisfy the site axioms.

## Main results

* `AlgebraicGeometry.ProEtale.SmallProetale.isSite` asserts the site axioms for the small
  pro-étale category of `S` in `B`.
* `AlgebraicGeometry.ProEtale.BigAffineProetale.isSite` asserts the site axioms for the affine
  pro-étale category over `S` in `B`.

## Implementation notes

The two sites are stated separately using the family-valued covering
predicates `AlgebraicGeometry.ProEtale.SmallProetale.IsCovering` and
`AlgebraicGeometry.ProEtale.BigAffineProetale.IsCovering`. `CategoryTheory.IsSite` retains the
isomorphism, composition, and base-change axioms for those families, rather than merely
asserting that their generated Grothendieck topologies exist.

## References

* [Stacks Project, Tag 098L](https://stacks.math.columbia.edu/tag/098L)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

/-- Two morphisms into the underlying objects of a cospan in a slice category over `T`, agreeing
after composition with the cospan, agree after composition with the structure morphisms. -/
private lemma comp_hom_eq_of_comp_left_eq {C : Type*} [Category C] {T : C} {X Y Z : Over T}
    (f : X ⟶ Z) (g : Y ⟶ Z) {P : C} (p₁ : P ⟶ X.left) (p₂ : P ⟶ Y.left)
    (h : p₁ ≫ f.left = p₂ ≫ g.left) : p₁ ≫ X.hom = p₂ ≫ Y.hom :=
  calc
    p₁ ≫ X.hom = (p₁ ≫ f.left) ≫ Z.hom := by simp only [Category.assoc, f.w]
    _ = (p₂ ≫ g.left) ≫ Z.hom := by rw [h]
    _ = p₂ ≫ Y.hom := by simp only [Category.assoc, g.w]

namespace SmallProetale

/-- The covering families on the small pro-étale category of `S` form a site. -/
@[stacks 098L "small pro-étale site"]
lemma isSite (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : IsSite (SmallProetale.IsCovering B S hS) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    exact B.covering_isSite.1
      ((SmallProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS).map f)
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    simpa [SmallProetale.IsCovering, BigProetaleOver.IsCovering,
      PreZeroHypercover.map, PreZeroHypercover.bind, PreZeroHypercover.pushforward] using
      B.covering_isSite.2.1 _ h𝒰 _ h𝒱 (fun i => congrArg
        (SmallProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS).obj (h i))
  · intro 𝒰 h𝒰 V g
    let K := SmallProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS
    let E : Covering B.Scheme := ⟨K.obj 𝒰.1, 𝒰.2.map K⟩
    obtain ⟨P, p₁, p₂, hpb, hcov⟩ := B.covering_isSite.2.2 E h𝒰 (K.obj V) (K.map g)
    dsimp [E, PreZeroHypercover.map] at P p₁ p₂ hpb hcov
    have hWeak (i : 𝒰.2.I₀) : WeaklyEtale (B.inclusion.map (p₂ i)) :=
      (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _
        ((B.isProetaleCovering_iff ⟨K.obj V, ⟨𝒰.2.I₀, P, p₂⟩⟩).mp hcov.1))
        ((PreZeroHypercover.map B.inclusion
          (⟨K.obj V, ⟨𝒰.2.I₀, P, p₂⟩⟩ : Covering B.Scheme).2).presieve₀_f i)
    let Q (i : 𝒰.2.I₀) : SmallProetale B S hS :=
      ⟨Over.mk (p₂ i ≫ V.obj.hom), by
        change WeaklyEtale (B.inclusion.map (p₂ i ≫ V.obj.hom))
        rw [Functor.map_comp]
        have := hWeak i
        infer_instance⟩
    let q₁ (i : 𝒰.2.I₀) : Q i ⟶ 𝒰.2.X i :=
      ObjectProperty.homMk (Over.homMk (p₁ i)
        (comp_hom_eq_of_comp_left_eq (𝒰.2.f i).hom g.hom (p₁ i) (p₂ i) (hpb i).w))
    let q₂ (i : 𝒰.2.I₀) : Q i ⟶ V :=
      ObjectProperty.homMk (Over.homMk (p₂ i) rfl)
    refine ⟨Q, q₁, q₂, ?_, ?_⟩
    · intro i
      apply IsPullback.of_map_of_faithful K
      simpa [K, SmallProetale.inclusion, BigProetaleOver.forget, q₁, q₂, Q] using hpb i
    · simpa [SmallProetale.IsCovering, BigProetaleOver.IsCovering,
        PreZeroHypercover.map, K, Q, q₂] using hcov

end SmallProetale

namespace BigAffineProetale

/-- The standard covering families on affine pro-étale objects over `S` form a site. -/
@[stacks 098L "affine pro-étale site"]
lemma isSite (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : IsSite (BigAffineProetale.IsCovering B S hS) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    let K := BigAffineProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS
    change B.covering _ ∧ Finite PUnit
    exact ⟨B.covering_isSite.1 (K.map f), inferInstance⟩
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    let K := BigAffineProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS
    change B.covering _ ∧ Finite _ at h𝒰 ⊢
    have hcomp := B.covering_isSite.2.1 ⟨K.obj 𝒰.1, 𝒰.2.map K⟩ h𝒰.1
      (fun i => ⟨K.obj (𝒱 i).1, (𝒱 i).2.map K⟩) (fun i => (h𝒱 i).1)
      (fun i => congrArg K.obj (h i))
    refine ⟨by simpa [BigAffineProetale.IsCovering, BigProetaleOver.IsCovering,
        K, PreZeroHypercover.map, PreZeroHypercover.bind,
        PreZeroHypercover.pushforward] using hcomp, ?_⟩
    have : Finite 𝒰.2.I₀ := h𝒰.2
    have : ∀ i, Finite (𝒱 i).2.I₀ := fun i => (h𝒱 i).2
    change Finite (Σ i : 𝒰.2.I₀, (𝒱 i).2.I₀)
    infer_instance
  · intro 𝒰 h𝒰 V g
    let K := BigAffineProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS
    change B.covering _ ∧ Finite _ at h𝒰
    obtain ⟨P, p₁, p₂, hpb, hcov⟩ :=
      B.covering_isSite.2.2 ⟨K.obj 𝒰.1, 𝒰.2.map K⟩ h𝒰.1 (K.obj V) (K.map g)
    dsimp [PreZeroHypercover.map] at P p₁ p₂ hpb hcov
    have hPaff (i : 𝒰.2.I₀) : IsAffine (B.inclusion.obj (P i)) := by
      have : IsAffine (B.inclusion.obj (K.obj (𝒰.2.X i))) :=
        BigAffineProetale.isAffine_toScheme_obj B S hS (𝒰.2.X i)
      have : IsAffine (B.inclusion.obj (K.obj V)) :=
        BigAffineProetale.isAffine_toScheme_obj B S hS V
      have : IsAffine (B.inclusion.obj (K.obj 𝒰.1)) :=
        BigAffineProetale.isAffine_toScheme_obj B S hS 𝒰.1
      exact IsAffine.of_isPullback ((hpb i).map B.inclusion)
    let Q (i : 𝒰.2.I₀) : BigAffineProetale B S hS :=
      ⟨Over.mk (p₂ i ≫ V.obj.hom), hPaff i⟩
    let q₁ (i : 𝒰.2.I₀) : Q i ⟶ 𝒰.2.X i :=
      ObjectProperty.homMk (Over.homMk (p₁ i)
        (comp_hom_eq_of_comp_left_eq (𝒰.2.f i).hom g.hom (p₁ i) (p₂ i) (hpb i).w))
    let q₂ (i : 𝒰.2.I₀) : Q i ⟶ V :=
      ObjectProperty.homMk (Over.homMk (p₂ i) rfl)
    refine ⟨Q, q₁, q₂, ?_, ?_⟩
    · intro i
      apply IsPullback.of_map_of_faithful K
      simpa [K, BigAffineProetale.inclusion,
        BigProetaleOver.forget, q₁, q₂, Q] using hpb i
    · change B.covering _ ∧ Finite _
      refine ⟨?_, h𝒰.2⟩
      simpa [BigAffineProetale.IsCovering,
        BigProetaleOver.IsCovering, K, Q, q₂,
        PreZeroHypercover.map] using hcov

end BigAffineProetale

end AlgebraicGeometry.ProEtale
