module

public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY

/-!
# Two graded ring homomorphisms that cross-commute induce the same morphism on the overlap

`Stacks.AlgebraicGeometry.ProjTwistChain.mapAwayHom_compat` compares the local morphisms attached
to two homogeneous elements for *one* graded ring homomorphism.  Gluing the partially defined
Segre projections needs the other comparison: *one* homogeneous element and *two* graded ring
homomorphisms.  This file proves it, under the only hypothesis that is available — that the two
homomorphisms commute across homogeneous elements of equal degree.

## Main definitions

* `Stacks.AlgebraicGeometry.SegreGlue.CrossComm`: the hypothesis
  `ψ a * ψ' b = ψ' a * ψ b` for `a` and `b` homogeneous of the *same* degree.

## Main results

* `Stacks.AlgebraicGeometry.SegreGlue.awayMap_comp_map_comm`: the ring-level statement.  The two
  composites `A_{(f)} → B_{(ψ f)} → B_{(ψ f · ψ' f)}` and `A_{(f)} → B_{(ψ' f)} → B_{(ψ f · ψ' f)}`
  are equal.  This is where `CrossComm` is used, and it is used exactly once: the element
  `a / f ^ n` goes to `ψ a · (ψ' f) ^ n` over the common denominator on one route and to
  `ψ' a · (ψ f) ^ n` on the other, and `a` and `f ^ n` are both homogeneous of degree `n • d`.

* `Stacks.AlgebraicGeometry.SegreGlue.homOfLE_mapAwayHom_comm`: the consequence for morphisms of
  schemes.  On any open contained in `D₊(ψ f)`, in `D₊(ψ' f)` and in `D₊(ψ f · ψ' f)` the two
  local morphisms of `Stacks.AlgebraicGeometry.ProjTwistChain.mapAwayHom` agree.

## Implementation notes

The passage from the ring statement to the scheme statement is the same manoeuvre as in
`Stacks.AlgebraicGeometry.ProjTwistChain.homOfLE_mapAwayHom`: restrict both local morphisms to
`D₊(ψ f · ψ' f)` with `AlgebraicGeometry.Proj.basicOpenToSpec_SpecMap_awayMap`, which turns the
restriction of `basicOpenToSpec` into `basicOpenToSpec` of the product followed by `Spec.map` of a
transition map of degree-zero localisations, and then contract the two `Spec.map`s into one.  After
that the two morphisms are `Spec.map` of the two composites compared in the ring lemma, followed by
the *same* open immersion `AlgebraicGeometry.Proj.awayι 𝒜 f`.

The third hypothesis of `homOfLE_mapAwayHom_comm` is redundant — `D₊(ψ f · ψ' f)` is the
intersection of the other two — but taking all three as arguments, as
`Stacks.AlgebraicGeometry.ProjTwistChain.homOfLE_mapAwayHom` does, avoids rewriting under
`Scheme.homOfLE` at the call sites, where the open is given in an unrelated form.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.SegreGlue

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The cross-commutation hypothesis.**  Two graded ring homomorphisms `ψ, ψ' : 𝒜 →+*ᵍ ℬ`
commute across any pair of homogeneous elements of `A` of the *same* degree.  Equality of degrees
is essential: for the Segre projections the two sides are both `y_j ^ e * y_k ^ e` times a common
factor, which they are only because the two polynomials have the same degree `e`. -/
public def CrossComm (ψ ψ' : 𝒜 →+*ᵍ ℬ) : Prop :=
  ∀ (e : ℕ) (a b : A), a ∈ 𝒜 e → b ∈ 𝒜 e → ψ a * ψ' b = ψ' a * ψ b

/-- **The ring-level overlap identity.**  Over the common denominator `ψ f · ψ' f` the two
transition maps out of the degree-zero localisation `A_{(f)}` agree. -/
public theorem awayMap_comp_map_comm (ψ ψ' : 𝒜 →+*ᵍ ℬ) (H : CrossComm 𝒜 ℬ ψ ψ')
    {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {x : B} (hx : x = ψ f * ψ' f) :
    (awayMap ℬ (mem_of_mem 𝒜 ℬ ψ' hf) hx).comp (Away.map ψ f) =
      (awayMap ℬ (mem_of_mem 𝒜 ℬ ψ hf) (hx.trans (mul_comm _ _))).comp (Away.map ψ' f) := by
  ext y
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf y
  have key : ψ a * ψ' f ^ n = ψ' a * ψ f ^ n := by
    rw [← map_pow, ← map_pow]
    exact H (n • d) a (f ^ n) ha (SetLike.pow_mem_graded n hf)
  simp only [RingHom.coe_comp, Function.comp_apply, Away.map_mk, awayMap_mk, Away.val_mk, key]

/-- **The overlap identity for morphisms of schemes.**  On an open lying in `D₊(ψ f)`, in
`D₊(ψ' f)` and in `D₊(ψ f · ψ' f)`, the local morphism to `AlgebraicGeometry.Proj 𝒜` attached to
`f` by `ψ` and the one attached to `f` by `ψ'` are equal. -/
public theorem homOfLE_mapAwayHom_comm (ψ ψ' : 𝒜 →+*ᵍ ℬ) (H : CrossComm 𝒜 ℬ ψ ψ')
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) {x : B} (hx : x = ψ f * ψ' f)
    {W : (AlgebraicGeometry.Proj ℬ).Opens} (hWx : W ≤ Proj.basicOpen ℬ x)
    (hWl : W ≤ Proj.basicOpen ℬ (ψ f)) (hWr : W ≤ Proj.basicOpen ℬ (ψ' f)) :
    (AlgebraicGeometry.Proj ℬ).homOfLE hWl ≫ mapAwayHom 𝒜 ℬ ψ hd hf =
      (AlgebraicGeometry.Proj ℬ).homOfLE hWr ≫ mapAwayHom 𝒜 ℬ ψ' hd hf := by
  have hxl : Proj.basicOpen ℬ x ≤ Proj.basicOpen ℬ (ψ f) :=
    Proj.basicOpen_mono ℬ (ψ f) x ⟨ψ' f, hx⟩
  have hxr : Proj.basicOpen ℬ x ≤ Proj.basicOpen ℬ (ψ' f) :=
    Proj.basicOpen_mono ℬ (ψ' f) x ⟨ψ f, hx.trans (mul_comm _ _)⟩
  have key : (AlgebraicGeometry.Proj ℬ).homOfLE hxl ≫ mapAwayHom 𝒜 ℬ ψ hd hf =
      (AlgebraicGeometry.Proj ℬ).homOfLE hxr ≫ mapAwayHom 𝒜 ℬ ψ' hd hf := by
    rw [mapAwayHom, mapAwayHom,
      ← Proj.basicOpenToSpec_SpecMap_awayMap_assoc ℬ (mem_of_mem 𝒜 ℬ ψ' hf) hx,
      ← Proj.basicOpenToSpec_SpecMap_awayMap_assoc ℬ (mem_of_mem 𝒜 ℬ ψ hf)
        (hx.trans (mul_comm _ _)),
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, awayMap_comp_map_comm 𝒜 ℬ ψ ψ' H hf hx]
  rw [← Scheme.homOfLE_homOfLE _ hWx hxl, ← Scheme.homOfLE_homOfLE _ hWx hxr, Category.assoc,
    Category.assoc, key]

end Stacks.AlgebraicGeometry.SegreGlue

end
