module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Closures of products over a field

Over a field every scheme is universally open over the base, so taking closures commutes with
forming products: the set-theoretic product of the closures of two subsets of schemes over a
field is the closure of their set-theoretic product, and the same holds for the closures of
the images of two morphisms.

## Main results

* `AlgebraicGeometry.closure_product`: the product of the closures of two subsets is the
  closure of their product.
* `AlgebraicGeometry.closure_range_pullback_map`: the product of the closures of the images of
  two morphisms over a field is the closure of the image of their product.

## Implementation notes

The set-theoretic product of two subsets is expressed inside the underlying space of the
scheme-theoretic fibre product as the intersection of their preimages under the two
projections; no scheme structure on the subsets or on their closures is needed. The reduction
to the dense case replaces a closure by the reduced induced closed subscheme structure on it,
whose underlying map is a closed embedding with image that closure.

## References

* [Stacks Project, Tag 047B](https://stacks.math.columbia.edu/tag/047B)
* [Stacks Project, Tag 04Q0](https://stacks.math.columbia.edu/tag/04Q0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Over a field, the second projection restricted to a fibre of the first projection is an
open map: that restriction is, up to isomorphism, a base change of a morphism out of the
spectrum of a field, and such a morphism is universally open. -/
private theorem fiberSnd_isOpenMap {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (x : X) :
    IsOpenMap ((pullback.fst f g).fiberι x ≫ pullback.snd f g) := by
  let p := pullback.fst f g
  let i := X.fromSpecResidueField x
  let t : Spec (X.residueField x) ⟶ Spec (.of k) := i ≫ f
  let e : p.fiber x ≅ pullback t g :=
    (pullbackSymmetry p i) ≪≫ pullbackRightPullbackFstIso f g i
  have hcomp : (p.fiberι x ≫ pullback.snd f g) = e.hom ≫ pullback.snd t g := by
    dsimp [e, p, i, t]
    simp [Scheme.Hom.fiberι, Scheme.Hom.fiber]
  rw [hcomp]
  exact (pullback.snd t g).isOpenMap.comp e.hom.isOpenMap

/-- Over a field, the product of two dense subsets is dense in the fibre product. -/
private theorem dense_pullback_product {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (A : Set X) (B : Set Y) (hA : Dense A) (hB : Dense B) :
    Dense ((pullback.fst f g).base ⁻¹' A ∩ (pullback.snd f g).base ⁻¹' B) := by
  let p := pullback.fst f g
  let q := pullback.snd f g
  have hp : IsOpenMap p := p.isOpenMap
  refine dense_iff_closure_eq.mpr <| Set.eq_univ_iff_forall.mpr fun z =>
    mem_closure_iff.mpr fun U hU hzU => ?_
  let V := p.base '' U
  obtain ⟨a, ⟨w, hwU, hwa⟩, haA⟩ :=
    mem_closure_iff.mp (hA (p.base z)) V (hp _ hU) ⟨z, hzU, rfl⟩
  let v : p.fiber a := (p.fiberHomeo a).symm ⟨w, by simp [hwa]⟩
  have hvw : p.fiberι a v = w := p.fiberι_fiberHomeo_symm a ⟨w, by simp [hwa]⟩
  let h := p.fiberι a ≫ q
  have hh : IsOpenMap h := fiberSnd_isOpenMap f g a
  let W := (p.fiberι a).base ⁻¹' U
  let T := h.base '' W
  have hvW : v ∈ W := by change (p.fiberι a).base v ∈ U; simpa [hvw] using hwU
  obtain ⟨b, ⟨hbT, hbB⟩⟩ :=
    mem_closure_iff.mp (hB (h.base v)) T (hh W (hU.preimage (p.fiberι a).continuous)) ⟨v, hvW, rfl⟩
  obtain ⟨v', hv'W, hv'b⟩ := hbT
  refine ⟨(p.fiberι a).base v', hv'W, ?_, ?_⟩
  · show p.base ((p.fiberι a).base v') ∈ A
    rwa [show p.base ((p.fiberι a).base v') = a from (p.fiberHomeo a v').property]
  · show q.base ((p.fiberι a).base v') ∈ B
    rwa [show q.base ((p.fiberι a).base v') = b by simpa [h] using hv'b]

/-- A subset is dense in the reduced induced closed subscheme structure on its closure. -/
private theorem dense_vanishing_subscheme_preimage {X : Scheme.{u}} (A : Set X) :
    Dense ((Scheme.IdealSheafData.vanishingIdeal
      (⟨closure A, isClosed_closure⟩ : Closeds X)).subschemeι ⁻¹' A) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨closure A, isClosed_closure⟩ : Closeds X)
  let i := I.subschemeι
  have hrange : Set.range i = closure A := by
    simp [i, I, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rw [i.isClosedEmbedding.isInducing.dense_iff]
  intro x
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr (hrange.symm ▸ subset_closure),
    ← hrange]
  exact ⟨x, rfl⟩

/-- **Stacks Project, Tag 047B.** The set-theoretic fibre product of the closures of two
subsets of schemes over a field is the closure of their set-theoretic fibre product. -/
@[stacks 047B, ega "IV 2.4.11" "more general"]
theorem closure_product {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (A : Set X) (B : Set Y) :
    (pullback.fst f g).base ⁻¹' closure A ∩ (pullback.snd f g).base ⁻¹' closure B =
      closure ((pullback.fst f g).base ⁻¹' A ∩ (pullback.snd f g).base ⁻¹' B) := by
  let p := pullback.fst f g
  let q := pullback.snd f g
  let ZA : Closeds X := ⟨closure A, isClosed_closure⟩
  let ZB : Closeds Y := ⟨closure B, isClosed_closure⟩
  let IA := Scheme.IdealSheafData.vanishingIdeal ZA
  let IB := Scheme.IdealSheafData.vanishingIdeal ZB
  let iX := IA.subschemeι
  let iY := IB.subschemeι
  let A' := iX.base ⁻¹' A
  let B' := iY.base ⁻¹' B
  have hA' : Dense A' := by
    simpa [A', iX, IA, ZA] using dense_vanishing_subscheme_preimage A
  have hB' : Dense B' := by
    simpa [B', iY, IB, ZB] using dense_vanishing_subscheme_preimage B
  let f' := iX ≫ f
  let g' := iY ≫ g
  let p' := pullback.fst f' g'
  let q' := pullback.snd f' g'
  let j := pullback.map f' g' f g iX iY (𝟙 _) (by simp [f']) (by simp [g'])
  let S' := p'.base ⁻¹' A' ∩ q'.base ⁻¹' B'
  let S := p.base ⁻¹' A ∩ q.base ⁻¹' B
  let L := p.base ⁻¹' closure A ∩ q.base ⁻¹' closure B
  have hjrange : Set.range j = L := by
    calc
      Set.range j = p.base ⁻¹' Set.range iX ∩ q.base ⁻¹' Set.range iY := by
        simpa [j, p, q, f', g'] using
          (Scheme.Pullback.range_map f' g' f g iX iY (𝟙 _) (by simp [f']) (by simp [g']))
      _ = L := by
        simp [L, iX, iY, IA, IB, ZA, ZB, Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hj₁ : j ≫ p = p' ≫ iX := pullback.lift_fst _ _ _
  have hj₂ : j ≫ q = q' ≫ iY := pullback.lift_snd _ _ _
  have hpreimage : S' = j.base ⁻¹' S := by
    ext z
    simp only [S', S, A', B', Set.mem_inter_iff, Set.mem_preimage, ← Scheme.Hom.comp_apply,
      hj₁, hj₂]
  have hSL : S ⊆ L :=
    Set.inter_subset_inter (Set.preimage_mono subset_closure) (Set.preimage_mono subset_closure)
  have himage : j.base '' S' = S := by
    rw [hpreimage, Set.image_preimage_eq_inter_range, hjrange]
    exact Set.inter_eq_left.mpr hSL
  have hSdense : Dense S' := dense_pullback_product f' g' A' B' hA' hB'
  show L = closure S
  refine Set.Subset.antisymm (fun z hz => ?_) (closure_minimal hSL
    ((isClosed_closure.preimage p.continuous).inter (isClosed_closure.preimage q.continuous)))
  rw [← hjrange] at hz
  obtain ⟨w, rfl⟩ := hz
  have hw : j w ∈ closure (j '' S') := mem_closure_image j.continuous.continuousAt (hSdense w)
  simpa [himage] using hw

/-- **Stacks Project, Tag 04Q0.** For morphisms `f : A ⟶ X` and `g : B ⟶ Y` of schemes over a
field, the closure of the image of the induced morphism `A ×ₖ B ⟶ X ×ₖ Y` is the
set-theoretic fibre product of the closures of the two images. -/
@[stacks 04Q0]
theorem closure_range_pullback_map {k : Type u} [Field k] {A B X Y : Scheme.{u}}
    (pA : A ⟶ Spec (.of k)) (pB : B ⟶ Spec (.of k))
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : A ⟶ X) (g : B ⟶ Y) (hf : f ≫ pX = pA) (hg : g ≫ pY = pB) :
    (pullback.fst pX pY).base ⁻¹' closure (Set.range f.base) ∩
        (pullback.snd pX pY).base ⁻¹' closure (Set.range g.base) =
      closure (Set.range
        (pullback.map pA pB pX pY f g (𝟙 _)
          (by simpa using hf.symm) (by simpa using hg.symm)).base) := by
  rw [closure_product, ← Scheme.Pullback.range_map pA pB pX pY f g (𝟙 _)
    (by simpa using hf.symm) (by simpa using hg.symm)]

end AlgebraicGeometry
