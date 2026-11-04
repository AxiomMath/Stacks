module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.RingTheory.DimensionFormula

/-!
# The codimension between the closures of two points of an affine open

Let `X` be a scheme, let `V` be an affine open of `X` and let `x`, `z` be points of `V` with
`z ∈ closure {x}`. This file identifies the codimension of `closure {z}` inside `closure {x}`,
computed in `X`, with the height of the image of the prime of `z` in `Γ(X, V) ⧸ 𝔭_x` — that is,
with `dim 𝒪_{closure{x}, z}`. Over `Spec A` itself this is
`topCodim_closureSingleton_eq_height_map_quotientMk`; the codimension does not change when the
ambient space is enlarged along an open embedding.

## Main results

* `IrreducibleClosedsCodim.topCodim_map_isOpenEmbedding` — **an open embedding preserves the
  codimension between two irreducible closed subsets.**
* `IrreducibleClosedsCodim.topCodim_closureSingleton_map_isOpenEmbedding` — the same for the
  closures of two points.
* `AlgebraicGeometry.topCodim_closureSingleton_eq_height_primeIdealOf` — at an affine open of a
  scheme the codimension is the height of the image of the prime of `z` in `Γ(X, V) ⧸ 𝔭_x`.

## References

* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 02I2](https://stacks.math.columbia.edu/tag/02I2)
-/

@[expose] public section

open AlgebraicGeometry Topology TopologicalSpace
open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

universe u

namespace IrreducibleClosedsCodim

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- **An open embedding preserves the codimension between two irreducible closed subsets.** -/
theorem topCodim_map_isOpenEmbedding {f : A → B} (hf : IsOpenEmbedding f)
    (a b : IrreducibleCloseds A) :
    topCodim (IrreducibleCloseds.map f hf.continuous a)
        (IrreducibleCloseds.map f hf.continuous b) = topCodim a b := by
  let e := IrreducibleCloseds.map f hf.continuous
  let E := IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf
  have hle (c d : IrreducibleCloseds A) : e c ≤ e d ↔ c ≤ d := E.map_rel_iff
  have hinj : Function.Injective e := fun c d h =>
    le_antisymm ((hle c d).mp h.le) ((hle d c).mp h.ge)
  have hpreimage (w : IrreducibleCloseds B) (hw : e a ≤ w) :
      ∃ c : IrreducibleCloseds A, e c = w := by
    obtain ⟨y, hy⟩ := a.isIrreducible.nonempty
    obtain ⟨c, hc⟩ := E.surjective ⟨w, ⟨y, hw (subset_closure ⟨y, hy, rfl⟩)⟩⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hlt (c d : IrreducibleCloseds A) : e c < e d ↔ c < d := E.lt_iff_lt
  have hstrict : StrictMono e := fun c d => (hlt c d).mpr
  have hreflect : ∀ c d, e c < e d → c < d := fun c d => (hlt c d).mp
  refine le_antisymm ?_ ?_
  · rw [topCodim_le_iff]
    intro q hqh hql
    have hmem : ∀ i, ∃ c, e c = q i := fun i =>
      hpreimage _ (hqh.symm.trans_le (q.monotone (Fin.zero_le i)))
    choose c hc using hmem
    have hcm : StrictMono c := by
      intro i j hij
      refine hreflect _ _ ?_
      rw [hc i, hc j]
      exact q.strictMono hij
    have hhead : (LTSeries.mk q.length c hcm).head = a := hinj ((hc 0).trans hqh)
    have hlast : (LTSeries.mk q.length c hcm).last = b :=
      hinj ((hc (Fin.last _)).trans hql)
    simpa using length_le_topCodim a b (LTSeries.mk q.length c hcm) hhead hlast
  · rw [topCodim_le_iff]
    intro p hph hpl
    have hhead : (p.map e hstrict).head = e a := by simp [hph]
    have hlast : (p.map e hstrict).last = e b := by simp [hpl]
    simpa using length_le_topCodim (e a) (e b) (p.map e hstrict) hhead hlast

/-- The image of the closure of a point under a continuous map is the closure of its image. -/
theorem map_closureSingleton {f : A → B} (hf : Continuous f) (y : A) :
    IrreducibleCloseds.map f hf (closureSingleton y) = closureSingleton (f y) := by
  apply SetLike.ext'
  rw [IrreducibleCloseds.coe_map, coe_closureSingleton, coe_closureSingleton,
    closure_image_closure hf, Set.image_singleton]

/-- **An open embedding preserves the codimension between the closures of two points.** No
hypothesis relates the two points. -/
theorem topCodim_closureSingleton_map_isOpenEmbedding {f : A → B} (hf : IsOpenEmbedding f)
    (a b : A) :
    topCodim (closureSingleton (f a)) (closureSingleton (f b)) =
      topCodim (closureSingleton a) (closureSingleton b) := by
  rw [← map_closureSingleton hf.continuous a, ← map_closureSingleton hf.continuous b]
  exact topCodim_map_isOpenEmbedding hf _ _

end IrreducibleClosedsCodim

namespace AlgebraicGeometry

open IrreducibleClosedsCodim

/-- **The codimension of `closure {z}` inside `closure {x}`, read at an affine open.** Let `X` be
a scheme, let `V` be an affine open of `X` and let `x`, `z` be points of `V` with
`z ∈ closure {x}`. Then the codimension of `closure {z}` inside `closure {x}`, computed in `X`,
is the height of the image of the prime of `z` in `Γ(X, V) ⧸ 𝔭_x`, which is the dimension of the
local ring of the reduced closure of `{x}` at `z`. -/
theorem topCodim_closureSingleton_eq_height_primeIdealOf {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {x z : X} (hx : x ∈ V) (hz : z ∈ V)
    (hzx : z ∈ closure ({x} : Set X)) :
    topCodim (closureSingleton z) (closureSingleton x) =
      ((hV.primeIdealOf ⟨z, hz⟩).asIdeal.map
        (Ideal.Quotient.mk (hV.primeIdealOf ⟨x, hx⟩).asIdeal)).height := by
  have hfx : hV.fromSpec (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  have hfz : hV.fromSpec (hV.primeIdealOf ⟨z, hz⟩) = z := hV.fromSpec_primeIdealOf ⟨z, hz⟩
  have hemb : IsOpenEmbedding hV.fromSpec.base := hV.fromSpec.isOpenEmbedding
  have hspec : (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≤ (hV.primeIdealOf ⟨z, hz⟩).asIdeal := by
    rw [PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.le_iff_specializes]
    refine hemb.isInducing.specializes_iff.mp ?_
    rw [hfx, hfz]
    exact specializes_iff_mem_closure.mpr hzx
  refine Eq.trans ?_ (topCodim_closureSingleton_eq_height_map_quotientMk
    (hV.primeIdealOf ⟨x, hx⟩) (hV.primeIdealOf ⟨z, hz⟩) hspec)
  have key := topCodim_closureSingleton_map_isOpenEmbedding hemb
    (hV.primeIdealOf ⟨z, hz⟩) (hV.primeIdealOf ⟨x, hx⟩)
  rwa [hfx, hfz] at key

end AlgebraicGeometry

end
