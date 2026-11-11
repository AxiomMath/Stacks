module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Images of filtrations by subobjects under a functor

Let `F : Fin (r + 1) → Subobject E` be a filtration `0 = E_0 ⊂ E_1 ⊂ ⋯ ⊂ E_r = E` of an object of
an abelian category, and let `G` be a functor to another abelian category which preserves zero
morphisms and cokernels. If `G` carries every inclusion `E_i ⊂ E_{i+1}` to a monomorphism, then
the images `G E_i ⊂ G E` form a filtration `0 = G E_0 ⊂ G E_1 ⊂ ⋯ ⊂ G E_r = G E` whose successive
quotients are the images `G (E_{i+1} / E_i)` of the successive quotients of `F`.

No exactness of `G` beyond the preservation of cokernels is asked for: monomorphy is demanded
only of the images of the inclusions of the filtration. This is the shape in which the inverse
image of modules along an arbitrary, not necessarily flat, morphism of algebraic spaces carries a
filtration with invertible successive quotients, the inclusions being split étale locally.

## Main results

* `CategoryTheory.Subobject.mono_map_arrow_of_filtration`: under the hypotheses above, `G` carries
  the inclusion of every member of the filtration to a monomorphism.
* `CategoryTheory.Subobject.exists_filtration_map`: the image filtration, with its successive
  quotients identified with the images of the successive quotients.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.Subobject

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) {r : ℕ} {E : C} (F : Fin (r + 1) → Subobject E) (hF : Monotone F)

/-- **The members of a filtration stay subobjects.** If a functor carries every inclusion
`E_i ⊂ E_{i+1}` of a filtration `0 = E_0 ⊂ ⋯ ⊂ E_r = E` to a monomorphism, it carries the
inclusion of every `E_i` into `E` to a monomorphism: downward from `E_r = E`, the inclusion of
`E_i` is that of `E_i ⊂ E_{i+1}` followed by that of `E_{i+1}`. -/
theorem mono_map_arrow_of_filtration (hr : F (Fin.last r) = ⊤)
    (hG : ∀ i : Fin r, Mono (G.map (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ))))
    (j : Fin (r + 1)) : Mono (G.map (F j).arrow) := by
  induction j using Fin.reverseInduction with
  | last =>
    have : IsIso (F (Fin.last r)).arrow := (isIso_arrow_iff_eq_top _).2 hr
    infer_instance
  | cast i ih =>
    have := hG i
    rw [← ofLE_arrow (hF i.castSucc_le_succ), G.map_comp]
    exact mono_comp _ _

variable [Abelian C] [Abelian D]

/-- **The image of a filtration under a functor.** Let `F` be a filtration
`0 = E_0 ⊂ E_1 ⊂ ⋯ ⊂ E_r = E` and let `G` preserve zero morphisms and cokernels and carry every
inclusion `E_i ⊂ E_{i+1}` to a monomorphism. Then `G E` has a filtration
`0 = E'_0 ⊂ E'_1 ⊂ ⋯ ⊂ E'_r = G E`, namely `E'_i = G E_i`, whose successive quotients are the
images under `G` of those of `F`. -/
theorem exists_filtration_map [G.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair G] (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (hG : ∀ i : Fin r, Mono (G.map (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)))) :
    ∃ (F' : Fin (r + 1) → Subobject (G.obj E)) (hF' : Monotone F'), F' 0 = ⊥ ∧
      F' (Fin.last r) = ⊤ ∧ ∀ i : Fin r,
        Nonempty (cokernel (ofLE (F' i.castSucc) (F' i.succ) (hF' i.castSucc_le_succ)) ≅
          G.obj (cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)))) := by
  have hm := mono_map_arrow_of_filtration G F hF hr hG
  have hle : ∀ i j : Fin (r + 1), i ≤ j → mk (G.map (F i).arrow) ≤ mk (G.map (F j).arrow) :=
    fun i j hij ↦ mk_le_mk_of_comm (G.map (ofLE _ _ (hF hij))) (by rw [← G.map_comp, ofLE_arrow])
  refine ⟨fun j ↦ mk (G.map (F j).arrow), hle, ?_, ?_, fun i ↦ ⟨?_⟩⟩
  · have h₀ : (F 0).arrow = 0 :=
      (mk_eq_bot_iff_zero (f := (F 0).arrow)).1 (by rw [mk_arrow]; exact h0)
    refine (mk_eq_bot_iff_zero (f := G.map (F 0).arrow)).2 ?_
    rw [h₀, G.map_zero]
  · have : IsIso (F (Fin.last r)).arrow := (isIso_arrow_iff_eq_top _).2 hr
    exact mk_eq_top_of_isIso _
  · refine cokernel.mapIso _ (G.map (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)))
      (underlyingIso _) (underlyingIso _) ?_ ≪≫ (PreservesCokernel.iso G _).symm
    rw [ofLE_mk_le_mk_of_comm (G.map (ofLE _ _ (hF i.castSucc_le_succ)))
      (by rw [← G.map_comp, ofLE_arrow])]
    simp

end CategoryTheory.Subobject

end
