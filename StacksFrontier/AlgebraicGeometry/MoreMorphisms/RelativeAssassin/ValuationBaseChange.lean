module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.Valuative.Specialization
public import StacksFrontier.RingTheory.Nagata.Japanese

/-!
# A valuation-ring base change through a component of a fibre

Let `f : X ⟶ S` be a morphism of schemes, `y` a point of `X`, and `Y` the reduced closed
subscheme supported on the closure of `y`. Given a point `s` of `S` and a generic point `ξ` of an
irreducible component of the fibre of `Y ⟶ S` over `s`, there is a valuation ring `A` and a
morphism `Spec A ⟶ S` sending the generic point to `f y` and the closed point to `s`, such that
after base change along it the picture is reproduced: the base-changed `Y` has a generic point of
a component of its fibre over the generic point of `Spec A` lying above `y`, the reduced closed
subscheme supported on the closure of that point is integral, and its fibre over the closed point
of `Spec A` has a generic point of a component lying above the image of `ξ`.

The valuation ring is the one witnessing the specialization `y ⤳ x`, where `x` is the image of
`ξ` in `X`; the resulting morphism `Spec A ⟶ S` lifts to a section of the base change, and the
two generic points are obtained from the generic point of the irreducible component containing
the image of that section.

## Main results

* `Stacks.RelativeAssassin.exists_valuation_base_change_generic_component`

## Implementation notes

The integral closed subscheme supported on the closure of a point is represented by the
vanishing ideal sheaf of that closure, and a point of a fibre is represented in the
scheme-theoretic fibre of the composite of its closed immersion with the structure morphism. The
base change is Mathlib's chosen pullback, and the base-changed closed subscheme is the pullback
of its ideal sheaf. The second closure is again given its canonical reduced induced structure.

## References

* [Stacks Project, Tag 0GSH](https://stacks.math.columbia.edu/tag/0GSH)
* [EGA IV, Proposition 12.1.1.5]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace Stacks.RelativeAssassin

/-- Every point of a sober space is a specialization of the generic point of an irreducible
component. -/
private lemma exists_generic_point_of_component_specializing
    {T : Type*} [TopologicalSpace T] [QuasiSober T] (z : T) :
    ∃ η : T, closure ({η} : Set T) ∈ irreducibleComponents T ∧ η ⤳ z := by
  have hC := irreducibleComponent_mem_irreducibleComponents z
  have hCirr : IsIrreducible (irreducibleComponent z) := isIrreducible_irreducibleComponent
  have hCclosed := isClosed_of_mem_irreducibleComponents _ hC
  refine ⟨hCirr.genericPoint, ?_, ?_⟩
  · rwa [hCirr.closure_genericPoint hCclosed]
  · exact (hCirr.isGenericPoint_genericPoint hCclosed).specializes mem_irreducibleComponent

/-- A generalization of a generic point of an irreducible component equals that point. -/
private lemma eq_of_component_generic_point_generalization
    {T : Type*} [TopologicalSpace T] [T0Space T] {x z : T}
    (hx : closure ({x} : Set T) ∈ irreducibleComponents T) (hzx : z ⤳ x) : z = x :=
  T0Space.t0 (hzx.antisymm (specializes_iff_closure_subset.mpr
    (hx.2 isIrreducible_singleton.closure (specializes_iff_closure_subset.mp hzx))))

private lemma apply_fiberι {X S : Scheme.{u}} (w : X ⟶ S) (s : S) (z : w.fiber s) :
    w (w.fiberι s z) = s := by
  have hmem : w.fiberι s z ∈ w ⁻¹' ({s} : Set S) := by
    rw [← Scheme.Hom.range_fiberι]
    exact ⟨z, rfl⟩
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hmem

/-- Applying both sides of `a ≫ b = c` to a point. -/
private lemma apply_comp_eq {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z}
    (h : a ≫ b = c) (z : X) : b (a z) = c z := by
  rw [← h, Scheme.Hom.comp_apply]

/-- The closed immersion of a closed subscheme sends every point into the support. -/
private lemma subschemeι_mem_support {X : Scheme.{u}} (Y : X.IdealSheafData) (z : Y.subscheme) :
    Y.subschemeι z ∈ (Y.support : Set X) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- Every point of `X` over `s` is a specialization of the image of a generic point of an
irreducible component of the fibre of `w` over `s`. -/
lemma exists_fiber_component_generic_specializes {X S : Scheme.{u}} (w : X ⟶ S) {s : S}
    (t : X) (ht : w t = s) :
    ∃ η : w.fiber s, closure ({η} : Set (w.fiber s)) ∈ irreducibleComponents (w.fiber s) ∧
      w.fiberι s η ⤳ t := by
  obtain ⟨η, hη, hspec⟩ :=
    exists_generic_point_of_component_specializing ((w.fiberHomeo s).symm ⟨t, ht⟩)
  exact ⟨η, hη, by simpa only [w.fiberι_fiberHomeo_symm] using hspec.map (w.fiberι s).continuous⟩

/-- If `m : W ⟶ V` lies over `g : S' ⟶ S` and sends a point `t` over `s'` to a generic point `ξ`
of an irreducible component of the fibre of `h : V ⟶ S` over `g s'`, then `m` sends some generic
point of an irreducible component of the fibre of `v : W ⟶ S'` over `s'` to `ξ`. -/
lemma exists_fiber_component_generic_map_eq {W V S' S : Scheme.{u}} {m : W ⟶ V} {v : W ⟶ S'}
    {h : V ⟶ S} {g : S' ⟶ S} (hcomm : m ≫ h = v ≫ g) {s' : S'} {s : S} (hs : g s' = s)
    {ξ : h.fiber s} (hξ : closure ({ξ} : Set (h.fiber s)) ∈ irreducibleComponents (h.fiber s))
    {t : W} (ht : v t = s') (htξ : m t = h.fiberι s ξ) :
    ∃ ζ : v.fiber s', closure ({ζ} : Set (v.fiber s')) ∈ irreducibleComponents (v.fiber s') ∧
      m (v.fiberι s' ζ) = h.fiberι s ξ := by
  obtain ⟨ζ, hζ, hspec⟩ := exists_fiber_component_generic_specializes v t ht
  refine ⟨ζ, hζ, ?_⟩
  have hbase : h (m (v.fiberι s' ζ)) = s := by
    simpa only [Scheme.Hom.comp_apply, apply_fiberι, hs] using
      apply_comp_eq hcomm (v.fiberι s' ζ)
  have hζ' : h.fiberι s ((h.fiberHomeo s).symm ⟨m (v.fiberι s' ζ), hbase⟩) =
      m (v.fiberι s' ζ) := h.fiberι_fiberHomeo_symm s _
  have heq : (h.fiberHomeo s).symm ⟨m (v.fiberι s' ζ), hbase⟩ = ξ := by
    refine eq_of_component_generic_point_generalization hξ
      ((h.fiberι s).isEmbedding.isInducing.specializes_iff.mp ?_)
    rw [hζ', ← htξ]
    exact hspec.map m.continuous
  rw [← hζ', heq]

/-- A point of a base-changed closed subscheme over `s'` is a specialization of a generic point
of an irreducible component of the fibre over `s'` of that closed subscheme. -/
lemma exists_fiber_component_generic_comap {X X' S' : Scheme.{u}} (Y : X.IdealSheafData)
    (p : X' ⟶ X) (q : X' ⟶ S') {x' : X'} (hx' : p x' ∈ (Y.support : Set X)) {s' : S'}
    (hs' : q x' = s') :
    ∃ η : ((Y.comap p).subschemeι ≫ q).fiber s',
      closure ({η} : Set (((Y.comap p).subschemeι ≫ q).fiber s')) ∈
        irreducibleComponents (((Y.comap p).subschemeι ≫ q).fiber s') ∧
      p ((Y.comap p).subschemeι (((Y.comap p).subschemeι ≫ q).fiberι s' η)) ∈
        (Y.support : Set X) ∧
      (Y.comap p).subschemeι (((Y.comap p).subschemeι ≫ q).fiberι s' η) ⤳ x' := by
  have hmem : ∀ w, p ((Y.comap p).subschemeι w) ∈ (Y.support : Set X) := fun w => by
    have h := subschemeι_mem_support (Y.comap p) w
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at h
    exact h
  obtain ⟨t, ht⟩ : x' ∈ Set.range (Y.comap p).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
      Closeds.coe_preimage]
    exact hx'
  obtain ⟨η, hη, hspec⟩ := exists_fiber_component_generic_specializes
    ((Y.comap p).subschemeι ≫ q) t (by rw [Scheme.Hom.comp_apply, ht, hs'])
  refine ⟨η, hη, hmem _, ?_⟩
  rw [← ht]
  exact hspec.map (Y.comap p).subschemeι.continuous

/-- Let `p, q` form a square over `f, g`, and let `y' ⤳ x'` in `X'`, where `x'` lies over `s'`
and maps to a generic point `ξ` of a component of the fibre of `Y ⟶ S` over `g s'`, and where
`p` maps the closure of `y'` into `Y`. Then the fibre over `s'` of the reduced closure of `y'`
has a generic point of a component mapping to `ξ`. -/
lemma exists_fiber_component_closure_map_eq {X S X' S' : Scheme.{u}} {f : X ⟶ S}
    {Y : X.IdealSheafData} {s : S} {ξ : (Y.subschemeι ≫ f).fiber s}
    (hξ : closure ({ξ} : Set ((Y.subschemeι ≫ f).fiber s)) ∈
      irreducibleComponents ((Y.subschemeι ≫ f).fiber s))
    {p : X' ⟶ X} {q : X' ⟶ S'} {g : S' ⟶ S} (hpq : p ≫ f = q ≫ g) {s' : S'} (hs : g s' = s)
    {y' x' : X'} (hy'x' : y' ⤳ x') (hx' : q x' = s')
    (hpx' : p x' = Y.subschemeι ((Y.subschemeι ≫ f).fiberι s ξ))
    (hY' : closure ({y'} : Set X') ⊆ p ⁻¹' (Y.support : Set X)) :
    let Y' : X'.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y'} : Set X'))
    ∃ ξ' : (Y'.subschemeι ≫ q).fiber s',
      closure ({ξ'} : Set ((Y'.subschemeι ≫ q).fiber s')) ∈
        irreducibleComponents ((Y'.subschemeι ≫ q).fiber s') ∧
      p (Y'.subschemeι ((Y'.subschemeι ≫ q).fiberι s' ξ')) =
        Y.subschemeι ((Y.subschemeι ≫ f).fiberι s ξ) := by
  intro Y'
  obtain ⟨m, hm⟩ :=
    (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support Y
      (Y'.subschemeι ≫ p)).mpr (by
        rintro _ ⟨z, rfl⟩
        have hz := subschemeι_mem_support Y' z
        rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hz
        exact hY' hz)
  have hmx : ∀ w, Y.subschemeι (m w) = p (Y'.subschemeι w) := apply_comp_eq hm
  obtain ⟨t, ht⟩ : x' ∈ Set.range Y'.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact specializes_iff_mem_closure.mp hy'x'
  have hcomm : m ≫ (Y.subschemeι ≫ f) = (Y'.subschemeι ≫ q) ≫ g := by
    simp only [Category.assoc]
    rw [reassoc_of% hm, hpq]
  obtain ⟨ζ, hζcomp, hζ⟩ := exists_fiber_component_generic_map_eq hcomm hs hξ (t := t)
    (by rw [Scheme.Hom.comp_apply, ht, hx'])
    (Y.subschemeι.isEmbedding.injective (by rw [hmx, ht, hpx']))
  exact ⟨ζ, hζcomp, by rw [← hmx, hζ]⟩

/-- A valuation-ring base change through a prescribed generic point of a component of
the fibre of the integral closure of a point. -/
@[stacks 0GSH]
theorem exists_valuation_base_change_generic_component
    {X S : Scheme.{u}} (f : X ⟶ S) (y : X)
    (Y : X.IdealSheafData)
    (hY : Y = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X)))
    (s : S) (x : X)
    (ξ : (Y.subschemeι ≫ f).fiber s)
    (hξ : closure ({ξ} : Set ((Y.subschemeι ≫ f).fiber s)) ∈
      irreducibleComponents ((Y.subschemeι ≫ f).fiber s))
    (hx : Y.subschemeι ((Y.subschemeι ≫ f).fiberι s ξ) = x) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (g : Spec (.of A) ⟶ S),
      g (genericPoint (Spec (.of A))) = f y ∧
      g (closedPoint A) = s ∧
      (let X' := (pullback f g : Scheme.{u})
       let p : X' ⟶ X := pullback.fst f g
       let q : X' ⟶ Spec (.of A) := pullback.snd f g
       let Z : X'.IdealSheafData := Y.comap p
       let j : Z.subscheme ⟶ X' := Z.subschemeι
       ∃ η : (j ≫ q).fiber (genericPoint (Spec (.of A))),
         closure ({η} : Set ((j ≫ q).fiber (genericPoint (Spec (.of A))))) ∈
           irreducibleComponents ((j ≫ q).fiber (genericPoint (Spec (.of A)))) ∧
         p (j ((j ≫ q).fiberι (genericPoint (Spec (.of A))) η)) = y ∧
         (let y' : X' := j ((j ≫ q).fiberι (genericPoint (Spec (.of A))) η)
          let Y' : X'.IdealSheafData :=
            Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y'} : Set X'))
          IsIntegral Y'.subscheme ∧
          ∃ ξ' : (Y'.subschemeι ≫ q).fiber (closedPoint A),
            closure ({ξ'} : Set ((Y'.subschemeι ≫ q).fiber (closedPoint A))) ∈
              irreducibleComponents ((Y'.subschemeι ≫ q).fiber (closedPoint A)) ∧
            p (Y'.subschemeι ((Y'.subschemeι ≫ q).fiberι (closedPoint A) ξ')) = x)) := by
  classical
  have hYc : (Y.support : Set X) = closure {y} := by
    rw [hY, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hxY : x ∈ closure {y} := by
    rw [← hYc, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨(Y.subschemeι ≫ f).fiberι s ξ, hx⟩
  let K : Type u := X.residueField y
  let : Field K := inferInstance
  obtain ⟨A, hAComm, hADomain, hAVal, F, e, hFη, hFclosed, _⟩ :=
    AlgebraicGeometry.exists_valuation_ring_of_specializes X
      (specializes_iff_mem_closure.mpr hxY) K (Iso.refl _).hom
  let : CommRing A := hAComm
  let : IsDomain A := hADomain
  let : ValuationRing A := hAVal
  let S' : Scheme := Spec (.of A)
  let ηA : S' := genericPoint S'
  let sA : S' := closedPoint A
  let g : S' ⟶ S := F ≫ f
  have hgs : g sA = s := by
    change f (F sA) = s
    rw [hFclosed, ← hx]
    exact apply_fiberι (Y.subschemeι ≫ f) s ξ
  let p : pullback f g ⟶ X := pullback.fst f g
  let q : pullback f g ⟶ S' := pullback.snd f g
  let σ : S' ⟶ pullback f g := pullback.lift F (𝟙 S') (by simp [g])
  have hpσ : ∀ z, p (σ z) = F z := apply_comp_eq (pullback.lift_fst _ _ _ : σ ≫ p = F)
  have hqσ : ∀ z, q (σ z) = z := fun z => by
    simpa using apply_comp_eq (pullback.lift_snd _ _ _ : σ ≫ q = 𝟙 S') z
  have hσY : p (σ ηA) ∈ (Y.support : Set X) := by rw [hpσ, hFη, hYc]; exact subset_closure rfl
  obtain ⟨η, hηcomp, hy'Y, hηspec⟩ := exists_fiber_component_generic_comap Y p q hσY (hqσ ηA)
  have hp'y : p ((Y.comap p).subschemeι (((Y.comap p).subschemeι ≫ q).fiberι ηA η)) = y := by
    refine T0Space.t0 (Specializes.antisymm ?_ ?_)
    · rw [← hFη, ← hpσ]
      exact hηspec.map p.continuous
    · rw [hYc] at hy'Y
      exact specializes_iff_mem_closure.mpr hy'Y
  obtain ⟨ζ, hζcomp, hζ⟩ := exists_fiber_component_closure_map_eq hξ
    (pullback.condition : p ≫ f = q ≫ g) hgs
    (hηspec.trans ((genericPoint_specializes sA).map σ.continuous)) (hqσ sA)
    (by rw [hpσ, hx]; exact hFclosed)
    (closure_minimal (Set.singleton_subset_iff.mpr hy'Y)
      (Y.support.isClosed.preimage p.continuous))
  refine ⟨A, hAComm, hADomain, hAVal, g, by change f (F ηA) = f y; rw [hFη], hgs, ?_⟩
  dsimp only
  refine ⟨η, hηcomp, hp'y, ?_, ζ, hζcomp, hζ.trans hx⟩
  refine @isIntegral_of_irreducibleSpace_of_isReduced _ ?_ ?_
  · exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  · refine Scheme.IdealSheafData.irreducibleSpace_subscheme _ _ ?_
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact isIrreducible_singleton.closure

end Stacks.RelativeAssassin

end
