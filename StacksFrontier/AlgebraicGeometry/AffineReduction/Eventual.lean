module

public import StacksFrontier.AlgebraicGeometry.LimitConeSmallness.Basic
public import StacksFrontier.AlgebraicGeometry.AffineReduction.Basic

/-!
# Finiteness at late stages of a limit, given eventual affineness

Let `S` be a quasi-compact quasi-separated scheme and let `X = lim_i X_i` be the limit of a system
of quasi-compact quasi-separated schemes over `S`, indexed by the opposite of a nonempty directed
preorder whose universe is independent of the scheme universe, with affine and finite transition
morphisms and with structure morphisms `X_i → S` locally of finite type. If `X → S` is integral and
the structure morphisms are affine at all sufficiently large stages (the conclusion of
[Stacks, Tag 09ZM]), then they are finite at all sufficiently large stages, as in
[Stacks, Tag 09ZN]. No smallness hypothesis on the index is needed.

## Main results

* `Stacks.Tag09ZNAffineReduction.isDirected_of_cofinal`: a cofinal subset of a nonempty directed
  preorder is directed.
* `Stacks.Tag09ZNAffineReduction.exists_isFinite_of_cofinal`: finiteness at some stage, given
  affineness of the structure morphisms along a cofinal part of the index.
* `Stacks.Tag09ZNAffineReduction.eventually_isAffineHom_of_exists`: affineness of the structure
  morphisms at every stage beyond a fixed one is eventual affineness along the preorder.
* `AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_eventually_isAffineHom`:
  **the structure morphisms are eventually finite, given that they are eventually affine.**
* `AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_card09ZM`: the same, with
  the hypothesis in the shape of the conclusion of [Stacks, Tag 09ZM], whose premise
  `IsAffineHom f` is discharged from `IsIntegralHom f`.

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
* [The Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
-/


@[expose] public section

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.LimitConeSmallness (subsetInclusion initial_op_subsetInclusion)

namespace Stacks.Tag09ZNAffineReduction

/-- A cofinal subset of a nonempty directed preorder is itself nonempty and directed. -/
theorem isDirected_of_cofinal {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (J : Set I) (hcof : ∀ i : I, ∃ j ∈ J, i ≤ j) : IsDirected ↥J (· ≤ ·) :=
  ⟨fun a b ↦ by
    obtain ⟨k, hak, hbk⟩ := exists_ge_ge (a : I) (b : I)
    obtain ⟨j, hjJ, hkj⟩ := hcof k
    exact ⟨⟨j, hjJ⟩, hak.trans hkj, hbk.trans hkj⟩⟩

/-- **The structure morphism at a late stage is finite, given that it is affine at every stage of
a cofinal part of the index.** -/
theorem exists_isFinite_of_cofinal {I : Type w} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {S : Scheme.{u}} [CompactSpace S]
    (F : Iᵒᵖ ⥤ Scheme.{u}) (q : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone F) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : ∀ i : I, f = c.π.app (op i) ≫ q.app (op i)) (hfint : IsIntegralHom f)
    (hfinite : ∀ (i j : I) (h : i ≤ j), IsFinite (F.map (homOfLE h).op))
    (hlft : ∀ i : I, LocallyOfFiniteType (q.app (op i)))
    (J : Set I) (hcof : ∀ i : I, ∃ j ∈ J, i ≤ j)
    (hJaff : ∀ j : I, j ∈ J → IsAffineHom (q.app (op j))) (j₀ : I) (hj₀ : j₀ ∈ J) :
    ∃ j : I, IsFinite (q.app (op j)) := by
  have hne : Nonempty ↥J := ⟨⟨j₀, hj₀⟩⟩
  have hdir : IsDirected ↥J (· ≤ ·) := isDirected_of_cofinal J hcof
  have hinit : ((subsetInclusion J).op).Initial := initial_op_subsetInclusion J hcof
  have hcJ : IsLimit (c.whisker (subsetInclusion J).op) :=
    (Functor.Initial.isLimitWhiskerEquiv _ c).symm hc
  have hp : IsStructureFamily ((subsetInclusion J).op ⋙ F)
      (fun a : ↥J ↦ q.app (op (a : I))) := by
    intro a b h
    have hnat := q.naturality (homOfLE (show (a : I) ≤ (b : I) from h)).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hnat
    exact hnat.symm
  obtain ⟨b, -, hb⟩ := exists_isFinite hp (c := c.whisker (subsetInclusion J).op) (f := f)
    (fun a ↦ hJaff (a : I) a.2) hcJ (fun a ↦ hf (a : I)) hfint
    (fun a b h ↦ hfinite (a : I) (b : I) h) (fun a ↦ hlft (a : I)) ⟨j₀, hj₀⟩
  exact ⟨(b : I), hb⟩

/-- If the structure morphisms are affine at every stage `j` admitting a morphism `j ⟶ i` in `Iᵒᵖ`,
for some stage `i`, then they are affine at all sufficiently large stages of `I`. -/
theorem eventually_isAffineHom_of_exists {I : Type w} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {S : Scheme.{u}} (F : Iᵒᵖ ⥤ Scheme.{u})
    (q : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (h : ∃ i : Iᵒᵖ, ∀ {j : Iᵒᵖ} (_ : j ⟶ i), IsAffineHom (q.app j)) :
    ∀ᶠ i in Filter.atTop, IsAffineHom (q.app (op i)) := by
  obtain ⟨i, hi⟩ := h
  rw [Filter.eventually_atTop]
  exact ⟨i.unop, fun j hj ↦ hi (homOfLE hj).op⟩

end Stacks.Tag09ZNAffineReduction

namespace AlgebraicGeometry

open Stacks.Tag09ZNAffineReduction in
/-- **Finiteness at late stages, given eventual affineness** ([Stacks, Tag 09ZN] with the
conclusion of [Stacks, Tag 09ZM] as a hypothesis). Let `c` be a limit cone over a system `F` of
quasi-compact quasi-separated schemes over a quasi-compact quasi-separated scheme `S`, indexed by
the opposite of a nonempty directed preorder `I`, with affine and finite transition morphisms and
structure morphisms `q_i` locally of finite type, and let `f : c.pt ⟶ S` be integral and
compatible with the `q_i`. If the `q_i` are affine for all sufficiently large `i`, then they are
finite for all sufficiently large `i`. -/
theorem eventually_isFinite_of_isLimit_of_isIntegral_of_eventually_isAffineHom
    {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : Iᵒᵖ ⥤ Scheme.{u}) (q : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone F) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : ∀ i, f = c.π.app (op i) ≫ q.app (op i))
    [IsIntegralHom f]
    [∀ i, CompactSpace (F.obj (op i))]
    [∀ i, QuasiSeparatedSpace (F.obj (op i))]
    (_haffine : ∀ {i j : I} (h : i ≤ j), IsAffineHom (F.map (homOfLE h).op))
    (hfinite : ∀ {i j : I} (h : i ≤ j), IsFinite (F.map (homOfLE h).op))
    [∀ i, LocallyOfFiniteType (q.app (op i))]
    (heventuallyAffine : ∀ᶠ i in Filter.atTop, IsAffineHom (q.app (op i))) :
    ∀ᶠ i in Filter.atTop, IsFinite (q.app (op i)) := by
  rw [Filter.eventually_atTop] at heventuallyAffine ⊢
  obtain ⟨i₀, hi₀⟩ := heventuallyAffine
  obtain ⟨k, hk⟩ := exists_isFinite_of_cofinal F q c hc f hf inferInstance
    (fun _ _ h ↦ hfinite h) (fun _ ↦ inferInstance) {j : I | i₀ ≤ j}
    (fun i ↦ by obtain ⟨j, hij, hi₀j⟩ := exists_ge_ge i i₀; exact ⟨j, hi₀j, hij⟩)
    (fun j hj ↦ hi₀ j hj) i₀ le_rfl
  refine ⟨k, fun j hj ↦ ?_⟩
  have h1 := hfinite hj
  have h2 := hk
  have hnat : F.map (homOfLE hj).op ≫ q.app (op k) = q.app (op j) := by
    simp
  rw [← hnat]
  infer_instance

open Stacks.Tag09ZNAffineReduction in
/-- **Finiteness at late stages from the conclusion of [Stacks, Tag 09ZM].** Under the hypotheses
of `AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_eventually_isAffineHom`
without eventual affineness, if `IsAffineHom f` implies that the structure morphisms are affine at
every stage `j` admitting a morphism `j ⟶ i` in `Iᵒᵖ`, for some stage `i`, then the structure
morphisms are finite at all sufficiently large stages. -/
theorem eventually_isFinite_of_isLimit_of_isIntegral_of_card09ZM
    {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : Iᵒᵖ ⥤ Scheme.{u}) (q : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone F) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : ∀ i, f = c.π.app (op i) ≫ q.app (op i))
    [IsIntegralHom f]
    [∀ i, CompactSpace (F.obj (op i))]
    [∀ i, QuasiSeparatedSpace (F.obj (op i))]
    (haffine : ∀ {i j : I} (h : i ≤ j), IsAffineHom (F.map (homOfLE h).op))
    (hfinite : ∀ {i j : I} (h : i ≤ j), IsFinite (F.map (homOfLE h).op))
    [∀ i, LocallyOfFiniteType (q.app (op i))]
    (h09ZM : IsAffineHom f → ∃ i : Iᵒᵖ, ∀ {j : Iᵒᵖ} (_ : j ⟶ i), IsAffineHom (q.app j)) :
    ∀ᶠ i in Filter.atTop, IsFinite (q.app (op i)) :=
  eventually_isFinite_of_isLimit_of_isIntegral_of_eventually_isAffineHom F q c hc f hf
    (fun h ↦ haffine h) (fun h ↦ hfinite h)
    (eventually_isAffineHom_of_exists F q (h09ZM inferInstance))

end AlgebraicGeometry

end

end
