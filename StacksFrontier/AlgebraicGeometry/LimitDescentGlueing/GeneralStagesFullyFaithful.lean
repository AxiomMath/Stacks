module

public import StacksFrontier.AlgebraicGeometry.LimitDescent.Faithfulness
public import StacksFrontier.AlgebraicGeometry.LimitDescentFull.Fullness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Full faithfulness over arbitrary stages: Stacks Tag 0EY1

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms, **with
no finiteness hypothesis whatsoever on the stages `Sᵢ`**.  Together with
`AlgebraicGeometry.LimitDescent.exists_model_of_locallyOfFinitePresentation` (essential
surjectivity), this file supplies the remaining half of the equivalence of categories of Stacks
Tag 0EY1 between `colim C_{Sᵢ}` and `C_S`, where `C_T` is the category of quasi-compact,
quasi-separated schemes locally of finite presentation over `T`: full faithfulness, i.e. the
colimit formula for morphism sets

`colim_j Hom_{Sⱼ}(Xᵢ ×_{Sᵢ} Sⱼ, Yᵢ ×_{Sᵢ} Sⱼ) ≅ Hom_S(Xᵢ ×_{Sᵢ} S, Yᵢ ×_{Sᵢ} S)`,

in its two halves: surjectivity of the comparison map (fullness) and injectivity (faithfulness).

## Main results

* `AlgebraicGeometry.LimitDescent.exists_morphism_after_baseChange_of_finallySmall`: fullness —
  a morphism between the base changes to `S` of two models over one arbitrary stage `Sᵢ` is
  already the base change of a morphism over some later stage.
* `AlgebraicGeometry.LimitDescent.eventually_eq_of_baseChange_eq_of_finallySmall`: faithfulness —
  two morphisms over one arbitrary stage `Sᵢ` whose base changes to `S` agree already agree after
  base change to some later stage.

## Implementation notes

Both results are
`AlgebraicGeometry.LimitDescent.exists_morphism_after_baseChange_of_small` and
`AlgebraicGeometry.LimitDescent.eventually_eq_of_baseChange_eq_of_small` with their hypothesis
`CategoryTheory.Small.{u} I` weakened to `CategoryTheory.FinallySmall.{u} I`, exactly as
`AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_finallySmall` weakens
`AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_small` for essential surjectivity: a `u`-small
cofinal subset `s` of `I` is again a nonempty directed preorder, and the inclusion of its opposite
into `Iᵒᵖ` is initial because `s` is cofinal and the order is thin.

Unlike essential surjectivity, fullness and faithfulness fix a base stage `i` in advance, so the
cofinal small subset has to be arranged to contain it: `insert i s` is still `u`-small (Mathlib's
`Small.small_insert`), still cofinal, and still directed, and now has `i` itself as a distinguished
object, so the diagram `G.op ⋙ D` restricted to it has `D.obj (.op i)` as the base change of a
member of its own index. Applying the `Small.{u}`-indexed theorem at that distinguished object and
reading its output stage `j₀` back through `G` recovers a stage of `I` above `i`.

The tag itself is registered on
`AlgebraicGeometry.LimitDescent.isEquivalence_baseChangeComparison` of
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesEquivalence`, which assembles the
two halves proved here with essential surjectivity into the equivalence of categories that the tag
asserts.

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.LimitDescent

/-- A finally `u`-small preorder has a `u`-small cofinal subset containing any given element. -/
private theorem exists_small_cofinal_set_mem {I : Type v} [Preorder I] [FinallySmall.{u} I]
    (i : I) : ∃ s : Set I, i ∈ s ∧ Small.{u} s ∧ ∀ x : I, ∃ y ∈ s, x ≤ y := by
  obtain ⟨s, hs, hsw⟩ :
      ∃ (s : Set I) (_ : Small.{u} s), ∀ x : I, ∃ y ∈ s, Nonempty (x ⟶ y) :=
    FinallySmall.exists_small_weakly_terminal_set I
  refine ⟨insert i s, Set.mem_insert i s, inferInstance, fun x => ?_⟩
  obtain ⟨y, hy, ⟨h⟩⟩ := hsw x
  exact ⟨y, Set.mem_insert_of_mem i hy, leOfHom h⟩

/-- A cofinal subset of a directed preorder is directed. -/
private theorem isDirected_of_cofinal {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    {s : Set I} (hs : ∀ x : I, ∃ y ∈ s, x ≤ y) : IsDirected {x : I // x ∈ s} (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
  obtain ⟨l, hl, hkl⟩ := hs k
  exact ⟨⟨l, hl⟩, hak.trans hkl, hbk.trans hkl⟩

/-- The inclusion of a subset of a preorder, as a functor. -/
private def subtypeInclusion {I : Type v} [Preorder I] (s : Set I) : {x : I // x ∈ s} ⥤ I where
  obj := Subtype.val
  map h := homOfLE (leOfHom h)

/-- The inclusion of a nonempty, directed, cofinal subset of a preorder is initial on
opposites. -/
private theorem initial_op_subtypeInclusion {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    {s : Set I}
    [Nonempty {x : I // x ∈ s}] [IsDirected {x : I // x ∈ s} (· ≤ ·)]
    (hs : ∀ x : I, ∃ y ∈ s, x ≤ y) : (subtypeInclusion s).op.Initial := by
  have : (subtypeInclusion s).Full := ⟨fun h => ⟨homOfLE (leOfHom h), Subsingleton.elim _ _⟩⟩
  have : (subtypeInclusion s).Faithful := ⟨fun _ => Subsingleton.elim _ _⟩
  refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun x => ?_
  obtain ⟨y, hy, hxy⟩ := hs x.unop
  exact ⟨.op ⟨y, hy⟩, ⟨(homOfLE hxy).op⟩⟩

/-- Restricting a limit cone along a small, directed, cofinal subset containing `i` gives a limit
cone over a small directed index with affine transition maps. -/
private theorem exists_small_cofinal_restriction
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [FinallySmall.{u} I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i : I) :
    ∃ (s : Set I) (_ : i ∈ s) (_ : Small.{u} s) (_ : Nonempty {x : I // x ∈ s})
      (_ : IsDirected {x : I // x ∈ s} (· ≤ ·))
      (_ : ∀ {a b : {x : I // x ∈ s}ᵒᵖ} (t : a ⟶ b),
        IsAffineHom (((subtypeInclusion s).op ⋙ D).map t)),
      Nonempty (IsLimit (c.whisker (subtypeInclusion s).op)) := by
  obtain ⟨s, hi, hs, hsle⟩ := exists_small_cofinal_set_mem.{v, u} i
  have : Nonempty {x : I // x ∈ s} := ⟨⟨i, hi⟩⟩
  have := isDirected_of_cofinal hsle
  have := initial_op_subtypeInclusion hsle
  exact ⟨s, hi, hs, inferInstance, inferInstance,
    fun t => inferInstanceAs (IsAffineHom (D.map ((subtypeInclusion s).op.map t))),
    ⟨(Functor.Initial.isLimitWhiskerEquiv _ c).symm hc⟩⟩

/-! ### Fullness -/

/-- **Fullness in Stacks Tag 0EY1, at the generality the source states it.**

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms — **no
finiteness hypothesis whatsoever is made on the stages `Sᵢ`** — let `Xᵢ`, `Yᵢ` be quasi-compact,
quasi-separated schemes locally of finite presentation over a stage `Sᵢ`, and let
`f : Xᵢ ×_{Sᵢ} S ⟶ Yᵢ ×_{Sᵢ} S` be a morphism over `S`. Then `f` is the base change of a morphism
`Xᵢ ×_{Sᵢ} Sⱼ ⟶ Yᵢ ×_{Sᵢ} Sⱼ` over some later stage `Sⱼ`, the identification of the iterated base
change with the base change to the limit being the canonical one over both factors.

This is `AlgebraicGeometry.LimitDescent.exists_morphism_after_baseChange_of_small` with the
smallness hypothesis on the index weakened to `CategoryTheory.FinallySmall.{u}`, which is what the
tag's directed *set* gives. -/
public theorem exists_morphism_after_baseChange_of_finallySmall
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [FinallySmall.{u} I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (Xᵢ Yᵢ : Over (D.obj (.op i)))
    (hXqc : CompactSpace Xᵢ.left) (hXqs : QuasiSeparatedSpace Xᵢ.left)
    (hYqc : CompactSpace Yᵢ.left) (hYqs : QuasiSeparatedSpace Yᵢ.left)
    (hX : LocallyOfFinitePresentation Xᵢ.hom)
    (hY : LocallyOfFinitePresentation Yᵢ.hom)
    (f : (Over.pullback (c.π.app (.op i))).obj Xᵢ ⟶
      (Over.pullback (c.π.app (.op i))).obj Yᵢ) :
    ∃ (j : I) (hij : i ≤ j)
      (g : (Over.pullback (D.map (homOfLE hij).op)).obj Xᵢ ⟶
        (Over.pullback (D.map (homOfLE hij).op)).obj Yᵢ)
      (α : (Over.pullback (c.π.app (.op j))).obj
          ((Over.pullback (D.map (homOfLE hij).op)).obj Xᵢ) ≅
        (Over.pullback (c.π.app (.op i))).obj Xᵢ)
      (β : (Over.pullback (c.π.app (.op j))).obj
          ((Over.pullback (D.map (homOfLE hij).op)).obj Yᵢ) ≅
        (Over.pullback (c.π.app (.op i))).obj Yᵢ),
      (α.hom.left ≫ pullback.fst Xᵢ.hom (c.π.app (.op i)) =
        pullback.fst ((Over.pullback (D.map (homOfLE hij).op)).obj Xᵢ).hom
            (c.π.app (.op j)) ≫ pullback.fst Xᵢ.hom (D.map (homOfLE hij).op)) ∧
      (β.hom.left ≫ pullback.fst Yᵢ.hom (c.π.app (.op i)) =
        pullback.fst ((Over.pullback (D.map (homOfLE hij).op)).obj Yᵢ).hom
            (c.π.app (.op j)) ≫ pullback.fst Yᵢ.hom (D.map (homOfLE hij).op)) ∧
      α.hom ≫ f = (Over.pullback (c.π.app (.op j))).map g ≫ β.hom := by
  obtain ⟨s, hi, _, _, _, _, ⟨hlim⟩⟩ := exists_small_cofinal_restriction D c hc i
  obtain ⟨j₀, hij₀, g₀, α₀, β₀, hα₀, hβ₀, heq₀⟩ :=
    exists_morphism_after_baseChange_of_small ((subtypeInclusion s).op ⋙ D)
      (c.whisker (subtypeInclusion s).op)
      hlim ⟨i, hi⟩ Xᵢ Yᵢ
      hXqc hXqs hYqc hYqs hX hY f
  exact ⟨j₀.1, hij₀, g₀, α₀, β₀, hα₀, hβ₀, heq₀⟩

/-! ### Faithfulness -/

/-- **Faithfulness in Stacks Tag 0EY1, at the generality the source states it.**

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms — **no
finiteness hypothesis whatsoever is made on the stages `Sᵢ`** — let `Xᵢ`, `Yᵢ` be quasi-compact,
quasi-separated schemes locally of finite presentation over a stage `Sᵢ`, and let
`f`, `g : Xᵢ ⟶ Yᵢ` be morphisms over `Sᵢ` whose base changes to `S` agree. Then the base changes
of `f` and `g` to some later stage `Sⱼ` already agree.

This is `AlgebraicGeometry.LimitDescent.eventually_eq_of_baseChange_eq_of_small` with the
smallness hypothesis on the index weakened to `CategoryTheory.FinallySmall.{u}`, which is what the
tag's directed *set* gives. -/
@[ega "IV 8.13.1" "special case, uniqueness"]
public theorem eventually_eq_of_baseChange_eq_of_finallySmall
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [FinallySmall.{u} I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (Xᵢ Yᵢ : Over (D.obj (.op i)))
    (hXqc : CompactSpace Xᵢ.left) (hXqs : QuasiSeparatedSpace Xᵢ.left)
    (hYqc : CompactSpace Yᵢ.left) (hYqs : QuasiSeparatedSpace Yᵢ.left)
    (hX : LocallyOfFinitePresentation Xᵢ.hom)
    (hY : LocallyOfFinitePresentation Yᵢ.hom)
    (f g : Xᵢ ⟶ Yᵢ)
    (hfg : (Over.pullback (c.π.app (.op i))).map f =
      (Over.pullback (c.π.app (.op i))).map g) :
    ∃ (j : I) (hij : i ≤ j),
      (Over.pullback (D.map (homOfLE hij).op)).map f =
        (Over.pullback (D.map (homOfLE hij).op)).map g := by
  obtain ⟨s, hi, _, _, _, _, ⟨hlim⟩⟩ := exists_small_cofinal_restriction D c hc i
  obtain ⟨j₀, hij₀, hres⟩ :=
    eventually_eq_of_baseChange_eq_of_small ((subtypeInclusion s).op ⋙ D)
      (c.whisker (subtypeInclusion s).op)
      hlim ⟨i, hi⟩ Xᵢ Yᵢ
      hXqc hXqs hYqc hYqs hX hY f g hfg
  exact ⟨j₀.1, hij₀, hres⟩

end AlgebraicGeometry.LimitDescent
