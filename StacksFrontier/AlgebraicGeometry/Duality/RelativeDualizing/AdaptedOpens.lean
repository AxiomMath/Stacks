module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartRefinement
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# Adapted opens of a morphism, and restriction compatibility of a comparison on them

An *adapted open* of a morphism `f : Y ⟶ X` is an affine open of the source together with an affine
open of the base it lies over. It is *good* for a chart of `f`, an affine open `V` of the source
over an affine open `U` of the base, when its source open is a principal open of `V` and its base
open is a principal open of `U`.

The adapted opens good for two (resp. three) charts form a basis of the overlap of their source
opens. For comparisons `e k i j` of the sections of two charts `i` and `j` over the adapted opens
`k` good for both, compatibility with restriction along every nesting of source opens follows from
compatibility along the nestings in which the base open shrinks as well: two principal opens of one
affine chart meet in a principal open of that chart, and the intersection of the base opens of two
nested adapted opens still lies under the smaller source open.

## Main definitions

* `Stacks.Discriminant.AdaptedOpen`: an affine open of the source together with an affine open of
  the base it lies over.
* `Stacks.Discriminant.AdaptedOpen.Good`: the adapted open is a principal refinement of a given
  chart, i.e. its source open is a principal open of the chart's source and its base open is a
  principal open of the chart's base.

## Main results

* `Stacks.Discriminant.AdaptedOpen.restrict_comparison_of_source_le`: restriction compatibility of
  a comparison along *any* nesting of source opens follows from restriction compatibility along the
  nestings that shrink the base open as well.
* `Stacks.Discriminant.AdaptedOpen.restrict_comparison_of_steps`: the same, from the two special
  cases in which only the source open and only the base open shrink.
* `Stacks.Discriminant.AdaptedOpen.exists_good_pair` and
  `Stacks.Discriminant.AdaptedOpen.exists_good_triple`: the adapted opens good for two (resp.
  three) charts form a basis of the overlap of their source opens.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u v

namespace Stacks.Discriminant

variable {X Y : Scheme.{u}}

/-- An **adapted open** of a morphism `f : Y ⟶ X`: an affine open of the source together with an
affine open of the base which it lies over. -/
public structure AdaptedOpen (f : Y ⟶ X) : Type u where
  /-- The open of the source. -/
  source : Y.affineOpens
  /-- The open of the base it lies over. -/
  base : X.affineOpens
  /-- The source open lies over the base open. -/
  source_le : source.1 ≤ f ⁻¹ᵁ base.1

namespace AdaptedOpen

variable {f : Y ⟶ X}

/-- An adapted open is **good** for a chart — an affine open `V` of the source over an affine open
`U` of the base — when its source open is a principal open of `V` and its base open is a principal
open of `U`. -/
public def Good (k : AdaptedOpen f) (V : Y.affineOpens) (U : X.affineOpens) : Prop :=
  (∃ g : Γ(Y, V.1), Y.basicOpen g = k.source.1) ∧ (∃ a : Γ(X, U.1), X.basicOpen a = k.base.1)

/-- The source open of an adapted open good for a chart lies inside that chart. -/
public theorem Good.le {k : AdaptedOpen f} {V : Y.affineOpens} {U : X.affineOpens}
    (h : k.Good V U) : k.source.1 ≤ V.1 := by
  obtain ⟨⟨g, hg⟩, -⟩ := h
  exact hg ▸ Y.basicOpen_le g

/-- Restriction of sections along the identity inclusion of an open is the identity. -/
private lemma presheaf_map_self {S : Scheme.{u}} (M : S.Modules) {W : S.Opens} (h : W ≤ W)
    (s : Γ(M, W)) : M.presheaf.map (homOfLE h).op s = s := by
  rw [show homOfLE h = 𝟙 W from Subsingleton.elim _ _]
  simp

/-- **Restriction compatibility along an arbitrary nesting of source opens follows from restriction
compatibility along the nestings that shrink the base open too.**

Let `e` compare the sections of the charts `i` and `j` over every adapted open good for both.
Suppose `e` is compatible with restriction whenever the source open *and* the base open shrink.
Then it is compatible with restriction whenever the source open shrinks, with no hypothesis on the
base opens. -/
public theorem restrict_comparison_of_source_le
    {ι : Type v} (V : ι → Y.affineOpens) (U : ι → X.affineOpens) (N : ι → Y.Modules)
    (e : ∀ (k : AdaptedOpen f) (i j : ι), k.Good (V i) (U i) → k.Good (V j) (U j) →
      Γ(N i, k.source.1) ≃ₗ[Γ(Y, k.source.1)] Γ(N j, k.source.1))
    (hres : ∀ (k l : AdaptedOpen f) (i j : ι) (hki : k.Good (V i) (U i))
      (hkj : k.Good (V j) (U j)) (hli : l.Good (V i) (U i)) (hlj : l.Good (V j) (U j))
      (hW : l.source.1 ≤ k.source.1) (_hU : l.base.1 ≤ k.base.1) (s : Γ(N i, k.source.1)),
      e l i j hli hlj ((N i).presheaf.map (homOfLE hW).op s) =
        (N j).presheaf.map (homOfLE hW).op (e k i j hki hkj s))
    (k l : AdaptedOpen f) (i j : ι) (hki : k.Good (V i) (U i)) (hkj : k.Good (V j) (U j))
    (hli : l.Good (V i) (U i)) (hlj : l.Good (V j) (U j))
    (hW : l.source.1 ≤ k.source.1) (s : Γ(N i, k.source.1)) :
    e l i j hli hlj ((N i).presheaf.map (homOfLE hW).op s) =
      (N j).presheaf.map (homOfLE hW).op (e k i j hki hkj s) := by
  obtain ⟨aki, hak⟩ := hki.2
  obtain ⟨ali, hal⟩ := hli.2
  obtain ⟨akj, hakj⟩ := hkj.2
  obtain ⟨alj, halj⟩ := hlj.2
  have hinf : X.basicOpen (aki * ali) = k.base.1 ⊓ l.base.1 := by
    rw [Scheme.basicOpen_mul, hak, hal]
  have haff : IsAffineOpen (k.base.1 ⊓ l.base.1) := hinf ▸ (U i).2.basicOpen (aki * ali)
  let q : AdaptedOpen f :=
    ⟨l.source, ⟨k.base.1 ⊓ l.base.1, haff⟩, le_inf (hW.trans k.source_le) l.source_le⟩
  have hqi : q.Good (V i) (U i) := ⟨hli.1, ⟨aki * ali, hinf⟩⟩
  have hqj : q.Good (V j) (U j) := ⟨hlj.1, ⟨akj * alj, by rw [Scheme.basicOpen_mul, hakj, halj]⟩⟩
  have h1 := hres k q i j hki hkj hqi hqj hW inf_le_left s
  have h2 := hres l q i j hli hlj hqi hqj le_rfl inf_le_right
    ((N i).presheaf.map (homOfLE hW).op s)
  simp only [presheaf_map_self] at h2
  rwa [← h2]

/-- **The two halves of the restriction hypothesis can be proved separately.** Restriction
compatibility along a nesting that shrinks the source open and the base open follows from the two
special cases: the base open fixed and the source open shrinking, and the source open fixed and the
base open shrinking. -/
public theorem restrict_comparison_of_steps
    {ι : Type v} (V : ι → Y.affineOpens) (U : ι → X.affineOpens) (N : ι → Y.Modules)
    (e : ∀ (k : AdaptedOpen f) (i j : ι), k.Good (V i) (U i) → k.Good (V j) (U j) →
      Γ(N i, k.source.1) ≃ₗ[Γ(Y, k.source.1)] Γ(N j, k.source.1))
    (hsource : ∀ (k l : AdaptedOpen f) (i j : ι) (hki : k.Good (V i) (U i))
      (hkj : k.Good (V j) (U j)) (hli : l.Good (V i) (U i)) (hlj : l.Good (V j) (U j))
      (hW : l.source.1 ≤ k.source.1) (_hU : l.base = k.base) (s : Γ(N i, k.source.1)),
      e l i j hli hlj ((N i).presheaf.map (homOfLE hW).op s) =
        (N j).presheaf.map (homOfLE hW).op (e k i j hki hkj s))
    (hbase : ∀ (k l : AdaptedOpen f) (i j : ι) (hki : k.Good (V i) (U i))
      (hkj : k.Good (V j) (U j)) (hli : l.Good (V i) (U i)) (hlj : l.Good (V j) (U j))
      (hW : l.source.1 ≤ k.source.1) (_hS : l.source = k.source)
      (_hU : l.base.1 ≤ k.base.1) (s : Γ(N i, k.source.1)),
      e l i j hli hlj ((N i).presheaf.map (homOfLE hW).op s) =
        (N j).presheaf.map (homOfLE hW).op (e k i j hki hkj s))
    (k l : AdaptedOpen f) (i j : ι) (hki : k.Good (V i) (U i)) (hkj : k.Good (V j) (U j))
    (hli : l.Good (V i) (U i)) (hlj : l.Good (V j) (U j))
    (hW : l.source.1 ≤ k.source.1) (s : Γ(N i, k.source.1)) :
    e l i j hli hlj ((N i).presheaf.map (homOfLE hW).op s) =
      (N j).presheaf.map (homOfLE hW).op (e k i j hki hkj s) := by
  refine restrict_comparison_of_source_le V U N e (fun k l i j hki hkj hli hlj hW hU s => ?_)
    k l i j hki hkj hli hlj hW s
  let p : AdaptedOpen f := ⟨l.source, k.base, hW.trans k.source_le⟩
  have hpi : p.Good (V i) (U i) := ⟨hli.1, hki.2⟩
  have hpj : p.Good (V j) (U j) := ⟨hlj.1, hkj.2⟩
  have h1 := hsource k p i j hki hkj hpi hpj hW rfl s
  have h2 := hbase p l i j hpi hpj hli hlj le_rfl rfl hU
    ((N i).presheaf.map (homOfLE hW).op s)
  simp only [presheaf_map_self] at h2
  rwa [h2]

/-- The adapted opens good for three charts form a basis of the overlap of their source opens. -/
private theorem exists_good_of_three_charts {ι : Type v} (V : ι → Y.affineOpens)
    (U : ι → X.affineOpens)
    (hVU : ∀ i, (V i).1 ≤ f ⁻¹ᵁ (U i).1) (i j m : ι) (W : Y.Opens)
    (hW : W ≤ (V i).1 ⊓ (V j).1 ⊓ (V m).1) (x : Y) (hx : x ∈ W) :
    ∃ k : AdaptedOpen f, k.Good (V i) (U i) ∧ k.Good (V j) (U j) ∧ k.Good (V m) (U m) ∧
      x ∈ k.source.1 ∧ k.source.1 ≤ W := by
  obtain ⟨a₁, a₂, a₃, ha₂, ha₃, hxa, -⟩ := exists_common_basicOpen_le₃ (U i) (U j) (U m)
    ((U i).1 ⊓ (U j).1 ⊓ (U m).1) le_rfl (f.base x)
    ⟨⟨hVU i (hW hx).1.1, hVU j (hW hx).1.2⟩, hVU m (hW hx).2⟩
  obtain ⟨g₁, g₂, g₃, hg₂, hg₃, hxg, hgle⟩ := exists_common_basicOpen_le₃ (V i) (V j) (V m)
    (W ⊓ f ⁻¹ᵁ X.basicOpen a₁) (inf_le_left.trans hW) x ⟨hx, hxa⟩
  exact ⟨⟨⟨Y.basicOpen g₁, (V i).2.basicOpen g₁⟩, ⟨X.basicOpen a₁, (U i).2.basicOpen a₁⟩,
      hgle.trans inf_le_right⟩,
    ⟨⟨g₁, rfl⟩, ⟨a₁, rfl⟩⟩, ⟨⟨g₂, hg₂.symm⟩, ⟨a₂, ha₂.symm⟩⟩,
    ⟨⟨g₃, hg₃.symm⟩, ⟨a₃, ha₃.symm⟩⟩, hxg, hgle.trans inf_le_left⟩

/-- **The adapted opens good for two charts form a basis of the overlap of their source opens.**
Given charts `(V i, U i)` and `(V j, U j)` of `f`, an open `W` inside `V i ⊓ V j` and a point of
`W`, there is an adapted open good for both charts, containing that point and inside `W`. -/
public theorem exists_good_pair {ι : Type v} (V : ι → Y.affineOpens) (U : ι → X.affineOpens)
    (hVU : ∀ i, (V i).1 ≤ f ⁻¹ᵁ (U i).1) (i j : ι) (W : Y.Opens)
    (hW : W ≤ (V i).1 ⊓ (V j).1) (x : Y) (hx : x ∈ W) :
    ∃ k : AdaptedOpen f, k.Good (V i) (U i) ∧ k.Good (V j) (U j) ∧
      x ∈ k.source.1 ∧ k.source.1 ≤ W := by
  obtain ⟨k, hi, hj, -, hx, hle⟩ := exists_good_of_three_charts V U hVU i j j W
    (hW.trans (le_inf le_rfl inf_le_right)) x hx
  exact ⟨k, hi, hj, hx, hle⟩

/-- **The adapted opens good for three charts form a basis of the overlap of their source opens.**
Given charts `(V i, U i)`, `(V j, U j)` and `(V m, U m)` of `f`, an open `W` inside
`V i ⊓ V j ⊓ V m` and a point of `W`, there is an adapted open good for the three charts,
containing that point and inside `W`. -/
public theorem exists_good_triple {ι : Type v} (V : ι → Y.affineOpens) (U : ι → X.affineOpens)
    (hVU : ∀ i, (V i).1 ≤ f ⁻¹ᵁ (U i).1) (i j m : ι) (W : Y.Opens)
    (hW : W ≤ (V i).1 ⊓ (V j).1 ⊓ (V m).1) (x : Y) (hx : x ∈ W) :
    ∃ k : AdaptedOpen f, k.Good (V i) (U i) ∧ k.Good (V j) (U j) ∧ k.Good (V m) (U m) ∧
      x ∈ k.source.1 ∧ k.source.1 ≤ W := by
  exact exists_good_of_three_charts V U hVU i j m W hW x hx

end AdaptedOpen

end Stacks.Discriminant

end
