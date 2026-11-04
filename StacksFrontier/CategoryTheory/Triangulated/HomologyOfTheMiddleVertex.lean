module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# The homology of the middle vertex of a morphism of distinguished triangles

Let `F : C ⥤ A` be a homological functor from a pretriangulated category to an abelian category,
equipped with a shift sequence over `ℤ` so that `F.shift n` plays the role of `H^n`, and let
`φ : S ⟶ T` be a morphism of distinguished triangles of `C`. Each triangle has a long exact
sequence

`… ⟶ H^{n-1}(X₃) ⟶ H^n(X₁) ⟶ H^n(X₂) ⟶ H^n(X₃) ⟶ H^{n+1}(X₁) ⟶ …`

and `φ` induces a morphism between the two. Splicing those sequences into exact
`CategoryTheory.ComposableArrows` and applying the four and five lemmas reads off `H^n(φ₂)` from
`H^n(φ₁)`, `H^n(φ₃)` and their neighbours — the **middle** vertex, where the two existing
readings in this library, `CategoryTheory.isIso_homology_of_homotopyTriangleMorphism` and
`CategoryTheory.epi_homology_of_homotopyTriangleMorphism` of
`StacksFrontier.Homology.HomotopyCategoryFiveLemma`, read off the third.

This is the diagram chase of the last paragraph of the proof of [Stacks, Tag 0FPV]. There, `φ₁`
is the identity of a strictly perfect complex `E^•`, `φ₃` is a map
`σ_{≤ m-1}K^• ⟶ L^•` between complexes with no cohomology in degrees `≥ m` which is surjective
on `H^{m-1}`, and the conclusion wanted is that the middle map `K ⟶ M` is invertible on
cohomology in degrees `≥ m` and surjective in degree `m - 1`: that is exactly
`CategoryTheory.Functor.isIso_and_epi_homology₂_of_triangleMorphism` below.

Nothing here is a clause of a tag; it is a step of a proof, so no `@[stacks …]` attribute is
attached.

## Main results

* `CategoryTheory.Functor.isIso_homology₂_of_triangleMorphism`: the five lemma for the middle
  vertex in one degree.
* `CategoryTheory.Functor.epi_homology₂_of_triangleMorphism`: the surjectivity half, one step
  shorter.
* `CategoryTheory.Functor.isIso_and_epi_homology₂_of_triangleMorphism`: the packaged form used
  by [Stacks, Tag 0FPV] — if `φ₁` is invertible on all of `H^•`, both third vertices have no
  cohomology above `m`, and `H^m(φ₃)` is surjective, then `H^n(φ₂)` is invertible for `n > m`
  and surjective for `n = m`.

## Implementation notes

**Why the chase and not a rotation.** The statements below are the third-vertex ones read on the
twice-rotated triangles, since rotating `(X₁, X₂, X₃)` twice gives `(X₃, X₁[1], X₂[1])`. Carried
out that way, every hypothesis and the conclusion would have to be transported across
`CategoryTheory.Functor.shiftIso` — the comparison between `F.shift n` applied to a shifted
object and `F.shift (n + 1)` — in four places, which is more work than the chase and leaves the
degrees in a shape no caller writes. The rows are therefore assembled directly, exactly as the
third-vertex statements assemble theirs.

**The rows.** Exactness comes from `CategoryTheory.Functor.homologySequence_exact₁`,
`homologySequence_exact₂` and `homologySequence_exact₃`, spliced with
`CategoryTheory.ComposableArrows.exact_of_δ₀`. The commutativity conditions asked for by the
`ComposableArrows.homMk` constructors are the naturality squares of the two maps of the triangles
and of the connecting morphism; each is opened with `change`, because as `homMk` states it the
goal mentions the arrows of the `ComposableArrows` rather than the functor applications they are
made of.

**Generality.** The statements are about an arbitrary homological functor with a shift sequence,
which is what `CategoryTheory.Functor.homologySequenceδ` and the three exactness lemmas are
stated for; the derived category of an abelian category and the homotopy category of cochain
complexes are both instances, so no sheaf-theoretic or complex-level hypothesis occurs.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Type u₂} [Category.{v₂} A] [Abelian A] (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]
  {S T : Triangle C}

/-- **The five lemma for the middle vertex of a morphism of distinguished triangles.** If the map
of first vertices is invertible in degree `n₁` and monic in degree `n₂ = n₁ + 1`, and the map of
third vertices is epic in degree `n₀ = n₁ - 1` and invertible in degree `n₁`, then the map of
second vertices is invertible in degree `n₁`. -/
theorem isIso_homology₂_of_triangleMorphism
    (hS : S ∈ distTriang C) (hT : T ∈ distTriang C) (φ : S ⟶ T) (n₀ n₁ n₂ : ℤ)
    (h₀₁ : n₀ + 1 = n₁) (h₁₂ : n₁ + 1 = n₂)
    (h₃ : Epi ((F.shift n₀).map φ.hom₃))
    (h₁ : IsIso ((F.shift n₁).map φ.hom₁))
    (h₃' : IsIso ((F.shift n₁).map φ.hom₃))
    (h₁' : Mono ((F.shift n₂).map φ.hom₁)) :
    IsIso ((F.shift n₁).map φ.hom₂) := by
  let rowS : ComposableArrows A 4 := ComposableArrows.mk₄
    (F.homologySequenceδ S n₀ n₁ h₀₁) ((F.shift n₁).map S.mor₁) ((F.shift n₁).map S.mor₂)
    (F.homologySequenceδ S n₁ n₂ h₁₂)
  let rowT : ComposableArrows A 4 := ComposableArrows.mk₄
    (F.homologySequenceδ T n₀ n₁ h₀₁) ((F.shift n₁).map T.mor₁) ((F.shift n₁).map T.mor₂)
    (F.homologySequenceδ T n₁ n₂ h₁₂)
  have exS : rowS.Exact :=
    ComposableArrows.exact_of_δ₀
      (F.homologySequence_exact₁ S hS n₀ n₁ h₀₁).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (F.homologySequence_exact₂ S hS n₁).exact_toComposableArrows
        (F.homologySequence_exact₃ S hS n₁ n₂ h₁₂).exact_toComposableArrows)
  have exT : rowT.Exact :=
    ComposableArrows.exact_of_δ₀
      (F.homologySequence_exact₁ T hT n₀ n₁ h₀₁).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (F.homologySequence_exact₂ T hT n₁).exact_toComposableArrows
        (F.homologySequence_exact₃ T hT n₁ n₂ h₁₂).exact_toComposableArrows)
  let φ' : rowS ⟶ rowT := ComposableArrows.homMk₄
    ((F.shift n₀).map φ.hom₃) ((F.shift n₁).map φ.hom₁) ((F.shift n₁).map φ.hom₂)
    ((F.shift n₁).map φ.hom₃) ((F.shift n₂).map φ.hom₁)
    (by change F.homologySequenceδ S n₀ n₁ h₀₁ ≫ (F.shift n₁).map φ.hom₁ =
          (F.shift n₀).map φ.hom₃ ≫ F.homologySequenceδ T n₀ n₁ h₀₁
        exact (F.homologySequenceδ_naturality φ n₀ n₁ h₀₁).symm)
    (by change (F.shift n₁).map S.mor₁ ≫ (F.shift n₁).map φ.hom₂ =
          (F.shift n₁).map φ.hom₁ ≫ (F.shift n₁).map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by change (F.shift n₁).map S.mor₂ ≫ (F.shift n₁).map φ.hom₃ =
          (F.shift n₁).map φ.hom₂ ≫ (F.shift n₁).map T.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    (by change F.homologySequenceδ S n₁ n₂ h₁₂ ≫ (F.shift n₂).map φ.hom₁ =
          (F.shift n₁).map φ.hom₃ ≫ F.homologySequenceδ T n₁ n₂ h₁₂
        exact (F.homologySequenceδ_naturality φ n₁ n₂ h₁₂).symm)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono exS exT φ' h₃ h₁ h₃' h₁'

/-- **The surjectivity half of the five lemma for the middle vertex**, one step shorter: if the
maps of first and third vertices are epic in degree `n₁` and the map of first vertices is monic
in degree `n₂ = n₁ + 1`, then the map of second vertices is epic in degree `n₁`. -/
theorem epi_homology₂_of_triangleMorphism
    (hS : S ∈ distTriang C) (hT : T ∈ distTriang C) (φ : S ⟶ T) (n₁ n₂ : ℤ)
    (h₁₂ : n₁ + 1 = n₂)
    (h₁ : Epi ((F.shift n₁).map φ.hom₁))
    (h₃ : Epi ((F.shift n₁).map φ.hom₃))
    (h₁' : Mono ((F.shift n₂).map φ.hom₁)) :
    Epi ((F.shift n₁).map φ.hom₂) := by
  let rowS : ComposableArrows A 3 := ComposableArrows.mk₃
    ((F.shift n₁).map S.mor₁) ((F.shift n₁).map S.mor₂) (F.homologySequenceδ S n₁ n₂ h₁₂)
  let rowT : ComposableArrows A 3 := ComposableArrows.mk₃
    ((F.shift n₁).map T.mor₁) ((F.shift n₁).map T.mor₂) (F.homologySequenceδ T n₁ n₂ h₁₂)
  have exS : rowS.Exact :=
    ComposableArrows.exact_of_δ₀
      (F.homologySequence_exact₂ S hS n₁).exact_toComposableArrows
      (F.homologySequence_exact₃ S hS n₁ n₂ h₁₂).exact_toComposableArrows
  have exT : rowT.Exact :=
    ComposableArrows.exact_of_δ₀
      (F.homologySequence_exact₂ T hT n₁).exact_toComposableArrows
      (F.homologySequence_exact₃ T hT n₁ n₂ h₁₂).exact_toComposableArrows
  let φ' : rowS ⟶ rowT := ComposableArrows.homMk₃
    ((F.shift n₁).map φ.hom₁) ((F.shift n₁).map φ.hom₂) ((F.shift n₁).map φ.hom₃)
    ((F.shift n₂).map φ.hom₁)
    (by change (F.shift n₁).map S.mor₁ ≫ (F.shift n₁).map φ.hom₂ =
          (F.shift n₁).map φ.hom₁ ≫ (F.shift n₁).map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by change (F.shift n₁).map S.mor₂ ≫ (F.shift n₁).map φ.hom₃ =
          (F.shift n₁).map φ.hom₂ ≫ (F.shift n₁).map T.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    (by change F.homologySequenceδ S n₁ n₂ h₁₂ ≫ (F.shift n₂).map φ.hom₁ =
          (F.shift n₁).map φ.hom₃ ≫ F.homologySequenceδ T n₁ n₂ h₁₂
        exact (F.homologySequenceδ_naturality φ n₁ n₂ h₁₂).symm)
  exact Abelian.epi_of_epi_of_epi_of_mono φ' exS exT h₁ h₃ h₁'

/-- **The degree-`m` diagram chase of [Stacks, Tag 0FPV].** Let `φ : S ⟶ T` be a morphism of
distinguished triangles whose first component is invertible on all of `H^•`, suppose neither
third vertex has cohomology in degrees above `m`, and suppose `H^m(φ₃)` is surjective. Then
`H^n(φ₂)` is invertible for every `n > m` and surjective for `n = m`.

The two vanishing hypotheses are what turn the four hypotheses of the five lemma into the single
surjectivity in degree `m`: above `m` the map of third vertices goes between zero objects, hence
is invertible, and in every degree above `m - 1` it is epic for the same reason. -/
theorem isIso_and_epi_homology₂_of_triangleMorphism
    (hS : S ∈ distTriang C) (hT : T ∈ distTriang C) (φ : S ⟶ T) (m : ℤ)
    (h₁ : ∀ n : ℤ, IsIso ((F.shift n).map φ.hom₁))
    (hS₃ : ∀ n : ℤ, m < n → IsZero ((F.shift n).obj S.obj₃))
    (hT₃ : ∀ n : ℤ, m < n → IsZero ((F.shift n).obj T.obj₃))
    (h₃ : Epi ((F.shift m).map φ.hom₃)) :
    (∀ n : ℤ, m < n → IsIso ((F.shift n).map φ.hom₂)) ∧
      Epi ((F.shift m).map φ.hom₂) := by
  have hepi₃ : ∀ n : ℤ, m < n → Epi ((F.shift n).map φ.hom₃) := fun n hn =>
    ⟨fun _ _ _ => (hT₃ n hn).eq_of_src _ _⟩
  have hiso₃ : ∀ n : ℤ, m < n → IsIso ((F.shift n).map φ.hom₃) := fun n hn => by
    rw [(hS₃ n hn).eq_of_src ((F.shift n).map φ.hom₃) ((hS₃ n hn).iso (hT₃ n hn)).hom]
    exact ((hS₃ n hn).iso (hT₃ n hn)).isIso_hom
  refine ⟨fun n hn => ?_, ?_⟩
  · refine F.isIso_homology₂_of_triangleMorphism hS hT φ (n - 1) n (n + 1) (by omega) rfl ?_
      (h₁ n) (hiso₃ n hn) ?_
    · rcases (show m = n - 1 ∨ m < n - 1 by omega) with heq | hlt
      · exact heq ▸ h₃
      · exact hepi₃ (n - 1) hlt
    · have := h₁ (n + 1); infer_instance
  · refine F.epi_homology₂_of_triangleMorphism hS hT φ m (m + 1) rfl ?_ h₃ ?_
    · have := h₁ m; infer_instance
    · have := h₁ (m + 1); infer_instance

end CategoryTheory.Functor

end
