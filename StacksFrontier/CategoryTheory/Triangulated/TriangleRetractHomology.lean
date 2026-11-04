module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A distinguished triangle which retracts onto another

Let `C` be a pre-triangulated category. This file records the two pieces of triangle
bookkeeping that the source's proof of the first assertion of Stacks 0FPV performs on the
triangle `ℰ ⟶ M ⟶ ℒ ⟶ ℰ[1]` after the retraction `M ⟶ K ⟶ M` has been produced.

* **The dotted arrow.** TR3 says that a commutative square between the first two vertices of
  two distinguished triangles extends to the third vertex; `exists_triangleMorphism` packages
  that as a morphism in `Triangle C`, which is the form in which two such extensions can be
  composed.

* **The retraction of the third vertices.** If `a : T ⟶ T'` and `b : T' ⟶ T` compose to a
  morphism which is invertible on the first two vertices of a distinguished triangle, then
  `b.hom₃` is a *split epimorphism* — the composite `a.hom₃ ≫ b.hom₃` is an isomorphism, by
  Mathlib's triangulated five lemma. This is the step of the source's proof where the two
  stacked morphisms of triangles give `σ_{≤ m - 1}𝒦 ⟶ ℒ` a section.

* **The diagram chase that follows it.** "Using the induced map of long exact sequences of
  cohomology sheaves from the morphism of triangles above, a diagram chase shows this implies
  `H^i(K) ⟶ H^i(M)` is an isomorphism for `i ≥ m` and surjective for `i = m - 1`." That is the
  four and five lemmas applied to the two long exact sequences of a homological functor, in the
  slot of the *second* vertex, together with the vanishing of the third vertices above `m - 1`.

## Main results

* `CategoryTheory.Pretriangulated.exists_triangleMorphism`: TR3 as a morphism of triangles.
* `CategoryTheory.Pretriangulated.isIso_hom₃_of_isIso_hom₁₂_self`: a self-morphism of a
  distinguished triangle which is invertible on the first two vertices is invertible on the
  third.
* `CategoryTheory.Pretriangulated.isSplitEpi_hom₃_of_comp`: the second of two composable
  morphisms of triangles whose composite is invertible on the first two vertices is a split
  epimorphism on the third. Only the outer triangle has to be distinguished.
* `CategoryTheory.Functor.epi_shift_map_hom₂` and
  `CategoryTheory.Functor.isIso_shift_map_hom₂`: the four and five lemmas for the two long exact
  cohomology sequences of a morphism of distinguished triangles, in the **second** slot — the
  middle vertex read off the outer two.
* `CategoryTheory.Functor.isIso_shift_map_hom₂_of_isZero_obj₃`: the source's diagram chase. If
  the first components are invertible on cohomology in every degree, the third vertices have no
  cohomology in the degrees `≥ m`, and the third component is epic on cohomology in degree
  `m - 1`, then the second component is invertible on cohomology in the degrees `≥ m` and epic
  in degree `m - 1`.

## Implementation notes

The source argues on cohomology: it reads the two stacked morphisms of triangles through
`H^{m-1}`, observes that the outer columns compose to the identity, and concludes that the
middle vertical composite `H^{m-1}(ℒ) ⟶ H^{m-1}(σ_{≤ m-1}𝒦) ⟶ H^{m-1}(ℒ)` is *surjective*.
That is weaker than what is available. The composite of the two morphisms of triangles is a
self-morphism of a distinguished triangle which is the identity on the first two vertices, so
`CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂` — the triangulated five lemma, Stacks 014A —
makes its third component an **isomorphism** already in `C`, with no homological functor and no
exact sequence. The conclusion recorded here is therefore `IsSplitEpi b.hom₃` in `C`; applying
any functor to a split epimorphism gives a split epimorphism, so the source's surjectivity
statement in degree `m - 1` is the image of this one under `H^{m-1}` and needs no separate
argument.

Nothing here is a clause of a tag: Stacks 014A is already registered on Mathlib's
`isIso₃_of_isIso₁₂`, and TR3 is a field of `CategoryTheory.Pretriangulated`. These are the two
repackagings the triangle bookkeeping of Stacks 0FPV consumes.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public noncomputable section

universe v u v' u'

namespace CategoryTheory.Pretriangulated

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- **TR3 as a morphism of triangles.** A commutative square between the first two vertices of
two distinguished triangles extends to a morphism in `Triangle C` whose first two components
are the given ones. The third component — the source's dotted arrow — is not determined by the
square, which is why this is an existence statement. -/
theorem exists_triangleMorphism (T₁ T₂ : Triangle C) (hT₁ : T₁ ∈ distTriang C)
    (hT₂ : T₂ ∈ distTriang C) (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ φ : T₁ ⟶ T₂, φ.hom₁ = a ∧ φ.hom₂ = b := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism _ _ hT₁ hT₂ a b comm
  exact ⟨Triangle.homMk _ _ a b c comm hc₂ hc₃, rfl, rfl⟩

/-- **The third vertex of a distinguished triangle retracts along a pair of morphisms of
triangles whose composite is invertible on the first two vertices.**

Let `T` be a distinguished triangle, `a : T ⟶ T'` and `b : T' ⟶ T` morphisms of triangles whose
composite is an isomorphism on `T.obj₁` and on `T.obj₂`. Then `b.hom₃ : T'.obj₃ ⟶ T.obj₃` is a
split epimorphism.

This is the conclusion the proof of the first assertion of Stacks 0FPV draws from its two
stacked morphisms of triangles: the composite `M ⟶ K ⟶ M` of the retraction is the identity,
`ℰ ⟶ ℰ` is the identity, so `σ_{≤ m - 1}𝒦 ⟶ ℒ` has a section. Two hypotheses the source's
diagram has are not used: the composite need only be *invertible* on the first two vertices
rather than the identity, and `T'` — the middle row of that diagram — need not be
distinguished, since the five lemma is applied to the self-morphism `a ≫ b` of `T`. -/
theorem isSplitEpi_hom₃_of_comp {T T' : Triangle C} (hT : T ∈ distTriang C)
    (a : T ⟶ T') (b : T' ⟶ T) [IsIso (a ≫ b).hom₁]
    [IsIso (a ≫ b).hom₂] : IsSplitEpi b.hom₃ := by
  have h : IsIso (a.hom₃ ≫ b.hom₃) := by
    have := isIso₃_of_isIso₁₂ (a ≫ b) hT hT inferInstance inferInstance
    exact (show (a ≫ b).hom₃ = a.hom₃ ≫ b.hom₃ from rfl) ▸ this
  exact IsSplitEpi.mk' ⟨inv (a.hom₃ ≫ b.hom₃) ≫ a.hom₃, by
    rw [Category.assoc]
    exact IsIso.inv_hom_id (a.hom₃ ≫ b.hom₃)⟩

end CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

open Limits Pretriangulated ComposableArrows

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  [Abelian A] (H : C ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
  {T T' : Triangle C} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (φ : T ⟶ T')

include hT hT'

/-- **The four lemma in the second slot.** For a morphism `φ` of distinguished triangles and a
homological functor `H`: if `H^{n₀}(φ.hom₁)` and `H^{n₀}(φ.hom₃)` are epic and `H^{n₁}(φ.hom₁)`
is monic, then `H^{n₀}(φ.hom₂)` is epic.

The rows are the four-term stretches
`H^{n₀}(obj₁) ⟶ H^{n₀}(obj₂) ⟶ H^{n₀}(obj₃) ⟶ H^{n₁}(obj₁)` of the two long exact sequences; the
third square is the naturality of the connecting morphism. -/
theorem epi_shift_map_hom₂ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (h₁ : Epi ((H.shift n₀).map φ.hom₁)) (h₃ : Epi ((H.shift n₀).map φ.hom₃))
    (h₁' : Mono ((H.shift n₁).map φ.hom₁)) :
    Epi ((H.shift n₀).map φ.hom₂) := by
  let rowT : ComposableArrows A 3 := mk₃
    ((H.shift n₀).map T.mor₁) ((H.shift n₀).map T.mor₂) (H.homologySequenceδ T n₀ n₁ h)
  let rowT' : ComposableArrows A 3 := mk₃
    ((H.shift n₀).map T'.mor₁) ((H.shift n₀).map T'.mor₂) (H.homologySequenceδ T' n₀ n₁ h)
  have exT : rowT.Exact :=
    exact_of_δ₀ (H.homologySequence_exact₂ T hT n₀).exact_toComposableArrows
      (H.homologySequence_exact₃ T hT n₀ n₁ h).exact_toComposableArrows
  have exT' : rowT'.Exact :=
    exact_of_δ₀ (H.homologySequence_exact₂ T' hT' n₀).exact_toComposableArrows
      (H.homologySequence_exact₃ T' hT' n₀ n₁ h).exact_toComposableArrows
  let ψ : rowT ⟶ rowT' := homMk₃
    ((H.shift n₀).map φ.hom₁) ((H.shift n₀).map φ.hom₂) ((H.shift n₀).map φ.hom₃)
    ((H.shift n₁).map φ.hom₁)
    (by change (H.shift n₀).map T.mor₁ ≫ (H.shift n₀).map φ.hom₂ =
          (H.shift n₀).map φ.hom₁ ≫ (H.shift n₀).map T'.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by change (H.shift n₀).map T.mor₂ ≫ (H.shift n₀).map φ.hom₃ =
          (H.shift n₀).map φ.hom₂ ≫ (H.shift n₀).map T'.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    (by change H.homologySequenceδ T n₀ n₁ h ≫ (H.shift n₁).map φ.hom₁ =
          (H.shift n₀).map φ.hom₃ ≫ H.homologySequenceδ T' n₀ n₁ h
        exact (H.homologySequenceδ_naturality φ n₀ n₁ h).symm)
  exact Abelian.epi_of_epi_of_epi_of_mono ψ exT exT' h₁ h₃ h₁'

/-- **The five lemma in the second slot.** For a morphism `φ` of distinguished triangles and a
homological functor `H`: if `H^{n'}(φ.hom₃)` is epic, `H^{n₀}(φ.hom₁)` and `H^{n₀}(φ.hom₃)` are
invertible and `H^{n₁}(φ.hom₁)` is monic, then `H^{n₀}(φ.hom₂)` is invertible.

The rows are the five-term stretches
`H^{n'}(obj₃) ⟶ H^{n₀}(obj₁) ⟶ H^{n₀}(obj₂) ⟶ H^{n₀}(obj₃) ⟶ H^{n₁}(obj₁)`. -/
theorem isIso_shift_map_hom₂ (n' n₀ n₁ : ℤ) (h' : n' + 1 = n₀) (h : n₀ + 1 = n₁)
    (h₃' : Epi ((H.shift n').map φ.hom₃)) (h₁ : IsIso ((H.shift n₀).map φ.hom₁))
    (h₃ : IsIso ((H.shift n₀).map φ.hom₃)) (h₁' : Mono ((H.shift n₁).map φ.hom₁)) :
    IsIso ((H.shift n₀).map φ.hom₂) := by
  let rowT : ComposableArrows A 4 := mk₄
    (H.homologySequenceδ T n' n₀ h') ((H.shift n₀).map T.mor₁) ((H.shift n₀).map T.mor₂)
    (H.homologySequenceδ T n₀ n₁ h)
  let rowT' : ComposableArrows A 4 := mk₄
    (H.homologySequenceδ T' n' n₀ h') ((H.shift n₀).map T'.mor₁) ((H.shift n₀).map T'.mor₂)
    (H.homologySequenceδ T' n₀ n₁ h)
  have exT : rowT.Exact :=
    exact_of_δ₀ (H.homologySequence_exact₁ T hT n' n₀ h').exact_toComposableArrows
      (exact_of_δ₀ (H.homologySequence_exact₂ T hT n₀).exact_toComposableArrows
        (H.homologySequence_exact₃ T hT n₀ n₁ h).exact_toComposableArrows)
  have exT' : rowT'.Exact :=
    exact_of_δ₀ (H.homologySequence_exact₁ T' hT' n' n₀ h').exact_toComposableArrows
      (exact_of_δ₀ (H.homologySequence_exact₂ T' hT' n₀).exact_toComposableArrows
        (H.homologySequence_exact₃ T' hT' n₀ n₁ h).exact_toComposableArrows)
  let ψ : rowT ⟶ rowT' := homMk₄
    ((H.shift n').map φ.hom₃) ((H.shift n₀).map φ.hom₁) ((H.shift n₀).map φ.hom₂)
    ((H.shift n₀).map φ.hom₃) ((H.shift n₁).map φ.hom₁)
    (by change H.homologySequenceδ T n' n₀ h' ≫ (H.shift n₀).map φ.hom₁ =
          (H.shift n').map φ.hom₃ ≫ H.homologySequenceδ T' n' n₀ h'
        exact (H.homologySequenceδ_naturality φ n' n₀ h').symm)
    (by change (H.shift n₀).map T.mor₁ ≫ (H.shift n₀).map φ.hom₂ =
          (H.shift n₀).map φ.hom₁ ≫ (H.shift n₀).map T'.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by change (H.shift n₀).map T.mor₂ ≫ (H.shift n₀).map φ.hom₃ =
          (H.shift n₀).map φ.hom₂ ≫ (H.shift n₀).map T'.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    (by change H.homologySequenceδ T n₀ n₁ h ≫ (H.shift n₁).map φ.hom₁ =
          (H.shift n₀).map φ.hom₃ ≫ H.homologySequenceδ T' n₀ n₁ h
        exact (H.homologySequenceδ_naturality φ n₀ n₁ h).symm)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono exT exT' ψ h₃' h₁ h₃ h₁'

/-- **The diagram chase of the proof of the first assertion of Stacks 0FPV.** Let `φ` be a
morphism of distinguished triangles whose first component is invertible on cohomology in every
degree, whose two third vertices have no cohomology in the degrees `≥ m`, and whose third
component is epic on cohomology in degree `m - 1`. Then the second component is invertible on
cohomology in every degree `≥ m` and epic on cohomology in degree `m - 1`.

In the source this is "using the induced map of long exact sequences of cohomology sheaves from
the morphism of triangles above, a diagram chase shows this implies `H^i(K) ⟶ H^i(M)` is an
isomorphism for `i ≥ m` and surjective for `i = m - 1`". The epimorphism in degree `m - 1` is
the one `CategoryTheory.Pretriangulated.isSplitEpi_hom₃_of_comp` produces; the vanishing above
`m - 1` holds because both third vertices are the cones of approximations in degree `m`. -/
@[sga "6 I 1.4.2" "(i) ⇒ (ii)"]
theorem isIso_shift_map_hom₂_of_isZero_obj₃ (m : ℤ)
    (h₁ : ∀ n : ℤ, IsIso ((H.shift n).map φ.hom₁))
    (hz : ∀ n : ℤ, m ≤ n → IsZero ((H.shift n).obj T.obj₃))
    (hz' : ∀ n : ℤ, m ≤ n → IsZero ((H.shift n).obj T'.obj₃))
    (hepi : Epi ((H.shift (m - 1)).map φ.hom₃)) :
    (∀ n : ℤ, m ≤ n → IsIso ((H.shift n).map φ.hom₂)) ∧
      Epi ((H.shift (m - 1)).map φ.hom₂) := by
  have hiso₃ : ∀ n : ℤ, m ≤ n → IsIso ((H.shift n).map φ.hom₃) := by
    intro n hn
    have heq : (H.shift n).map φ.hom₃ = ((hz n hn).iso (hz' n hn)).hom :=
      (hz n hn).eq_of_src _ _
    rw [heq]
    infer_instance
  refine ⟨fun n hn => ?_, ?_⟩
  · have h₃' : Epi ((H.shift (n - 1)).map φ.hom₃) := by
      rcases eq_or_lt_of_le hn with rfl | hlt
      · simpa using hepi
      · have := hiso₃ (n - 1) (by omega)
        infer_instance
    have := h₁ n
    have := hiso₃ n hn
    have : Mono ((H.shift (n + 1)).map φ.hom₁) := by
      have := h₁ (n + 1)
      infer_instance
    exact isIso_shift_map_hom₂ H hT hT' φ (n - 1) n (n + 1) (by omega) rfl h₃'
      inferInstance inferInstance this
  · have he₁ : Epi ((H.shift (m - 1)).map φ.hom₁) := by
      have := h₁ (m - 1)
      infer_instance
    have hm₁ : Mono ((H.shift m).map φ.hom₁) := by
      have := h₁ m
      infer_instance
    exact epi_shift_map_hom₂ H hT hT' φ (m - 1) m (by omega) he₁ hepi hm₁

end CategoryTheory.Functor

end
