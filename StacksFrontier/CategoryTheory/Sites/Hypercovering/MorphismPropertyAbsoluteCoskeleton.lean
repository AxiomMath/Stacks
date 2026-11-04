module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Map
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismProperty

/-!
# Hypercoverings for a property of morphisms via absolute coskeleta

Let `C` be a category with fibre products, `P` a property of morphisms of `C` and
`a : U → X` an augmented simplicial object of `C`. The condition in degree `n + 1 ≥ 2` of a
`P`-hypercovering asks that the matching morphism `U_{n+1} → (cosk_n sk_n U)_{n+1}` belong to
`P`, the coskeleton being formed in the slice category `C/X`.

For `n ≥ 1` the value `(cosk_n sk_n U)_{n+1}` is the limit of a diagram indexed by the category
`(Δ/⦋n+1⦌)_{≤n}`, which is connected, and the forgetful functor `C/X ⥤ C` preserves connected
limits. Hence, as soon as the coskeleta of `C` itself exist (for instance when `C` has finite
limits), the matching morphism formed in `C/X` and the one formed in `C` agree up to an
isomorphism of arrows which is the identity on `U_{n+1}`. For a property `P` respecting
isomorphisms the condition in degree `n + 1` may therefore equally be read with the coskeleton
of `U` formed in `C`. This is not so for `n = 0`: `(cosk_0 sk_0 U)_1` is `U₀ × U₀` in `C` but
`U₀ ×_X U₀` in `C/X`, which is why the degree-one condition is stated separately.

## Main results

* `CategoryTheory.SimplicialObject.Augmented.nonempty_matchingArrow_iso_coskAdj_unit`: for
  `n ≥ 1` the matching morphism `U_{n+1} → (cosk_n sk_n U)_{n+1}` formed in `C/X` is isomorphic,
  as an arrow of `C`, to the one formed in `C`.
* `CategoryTheory.MorphismProperty.isHypercovering_iff_coskAdj_unit`: for `P` respecting
  isomorphisms, an augmented simplicial object is a `P`-hypercovering if and only if
  `U₀ → X`, `U₁ → U₀ ×_X U₀` and the matching morphisms `U_{n+1} → (cosk_n sk_n U)_{n+1}`,
  `n ≥ 1`, with the coskeleta formed in `C`, belong to `P`.

## References

* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
* [Stacks Project, Tag 0183](https://stacks.math.columbia.edu/tag/0183)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory

namespace SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- For `n ≥ 1`, the matching morphism `U_{n+1} → (cosk_n sk_n U)_{n+1}` of an augmented
simplicial object `U → X`, formed with the coskeleton of the slice category over `X`, is
isomorphic as an arrow of `C`, by an isomorphism which is the identity on `U_{n+1}`, to the
degree-`n + 1` component of the unit `U → cosk_n sk_n U` of the coskeleton of `U` formed in `C`.
The limits defining the coskeleton in degree `n + 1` are connected, and the forgetful functor of
the slice category preserves connected limits. -/
theorem nonempty_matchingArrow_iso_coskAdj_unit (A : SimplicialObject.Augmented C) (n : ℕ)
    (hn : 1 ≤ n)
    [∀ Z : SimplicialObject.Truncated C n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension Z] :
    ∃ e : (matchingArrow A n).right ≅ ((cosk n).obj A.left).obj (op ⦋n + 1⦌),
      (matchingArrow A n).hom ≫ e.hom = ((coskAdj n).unit.app A.left).app (op ⦋n + 1⦌) := by
  let : HasFiniteLimits (Over A.right) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : ∀ F : SimplicialObject.Truncated (Over A.right) n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F :=
    (Truncated.hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
      (C := Over A.right)).2 (fun _ ↦ inferInstance) n (by omega)
  have : NeZero n := ⟨by omega⟩
  have : ∀ m : SimplexCategoryᵒᵖ,
      IsConnected (StructuredArrow m (SimplexCategory.Truncated.inclusion n).op) :=
    fun m ↦ Functor.Final.out m
  have : (Over.forget A.right).PreservesPointwiseRightKanExtensions
      (SimplexCategory.Truncated.inclusion n).op := fun _ _ ↦ inferInstance
  exact Stacks.CategoryTheory.Hypercovering.exists_iso_map_coskAdj_unit_app' n
    (over A) (Over.forget A.right) (op ⦋n + 1⦌)

/-- For `n ≥ 1`, the matching morphism `U_{n+1} → (cosk_n sk_n U)_{n+1}` formed in the slice
category over `X` is isomorphic, as an arrow of `C`, to the one formed in `C`. -/
theorem nonempty_matchingArrow_iso (A : SimplicialObject.Augmented C) (n : ℕ) (hn : 1 ≤ n)
    [∀ Z : SimplicialObject.Truncated C n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension Z] :
    Nonempty (matchingArrow A n ≅
      Arrow.mk (((coskAdj n).unit.app A.left).app (op ⦋n + 1⦌))) := by
  obtain ⟨e, he⟩ := nonempty_matchingArrow_iso_coskAdj_unit A n hn
  exact ⟨Arrow.isoMk (Iso.refl _) e (by simpa using he.symm)⟩

end SimplicialObject.Augmented

open SimplicialObject.Augmented in
/-- **A `P`-hypercovering via absolute coskeleta.** Let `C` be a category with fibre products in
which the coskeleta exist, and let `P` respect isomorphisms. An augmented simplicial object
`a : U → X` is a `P`-hypercovering if and only if `U₀ → X` is in `P`, `U₁ → U₀ ×_X U₀` is in `P`,
and for every `n ≥ 1` the morphism `U_{n+1} → (cosk_n sk_n U)_{n+1}` is in `P`, the coskeleton
of `U` being formed in `C`. -/
theorem MorphismProperty.isHypercovering_iff_coskAdj_unit {C : Type u} [Category.{v} C]
    [HasPullbacks C]
    [∀ (n : ℕ) (Z : SimplicialObject.Truncated C n),
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension Z]
    (P : MorphismProperty C) [P.RespectsIso] (A : SimplicialObject.Augmented C) :
    P.IsHypercovering A ↔ P (A.hom.app (Opposite.op ⦋0⦌)) ∧ P (firstMatchingArrow A).hom ∧
      ∀ n : ℕ, 1 ≤ n →
        P (((SimplicialObject.coskAdj n).unit.app A.left).app (Opposite.op ⦋n + 1⦌)) := by
  have key (n : ℕ) (hn : 1 ≤ n) :=
    P.arrow_mk_iso_iff (nonempty_matchingArrow_iso A n hn).some
  constructor <;> rintro ⟨h₀, h₁, h⟩ <;> refine ⟨h₀, h₁, fun n hn ↦ ?_⟩
  exacts [(key n hn).1 (h n hn), (key n hn).2 (h n hn)]

end CategoryTheory

end
