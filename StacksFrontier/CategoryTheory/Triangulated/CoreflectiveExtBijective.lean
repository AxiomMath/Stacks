module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Shift.Basic

/-!
# Homs out of a coreflective shift-stable subcategory

Let `𝒟` be a category with a shift by `ℤ` and let `P` be a property of objects of `𝒟`, stable
under the shift, whose inclusion has a right adjoint `R` (for instance `D_QCoh(𝒪_X) ⊆ D(𝒪_X)`
on a quasi-compact quasi-separated algebraic space, with `R` the derived coherator `DQ_X` of
[Stacks Project, Tag 0CR4]). If `φ : M ⟶ N` is a morphism with `R(φ)` an isomorphism, then for
every object `K` satisfying `P` the maps `Hom(K, M[i]) ⟶ Hom(K, N[i])` are bijective for all
`i`. This is the first step of the proof of [Stacks Project, Tag 0D3P]: with `K = NL_{X/B}`,
which lies in `D_QCoh(𝒪_X)`, the hypothesis `DQ_X(ℱ) ≅ DQ_X(𝒢)` gives
`Ext^i(NL_{X/B}, ℱ) ≅ Ext^i(NL_{X/B}, 𝒢)` for all `i`.

## Main results

* `CategoryTheory.ObjectProperty.bijective_comp_shift_map_of_isIso_rightAdjoint_map`

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.ObjectProperty

variable {𝒟 : Type*} [Category 𝒟] [HasShift 𝒟 ℤ] (P : ObjectProperty 𝒟)
  [P.ι.IsLeftAdjoint]

/-- Post-composition with an isomorphism is bijective. -/
theorem _root_.CategoryTheory.bijective_comp_of_isIso {𝒞 : Type*} [Category 𝒞] {K M N : 𝒞}
    (f : M ⟶ N) [IsIso f] : Function.Bijective (fun ξ : K ⟶ M => ξ ≫ f) :=
  ⟨fun a b h => by simpa using congrArg (· ≫ inv f) h, fun y => ⟨y ≫ inv f, by simp⟩⟩

/-- Under an adjunction `F ⊣ G`, post-composition with `φ` on homs out of `F X` is bijective
iff post-composition with `G.map φ` on homs into `G M` is. -/
private theorem bijective_comp_iff_bijective_comp_map {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {M N : D} (φ : M ⟶ N) :
    Function.Bijective (fun ξ : F.obj X ⟶ M => ξ ≫ φ) ↔
      Function.Bijective (fun η : X ⟶ G.obj M => η ≫ G.map φ) := by
  have key : (fun η : X ⟶ G.obj M => η ≫ G.map φ) =
      (adj.homEquiv X N) ∘ (fun ξ : F.obj X ⟶ M => ξ ≫ φ) ∘ (adj.homEquiv X M).symm := by
    funext η
    simp [Adjunction.homEquiv_naturality_right]
  rw [key]
  exact ⟨fun h => (adj.homEquiv X N).bijective.comp (h.comp (adj.homEquiv X M).symm.bijective),
    fun h => by
      simpa [Function.comp_def] using
        (adj.homEquiv X N).symm.bijective.comp (h.comp (adj.homEquiv X M).bijective)⟩

omit [HasShift 𝒟 ℤ] in
/-- Homs from an object satisfying `P` into `M` are homs into `R(M)`, naturally in `M`; so
post-composition with `φ` is bijective on them once `R(φ)` is an isomorphism. -/
theorem bijective_comp_of_isIso_rightAdjoint_map {K : 𝒟} (hK : P K) {M N : 𝒟} (φ : M ⟶ N)
    [IsIso (P.ι.rightAdjoint.map φ)] :
    Function.Bijective (fun ξ : K ⟶ M => ξ ≫ φ) :=
  (bijective_comp_iff_bijective_comp_map (Adjunction.ofIsLeftAdjoint P.ι)
    (X := (⟨K, hK⟩ : P.FullSubcategory)) φ).2 (bijective_comp_of_isIso _)

/-- **`Ext^i` out of the subcategory is inverted by `φ` once `R(φ)` is an isomorphism**: for
`K` satisfying a shift-stable coreflective property `P` and `φ : M ⟶ N` with `R(φ)` an
isomorphism, `Hom(K, M[i]) ⟶ Hom(K, N[i])` is bijective for every `i`. -/
theorem bijective_comp_shift_map_of_isIso_rightAdjoint_map [P.IsStableUnderShift ℤ]
    {K : 𝒟} (hK : P K) {M N : 𝒟} (φ : M ⟶ N) [IsIso (P.ι.rightAdjoint.map φ)] (i : ℤ) :
    Function.Bijective (fun ξ : K ⟶ M⟦i⟧ => ξ ≫ φ⟦i⟧') :=
  (bijective_comp_iff_bijective_comp_map
    (shiftEquiv' 𝒟 (-i) i (neg_add_cancel i)).toAdjunction φ).1
    (P.bijective_comp_of_isIso_rightAdjoint_map (P.le_shift (-i) K hK) φ)

end CategoryTheory.ObjectProperty

end
