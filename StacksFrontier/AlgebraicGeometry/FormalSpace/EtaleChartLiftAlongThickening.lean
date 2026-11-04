module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting along an étale chart across a universal homeomorphism

Let `π : W₀ ⟶ W` be a morphism from a representable presheaf to a presheaf on the big fppf site
of `S` which is étale after every representable base change, for instance an étale chart of an
algebraic space. Let `j₀ : Z₀ ⟶ Z` be a morphism of site objects whose underlying morphism of
schemes is a universal homeomorphism, for instance a closed immersion which is surjective on
points. Then a morphism `c : Z ⟶ W` together with a lift `l₀ : Z₀ ⟶ W₀` of its restriction to
`Z₀` has exactly one lift `l : Z ⟶ W₀` restricting to `l₀`.

This is the step of the étale-local reduction of the existence half of Stacks 0GI3 which lifts
a morphism out of a completion along an étale chart, one section at a time: the infinitesimal
neighbourhoods of the closed subset are universal homeomorphisms onto each other.

## Main results

* `AlgebraicGeometry.Space.existsUnique_lift_of_universalHomeomorphism`: the statement above.

## Implementation notes

The base change `P = Z ×_W W₀` is a site object étale over `Z`, and lifts of `c` are sections of
`P ⟶ Z`; the given `l₀` is a section over `Z₀`, and
`Stacks.Etale.existsUnique_section_of_universalHomeomorphism` (Stacks 0BTY) extends it uniquely.

## References

* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Lifting along an étale chart across a universal homeomorphism.** Let `π : W₀ ⟶ W` be étale
after every representable base change, let `j₀ : Z₀ ⟶ Z` be a morphism of site objects whose
underlying morphism of schemes is a universal homeomorphism, and let `c : Z ⟶ W` and
`l₀ : Z₀ ⟶ W₀` satisfy `l₀ ≫ π = j₀ ≫ c`. Then there is a unique `l : Z ⟶ W₀` with `l ≫ π = c`
and `j₀ ≫ l = l₀`. -/
@[sga "1 I 5.6" "more general"]
theorem existsUnique_lift_of_universalHomeomorphism {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W₀ Z Z₀ : BigFppfOver B S hS} (π : yoneda.obj W₀ ⟶ W)
    (hπ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf π)
    (j₀ : Z₀ ⟶ Z) [UniversalHomeomorphism ((BigFppfOver.toScheme B S hS).map j₀)]
    (c : yoneda.obj Z ⟶ W) (l₀ : Z₀ ⟶ W₀) (hl₀ : yoneda.map l₀ ≫ π = yoneda.map j₀ ≫ c) :
    ∃! l : Z ⟶ W₀, yoneda.map l ≫ π = c ∧ j₀ ≫ l = l₀ := by
  let T := BigFppfOver.toScheme B S hS
  have hrep := hπ.rep
  set P := hrep.pullback c
  set snd := hrep.snd c
  obtain ⟨fst, hfst⟩ := yoneda.map_surjective (hrep.fst c)
  have hw : yoneda.map fst ≫ π = yoneda.map snd ≫ c := by rw [hfst]; exact hrep.w c
  have hsnd : Etale (T.map snd) := hπ.property_snd c
  have lift_fst : ∀ {Y : BigFppfOver B S hS} (a : Y ⟶ W₀) (b : Y ⟶ Z) h,
      hrep.lift (yoneda.map a) b h ≫ fst = a := fun a b h =>
    yoneda.map_injective (by rw [Functor.map_comp, hfst]; exact hrep.lift_fst _ _ _)
  set s₀ := hrep.lift (yoneda.map l₀) j₀ hl₀
  have hs₀snd : s₀ ≫ snd = j₀ := hrep.lift_snd _ _ _
  have hs₀fst : s₀ ≫ fst = l₀ := lift_fst _ _ _
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, hσu⟩ := Stacks.Etale.existsUnique_section_of_universalHomeomorphism
    (T.map j₀) (T.map snd) (T.map s₀) (by rw [← Functor.map_comp, hs₀snd])
  obtain ⟨σ', hσ' : T.map σ' = σ⟩ :=
    BigFppfOver.exists_hom_of_comp_eq B S hS (X := Z) (Y := P) σ (by
      have h := Over.w snd
      have h' := congrArg B.inclusion.map h
      rw [Functor.map_comp] at h'
      change σ ≫ B.inclusion.map P.hom = B.inclusion.map Z.hom
      rw [← h']
      change σ ≫ T.map snd ≫ B.inclusion.map Z.hom = B.inclusion.map Z.hom
      rw [← Category.assoc, hσ₁, Category.id_comp])
  have hσ'snd : σ' ≫ snd = 𝟙 Z := T.map_injective (by simp [hσ', hσ₁])
  have hσ'j : j₀ ≫ σ' = s₀ := T.map_injective (by simp [hσ', hσ₂])
  refine ⟨σ' ≫ fst, ⟨?_, ?_⟩, ?_⟩
  · rw [Functor.map_comp, Category.assoc, hw, ← Category.assoc, ← Functor.map_comp, hσ'snd,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [← Category.assoc, hσ'j, hs₀fst]
  · rintro l ⟨hl₁, hl₂⟩
    have hc : yoneda.map l ≫ π = yoneda.map (𝟙 Z) ≫ c := by
      rw [CategoryTheory.Functor.map_id, Category.id_comp, hl₁]
    set τ := hrep.lift (yoneda.map l) (𝟙 Z) hc
    have hτsnd : τ ≫ snd = 𝟙 Z := hrep.lift_snd _ _ _
    have hτfst : τ ≫ fst = l := lift_fst _ _ _
    have hτj : j₀ ≫ τ = s₀ := by
      apply hrep.hom_ext
      · rw [Functor.map_comp, Category.assoc, hrep.lift_fst, hrep.lift_fst, ← hl₂,
          Functor.map_comp]
      · rw [Category.assoc, hτsnd, Category.comp_id, hs₀snd]
    have hτσ : T.map τ = σ := hσu _
      ⟨by rw [← Functor.map_comp, hτsnd, CategoryTheory.Functor.map_id],
        by rw [← Functor.map_comp, hτj]⟩
    have : τ = σ' := T.map_injective (hτσ.trans hσ'.symm)
    rw [← hτfst, this]

end Space

end AlgebraicGeometry

end
