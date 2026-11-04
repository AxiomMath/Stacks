module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# The diagonal of the explicit 2-fibre product of categories

Let `G : C ⥤ E` be a functor. Its diagonal is the functor `Δ_G : C ⥤ G ⊡ G` into the explicit
2-fibre product `CategoryTheory.Limits.CategoricalPullback`, sending `x` to the triple
`(x, x, 𝟙)`. When `E` is a groupoid, `G` is fully faithful if and only if `Δ_G` is an
equivalence; this is the form of Stacks 04Z7 for the explicit 2-fibre product of categories.

## Main definitions

* `CategoryTheory.Limits.CategoricalPullback.diagonal`: the diagonal `Δ_G : C ⥤ G ⊡ G`.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.isGroupoid`: the explicit 2-fibre product of two
  functors out of groupoids is a groupoid.
* `CategoryTheory.Limits.CategoricalPullback.fullyFaithful_iff_isEquivalence_diagonal`: a
  functor into a groupoid is fully faithful if and only if its diagonal is an equivalence.

## References

* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

section IsGroupoid

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

/-- The explicit 2-fibre product of two functors out of groupoids is a groupoid: a morphism of
the 2-fibre product is invertible as soon as both of its components are. -/
instance isGroupoid (F : A ⥤ B) (G : C ⥤ B) [IsGroupoid A] [IsGroupoid C] :
    IsGroupoid (F ⊡ G) where
  all_isIso f :=
    (CategoricalPullback.isIso_iff F G f).2 ⟨IsGroupoid.all_isIso _, IsGroupoid.all_isIso _⟩

end IsGroupoid

section Diagonal

variable {C : Type u₁} {E : Type u₂} [Category.{v₁} C] [Category.{v₂} E]

/-- The diagonal `Δ_G : C ⥤ G ⊡ G` of a functor `G : C ⥤ E`: it sends an object `x` to the
triple `(x, x, 𝟙)` and a morphism `f` to the pair `(f, f)`. -/
@[implicit_reducible]
def diagonal (G : C ⥤ E) : C ⥤ G ⊡ G where
  obj x := { fst := x, snd := x, iso := Iso.refl (G.obj x) }
  map f := { fst := f, snd := f, w := by simp }

variable (G : C ⥤ E)

/-- The first component of `Δ_G x` is `x`. -/
@[simp] lemma diagonal_obj_fst (x : C) : ((diagonal G).obj x).fst = x := rfl

/-- The second component of `Δ_G x` is `x`. -/
@[simp] lemma diagonal_obj_snd (x : C) : ((diagonal G).obj x).snd = x := rfl

/-- The structural isomorphism of `Δ_G x` is the identity of `G x`. -/
@[simp] lemma diagonal_obj_iso (x : C) : ((diagonal G).obj x).iso = Iso.refl (G.obj x) := rfl

/-- The first component of `Δ_G f` is `f`. -/
@[simp] lemma diagonal_map_fst {x y : C} (f : x ⟶ y) : ((diagonal G).map f).fst = f := rfl

/-- The second component of `Δ_G f` is `f`. -/
@[simp] lemma diagonal_map_snd {x y : C} (f : x ⟶ y) : ((diagonal G).map f).snd = f := rfl

/-- The diagonal of any functor is faithful. -/
instance faithful_diagonal : (diagonal G).Faithful where
  map_injective {_ _} {_ _} h := by
    simpa using congrArg CategoricalPullback.Hom.fst h

/-- The diagonal of a faithful functor is full. -/
theorem full_diagonal [G.Faithful] : (diagonal G).Full where
  map_surjective {_ _} m :=
    ⟨m.fst, CategoricalPullback.hom_ext rfl
      (G.map_injective (by simpa using m.w))⟩

/-- If the diagonal of `G` is full, then `G` is faithful. -/
theorem faithful_of_full_diagonal (h : (diagonal G).Full) : G.Faithful where
  map_injective {x y} {f g} hfg := by
    obtain ⟨k, hk⟩ := h.map_surjective
      (⟨f, g, by simp [hfg]⟩ : (diagonal G).obj x ⟶ (diagonal G).obj y)
    have h₁ : k = f := by simpa using congrArg CategoricalPullback.Hom.fst hk
    have h₂ : k = g := by simpa using congrArg CategoricalPullback.Hom.snd hk
    exact h₁.symm.trans h₂

/-- The diagonal of a fully faithful functor is essentially surjective. -/
theorem essSurj_diagonal [G.Full] [G.Faithful] : (diagonal G).EssSurj where
  mem_essImage t := by
    have : IsIso (G.map (G.preimage t.iso.hom)) := by
      rw [G.map_preimage]; infer_instance
    have : IsIso (G.preimage t.iso.hom) := isIso_of_fully_faithful G _
    exact ⟨t.fst, ⟨mkIso (Iso.refl _) (asIso (G.preimage t.iso.hom)) (by simp)⟩⟩

/-- If `E` is a groupoid and the diagonal of `G : C ⥤ E` is essentially surjective, then `G` is
full. -/
theorem full_of_essSurj_diagonal [IsGroupoid E] (h : (diagonal G).EssSurj) : G.Full where
  map_surjective {x y} w := by
    have : IsIso w := IsGroupoid.all_isIso w
    obtain ⟨z, ⟨e⟩⟩ := h.mem_essImage (⟨x, y, asIso w⟩ : G ⊡ G)
    have : IsIso (show z ⟶ x from e.hom.fst) := inferInstanceAs (IsIso e.hom.fst)
    have hkey : G.map (show z ⟶ x from e.hom.fst) ≫ w =
        G.map (show z ⟶ y from e.hom.snd) := by simpa using e.hom.w
    refine ⟨inv (show z ⟶ x from e.hom.fst) ≫ (show z ⟶ y from e.hom.snd), ?_⟩
    rw [G.map_comp, ← hkey, ← Category.assoc, ← G.map_comp, IsIso.inv_hom_id, G.map_id,
      Category.id_comp]

/-- A functor `G : C ⥤ E` into a groupoid is fully faithful if and only if its diagonal
`Δ_G : C ⥤ G ⊡ G` is an equivalence. -/
theorem fullyFaithful_iff_isEquivalence_diagonal [IsGroupoid E] :
    (G.Full ∧ G.Faithful) ↔ (diagonal G).IsEquivalence :=
  ⟨fun ⟨_, _⟩ => { faithful := faithful_diagonal G, full := full_diagonal G
                   essSurj := essSurj_diagonal G },
    fun hΔ => ⟨full_of_essSurj_diagonal G hΔ.essSurj, faithful_of_full_diagonal G hΔ.full⟩⟩

end Diagonal

end CategoryTheory.Limits.CategoricalPullback

end
