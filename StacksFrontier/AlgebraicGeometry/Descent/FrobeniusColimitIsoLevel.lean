module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageShift

/-!
# An isomorphism of the colimit category is presented by an isomorphism of `C`

Let `F : C ⥤ C` be an endofunctor and let `colim_F C` be the colimit category of Stacks Tag
0EXA, whose objects are the pairs `(E, n)` and whose Hom-sets are the colimits
`colim_N Hom_C(F^{N - n}E, F^{N - m}G)`. Every morphism of `colim_F C` is presented at some level
by a morphism of `C`, and this file records that **an isomorphism of `colim_F C` is presented at
some level by an isomorphism of `C`**: the presentations of the two halves of an isomorphism can
be raised to a common level at which they are already mutually inverse in `C`.

## Main results

* `CategoryTheory.EndoColim.exists_common_level_of_iso`: the two halves of an isomorphism of
  `colim_F C` are presented at one and the same level.
* `CategoryTheory.EndoColim.exists_isoRep_of_iso`: **an isomorphism of `colim_F C` is presented
  at some level by a pair of mutually inverse morphisms of `C`.**
* `CategoryTheory.EndoColim.exists_iso_hom_eq`: the same, packaged as an isomorphism of `C`
  presenting the given isomorphism of `colim_F C`.

## Implementation notes

Both halves are first brought to the common level `k₁ + k₂`, by raising each presentation by the
level of the other. There the composite `e.hom ≫ e.inv` is presented by
`CategoryTheory.EndoColim.compHom`, which raises both factors by one and the same amount, so
that the identity `e.hom ≫ e.inv = 𝟙` says — through
`CategoryTheory.EndoColim.Hom.of_eq_of_iff` and
`CategoryTheory.EndoColim.Hom.of_id` — that the raises of the two presentations by some amount
compose to an identity of `C`, after transports comparing the exponents. Those transports cancel
by `CategoryTheory.endoHomCast_comp_endoHomCast`, which is the content of
`CategoryTheory.endoRaise_comp_endoRaise_eq_id_of_eq_id`: the clean invariant is that
`endoRaise f m ≫ endoRaise g m` is an identity, a composite which needs no transport at all
since the exponents of the two raises match on the nose.

The two halves of the inverse relation are produced at two unrelated amounts, and
`CategoryTheory.endoRaise_comp_endoRaise_eq_id_of_le` raises both to their sum; a single further
application of `CategoryTheory.EndoColim.Hom.of_raise` moves the presentations to the level
`k₁ + k₂ + m` at which both relations hold.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-! ### Transports around a composite which is an identity -/

/-- **A composite of transported raises which is an identity is an identity before the
transports.** The two raises are by the same amount, so their exponents match on the nose and the
untransported composite is already defined. -/
lemma endoRaise_comp_endoRaise_eq_id_of_eq_id {E G : C} {a b m q t : ℕ}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G)
    (g : (F.endoIter b).obj G ⟶ (F.endoIter a).obj E)
    (h₁ h₁' : a + m = q) (h₂ h₂' : b + m = t)
    (h : endoHomCast h₁ h₂ (endoRaise f m) ≫ endoHomCast h₂' h₁' (endoRaise g m) =
      𝟙 ((F.endoIter q).obj E)) :
    endoRaise f m ≫ endoRaise g m = 𝟙 ((F.endoIter (a + m)).obj E) := by
  rw [endoHomCast_comp_endoHomCast] at h
  have h' := congrArg (endoHomCast h₁.symm h₁.symm) h
  rw [endoHomCast_endoHomCast, endoHomCast_id] at h'
  exact h'

/-- **Two raises which compose to an identity still compose to an identity after being raised
further.** -/
lemma endoRaise_comp_endoRaise_eq_id_of_le {E G : C} {a b : ℕ}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G)
    (g : (F.endoIter b).obj G ⟶ (F.endoIter a).obj E) {m m' : ℕ} (hm : m ≤ m')
    (h : endoRaise f m ≫ endoRaise g m = 𝟙 ((F.endoIter (a + m)).obj E)) :
    endoRaise f m' ≫ endoRaise g m' = 𝟙 ((F.endoIter (a + m')).obj E) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h₁ := congrArg (fun x ↦ endoRaise x t) h
  simp only [endoRaise_comp, endoRaise_id, endoRaise_endoRaise] at h₁
  exact endoRaise_comp_endoRaise_eq_id_of_eq_id f g _ _ _ _ h₁

namespace EndoColim

/-! ### The two halves of an isomorphism at a common level -/

/-- Raising a presentation by `k₂` presents the same morphism at the level `k₁ + k₂ = k`. -/
private lemma Hom.of_endoHomCast_endoRaise {A B : EndoColim F} {k₁ k₂ k : ℕ} (hk : k₁ + k₂ = k)
    (f : (F.endoIter (B.stage + k₁)).obj A.obj ⟶ (F.endoIter (A.stage + k₁)).obj B.obj)
    (u : A ⟶ B) (hf : Hom.of k₁ f = u) :
    Hom.of k (endoHomCast (by omega) (by omega) (endoRaise f k₂)) = u := by
  subst hk
  exact (Hom.of_raise k₁ f k₂).trans hf

/-- **The two halves of an isomorphism of `colim_F C` are presented at one and the same level**,
by raising each presentation by the level of the other. -/
lemma exists_common_level_of_iso {A B : EndoColim F} (e : A ≅ B) :
    ∃ (k : ℕ) (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj)
      (g : (F.endoIter (A.stage + k)).obj B.obj ⟶ (F.endoIter (B.stage + k)).obj A.obj),
      Hom.of k f = e.hom ∧ Hom.of k g = e.inv := by
  obtain ⟨k₁, f₁, hf₁⟩ := Hom.exists_of e.hom
  obtain ⟨k₂, g₁, hg₁⟩ := Hom.exists_of e.inv
  exact ⟨k₁ + k₂, _, _, Hom.of_endoHomCast_endoRaise rfl f₁ _ hf₁,
    Hom.of_endoHomCast_endoRaise (Nat.add_comm k₂ k₁) g₁ _ hg₁⟩

/-! ### The inverse relations at a level -/

/-- **An identity `e.hom ≫ e.inv = 𝟙` in `colim_F C`, with both halves presented at one level,
holds in `C` after both presentations are raised by some amount.** -/
lemma exists_endoRaise_comp_eq_id {A B : EndoColim F} {k : ℕ}
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj)
    (g : (F.endoIter (A.stage + k)).obj B.obj ⟶ (F.endoIter (B.stage + k)).obj A.obj)
    (h : Hom.of k f ≫ Hom.of k g = 𝟙 A) :
    ∃ m : ℕ, endoRaise f m ≫ endoRaise g m =
      𝟙 ((F.endoIter (B.stage + k + m)).obj A.obj) := by
  have h' : Hom.of (B.stage + k + k) (compHom k f k g) =
      Hom.of (B.stage + k + k)
        (𝟙 ((F.endoIter (A.stage + (B.stage + k + k))).obj A.obj)) :=
    h.trans (Hom.of_id A (B.stage + k + k)).symm
  rw [Hom.of_eq_of_iff] at h'
  obtain ⟨j, i, hji, he⟩ := h'
  obtain rfl : j = i := Nat.add_left_cancel (n := B.stage + k + k) hji
  refine ⟨A.stage + k + j, ?_⟩
  simp only [compHom, endoRaise_comp, endoRaise_endoHomCast, endoRaise_endoRaise,
    endoHomCast_comp_rfl, endoHomCast_endoHomCast, endoRaise_id, endoHomCast_id] at he
  exact endoRaise_comp_endoRaise_eq_id_of_eq_id f g _ _ _ _ he

/-! ### An isomorphism is presented by an isomorphism -/

/-- **An isomorphism of `colim_F C` is presented at some level by an isomorphism of `C`**: there
are a level `k` and mutually inverse morphisms `f` and `g` of `C` at that level presenting the
two halves of the isomorphism. -/
theorem exists_isoRep_of_iso {A B : EndoColim F} (e : A ≅ B) :
    ∃ (k : ℕ) (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj)
      (g : (F.endoIter (A.stage + k)).obj B.obj ⟶ (F.endoIter (B.stage + k)).obj A.obj),
      f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ ∧ Hom.of k f = e.hom ∧ Hom.of k g = e.inv := by
  obtain ⟨k₀, f, g, hf, hg⟩ := exists_common_level_of_iso e
  obtain ⟨m₁, h₁⟩ := exists_endoRaise_comp_eq_id f g (by rw [hf, hg]; exact e.hom_inv_id)
  obtain ⟨m₂, h₂⟩ := exists_endoRaise_comp_eq_id g f (by rw [hf, hg]; exact e.inv_hom_id)
  have hA := endoRaise_comp_endoRaise_eq_id_of_le f g (Nat.le_add_right m₁ m₂) h₁
  have hB := endoRaise_comp_endoRaise_eq_id_of_le g f (Nat.le_add_left m₂ m₁) h₂
  refine ⟨k₀ + (m₁ + m₂), endoHomCast (by omega) (by omega) (endoRaise f (m₁ + m₂)),
    endoHomCast (by omega) (by omega) (endoRaise g (m₁ + m₂)), ?_, ?_, ?_, ?_⟩
  · rw [endoHomCast_comp_endoHomCast, hA, endoHomCast_id]
  · rw [endoHomCast_comp_endoHomCast, hB, endoHomCast_id]
  · exact (Hom.of_raise k₀ f (m₁ + m₂)).trans hf
  · exact (Hom.of_raise k₀ g (m₁ + m₂)).trans hg

/-- **An isomorphism of `colim_F C` is presented at some level by an isomorphism of `C`**, in the
form of an isomorphism of `C` whose underlying morphism presents the given one. -/
theorem exists_iso_hom_eq {A B : EndoColim F} (e : A ≅ B) :
    ∃ (k : ℕ) (u : (F.endoIter (B.stage + k)).obj A.obj ≅ (F.endoIter (A.stage + k)).obj B.obj),
      Hom.of k u.hom = e.hom := by
  obtain ⟨k, f, g, hfg, hgf, hf, hg⟩ := exists_isoRep_of_iso e
  exact ⟨k, ⟨f, g, hfg, hgf⟩, hf⟩

end EndoColim

end CategoryTheory

end
