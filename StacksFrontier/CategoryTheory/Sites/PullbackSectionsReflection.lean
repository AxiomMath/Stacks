module

public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsMate

/-!
# The restriction map on sections of a sheaf pullback detects inverse images

Let `a : C ⥤ D`, `b : D ⥤ E` and `c : C ⥤ E` be continuous functors of sites with a
factorization `a ⋙ b ≅ c`. Two global sections of `a⁻¹F` have the same image under
`CategoryTheory.sheafPullbackSectionsRestriction` *exactly* when their inverse images along
`b` agree, as morphisms out of the inverse image of a terminal sheaf.

One implication is `CategoryTheory.sheafPullback_map_eq_of_sheafPullbackSectionsRestriction_eq`;
this file supplies the converse, and hence the equivalence. The converse is what turns the
equality locus of two sections on a small site — which is detected by inverse images, by Stacks
09XM — into a statement about two sections of the big-site presheaf `T ↦ Γ(T, f_T⁻¹F)`, whose
restriction maps are the maps of `sheafPullbackSectionsRestriction`.

## Main results

* `CategoryTheory.sheafPullbackSectionsRestriction_eq_of_sheafPullback_map_eq` — if the inverse
  images along `b` of two global sections of `a⁻¹F` agree, then so do their images under
  `sheafPullbackSectionsRestriction`.
* `CategoryTheory.sheafPullbackSectionsRestriction_eq_iff` — the two conditions are equivalent.

## Implementation notes

The proof is the computation in
`CategoryTheory.sheafPullback_map_eq_of_comp_sheafPullbackRestriction_eq` read backwards: the
`b`-adjunct of `b⁻¹σ ≫ sheafPullbackRestrictionAdjunct` is `σ ≫ sheafPullbackRestriction`, so
equal inverse images give equal composites with `sheafPullbackRestriction`; by naturality of
`CategoryTheory.Sheaf.ΓEquivHomTerminal` this says that the two sections have the same image
under the map `Sheaf.Γ` induces on `sheafPullbackRestriction`, which differs from
`sheafPullbackSectionsRestriction` by an isomorphism.

No invertibility of the adjunct is used, so the implication proved here needs none of the
hypotheses of `CategoryTheory.isIso_sheafPullbackRestrictionAdjunct` beyond those already
present.

## References

* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(b.sheafPushforwardContinuous (Type w) K L).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]
  [HasTerminal D] [HasTerminal E]
  [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]
  [HasSheafify K (Type w)] [HasTerminal (Sheaf K (Type w))]

/-- **The restriction map on global sections is detected by inverse images.** If two global
sections of `a⁻¹F` have the same inverse image along `b`, as morphisms out of the inverse image
of a terminal sheaf, then they have the same image under
`CategoryTheory.sheafPullbackSectionsRestriction`.

This is the converse of
`CategoryTheory.sheafPullback_map_eq_of_sheafPullbackSectionsRestriction_eq`. -/
public lemma sheafPullbackSectionsRestriction_eq_of_sheafPullback_map_eq (e : a ⋙ b ≅ c)
    {T : D} (hT : IsTerminal T) (hbT : IsTerminal (b.obj T)) (F : Sheaf J (Type w))
    (s₁ s₂ : (Sheaf.Γ K (Type w)).obj ((a.sheafPullback (Type w) J K).obj F))
    (h : (b.sheafPullback (Type w) K L).map (Sheaf.ΓEquivHomTerminal K _ s₁) =
      (b.sheafPullback (Type w) K L).map (Sheaf.ΓEquivHomTerminal K _ s₂)) :
    sheafPullbackSectionsRestriction J K L a b c e hT hbT F s₁ =
      sheafPullbackSectionsRestriction J K L a b c e hT hbT F s₂ := by
  let adjB := b.sheafAdjunctionContinuous (Type w) K L
  have hcomp : ∀ σ : (⊤_ (Sheaf K (Type w))) ⟶ (a.sheafPullback (Type w) J K).obj F,
      adjB.homEquiv _ _ ((b.sheafPullback (Type w) K L).map σ ≫
          sheafPullbackRestrictionAdjunct J K L a b c e F) =
        σ ≫ sheafPullbackRestriction J K L a b c e F := by
    intro σ
    rw [adjB.homEquiv_naturality_left]
    exact congrArg _ ((adjB.homEquiv _ _).apply_symm_apply _)
  have hΓ : (Sheaf.Γ K (Type w)).map (sheafPullbackRestriction J K L a b c e F) s₁ =
      (Sheaf.Γ K (Type w)).map (sheafPullbackRestriction J K L a b c e F) s₂ := by
    refine (Sheaf.ΓEquivHomTerminal K _).injective ?_
    rw [Sheaf.ΓEquivHomTerminal_naturality, Sheaf.ΓEquivHomTerminal_naturality, ← hcomp,
      ← hcomp, h]
  rw [sheafPullbackSectionsRestriction_eq J K L a b c e hT hbT F, types_comp_apply,
    types_comp_apply, hΓ]

/-- **The restriction map on global sections has the same fibres as inverse image along `b`.**
Two global sections of `a⁻¹F` agree after
`CategoryTheory.sheafPullbackSectionsRestriction` exactly when their inverse images along `b`
agree. -/
public lemma sheafPullbackSectionsRestriction_eq_iff (e : a ⋙ b ≅ c)
    {T : D} (hT : IsTerminal T) (hbT : IsTerminal (b.obj T)) (F : Sheaf J (Type w))
    (s₁ s₂ : (Sheaf.Γ K (Type w)).obj ((a.sheafPullback (Type w) J K).obj F)) :
    sheafPullbackSectionsRestriction J K L a b c e hT hbT F s₁ =
        sheafPullbackSectionsRestriction J K L a b c e hT hbT F s₂ ↔
      (b.sheafPullback (Type w) K L).map (Sheaf.ΓEquivHomTerminal K _ s₁) =
        (b.sheafPullback (Type w) K L).map (Sheaf.ΓEquivHomTerminal K _ s₂) :=
  ⟨sheafPullback_map_eq_of_sheafPullbackSectionsRestriction_eq J K L a b c e hT hbT F s₁ s₂,
    sheafPullbackSectionsRestriction_eq_of_sheafPullback_map_eq J K L a b c e hT hbT F s₁ s₂⟩

end CategoryTheory
