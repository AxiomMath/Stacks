module

public import StacksFrontier.CategoryTheory.Sites.Continuous.FreeAbelianLowerShriekTransition
public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriekTautological

/-!
# The free abelian sheaf functor carries the counit of lower shriek to the counit

Let `u : (C, T₀) ⥤ (D, T₁)` be a functor of sites, continuous and cocontinuous, so that
restriction `u^{-1}` along `u` has both an extension by zero `u_!` on the left and a direct image
on the right. Two comparisons move the free abelian sheaf functor across `u`:

* restriction commutes with it, by Mathlib's
  `CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility` — restriction commutes
  with sheafification, and the sectionwise free abelian group commutes with restriction of
  presheaves on the nose; this is what
  `CategoryTheory.SemiRepresentable.freeSheafPushforwardIso` is built from;
* extension by zero commutes with it, by `CategoryTheory.Functor.freeLowerShriekIso`, both
  composites being left adjoint to restriction followed by forgetting the group structure.

This module proves that the two comparisons **carry the counit of `u_! ⊣ u^{-1}` on sheaves of
sets to the counit on abelian sheaves**. That is the third and last of the three squares needed to
show that the free abelian sheaf comparison of Stacks 0D87 part (2) carries the shriek restriction
transition `j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}` on abelian sheaves to the one on sheaves of sets, the
other two being
`CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_naturality'` and
`CategoryTheory.Functor.freeLowerShriekIso_comp`.

## Main results

* `CategoryTheory.Functor.sheafPushforwardContinuous_map_freeSheafUnit`: **restricting the unit of
  the free abelian sheaf adjunction along `u` is the unit followed by the
  pushforward-sheafification comparison.** The content is Mathlib's characterisation
  `CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility` of that comparison by
  what it does to the sheafification unit.
* `CategoryTheory.Functor.shriekFreeAdjunction_unit_app_comp_map_counit`: the hypothesis of the
  uniqueness lemma below, namely that the two adjuncts agree.
* `CategoryTheory.Functor.freeLowerShriekIso_hom_app_comp_map_counit`: **the counit square.**

## Implementation notes

The counit of `u_! ⊣ u^{-1}` on abelian sheaves is a counit of
`CategoryTheory.Functor.freeShriekAdjunction` only after composing with the counit of the free
abelian sheaf adjunction, so `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit` does not
apply: the object the square is read at is not of the form `(right adjoint).obj _`. The substitute
is `Stacks.CategoryTheory.leftAdjointUniq_hom_app_comp_of_unit`, which reads uniqueness of a left
adjoint on the unit side instead, and whose hypothesis is exactly
`shriekFreeAdjunction_unit_app_comp_map_counit`.

Two frictions, both the "two spellings of one object" obstruction the neighbouring modules
record. `CategoryTheory.Category.assoc` is unusable by `rw` here — the outer and inner `≫` of
`(f ≫ g) ≫ h` carry different spellings of the category instance of `Sheaf T₀ (Type u)`, and `rw`
reports that the pattern does not occur in a goal that visibly contains it; the associativity
steps are therefore term-mode `refine Eq.trans (Category.assoc _ _ _) ?_`, which unifies by
defeq. Likewise `CategoryTheory.Functor.map_comp` cannot be used by `rw` to merge two
`(forget AddCommGrpCat).map` factors, because a `simp only` that mentions
`Functor.whiskerRight_app` rewrites `(forget AddCommGrpCat).map` into its `ConcreteCategory.hom`
coercion and the pattern is gone; that merge is done as a term,
`(F.map_comp _ _).symm.trans (congrArg F.map _)`.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Functor

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (T₀ : GrothendieckTopology C) (T₁ : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous T₀ T₁] [u.IsCocontinuous T₀ T₁]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasPointwiseRightKanExtension P]
  [HasWeakSheafify T₀ (Type u)] [HasWeakSheafify T₁ (Type u)]
  [HasWeakSheafify T₀ AddCommGrpCat.{u}] [HasWeakSheafify T₁ AddCommGrpCat.{u}]
  [∀ F : Cᵒᵖ ⥤ Type u, u.op.HasLeftKanExtension F]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasLeftKanExtension F]

omit [HasWeakSheafify T₀ (Type u)] [HasWeakSheafify T₁ (Type u)]
  [∀ F : Cᵒᵖ ⥤ Type u, u.op.HasLeftKanExtension F]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasLeftKanExtension F] in
/-- **Restricting the unit of the free abelian sheaf adjunction along a continuous and
cocontinuous functor of sites** gives the unit at the restricted sheaf, followed by the
pushforward-sheafification comparison at the presheaf `Z ⋙ ℤ`.

Both sides are morphisms of sheaves of sets, so the identity is checked on underlying presheaves
and then at an object, where `CategoryTheory.Sheaf.adjunction_unit_app_hom` splits each unit into
the sectionwise free abelian group unit followed by the sheafification unit; the free abelian
group units on the two sides are the same map, and the two sheafification units are matched by
Mathlib's `CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility`. -/
theorem sheafPushforwardContinuous_map_freeSheafUnit (Z : Sheaf T₁ (Type u)) :
    (u.sheafPushforwardContinuous (Type u) T₀ T₁).map
        ((Sheaf.adjunction T₁ AddCommGrpCat.adj).unit.app Z) =
      (Sheaf.adjunction T₀ AddCommGrpCat.adj).unit.app
          ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z) ≫
        (sheafCompose T₀ (forget AddCommGrpCat.{u})).map
          ((u.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u} T₀ T₁).hom.app
            (Z.obj ⋙ AddCommGrpCat.free)) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  have hts : (toSheafify T₀ (((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z).obj ⋙
          AddCommGrpCat.free)).app V ≫
        (((u.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u} T₀ T₁).hom.app
          (Z.obj ⋙ AddCommGrpCat.free)).hom).app V =
      (toSheafify T₁ (Z.obj ⋙ AddCommGrpCat.free)).app (u.op.obj V) :=
    NatTrans.congr_app (u.toSheafify_pullbackSheafificationCompatibility
      AddCommGrpCat.{u} T₀ T₁ (Z.obj ⋙ AddCommGrpCat.free)) V
  have hL : ((u.sheafPushforwardContinuous (Type u) T₀ T₁).map
        ((Sheaf.adjunction T₁ AddCommGrpCat.adj).unit.app Z)).hom.app V =
      ((Sheaf.adjunction T₁ AddCommGrpCat.adj).unit.app Z).hom.app (u.op.obj V) := rfl
  have hR : (((Sheaf.adjunction T₀ AddCommGrpCat.adj).unit.app
            ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z) ≫
          (sheafCompose T₀ (forget AddCommGrpCat.{u})).map
            ((u.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u} T₀ T₁).hom.app
              (Z.obj ⋙ AddCommGrpCat.free))).hom).app V =
      ((Sheaf.adjunction T₀ AddCommGrpCat.adj).unit.app
            ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z)).hom.app V ≫
        (forget AddCommGrpCat.{u}).map
          (((u.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u}
            T₀ T₁).hom.app (Z.obj ⋙ AddCommGrpCat.free)).hom.app V) := rfl
  have hts' : (forget AddCommGrpCat.{u}).map
          ((toSheafify T₀ (((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z).obj ⋙
            AddCommGrpCat.free)).app V) ≫
        (forget AddCommGrpCat.{u}).map
          (((u.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u} T₀ T₁).hom.app
            (Z.obj ⋙ AddCommGrpCat.free)).hom.app V) =
      (forget AddCommGrpCat.{u}).map
        ((toSheafify T₁ (Z.obj ⋙ AddCommGrpCat.free)).app (u.op.obj V)) :=
    ((forget AddCommGrpCat.{u}).map_comp _ _).symm.trans
      (congrArg (forget AddCommGrpCat.{u}).map hts)
  have key : ((Adjunction.whiskerRight Dᵒᵖ AddCommGrpCat.adj).unit.app Z.obj).app
          (u.op.obj V) ≫
        (forget AddCommGrpCat.{u}).map
          ((toSheafify T₁ (Z.obj ⋙ AddCommGrpCat.free)).app (u.op.obj V)) =
      ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).unit.app
            ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z).obj).app V ≫
        (forget AddCommGrpCat.{u}).map
            ((toSheafify T₀ (((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z).obj ⋙
              AddCommGrpCat.free)).app V) ≫
          (forget AddCommGrpCat.{u}).map
            (((u.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u}
              T₀ T₁).hom.app (Z.obj ⋙ AddCommGrpCat.free)).hom.app V) :=
    (congrArg (fun m => ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).unit.app
      ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z).obj).app V ≫ m) hts').symm
  rw [hL, hR, Sheaf.adjunction_unit_app_hom, Sheaf.adjunction_unit_app_hom,
    NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerRight_app]
  exact key

omit [HasWeakSheafify T₀ (Type u)]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasLeftKanExtension F] in
/-- **The two adjuncts agree.** The unit of
`CategoryTheory.Functor.shriekFreeAdjunction` at the restricted sheaf `u^{-1}Z`, followed by the
restriction of the free abelian sheaf functor applied to the counit of `u_! ⊣ u^{-1}` on sheaves
of sets, is the unit of the free abelian sheaf adjunction followed by the
pushforward-sheafification comparison.

This is the hypothesis `freeLowerShriekIso_hom_app_comp_map_counit` feeds to
`Stacks.CategoryTheory.leftAdjointUniq_hom_app_comp_of_unit`. The unit of the composite
adjunction splits by `CategoryTheory.Adjunction.comp_unit_app`; the naturality of the free abelian
sheaf unit at the counit and the right triangle identity of `u_! ⊣ u^{-1}` then collapse the
left-hand side to the restriction of the free abelian sheaf unit, which is
`sheafPushforwardContinuous_map_freeSheafUnit`. -/
theorem shriekFreeAdjunction_unit_app_comp_map_counit (Z : Sheaf T₁ (Type u)) :
    (shriekFreeAdjunction T₀ T₁ u).unit.app
          ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z) ≫
        (u.sheafPushforwardContinuous AddCommGrpCat.{u} T₀ T₁ ⋙
            sheafCompose T₀ (forget AddCommGrpCat.{u})).map
          ((Sheaf.composeAndSheafify T₁ AddCommGrpCat.free).map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
              T₀ T₁).counit.app Z)) =
      (Sheaf.adjunction T₀ AddCommGrpCat.adj).unit.app
          ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z) ≫
        (sheafCompose T₀ (forget AddCommGrpCat.{u})).map
          ((u.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u} T₀ T₁).hom.app
            (Z.obj ⋙ AddCommGrpCat.free)) := by
  rw [← sheafPushforwardContinuous_map_freeSheafUnit T₀ T₁ u Z]
  have hswap : (u.sheafPushforwardContinuous AddCommGrpCat.{u} T₀ T₁ ⋙
          sheafCompose T₀ (forget AddCommGrpCat.{u})).map
        ((Sheaf.composeAndSheafify T₁ AddCommGrpCat.free).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
            T₀ T₁).counit.app Z)) =
      (u.sheafPushforwardContinuous (Type u) T₀ T₁).map
        ((sheafCompose T₁ (forget AddCommGrpCat.{u})).map
          ((Sheaf.composeAndSheafify T₁ AddCommGrpCat.free).map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
              T₀ T₁).counit.app Z))) := rfl
  have hnat : (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
            T₀ T₁).counit.app Z ≫
        (Sheaf.adjunction T₁ AddCommGrpCat.adj).unit.app Z =
      (Sheaf.adjunction T₁ AddCommGrpCat.adj).unit.app
          ((Functor.sheafPullbackConstruction.sheafPullback u (Type u) T₀ T₁).obj
            ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z)) ≫
        (sheafCompose T₁ (forget AddCommGrpCat.{u})).map
          ((Sheaf.composeAndSheafify T₁ AddCommGrpCat.free).map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
              T₀ T₁).counit.app Z)) :=
    (Sheaf.adjunction T₁ AddCommGrpCat.adj).unit.naturality
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
        T₀ T₁).counit.app Z)
  have hu : (shriekFreeAdjunction T₀ T₁ u).unit.app
        ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u) T₀ T₁).unit.app
          ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z) ≫
        (u.sheafPushforwardContinuous (Type u) T₀ T₁).map
          ((Sheaf.adjunction T₁ AddCommGrpCat.adj).unit.app
            ((Functor.sheafPullbackConstruction.sheafPullback u (Type u) T₀ T₁).obj
              ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z))) :=
    Adjunction.comp_unit_app _ _ _
  have hbg : (u.sheafPushforwardContinuous (Type u) T₀ T₁).map
          ((Sheaf.adjunction T₁ AddCommGrpCat.adj).unit.app
            ((Functor.sheafPullbackConstruction.sheafPullback u (Type u) T₀ T₁).obj
              ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z))) ≫
        (u.sheafPushforwardContinuous (Type u) T₀ T₁).map
          ((sheafCompose T₁ (forget AddCommGrpCat.{u})).map
            ((Sheaf.composeAndSheafify T₁ AddCommGrpCat.free).map
              ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
                T₀ T₁).counit.app Z))) =
      (u.sheafPushforwardContinuous (Type u) T₀ T₁).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
            T₀ T₁).counit.app Z) ≫
        (u.sheafPushforwardContinuous (Type u) T₀ T₁).map
          ((Sheaf.adjunction T₁ AddCommGrpCat.adj).unit.app Z) :=
    ((u.sheafPushforwardContinuous (Type u) T₀ T₁).map_comp _ _).symm.trans
      ((congrArg (u.sheafPushforwardContinuous (Type u) T₀ T₁).map hnat.symm).trans
        ((u.sheafPushforwardContinuous (Type u) T₀ T₁).map_comp _ _))
  rw [hswap, hu]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m =>
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u) T₀ T₁).unit.app
      ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z) ≫ m) hbg) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact (eq_whisker ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
    T₀ T₁).right_triangle_components _) _).trans (Category.id_comp _)

omit [HasWeakSheafify T₀ (Type u)] in
/-- **The free abelian sheaf comparisons carry the counit of `u_! ⊣ u^{-1}` on sheaves of sets to
the counit on abelian sheaves.** For a sheaf of sets `Z` on `(D, T₁)`, the comparison
`CategoryTheory.Functor.freeLowerShriekIso` read at the restriction `u^{-1}Z`, followed by the
free abelian sheaf functor applied to the counit at `Z`, is the extension by zero of the
pushforward-sheafification comparison followed by the counit at `ℤ_Z^♯`.

This is the counit square of the free abelian sheaf comparison for an arbitrary continuous and
cocontinuous functor of sites. At the relocalization functor `r_f` of a morphism of
semi-representable objects it is the third of the three squares that carry the shriek restriction
transition of Stacks 0D87 part (2) across the free abelian sheaf functor. -/
theorem freeLowerShriekIso_hom_app_comp_map_counit (Z : Sheaf T₁ (Type u)) :
    (Functor.freeLowerShriekIso T₀ T₁ u).hom.app
          ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z) ≫
        (Sheaf.composeAndSheafify T₁ AddCommGrpCat.free).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
            T₀ T₁).counit.app Z) =
      (Functor.sheafPullbackConstruction.sheafPullback u AddCommGrpCat.{u} T₀ T₁).map
          ((Functor.freePushforwardIso T₀ T₁ u).inv.app Z) ≫
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u AddCommGrpCat.{u}
            T₀ T₁).counit.app
          ((Sheaf.composeAndSheafify T₁ AddCommGrpCat.free).obj Z) :=
  Stacks.CategoryTheory.leftAdjointUniq_hom_app_comp_of_unit
    (Sheaf.adjunction T₀ AddCommGrpCat.adj)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u AddCommGrpCat.{u} T₀ T₁)
    (shriekFreeAdjunction T₀ T₁ u)
    ((u.sheafPushforwardContinuous (Type u) T₀ T₁).obj Z)
    ((Sheaf.composeAndSheafify T₁ AddCommGrpCat.free).obj Z)
    ((Sheaf.composeAndSheafify T₁ AddCommGrpCat.free).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type u)
        T₀ T₁).counit.app Z))
    ((Functor.freePushforwardIso T₀ T₁ u).inv.app Z)
    (shriekFreeAdjunction_unit_app_comp_map_counit T₀ T₁ u Z)

end CategoryTheory.Functor

end
