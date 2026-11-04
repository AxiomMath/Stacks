module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite

/-!
# The base change of a composite along a prescribed point of the intermediate product

Let `C` be a category, let `uu : Uo ⟶ X` be a morphism of `C`, let `𝒳`, `𝒴`, `𝒵` be categories
over the slice `C/X` and let `Ff : 𝒳 ⥤ 𝒴`, `Fg : 𝒴 ⥤ 𝒵` be 1-morphisms over `C/X`. Fix a point
`zz : C/Uo ⥤ 𝒵` and presheaves `Fp`, `Gq` on `C/Uo` representing, over `C/Uo`, the two base
changes `Uo ×_{zz, 𝒵, Ff ⋙ Fg} 𝒳` and `Uo ×_{zz, 𝒵, Fg} 𝒴`, so that
`CategoryTheory.PresheafOfCategories.baseChangeNatTrans` is the comparison morphism
`α : Λ_{uu} Fp ⟶ Λ_{uu} Gq` of the relocalized presheaves.

`CategoryTheory.PresheafOfCategories.exists_isPullback_baseChangeNatTrans` identifies the fibre
of `α` over a *section* of `Λ_{uu} Gq` as the relocalization of a presheaf representing the base
change of `Ff` alone, along the point of `𝒴` that 2-Yoneda produces from that section. This file
is the companion statement in which the point is **given**: for any 1-morphism
`w : C/A ⥤ Uo ×_{zz, 𝒵, Fg} 𝒴` over `C/X` lying over `CategoryTheory.Over.map t`, the
relocalization of a presheaf representing

```text
A ×_{w ⋙ π₂, 𝒴, Ff} 𝒳
```

is a fibre product of `α`, the section being the one that `w` itself names.

Both forms are needed, and neither implies the other cheaply. A consumer covering the
intermediate product by representables — the proof of Stacks 045B — starts from a section and
needs the point; a consumer testing a property at a *prescribed* scheme-valued point of `𝒴` —
the proof of Stacks 05XK — starts from the point and needs the square, and for it a point merely
2-isomorphic to the prescribed one is not enough, because the presheaf it is handed represents
the base change along the prescribed point on the nose.

## Main results

* `CategoryTheory.PresheafOfCategories.exists_section_isPullback_baseChangeNatTrans_of_point`: the
  statement above.

## Implementation notes

The section named by `w` is reconstructed from its value at the tautological object `A → A` of
`C/A`, which is terminal there, so that
`CategoryTheory.PresheafOfCategories.sectionFamily_eq_of_eq_at_id` identifies the family of
restrictions of the reconstructed section with the family `w` names. The one wrinkle is that the
image of the tautological object under `CategoryTheory.Over.map t` is `A → 𝟙 ≫ t → X` rather than
`A → t → X`; the comparison is the isomorphism of `C/X` whose underlying morphism is the identity
of `A`, and `CategoryTheory.OverShriek.overMapTautHom` at the tautological object is its inverse.

The chain of equivalences over `C/A` is the one used for Stacks 045B, with the point no
longer produced by 2-Yoneda: the decomposition of the base change of a composite
(`CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_baseChange_splitSnd`), the
replacement of the two legs by categories of elements
(`CategoryTheory.TwoFibreProductOver.mapBase` and
`CategoryTheory.TwoFibreProductOver.precomposeSnd`), and the identification of the resulting
2-fibre product with a category of elements
(`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_twoFibreProductPresheaf`). It is
composed inside the theorem because at a concrete instantiation
`StacksRepresentableCFG.EquivalenceOver.trans` can no longer synthesize the `Category` instance
of a `CategoryTheory.TwoFibreProductOver`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 05XK](https://stacks.math.columbia.edu/tag/05XK)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.OverShriek

namespace CategoryTheory.PresheafOfCategories

universe v u v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u} [Category.{v} C] {X Uo : C} (uu : Uo ⟶ X)
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  {𝒵 : Type u₃} [Category.{v₃} 𝒵]
  {p𝒳 : 𝒳 ⥤ Over X} {p𝒴 : 𝒴 ⥤ Over X} {p𝒵 : 𝒵 ⥤ Over X}
  {Ff : 𝒳 ⥤ 𝒴} {Fg : 𝒴 ⥤ 𝒵} (zz : Over Uo ⥤ 𝒵)
  {Fp Gq : (Over Uo)ᵒᵖ ⥤ Type v}
  (hFf : Ff ⋙ p𝒴 = p𝒳)
  (E : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map uu) p𝒳 p𝒵 zz (Ff ⋙ Fg)) (discreteProjection Fp))
  (EG : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map uu) p𝒴 p𝒵 zz Fg) (discreteProjection Gq))

/-- **`CategoryTheory.OverShriek.overMapTautHom` at the tautological object is an isomorphism.**
The image of the tautological object `A → A` of `C/A` under `CategoryTheory.Over.map t` is
`A → 𝟙 ≫ t → X` rather than `A → t → X`, and the comparison between the two is the isomorphism
of `C/X` whose underlying morphism is the identity of `A`. -/
def overMapTautIso {A : C} (t : A ⟶ X) :
    (Over.map t).obj (Over.mk (𝟙 A)) ≅ Over.mk t where
  hom := overMapTautHom t (Over.mk (𝟙 A))
  inv := Over.homMk (𝟙 A) (by simp)
  hom_inv_id := Over.OverMorphism.ext (by simp)
  inv_hom_id := Over.OverMorphism.ext (by simp)

/-- **The fibre of the comparison morphism over the section named by a prescribed point.** Let
`w : C/A ⥤ Uo ×_{zz, 𝒵, Fg} 𝒴` be a 1-morphism over `C/X` lying over `Over.map t`. Then there
are a presheaf `fib` on `C/A` and a section `β` of `Λ_{uu} Gq` over `A → X` such that

* the relocalization of `fib` along `A → X`, with its structural morphism
  `CategoryTheory.OverShriek.relocalizeToYoneda`, is the fibre product of
  `CategoryTheory.PresheafOfCategories.baseChangeNatTrans` and `β`; and
* `fib` represents, over `C/A`, the base change `A ×_{w ⋙ π₂, 𝒴, Ff} 𝒳`.

Unlike `CategoryTheory.PresheafOfCategories.exists_isPullback_baseChangeNatTrans`, the point of
`𝒴` is the one prescribed by `w` rather than one produced from a section by 2-Yoneda, which is
what lets a consumer test a property of the structural morphism of a presheaf representing the
base change along a point it was handed.

The section `β` is *produced* here out of `w`, which is what distinguishes this from
`CategoryTheory.PresheafOfCategories.exists_isPullback_baseChangeNatTrans_of_point`: that
statement takes both the point and a section restricting to the family the point names, and is
the form to use when a section is already in hand. -/
theorem exists_section_isPullback_baseChangeNatTrans_of_point
    (hFg : Fg ⋙ p𝒵 = p𝒴) (hz : zz ⋙ p𝒵 = Over.map uu)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids) {A : C} (t : A ⟶ X)
    (w : Over A ⥤ TwoFibreProductOver (Over.map uu) p𝒴 p𝒵 zz Fg)
    (hw : w ⋙ TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg = Over.map t) :
    ∃ (fib : (Over A)ᵒᵖ ⥤ Type v)
      (c : (relocalizePresheafFunctor t).obj fib ⟶ (relocalizePresheafFunctor uu).obj Fp)
      (β : yoneda.obj (Over.mk t) ⟶ (relocalizePresheafFunctor uu).obj Gq),
      IsPullback c (relocalizeToYoneda t fib) (baseChangeNatTrans uu zz hFf E EG) β ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map t) p𝒳 p𝒴
            (w ⋙ TwoFibreProductOver.snd (Over.map uu) p𝒴 p𝒵 zz Fg) Ff)
          (discreteProjection fib)) := by
  classical
  have hFfg : (Ff ⋙ Fg) ⋙ p𝒵 = p𝒳 := by rw [Functor.assoc, hFg, hFf]
  have hsfX := TwoFibreProductOver.isFiberedInGroupoids (Over.map uu) p𝒳 p𝒵 zz (Ff ⋙ Fg)
    (Functor.IsFiberedInGroupoids.over_map uu) h𝒳 h𝒵 hz hFfg
  have hsfY := TwoFibreProductOver.isFiberedInGroupoids (Over.map uu) p𝒴 p𝒵 zz Fg
    (Functor.IsFiberedInGroupoids.over_map uu) h𝒴 h𝒵 hz hFg
  have hsfR := TwoFibreProductOver.isFiberedInGroupoids
    (TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg) p𝒳 p𝒴
    (TwoFibreProductOver.snd (Over.map uu) p𝒴 p𝒵 zz Fg) Ff hsfY h𝒳 h𝒴
    TwoFibreProductOver.snd_comp_eq hFf
  have hKsf := TwoFibreProductOver.splitSndProjection_comp_structureFunctor
    (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf
  -- The two legs of the base-changed product, read as 1-morphisms into a category of elements.
  have hbY : (EG.hom.functor ⋙ relocalizeToElements uu Gq) ⋙
      discreteProjection ((relocalizePresheafFunctor uu).obj Gq) =
      TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg :=
    (congrArg (· ⋙ Over.map uu) EG.hom.w).trans TwoFibreProductOver.fst_comp_eq
  have hσ : (w ⋙ (EG.hom.functor ⋙ relocalizeToElements uu Gq)) ⋙
      discreteProjection ((relocalizePresheafFunctor uu).obj Gq) = Over.map t :=
    by rw [Functor.assoc, hbY, hw]
  -- The section of `Λ_{uu} Gq` over `A → X` that `w` names, reconstructed from its value at the
  -- tautological object of `C/A`.
  set σ := w ⋙ (EG.hom.functor ⋙ relocalizeToElements uu Gq) with hσdef
  have hβ : ∀ τ : Over A,
      (yonedaEquiv.symm (((relocalizePresheafFunctor uu).obj Gq).map (overMapTautIso t).inv.op
          (sectionOfBasedFunctor σ hσ (Over.mk (𝟙 A))))).app
        (op ((Over.map t).obj τ)) (overMapTautHom t τ) =
      sectionOfBasedFunctor σ hσ τ := by
    refine congrFun (sectionFamily_eq_of_eq_at_id t _ _
      (fun g => app_overMapTautHom_map t _ g)
      (fun g => sectionOfBasedFunctor_map σ hσ g) ?_)
    have hval : (yonedaEquiv.symm (((relocalizePresheafFunctor uu).obj Gq).map
            (overMapTautIso t).inv.op
            (sectionOfBasedFunctor σ hσ (Over.mk (𝟙 A))))).app
          (op ((Over.map t).obj (Over.mk (𝟙 A)))) (overMapTautHom t (Over.mk (𝟙 A))) =
        ((relocalizePresheafFunctor uu).obj Gq).map (overMapTautIso t).hom.op
          (((relocalizePresheafFunctor uu).obj Gq).map (overMapTautIso t).inv.op
            (sectionOfBasedFunctor σ hσ (Over.mk (𝟙 A)))) := rfl
    rw [hval, ← Functor.map_comp_apply, ← op_comp, (overMapTautIso t).hom_inv_id, op_id,
      Functor.map_id_apply]
  -- The two 1-morphisms whose base change the presheaf represents.
  have hKb : (TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙
      (EG.hom.functor ⋙ relocalizeToElements uu Gq)) ⋙
      discreteProjection ((relocalizePresheafFunctor uu).obj Gq) =
      TwoFibreProductOver.structureFunctor (Over.map uu) p𝒳 p𝒵 zz (Ff ⋙ Fg) :=
    by rw [Functor.assoc, hbY, hKsf]
  have hcX : (elementsToRelocalize uu Fp ⋙ E.inv.functor) ⋙
      TwoFibreProductOver.structureFunctor (Over.map uu) p𝒳 p𝒵 zz (Ff ⋙ Fg) =
      discreteProjection ((relocalizePresheafFunctor uu).obj Fp) := by
    rw [← TwoFibreProductOver.fst_comp_eq]
    exact (congrArg (elementsToRelocalize uu Fp ⋙ · ⋙ Over.map uu) E.inv.w).trans
      (elementsToRelocalize_comp_eq uu Fp)
  have : (elementsToRelocalize uu Fp ⋙ E.inv.functor).IsEquivalence :=
    ((E.compRight (Over.map uu)).trans
      (relocalizeElementsEquivalenceOver uu Fp)).isEquivalence_inv_functor
  have : (EG.hom.functor ⋙ relocalizeToElements uu Gq).IsEquivalence :=
    ((EG.compRight (Over.map uu)).trans
      (relocalizeElementsEquivalenceOver uu Gq)).isEquivalence_hom_functor
  -- The four 2-fibre products involved are fibred in groupoids over `C/A`.
  have h1 := isFiberedInGroupoids_fst_overMap_of t (G := w)
    (F := TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf)
    hsfX hsfY hw hKsf
  have h2 := isFiberedInGroupoids_fst_overMap_of t (G := w)
    (F := TwoFibreProductOver.fst
      (TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg) p𝒳 p𝒴
      (TwoFibreProductOver.snd (Over.map uu) p𝒴 p𝒵 zz Fg) Ff)
    hsfR hsfY hw TwoFibreProductOver.fst_comp_eq
  have hP2 := isFiberedInGroupoids_fst_overMap_of t (G := σ)
    (F := TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙
      (EG.hom.functor ⋙ relocalizeToElements uu Gq))
    hsfX (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids hσ hKb
  have hP3 := isFiberedInGroupoids_fst_overMap_of t (G := σ)
    (F := (elementsToRelocalize uu Fp ⋙ E.inv.functor) ⋙
      (TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙
        (EG.hom.functor ⋙ relocalizeToElements uu Gq)))
    (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids
    (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids hσ
    (relocalizeBasedFunctor_comp_eq uu (baseChangeElementsMap uu zz hFf E EG)
      (baseChangeElementsMap_comp_eq uu zz hFf E EG))
  -- The chain of equivalences over `C/A`.
  obtain ⟨cap⟩ := TwoFibreProductOver.nonempty_equivalenceOver_baseChange_splitSnd
    (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf (Over.map t) hFg w hw
    (Functor.IsFiberedInGroupoids.over_map t) hsfX hsfR h1 h2
  obtain ⟨mb⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h1 hP2
    (TwoFibreProductOver.mapBase w
      (TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf)
      (EG.hom.functor ⋙ relocalizeToElements uu Gq) hbY)
    (TwoFibreProductOver.mapBase_comp_fst _ _ _ _)
    (TwoFibreProductOver.isEquivalence_mapBase hbY)
  obtain ⟨ps⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hP3 hP2
    (TwoFibreProductOver.precomposeSnd σ
      (TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙
        (EG.hom.functor ⋙ relocalizeToElements uu Gq))
      (elementsToRelocalize uu Fp ⋙ E.inv.functor) hcX)
    (TwoFibreProductOver.precomposeSnd_comp_fst _ _ _ _)
    (TwoFibreProductOver.isEquivalence_precomposeSnd
      (Functor.IsFiberedInGroupoids.over_map t)
      (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids hsfX hcX hKb)
  obtain ⟨tp⟩ := nonempty_equivalenceOver_twoFibreProductPresheaf t
    (relocalizeBasedFunctor uu (baseChangeElementsMap uu zz hFf E EG))
    (relocalizeBasedFunctor_comp_eq uu (baseChangeElementsMap uu zz hFf E EG)
      (baseChangeElementsMap_comp_eq uu zz hFf E EG)) σ hσ
  obtain ⟨c, hc⟩ := exists_isPullback_relocalize_twoFibreProductPresheaf t
    (relocalizeBasedFunctor uu (baseChangeElementsMap uu zz hFf E EG))
    (relocalizeBasedFunctor_comp_eq uu (baseChangeElementsMap uu zz hFf E EG)
      (baseChangeElementsMap_comp_eq uu zz hFf E EG)) σ hσ _ hβ
  exact ⟨_, c, _, hc, ⟨cap.symm.trans (mb.trans (ps.symm.trans tp))⟩⟩

end CategoryTheory.PresheafOfCategories

end
