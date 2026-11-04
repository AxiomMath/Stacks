module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.CanonicalMapAsDeltaFunctorMorphism
import StacksCore.Tactic.StacksAttribute

/-! # The explicit chain map induces the canonical map on homology

Let `f : C' ⥤ C` be a functor between small categories, let `F` be an abelian presheaf on `C`,
let `F'` be one on `C'`, and let `t : F' ⟶ f⁻¹F` be a morphism of presheaves. Stacks 08PH
displays a chain map `K_•(F') ⟶ K_•(F)` of simplicial replacement complexes and asserts that,
under the comparison of Stacks 08PG between `H_n(C, -)` and the homology of the simplicial
replacement, it induces the canonical map `H_n(C', F') ⟶ H_n(C, F)`. This file proves that
identification, which completes Stacks 08PH.

## The argument

Both sides are natural in the coefficients, and the comparison of Stacks 08PG is a canonical
isomorphism of δ-functors, so the identification is a statement about morphisms of δ-functors
and the universality of the simplicial replacement δ-functor reduces it to degree zero. The
statement splits into two halves.

**The coefficient half.** The chain map factors as the coefficient change `K_•(t)` followed by
the chain map with identity coefficients, `replacementChainMap_eq_comp`; correspondingly the
canonical map factors as `Lₙ colim_{C'}(t)` followed by the canonical map with identity
coefficients, `homologyMapAux_eq_comp`. Both factorizations are computations on one summand,
respectively an application of `Stacks.CategoryHomology.homologyMapAux_eq` to the composite of
the two lifts. The coefficient half of the identification is then exactly the naturality of the
08PG comparison, `Stacks.CategoryHomology.categoryHomologyReplacementIso_naturality`.

**The index half.** With the coefficient morphism the identity, both sides are morphisms of
δ-functors out of `F ↦ H_n(C', f⁻¹F)` — that is
`Stacks.CategoryHomology.homologyMapAuxDeltaHom` and
`Stacks.CategoryHomology.replacementChainMapDeltaHom`, and it is the part of Stacks 08PH that
required the new homological algebra. The universality of
`Stacks.CategoryHomology.replacementHomologyDeltaFunctor` identifies them as soon as their
degree-zero components agree, and in degree zero both are `Limits.colimit.pre`:

* `replacementChainMap_homologyMap_zero`: the chain map is compatible with the augmentations
  `K_0(G) ⟶ colim G` in degree zero, by a one-summand computation and `Limits.colimit.ι_pre`, so
  on degree-zero homology it is `colimit.pre` read through
  `Stacks.CategoryHomology.replacementHomologyZeroIsoColimit`;
* `homologyMapAux_fromLeftDerivedZero`: the canonical map is compatible with
  `CategoryTheory.Functor.fromLeftDerivedZero`, because the lift used to define it is compatible
  with the augmentations in degree zero and the comparison of the two colimits is natural.

## Main results

* `Stacks.CategoryHomology.replacementChainMap_homologyMap`: **Stacks 08PH**, the identification
  of the homology map of the explicit chain map with
  `Stacks.CategoryHomology.categoryHomologyMap`.
* `Stacks.CategoryHomology.replacementChainMap_homologyMap_iso`: naturally isomorphic indexing
  functors with correspondingly reindexed coefficient morphisms induce the same map on the
  homology of the simplicial replacements.
* `Stacks.CategoryHomology.homologyMapAux_homologyMap`: the index half, stated separately.

## Implementation notes

**Universes have to be pinned by hand throughout.** The value universe of the presheaves is
`max u u' v`, while every declaration about the simplicial replacement over a single category
`C : Type u` is stated for presheaves valued in `AddCommGrpCat.{max u v}` or, in the case of
`Stacks.CategoryHomology.simplicialReplacementComplex`, in `AddCommGrpCat.{v}`. Solving
`max u ?v =?= max u u' v` for `?v` is beyond Lean's level unifier even though `?v := max u' v`
works, so every such occurrence carries explicit universes — and the two conventions must not be
confused: `replacementAugmentation.{u, max u' v}` but
`simplicialReplacementComplex.{u, max u u' v}`.

**`replacementHomologyZeroIsoColimit_naturality'`** is the two-category form of the
one-category `Stacks.CategoryHomology.replacementHomologyZeroIsoColimit_naturality`; its proof is
the same, since nothing in it uses that the two presheaves live on one category. It is stated
here rather than by generalizing that lemma because that lemma's universe shape is
`max u v` and generalizing it to two categories would leave the existing call site solving
`max u ?u₂ v =?= max u v`.

**`pOpcycles_comp_fromLeftDerivedZero'_aug0`** restates Mathlib's
`CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'` with the augmentation
spelled `CategoryTheory.ProjectiveResolution.aug0`, whose codomain is the resolved object rather
than `((ChainComplex.single₀ _).obj Z).X 0`. The two differ only by default-transparency
unfolding — which is why Mathlib's own statement carries
`set_option backward.isDefEq.respectTransparency false` — and the `aug0` spelling is the one in
which the naturality of `Stacks.CategoryHomology.colimitRestrictionPre` can be applied.

**Term mode for the two `NatTrans.comp_app`s** in the proof of
`replacementChainMapDeltaHom_comp_eq`: the two morphisms being composed there are natural
transformations between functors whose sources are spelled differently (`W ⋙ Hₙ` against the
degree-`n` functor of a precomposed δ-functor), so the composite is type-correct only at default
transparency and `simp only [NatTrans.comp_app]` reports no progress.

## References

* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u' v

namespace Stacks.CategoryHomology

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C']

/-! ### Degree zero for the explicit chain map -/

/-- **The explicit chain map with identity coefficients is compatible with the augmentations.**
On the summand indexed by a one-object string `U'` of `C'` the left side is the colimit injection
of `F` at `f(U')` and the right side is the colimit injection of `f⁻¹F` at `U'` followed by the
comparison of the two colimits, and the two agree by `CategoryTheory.Limits.colimit.ι_pre`. -/
lemma replacementChainMap_f_zero_comp_augmentation (f : C' ⥤ C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    (replacementChainMap f (𝟙 (f.op ⋙ F))).f 0 ≫ replacementAugmentation.{u, max u' v} F =
      replacementAugmentation.{u', max u v} (f.op ⋙ F) ≫ colimit.pre F f.op := by
  refine replacementGroup_hom_ext 0 fun x s => ?_
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, replacementChainMap_degreewise,
    replacementGroupMap_on_summand, replacementAugmentation_summand.{u, max u' v},
    replacementAugmentation_summand.{u', max u v}]
  have h := ConcreteCategory.congr_hom (colimit.ι_pre F f.op (op x.right)) s
  simp only [ConcreteCategory.comp_apply] at h
  exact h.symm

/-- **The two-category form of
`Stacks.CategoryHomology.replacementHomologyZeroIsoColimit_naturality`.** A chain map between the
simplicial replacements of presheaves on two different small categories which is compatible in
degree zero with the augmentations induces, on degree-zero homology, the map it is compatible
with. -/
theorem replacementHomologyZeroIsoColimit_naturality'
    {G : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {G' : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (Φ : simplicialReplacementComplex.{u', max u u' v} G ⟶
      simplicialReplacementComplex.{u, max u u' v} G')
    (ψ : colimit G ⟶ colimit G')
    (hΦ : Φ.f 0 ≫ replacementAugmentation.{u, max u' v} G' =
      replacementAugmentation.{u', max u v} G ≫ ψ) :
    HomologicalComplex.homologyMap Φ 0 ≫
        (replacementHomologyZeroIsoColimit.{u, max u' v} G').hom =
      (replacementHomologyZeroIsoColimit.{u', max u v} G).hom ≫ ψ := by
  have hop : HomologicalComplex.opcyclesMap Φ 0 ≫
      (replacementOpcyclesZeroIsoColimit.{u, max u' v} G').hom =
      (replacementOpcyclesZeroIsoColimit.{u', max u v} G).hom ≫ ψ := by
    rw [← cancel_epi ((simplicialReplacementComplex.{u', max u u' v} G).pOpcycles 0),
      HomologicalComplex.p_opcyclesMap_assoc,
      pOpcycles_comp_replacementOpcyclesZeroIsoColimit.{u, max u' v},
      pOpcycles_comp_replacementOpcyclesZeroIsoColimit_assoc.{u', max u v}, hΦ]
  have hhom : HomologicalComplex.homologyMap Φ 0 ≫
      (ChainComplex.isoHomologyι₀ (simplicialReplacementComplex.{u, max u u' v} G')).hom =
      (ChainComplex.isoHomologyι₀ (simplicialReplacementComplex.{u', max u u' v} G)).hom ≫
        HomologicalComplex.opcyclesMap Φ 0 := by
    rw [← cancel_epi
        (ChainComplex.isoHomologyι₀ (simplicialReplacementComplex.{u', max u u' v} G)).inv,
      Iso.inv_hom_id_assoc, ChainComplex.isoHomologyι₀_inv_naturality_assoc, Iso.inv_hom_id,
      Category.comp_id]
  calc HomologicalComplex.homologyMap Φ 0 ≫
        (replacementHomologyZeroIsoColimit.{u, max u' v} G').hom
      = (HomologicalComplex.homologyMap Φ 0 ≫
          (ChainComplex.isoHomologyι₀
            (simplicialReplacementComplex.{u, max u u' v} G')).hom) ≫
            (replacementOpcyclesZeroIsoColimit.{u, max u' v} G').hom := by
        rw [replacementHomologyZeroIsoColimit, Iso.trans_hom, Category.assoc]
    _ = (ChainComplex.isoHomologyι₀ (simplicialReplacementComplex.{u', max u u' v} G)).hom ≫
          (HomologicalComplex.opcyclesMap Φ 0 ≫
            (replacementOpcyclesZeroIsoColimit.{u, max u' v} G').hom) := by
        rw [hhom, Category.assoc]
    _ = (replacementHomologyZeroIsoColimit.{u', max u v} G).hom ≫ ψ := by
        rw [hop, replacementHomologyZeroIsoColimit, Iso.trans_hom, Category.assoc]

/-- **In degree zero the explicit chain map is the comparison of the two colimits**, read through
the identification of the degree-zero homology of a simplicial replacement with the colimit. -/
lemma replacementChainMap_homologyMap_zero (f : C' ⥤ C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) 0 ≫
        (replacementHomologyZeroIsoColimit.{u, max u' v} F).hom =
      (replacementHomologyZeroIsoColimit.{u', max u v} (f.op ⋙ F)).hom ≫ colimit.pre F f.op :=
  replacementHomologyZeroIsoColimit_naturality' _ _
    (replacementChainMap_f_zero_comp_augmentation f F)

/-! ### Degree zero for the canonical map -/

/-- `CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'` with the
augmentation spelled `CategoryTheory.ProjectiveResolution.aug0`, whose codomain is the resolved
object. -/
@[reassoc]
lemma pOpcycles_comp_fromLeftDerivedZero'_aug0 {A : Type*} [Category A] [Abelian A]
    {B : Type*} [Category B] [Abelian B] {X : A} (P : ProjectiveResolution X) (G : A ⥤ B)
    [G.Additive] :
    HomologicalComplex.pOpcycles
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) 0 ≫
      P.fromLeftDerivedZero' G = G.map (ProjectiveResolution.aug0 P) :=
  ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' P G

section Aux

variable [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]
  [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]

/-- The lift used to define the canonical map with identity coefficients is compatible with the
degree-zero augmentations, in the `CategoryTheory.ProjectiveResolution.aug0` spelling. -/
lemma lift'_f_zero_comp_aug0 (f : C' ⥤ C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    (ProjectiveResolution.lift' (𝟙 (f.op ⋙ F)) (ProjectiveResolution.of (f.op ⋙ F))
        ((presheafRestriction.{u, u', v} f).mapAugmentation
          (ProjectiveResolution.of F).π)).f 0 ≫
      (presheafRestriction.{u, u', v} f).map (ProjectiveResolution.aug0
        (ProjectiveResolution.of F)) =
      ProjectiveResolution.aug0 (ProjectiveResolution.of (f.op ⋙ F)) := by
  have h := ProjectiveResolution.lift'_commutes_zero
    (𝟙 ((presheafRestriction.{u, u', v} f).obj F))
    (ProjectiveResolution.of ((presheafRestriction.{u, u', v} f).obj F))
    (Functor.mapAugOf (presheafRestriction.{u, u', v} f) (ProjectiveResolution.of F))
  simp only [Functor.mapAugmentation_f_zero] at h
  exact h

/-- **In degree zero the canonical map on homology is the comparison of the two colimits**, read
through `CategoryTheory.Functor.fromLeftDerivedZero`. -/
lemma homologyMapAux_fromLeftDerivedZero (f : C' ⥤ C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ F)) 0 ≫
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).fromLeftDerivedZero.app F =
      (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).fromLeftDerivedZero.app (f.op ⋙ F) ≫
        colimit.pre F f.op := by
  rw [ProjectiveResolution.fromLeftDerivedZero_eq (ProjectiveResolution.of F) colim,
    ProjectiveResolution.fromLeftDerivedZero_eq (ProjectiveResolution.of (f.op ⋙ F)) colim]
  dsimp only [homologyMapAux, ProjectiveResolution.transferHomology]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  have hopc : HomologicalComplex.opcyclesMap
        ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (ProjectiveResolution.lift' (𝟙 (f.op ⋙ F)) (ProjectiveResolution.of (f.op ⋙ F))
              ((presheafRestriction.{u, u', v} f).mapAugmentation
                (ProjectiveResolution.of F).π)) ≫
          colimitRestrictionPreComplex.{u, u', v} f (ProjectiveResolution.of F).complex) 0 ≫
        (ProjectiveResolution.of F).fromLeftDerivedZero' colim =
      (ProjectiveResolution.of (f.op ⋙ F)).fromLeftDerivedZero' colim ≫ colimit.pre F f.op := by
    rw [← cancel_epi (HomologicalComplex.pOpcycles
        ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (ProjectiveResolution.of (f.op ⋙ F)).complex) 0),
      HomologicalComplex.p_opcyclesMap_assoc,
      pOpcycles_comp_fromLeftDerivedZero'_aug0,
      pOpcycles_comp_fromLeftDerivedZero'_aug0_assoc,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc,
      show (colimitRestrictionPreComplex.{u, u', v} f (ProjectiveResolution.of F).complex).f 0 =
        (colimitRestrictionPre.{u, u', v} f).app
          ((ProjectiveResolution.of F).complex.X 0) from rfl,
      ← (colimitRestrictionPre.{u, u', v} f).naturality
        (ProjectiveResolution.aug0 (ProjectiveResolution.of F)), Functor.comp_map,
      ← Functor.map_comp_assoc, lift'_f_zero_comp_aug0, colimitRestrictionPre_app]
  have hhom : HomologicalComplex.homologyMap
        ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (ProjectiveResolution.lift' (𝟙 (f.op ⋙ F)) (ProjectiveResolution.of (f.op ⋙ F))
              ((presheafRestriction.{u, u', v} f).mapAugmentation
                (ProjectiveResolution.of F).π)) ≫
          colimitRestrictionPreComplex.{u, u', v} f (ProjectiveResolution.of F).complex) 0 ≫
        (ChainComplex.isoHomologyι₀ ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (ProjectiveResolution.of F).complex)).hom =
      (ChainComplex.isoHomologyι₀ ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (ProjectiveResolution.of (f.op ⋙ F)).complex)).hom ≫
        HomologicalComplex.opcyclesMap
          ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).map
              (ProjectiveResolution.lift' (𝟙 (f.op ⋙ F)) (ProjectiveResolution.of (f.op ⋙ F))
                ((presheafRestriction.{u, u', v} f).mapAugmentation
                  (ProjectiveResolution.of F).π)) ≫
            colimitRestrictionPreComplex.{u, u', v} f (ProjectiveResolution.of F).complex) 0 := by
    rw [← cancel_epi (ChainComplex.isoHomologyι₀
        ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (ProjectiveResolution.of (f.op ⋙ F)).complex)).inv,
      Iso.inv_hom_id_assoc, ChainComplex.isoHomologyι₀_inv_naturality_assoc, Iso.inv_hom_id,
      Category.comp_id]
  have key : HomologicalComplex.homologyMap
        ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (ProjectiveResolution.lift' (𝟙 (f.op ⋙ F)) (ProjectiveResolution.of (f.op ⋙ F))
              ((presheafRestriction.{u, u', v} f).mapAugmentation
                (ProjectiveResolution.of F).π)) ≫
          colimitRestrictionPreComplex.{u, u', v} f (ProjectiveResolution.of F).complex) 0 ≫
        (ChainComplex.isoHomologyι₀ ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (ProjectiveResolution.of F).complex)).hom ≫
          (ProjectiveResolution.of F).fromLeftDerivedZero' colim =
      ((ChainComplex.isoHomologyι₀ ((colim.mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (ProjectiveResolution.of (f.op ⋙ F)).complex)).hom ≫
          (ProjectiveResolution.of (f.op ⋙ F)).fromLeftDerivedZero' colim) ≫
        colimit.pre F f.op := by
    rw [reassoc_of% hhom, hopc, Category.assoc]
  exact key

end Aux

/-! ### The index half -/

/-- The 08PG comparison is the degree-`n` component of the isomorphism of δ-functors it is
defined from. -/
lemma categoryHomologyReplacementIso_hom_eq {D : Type u} [SmallCategory D]
    (F : Dᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    (categoryHomologyReplacementIso.{u, v} F n).hom =
      ((derivedColimitReplacementDeltaIso.{u, v} (C := D)).hom.app n).app F :=
  rfl

section Index

variable [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]
  [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]

/-- **The identification of Stacks 08PH in degree zero.** Both sides are the comparison of the
two colimits, by `homologyMapAux_fromLeftDerivedZero` and
`replacementChainMap_homologyMap_zero`. -/
lemma homologyMapAux_homologyMap_zero (f : C' ⥤ C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ F)) 0 ≫
        (categoryHomologyReplacementIso.{u, max u' v} F 0).hom =
      (categoryHomologyReplacementIso.{u', max u v} (f.op ⋙ F) 0).hom ≫
        HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) 0 := by
  have hinv : (replacementHomologyZeroIsoColimit.{u', max u v} (f.op ⋙ F)).inv ≫
      HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) 0 =
      colimit.pre F f.op ≫ (replacementHomologyZeroIsoColimit.{u, max u' v} F).inv := by
    rw [← cancel_epi (replacementHomologyZeroIsoColimit.{u', max u v} (f.op ⋙ F)).hom,
      Iso.hom_inv_id_assoc, ← reassoc_of% replacementChainMap_homologyMap_zero f F,
      Iso.hom_inv_id, Category.comp_id]
  rw [categoryHomologyReplacementIso_zero.{u, max u' v},
    categoryHomologyReplacementIso_zero.{u', max u v}]
  simp only [Category.assoc]
  rw [reassoc_of% homologyMapAux_fromLeftDerivedZero f F, hinv]

/-- **The two morphisms of δ-functors agree.** The explicit chain map composed with the 08PG
comparison over `C'`, and the canonical map on homology composed with the 08PG comparison over
`C`, are the same morphism of homological δ-functors, because
`Stacks.CategoryHomology.replacementHomologyDeltaFunctor` is universal and their degree-zero
components agree. -/
theorem replacementChainMapDeltaHom_comp_eq (f : C' ⥤ C) :
    HomologicalDeltaFunctor.Hom.precomp (presheafRestriction.{u, u', v} f)
        (derivedColimitReplacementDeltaIso.{u', max u v} (C := C')).hom ≫
      replacementChainMapDeltaHom.{u, u', v} f =
    homologyMapAuxDeltaHom.{u, u', v} f ≫
      (derivedColimitReplacementDeltaIso.{u, max u' v} (C := C)).hom := by
  have := replacementHomologyDeltaFunctor_isUniversal.{u, max u' v} (C := C)
  refine HomologicalDeltaFunctor.IsUniversal.hom_ext_zero ?_
  refine NatTrans.ext (funext fun F => ?_)
  simp only [HomologicalDeltaFunctor.comp_app, HomologicalDeltaFunctor.Hom.precomp_app]
  refine (NatTrans.comp_app _ _ F).trans ?_
  refine Eq.trans ?_ (NatTrans.comp_app _ _ F).symm
  rw [Functor.whiskerLeft_app, replacementChainMapDeltaHom_app, homologyMapAuxDeltaHom_app,
    ← categoryHomologyReplacementIso_hom_eq.{u, max u' v},
    ← categoryHomologyReplacementIso_hom_eq.{u', max u v}]
  exact (homologyMapAux_homologyMap_zero f F).symm

/-- **The index half of Stacks 08PH.** With the coefficient morphism the identity, the explicit
chain map induces the canonical map on homology, in every degree. -/
theorem homologyMapAux_homologyMap (f : C' ⥤ C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v})
    (n : ℕ) :
    (categoryHomologyReplacementIso.{u', max u v} (f.op ⋙ F) n).hom ≫
        HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) n =
      homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ F)) n ≫
        (categoryHomologyReplacementIso.{u, max u' v} F n).hom := by
  have h := NatTrans.congr_app
    (congrArg (fun α => HomologicalDeltaFunctor.Hom.app α n)
      (replacementChainMapDeltaHom_comp_eq.{u, u', v} f)) F
  simp only [HomologicalDeltaFunctor.comp_app, HomologicalDeltaFunctor.Hom.precomp_app] at h
  have e₁ := NatTrans.comp_app (Functor.whiskerLeft (presheafRestriction.{u, u', v} f)
      ((derivedColimitReplacementDeltaIso.{u', max u v} (C := C')).hom.app n))
    ((replacementChainMapDeltaHom.{u, u', v} f).app n) F
  have e₂ := NatTrans.comp_app ((homologyMapAuxDeltaHom.{u, u', v} f).app n)
    ((derivedColimitReplacementDeltaIso.{u, max u' v} (C := C)).hom.app n) F
  have h₂ := e₁.symm.trans (h.trans e₂)
  rw [Functor.whiskerLeft_app, replacementChainMapDeltaHom_app,
    homologyMapAuxDeltaHom_app] at h₂
  rw [categoryHomologyReplacementIso_hom_eq.{u, max u' v},
    categoryHomologyReplacementIso_hom_eq.{u', max u v}]
  exact h₂

/-! ### The coefficient half -/

/-- **The canonical map on homology factors through the identity coefficient morphism**: change
the coefficients over `C'` first, then apply the canonical map with identity coefficients. Both
sides are computed by `Stacks.CategoryHomology.homologyMapAux_eq` from the composite of the two
lifts. -/
lemma homologyMapAux_eq_comp (f : C' ⥤ C) {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} (t : F' ⟶ f.op ⋙ F) (n : ℕ) :
    homologyMapAux.{u, u', v} f t n =
      ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerived n).map t ≫
        homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ F)) n := by
  have hφ : (ProjectiveResolution.lift t (ProjectiveResolution.of F')
          (ProjectiveResolution.of (f.op ⋙ F)) ≫
        Functor.leftDerivedCompLift (presheafRestriction.{u, u', v} f)
          (ProjectiveResolution.of F) (ProjectiveResolution.of (f.op ⋙ F))) ≫
      (presheafRestriction.{u, u', v} f).mapAugmentation (ProjectiveResolution.of F).π =
      (ProjectiveResolution.of F').π ≫ (ChainComplex.single₀ _).map t := by
    rw [Category.assoc, ProjectiveResolution.lift'_commutes, CategoryTheory.Functor.map_id,
      Category.comp_id, ProjectiveResolution.lift_commutes]
  rw [homologyMapAux_eq f t n _ hφ,
    Functor.leftDerived_map_eq colim n t (P := ProjectiveResolution.of F')
      (Q := ProjectiveResolution.of (f.op ⋙ F)) (ProjectiveResolution.lift t _ _)
      (ProjectiveResolution.lift_commutes _ _ _)]
  dsimp only [homologyMapAux, ProjectiveResolution.transferHomology]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_comp_assoc]
  rfl

end Index

/-- **The explicit chain map factors through the identity coefficient morphism**, degreewise on
summands. -/
lemma replacementGroupMapOfFunctor_eq_comp (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) (n : ℕ) :
    replacementGroupMapOfFunctor f t n =
      replacementGroupMap t n ≫ replacementGroupMapOfFunctor f (𝟙 (f.op ⋙ F)) n := by
  refine replacementGroup_hom_ext n fun x s => ?_
  rw [AddCommGrpCat.comp_apply, replacementGroupMap_on_summand,
    replacementGroupMap_summand.{u', max u v}, replacementGroupMap_on_summand]
  rfl

/-- **The explicit chain map factors through the identity coefficient morphism.** -/
lemma replacementChainMap_eq_comp (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) :
    replacementChainMap f t =
      (replacementComplexFunctor (C := C')).map t ≫ replacementChainMap f (𝟙 (f.op ⋙ F)) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine Eq.trans ?_ (HomologicalComplex.comp_f _ _ n).symm
  rw [replacementChainMap_degreewise, replacementComplexFunctor_map_f,
    replacementChainMap_degreewise]
  exact replacementGroupMapOfFunctor_eq_comp f t n

/-! ### Stacks 08PH -/

/-- **Stacks 08PH, the identification of the homology map.** Under the comparison of Stacks 08PG
between the homology of a category and the homology of its simplicial replacement, the explicit
chain map `K_•(F') ⟶ K_•(F)` induced by a functor `f : C' ⥤ C` and a morphism `t : F' ⟶ f⁻¹F`
induces the canonical map `Stacks.CategoryHomology.categoryHomologyMap`.

The coefficient half is the naturality of the 08PG comparison; the index half is
`homologyMapAux_homologyMap`, which rests on the canonical map being a morphism of homological
δ-functors. -/
@[stacks 08PH "the displayed chain map on homology"]
theorem replacementChainMap_homologyMap (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) (n : ℕ) :
    (categoryHomologyReplacementIso.{u', max u v} F' n).hom ≫
        HomologicalComplex.homologyMap (replacementChainMap f t) n =
      categoryHomologyMap f t n ≫ (categoryHomologyReplacementIso.{u, max u' v} F n).hom := by
  have := presheafEnoughProjectives.{u, max u' v} C
  have := presheafEnoughProjectives.{u', max u v} C'
  have hcm : HomologicalComplex.homologyMap (replacementChainMap f t) n =
      HomologicalComplex.homologyMap ((replacementComplexFunctor (C := C')).map t) n ≫
        HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) n := by
    rw [replacementChainMap_eq_comp f t]
    exact HomologicalComplex.homologyMap_comp _ _ n
  have step₁ : (categoryHomologyReplacementIso.{u', max u v} F' n).hom ≫
        HomologicalComplex.homologyMap (replacementChainMap f t) n =
      ((categoryHomologyReplacementIso.{u', max u v} F' n).hom ≫
          HomologicalComplex.homologyMap ((replacementComplexFunctor (C := C')).map t) n) ≫
        HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) n :=
    (congrArg (fun m => (categoryHomologyReplacementIso.{u', max u v} F' n).hom ≫ m) hcm).trans
      (Category.assoc _ _ _).symm
  have step₂ : ((categoryHomologyReplacementIso.{u', max u v} F' n).hom ≫
          HomologicalComplex.homologyMap ((replacementComplexFunctor (C := C')).map t) n) ≫
        HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) n =
      (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerived n).map t ≫
          (categoryHomologyReplacementIso.{u', max u v} (f.op ⋙ F) n).hom) ≫
        HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) n :=
    congrArg (fun m => m ≫
        HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) n)
      (categoryHomologyReplacementIso_naturality.{u', max u v} t n).symm
  have step₃ : (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerived n).map t ≫
          (categoryHomologyReplacementIso.{u', max u v} (f.op ⋙ F) n).hom) ≫
        HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) n =
      ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerived n).map t ≫
        homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ F)) n ≫
          (categoryHomologyReplacementIso.{u, max u' v} F n).hom :=
    (Category.assoc _ _ _).trans
      (congrArg
        (fun m => ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerived n).map t ≫ m)
        (homologyMapAux_homologyMap.{u, u', v} f F n))
  have step₄ : ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerived n).map t ≫
        homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ F)) n ≫
          (categoryHomologyReplacementIso.{u, max u' v} F n).hom =
      homologyMapAux.{u, u', v} f t n ≫
        (categoryHomologyReplacementIso.{u, max u' v} F n).hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun m => m ≫ (categoryHomologyReplacementIso.{u, max u' v} F n).hom)
        (homologyMapAux_eq_comp f t n).symm)
  rw [show categoryHomologyMap f t n = homologyMapAux.{u, u', v} f t n from rfl]
  exact ((step₁.trans step₂).trans step₃).trans step₄

/-- **Stacks 08PH.** Naturally isomorphic indexing functors with coefficient morphisms matching
under the induced reindexing give the same map on the homology of the simplicial replacement
complexes. This follows from the identification of the homology map together with
`Stacks.CategoryHomology.categoryHomologyMap_iso`, the 08PG comparison being an isomorphism. -/
theorem replacementChainMap_homologyMap_iso (f g : C' ⥤ C) (e : f ≅ g)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) (s : F' ⟶ g.op ⋙ F)
    (h : t = s ≫ Functor.whiskerRight (NatTrans.op e.hom) F) (n : ℕ) :
    HomologicalComplex.homologyMap (replacementChainMap f t) n =
      HomologicalComplex.homologyMap (replacementChainMap g s) n := by
  refine (cancel_epi (categoryHomologyReplacementIso.{u', max u v} F' n).hom).mp ?_
  rw [replacementChainMap_homologyMap, replacementChainMap_homologyMap,
    categoryHomologyMap_iso f g e t s h]

end Stacks.CategoryHomology

end
