module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquarePasting
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCoverTowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImageCompositionIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiCellCompositionProof
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SingleRightDerivedUnitFunctorNaturality

/-!
# The composition functoriality of the *derived* comparison map of [Stacks, Tag 07Q9]

`SmallSite/CrisZariskiCellCompositionProof.lean` proves the composition functoriality of the
**underived** comparison map, `...SmallSite.zariskiComparison_comp'`.  **This module proves the
derived one**, `...SmallSite.derivedZariskiComparison_comp'`, with no hypotheses.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `derivedCrisUnit_comp_eq` — **the derived unit of a composite is the composite of the derived
  units**, the derived mirror of `...SmallSite.crisUnit_comp_eq`.
* `derivedZariskiSquare_comp` — **the three derived squares of topoi are coherent under
  composition**, the derived mirror of
  `...SmallSite.crisZariskiSquare_hom_app_comp_of_cellComp` with its coherence argument supplied
  by `...SmallSite.crisZariskiCellComp`.
* `derivedZariskiComparison_comp'` — **the composition functoriality of the comparison map of
  [Stacks, Tag 07Q9] in `D⁺(Ab(X_Zar))`**, with no hypotheses.
* `annihilation07Q9_derivedZariskiComparison_comp` — **the tower step of [Stacks, Tag 07Q9] in
  its own vocabulary**: the annihilators of `...SmallSite.Annihilation07Q9` multiply along a
  composition of covers, the identification of the composite's comparison map being discharged
  by the previous item.

The three auxiliary identifications
`rightDerivedFunctorPlusIsoOfCompIso_eq`, `derivedCrisDirectImageCompIso_eq` and
`derivedZariskiPushforwardComp_eq` say that the two composition isomorphisms this library
builds with `Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso` are the ones
`Stacks.DerivedFunctor.derivedSquare_paste` is phrased with.

## How they are proved

* `derivedZariskiSquare_comp` is an **instantiation** of the abstract
  `Stacks.DerivedFunctor.derivedSquare_paste_app` at `a₁, a₂, a₀ := f₁_{cris, *}, f₂_{cris, *},
  (f₁ ≫ f₂)_{cris, *}`, `v₂, v₁, v₀ := u_{X₂/S₂, *}, u_{X₁/S₁, *}, u_{X₀/S₀, *}` and
  `b₁, b₂, b₀ := f₁_{Zar, *}, f₂_{Zar, *}, (f₁ ≫ f₂)_{Zar, *}`.  Its underived hypothesis is
  `...SmallSite.crisZariskiSquare_hom_app_comp_of_cellComp` on the nose.
* `derivedCrisUnit_comp_eq` is the underived `...SmallSite.crisUnit_comp_eq` placed in degree
  zero, read through three properties of the canonical map
  `Stacks.Cohomology.singleRightDerivedUnit`: its naturality in the sheaf, its naturality in the
  functor being derived (`Stacks.Cohomology.singleRightDerivedUnit_natIso_inv_app`) and its
  compatibility with composition of the functors being derived
  (`Stacks.Cohomology.singleRightDerivedUnit_comp_app`).
* `derivedZariskiComparison_comp'` follows from the two exactly as the underived
  `...SmallSite.zariskiComparison_comp'` follows from `crisUnit_comp_eq` and
  `crisZariskiSquare_hom_app_comp_of_cellComp`.

## Scope
**No `@[stacks]` attribute is placed, and nothing here is a clause of [Stacks, Tag 07Q9]**, which
is `...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of
`SmallSite/AlphaPCover07Q9Main.lean`.  Its *local* step — over an open where `f` is a chain of
`α_p`-extensions the cone is annihilated by the degree — comes from [Stacks, Proposition 07LG]
(`...SmallSite.crystalPairDeRhamComplex_computesCohomology`) and [Stacks, Tag 07N1].  The tower
propagation is `...SmallSite.annihilation07Q9_chainComp`.

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M), when the composition comparison
  of right derived functors is an isomorphism
* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2), that comparison

Tags covered: none.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The two composition isomorphisms, in the shape the pasting is phrased with -/

section Abstract

variable {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]

omit [HasDerivedCategory D] [EnoughInjectives D] in
/-- **The transport of right derivation along an isomorphism `F ⋙ G ≅ H` of underived functors
is the invariance comparison of that isomorphism.**  `Stacks.EtaleCohomology`'s
`rightDerivedFunctorPlusIsoOfCompIso` inserts the coherence isomorphism identifying the functor
induced on `K⁺` by `F ⋙ G` with the composite of the induced functors, and that coherence is the
identity (`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app`), so the two
agree.  Both are descended from the same universal property, so they agree as soon as they agree
after the derived-functor unit. -/
theorem rightDerivedFunctorPlusIsoOfCompIso_eq (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e =
      Functor.rightDerivedFunctorPlusNatIso e := by
  refine Iso.ext (Functor.rightDerived_ext (F ⋙ G).rightDerivedFunctorPlus
    (F ⋙ G).rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) _ _ _
    (NatTrans.ext (funext fun K ↦ ?_)))
  have h1 : (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
      (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e).hom.app
        (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((Stacks.EtaleCohomology.mapHomotopyCategoryPlusIsoOfCompIso F G H e).hom.app K) ≫
        H.rightDerivedFunctorPlusUnit.app K :=
    Functor.rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctorPlus
      H.rightDerivedFunctorPlus (F ⋙ G).rightDerivedFunctorPlusUnit
      H.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C)
      (Functor.isoWhiskerRight
        (Stacks.EtaleCohomology.mapHomotopyCategoryPlusIsoOfCompIso F G H e)
        DerivedCategory.Plus.Qh).hom K
  have h2 : (Stacks.EtaleCohomology.mapHomotopyCategoryPlusIsoOfCompIso F G H e).hom.app K =
      (Functor.mapHomotopyCategoryPlusNatIso e).hom.app K :=
    (CategoryTheory.eq_whisker
        (Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app F G K)
        ((Functor.mapHomotopyCategoryPlusNatIso e).hom.app K)).trans
      (Category.id_comp _)
  exact (h1.trans (CategoryTheory.eq_whisker
        (congrArg DerivedCategory.Plus.Qh.map h2)
        (H.rightDerivedFunctorPlusUnit.app K))).trans
    (Functor.rightDerivedFunctorPlusNatIso_hom_fac_app e K).symm

omit [Abelian E] [HasDerivedCategory E] in
/-- A commuting triangle solved for the inverse of its invertible edge. -/
private lemma eq_comp_inv_of_comp_eq {X Y Z : E} (f : X ⟶ Y) (α : Y ≅ Z) (g : X ⟶ Z)
    (h : f ≫ α.hom = g) : f = g ≫ α.inv := by
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Abstract

section Composition

variable {S₂ S₁ S₀ : GlobalCrystallineSituation.{u}}
  {f₁S : S₂.S ⟶ S₁.S} {f₁X : S₂.X ⟶ S₁.X}
  {f₂S : S₁.S ⟶ S₀.S} {f₂X : S₁.X ⟶ S₀.X}
  (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁S = f₁X ≫ S₁.toClosedFiber)
  (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂S = f₂X ≫ S₀.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S₁) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₂) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₁) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory.{w'} (Sheaf (opensTopology S₂) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₁) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})] in
/-- **`...SmallSite.derivedCrisDirectImageCompIso` is the invariance comparison of
`crisDirectImageComp` followed by the composition comparison of [Stacks, Tag 05T2].**  This is
`rightDerivedFunctorPlusIsoOfCompIso_eq` applied to the isomorphism
`f₁_{cris, *} ∘ f₂_{cris, *} ≅ (f₁ ≫ f₂)_{cris, *}` the derived composition isomorphism is built
from. -/
theorem derivedCrisDirectImageCompIso_eq :
    derivedCrisDirectImageCompIso h₁ h₂ =
      Functor.rightDerivedFunctorPlusNatIso (crisDirectImageComp h₁ h₂) ≪≫
        Functor.rightDerivedFunctorPlusCompIso (crisDirectImage S₂ S₁ f₁S f₁X h₁)
          (crisDirectImage S₁ S₀ f₂S f₂X h₂) := by
  show (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso
        (crisDirectImage S₂ S₁ f₁S f₁X h₁) (crisDirectImage S₁ S₀ f₂S f₂X h₂)
        (crisDirectImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂))
        (crisDirectImageComp h₁ h₂).symm).symm ≪≫ _ = _
  rw [rightDerivedFunctorPlusIsoOfCompIso_eq,
    Functor.rightDerivedFunctorPlusNatIso_symm, Iso.symm_symm_eq]

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S₁) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1})] in
/-- **`...SmallSite.derivedZariskiPushforwardComp` is the invariance comparison of
`zariskiPushforwardComp` inverted, followed by the composition comparison of
[Stacks, Tag 05T2].** -/
theorem derivedZariskiPushforwardComp_eq :
    derivedZariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X) =
      (Functor.rightDerivedFunctorPlusNatIso
          (zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X))).symm ≪≫
        Functor.rightDerivedFunctorPlusCompIso (zariskiPushforward S₂ S₁ f₁X)
          (zariskiPushforward S₁ S₀ f₂X) := by
  show (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso
        (zariskiPushforward S₂ S₁ f₁X) (zariskiPushforward S₁ S₀ f₂X)
        (zariskiPushforward S₂ S₀ (f₁X ≫ f₂X))
        (zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X))).symm ≪≫ _ = _
  rw [rightDerivedFunctorPlusIsoOfCompIso_eq]

/-- **The three derived squares of topoi of [Stacks, Tag 07Q9] are coherent under
composition**, with no hypotheses: the derived commutation for `f₂`, then `Rf₂_{Zar, *}` of the
one for `f₁`, then the composition isomorphism of the derived Zariski direct images inverted, is
the composition isomorphism of the derived crystalline direct images inverted followed by the
derived commutation for `f₁ ≫ f₂`.

This is the derived mirror of `...SmallSite.crisZariskiSquare_hom_app_comp_of_cellComp`, and it
is an instantiation of the abstract `Stacks.DerivedFunctor.derivedSquare_paste_app` whose
underived hypothesis is that lemma fed with `...SmallSite.crisZariskiCellComp`. -/
theorem derivedZariskiSquare_comp
    (K : DerivedCategory.Plus (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1})) :
    (derivedZariskiSquare S₁ S₀ f₂S f₂X h₂
            (crisZariskiSquare S₁ S₀ f₂S f₂X h₂)).hom.app
          ((derivedCrisDirectImageFunctor S₂ S₁ f₁S f₁X h₁).obj K) ≫
        (derivedZariskiPushforwardFunctor S₁ S₀ f₂X).map
          ((derivedZariskiSquare S₂ S₁ f₁S f₁X h₁
            (crisZariskiSquare S₂ S₁ f₁S f₁X h₁)).hom.app K) ≫
        (derivedZariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).inv.app
          ((derivedZariskiDirectImageFunctor S₂).obj K) =
      (derivedZariskiDirectImageFunctor S₀).map
          ((derivedCrisDirectImageCompIso h₁ h₂).inv.app K) ≫
        (derivedZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂)
          (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
            (comp_closedFiber_compat h₁ h₂))).hom.app K :=
  Stacks.DerivedFunctor.derivedSquare_paste_app (crisDirectImageComp h₁ h₂)
    (zariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X))
    (crisZariskiSquare S₂ S₁ f₁S f₁X h₁) (crisZariskiSquare S₁ S₀ f₂S f₂X h₂)
    (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂))
    _ _ _ _ _ rfl rfl rfl (derivedCrisDirectImageCompIso_eq h₁ h₂)
    (derivedZariskiPushforwardComp_eq (f₁X := f₁X) (f₂X := f₂X))
    (crisZariskiSquare_hom_app_comp_of_cellComp h₁ h₂ (crisZariskiCellComp h₁ h₂)) K


/-! ### The derived unit of a composite -/

omit [HasDerivedCategory.{w'} (Sheaf (opensTopology S₂) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₁) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})] in
/-- **The derived unit of a composite cover is the composite of the derived units**: the derived
mirror of `...SmallSite.crisUnit_comp_eq`.

The unit `ℱ[0] ⟶ R(f₁ ≫ f₂)_{cris, *}ℱ'[0]` of the composite cover is the unit of `f₂`, followed
by `Rf₂_{cris, *}` of the unit of `f₁`, read through the composition comparison
`...SmallSite.crisInverseImageCompCell` of the crystalline inverse images and the composition
isomorphism `...SmallSite.derivedCrisDirectImageCompIso` of the derived direct images.

Three properties of `Stacks.Cohomology.singleRightDerivedUnit` do the work: its naturality in the
sheaf, its naturality in the functor being derived
(`Stacks.Cohomology.singleRightDerivedUnit_natIso_inv_app`) and its compatibility with
composition of the functors being derived
(`Stacks.Cohomology.singleRightDerivedUnit_comp_app`). -/
theorem derivedCrisUnit_comp_eq (F : Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1}) :
    derivedCrisUnit S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) F =
      (derivedCrisUnit S₁ S₀ f₂S f₂X h₂ F ≫
          (derivedCrisDirectImageFunctor S₁ S₀ f₂S f₂X h₂).map
            (derivedCrisUnit S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F))) ≫
        (derivedCrisDirectImageFunctor S₂ S₁ f₁S f₁X h₁ ⋙
              derivedCrisDirectImageFunctor S₁ S₀ f₂S f₂X h₂).map
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).map
                ((crisInverseImageCompCell h₁ h₂).app F)) ≫
          (derivedCrisDirectImageCompIso h₁ h₂).inv.app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).obj
                (crisPullback S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
                  (comp_closedFiber_compat h₁ h₂) F)) := by
  have hnat₂ := (Stacks.Cohomology.singleRightDerivedUnit
    (crisDirectImage S₁ S₀ f₂S f₂X h₂)).naturality
      (crisUnit S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F))
  have hnatΨ := (Stacks.Cohomology.singleRightDerivedUnit
    (crisDirectImage S₂ S₁ f₁S f₁X h₁ ⋙ crisDirectImage S₁ S₀ f₂S f₂X h₂)).naturality
      ((crisInverseImageCompCell h₁ h₂).app F)
  have hnatE := Stacks.Cohomology.singleRightDerivedUnit_natIso_inv_app
    (crisDirectImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂))
    (crisDirectImage S₂ S₁ f₁S f₁X h₁ ⋙ crisDirectImage S₁ S₀ f₂S f₂X h₂)
    (crisDirectImageComp h₁ h₂)
    (crisPullback S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) F)
  have hcompC := (Iso.eq_comp_inv
    ((Functor.rightDerivedFunctorPlusCompIso (crisDirectImage S₂ S₁ f₁S f₁X h₁)
      (crisDirectImage S₁ S₀ f₂S f₂X h₂)).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).obj
            (crisPullback S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F))))).2
    (Stacks.Cohomology.singleRightDerivedUnit_comp_app (crisDirectImage S₂ S₁ f₁S f₁X h₁)
      (crisDirectImage S₁ S₀ f₂S f₂X h₂)
      (crisPullback S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F)))
  have hcompnat := (Functor.rightDerivedFunctorPlusCompIso (crisDirectImage S₂ S₁ f₁S f₁X h₁)
    (crisDirectImage S₁ S₀ f₂S f₂X h₂)).inv.naturality
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).map
          ((crisInverseImageCompCell h₁ h₂).app F))
  simp only [Functor.comp_obj, Functor.comp_map, Iso.app_inv]
    at hnat₂ hnatΨ hnatE hcompC hcompnat
  simp only [derivedCrisUnit, derivedCrisDirectImageFunctor, crisUnit_comp_eq h₁ h₂ F,
    derivedCrisDirectImageCompIso_eq h₁ h₂, Iso.trans_inv, NatTrans.comp_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [hnatE, reassoc_of% hnatΨ, hcompC]
  simp only [Category.assoc]
  rw [← reassoc_of% hcompnat, reassoc_of% hnat₂]


/-! ### The composition functoriality of the derived comparison map -/

/-- **The composition functoriality of the comparison map of [Stacks, Tag 07Q9] in
`D⁺(Ab(X_Zar))`**, with no hypotheses.

The comparison map `Ru_{X₀/S₀, *}ℱ ⟶ R(f₁ ≫ f₂)_{Zar, *}Ru_{X₂/S₂, *}ℱ'` of the composite cover
is the comparison map of `f₂`, followed by `Rf₂_{Zar, *}` of the comparison map of `f₁`, read
through the composition isomorphism `...SmallSite.derivedZariskiPushforwardComp` of the derived
Zariski direct images and the composition comparison `...SmallSite.crisInverseImageCompCell` of
the crystalline inverse images.

This is the derived mirror of `...SmallSite.zariskiComparison_comp'`, and it is what lets the
tower reduction of [Stacks, Tag 07Q9] — `...SmallSite.annihilation07Q9_chainComp` — be pointed
at the comparison map of an iterated `α_p`-cover: it is the hypothesis `hfact` of
`...SmallSite.annihilation07Q9_derivedZariskiComparison_of_tower`.

Two inputs, both theorems of this library and both unconditional: `derivedCrisUnit_comp_eq`,
that the derived unit of a composite is the composite of the derived units, and
`derivedZariskiSquare_comp`, the coherence of the three derived squares of topoi. -/
theorem derivedZariskiComparison_comp' (F : Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1}) :
    derivedZariskiComparison S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂)
        (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
          (comp_closedFiber_compat h₁ h₂)) F =
      derivedZariskiComparison S₁ S₀ f₂S f₂X h₂ (crisZariskiSquare S₁ S₀ f₂S f₂X h₂) F ≫
        (derivedZariskiPushforwardFunctor S₁ S₀ f₂X).map
            (derivedZariskiComparison S₂ S₁ f₁S f₁X h₁ (crisZariskiSquare S₂ S₁ f₁S f₁X h₁)
              (crisPullback S₁ S₀ f₂S f₂X h₂ F)) ≫
          (derivedZariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).inv.app
            ((derivedZariskiDirectImageFunctor S₂).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).obj
                  (crisPullback S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F)))) ≫
          (derivedZariskiPushforwardFunctor S₂ S₀ (f₁X ≫ f₂X)).map
            ((derivedZariskiDirectImageFunctor S₂).map
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).map
                  ((crisInverseImageCompCell h₁ h₂).app F))) := by
  have hnat₂ := (derivedZariskiSquare S₁ S₀ f₂S f₂X h₂
    (crisZariskiSquare S₁ S₀ f₂S f₂X h₂)).hom.naturality
      (derivedCrisUnit S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F))
  have hnatf := (derivedZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
    (comp_closedFiber_compat h₁ h₂) (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
      (comp_closedFiber_compat h₁ h₂))).hom.naturality
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).map
          ((crisInverseImageCompCell h₁ h₂).app F))
  have hκ := (derivedCrisDirectImageCompIso h₁ h₂).inv.naturality
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).map
          ((crisInverseImageCompCell h₁ h₂).app F))
  have hsq := derivedZariskiSquare_comp h₁ h₂
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).obj
          (crisPullback S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F)))
  have hκU := congrArg (derivedZariskiDirectImageFunctor S₀).map hκ
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp] at hnat₂ hnatf hκU hsq
  simp only [derivedZariskiComparison, derivedZariskiDirectImage,
    derivedCrisUnit_comp_eq h₁ h₂ F, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rw [← reassoc_of% hnat₂, reassoc_of% hκU, reassoc_of% hsq, hnatf]


/-! ### The tower step of [Stacks, Tag 07Q9] -/

/-- `...SmallSite.annihilation07Q9_comp_isIso` with the invertibility an explicit argument, so
that it can be supplied by a term whose objects are spelled as the caller spells them rather than
found by instance search. -/
private theorem annihilation07Q9_comp_isIso_of (S : GlobalCrystallineSituation.{u})
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] (q : ℕ)
    {A B B' : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})}
    (α : A ⟶ B) (e : B ⟶ B') (he : IsIso e) (h : Annihilation07Q9 S q α) :
    Annihilation07Q9 S q (α ≫ e) :=
  have := he
  annihilation07Q9_comp_isIso S q α e h


/-- **One stage of the tower reduction of [Stacks, Tag 07Q9], in 07Q9's own vocabulary.**  If the
comparison map of `f₂` satisfies `...SmallSite.Annihilation07Q9` for `b`, and the comparison map
of `f₁` pushed down to `X₀` along `Rf₂_{Zar, *}` satisfies it for `a`, then the comparison map of
`f₁ ≫ f₂` satisfies it for `b * a`.

This is the source's "(This uses axiom TR4 for the triangulated category `D(X)`.)" for a single
composition, with the identification of the composite's comparison map discharged: the three
isomorphisms by which `derivedZariskiComparison_comp'` presents that composite are absorbed by
`...SmallSite.annihilation07Q9_comp_isIso`, and the annihilators multiply by
`...SmallSite.annihilation07Q9_comp`.  Nothing beyond the two stage hypotheses is carried, and
iterating it along `AlgebraicGeometry.IsAlphaPCoverComposite` — whose `comp` constructor is a
single composition — gives the exponent `p ^ n = q` of the source.

The per-stage hypotheses are where the mathematics of [Stacks, Tag 07Q9] lives: for an
`α_p`-cover they come from [Stacks, Proposition 60.21.3, Tag 07LG]
(`...SmallSite.crystalPairDeRhamComplex_computesCohomology`) together with
[Stacks, Lemma 60.25.1, Tag 07Q7] at `a = p` for the extension of [Stacks, Lemma 60.25.3,
Tag 07N1].  **No `@[stacks]` attribute is placed here**: this is an assembly step, not the tag,
which is `...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of
`SmallSite/AlphaPCover07Q9Main.lean` (proved over chain opens directly, not through this
lemma). -/
theorem annihilation07Q9_derivedZariskiComparison_comp (a b : ℕ)
    (F : Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1})
    (hβ : Annihilation07Q9 S₀ b
      (derivedZariskiComparison S₁ S₀ f₂S f₂X h₂ (crisZariskiSquare S₁ S₀ f₂S f₂X h₂) F))
    (hα : Annihilation07Q9 S₀ a
      ((derivedZariskiPushforwardFunctor S₁ S₀ f₂X).map
        (derivedZariskiComparison S₂ S₁ f₁S f₁X h₁ (crisZariskiSquare S₂ S₁ f₁S f₁X h₁)
          (crisPullback S₁ S₀ f₂S f₂X h₂ F)))) :
    Annihilation07Q9 S₀ (b * a)
      (derivedZariskiComparison S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂)
        (crisZariskiSquare S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
          (comp_closedFiber_compat h₁ h₂)) F) := by
  have hcell : IsIso ((crisInverseImageCompCell h₁ h₂).app F) := inferInstance
  have hpc : IsIso ((derivedZariskiPushforwardComp (f₁X := f₁X) (f₂X := f₂X)).inv.app
      ((derivedZariskiDirectImageFunctor S₂).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).obj
            (crisPullback S₂ S₁ f₁S f₁X h₁ (crisPullback S₁ S₀ f₂S f₂X h₂ F))))) :=
    inferInstance
  have hce : IsIso ((derivedZariskiPushforwardFunctor S₂ S₀ (f₁X ≫ f₂X)).map
      ((derivedZariskiDirectImageFunctor S₂).map
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) 0).map
            ((crisInverseImageCompCell h₁ h₂).app F)))) :=
    inferInstance
  rw [derivedZariskiComparison_comp' h₁ h₂ F]
  exact annihilation07Q9_comp S₀ b a _ _ hβ
    (annihilation07Q9_comp_isIso_of S₀ a _ _ (IsIso.comp_isIso' hpc hce) hα)

end Composition

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
