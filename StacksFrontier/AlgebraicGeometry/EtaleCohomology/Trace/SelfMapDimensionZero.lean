module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapTwistRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroBlocks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of an endomorphism over a separably closed field in dimension zero

Let `Ω` be a separably closed field, `f : W ⟶ Spec Ω` a finite étale morphism and `φ : W ⟶ W`
an endomorphism over `Ω`. Then `W` is the disjoint union of copies of `Spec Ω`, one for each
`Ω`-point, and `φ` permutes them. For a bounded below complex `C` on `Spec Ω` the action `φ^*`
on `RΓ(W, f^{-1} C)` of `Stacks.EtaleCohomology.selfMapCohomologyEndo` permutes the blocks
`Γ(ȳ, f^{-1} C)`, so its trace is the sum over the points `ȳ` fixed by `φ` of the traces of the
blocks there, and every such block is the identity.

This is the dimension zero case, for the twisted endomorphisms `(g^{-1} π)^*`, used in Step 9 of
the proof of [Stacks, Tag 03UG] (the source invokes Step 2 there).

All names are in the namespace `Stacks.EtaleCohomology`.

## Main definitions

* `pullbackTop`: the base change of the final object of the small étale site of `Spec Ω`, a final
  object of the small étale site of `W`.
* `selfMapSections`: the sections of `f^{-1} C` over an étale `W`-scheme, as a functor of `C`.
* `selfMapBlockRestriction`, `selfMapBlockInclusion`: the projections to, and inclusions of, the
  values on the `Ω`-points.
* `selfMapSectionsTwistEndo`: the endomorphism of the sections over the final object induced by a
  twist `f^{-1} ⟶ f^{-1} ⋙ φ_*`.

## Main results

* `perfectDerivedTrace_selfMapSectionsTwistEndo_eq_sum`: the trace of the twisted endomorphism is
  the sum of the traces of the blocks at the fixed points.
* `perfectDerivedTrace_selfMapCohomologyEndo_eq_sum_of_etale`: the trace of `φ^*` on
  `RΓ(W, f^{-1} C)` is the sum, over the `Ω`-points fixed by `φ`, of the traces of the self-map
  twist at those points.
* `selfMapPointTwist_selfMapTwist_app`: the self-map twist is the identity at a fixed point.
* `perfectDerivedTrace_selfMapCohomologyEndo_eq_card_smul`: the trace of `φ^*` on `RΓ(W, f^{-1} C)`
  is the number of `Ω`-points fixed by `φ` times the trace of the identity of the complex of
  sections of `C` over `Spec Ω`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 2 and 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize HasDerivedCategory.standard

/-! ### The blocks -/

section Blocks

variable (Λ : Type r) [Ring Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {W : Scheme.{u}}
  (f : W ⟶ Spec (.of Ω))

/-- The base change along `f` of the final object of the small étale site of `Spec Ω`. -/
abbrev pullbackTop : W.Etale :=
  (smallEtaleBaseChange f).obj (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))

/-- The morphism of an étale `W`-scheme to `pullbackTop`. -/
abbrev toPullbackTop (V : W.Etale) : V ⟶ pullbackTop f :=
  MorphismProperty.Over.homMk (pullback.lift (V.hom ≫ f) V.hom (Category.comp_id _))
    (pullback.lift_snd _ _ _)

omit [IsSepClosed Ω] in
/-- Every morphism to `pullbackTop` is the canonical one. -/
lemma eq_toPullbackTop {V : W.Etale} (m : V ⟶ pullbackTop f) : m = toPullbackTop f V := by
  have chase : ∀ {C : Type _} [Category C] {V P T S : C} (m : V ⟶ P) (fst : P ⟶ T)
      (snd : P ⟶ S) (g : S ⟶ T) (v : V ⟶ S) (_ : m ≫ snd = v) (_ : fst ≫ 𝟙 T = snd ≫ g),
      m ≫ fst = v ≫ g := by
    intro C _ V P T S m fst snd g v h1 h2
    rw [← h1, Category.assoc, ← h2, Category.comp_id]
  exact smallEtaleBaseChange_hom_ext _
    ((chase _ _ _ _ _ (smallEtaleBaseChange_w _ m) pullback.condition).trans
      (pullback.lift_fst _ _ _).symm)

/-- `pullbackTop` is a final object of the small étale site of `W`. -/
def isTerminalPullbackTop : IsTerminal (pullbackTop f) :=
  IsTerminal.ofUniqueHom (toPullbackTop f) (fun _ m => eq_toPullbackTop f m)

/-- The sections of `f^{-1} C` over an étale `W`-scheme `V`, as a functor of the sheaf `C` on
`Spec Ω`. -/
abbrev selfMapSections (V : W.Etale) :
    EtaleModules.{u, r} Λ (Spec (.of Ω)) ⥤ ModuleCat.{max (u + 1) r} Λ :=
  etaleModuleInverseImage.{u, r} Λ f ⋙ sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
    (CategoryTheory.evaluation W.Etaleᵒᵖ (ModuleCat.{max (u + 1) r} Λ)).obj (op V)

/-- Restriction along a morphism of étale `W`-schemes, natural in the sheaf on `Spec Ω`. -/
abbrev selfMapSectionsMap {V V' : W.Etale} (g : V ⟶ V') :
    selfMapSections Λ f V' ⟶ selfMapSections Λ f V :=
  Functor.whiskerLeft _ (Functor.whiskerLeft _
    ((CategoryTheory.evaluation W.Etaleᵒᵖ (ModuleCat.{max (u + 1) r} Λ)).map g.op))

/-- The morphism from `pullbackTop` to the final object `W` of the small étale site. -/
abbrev pullbackTopToTop : pullbackTop f ⟶ Scheme.Etale.mk (𝟙 W) :=
  (isTerminalEtaleMkId W).from _

open scoped Classical in
/-- A finite `W` has finitely many `Ω`-points. -/
instance [IsFinite f] : Fintype (EtaleSections f) := Fintype.ofFinite _

variable [Etale f]

/-- Restriction from the sections over `pullbackTop` to the sections over the `Ω`-point `ȳ`. -/
abbrev selfMapBlockRestriction (y : EtaleSections f) :
    selfMapSections Λ f (pullbackTop f) ⟶ selfMapSections Λ f (etaleSectionObj f y) :=
  selfMapSectionsMap Λ f (toPullbackTop f _)

/-- Extension by zero from the sections over the `Ω`-point `ȳ` to the sections over
`pullbackTop`. -/
def selfMapBlockInclusion (y : EtaleSections f) :
    selfMapSections Λ f (etaleSectionObj f y) ⟶ selfMapSections Λ f (pullbackTop f) where
  app C := etaleSectionsInclusion Λ f ((etaleModuleInverseImage.{u, r} Λ f).obj C) y ≫
    ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj.map (pullbackTopToTop f).op
  naturality C C' φ := by
    have h₁ := etaleSectionsInclusion_naturality Λ f ((etaleModuleInverseImage.{u, r} Λ f).map φ) y
    have h₂ := ((etaleModuleInverseImage.{u, r} Λ f).map φ).hom.naturality (pullbackTopToTop f).op
    change ((etaleModuleInverseImage.{u, r} Λ f).map φ).hom.app _ ≫ _ ≫ _ =
      (_ ≫ _) ≫ ((etaleModuleInverseImage.{u, r} Λ f).map φ).hom.app _
    rw [Category.assoc, h₂, reassoc_of% h₁]

/-- The block inclusion at `ȳ` followed by the block restriction at `ȳ'` is the inclusion at `ȳ`
followed by restriction along `ȳ' ⟶ final`. -/
private lemma selfMapBlockInclusion_comp_selfMapBlockRestriction_app (y y' : EtaleSections f)
    (C : EtaleModules.{u, r} Λ (Spec (.of Ω))) :
    (selfMapBlockInclusion Λ f y ≫ selfMapBlockRestriction Λ f y').app C =
      etaleSectionsInclusion Λ f ((etaleModuleInverseImage.{u, r} Λ f).obj C) y ≫
        ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj.map (etaleSectionToTop f y').op := by
  have h : toPullbackTop f (etaleSectionObj f y') ≫ pullbackTopToTop f = etaleSectionToTop f y' :=
    (isTerminalEtaleMkId _).hom_ext _ _
  change (etaleSectionsInclusion Λ f _ y ≫
      ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj.map (pullbackTopToTop f).op) ≫
      ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj.map
        (toPullbackTop f (etaleSectionObj f y')).op = _
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, h]

/-- The block inclusion at `ȳ` followed by the block restriction at `ȳ` is the identity. -/
@[reassoc (attr := simp)]
lemma selfMapBlockInclusion_comp_selfMapBlockRestriction_self (y : EtaleSections f) :
    selfMapBlockInclusion Λ f y ≫ selfMapBlockRestriction Λ f y = 𝟙 _ := by
  ext C : 2
  rw [selfMapBlockInclusion_comp_selfMapBlockRestriction_app]
  exact etaleSectionsInclusion_restrict_self Λ f _ y

/-- The block inclusion at `ȳ` followed by the block restriction at `ȳ' ≠ ȳ` vanishes. -/
@[reassoc]
lemma selfMapBlockInclusion_comp_selfMapBlockRestriction_of_ne {y y' : EtaleSections f}
    (hy : y ≠ y') : selfMapBlockInclusion Λ f y ≫ selfMapBlockRestriction Λ f y' = 0 := by
  ext C : 2
  rw [selfMapBlockInclusion_comp_selfMapBlockRestriction_app]
  exact etaleSectionsInclusion_restrict_of_ne Λ f _ hy

/-- **The blocks decompose the identity.** -/
lemma sum_selfMapBlockRestriction_comp_selfMapBlockInclusion [IsFinite f] :
    ∑ y, selfMapBlockRestriction Λ f y ≫ selfMapBlockInclusion Λ f y = 𝟙 _ := by
  ext C : 2
  set G := ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj
  have h₁ : ∀ y : EtaleSections f, toPullbackTop f (etaleSectionObj f y) =
      etaleSectionToTop f y ≫ toPullbackTop f _ := fun y => (eq_toPullbackTop f _).symm
  have h₂ : pullbackTopToTop f ≫ toPullbackTop f _ = 𝟙 _ :=
    (eq_toPullbackTop f _).trans (eq_toPullbackTop f _).symm
  have hsum := sum_etaleSections_restrict_inclusion Λ f ((etaleModuleInverseImage.{u, r} Λ f).obj C)
  rw [NatTrans.app_sum]
  change ∑ y, G.map (toPullbackTop f (etaleSectionObj f y)).op ≫
    (etaleSectionsInclusion Λ f _ y ≫ G.map (pullbackTopToTop f).op) = 𝟙 _
  simp_rw [h₁, op_comp, Functor.map_comp, Category.assoc, ← Preadditive.comp_sum,
    ← Category.assoc, ← Preadditive.sum_comp]
  change G.map (toPullbackTop f _).op ≫ (∑ y, G.map (etaleSectionToTop f y).op ≫
    etaleSectionsInclusion Λ f _ y) ≫ G.map (pullbackTopToTop f).op = 𝟙 _
  rw [hsum, Category.id_comp, ← Functor.map_comp, ← op_comp, h₂, op_id,
    CategoryTheory.Functor.map_id]

end Blocks

/-! ### The twisted endomorphism permutes the blocks -/

section Twist

variable (Λ : Type r) [Ring Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {W : Scheme.{u}}
  (f : W ⟶ Spec (.of Ω)) [Etale f] (φ : W ⟶ W) (w : φ ≫ f = f)
  (τ : etaleModuleInverseImage.{u, r} Λ f ⟶
    etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleDirectImage.{u, r} Λ φ)

/-- The comparison `T ⟶ φ^* T` for `T = pullbackTop`, from `f = φ ≫ f`. -/
abbrev pullbackTopSelfMap : pullbackTop f ⟶ (smallEtaleBaseChange φ).obj (pullbackTop f) :=
  (smallEtaleBaseChangeComp' φ f f w.symm).hom.app (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))

/-- The base change along `φ` of `pullbackTop` is again a final object. -/
def isTerminalSelfMapPullbackTop : IsTerminal ((smallEtaleBaseChange φ).obj (pullbackTop f)) :=
  (isTerminalPullbackTop f).ofIso
    ((smallEtaleBaseChangeComp' φ f f w.symm).app (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))

/-- **The endomorphism of the sections over `pullbackTop` induced by a twist** `τ`: the twist at
`pullbackTop`, followed by restriction along `pullbackTop ⟶ φ^* pullbackTop`. -/
def selfMapSectionsTwistEndo :
    selfMapSections Λ f (pullbackTop f) ⟶ selfMapSections Λ f (pullbackTop f) :=
  Functor.whiskerRight τ (sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
      (CategoryTheory.evaluation W.Etaleᵒᵖ (ModuleCat.{max (u + 1) r} Λ)).obj
        (op (pullbackTop f))) ≫
    selfMapSectionsMap Λ f (pullbackTopSelfMap f φ w)

/-- The `Ω`-point `ȳ ≫ φ`. -/
abbrev selfMapSection (y : EtaleSections f) : EtaleSections f :=
  ⟨y.1 ≫ φ, by rw [Category.assoc, w, y.2]⟩

/-- The morphism `ȳ ⟶ φ^* ȳ₂` of étale `W`-schemes attached to `ȳ₂ = ȳ ≫ φ`. -/
def selfMapSectionLift {y y₂ : EtaleSections f} (h : y₂.1 = y.1 ≫ φ) :
    etaleSectionObj f y ⟶ (smallEtaleBaseChange φ).obj (etaleSectionObj f y₂) :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 _) y.1 ((Category.id_comp _).trans h))
    (pullback.lift_snd _ _ _)

/-- The twist at the `Ω`-point `ȳ₂` followed by restriction along `ȳ ⟶ φ^* ȳ₂`. -/
def selfMapPointTwist {y y₂ : EtaleSections f} (h : y₂.1 = y.1 ≫ φ) :
    selfMapSections Λ f (etaleSectionObj f y₂) ⟶ selfMapSections Λ f (etaleSectionObj f y) :=
  Functor.whiskerRight τ (sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
      (CategoryTheory.evaluation W.Etaleᵒᵖ (ModuleCat.{max (u + 1) r} Λ)).obj
        (op (etaleSectionObj f y₂))) ≫
    selfMapSectionsMap Λ f (selfMapSectionLift f φ h)

/-- Restricting along `toPullbackTop` at `ȳ` after `pullbackTopSelfMap` is restricting along
`ȳ ⟶ φ^* ȳ₂` after `φ^*` of `toPullbackTop` at `ȳ₂`. -/
private lemma pullbackTopSelfMap_map_comp {Ω : Type u} [Field Ω] (f : W ⟶ Spec (.of Ω))
    [Etale f] (φ : W ⟶ W) (w : φ ≫ f = f) {y y₂ : EtaleSections f} (h : y₂.1 = y.1 ≫ φ)
    {D : Type*} [Category D] (G : W.Etaleᵒᵖ ⥤ D) :
    G.map (pullbackTopSelfMap f φ w).op ≫ G.map (toPullbackTop f (etaleSectionObj f y)).op =
      G.map ((smallEtaleBaseChange φ).map (toPullbackTop f (etaleSectionObj f y₂))).op ≫
        G.map (selfMapSectionLift f φ h).op := by
  have ht : toPullbackTop f (etaleSectionObj f y) ≫ pullbackTopSelfMap f φ w =
      selfMapSectionLift f φ h ≫
        (smallEtaleBaseChange φ).map (toPullbackTop f (etaleSectionObj f y₂)) :=
    (isTerminalSelfMapPullbackTop f φ w).hom_ext _ _
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ht]

omit [IsSepClosed Ω] in
/-- **The twisted endomorphism permutes the blocks**: followed by restriction to `ȳ`, it is
restriction to `ȳ₂ = ȳ ≫ φ` followed by the twist at `ȳ₂`. -/
lemma selfMapSectionsTwistEndo_comp_selfMapBlockRestriction {y y₂ : EtaleSections f}
    (h : y₂.1 = y.1 ≫ φ) :
    selfMapSectionsTwistEndo Λ f φ w τ ≫ selfMapBlockRestriction Λ f y =
      selfMapBlockRestriction Λ f y₂ ≫ selfMapPointTwist Λ f φ τ h := by
  ext C : 2
  set G := ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj
  set t := (τ.app C).hom
  have hτ := t.naturality (toPullbackTop f (etaleSectionObj f y₂)).op
  change (t.app _ ≫ G.map (pullbackTopSelfMap f φ w).op) ≫
      G.map (toPullbackTop f (etaleSectionObj f y)).op =
    G.map (toPullbackTop f (etaleSectionObj f y₂)).op ≫ t.app _ ≫
      G.map (selfMapSectionLift f φ h).op
  have hct := pullbackTopSelfMap_map_comp f φ w h G
  have chase : ∀ {D : Type _} [Category D] {A B C E F : D} (τT : A ⟶ B) (Gc : B ⟶ A)
      (Gt : A ⟶ C) (Gm : B ⟶ E) (Gl : E ⟶ C) (Gt₂ : A ⟶ F) (τY : F ⟶ E)
      (_ : Gc ≫ Gt = Gm ≫ Gl) (_ : Gt₂ ≫ τY = τT ≫ Gm), (τT ≫ Gc) ≫ Gt = Gt₂ ≫ τY ≫ Gl := by
    intro D _ A B C E F τT Gc Gt Gm Gl Gt₂ τY hct hτ
    rw [Category.assoc, hct, reassoc_of% hτ]
  exact chase _ _ _ _ _ _ _ hct hτ

/-- **The diagonal block at a point not fixed by `φ` vanishes.** -/
lemma selfMapBlockInclusion_comp_selfMapSectionsTwistEndo_comp_selfMapBlockRestriction_of_ne
    (y : EtaleSections f) (hy : y.1 ≫ φ ≠ y.1) :
    selfMapBlockInclusion Λ f y ≫ selfMapSectionsTwistEndo Λ f φ w τ ≫
      selfMapBlockRestriction Λ f y = 0 := by
  rw [selfMapSectionsTwistEndo_comp_selfMapBlockRestriction Λ f φ w τ
    (y₂ := selfMapSection f φ w y) rfl,
    selfMapBlockInclusion_comp_selfMapBlockRestriction_of_ne_assoc, zero_comp]
  exact fun h => hy (congrArg Subtype.val h).symm

/-- **The diagonal block at a point fixed by `φ` is the twist there.** -/
lemma selfMapBlockInclusion_comp_selfMapSectionsTwistEndo_comp_selfMapBlockRestriction_of_eq
    (y : EtaleSections f) (hy : y.1 = y.1 ≫ φ) :
    selfMapBlockInclusion Λ f y ≫ selfMapSectionsTwistEndo Λ f φ w τ ≫
      selfMapBlockRestriction Λ f y = selfMapPointTwist Λ f φ τ hy := by
  rw [selfMapSectionsTwistEndo_comp_selfMapBlockRestriction Λ f φ w τ hy,
    selfMapBlockInclusion_comp_selfMapBlockRestriction_self_assoc]

end Twist

/-! ### The trace -/

section Trace

open CategoryTheory.FilteredDerived

variable (Λ : Type r) [Ring Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {W : Scheme.{u}}
  (f : W ⟶ Spec (.of Ω)) [Etale f] [IsFinite f] (φ : W ⟶ W) (w : φ ≫ f = f)
  (τ : etaleModuleInverseImage.{u, r} Λ f ⟶
    etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleDirectImage.{u, r} Λ φ)

/-- The sections over an étale `W`-scheme form an additive functor. -/
instance (V : W.Etale) : (selfMapSections Λ f V).Additive := inferInstance

/-- The `Ω`-points of `W` fixed by `φ`. -/
abbrev SelfMapFixedSections : Type u := {y : EtaleSections f // y.1 = y.1 ≫ φ}

open scoped Classical in
/-- **The trace of the twisted endomorphism in dimension zero, block form.**  The trace of the
endomorphism of the sections of `f^{-1} C` over the final object induced by a twist is the sum,
over the `Ω`-points `ȳ` fixed by `φ`, of the traces of the twist at `ȳ`. -/
theorem perfectDerivedTrace_selfMapSectionsTwistEndo_eq_sum
    (C : CochainComplex (EtaleModules.{u, r} Λ (Spec (.of Ω))) ℤ)
    (hC : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((selfMapSections Λ f (pullbackTop f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)))
    (hP : ∀ y, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((selfMapSections Λ f (etaleSectionObj f y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C))) :
    perfectDerivedTrace Λ ⟨_, hC⟩ (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (selfMapSectionsTwistEndo Λ f φ w τ) _).app C)) =
      ∑ y : SelfMapFixedSections f φ, perfectDerivedTrace Λ ⟨_, hP y.1⟩
        (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (selfMapPointTwist Λ f φ τ y.2) _).app C)) := by
  rw [perfectDerivedTrace_mapHomologicalComplex_eq_sum
    (selfMapSections Λ f (pullbackTop f)) Finset.univ
    (fun y => selfMapSections Λ f (etaleSectionObj f y)) (selfMapBlockRestriction Λ f)
    (selfMapBlockInclusion Λ f) (sum_selfMapBlockRestriction_comp_selfMapBlockInclusion Λ f) _ C
    hC hP, ← Fintype.sum_subtype_add_sum_subtype (fun y : EtaleSections f => y.1 = y.1 ≫ φ)]
  rw [Fintype.sum_eq_zero (fun y : {y // ¬ _} => _) (fun y => ?_), add_zero]
  · refine Fintype.sum_congr _ _ fun y => ?_
    simp only
      [selfMapBlockInclusion_comp_selfMapSectionsTwistEndo_comp_selfMapBlockRestriction_of_eq
        Λ f φ w τ y.1 y.2]
  · rw [selfMapBlockInclusion_comp_selfMapSectionsTwistEndo_comp_selfMapBlockRestriction_of_ne
      Λ f φ w τ y.1 (fun h => y.2 h.symm)]
    convert perfectDerivedTrace_zero Λ _
    rw [← DerivedCategory.Q.map_zero]
    congr 1

end Trace

/-! ### The self-map twist: the derived endomorphism and the blocks -/

section SelfMap

open CategoryTheory.FilteredDerived

variable (Λ : Type r) [Ring Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {W : Scheme.{u}}
  (f : W ⟶ Spec (.of Ω)) [Etale f] (φ : W ⟶ W) (w : φ ≫ f = f)

/-- **Global sections over `Spec Ω` of `f_* f^{-1} C` are the sections of `f^{-1} C` over
`pullbackTop`**, naturally in `C`. -/
def selfMapSectionsIso :
    etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleDirectImage.{u, r} Λ f ⋙
        etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω)) ≅
      selfMapSections Λ f (pullbackTop f) :=
  Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleDirectImage.{u, r} Λ f)
    (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleMkId (Spec (.of Ω))))

omit [IsSepClosed Ω] [Etale f] in
/-- The termwise endomorphism of `Γ(Spec Ω, f_* f^{-1} C)` attached to the self-map twist is
the twisted endomorphism of the sections over `pullbackTop`. -/
lemma twistChainEndo_f_comp_selfMapSectionsIso_hom
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ (Spec (.of Ω)))) (n : ℤ) :
    (Functor.twistChainEndo (etaleModuleDirectImage.{u, r} Λ φ)
        (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω)))
        (selfMapDirectImageComp.{u, r} Λ f φ w)
        ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C)
        (selfMapComplexTwist.{u, r} Λ f φ w C)).hom.f n ≫
        (selfMapSectionsIso Λ f).hom.app (C.obj.X n) =
      (selfMapSectionsIso Λ f).hom.app (C.obj.X n) ≫
        (selfMapSectionsTwistEndo Λ f φ w (selfMapTwist.{u, r} Λ f φ w)).app (C.obj.X n) := by
  have h := (Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{max (u + 1) r} Λ)
    (isTerminalEtaleMkId (Spec (.of Ω)))).hom.naturality
      ((etaleModuleDirectImage.{u, r} Λ f).map ((selfMapTwist.{u, r} Λ f φ w).app (C.obj.X n)) ≫
        (selfMapDirectImageComp.{u, r} Λ f φ w).hom.app
          ((etaleModuleInverseImage.{u, r} Λ f).obj (C.obj.X n)))
  exact h

variable [IsFinite f]

/-- The direct image along a finite morphism preserves finite colimits. -/
instance : PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ f) :=
  ((exactFunctor_iff _).1 (etaleModuleDirectImage_exact_of_isIntegralHom Λ f)).2

/-- The complex `Γ(Spec Ω, f_* f^{-1} C)` is the complex of sections over `pullbackTop`. -/
abbrev selfMapSectionsComplexIso (C : CochainComplex.Plus (EtaleModules.{u, r} Λ (Spec (.of Ω)))) :
    DerivedCategory.Q.obj
        ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).mapCochainComplexPlus.obj
          ((etaleModuleDirectImage.{u, r} Λ f).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C))).obj ≅
      DerivedCategory.Q.obj (((selfMapSections Λ f (pullbackTop f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.obj) :=
  DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (selfMapSectionsIso Λ f) _).app C.obj)

open scoped Classical in
/-- **The trace of `φ^*` on `RΓ(W, f^{-1} C)` for `W` finite étale over `Ω`, block form**: the sum
over the `Ω`-points fixed by `φ` of the traces of the self-map twist at those points. -/
theorem perfectDerivedTrace_selfMapCohomologyEndo_eq_sum_of_etale
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ (Spec (.of Ω))))
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ f C)))
    (hP : ∀ y, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((selfMapSections Λ f (etaleSectionObj f y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.obj))) :
    perfectDerivedTrace Λ ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, r} Λ f φ w C)) =
      ∑ y : SelfMapFixedSections f φ, perfectDerivedTrace Λ ⟨_, hP y.1⟩
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (selfMapPointTwist Λ f φ (selfMapTwist.{u, r} Λ f φ w) y.2) _).app C.obj)) := by
  have hM := (Functor.isPerfect_twist_iff_of_exact (etaleModuleDirectImage.{u, r} Λ f)
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω)))
    ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C)).1 hperf
  have hC := StacksDraft.Perfect.isPerfect_of_iso (selfMapSectionsComplexIso Λ f C).symm hM
  rw [selfMapCohomologyEndo, Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_exact _ _ _ _ _ _
    hperf, ← perfectDerivedTrace_selfMapSectionsTwistEndo_eq_sum Λ f φ w _ C.obj hC hP]
  refine perfectDerivedTrace_congr Λ _ _ (selfMapSectionsComplexIso Λ f C) _ _ ?_
  refine (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map ?_).trans (DerivedCategory.Q.map_comp _ _))
  ext n : 1
  exact twistChainEndo_f_comp_selfMapSectionsIso_hom Λ f φ w C n

end SelfMap

/-! ### The self-map twist is the identity at a fixed point -/

section PointTwist

variable (Λ : Type r) [Ring Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {W : Scheme.{u}}
  (f : W ⟶ Spec (.of Ω)) [Etale f] (φ : W ⟶ W) (w : φ ≫ f = f)

/-- **Pulling back a section to an `Ω`-point**: a section of `C` over `Spec Ω` gives, by the unit
of `f^{-1} ⊣ f_*` and restriction, a section of `f^{-1} C` over the `Ω`-point `ȳ`. -/
def selfMapPointRestriction (y : EtaleSections f) :
    sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
        (CategoryTheory.evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{max (u + 1) r} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ⟶
      selfMapSections Λ f (etaleSectionObj f y) :=
  Functor.whiskerRight (etaleModuleInverseImageAdj.{u, r} Λ f).unit
      (sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
        (CategoryTheory.evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{max (u + 1) r} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))) ≫
    selfMapSectionsMap Λ f (toPullbackTop f (etaleSectionObj f y))

omit [IsSepClosed Ω] in
/-- `selfMapPointRestriction` at `C` is the unit of `f^{-1} ⊣ f_*` on the sections over `Spec Ω`
followed by restriction along `ȳ ⟶ pullbackTop`. -/
lemma selfMapPointRestriction_app (y : EtaleSections f) (C : EtaleModules.{u, r} Λ (Spec (.of Ω))) :
    (selfMapPointRestriction Λ f y).app C =
      ((etaleModuleInverseImageAdj.{u, r} Λ f).unit.app C).hom.app
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ≫
        ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj.map
          (toPullbackTop f (etaleSectionObj f y)).op :=
  rfl

private lemma pointChase {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ : D} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₂) (t : X₁ ⟶ X₄) (b' : X₄ ⟶ X₃) (s : X₄ ⟶ X₁)
    (hn : b ≫ c = t ≫ b') (hc : b' ≫ d = s ≫ b) (hs : a ≫ t ≫ s = a) :
    (a ≫ b) ≫ c ≫ d = a ≫ b := by
  rw [Category.assoc, reassoc_of% hn, hc, ← Category.assoc t, ← Category.assoc, ← Category.assoc,
    Category.assoc a, hs]

omit [IsSepClosed Ω] in
/-- **The self-map twist fixes pulled back sections**: at a point `ȳ` fixed by `φ`, the twist at
`ȳ` followed by restriction along `ȳ ⟶ φ^* ȳ` fixes the sections pulled back from `Spec Ω`. -/
lemma selfMapPointRestriction_comp_selfMapPointTwist {y : EtaleSections f} (hy : y.1 = y.1 ≫ φ) :
    selfMapPointRestriction Λ f y ≫ selfMapPointTwist Λ f φ (selfMapTwist.{u, r} Λ f φ w) hy =
      selfMapPointRestriction Λ f y := by
  ext C : 2
  set G := ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj
  set t := ((selfMapTwist.{u, r} Λ f φ w).app C).hom
  set U := op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
  have hstar : ((etaleModuleInverseImageAdj.{u, r} Λ f).unit.app C).hom.app U ≫
      t.app (op (pullbackTop f)) ≫ G.map (pullbackTopSelfMap f φ w).op =
        ((etaleModuleInverseImageAdj.{u, r} Λ f).unit.app C).hom.app U := by
    have h := congrArg (fun z => z ≫ (selfMapDirectImageComp.{u, r} Λ f φ w).hom.app
      ((etaleModuleInverseImage.{u, r} Λ f).obj C)) (unit_comp_map_selfMapTwist Λ f φ w C)
    simp only [Category.assoc, Iso.inv_hom_id_app] at h
    have h' := congrArg (fun z => z.hom.app U) h
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h'
    rw [etaleModuleDirectImageComp_hom_app_hom_app] at h'
    exact (Category.assoc _ _ _).symm.trans h'
  have hn := t.naturality (toPullbackTop f (etaleSectionObj f y)).op
  have hc := (pullbackTopSelfMap_map_comp f φ w hy G).symm
  exact pointChase _ _ _ _ _ _ _ hn hc hstar

/-- The `Ω`-point `ȳ ≫ f = 𝟙` of `Spec Ω`, as a morphism of étale `Spec Ω`-schemes to the final
object; it is an isomorphism. -/
abbrev selfMapPointBaseHom (y : EtaleSections f) :
    haveI : Etale (y.1 ≫ f) := by rw [y.2]; infer_instance
    Scheme.Etale.mk (y.1 ≫ f) ⟶ Scheme.Etale.mk (𝟙 (Spec (.of Ω))) :=
  haveI : Etale (y.1 ≫ f) := by rw [y.2]; infer_instance
  MorphismProperty.Over.homMk (y.1 ≫ f) (Category.comp_id _)

/-- `selfMapPointBaseHom` is an isomorphism. -/
instance (y : EtaleSections f) : IsIso (selfMapPointBaseHom f y) := by
  have : Etale (y.1 ≫ f) := by rw [y.2]; infer_instance
  refine ⟨⟨MorphismProperty.Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ (y.1 ≫ f) = 𝟙 _
    rw [y.2, Category.comp_id]), ?_, ?_⟩⟩
  · apply MorphismProperty.Over.Hom.ext
    change (y.1 ≫ f) ≫ 𝟙 _ = 𝟙 _
    rw [y.2, Category.comp_id]
  · apply MorphismProperty.Over.Hom.ext
    change 𝟙 _ ≫ (y.1 ≫ f) = 𝟙 _
    rw [y.2, Category.comp_id]

private lemma germChase {D : Type*} [Category D] {X₀ X₀' X₁ X₂ X₄ X₅ : D} (r : X₀ ⟶ X₄)
    (a : X₀ ⟶ X₀') (g : X₀' ⟶ X₁) (g' : X₀ ⟶ X₁) (p : X₁ ⟶ X₂) (s : X₂ ⟶ X₄) (u : X₀ ⟶ X₅)
    (g'' : X₅ ⟶ X₂) (m : X₅ ⟶ X₄) (hr : r = u ≫ m) (h1 : a ≫ g = g') (hb : g' ≫ p = u ≫ g'')
    (hc : g'' ≫ s = m) : r = a ≫ g ≫ p ≫ s := by
  rw [hr, ← hc, ← reassoc_of% hb, ← reassoc_of% h1]

/-- **Pulling back sections to an `Ω`-point is the composite of the stalk identifications**:
`C(Spec Ω) ≅ C_{ȳ ≫ f} ≅ (f^{-1} C)_ȳ ≅ (f^{-1} C)(ȳ)`. -/
lemma selfMapPointRestriction_app_eq (y : EtaleSections f)
    (C : EtaleModules.{u, r} Λ (Spec (.of Ω))) :
    haveI : Etale (y.1 ≫ f) := by rw [y.2]; infer_instance
    haveI : Etale y.1 := etale_of_section f y.1 y.2
    (selfMapPointRestriction Λ f y).app C =
      C.obj.map (selfMapPointBaseHom f y).op ≫
        (presheafFiberSelfIso (y.1 ≫ f) (ModuleCat.{max (u + 1) r} Λ)).hom.app C.obj ≫
        (etaleModuleStalkPullbackIso Λ f y.1).inv.app C ≫
        (presheafFiberSelfIso y.1 (ModuleCat.{max (u + 1) r} Λ)).inv.app
          ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj := by
  have : Etale (y.1 ≫ f) := by rw [y.2]; infer_instance
  have : Etale y.1 := etale_of_section f y.1 y.2
  have h1 := (pointSmallEtale (y.1 ≫ f)).toPresheafFiber_w (selfMapPointBaseHom f y)
    (pointSmallEtaleSelfElement (y.1 ≫ f)) C.obj
  have hb := toPresheafFiber_comp_etaleModuleStalkPullbackIso_inv Λ f y.1 C
    (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
    ((pointSmallEtale (y.1 ≫ f)).fiber.map (selfMapPointBaseHom f y)
      (pointSmallEtaleSelfElement (y.1 ≫ f)))
  have hc := toPresheafFiber_comp_presheafFiberSelfIso_inv y.1 (ModuleCat.{max (u + 1) r} Λ)
    ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj _
    ((pointSmallEtaleComapFiberIso f y.1).hom.app (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      ((pointSmallEtale (y.1 ≫ f)).fiber.map (selfMapPointBaseHom f y)
        (pointSmallEtaleSelfElement (y.1 ≫ f))))
  have hm : toPullbackTop f (etaleSectionObj f y) = pointSmallEtaleSelfHom y.1
      ((pointSmallEtaleComapFiberIso f y.1).hom.app (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        ((pointSmallEtale (y.1 ≫ f)).fiber.map (selfMapPointBaseHom f y)
          (pointSmallEtaleSelfElement (y.1 ≫ f)))) := (eq_toPullbackTop f _).symm
  have hr := selfMapPointRestriction_app Λ f y C
  rw [hm] at hr
  exact germChase _ _ _ _ _ _ _ _ _ hr h1 hb hc

/-- Pulling back a section of `C` over `Spec Ω` to an `Ω`-point is an isomorphism. -/
lemma isIso_selfMapPointRestriction_app (y : EtaleSections f)
    (C : EtaleModules.{u, r} Λ (Spec (.of Ω))) : IsIso ((selfMapPointRestriction Λ f y).app C) := by
  have : Etale (y.1 ≫ f) := by rw [y.2]; infer_instance
  have : Etale y.1 := etale_of_section f y.1 y.2
  rw [selfMapPointRestriction_app_eq]
  exact (asIso (C.obj.map (selfMapPointBaseHom f y).op) ≪≫
    (presheafFiberSelfIso (y.1 ≫ f) (ModuleCat.{max (u + 1) r} Λ)).app C.obj ≪≫
    ((etaleModuleStalkPullbackIso Λ f y.1).app C).symm ≪≫
    ((presheafFiberSelfIso y.1 (ModuleCat.{max (u + 1) r} Λ)).app
      ((etaleModuleInverseImage.{u, r} Λ f).obj C).obj).symm).isIso_hom

/-- **The self-map twist is the identity at a fixed point.** -/
theorem selfMapPointTwist_selfMapTwist_app {y : EtaleSections f} (hy : y.1 = y.1 ≫ φ)
    (C : EtaleModules.{u, r} Λ (Spec (.of Ω))) :
    (selfMapPointTwist.{u, r} Λ f φ (selfMapTwist.{u, r} Λ f φ w) hy).app C =
      𝟙 ((selfMapSections.{u, r} Λ f (etaleSectionObj f y)).obj C) := by
  have := isIso_selfMapPointRestriction_app Λ f y C
  have h := congrArg (fun z => NatTrans.app z C)
    (selfMapPointRestriction_comp_selfMapPointTwist Λ f φ w hy)
  dsimp only [NatTrans.comp_app] at h
  exact (IsIso.inv_hom_id_assoc _ _).symm.trans
    ((congrArg (fun z => CategoryTheory.inv ((selfMapPointRestriction.{u, r} Λ f y).app C) ≫ z)
      h).trans (IsIso.inv_hom_id _))

end PointTwist

/-! ### The count -/

section Count

open CategoryTheory.FilteredDerived

variable (Λ : Type r) [Ring Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {W : Scheme.{u}}
  (f : W ⟶ Spec (.of Ω)) [Etale f] (φ : W ⟶ W) (w : φ ≫ f = f)

/-- The complex of sections over `Spec Ω` of a complex of sheaves on `Spec Ω`. -/
abbrev baseSectionsComplex (K : CochainComplex (EtaleModules.{u, r} Λ (Spec (.of Ω))) ℤ) :
    CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ :=
  ((sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
    (CategoryTheory.evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{max (u + 1) r} Λ)).obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- **The block at an `Ω`-point is the complex of sections over `Spec Ω`**, by pulling back. -/
def selfMapPointRestrictionComplexIso (y : EtaleSections f)
    (K : CochainComplex (EtaleModules.{u, r} Λ (Spec (.of Ω))) ℤ) :
    baseSectionsComplex Λ K ≅
      ((selfMapSections Λ f (etaleSectionObj f y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => haveI := isIso_selfMapPointRestriction_app Λ f y (K.X n)
      asIso ((selfMapPointRestriction Λ f y).app (K.X n)))
    (fun i j _ => ((selfMapPointRestriction Λ f y).naturality (K.d i j)).symm)

variable [IsFinite f]

/-- **The trace of `φ^*` on `RΓ(W, f^{-1} C)` for `W` finite étale over a separably closed field
`Ω`**: the number of `Ω`-points fixed by `φ`, times the trace of the identity of the complex of
sections of `C` over `Spec Ω` (its Euler characteristic). This is the dimension zero case of the
trace formula for the twisted endomorphisms `(g^{-1} π)^*` in Step 9 of [Stacks, Tag 03UG]. -/
@[sga "5 III 4.11" "special case"]
theorem perfectDerivedTrace_selfMapCohomologyEndo_eq_card_smul
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ (Spec (.of Ω))))
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ f C)))
    (hΓ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (baseSectionsComplex Λ C.obj))) :
    perfectDerivedTrace Λ ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, r} Λ f φ w C)) =
      Nat.card (SelfMapFixedSections f φ) • perfectDerivedTrace Λ ⟨_, hΓ⟩ (𝟙 _) := by
  have hP : ∀ y, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((selfMapSections Λ f (etaleSectionObj f y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.obj)) := fun y =>
    StacksDraft.Perfect.isPerfect_of_iso
      (DerivedCategory.Q.mapIso (selfMapPointRestrictionComplexIso Λ f y C.obj)).symm hΓ
  classical
  rw [perfectDerivedTrace_selfMapCohomologyEndo_eq_sum_of_etale Λ f φ w C hperf hP,
    Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h1 : (NatTrans.mapHomologicalComplex
      (selfMapPointTwist Λ f φ (selfMapTwist.{u, r} Λ f φ w) y.2) (ComplexShape.up ℤ)).app C.obj =
        𝟙 _ := by
    ext n : 1
    exact selfMapPointTwist_selfMapTwist_app Λ f φ w y.2 (C.obj.X n)
  rw [h1, CategoryTheory.Functor.map_id]
  exact (perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Q.mapIso (selfMapPointRestrictionComplexIso Λ f y.1 C.obj)) _ _
    (by rw [Category.id_comp, Category.comp_id])).symm

end Count

end Stacks.EtaleCohomology

end
