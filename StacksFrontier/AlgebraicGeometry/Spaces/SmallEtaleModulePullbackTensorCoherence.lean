module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackBraiding
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensorComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The comparison of Stacks 03EL for algebraic spaces is monoidal

Let `f : X ⟶ Y` be a morphism of algebraic spaces.  The comparison of Stacks 03EL,
`AlgebraicGeometry.Space.modulePullbackTensorIso`,
`f^*(G ⊗ G') ≅ f^*G ⊗ f^*G'`, and the comparison of the units,
`AlgebraicGeometry.Space.modulePullbackUnitIso`, `f^*𝒪_Y ≅ 𝒪_X`, are compatible with the
associator, with both unitors and with the braiding of the monoidal structure
`AlgebraicGeometry.Space.modulesMonoidalCategory` of `𝒪`-modules.

For a morphism of ringed topoi these four coherences are known for the *strict* monoidal
structure of Tag 01CA, whose tensor product is the tensor product sheaf on the nose:
`Stacks.SheafOfModules.RingedToposPullback.associativity`, `leftUnitality`, `rightUnitality`
and `braiding`.  The monoidal structure of `𝒪`-modules on an algebraic space is the
*localized* one, `Stacks.SheafOfModules.monoidalCategory`, and the comparison
`AlgebraicGeometry.Space.modulePullbackTensorIso` is the four-field comparison conjugated by
`AlgebraicGeometry.Space.modulesTensorObjIso`.  The structural morphisms of the strict
structure are those of the localized one conjugated by the same isomorphism
(`Stacks.SheafOfModules.Strict.associator_eq` and its companions, all `rfl`), so each
coherence transports.  The transport is done once, over abstract monoidal categories, in the
private lemmas of the first section, and then instantiated.

## Main results

* `AlgebraicGeometry.Space.modulePullbackTensorIso_associativity`: **the comparison of
  Stacks 03EL for algebraic spaces is compatible with the associator.**
* `AlgebraicGeometry.Space.modulePullbackTensorIso_leftUnitality` and
  `AlgebraicGeometry.Space.modulePullbackTensorIso_rightUnitality`: it is compatible with the two
  unitors, the units being matched by `AlgebraicGeometry.Space.modulePullbackUnitIso`.
* `AlgebraicGeometry.Space.modulePullbackTensorIso_braiding`: it is compatible with the
  braiding `AlgebraicGeometry.Space.modulesBraidedCategory`.
* `AlgebraicGeometry.Space.modulePullbackTensorIso_whiskerLeft_naturality` and
  `AlgebraicGeometry.Space.modulePullbackTensorIso_whiskerRight_naturality`: its naturality in
  each variable separately, in whiskered form.

## Implementation notes

The four coherences of the strict structure are fed to the transport lemmas with the strict
structural morphisms *named* (`(self := …)`), each identified with its conjugate by its own `rfl`
lemma; only the comparison itself is matched across the two spellings of the small étale
ringed topos.  For the associativity that match exhausts the heartbeat budget at `whnf` unless
`Stacks.SheafOfModules.Tensor.sheafTensor` and `Stacks.SheafOfModules.pullbackTensorIso` are
made locally irreducible, which stops the unifier from unfolding the tensor product sheaf into
its sheafification.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

/-! ### Transport of the coherences along a conjugation of the tensor product -/

section Conjugation

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  (F : C ⥤ D) {TC : C → C → C} (tC : ∀ A B : C, A ⊗ B ≅ TC A B)
  {TD : D → D → D} (tD : ∀ A B : D, A ⊗ B ≅ TD A B)
  (δ : ∀ A B : C, F.obj (TC A B) ≅ TD (F.obj A) (F.obj B))
  (μ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
  (hμ : ∀ A B : C, μ A B = F.mapIso (tC A B) ≪≫ δ A B ≪≫ (tD (F.obj A) (F.obj B)).symm)
include hμ

/-- The comparison `δ`, recovered from its conjugate `μ`. -/
private theorem conj_delta (A B : C) :
    (δ A B).hom = F.map (tC A B).inv ≫ (μ A B).hom ≫ (tD (F.obj A) (F.obj B)).hom := by
  simp only [hμ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.map_inv_hom_id_assoc]

/-- **Associativity transports along conjugation.** -/
private theorem conj_associativity
    (hR : ∀ (A : C) {B B' : C} (b : B ⟶ B'), F.map (A ◁ b) ≫ (μ A B').hom =
      (μ A B).hom ≫ (F.obj A ◁ F.map b))
    (hL : ∀ {A A' : C} (a : A ⟶ A') (B : C), F.map (a ▷ B) ≫ (μ A' B).hom =
      (μ A B).hom ≫ (F.map a ▷ F.obj B))
    (A B E : C)
    (aY : TC (TC A B) E ⟶ TC A (TC B E))
    (haY : aY = ((tC (TC A B) E).inv ≫ ((tC A B).inv ⊗ₘ 𝟙 E)) ≫ ((α_ A B E).hom ≫
      ((𝟙 A ⊗ₘ (tC B E).hom) ≫ (tC A (TC B E)).hom)))
    (wl : TD (F.obj A) (F.obj (TC B E)) ⟶ TD (F.obj A) (TD (F.obj B) (F.obj E)))
    (hwl : wl = (tD (F.obj A) (F.obj (TC B E))).inv ≫ (F.obj A ◁ (δ B E).hom) ≫
      (tD (F.obj A) (TD (F.obj B) (F.obj E))).hom)
    (wr : TD (F.obj (TC A B)) (F.obj E) ⟶ TD (TD (F.obj A) (F.obj B)) (F.obj E))
    (hwr : wr = (tD (F.obj (TC A B)) (F.obj E)).inv ≫ ((δ A B).hom ▷ F.obj E) ≫
      (tD (TD (F.obj A) (F.obj B)) (F.obj E)).hom)
    (aX : TD (TD (F.obj A) (F.obj B)) (F.obj E) ⟶ TD (F.obj A) (TD (F.obj B) (F.obj E)))
    (haX : aX = ((tD (TD (F.obj A) (F.obj B)) (F.obj E)).inv ≫
      ((tD (F.obj A) (F.obj B)).inv ⊗ₘ 𝟙 (F.obj E))) ≫ ((α_ (F.obj A) (F.obj B) (F.obj E)).hom ≫
      ((𝟙 (F.obj A) ⊗ₘ (tD (F.obj B) (F.obj E)).hom) ≫ (tD (F.obj A) (TD (F.obj B) (F.obj
          E))).hom)))
    (h : F.map aY ≫ (δ A (TC B E)).hom ≫ wl = (δ (TC A B) E).hom ≫ wr ≫ aX) :
    F.map (α_ A B E).hom ≫ (μ A (B ⊗ E)).hom ≫
        (F.obj A ◁ (μ B E).hom) =
      (μ (A ⊗ B) E).hom ≫ ((μ A B).hom ▷ F.obj E) ≫
        (α_ (F.obj A) (F.obj B) (F.obj E)).hom := by
  subst haY hwl hwr haX
  rw [conj_delta F tC tD δ μ hμ A (TC B E), conj_delta F tC tD δ μ hμ B E,
    conj_delta F tC tD δ μ hμ (TC A B) E, conj_delta F tC tD δ μ hμ A B] at h
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.map_hom_inv_id_assoc,
    tensorHom_id, id_tensorHom, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.hom_inv_whiskerRight_assoc] at h
  rw [reassoc_of% (hR A (tC B E).hom), ← reassoc_of% (hL (tC A B).inv E)] at h
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.map_hom_inv_id_assoc] at h
  rw [← cancel_epi (F.map ((tC (TC A B) E).inv ≫ (tC A B).inv ▷ E)),
    ← cancel_mono ((F.obj A ◁ (tD (F.obj B) (F.obj E)).hom) ≫
      (tD (F.obj A) (TD (F.obj B) (F.obj E))).hom)]
  simpa only [Functor.map_comp, Category.assoc, MonoidalCategory.whiskerLeft_comp] using h

/-- **The braiding transports along conjugation.** -/
private theorem conj_braiding [BraidedCategory C] [BraidedCategory D] (A B : C)
    (h : F.map ((tC A B).inv ≫ (β_ A B).hom ≫ (tC B A).hom) ≫ (δ B A).hom =
      (δ A B).hom ≫ ((tD (F.obj A) (F.obj B)).inv ≫ (β_ (F.obj A) (F.obj B)).hom ≫
        (tD (F.obj B) (F.obj A)).hom)) :
    F.map (β_ A B).hom ≫ (μ B A).hom =
      (μ A B).hom ≫ (β_ (F.obj A) (F.obj B)).hom := by
  rw [conj_delta F tC tD δ μ hμ B A, conj_delta F tC tD δ μ hμ A B] at h
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.map_hom_inv_id_assoc] at h
  rw [← cancel_epi (F.map (tC A B).inv), ← cancel_mono (tD (F.obj B) (F.obj A)).hom]
  simpa only [Category.assoc] using h

/-- **The left unitor transports along conjugation.** -/
private theorem conj_leftUnitality (u : F.obj (𝟙_ C) ⟶ 𝟙_ D) (A : C)
    (h : F.map ((tC (𝟙_ C) A).inv ≫ (λ_ A).hom) =
      (δ (𝟙_ C) A).hom ≫ ((tD (F.obj (𝟙_ C)) (F.obj A)).inv ≫ (u ▷ F.obj A) ≫
        (tD (𝟙_ D) (F.obj A)).hom) ≫ ((tD (𝟙_ D) (F.obj A)).inv ≫ (λ_ (F.obj A)).hom)) :
    F.map (λ_ A).hom = (μ (𝟙_ C) A).hom ≫ (u ▷ F.obj A) ≫ (λ_ (F.obj A)).hom := by
  rw [conj_delta F tC tD δ μ hμ (𝟙_ C) A] at h
  rw [← cancel_epi (F.map (tC (𝟙_ C) A).inv)]
  simpa only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc] using h

/-- **The right unitor transports along conjugation.** -/
private theorem conj_rightUnitality (u : F.obj (𝟙_ C) ⟶ 𝟙_ D) (A : C)
    (h : F.map ((tC A (𝟙_ C)).inv ≫ (ρ_ A).hom) =
      (δ A (𝟙_ C)).hom ≫ ((tD (F.obj A) (F.obj (𝟙_ C))).inv ≫ (F.obj A ◁ u) ≫
        (tD (F.obj A) (𝟙_ D)).hom) ≫ ((tD (F.obj A) (𝟙_ D)).inv ≫ (ρ_ (F.obj A)).hom)) :
    F.map (ρ_ A).hom = (μ A (𝟙_ C)).hom ≫ (F.obj A ◁ u) ≫ (ρ_ (F.obj A)).hom := by
  rw [conj_delta F tC tD δ μ hμ A (𝟙_ C)] at h
  rw [← cancel_epi (F.map (tC A (𝟙_ C)).inv)]
  simpa only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc] using h

end Conjugation

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The comparison of Stacks 03EL for algebraic spaces is natural in its second variable, in
whiskered form. -/
theorem modulePullbackTensorIso_whiskerLeft_naturality (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) {G' G'' : Modules.{u, u} B S hS Y.1 Y.2} (b : G' ⟶ G'') :
    (modulePullback B S hS f).map (G ◁ b) ≫ (modulePullbackTensorIso B S hS f G G'').hom =
      (modulePullbackTensorIso B S hS f G G').hom ≫
        ((modulePullback B S hS f).obj G ◁ (modulePullback B S hS f).map b) := by
  have h := modulePullbackTensorIso_hom_naturality B S hS f (𝟙 G) b
  rw [(modulePullback B S hS f).map_id G] at h
  simpa only [id_tensorHom] using h

/-- The comparison of Stacks 03EL for algebraic spaces is natural in its first variable, in
whiskered form. -/
theorem modulePullbackTensorIso_whiskerRight_naturality (f : X ⟶ Y)
    {G G' : Modules.{u, u} B S hS Y.1 Y.2} (a : G ⟶ G') (G'' : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).map (a ▷ G'') ≫ (modulePullbackTensorIso B S hS f G' G'').hom =
      (modulePullbackTensorIso B S hS f G G'').hom ≫
        ((modulePullback B S hS f).map a ▷ (modulePullback B S hS f).obj G'') := by
  have h := modulePullbackTensorIso_hom_naturality B S hS f a (𝟙 G'')
  rw [(modulePullback B S hS f).map_id G''] at h
  simpa only [tensorHom_id] using h

private theorem associator_strict_source (_f : X ⟶ Y) (G G' G'' : Modules.{u, u} B S hS Y.1 Y.2) :
    (MonoidalCategoryStruct.associator (self :=
        (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
        Y).O).toMonoidalCategoryStruct) G G' G'').hom =
      (((modulesTensorObjIso B S hS Y.1 Y.2 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u,
          u, u, u} (structureSheaf B S hS Y.1 Y.2)).obj G).obj G') G'').inv ≫ ((modulesTensorObjIso
          B S hS Y.1 Y.2 G G').inv ⊗ₘ 𝟙 G'')) ≫ ((α_ G G' G'').hom ≫ ((𝟙 G ⊗ₘ (modulesTensorObjIso B
          S hS Y.1 Y.2 G' G'').hom) ≫ (modulesTensorObjIso B S hS Y.1 Y.2 G
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} (structureSheaf B S hS Y.1
          Y.2)).obj G').obj G'')).hom))) :=
  rfl

private theorem whiskerLeft_strict_target (f : X ⟶ Y) (G G' G'' : Modules.{u, u} B S hS Y.1 Y.2) :
    MonoidalCategoryStruct.whiskerLeft (self :=
        (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
        X).O).toMonoidalCategoryStruct) ((smallEtaleRingedToposModulesHom B S hS
        f).pullbackModules.obj G)
        (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison
        (smallEtaleRingedToposModulesHom B S hS f) G' G'') =
      (modulesTensorObjIso B S hS X.1 X.2 ((modulePullback B S hS f).obj G) ((modulePullback B S hS
          f).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} (structureSheaf B S
          hS Y.1 Y.2)).obj G').obj G''))).inv ≫ (MonoidalCategoryStruct.whiskerLeft (C :=
          Modules.{u, u} B S hS X.1 X.2) ((modulePullback B S hS f).obj G)
          (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparisonIso
          (smallEtaleRingedToposModulesHom B S hS f) G' G'').hom) ≫ (modulesTensorObjIso B S hS X.1
          X.2 ((modulePullback B S hS f).obj G) (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1,
          u, u, u, u} (structureSheaf B S hS X.1 X.2)).obj ((modulePullback B S hS f).obj G')).obj
          ((modulePullback B S hS f).obj G''))).hom :=
  rfl

private theorem whiskerRight_strict_target (f : X ⟶ Y) (G G' G'' : Modules.{u, u} B S hS Y.1 Y.2) :
    MonoidalCategoryStruct.whiskerRight (self :=
        (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
        X).O).toMonoidalCategoryStruct)
        (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison
        (smallEtaleRingedToposModulesHom B S hS f) G G') ((smallEtaleRingedToposModulesHom B S hS
        f).pullbackModules.obj G'') =
      (modulesTensorObjIso B S hS X.1 X.2 ((modulePullback B S hS f).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} (structureSheaf B S hS Y.1
          Y.2)).obj G).obj G')) ((modulePullback B S hS f).obj G'')).inv ≫
          (MonoidalCategoryStruct.whiskerRight (C := Modules.{u, u} B S hS X.1 X.2)
          (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparisonIso
          (smallEtaleRingedToposModulesHom B S hS f) G G').hom ((modulePullback B S hS f).obj G''))
          ≫ (modulesTensorObjIso B S hS X.1 X.2 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1,
          u, u, u, u} (structureSheaf B S hS X.1 X.2)).obj ((modulePullback B S hS f).obj G)).obj
          ((modulePullback B S hS f).obj G')) ((modulePullback B S hS f).obj G'')).hom :=
  rfl

private theorem associator_strict_target (f : X ⟶ Y) (G G' G'' : Modules.{u, u} B S hS Y.1 Y.2) :
    (MonoidalCategoryStruct.associator (self :=
        (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
        X).O).toMonoidalCategoryStruct) ((smallEtaleRingedToposModulesHom B S hS
        f).pullbackModules.obj G) ((smallEtaleRingedToposModulesHom B S hS f).pullbackModules.obj
        G') ((smallEtaleRingedToposModulesHom B S hS f).pullbackModules.obj G'')).hom =
      (((modulesTensorObjIso B S hS X.1 X.2 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u,
          u, u, u} (structureSheaf B S hS X.1 X.2)).obj ((modulePullback B S hS f).obj G)).obj
          ((modulePullback B S hS f).obj G')) ((modulePullback B S hS f).obj G'')).inv ≫
          ((modulesTensorObjIso B S hS X.1 X.2 ((modulePullback B S hS f).obj G) ((modulePullback B
          S hS f).obj G')).inv ⊗ₘ 𝟙 ((modulePullback B S hS f).obj G''))) ≫ ((α_ ((modulePullback B
          S hS f).obj G) ((modulePullback B S hS f).obj G') ((modulePullback B S hS f).obj G'')).hom
          ≫ ((𝟙 ((modulePullback B S hS f).obj G) ⊗ₘ (modulesTensorObjIso B S hS X.1 X.2
          ((modulePullback B S hS f).obj G') ((modulePullback B S hS f).obj G'')).hom) ≫
          (modulesTensorObjIso B S hS X.1 X.2 ((modulePullback B S hS f).obj G)
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} (structureSheaf B S hS X.1
          X.2)).obj ((modulePullback B S hS f).obj G')).obj ((modulePullback B S hS f).obj
          G''))).hom))) :=
  rfl

section Irreducible

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor
  Stacks.SheafOfModules.pullbackTensorIso

/-- `Stacks.SheafOfModules.RingedToposPullback.associativity` at the morphism of small étale
ringed topoi of `f`, with the source functor spelled `AlgebraicGeometry.Space.modulePullback`. -/
private theorem associativity_strict (f : X ⟶ Y) (G G' G'' : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).map (MonoidalCategoryStruct.associator (self :=
        (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
        Y).O).toMonoidalCategoryStruct) G G' G'').hom ≫
      (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparisonIso
          (smallEtaleRingedToposModulesHom B S hS f) G (MonoidalCategoryStruct.tensorObj (self :=
          (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
          Y).O).toMonoidalCategoryStruct) G' G'')).hom ≫
        MonoidalCategoryStruct.whiskerLeft (self :=
            (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
            X).O).toMonoidalCategoryStruct) ((smallEtaleRingedToposModulesHom B S hS
            f).pullbackModules.obj G)
            (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison
            (smallEtaleRingedToposModulesHom B S hS f) G' G'') =
      (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparisonIso
          (smallEtaleRingedToposModulesHom B S hS f) (MonoidalCategoryStruct.tensorObj (self :=
          (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
          Y).O).toMonoidalCategoryStruct) G G') G'').hom ≫
        MonoidalCategoryStruct.whiskerRight (self :=
            (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
            X).O).toMonoidalCategoryStruct)
            (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison
            (smallEtaleRingedToposModulesHom B S hS f) G G') ((smallEtaleRingedToposModulesHom B S
            hS f).pullbackModules.obj G'') ≫
          (MonoidalCategoryStruct.associator (self :=
              (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S
              hS X).O).toMonoidalCategoryStruct) ((smallEtaleRingedToposModulesHom B S hS
              f).pullbackModules.obj G) ((smallEtaleRingedToposModulesHom B S hS
              f).pullbackModules.obj G') ((smallEtaleRingedToposModulesHom B S hS
              f).pullbackModules.obj G'')).hom :=
  Stacks.SheafOfModules.RingedToposPullback.associativity (smallEtaleRingedToposModulesHom B S hS f)
      G G' G''

/-- **The comparison of Stacks 03EL for algebraic spaces is compatible with the associator.**
For `f : X ⟶ Y` and `𝒪_Y`-modules `G`, `G'`, `G''`, the two ways of comparing
`f^*((G ⊗ G') ⊗ G'')` with `f^*G ⊗ (f^*G' ⊗ f^*G'')` agree. -/
theorem modulePullbackTensorIso_associativity (f : X ⟶ Y)
    (G G' G'' : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).map (α_ G G' G'').hom ≫
        (modulePullbackTensorIso B S hS f G (G' ⊗ G'')).hom ≫
          ((modulePullback B S hS f).obj G ◁ (modulePullbackTensorIso B S hS f G' G'').hom) =
      (modulePullbackTensorIso B S hS f (G ⊗ G') G'').hom ≫
        ((modulePullbackTensorIso B S hS f G G').hom ▷ (modulePullback B S hS f).obj G'') ≫
          (α_ ((modulePullback B S hS f).obj G) ((modulePullback B S hS f).obj G')
            ((modulePullback B S hS f).obj G'')).hom :=
  conj_associativity (modulePullback B S hS f)
    (TC := fun A A' => MonoidalCategoryStruct.tensorObj (self :=
        (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
        Y).O).toMonoidalCategoryStruct) A A')
    (modulesTensorObjIso B S hS Y.1 Y.2)
    (TD := fun A A' => MonoidalCategoryStruct.tensorObj (self :=
        (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS
        X).O).toMonoidalCategoryStruct) A A')
    (modulesTensorObjIso B S hS X.1 X.2)
    (fun A A' => Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparisonIso
      (smallEtaleRingedToposModulesHom B S hS f) A A')
    (modulePullbackTensorIso B S hS f) (fun _ _ => rfl)
    (modulePullbackTensorIso_whiskerLeft_naturality B S hS f)
    (modulePullbackTensorIso_whiskerRight_naturality B S hS f) G G' G''
    _ (associator_strict_source B S hS f G G' G'') _ (whiskerLeft_strict_target B S hS f G G' G'')
    _ (whiskerRight_strict_target B S hS f G G' G'') _ (associator_strict_target B S hS f G G' G'')
    (associativity_strict B S hS f G G' G'')

end Irreducible

/-- **The comparison of Stacks 03EL for algebraic spaces is compatible with the braiding.** -/
theorem modulePullbackTensorIso_braiding (f : X ⟶ Y) (G G' : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).map (β_ G G').hom ≫ (modulePullbackTensorIso B S hS f G' G).hom =
      (modulePullbackTensorIso B S hS f G G').hom ≫
        (β_ ((modulePullback B S hS f).obj G) ((modulePullback B S hS f).obj G')).hom :=
  conj_braiding (modulePullback B S hS f) (modulesTensorObjIso B S hS Y.1 Y.2)
    (modulesTensorObjIso B S hS X.1 X.2)
    (fun A A' => (Stacks.SheafOfModules.pullbackTensorIso
      (smallEtaleRingedToposModulesHom B S hS f)).app (A, A'))
    (modulePullbackTensorIso B S hS f) (fun _ _ => rfl) G G'
    (Stacks.SheafOfModules.RingedToposPullback.braiding
      (smallEtaleRingedToposModulesHom B S hS f) G G')

/-- **The comparison of Stacks 03EL for algebraic spaces is compatible with the left unitor**,
the units being matched by `AlgebraicGeometry.Space.modulePullbackUnitIso`. -/
theorem modulePullbackTensorIso_leftUnitality (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).map (λ_ G).hom =
      (modulePullbackTensorIso B S hS f (𝟙_ _) G).hom ≫
        ((modulePullbackUnitIso B S hS f).hom ▷ (modulePullback B S hS f).obj G) ≫
          (λ_ ((modulePullback B S hS f).obj G)).hom :=
  conj_leftUnitality (modulePullback B S hS f) (modulesTensorObjIso B S hS Y.1 Y.2)
    (modulesTensorObjIso B S hS X.1 X.2)
    (fun A A' => (Stacks.SheafOfModules.pullbackTensorIso
      (smallEtaleRingedToposModulesHom B S hS f)).app (A, A'))
    (modulePullbackTensorIso B S hS f) (fun _ _ => rfl)
    (modulePullbackUnitIso B S hS f).hom G
    (Stacks.SheafOfModules.RingedToposPullback.leftUnitality
      (smallEtaleRingedToposModulesHom B S hS f) G)

/-- **The comparison of Stacks 03EL for algebraic spaces is compatible with the right
unitor**, the units being matched by `AlgebraicGeometry.Space.modulePullbackUnitIso`. -/
theorem modulePullbackTensorIso_rightUnitality (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).map (ρ_ G).hom =
      (modulePullbackTensorIso B S hS f G (𝟙_ _)).hom ≫
        ((modulePullback B S hS f).obj G ◁ (modulePullbackUnitIso B S hS f).hom) ≫
          (ρ_ ((modulePullback B S hS f).obj G)).hom :=
  conj_rightUnitality (modulePullback B S hS f) (modulesTensorObjIso B S hS Y.1 Y.2)
    (modulesTensorObjIso B S hS X.1 X.2)
    (fun A A' => (Stacks.SheafOfModules.pullbackTensorIso
      (smallEtaleRingedToposModulesHom B S hS f)).app (A, A'))
    (modulePullbackTensorIso B S hS f) (fun _ _ => rfl)
    (modulePullbackUnitIso B S hS f).hom G
    (Stacks.SheafOfModules.RingedToposPullback.rightUnitality
      (smallEtaleRingedToposModulesHom B S hS f) G)


end AlgebraicGeometry.Space

end
