module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentAffineModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentTriangle

/-!
# The conclusion of Stacks 0DKV read on an affine model

Let `D` be Situation 0DKU with `X₀` an affine algebraic space, `e₀ : yoneda Z' ≅ X₀`, and let
`R` represent the base changes along `e₀ ≫ p₀`, so that the stages `Xⱼ` and the limit `X` are
represented by the objects `Wⱼ` and `W` of `R`
(`AlgebraicGeometry.Space.RelativeDescentSituation.stageModelIso`). This file transports the
derived homomorphism sets of the situation, with their transition and comparison maps, to the
derived homomorphism sets over the represented presheaves `yoneda Wⱼ` and `yoneda W` with the
maps induced by the morphisms of the site, and deduces the conclusion of Stacks 0DKV for `D` from
the corresponding statement for the represented system,
`AlgebraicGeometry.Space.RelativeDescentSituation.ModelHomDescent`.

## Main results

* `AlgebraicGeometry.Space.DerivedPullbackComposition.factorHom_bijective_of_isIso`: the map of
  derived homomorphism sets induced by a factorisation through an isomorphism is bijective.
* `AlgebraicGeometry.Space.RelativeDescentSituation.stageModelHomEquiv` and
  `limitModelHomEquiv`, with their compatibilities `stageModelHomEquiv_homTransition` and
  `limitModelHomEquiv_homComparison`.
* `AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_of_modelHomDescent`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/- The derived pullback `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, the datum
`AlgebraicGeometry.Space.DerivedPullbackComposition` and the conclusion of Stacks 0DKV are stated
for the standard model of the derived category, so the declarations below are stated at it too. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/- The filtered colimits used to form the étale sheafification, through Mathlib's instance, so that
the derived categories of `𝒪`-modules below are spelled as in the files of the derived pullback. -/
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

/-- The additive structure of `𝒪_X`-modules, the instance with which the homotopy categories of
degreewise pullback are formed. -/
local instance (priority := 6000) preadditive_smallEtaleModules_model {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS) :
    Preadditive (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  SheafOfModules.instPreadditive _

namespace DerivedPullbackComposition

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (P : DerivedPullbackComposition B S hS)

/-- The derived pullback along an isomorphism of algebraic spaces is an equivalence. -/
def pullbackEquivalenceOfIsIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [IsIso f] :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ≌
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  CategoryTheory.Equivalence.mk (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedModulePullback B S hS (inv f))
    ((P.iso (inv f) f (𝟙 Y) (IsIso.inv_hom_id f) ≪≫ P.idIso Y).symm)
    (P.iso f (inv f) (𝟙 X) (IsIso.hom_inv_id f) ≪≫ P.idIso X)

/-- **A factorisation through an isomorphism induces bijections of derived homomorphisms.** -/
theorem factorHom_bijective_of_isIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    Function.Bijective (P.factorHom f g k h K L) := by
  have hF : Function.Bijective (fun φ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L =>
        (smallEtaleDerivedModulePullback B S hS f).map φ) :=
    (P.pullbackEquivalenceOfIsIso f).fullyFaithfulFunctor.map_bijective _ _
  exact (((P.iso f g k h).app K).homCongr ((P.iso f g k h).app L)).bijective.comp hF

end DerivedPullbackComposition

namespace RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : RelativeDescentSituation B S hS hZ I} (P : DerivedPullbackComposition B S hS)
  {Z' : BigAffineFppf B S hS}
  (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ D.X₀)
  (R : D.AffineBaseChangeRepresentation Z' (e₀.hom ≫ D.p₀))

/-- `yoneda Z'`, the model of `X₀`, as an algebraic space. -/
abbrev modelBase : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z'), isAlgebraicSpace_yoneda B S hS _⟩

/-- The identification of the model of `X₀` with `X₀`. -/
abbrev modelInitialHom : modelBase (Z' := Z') ⟶ D.initialSource := ObjectProperty.homMk e₀.hom

/-- The identification of the model of `Xⱼ` with `Xⱼ`. -/
abbrev modelStageHom (j : D.LaterIndex) :
    (⟨yoneda.obj (R.W.obj (op j)), isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶
      D.stageSource j :=
  ObjectProperty.homMk (D.stageModelIso e₀ R j).hom

/-- The identification of the model of `X` with `X`. -/
abbrev modelLimitHom :
    (⟨yoneda.obj R.c.pt, isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶
      D.limitSource :=
  ObjectProperty.homMk (D.limitModelIso e₀ R).hom

/-- The pullback on homotopy categories along the morphism of algebraic spaces represented by a
morphism `g` of the site has a left derived functor. -/
instance hasLeftDerivedFunctor_representedSpaceMap_model {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    (smallEtaleModulePullbackOnHomotopy B S hS (representedSpaceMap B S hS g)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- The pullback on homotopy categories along `modelInitialHom e₀` has a left derived functor. -/
instance hasLeftDerivedFunctor_modelInitialHom :
    (smallEtaleModulePullbackOnHomotopy B S hS (modelInitialHom e₀)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS D.initialSource) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- The pullback on homotopy categories along `modelStageHom e₀ R j` has a left derived functor. -/
instance hasLeftDerivedFunctor_modelStageHom (j : D.LaterIndex) :
    (smallEtaleModulePullbackOnHomotopy B S hS (modelStageHom e₀ R j)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS (D.stageSource j)) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- The pullback on homotopy categories along `modelLimitHom e₀ R` has a left derived functor. -/
instance hasLeftDerivedFunctor_modelLimitHom :
    (smallEtaleModulePullbackOnHomotopy B S hS (modelLimitHom e₀ R)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS D.limitSource) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- The identification `modelStageHom e₀ R j` of the model of `Xⱼ` with `Xⱼ` is an
isomorphism. -/
instance (j : D.LaterIndex) : IsIso (modelStageHom e₀ R j) :=
  ⟨⟨ObjectProperty.homMk (D.stageModelIso e₀ R j).inv,
    ObjectProperty.hom_ext _ (D.stageModelIso e₀ R j).hom_inv_id,
    ObjectProperty.hom_ext _ (D.stageModelIso e₀ R j).inv_hom_id⟩⟩

/-- The identification `modelLimitHom e₀ R` of the model of `X` with `X` is an isomorphism. -/
instance : IsIso (modelLimitHom e₀ R) :=
  ⟨⟨ObjectProperty.homMk (D.limitModelIso e₀ R).inv,
    ObjectProperty.hom_ext _ (D.limitModelIso e₀ R).hom_inv_id,
    ObjectProperty.hom_ext _ (D.limitModelIso e₀ R).inv_hom_id⟩⟩

/-- The model identifications intertwine the map `Wⱼ → Z'` with the map `Xⱼ → X₀`. -/
theorem modelStageHom_comp_stageToInitial (j : D.LaterIndex) :
    representedSpaceMap B S hS (R.q j) ≫ modelInitialHom e₀ =
      modelStageHom e₀ R j ≫ D.stageToInitial j :=
  ObjectProperty.hom_ext _ (D.stageModelIso_hom_toX₀ e₀ R j).symm

/-- The model identifications intertwine the map `W → Z'` with the map `X → X₀`. -/
theorem modelLimitHom_comp_limitToInitial :
    representedSpaceMap B S hS R.qc ≫ modelInitialHom e₀ =
      modelLimitHom e₀ R ≫ D.limitToInitial :=
  ObjectProperty.hom_ext _ (D.limitModelIso_hom_toInitial e₀ R).symm

/-- The model identifications intertwine the transition morphism `Wₖ → Wⱼ` with the
transition morphism `Xₖ → Xⱼ`. -/
theorem modelStageHom_comp_sourceTransition {j k : D.LaterIndex} (h : j.1 ≤ k.1) :
    modelStageHom e₀ R k ≫ D.sourceTransition h =
      representedSpaceMap B S hS (R.W.map (homOfLE (show j ≤ k from h)).op) ≫
        modelStageHom e₀ R j :=
  ObjectProperty.hom_ext _ (D.stageModelIso_hom_fᵢⱼ e₀ R h)

/-- The model identifications intertwine the leg `W → Wⱼ` of the cone with the projection
`X → Xⱼ`. -/
theorem modelLimitHom_comp_sourceProjection (j : D.LaterIndex) :
    modelLimitHom e₀ R ≫ D.sourceProjection j =
      representedSpaceMap B S hS (R.c.π.app (op j)) ≫ modelStageHom e₀ R j :=
  ObjectProperty.hom_ext _ (D.limitModelIso_hom_fᵢ e₀ R j)

/-- The represented transition morphism `Wₖ → Wⱼ` followed by `Wⱼ → Z'` is `Wₖ → Z'`. -/
theorem representedSpaceMap_W_map_q {j k : D.LaterIndex} (h : j.1 ≤ k.1) :
    representedSpaceMap B S hS (R.W.map (homOfLE (show j ≤ k from h)).op) ≫
        representedSpaceMap B S hS (R.q j) = representedSpaceMap B S hS (R.q k) :=
  ObjectProperty.hom_ext _ (by
    show yoneda.map _ ≫ yoneda.map _ = yoneda.map _
    rw [← Functor.map_comp, R.map_q])

/-- The represented leg `W → Wⱼ` of the cone followed by `Wⱼ → Z'` is `W → Z'`. -/
theorem representedSpaceMap_π_q (j : D.LaterIndex) :
    representedSpaceMap B S hS (R.c.π.app (op j)) ≫ representedSpaceMap B S hS (R.q j) =
      representedSpaceMap B S hS R.qc :=
  ObjectProperty.hom_ext _ (by
    show yoneda.map _ ≫ yoneda.map _ = yoneda.map _
    rw [← Functor.map_comp, R.π_q])

variable (K L : D.InitialDerived)

/-- **The derived homomorphisms at a stage, read on the model.** -/
def stageModelHomEquiv (j : D.LaterIndex) :
    ((smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).obj K ⟶
        (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).obj L) ≃
      ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (R.q j))).obj
          ((smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj K) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (R.q j))).obj
          ((smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj L)) :=
  (Equiv.ofBijective _ (P.factorHom_bijective_of_isIso (modelStageHom e₀ R j)
      (D.stageToInitial j) _ rfl K L)).trans
    (P.baseChangeHomEquiv (representedSpaceMap B S hS (R.q j)) (modelInitialHom e₀) _
      (modelStageHom_comp_stageToInitial e₀ R j) K L)

/-- **The derived homomorphisms at the limit, read on the model.** -/
def limitModelHomEquiv :
    ((smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj K ⟶
        (smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj L) ≃
      ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS R.qc)).obj
          ((smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj K) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS R.qc)).obj
          ((smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj L)) :=
  (Equiv.ofBijective _ (P.factorHom_bijective_of_isIso (modelLimitHom e₀ R)
      D.limitToInitial _ rfl K L)).trans
    (P.baseChangeHomEquiv (representedSpaceMap B S hS R.qc) (modelInitialHom e₀) _
      (modelLimitHom_comp_limitToInitial e₀ R) K L)

/-- Changing base commutes with the maps induced by factorisations, for a square of
identifications `a ≫ t = r ≫ b` of represented spaces with spaces over `Z`. -/
private theorem baseChangeHomEquiv_factorHom_factorHom {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (P : DerivedPullbackComposition B S hS)
    {M N X Y Z Z' : AlgebraicSpaces B S hS} (r : M ⟶ N) (pN : N ⟶ Z') (pM : M ⟶ Z') (ι : Z' ⟶ Z)
    (a : M ⟶ X) (b : N ⟶ Y) (t : X ⟶ Y) (g : Y ⟶ Z) (g' : X ⟶ Z) (hr : r ≫ pN = pM)
    (ht : t ≫ g = g') (e1 : a ≫ t = r ≫ b) (hN : pN ≫ ι = b ≫ g) (hM : pM ≫ ι = a ≫ g')
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (φ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    P.baseChangeHomEquiv pM ι (a ≫ g') hM K L
        (P.factorHom a g' (a ≫ g') rfl K L (P.factorHom t g g' ht K L φ)) =
      P.factorHom r pN pM hr _ _
        (P.baseChangeHomEquiv pN ι (b ≫ g) hN K L (P.factorHom b g (b ≫ g) rfl K L φ)) := by
  have e2 : r ≫ (b ≫ g) = a ≫ g' := by rw [← Category.assoc, ← e1, Category.assoc, ht]
  have hc : (a ≫ t) ≫ g = a ≫ g' := by rw [Category.assoc, ht]
  have hc' : (r ≫ b) ≫ g = a ≫ g' := by rw [Category.assoc, e2]
  rw [P.factorHom_comp a t g g' _ _ ht rfl hc rfl, P.factorHom_congr g _ hc hc' e1,
    ← P.factorHom_comp r b g _ _ _ rfl rfl hc' e2]
  exact P.baseChangeHomEquiv_factorHom _ _ _ _ _ _ hr hN hM e2 _ _ _

/-- The model identifications carry the transition maps of the situation to the maps induced
by the transition morphisms of the representing objects. -/
theorem stageModelHomEquiv_homTransition {j k : D.LaterIndex} (h : j.1 ≤ k.1)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).obj L) :
    stageModelHomEquiv P e₀ R K L k (D.homTransition P K L h φ) =
      P.factorHom (representedSpaceMap B S hS (R.W.map (homOfLE (show j ≤ k from h)).op))
        (representedSpaceMap B S hS (R.q j)) (representedSpaceMap B S hS (R.q k))
        (representedSpaceMap_W_map_q e₀ R h) _ _ (stageModelHomEquiv P e₀ R K L j φ) := by
  simp only [stageModelHomEquiv, Equiv.trans_apply, Equiv.ofBijective_apply, homTransition]
  exact baseChangeHomEquiv_factorHom_factorHom P _ _ _ _ _ _ _ _ _
    (representedSpaceMap_W_map_q e₀ R h) (D.sourceTransition_comp_stageToInitial h)
    (modelStageHom_comp_sourceTransition e₀ R h) (modelStageHom_comp_stageToInitial e₀ R j)
    (modelStageHom_comp_stageToInitial e₀ R k) K L φ

/-- The model identifications carry the comparison maps of the situation to the maps induced
by the legs of the cone of representing objects. -/
theorem limitModelHomEquiv_homComparison (j : D.LaterIndex)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).obj L) :
    limitModelHomEquiv P e₀ R K L (D.homComparison P K L j φ) =
      P.factorHom (representedSpaceMap B S hS (R.c.π.app (op j)))
        (representedSpaceMap B S hS (R.q j)) (representedSpaceMap B S hS R.qc)
        (representedSpaceMap_π_q e₀ R j) _ _ (stageModelHomEquiv P e₀ R K L j φ) := by
  simp only [stageModelHomEquiv, limitModelHomEquiv, Equiv.trans_apply, Equiv.ofBijective_apply,
    homComparison]
  exact baseChangeHomEquiv_factorHom_factorHom P _ _ _ _ _ _ _ _ _
    (representedSpaceMap_π_q e₀ R j) (D.sourceProjection_comp_stageToInitial j)
    (modelLimitHom_comp_sourceProjection e₀ R j) (modelStageHom_comp_stageToInitial e₀ R j)
    (modelLimitHom_comp_limitToInitial e₀ R) K L φ

variable (K' L' : DerivedCategory (SheafOfModules.{u}
  (ringedToposStructureRingSheaf B S hS (modelBase (Z' := Z')))))

/-- **The conclusion of Stacks 0DKV for the represented system**: every morphism over the
model of the limit comes from a stage, and two morphisms at a stage with the same image agree
at a later stage. -/
def ModelHomDescent : Prop :=
  (∀ ψ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS R.qc)).obj K' ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS R.qc)).obj L',
      ∃ (j : D.LaterIndex)
        (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (R.q j))).obj K' ⟶
          (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (R.q j))).obj L'),
        P.factorHom (representedSpaceMap B S hS (R.c.π.app (op j)))
          (representedSpaceMap B S hS (R.q j)) (representedSpaceMap B S hS R.qc)
          (representedSpaceMap_π_q e₀ R j) K' L' φ = ψ) ∧
    ∀ (j : D.LaterIndex)
      (φ φ' : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (R.q j))).obj K' ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (R.q j))).obj L'),
      P.factorHom (representedSpaceMap B S hS (R.c.π.app (op j)))
          (representedSpaceMap B S hS (R.q j)) (representedSpaceMap B S hS R.qc)
          (representedSpaceMap_π_q e₀ R j) K' L' φ =
        P.factorHom (representedSpaceMap B S hS (R.c.π.app (op j)))
          (representedSpaceMap B S hS (R.q j)) (representedSpaceMap B S hS R.qc)
          (representedSpaceMap_π_q e₀ R j) K' L' φ' →
        ∃ (k : D.LaterIndex) (h : j.1 ≤ k.1),
          P.factorHom (representedSpaceMap B S hS (R.W.map (homOfLE (show j ≤ k from h)).op))
              (representedSpaceMap B S hS (R.q j)) (representedSpaceMap B S hS (R.q k))
              (representedSpaceMap_W_map_q e₀ R h) K' L' φ =
            P.factorHom (representedSpaceMap B S hS (R.W.map (homOfLE (show j ≤ k from h)).op))
              (representedSpaceMap B S hS (R.q j)) (representedSpaceMap B S hS (R.q k))
              (representedSpaceMap_W_map_q e₀ R h) K' L' φ'

/-- **Stacks 0DKV for a situation with affine `X₀`, from its affine model.** -/
theorem homDescent_of_modelHomDescent
    (h : ModelHomDescent P e₀ R
      ((smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj K)
      ((smallEtaleDerivedModulePullback B S hS (modelInitialHom e₀)).obj L)) :
    D.HomDescent P K L := by
  refine ⟨fun ψ ↦ ?_, fun j φ φ' hφ ↦ ?_⟩
  · obtain ⟨j, x, hx⟩ := h.1 (limitModelHomEquiv P e₀ R K L ψ)
    refine ⟨j, (stageModelHomEquiv P e₀ R K L j).symm x, ?_⟩
    apply (limitModelHomEquiv P e₀ R K L).injective
    rw [limitModelHomEquiv_homComparison P e₀ R K L j, Equiv.apply_symm_apply]
    exact hx
  · have := congrArg (limitModelHomEquiv P e₀ R K L) hφ
    rw [limitModelHomEquiv_homComparison P e₀ R K L j φ,
      limitModelHomEquiv_homComparison P e₀ R K L j φ'] at this
    obtain ⟨k, hjk, hk⟩ := h.2 j (stageModelHomEquiv P e₀ R K L j φ)
      (stageModelHomEquiv P e₀ R K L j φ') this
    refine ⟨k, hjk, (stageModelHomEquiv P e₀ R K L k).injective ?_⟩
    exact (stageModelHomEquiv_homTransition P e₀ R K L hjk φ).trans
      (hk.trans (stageModelHomEquiv_homTransition P e₀ R K L hjk φ').symm)

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
