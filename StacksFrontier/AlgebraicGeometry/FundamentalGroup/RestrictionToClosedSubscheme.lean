module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProdHomEquiv
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHom
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Thickening
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.AlgebraicGeometry.Thickenings.Infinitesimal

/-!
# Sections of a finite étale cover and restriction to a closed subscheme

Let `Y ⊆ X` be a closed subscheme. Restriction of finite étale covers `FÉt_X ⟶ FÉt_Y` is fully
faithful if and only if, for every finite étale cover `W` of `X`, every section of `W` over `Y`
extends uniquely to a section over `X`. Sections over `Y` extend uniquely to each infinitesimal
neighbourhood of `Y` in `X`. If `X` is Noetherian and the completion functor
`Coh(𝒪_X) ⟶ Coh(X, I)` along the ideal sheaf `I` of `Y` is fully faithful on the finite locally
free objects, then `FÉt_X ⟶ FÉt_Y` is fully faithful.

## Main definitions

All names are in the namespace `Stacks.FundamentalGroup`.

* `selfFiniteEtaleOver`: the finite étale cover of `X` by itself.
* `unitAlgebra`, `nthOrderAlgebra`: the structure sheaf of `X`, and the direct image of the
  structure sheaf of the `n`-th infinitesimal neighbourhood of `Y`, as sheaves of
  `𝒪_X`-algebras.
* `nthOrderAlgebraRestriction`, `nthOrderAlgebraTransition`: the canonical morphisms between
  them, with underlying morphisms of modules `nthOrderUnitMap` and `nthOrderTransitionMap`.

## Main results

* `bijective_restrictSection_of_fullyFaithful`: sections of a finite étale cover restrict
  bijectively along a morphism whose base-change functor on finite étale covers is fully
  faithful.
* `fullyFaithful_finiteEtaleBaseChange_of_bijective_restrictSection`: if the sections of every
  finite étale cover of `X` restrict bijectively to `Y`, then `FÉt_X ⟶ FÉt_Y` is fully faithful.
* `bijective_restrictSection_nthOrderInclusion`: sections over the `n`-th infinitesimal
  neighbourhood of `Y` restrict bijectively to sections over `Y`.
* `fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithfulOnFiniteLocallyFree`: full
  faithfulness of the completion functor on finite locally free coherent modules gives full
  faithfulness of `FÉt_X ⟶ FÉt_Y`.
* `fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful`,
  `fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful_of_dualSections`,
  `bijective_map_finiteEtaleBaseChange_of_completionFullyFaithful`: the same conclusion under
  additional hypotheses.

## Implementation notes

A section of a finite étale cover `U` of `X` along `g : T ⟶ X` is the subtype
`{s : T ⟶ U.left // s ≫ U.hom = g}`.

## References

* [Stacks Project, Tag 0BL7](https://stacks.math.columbia.edu/tag/0BL7)
* [Stacks Project, Tag 0BQB](https://stacks.math.columbia.edu/tag/0BQB)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-! ### Sections of a finite étale cover -/

/-- The finite étale cover of `X` by `X` itself, through the identity morphism. -/
public def selfFiniteEtaleOver (X : Scheme.{u}) : FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩

/-- The structure morphism of the cover of `X` by itself is the identity of `X`. -/
private theorem selfFiniteEtaleOver_hom (X : Scheme.{u}) :
    (selfFiniteEtaleOver X).hom = 𝟙 X :=
  rfl

/-- Sections of the base change of `U` along `g` over a morphism `h` are the sections of `U`
itself over the composite `h ≫ g`. -/
private def pullbackSectionEquiv {X T Z : Scheme.{u}} (U : FiniteEtaleOver X) (g : T ⟶ X)
    (h : Z ⟶ T) (k : Z ⟶ X) (hk : h ≫ g = k) :
    {σ : Z ⟶ ((finiteEtaleBaseChange g).obj U).left //
        σ ≫ ((finiteEtaleBaseChange g).obj U).hom = h} ≃
      {s : Z ⟶ U.left // s ≫ U.hom = k} where
  toFun σ := ⟨σ.1 ≫ finiteEtaleBaseChangeProj g U, by
    rw [Category.assoc, finiteEtaleBaseChangeProj_comp_hom, ← Category.assoc, σ.2]
    exact hk⟩
  invFun s := ⟨baseChangeLift U g (show s.1 ≫ U.hom = h ≫ g by rw [s.2, hk]),
    baseChangeLift_hom _ _ _⟩
  left_inv σ := Subtype.ext (finiteEtaleBaseChangeProj_hom_ext g U
    (by rw [baseChangeLift_proj]) (by rw [baseChangeLift_hom, σ.2]))
  right_inv s := Subtype.ext (baseChangeLift_proj _ _ _)

/-- The morphism of base-changed covers along `j` determined by a section of `V` over `j`, with
source the base change of the cover of `T` by itself. -/
private def baseChangeSelfHom {T Y : Scheme.{u}} (j : Y ⟶ T) (V : FiniteEtaleOver T)
    {τ : Y ⟶ V.left} (hτ : τ ≫ V.hom = j) :
    (finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T) ⟶ (finiteEtaleBaseChange j).obj V :=
  MorphismProperty.Over.homMk
    (baseChangeLift V j
      (show (((finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T)).hom ≫ τ) ≫ V.hom
          = ((finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T)).hom ≫ j by
        rw [Category.assoc, hτ]))
    (baseChangeLift_hom _ _ _)

/-- The underlying morphism of `baseChangeSelfHom`, followed by the projection to the cover, is
the given section composed with the structure morphism. -/
private theorem baseChangeSelfHom_left_proj {T Y : Scheme.{u}} (j : Y ⟶ T)
    (V : FiniteEtaleOver T) {τ : Y ⟶ V.left} (hτ : τ ≫ V.hom = j) :
    (baseChangeSelfHom j V hτ).left ≫ finiteEtaleBaseChangeProj j V
      = ((finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T)).hom ≫ τ :=
  baseChangeLift_proj _ _ _

/-- The structure morphism of the base change along `j` of the cover of `T` by itself is an
isomorphism. -/
private theorem isIso_selfFiniteEtaleOver_baseChange_hom {T Y : Scheme.{u}} (j : Y ⟶ T) :
    IsIso (((finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T)).hom) :=
  inferInstanceAs (IsIso (pullback.snd (𝟙 T) j))

/-- The projection from the base change along `j` of the cover of `T` by itself is its structure
morphism followed by `j`. -/
private theorem selfFiniteEtaleOver_baseChange_proj {T Y : Scheme.{u}} (j : Y ⟶ T) :
    finiteEtaleBaseChangeProj j (selfFiniteEtaleOver T)
      = ((finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T)).hom ≫ j :=
  (Category.comp_id _).symm.trans
    (finiteEtaleBaseChangeProj_comp_hom j (selfFiniteEtaleOver T))

/-- A morphism out of `T` precomposed with the projection from the base change of the cover of
`T` by itself factors through the structure morphism of that base change. -/
private theorem selfFiniteEtaleOver_baseChange_proj_comp {T Y Z : Scheme.{u}} (j : Y ⟶ T)
    (m : T ⟶ Z) :
    finiteEtaleBaseChangeProj j (selfFiniteEtaleOver T) ≫ m
      = ((finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T)).hom ≫ j ≫ m :=
  (congrArg (fun p => p ≫ m) (selfFiniteEtaleOver_baseChange_proj j)).trans
    (Category.assoc _ _ _)

/-- If base change along `j : Y ⟶ T` is fully faithful on finite étale covers, then for every
finite étale cover `U` of `X` and every `g : T ⟶ X` the sections of `U` over `g` restrict
bijectively to the sections of `U` over `j ≫ g`. -/
public theorem bijective_restrictSection_of_fullyFaithful {X T Y : Scheme.{u}} (g : T ⟶ X)
    (j : Y ⟶ T) (k : Y ⟶ X) (hk : j ≫ g = k)
    (hj : (finiteEtaleBaseChange j).FullyFaithful) (U : FiniteEtaleOver X) :
    Function.Bijective (fun s : {s : T ⟶ U.left // s ≫ U.hom = g} =>
      (⟨j ≫ s.1, by rw [Category.assoc, s.2, hk]⟩ : {t : Y ⟶ U.left // t ≫ U.hom = k})) := by
  have hepi : Epi (((finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T)).hom) := by
    have := isIso_selfFiniteEtaleOver_baseChange_hom j
    infer_instance
  have hbase : ∀ V : FiniteEtaleOver T, Function.Bijective
      (fun σ : {σ : T ⟶ V.left // σ ≫ V.hom = 𝟙 T} =>
        (⟨j ≫ σ.1, by rw [Category.assoc, σ.2, Category.comp_id]⟩ :
          {τ : Y ⟶ V.left // τ ≫ V.hom = j})) := by
    intro V
    refine ⟨?_, ?_⟩
    · intro σ₁ σ₂ hσ
      have hv : j ≫ σ₁.1 = j ≫ σ₂.1 := congrArg Subtype.val hσ
      have hmap : (finiteEtaleBaseChange j).map
            (MorphismProperty.Over.homMk σ₁.1 σ₁.2 : selfFiniteEtaleOver T ⟶ V)
          = (finiteEtaleBaseChange j).map
            (MorphismProperty.Over.homMk σ₂.1 σ₂.2 : selfFiniteEtaleOver T ⟶ V) := by
        refine finiteEtaleOver_hom_ext j ?_
        rw [finiteEtaleBaseChangeProj_naturality, finiteEtaleBaseChangeProj_naturality]
        show finiteEtaleBaseChangeProj j (selfFiniteEtaleOver T) ≫ σ₁.1
          = finiteEtaleBaseChangeProj j (selfFiniteEtaleOver T) ≫ σ₂.1
        rw [selfFiniteEtaleOver_baseChange_proj_comp,
          selfFiniteEtaleOver_baseChange_proj_comp, hv]
      exact Subtype.ext (congrArg (fun m => m.left) (hj.map_injective hmap))
    · intro τ
      refine ⟨⟨(hj.preimage (baseChangeSelfHom j V τ.2)).left,
        (MorphismProperty.Over.w (hj.preimage (baseChangeSelfHom j V τ.2))).trans
          (selfFiniteEtaleOver_hom T)⟩, ?_⟩
      refine Subtype.ext ?_
      show j ≫ (hj.preimage (baseChangeSelfHom j V τ.2)).left = τ.1
      have hkey : finiteEtaleBaseChangeProj j (selfFiniteEtaleOver T) ≫
            (hj.preimage (baseChangeSelfHom j V τ.2)).left
          = ((finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T)).hom ≫ τ.1 := by
        rw [← finiteEtaleBaseChangeProj_naturality j (hj.preimage (baseChangeSelfHom j V τ.2)),
          hj.map_preimage]
        exact baseChangeSelfHom_left_proj j V τ.2
      refine (cancel_epi (((finiteEtaleBaseChange j).obj (selfFiniteEtaleOver T)).hom)).mp ?_
      exact (selfFiniteEtaleOver_baseChange_proj_comp j
        (hj.preimage (baseChangeSelfHom j V τ.2)).left).symm.trans hkey
  have key : (fun s : {s : T ⟶ U.left // s ≫ U.hom = g} =>
        (⟨j ≫ s.1, by rw [Category.assoc, s.2, hk]⟩ :
          {t : Y ⟶ U.left // t ≫ U.hom = k}))
      = (pullbackSectionEquiv U g j k hk) ∘
          (fun σ : {σ : T ⟶ ((finiteEtaleBaseChange g).obj U).left //
              σ ≫ ((finiteEtaleBaseChange g).obj U).hom = 𝟙 T} =>
            (⟨j ≫ σ.1, by rw [Category.assoc, σ.2, Category.comp_id]⟩ :
              {τ : Y ⟶ ((finiteEtaleBaseChange g).obj U).left //
                τ ≫ ((finiteEtaleBaseChange g).obj U).hom = j})) ∘
          (pullbackSectionEquiv U g (𝟙 T) g (Category.id_comp g)).symm := by
    refine funext fun s => Subtype.ext ?_
    show j ≫ s.1 = (j ≫ baseChangeLift U g _) ≫ finiteEtaleBaseChangeProj g U
    rw [Category.assoc, baseChangeLift_proj]
  rw [key]
  exact (pullbackSectionEquiv U g j k hk).bijective.comp
    ((hbase _).comp (pullbackSectionEquiv U g (𝟙 T) g (Category.id_comp g)).symm.bijective)

/-! ### The converse -/

/-- A morphism of `X`-schemes out of `T`, viewed over `X` by `g`, is a morphism of schemes whose
composite with the structure morphism of the target is `g`. -/
private def overHomEquivSection {X T : Scheme.{u}} (W : Over X) (g : T ⟶ X) :
    ((Over.mk g : Over X) ⟶ W) ≃ {s : T ⟶ W.left // s ≫ W.hom = g} where
  toFun u := ⟨u.left, Over.w u⟩
  invFun s := Over.homMk s.1 s.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- If for every finite étale cover `W` of `X` the sections of `W` over `X` restrict bijectively to
the sections of `W` over `i : Y ⟶ X`, then base change along `i` is fully faithful on finite étale
covers. -/
public theorem fullyFaithful_finiteEtaleBaseChange_of_bijective_restrictSection
    {X Y : Scheme.{u}} (i : Y ⟶ X)
    (h : ∀ W : FiniteEtaleOver X, Function.Bijective
      (fun s : {s : X ⟶ W.left // s ≫ W.hom = 𝟙 X} =>
        (⟨i ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ :
          {t : Y ⟶ W.left // t ≫ W.hom = i}))) :
    Nonempty (finiteEtaleBaseChange i).FullyFaithful := by
  have key : ∀ A B : FiniteEtaleOver X,
      Function.Bijective (fun φ : A ⟶ B => (finiteEtaleBaseChange i).map φ) := by
    intro A B
    have _ : IsFinite (Over.mk A.hom : Over X).hom := A.prop.1
    have _ : Etale (Over.mk A.hom : Over X).hom := A.prop.2
    have _ : IsFinite (Over.mk B.hom : Over X).hom := B.prop.1
    have _ : Etale (Over.mk B.hom : Over X).hom := B.prop.2
    obtain ⟨W, hWfin, hWet, ⟨e⟩⟩ :=
      exists_finiteEtale_internalHom X (Over.mk A.hom) (Over.mk B.hom)
    have hprecomp : Function.Bijective
        (fun u : (Over.mk (𝟙 X) : Over X) ⟶ W => overToSelf i ≫ u) := by
      have hW := h (MorphismProperty.Over.mk ⊤ W.hom ⟨hWfin, hWet⟩)
      have hcomp : (fun u : (Over.mk (𝟙 X) : Over X) ⟶ W => overToSelf i ≫ u)
          = (overHomEquivSection W i).symm ∘
              (fun s : {s : X ⟶ W.left // s ≫ W.hom = 𝟙 X} =>
                (⟨i ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ :
                  {t : Y ⟶ W.left // t ≫ W.hom = i})) ∘
              (overHomEquivSection W (𝟙 X)) :=
        funext fun _ => Over.OverMorphism.ext rfl
      rw [hcomp]
      exact (overHomEquivSection W i).symm.bijective.comp
        (hW.comp (overHomEquivSection W (𝟙 X)).bijective)
    have hmid : Function.Bijective
        (fun ξ : (Over.mk A.hom ⨯ Over.mk (𝟙 X) : Over X) ⟶ Over.mk B.hom =>
          prod.map (𝟙 (Over.mk A.hom : Over X)) (overToSelf i) ≫ ξ) := by
      have hcomp : ((fun ξ : (Over.mk A.hom ⨯ Over.mk (𝟙 X) : Over X) ⟶ Over.mk B.hom =>
            prod.map (𝟙 (Over.mk A.hom : Over X)) (overToSelf i) ≫ ξ) ∘
            (Iso.toEquiv (e.app (Opposite.op (Over.mk (𝟙 X) : Over X)))))
          = ((Iso.toEquiv (e.app (Opposite.op (Over.mk i : Over X)))) ∘
            (fun u : (Over.mk (𝟙 X) : Over X) ⟶ W => overToSelf i ≫ u)) :=
        funext fun u => (NatTrans.naturality_apply e.hom (overToSelf i).op u).symm
      have h1 := (Iso.toEquiv (e.app (Opposite.op (Over.mk (𝟙 X) : Over X)))).bijective
      have h2 := (Iso.toEquiv (e.app (Opposite.op (Over.mk i : Over X)))).bijective
      have hrhs := h2.comp hprecomp
      rw [← hcomp] at hrhs
      exact (Function.Bijective.of_comp_iff _ h1).mp hrhs
    have hcomp : (fun φ : A ⟶ B => (finiteEtaleBaseChange i).map φ)
        = (prodHomEquivBaseChangeHom A B i) ∘
            (fun ξ : (Over.mk A.hom ⨯ Over.mk (𝟙 X) : Over X) ⟶ Over.mk B.hom =>
              prod.map (𝟙 (Over.mk A.hom : Over X)) (overToSelf i) ≫ ξ) ∘
            (prodSelfHomEquiv A B).symm := by
      refine funext fun φ => ?_
      have hpm := prodHomEquivBaseChangeHom_prod_map i A B ((prodSelfHomEquiv A B).symm φ)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hpm.symm
    rw [hcomp]
    exact (prodHomEquivBaseChangeHom A B i).bijective.comp
      (hmid.comp (prodSelfHomEquiv A B).symm.bijective)
  have _ : (finiteEtaleBaseChange i).Faithful := ⟨fun hfg => (key _ _).1 hfg⟩
  have _ : (finiteEtaleBaseChange i).Full := ⟨fun f => (key _ _).2 f⟩
  exact ⟨.ofFullyFaithful _⟩

/-! ### The infinitesimal neighbourhoods -/

open Stacks.Thickenings in
/-- Sections of a finite étale cover of `X` over the `n`-th infinitesimal neighbourhood of a closed
subscheme `Y` restrict bijectively to sections over `Y`. -/
public theorem bijective_restrictSection_nthOrderInclusion {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (U : FiniteEtaleOver X) (n : ℕ) :
    Function.Bijective
      (fun s : {s : nthOrderInfinitesimalNeighbourhood i n ⟶ U.left //
          s ≫ U.hom = nthOrderToBase i n} =>
        (⟨nthOrderInclusion i n ≫ s.1, by rw [Category.assoc, s.2, nthOrderInclusion_toBase]⟩ :
          {t : Y ⟶ U.left // t ≫ U.hom = i})) := by
  have _ := finiteEtaleBaseChange_isEquivalence_of_isThickening (nthOrderInclusion i n)
    (nthOrderInclusion_isThickening i n)
  exact bijective_restrictSection_of_fullyFaithful (nthOrderToBase i n) (nthOrderInclusion i n) i
    (nthOrderInclusion_toBase i n) (.ofFullyFaithful _) U

/-! ### Full faithfulness from completion -/

section Completion

open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence Stacks.Thickenings
open Stacks.Algebraization (nthInfinitesimalNeighbourhoodTransition
  nthInfinitesimalNeighbourhoodOver)

/-- The structure sheaf of `X` as a sheaf of `𝒪_X`-algebras: the direct image of the structure
sheaf along the identity. -/
public abbrev unitAlgebra (X : Scheme.{u}) : AlgebraSheaf X :=
  pushforwardAlgebra (Over.mk (𝟙 X) : Over X).hom

/-- The direct image of the structure sheaf of the `n`-th infinitesimal neighbourhood of a
closed subscheme `Y ⊆ X`, as a sheaf of `𝒪_X`-algebras. -/
public abbrev nthOrderAlgebra {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    AlgebraSheaf X :=
  pushforwardAlgebra (nthInfinitesimalNeighbourhoodOver i n).hom

/-- The canonical morphism of sheaves of `𝒪_X`-algebras from `𝒪_X` to the direct image of the
structure sheaf of the `n`-th infinitesimal neighbourhood, induced by the structure morphism of
that neighbourhood as a scheme over `X`. -/
public def nthOrderAlgebraRestriction {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    (n : ℕ) : unitAlgebra X ⟶ nthOrderAlgebra i n :=
  pushforwardAlgebraMap
    (Over.homMk (nthOrderToBase i n) (Category.comp_id (nthOrderToBase i n)) :
      nthInfinitesimalNeighbourhoodOver i n ⟶ Over.mk (𝟙 X))

/-- The transition morphism of direct image algebras from the `(n+1)`-st to the `n`-th
infinitesimal neighbourhood, induced by the inclusion of the smaller neighbourhood into the
larger one as schemes over `X`. -/
public def nthOrderAlgebraTransition {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    (n : ℕ) : nthOrderAlgebra i n.succ ⟶ nthOrderAlgebra i n :=
  pushforwardAlgebraMap (nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n))

/-- The underlying morphism of `𝒪_X`-modules of `nthOrderAlgebraRestriction`: the canonical map
from the structure sheaf of `X` to the direct image of the structure sheaf of the `n`-th
infinitesimal neighbourhood of `Y` in `X`. -/
public def nthOrderUnitMap {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    SheafOfModules.unit X.ringCatSheaf ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra i n) :=
  AlgebraSheaf.underlyingModuleMap (nthOrderAlgebraRestriction i n)

/-- The underlying morphism of `𝒪_X`-modules of `nthOrderAlgebraTransition`. -/
public def nthOrderTransitionMap {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    AlgebraSheaf.underlyingModule (nthOrderAlgebra i (n + 1)) ⟶
      AlgebraSheaf.underlyingModule (nthOrderAlgebra i n) :=
  AlgebraSheaf.underlyingModuleMap (nthOrderAlgebraTransition i n)

/-- `nthOrderUnitMap` unfolded to the morphism of direct image algebras it comes from. -/
private theorem nthOrderUnitMap_eq {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    (n : ℕ) :
    nthOrderUnitMap i n =
      AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap
        (Over.homMk (nthOrderToBase i n) (Category.comp_id (nthOrderToBase i n)) :
          nthInfinitesimalNeighbourhoodOver i n ⟶ Over.mk (𝟙 X))) :=
  rfl

/-- `nthOrderTransitionMap` unfolded to the morphism of direct image algebras it comes from. -/
private theorem nthOrderTransitionMap_eq {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    (n : ℕ) :
    nthOrderTransitionMap i n =
      AlgebraSheaf.underlyingModuleMap
        (pushforwardAlgebraMap (nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n))) :=
  rfl

/-- Taking underlying modules is compatible with composition of morphisms of algebra sheaves. -/
private theorem underlyingModuleMap_comp {X : Scheme.{u}} {A B C : AlgebraSheaf X}
    (f : A ⟶ B) (g : B ⟶ C) :
    AlgebraSheaf.underlyingModuleMap (f ≫ g) =
      AlgebraSheaf.underlyingModuleMap f ≫ AlgebraSheaf.underlyingModuleMap g :=
  (AlgebraSheaf.underlyingModuleFunctor X).map_comp f g

/-- A morphism of algebra sheaves is determined by its underlying morphism of modules. -/
private theorem underlyingModuleMap_injective {X : Scheme.{u}} {A B : AlgebraSheaf X}
    {f g : A ⟶ B}
    (h : AlgebraSheaf.underlyingModuleMap f = AlgebraSheaf.underlyingModuleMap g) : f = g := by
  have happ : ∀ (U : (X.Opens)ᵒᵖ) (x : (A.right.obj.obj U : Type u)),
      (f.right.hom.app U).hom x = (g.right.hom.app U).hom x := fun U x =>
    congrArg (fun φ : AlgebraSheaf.underlyingModule A ⟶ AlgebraSheaf.underlyingModule B =>
      φ.val.app U x) h
  refine Under.UnderMorphism.ext (Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_)))
  exact CommRingCat.hom_ext (RingHom.ext (happ U))

/-- The sections of a morphism `f : V ⟶ X` affine over `X` over an `X`-scheme `G` are the morphisms
of sheaves of `𝒪_X`-algebras `f _* 𝒪_V ⟶ G.hom _* 𝒪_{G.left}`. -/
private noncomputable def sectionAlgebraEquiv {X V : Scheme.{u}} (f : V ⟶ X) [IsAffineHom f]
    (G : Over X) :
    {s : G.left ⟶ V // s ≫ f = G.hom} ≃
      (pushforwardAlgebra (Over.mk f : Over X).hom ⟶ pushforwardAlgebra G.hom) :=
  haveI : IsAffineHom (Over.mk f : Over X).hom := ‹IsAffineHom f›
  (overHomEquivSection (Over.mk f) G.hom).symm.trans (overHomEquivAlgebraHom G (Over.mk f))

/-- `sectionAlgebraEquiv` is the canonical map on pushed-forward structure sheaves. -/
private theorem sectionAlgebraEquiv_apply {X V : Scheme.{u}} (f : V ⟶ X) [IsAffineHom f]
    (G : Over X) (s : {s : G.left ⟶ V // s ≫ f = G.hom}) :
    sectionAlgebraEquiv f G s =
      pushforwardAlgebraMap (Over.homMk s.1 s.2 : G ⟶ Over.mk f) :=
  have : IsAffineHom (Over.mk f : Over X).hom := ‹IsAffineHom f›
  overHomEquivAlgebraHom_apply ((overHomEquivSection (Over.mk f) G.hom).symm s)

/-- Under `sectionAlgebraEquiv`, restricting a section along a morphism `k` of `X`-schemes is
composition with the canonical morphism of direct image algebras attached to `k`. -/
private theorem sectionAlgebraEquiv_restrict {X V : Scheme.{u}} (f : V ⟶ X) [IsAffineHom f]
    {G G' : Over X} (k : G' ⟶ G) (s : {s : G.left ⟶ V // s ≫ f = G.hom})
    (s' : {s : G'.left ⟶ V // s ≫ f = G'.hom}) (hs' : s'.1 = k.left ≫ s.1) :
    sectionAlgebraEquiv f G' s' = sectionAlgebraEquiv f G s ≫ pushforwardAlgebraMap k := by
  have h1 : (Over.homMk s'.1 s'.2 : G' ⟶ Over.mk f) =
      k ≫ (Over.homMk s.1 s.2 : G ⟶ Over.mk f) :=
    Over.OverMorphism.ext hs'
  rw [sectionAlgebraEquiv_apply, sectionAlgebraEquiv_apply, h1, pushforwardAlgebraMap_comp]

/-- `sectionAlgebraEquiv_restrict`, read on the underlying modules. -/
private theorem underlyingModuleMap_sectionAlgebraEquiv_restrict {X V : Scheme.{u}} (f : V ⟶ X)
    [IsAffineHom f] {G G' : Over X} (k : G' ⟶ G) (s : {s : G.left ⟶ V // s ≫ f = G.hom})
    (s' : {s : G'.left ⟶ V // s ≫ f = G'.hom}) (hs' : s'.1 = k.left ≫ s.1) :
    AlgebraSheaf.underlyingModuleMap (sectionAlgebraEquiv f G' s') =
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraEquiv f G s) ≫
        AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap k) := by
  rw [sectionAlgebraEquiv_restrict f k s s' hs', underlyingModuleMap_comp]

/-- The restriction of a section over `X` to the `n`-th infinitesimal neighbourhood, read on the
underlying modules: it is composition with `nthOrderUnitMap`. -/
private theorem underlyingModuleMap_sectionAlgebraEquiv_nthOrder {X Y V : Scheme.{u}}
    (i : Y ⟶ X) [IsClosedImmersion i] (f : V ⟶ X) [IsAffineHom f] (n : ℕ)
    (s : {s : X ⟶ V // s ≫ f = 𝟙 X})
    (s' : {t : nthOrderInfinitesimalNeighbourhood i n ⟶ V // t ≫ f = nthOrderToBase i n})
    (hs' : s'.1 = nthOrderToBase i n ≫ s.1) :
    AlgebraSheaf.underlyingModuleMap
        (sectionAlgebraEquiv f (nthInfinitesimalNeighbourhoodOver i n) s') =
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraEquiv f (Over.mk (𝟙 X)) s) ≫
        nthOrderUnitMap i n := by
  rw [nthOrderUnitMap_eq]
  exact underlyingModuleMap_sectionAlgebraEquiv_restrict f
    (Over.homMk (nthOrderToBase i n) (Category.comp_id (nthOrderToBase i n)) :
      nthInfinitesimalNeighbourhoodOver i n ⟶ Over.mk (𝟙 X)) s s' hs'

/-- The structure morphism of the `(n+1)`-st infinitesimal neighbourhood, precomposed with the
inclusion of the `n`-th, is the structure morphism of the `n`-th. -/
private theorem transition_comp_nthOrderToBase {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    (nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n)).left ≫
        nthOrderToBase i (n + 1) = nthOrderToBase i n :=
  Over.w (nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n))

/-- The inclusion of `Y` into the `n`-th infinitesimal neighbourhood, followed by the inclusion of
that neighbourhood into the `(n+1)`-st, is the inclusion of `Y` into the `(n+1)`-st. -/
private theorem nthOrderInclusion_transition {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    nthOrderInclusion i n ≫
        (nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n)).left =
      nthOrderInclusion i (n + 1) := by
  have h1 : (nthOrderInclusion i n ≫
      (nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n)).left) ≫
      nthOrderToBase i (n + 1) = i :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => nthOrderInclusion i n ≫ k)
        (transition_comp_nthOrderToBase i n)).trans (nthOrderInclusion_toBase i n))
  have h2 : nthOrderInclusion i (n + 1) ≫ nthOrderToBase i (n + 1) = i :=
    nthOrderInclusion_toBase i (n + 1)
  have _ : Mono (nthOrderToBase i (n + 1)) := inferInstance
  exact (cancel_mono (nthOrderToBase i (n + 1))).mp (h1.trans h2.symm)

/-- Restriction of a section over `X` to `Y` factors through the `n`-th infinitesimal
neighbourhood of `Y`. -/
private theorem restrictSection_factor {X Y V : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    (f : V ⟶ X) (n : ℕ) (s : {s : X ⟶ V // s ≫ f = 𝟙 X})
    (s' : {t : nthOrderInfinitesimalNeighbourhood i n ⟶ V // t ≫ f = nthOrderToBase i n})
    (hs' : s'.1 = nthOrderToBase i n ≫ s.1) :
    (⟨i ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ :
        {t : Y ⟶ V // t ≫ f = i}) =
      ⟨nthOrderInclusion i n ≫ s'.1, by
        rw [Category.assoc, s'.2, nthOrderInclusion_toBase]⟩ :=
  Subtype.ext
    ((((congrArg (fun k => k ≫ s.1) (nthOrderInclusion_toBase i n)).symm).trans
        (Category.assoc _ _ _)).trans
      (congrArg (fun z => nthOrderInclusion i n ≫ z) hs'.symm))

/-- A section over `X` restricts to a section over the `n`-th infinitesimal neighbourhood of `Y`.
-/
private theorem restrictSection_nthOrder_exists {X Y V : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (f : V ⟶ X) (n : ℕ) (s : {s : X ⟶ V // s ≫ f = 𝟙 X}) :
    ∃ s' : {t : nthOrderInfinitesimalNeighbourhood i n ⟶ V // t ≫ f = nthOrderToBase i n},
      s'.1 = nthOrderToBase i n ≫ s.1 :=
  ⟨⟨nthOrderToBase i n ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩, rfl⟩

/-- Let `f : V ⟶ X` be affine. If the sections of `f` over each infinitesimal neighbourhood of `Y`
restrict bijectively to sections over `Y`, and morphisms of modules `f _* 𝒪_V ⟶ 𝒪_X` are determined
by their composites with the maps `nthOrderUnitMap i n`, then the sections of `f` over `X` restrict
injectively to sections over `Y`. -/
private theorem injective_restrictSection_of_bridge {X Y V : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (f : V ⟶ X) [IsAffineHom f]
    (hrn : ∀ n : ℕ, Function.Bijective
      (fun t : {t : nthOrderInfinitesimalNeighbourhood i n ⟶ V //
          t ≫ f = nthOrderToBase i n} =>
        (⟨nthOrderInclusion i n ≫ t.1, by
            rw [Category.assoc, t.2, nthOrderInclusion_toBase]⟩ :
          {t : Y ⟶ V // t ≫ f = i})))
    (hinj : ∀ φ ψ : AlgebraSheaf.underlyingModule
        (pushforwardAlgebra (Over.mk f : Over X).hom) ⟶ SheafOfModules.unit X.ringCatSheaf,
      (∀ n : ℕ, φ ≫ nthOrderUnitMap i n = ψ ≫ nthOrderUnitMap i n) → φ = ψ) :
    Function.Injective
      (fun s : {s : X ⟶ V // s ≫ f = 𝟙 X} =>
        (⟨i ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ :
          {t : Y ⟶ V // t ≫ f = i})) := by
  intro s s' hss
  refine (sectionAlgebraEquiv f (Over.mk (𝟙 X))).injective
    (underlyingModuleMap_injective (hinj _ _ fun n => ?_))
  obtain ⟨a, ha⟩ := restrictSection_nthOrder_exists i f n s
  obtain ⟨b, hb⟩ := restrictSection_nthOrder_exists i f n s'
  have hab : a = b :=
    (hrn n).1 (((restrictSection_factor i f n s a ha).symm.trans hss).trans
      (restrictSection_factor i f n s' b hb))
  refine ((underlyingModuleMap_sectionAlgebraEquiv_nthOrder i f n s a ha).symm.trans ?_).trans
    (underlyingModuleMap_sectionAlgebraEquiv_nthOrder i f n s' b hb)
  exact congrArg (fun z => AlgebraSheaf.underlyingModuleMap
    (sectionAlgebraEquiv f (nthInfinitesimalNeighbourhoodOver i n) z)) hab

/-- Let `f : V ⟶ X` be affine. Suppose the sections of `f` over each infinitesimal neighbourhood of
`Y` restrict bijectively to sections over `Y`, every compatible system of morphisms of modules from
`f _* 𝒪_V` to the modules underlying `nthOrderAlgebra i n` comes from a morphism `f _* 𝒪_V ⟶ 𝒪_X`,
and a morphism of modules `f _* 𝒪_V ⟶ 𝒪_X` whose composites with the maps
`nthOrderAlgebraRestriction i n` are morphisms of algebra sheaves is itself one. Then the sections
of `f` over `X` restrict surjectively to sections over `Y`. -/
private theorem surjective_restrictSection_of_bridge {X Y V : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (f : V ⟶ X) [IsAffineHom f]
    (hrn : ∀ n : ℕ, Function.Bijective
      (fun t : {t : nthOrderInfinitesimalNeighbourhood i n ⟶ V //
          t ≫ f = nthOrderToBase i n} =>
        (⟨nthOrderInclusion i n ≫ t.1, by
            rw [Category.assoc, t.2, nthOrderInclusion_toBase]⟩ :
          {t : Y ⟶ V // t ≫ f = i})))
    (hsurj : ∀ α : ∀ n : ℕ, AlgebraSheaf.underlyingModule
        (pushforwardAlgebra (Over.mk f : Over X).hom) ⟶
          AlgebraSheaf.underlyingModule (nthOrderAlgebra i n),
      (∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap i n = α n) →
      ∃ φ : AlgebraSheaf.underlyingModule (pushforwardAlgebra (Over.mk f : Over X).hom) ⟶
          SheafOfModules.unit X.ringCatSheaf,
        ∀ n : ℕ, φ ≫ nthOrderUnitMap i n = α n)
    (hmul : ∀ (φ : AlgebraSheaf.underlyingModule
        (pushforwardAlgebra (Over.mk f : Over X).hom) ⟶
          AlgebraSheaf.underlyingModule (unitAlgebra X)),
      (∀ n : ℕ, ∃ ψ : pushforwardAlgebra (Over.mk f : Over X).hom ⟶ nthOrderAlgebra i n,
        AlgebraSheaf.underlyingModuleMap ψ =
          φ ≫ AlgebraSheaf.underlyingModuleMap (nthOrderAlgebraRestriction i n)) →
      ∃ ψ : pushforwardAlgebra (Over.mk f : Over X).hom ⟶ unitAlgebra X,
        AlgebraSheaf.underlyingModuleMap ψ = φ) :
    Function.Surjective
      (fun s : {s : X ⟶ V // s ≫ f = 𝟙 X} =>
        (⟨i ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ :
          {t : Y ⟶ V // t ≫ f = i})) := by
  intro t
  have hex : ∀ n : ℕ, ∃ a : {t : nthOrderInfinitesimalNeighbourhood i n ⟶ V //
      t ≫ f = nthOrderToBase i n},
      (⟨nthOrderInclusion i n ≫ a.1, by
        rw [Category.assoc, a.2, nthOrderInclusion_toBase]⟩ :
          {t : Y ⟶ V // t ≫ f = i}) = t := fun n => (hrn n).2 t
  choose tn htn using hex
  have hstep : ∀ n : ℕ, (tn n).1 =
      (nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n)).left ≫ (tn (n + 1)).1 := by
    intro n
    have hval : nthOrderInclusion i n ≫
        ((nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n)).left ≫
          (tn (n + 1)).1) = nthOrderInclusion i (n + 1) ≫ (tn (n + 1)).1 :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ (tn (n + 1)).1) (nthOrderInclusion_transition i n))
    have hmem : ((nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n)).left ≫
        (tn (n + 1)).1) ≫ f = nthOrderToBase i n :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => (nthInfinitesimalNeighbourhoodTransition i
            (Nat.le_succ n)).left ≫ z) (tn (n + 1)).2).trans
          (transition_comp_nthOrderToBase i n))
    have hx : (⟨(nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n)).left ≫
          (tn (n + 1)).1, hmem⟩ :
        {t : nthOrderInfinitesimalNeighbourhood i n ⟶ V //
          t ≫ f = nthOrderToBase i n}) = tn n :=
      (hrn n).1 ((Subtype.ext hval).trans ((htn (n + 1)).trans (htn n).symm))
    exact (congrArg Subtype.val hx).symm
  have hcompat : ∀ n : ℕ,
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraEquiv f
            (nthInfinitesimalNeighbourhoodOver i (n + 1)) (tn (n + 1))) ≫
          nthOrderTransitionMap i n =
        AlgebraSheaf.underlyingModuleMap (sectionAlgebraEquiv f
          (nthInfinitesimalNeighbourhoodOver i n) (tn n)) := by
    intro n
    rw [nthOrderTransitionMap_eq]
    exact (underlyingModuleMap_sectionAlgebraEquiv_restrict f
      (nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n)) (tn (n + 1)) (tn n)
      (hstep n)).symm
  obtain ⟨σ, hσ⟩ := hsurj
    (fun n => AlgebraSheaf.underlyingModuleMap
      (sectionAlgebraEquiv f (nthInfinitesimalNeighbourhoodOver i n) (tn n))) hcompat
  obtain ⟨ψ, hψ⟩ := hmul σ fun n =>
    ⟨sectionAlgebraEquiv f (nthInfinitesimalNeighbourhoodOver i n) (tn n), (hσ n).symm⟩
  refine ⟨(sectionAlgebraEquiv f (Over.mk (𝟙 X))).symm ψ, ?_⟩
  obtain ⟨a, ha⟩ := restrictSection_nthOrder_exists i f 0
    ((sectionAlgebraEquiv f (Over.mk (𝟙 X))).symm ψ)
  have hψ' : sectionAlgebraEquiv f (Over.mk (𝟙 X))
      ((sectionAlgebraEquiv f (Over.mk (𝟙 X))).symm ψ) = ψ :=
    (sectionAlgebraEquiv f (Over.mk (𝟙 X))).apply_symm_apply ψ
  have hzero : a = tn 0 := by
    refine (sectionAlgebraEquiv f (nthInfinitesimalNeighbourhoodOver i 0)).injective
      (underlyingModuleMap_injective ?_)
    refine (underlyingModuleMap_sectionAlgebraEquiv_nthOrder i f 0
      ((sectionAlgebraEquiv f (Over.mk (𝟙 X))).symm ψ) a ha).trans ?_
    rw [hψ', hψ]
    exact hσ 0
  refine ((restrictSection_factor i f 0
    ((sectionAlgebraEquiv f (Over.mk (𝟙 X))).symm ψ) a ha).trans ?_).trans (htn 0)
  exact congrArg (fun z : {t : nthOrderInfinitesimalNeighbourhood i 0 ⟶ V //
      t ≫ f = nthOrderToBase i 0} =>
    (⟨nthOrderInclusion i 0 ≫ z.1, by
      rw [Category.assoc, z.2, nthOrderInclusion_toBase]⟩ :
        {t : Y ⟶ V // t ≫ f = i})) hzero

/-- Over a Noetherian scheme, if completion along the ideal sheaf of `i` is fully faithful on the
finite locally free objects, then the dual of every coherent finite locally free module is
infinitesimally section complete. -/
private theorem isInfinitesimalSectionsComplete_dualSheaf_of_completionFullyFaithful
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i]
    (hcompletion : Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X i.ker)
    (P : X.Modules) (hPf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} P)
    (hPc : _root_.SheafOfModules.IsCoherent P) :
    Stacks.Algebraization.IsInfinitesimalSectionsComplete i
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf P) :=
  Stacks.Algebraization.isInfinitesimalSectionsComplete_of_completionFullyFaithful i
    hcompletion
    (Stacks.Algebraization.internalHomCoherent X ⟨P, hPc⟩
      (Stacks.Algebraization.unitCoherentModule X))
    (Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf P hPf)

/-- Restriction `FÉt_X ⟶ FÉt_Y` is fully faithful if, for the direct image `M` of the structure
sheaf of every finite étale cover of `X`, the morphisms of modules out of each coherent finite
locally free module into `𝒪_X` satisfy `hdual`, and a module map `M ⟶ 𝒪_X` that is
algebra-like on every infinitesimal neighbourhood is a morphism of algebra sheaves (`hmul`). -/
private theorem fullyFaithful_finiteEtaleBaseChange_of_dualSections_bridge {X Y : Scheme.{u}}
    (i : Y ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i]
    (hdual : ∀ N : X.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N →
      _root_.SheafOfModules.IsCoherent N →
      (∀ φ ψ : N ⟶ SheafOfModules.unit X.ringCatSheaf,
          (∀ n : ℕ, φ ≫ nthOrderUnitMap i n = ψ ≫ nthOrderUnitMap i n) → φ = ψ) ∧
        ∀ α : ∀ n : ℕ, N ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra i n),
          (∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap i n = α n) →
          ∃ φ : N ⟶ SheafOfModules.unit X.ringCatSheaf,
            ∀ n : ℕ, φ ≫ nthOrderUnitMap i n = α n)
    (hmul : ∀ {V : Scheme.{u}} (f : V ⟶ X) [IsAffineHom f],
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (Over.mk f : Over X).hom)) →
      _root_.SheafOfModules.IsCoherent
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (Over.mk f : Over X).hom)) →
      ∀ (φ : AlgebraSheaf.underlyingModule
          (pushforwardAlgebra (Over.mk f : Over X).hom) ⟶
            AlgebraSheaf.underlyingModule (unitAlgebra X)),
      (∀ n : ℕ, ∃ ψ : pushforwardAlgebra (Over.mk f : Over X).hom ⟶ nthOrderAlgebra i n,
        AlgebraSheaf.underlyingModuleMap ψ =
          φ ≫ AlgebraSheaf.underlyingModuleMap (nthOrderAlgebraRestriction i n)) →
      ∃ ψ : pushforwardAlgebra (Over.mk f : Over X).hom ⟶ unitAlgebra X,
        AlgebraSheaf.underlyingModuleMap ψ = φ) :
    Nonempty (finiteEtaleBaseChange i).FullyFaithful := by
  refine fullyFaithful_finiteEtaleBaseChange_of_bijective_restrictSection i fun W => ?_
  have key : ∀ (V : Scheme.{u}) (f : V ⟶ X), IsFinite f → Etale f → Function.Bijective
      (fun s : {s : X ⟶ V // s ≫ f = 𝟙 X} =>
        (⟨i ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ :
          {t : Y ⟶ V // t ≫ f = i})) := by
    intro V f hfin het
    have : IsAffineHom f := inferInstance
    have hMc : _root_.SheafOfModules.IsCoherent
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (Over.mk f : Over X).hom)) :=
      isCoherent_underlyingModule_pushforwardAlgebra f
    have hMf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (Over.mk f : Over X).hom)) :=
      ExtendedEtale.isFiniteLocallyFree_underlyingModule_pushforwardAlgebra f
    obtain ⟨hinj, hsurj⟩ := hdual _ hMf hMc
    have hrn : ∀ n : ℕ, Function.Bijective
        (fun t : {t : nthOrderInfinitesimalNeighbourhood i n ⟶ V //
            t ≫ f = nthOrderToBase i n} =>
          (⟨nthOrderInclusion i n ≫ t.1, by
              rw [Category.assoc, t.2, nthOrderInclusion_toBase]⟩ :
            {t : Y ⟶ V // t ≫ f = i})) := fun n =>
      bijective_restrictSection_nthOrderInclusion i (MorphismProperty.Over.mk ⊤ f ⟨hfin, het⟩) n
    exact ⟨injective_restrictSection_of_bridge i f hrn hinj,
      surjective_restrictSection_of_bridge i f hrn hsurj (hmul f hMf hMc)⟩
  exact key W.left W.hom W.prop.1 W.prop.2

/-- Let `X` be a Noetherian scheme and `Y ⊆ X` a closed subscheme with ideal sheaf `I` such that
the completion functor `Coh(𝒪_X) ⟶ Coh(X, I)` is fully faithful on the finite locally free objects.
Assume `h0GN2`: for a finite locally free module `N` on a scheme `Z` with a closed subscheme `κ`
along which the dual `N^∨` is infinitesimally section complete, the `𝒪_Z`-module maps `N ⟶ 𝒪_Z` are
the compatible systems of maps into the modules underlying `nthOrderAlgebra κ n`. Assume
`halgebra`: a morphism of the underlying modules of algebra sheaves `B` and `C`, with `B` coherent
and finite locally free, which becomes a morphism of algebra sheaves after composition with each
member of a family of morphisms of algebra sheaves out of `C` that is jointly injective on the
morphisms out of coherent finite locally free modules, is a morphism of algebra sheaves. Then the
restriction functor `FÉt_X ⟶ FÉt_Y` is fully faithful. -/
public theorem fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsNoetherian X] [IsClosedImmersion i]
    (hcompletion : Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X i.ker)
    (h0GN2 : ∀ {Z Z' : Scheme.{u}} (κ : Z' ⟶ Z) [IsClosedImmersion κ] (N : Z.Modules),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N →
      Stacks.Algebraization.IsInfinitesimalSectionsComplete κ
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) →
      (∀ φ ψ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
          (∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = ψ ≫ nthOrderUnitMap κ n) → φ = ψ) ∧
        ∀ α : ∀ n : ℕ, N ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra κ n),
          (∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap κ n = α n) →
          ∃ φ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
            ∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = α n)
    (halgebra : ∀ {Z : Scheme.{u}} (B C : AlgebraSheaf Z) (D : ℕ → AlgebraSheaf Z)
      (r : ∀ n : ℕ, C ⟶ D n)
      (φ : AlgebraSheaf.underlyingModule B ⟶ AlgebraSheaf.underlyingModule C),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (AlgebraSheaf.underlyingModule B) →
      _root_.SheafOfModules.IsCoherent (AlgebraSheaf.underlyingModule B) →
      (∀ n : ℕ, ∃ ψ : B ⟶ D n,
        AlgebraSheaf.underlyingModuleMap ψ = φ ≫ AlgebraSheaf.underlyingModuleMap (r n)) →
      (∀ P : Z.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} P →
        _root_.SheafOfModules.IsCoherent P →
        ∀ a b : P ⟶ AlgebraSheaf.underlyingModule C,
          (∀ n : ℕ, a ≫ AlgebraSheaf.underlyingModuleMap (r n) =
            b ≫ AlgebraSheaf.underlyingModuleMap (r n)) → a = b) →
      ∃ ψ : B ⟶ C, AlgebraSheaf.underlyingModuleMap ψ = φ) :
    Nonempty (finiteEtaleBaseChange i).FullyFaithful := by
  have : IsLocallyNoetherian X := inferInstance
  have hsc := isInfinitesimalSectionsComplete_dualSheaf_of_completionFullyFaithful i hcompletion
  refine fullyFaithful_finiteEtaleBaseChange_of_dualSections_bridge i
    (fun P hPf hPc => h0GN2 i P hPf (hsc P hPf hPc)) ?_
  intro V f _ hMf hMc φ hφ
  exact halgebra (pushforwardAlgebra (Over.mk f : Over X).hom) (unitAlgebra X)
    (fun n => nthOrderAlgebra i n) (fun n => nthOrderAlgebraRestriction i n) φ hMf hMc hφ
    fun P hPf hPc a b hab => (h0GN2 i P hPf (hsc P hPf hPc)).1 a b hab

/-- Under the hypotheses of `fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful`,
restriction of finite étale covers along `i` is bijective on every hom set. -/
public theorem bijective_map_finiteEtaleBaseChange_of_completionFullyFaithful
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsNoetherian X] [IsClosedImmersion i]
    (hcompletion : Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X i.ker)
    (h0GN2 : ∀ {Z Z' : Scheme.{u}} (κ : Z' ⟶ Z) [IsClosedImmersion κ] (N : Z.Modules),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N →
      Stacks.Algebraization.IsInfinitesimalSectionsComplete κ
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) →
      (∀ φ ψ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
          (∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = ψ ≫ nthOrderUnitMap κ n) → φ = ψ) ∧
        ∀ α : ∀ n : ℕ, N ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra κ n),
          (∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap κ n = α n) →
          ∃ φ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
            ∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = α n)
    (halgebra : ∀ {Z : Scheme.{u}} (B C : AlgebraSheaf Z) (D : ℕ → AlgebraSheaf Z)
      (r : ∀ n : ℕ, C ⟶ D n)
      (φ : AlgebraSheaf.underlyingModule B ⟶ AlgebraSheaf.underlyingModule C),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (AlgebraSheaf.underlyingModule B) →
      _root_.SheafOfModules.IsCoherent (AlgebraSheaf.underlyingModule B) →
      (∀ n : ℕ, ∃ ψ : B ⟶ D n,
        AlgebraSheaf.underlyingModuleMap ψ = φ ≫ AlgebraSheaf.underlyingModuleMap (r n)) →
      (∀ P : Z.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} P →
        _root_.SheafOfModules.IsCoherent P →
        ∀ a b : P ⟶ AlgebraSheaf.underlyingModule C,
          (∀ n : ℕ, a ≫ AlgebraSheaf.underlyingModuleMap (r n) =
            b ≫ AlgebraSheaf.underlyingModuleMap (r n)) → a = b) →
      ∃ ψ : B ⟶ C, AlgebraSheaf.underlyingModuleMap ψ = φ)
    (A B : FiniteEtaleOver X) :
    Function.Bijective (fun φ : A ⟶ B => (finiteEtaleBaseChange i).map φ) :=
  (Functor.FullyFaithful.nonempty_iff_map_bijective (finiteEtaleBaseChange i)).mp
    (fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful i hcompletion h0GN2 halgebra)
    A B

/-- Let `X` be a Noetherian scheme and `Y ⊆ X` a closed subscheme with ideal sheaf `I` such that
the completion functor `Coh(𝒪_X) ⟶ Coh(X, I)` is fully faithful on the finite locally free objects.
Under the hypothesis `h0GN2` of `fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful`,
the restriction functor `FÉt_X ⟶ FÉt_Y` is fully faithful. -/
public theorem fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful_of_dualSections
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsNoetherian X] [IsClosedImmersion i]
    (hcompletion : Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X i.ker)
    (h0GN2 : ∀ {Z Z' : Scheme.{u}} (κ : Z' ⟶ Z) [IsClosedImmersion κ] (N : Z.Modules),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N →
      Stacks.Algebraization.IsInfinitesimalSectionsComplete κ
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) →
      (∀ φ ψ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
          (∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = ψ ≫ nthOrderUnitMap κ n) → φ = ψ) ∧
        ∀ α : ∀ n : ℕ, N ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra κ n),
          (∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap κ n = α n) →
          ∃ φ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
            ∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = α n) :
    Nonempty (finiteEtaleBaseChange i).FullyFaithful := by
  have : IsLocallyNoetherian X := inferInstance
  have hsc := isInfinitesimalSectionsComplete_dualSheaf_of_completionFullyFaithful i hcompletion
  refine fullyFaithful_finiteEtaleBaseChange_of_dualSections_bridge i
    (fun P hPf hPc => h0GN2 i P hPf (hsc P hPf hPc)) ?_
  intro V f _ hMf hMc φ hφ
  exact Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective_of_isLocallyNoetherian
    (pushforwardAlgebra (Over.mk f : Over X).hom) (unitAlgebra X)
    (fun n => nthOrderAlgebra i n) (fun n => nthOrderAlgebraRestriction i n) φ hMf hMc hφ
    fun P hPf hPc a b hab => (h0GN2 i P hPf (hsc P hPf hPc)).1 a b hab

/-! ### Completion of the structure sheaf -/

open Opposite
open Stacks.Algebraization (idealPowerQuotient idealPowerMultiple infinitesimalQuotientIso
  infinitesimalQuotientπ completionFunctor completionProjection unitCoherentModule
  completionFunctor_obj completionProjection_comp_eqToHom completionProjection_transition
  completionFunctor_map_quotient epi_completionProjection ker_nthInfinitesimalNeighbourhoodι
  comp_eq_zero_of_idealPowerMultiple_eq_bot idealQuotientPushforwardMap_π
  nthInfinitesimalNeighbourhoodι)

/-- The canonical morphisms from `𝒪_X` to the algebras `nthOrderAlgebra i n` form a cone: the
morphism at the `(n+1)`-st neighbourhood followed by the transition to the `n`-th is the morphism
at the `n`-th. -/
private theorem nthOrderAlgebraRestriction_comp_nthOrderAlgebraTransition {X Y : Scheme.{u}}
    (i : Y ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    nthOrderAlgebraRestriction i (n + 1) ≫ nthOrderAlgebraTransition i n =
      nthOrderAlgebraRestriction i n := by
  have hover : (nthInfinitesimalNeighbourhoodTransition i (Nat.le_succ n) ≫
        (Over.homMk (nthOrderToBase i (n + 1))
          (Category.comp_id (nthOrderToBase i (n + 1))) :
            nthInfinitesimalNeighbourhoodOver i (n + 1) ⟶ Over.mk (𝟙 X))) =
      (Over.homMk (nthOrderToBase i n) (Category.comp_id (nthOrderToBase i n)) :
        nthInfinitesimalNeighbourhoodOver i n ⟶ Over.mk (𝟙 X)) :=
    Over.OverMorphism.ext (transition_comp_nthOrderToBase i n)
  rw [nthOrderAlgebraRestriction, nthOrderAlgebraRestriction, nthOrderAlgebraTransition,
    ← pushforwardAlgebraMap_comp, hover]

/-- `nthOrderUnitMap i (n + 1)` followed by `nthOrderTransitionMap i n` is `nthOrderUnitMap i n`.
-/
private theorem nthOrderUnitMap_comp_nthOrderTransitionMap {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    nthOrderUnitMap i (n + 1) ≫ nthOrderTransitionMap i n = nthOrderUnitMap i n :=
  (underlyingModuleMap_comp (nthOrderAlgebraRestriction i (n + 1))
      (nthOrderAlgebraTransition i n)).symm.trans
    (congrArg AlgebraSheaf.underlyingModuleMap
      (nthOrderAlgebraRestriction_comp_nthOrderAlgebraTransition i n))

/-- The quotient of `𝒪_X` by the `(n+1)`-st power of the ideal sheaf of `Y` is isomorphic to the
direct image of the structure sheaf of the `n`-th infinitesimal neighbourhood of `Y`, the module
underlying `nthOrderAlgebra i n`. -/
private noncomputable def quotientNthOrderAlgebraIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    idealPowerQuotient i.ker (n + 1) (SheafOfModules.unit X.ringCatSheaf) ≅
      AlgebraSheaf.underlyingModule (nthOrderAlgebra i n) :=
  infinitesimalQuotientIso i (SheafOfModules.unit X.ringCatSheaf) n ≪≫
    (Scheme.Modules.pushforward (nthInfinitesimalNeighbourhoodι i n)).mapIso
      (Scheme.Modules.pullbackUnitIso (nthInfinitesimalNeighbourhoodι i n))

/-- The quotient projection of `𝒪_X` followed by `quotientNthOrderAlgebraIso` is `nthOrderUnitMap`.
-/
private theorem quotientNthOrderAlgebraIso_π {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    infinitesimalQuotientπ i (SheafOfModules.unit X.ringCatSheaf) n ≫
        (quotientNthOrderAlgebraIso i n).hom =
      nthOrderUnitMap i n :=
  have h1 : infinitesimalQuotientπ i (SheafOfModules.unit X.ringCatSheaf) n ≫
      (infinitesimalQuotientIso i (SheafOfModules.unit X.ringCatSheaf) n).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction
        (nthInfinitesimalNeighbourhoodι i n)).unit.app (Scheme.unitModule X) :=
    idealQuotientPushforwardMap_π i.ker (n + 1) (SheafOfModules.unit X.ringCatSheaf)
      (nthInfinitesimalNeighbourhoodι i n) (ker_nthInfinitesimalNeighbourhoodι i n)
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (Scheme.Modules.pushforward
        (nthInfinitesimalNeighbourhoodι i n)).map
          (Scheme.Modules.pullbackUnitIso (nthInfinitesimalNeighbourhoodι i n)).hom) h1).trans
      ((Adjunction.homEquiv_unit _ _ _ _).symm.trans
        (Scheme.Modules.pullbackUnitIso_homEquiv (nthInfinitesimalNeighbourhoodι i n))))

/-- The `n`-th term of the completion of `𝒪_X` along the ideal sheaf of `Y` is isomorphic to the
module underlying `nthOrderAlgebra i n`. -/
private noncomputable def completionTermNthOrderAlgebraIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] (n : ℕ) :
    ((completionFunctor X i.ker).obj (unitCoherentModule X)).obj.obj (op n) ≅
      AlgebraSheaf.underlyingModule (nthOrderAlgebra i n) :=
  eqToIso (completionFunctor_obj X i.ker (unitCoherentModule X) n) ≪≫
    quotientNthOrderAlgebraIso i n

/-- The projection of `𝒪_X` onto the `n`-th term of its completion followed by
`completionTermNthOrderAlgebraIso` is `nthOrderUnitMap`. -/
private theorem completionProjection_comp_completionTermNthOrderAlgebraIso {X Y : Scheme.{u}}
    (i : Y ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] (n : ℕ) :
    completionProjection X i.ker (unitCoherentModule X) n ≫
        (completionTermNthOrderAlgebraIso i n).hom =
      nthOrderUnitMap i n :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (quotientNthOrderAlgebraIso i n).hom)
        (completionProjection_comp_eqToHom i (unitCoherentModule X) n)).trans
      (quotientNthOrderAlgebraIso_π i n))

/-- The isomorphisms `completionTermNthOrderAlgebraIso` carry the transition maps of the completion
of `𝒪_X` to the maps `nthOrderTransitionMap`. -/
private theorem completionTermNthOrderAlgebraIso_transition {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] (n : ℕ) :
    ((completionFunctor X i.ker).obj (unitCoherentModule X)).obj.map
          (homOfLE (Nat.le_succ n)).op ≫ (completionTermNthOrderAlgebraIso i n).hom =
      (completionTermNthOrderAlgebraIso i (n + 1)).hom ≫ nthOrderTransitionMap i n := by
  have := epi_completionProjection X i.ker (unitCoherentModule X) (n + 1)
  refine (cancel_epi (C := X.Modules)
    (completionProjection X i.ker (unitCoherentModule X) (n + 1))).1 ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (completionTermNthOrderAlgebraIso i n).hom)
        (completionProjection_transition X i.ker (unitCoherentModule X) n)).trans
      ((completionProjection_comp_completionTermNthOrderAlgebraIso i n).trans
        ((nthOrderUnitMap_comp_nthOrderTransitionMap i n).symm.trans
          ((congrArg (fun k => k ≫ nthOrderTransitionMap i n)
              (completionProjection_comp_completionTermNthOrderAlgebraIso i (n + 1))).symm.trans
            (Category.assoc _ _ _)))))

/-- The inverses of the isomorphisms `completionTermNthOrderAlgebraIso` carry the maps
`nthOrderTransitionMap` to the transition maps of the completion of `𝒪_X`. -/
private theorem completionTermNthOrderAlgebraIso_inv_transition {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] (n : ℕ) :
    (completionTermNthOrderAlgebraIso i (n + 1)).inv ≫
        ((completionFunctor X i.ker).obj (unitCoherentModule X)).obj.map
          (homOfLE (Nat.le_succ n)).op =
      nthOrderTransitionMap i n ≫ (completionTermNthOrderAlgebraIso i n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact completionTermNthOrderAlgebraIso_transition i n

/-- The projection of a coherent module onto a term of its completion, followed by the
identification of that term with the ideal-power quotient, is the quotient projection. -/
private theorem completionProjection_comp_eqToHom_quotient {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    completionProjection X I F n ≫ eqToHom (completionFunctor_obj X I F n) =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι := by
  have h1 : eqToHom (completionFunctor_obj X I F n).symm ≫
      eqToHom (completionFunctor_obj X I F n) =
      𝟙 (idealPowerQuotient I (n + 1) F.obj) := by
    rw [eqToHom_trans, eqToHom_refl]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => cokernel.π (C := X.Modules)
        (idealPowerMultiple I (n + 1) F.obj).ι ≫ k) h1).trans (Category.comp_id _))

/-- If completion is injective on the morphisms from `F` to `G`, then two morphisms `F ⟶ G` whose
composites with the projections onto the terms of the completion of `G` agree are equal. -/
private theorem hom_ext_of_completionProjection {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hbij : Function.Bijective (fun f : F ⟶ G => (completionFunctor X I).map f))
    (φ ψ : F.obj ⟶ G.obj)
    (h : ∀ n : ℕ, φ ≫ completionProjection X I G n = ψ ≫ completionProjection X I G n) :
    φ = ψ := by
  have hmapeq : (completionFunctor X I).map (ObjectProperty.homMk (Y := G) φ) =
      (completionFunctor X I).map (ObjectProperty.homMk (Y := G) ψ) := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
    have := epi_completionProjection X I F n.unop
    refine (cancel_epi (C := X.Modules) (completionProjection X I F n.unop)).1 ?_
    refine (completionFunctor_map_quotient X I (ObjectProperty.homMk (Y := G) φ) n.unop).trans ?_
    exact (h n.unop).trans
      (completionFunctor_map_quotient X I (ObjectProperty.homMk (Y := G) ψ) n.unop).symm
  exact congrArg (fun f : F ⟶ G => f.hom) (hbij.1 hmapeq)

/-- If completion is surjective on the morphisms from `F` to `G`, then every system of morphisms
from `F` into the terms of the completion of `G` compatible with the transition maps is the system
of composites of a single morphism `F ⟶ G` with the projections. -/
private theorem exists_hom_of_completionProjection {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hbij : Function.Bijective (fun f : F ⟶ G => (completionFunctor X I).map f))
    (β : ∀ n : ℕ, F.obj ⟶ ((completionFunctor X I).obj G).obj.obj (op n))
    (hβ : ∀ n : ℕ, β (n + 1) ≫ ((completionFunctor X I).obj G).obj.map
      (homOfLE (Nat.le_succ n)).op = β n) :
    ∃ φ : F.obj ⟶ G.obj, ∀ n : ℕ, φ ≫ completionProjection X I G n = β n := by
  have hbot : ∀ n : ℕ,
      idealPowerMultiple I (n + 1) (((completionFunctor X I).obj G).obj.obj (op n)) = ⊥ :=
    ((completionFunctor X I).obj G).property.2.1
  have hzero : ∀ n : ℕ, ((idealPowerMultiple I (n + 1) F.obj).ι :
        ((idealPowerMultiple I (n + 1) F.obj).toSheafOfModules : X.Modules) ⟶ F.obj) ≫ β n =
      (0 : ((idealPowerMultiple I (n + 1) F.obj).toSheafOfModules : X.Modules) ⟶ _) :=
    fun n => comp_eq_zero_of_idealPowerMultiple_eq_bot I (n + 1) (β n) (hbot n)
  let θ : ∀ n : ℕ, ((completionFunctor X I).obj F).obj.obj (op n) ⟶
      ((completionFunctor X I).obj G).obj.obj (op n) := fun n =>
    eqToHom (completionFunctor_obj X I F n) ≫
      cokernel.desc (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι (β n) (hzero n)
  have hθ : ∀ n : ℕ, completionProjection X I F n ≫ θ n = β n := by
    intro n
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ cokernel.desc (C := X.Modules)
      (idealPowerMultiple I (n + 1) F.obj).ι (β n) (hzero n)) ?_).trans
      (cokernel.π_desc _ _ _)
    exact completionProjection_comp_eqToHom_quotient I F n
  have hnat : ∀ n : ℕ,
      ((completionFunctor X I).obj F).obj.map (homOfLE (n.le_add_right 1)).op ≫ θ n =
        θ (n + 1) ≫ ((completionFunctor X I).obj G).obj.map (homOfLE (n.le_add_right 1)).op := by
    intro n
    have := epi_completionProjection X I F (n + 1)
    refine (cancel_epi (C := X.Modules) (completionProjection X I F (n + 1))).1 ?_
    refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
    refine ((congrArg (fun k => k ≫ θ n)
      (completionProjection_transition X I F n)).trans (hθ n)).trans ?_
    exact (hβ n).symm.trans (congrArg (fun k => k ≫ ((completionFunctor X I).obj G).obj.map
      (homOfLE (Nat.le_succ n)).op) (hθ (n + 1)).symm)
  obtain ⟨f, hf⟩ := hbij.2 (ObjectProperty.homMk (NatTrans.ofOpSequence θ hnat))
  refine ⟨f.hom, fun n => ?_⟩
  refine (completionFunctor_map_quotient X I f n).symm.trans ?_
  refine (congrArg (fun k => completionProjection X I F n ≫ k) ?_).trans (hθ n)
  exact congrArg (fun z : (completionFunctor X I).obj F ⟶ (completionFunctor X I).obj G =>
    z.hom.app (op n)) hf

/-- Let `Y ⊆ X` be a closed subscheme of a locally Noetherian scheme such that completion along the
ideal sheaf of `Y` is fully faithful on the finite locally free coherent modules, and let `N` be a
coherent, finite locally free `𝒪_X`-module. Then the `𝒪_X`-module maps `N ⟶ 𝒪_X` are exactly the
compatible systems of maps from `N` into the modules underlying `nthOrderAlgebra i n`. -/
private theorem dualSections_of_completionFullyFaithful {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X]
    (hcompletion : Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X i.ker)
    (N : X.Modules)
    (hNf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (hNc : _root_.SheafOfModules.IsCoherent N) :
    (∀ φ ψ : N ⟶ SheafOfModules.unit X.ringCatSheaf,
        (∀ n : ℕ, φ ≫ nthOrderUnitMap i n = ψ ≫ nthOrderUnitMap i n) → φ = ψ) ∧
      ∀ α : ∀ n : ℕ, N ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra i n),
        (∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap i n = α n) →
        ∃ φ : N ⟶ SheafOfModules.unit X.ringCatSheaf,
          ∀ n : ℕ, φ ≫ nthOrderUnitMap i n = α n := by
  have hOflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (unitCoherentModule X).obj :=
    have := AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit X
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (SheafOfModules.unit X.ringCatSheaf) 1
  have hbij := hcompletion ⟨N, hNc⟩ (unitCoherentModule X) hNf hOflf
  have e : ∀ (n : ℕ) (χ : N ⟶ SheafOfModules.unit X.ringCatSheaf),
      (χ ≫ completionProjection X i.ker (unitCoherentModule X) n) ≫
          (completionTermNthOrderAlgebraIso i n).hom =
        χ ≫ nthOrderUnitMap i n := fun n χ =>
    (Category.assoc _ _ _).trans
      (congrArg (fun k => χ ≫ k)
        (completionProjection_comp_completionTermNthOrderAlgebraIso i n))
  refine ⟨fun φ ψ hφψ => ?_, fun α hα => ?_⟩
  · refine hom_ext_of_completionProjection i.ker ⟨N, hNc⟩ (unitCoherentModule X) hbij φ ψ
      fun n => ?_
    refine (Iso.cancel_iso_hom_right _ _ (completionTermNthOrderAlgebraIso i n)).1 ?_
    exact (e n φ).trans ((hφψ n).trans (e n ψ).symm)
  · have hcompat : ∀ n : ℕ, (α (n + 1) ≫ (completionTermNthOrderAlgebraIso i (n + 1)).inv) ≫
        ((completionFunctor X i.ker).obj (unitCoherentModule X)).obj.map
          (homOfLE (Nat.le_succ n)).op =
        α n ≫ (completionTermNthOrderAlgebraIso i n).inv := fun n =>
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => α (n + 1) ≫ k)
            (completionTermNthOrderAlgebraIso_inv_transition i n)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ (completionTermNthOrderAlgebraIso i n).inv) (hα n))))
    obtain ⟨φ, hφ⟩ := exists_hom_of_completionProjection i.ker ⟨N, hNc⟩ (unitCoherentModule X)
      hbij (fun n => α n ≫ (completionTermNthOrderAlgebraIso i n).inv) hcompat
    refine ⟨φ, fun n => ?_⟩
    refine (e n φ).symm.trans ?_
    refine (congrArg (fun k => k ≫ (completionTermNthOrderAlgebraIso i n).hom) (hφ n)).trans ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => α n ≫ k)
        (completionTermNthOrderAlgebraIso i n).inv_hom_id).trans (Category.comp_id _))

/-- Let `X` be a Noetherian scheme and `Y ⊆ X` a closed subscheme with ideal sheaf `I`. If the
completion functor `Coh(𝒪_X) ⟶ Coh(X, I)` is fully faithful on the full subcategory of finite
locally free objects, then the restriction functor `FÉt_X ⟶ FÉt_Y` is fully faithful. -/
@[stacks 0EL8 "proved from full faithfulness of completion on the finite locally free coherent \
modules alone"]
public theorem fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithfulOnFiniteLocallyFree
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsNoetherian X] [IsClosedImmersion i]
    (hcompletion : Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X i.ker) :
    Nonempty (finiteEtaleBaseChange i).FullyFaithful := by
  have : IsLocallyNoetherian X := inferInstance
  have hdual := dualSections_of_completionFullyFaithful i hcompletion
  refine fullyFaithful_finiteEtaleBaseChange_of_dualSections_bridge i hdual ?_
  intro V f _ hMf hMc φ hφ
  exact AlgebraSheaf.exists_hom_of_jointlyInjective
    (pushforwardAlgebra (Over.mk f : Over X).hom) (unitAlgebra X)
    (fun n => nthOrderAlgebra i n) (fun n => nthOrderAlgebraRestriction i n) φ
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit hMf hMc hφ
    fun P hPf hPc a b hab => (hdual P hPf hPc).1 a b hab

end Completion

end Stacks.FundamentalGroup

end

end
