module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.DirectImageDelta
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.PullbackWedge
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaIdentityBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaComplexes

/-!
# The projection formula is compatible with base change

Let
```
X' --g'--> X
|f'        |f
v          v
S' --g---> S
```
be a commutative square of schemes and `G` a finite locally free `𝒪_S`-module. The base change
map `R^q f_* F ⟶ g_* R^q f'_*(M)` attached to `φ : F ⟶ g'_* M` is compatible with the projection
formulas `R^q f_*(F ⊗ f^* G) ≅ R^q f_* F ⊗ G` and `R^q f'_*(M ⊗ f'^* g^* G) ≅ R^q f'_* M ⊗ g^* G`.

The proof is a uniqueness statement for families of maps indexed by such pairs `(F, M, φ)` which
commute with the connecting morphisms: a pair embeds into the pair
`(I ⊞ g'_* J, J, pr₂)` with `I` and `J` injective, and `R^{q+1} f_*((I ⊞ g'_* J) ⊗ f^* G) = 0`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.pair_ext`: two families of maps
  `T^q(F) ⟶ U^q(M)`, indexed by `φ : F ⟶ P M` and commuting with the connecting morphisms, agree
  once they agree in degree zero.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.projectionFormulaMap_square`: in degree
  zero, the projection formula maps along the two sides of the square agree.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.projectionPairLeft_eq_right`: the
  projection formula is compatible with base change in every degree.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.projectionFormula_higherBaseChangeNat`: the
  same, for the base change map `g^* R^q f_* ⟶ R^q f'_* g'^*`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open Stacks.AlgebraicGeometry.LerayAffineBase (pushDelta)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Uniqueness

variable {A A' C : Type*} [Category A] [Category A'] [Category C] [Abelian A] [Abelian A']
  [Abelian C] [EnoughInjectives A] [EnoughInjectives A'] (P : A' ⥤ A) [P.Additive]
  (T : DeltaFunctor A C) (U : ℕ → A' → C)
  (δU : ∀ {S' : ShortComplex A'}, S'.ShortExact → ∀ q : ℕ, U q S'.X₃ ⟶ U (q + 1) S'.X₁)

/-- **Families of maps out of a δ-functor indexed by pairs are determined in degree zero.** Let
`T` be a δ-functor on `𝒜` killing `I ⊞ P J` in positive degrees for `I`, `J` injective. Two
families `η q φ : T^q(F) ⟶ U^q(M)`, indexed by `φ : F ⟶ P M`, which commute with the connecting
morphisms along every morphism `S ⟶ P(S')` of short exact sequences, agree if they agree in degree
zero. -/
public theorem pair_ext
    (hT : ∀ (I : A) [Injective I] (J : A') [Injective J] (q : ℕ),
      IsZero ((T.functor (q + 1)).obj (I ⊞ P.obj J)))
    (η η' : ∀ (q : ℕ) {F : A} {M : A'}, (F ⟶ P.obj M) → ((T.functor q).obj F ⟶ U q M))
    (hη : ∀ {S : ShortComplex A} (hS : S.ShortExact) {S' : ShortComplex A'} (hS' : S'.ShortExact)
      (μ : S ⟶ S'.map P) (q : ℕ), T.δ hS q ≫ η (q + 1) μ.τ₁ = η q μ.τ₃ ≫ δU hS' q)
    (hη' : ∀ {S : ShortComplex A} (hS : S.ShortExact) {S' : ShortComplex A'} (hS' : S'.ShortExact)
      (μ : S ⟶ S'.map P) (q : ℕ), T.δ hS q ≫ η' (q + 1) μ.τ₁ = η' q μ.τ₃ ≫ δU hS' q)
    (h0 : ∀ {F : A} {M : A'} (φ : F ⟶ P.obj M), η 0 φ = η' 0 φ) :
    ∀ (q : ℕ) {F : A} {M : A'} (φ : F ⟶ P.obj M), η q φ = η' q φ
  | 0, _, _, φ => h0 φ
  | q + 1, F, M, φ => by
    let a : F ⟶ Injective.under F ⊞ P.obj (Injective.under M) :=
      biprod.lift (Injective.ι F) (φ ≫ P.map (Injective.ι M))
    have : Mono a := mono_of_mono_fac (biprod.lift_fst (Injective.ι F) _)
    let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel a) }
    let S' := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M))
      (cokernel.condition _)
    have hS' : S'.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel S' (cokernelIsCokernel _) }
    have hd : a ≫ biprod.snd ≫ P.map (cokernel.π (Injective.ι M)) = 0 := by
      rw [biprod.lift_snd_assoc, Category.assoc, ← P.map_comp, cokernel.condition, P.map_zero,
        comp_zero]
    let μ : S ⟶ S'.map P :=
      { τ₁ := φ
        τ₂ := biprod.snd
        τ₃ := cokernel.desc a (biprod.snd ≫ P.map (cokernel.π (Injective.ι M))) hd
        comm₁₂ := (biprod.lift_snd _ _).symm
        comm₂₃ := (cokernel.π_desc _ _ _).symm }
    have : Epi (T.δ hS q) := T.epi_δ_of_map_f_eq_zero hS q
      ((hT (Injective.under F) (Injective.under M) q).eq_of_tgt _ _)
    exact (cancel_epi (T.δ hS q)).1 ((hη hS hS' μ q).trans
      ((congrArg (· ≫ δU hS' q) (pair_ext hT η η' hη hη' h0 q μ.τ₃)).trans
        (hη' hS hS' μ q).symm))

end Uniqueness

section RingedSpace

open Stacks.RingedSpace

variable {Z₁ Z₂ : RingedSpace.{u, u}} (k : Z₁ ⟶ Z₂)

/-- The transpose of `k^*(A ⊗ G) ⟶ k^* A ⊗ k^* G ⟶ Y ⊗ k^* G` is the transpose of
`h : k^* A ⟶ Y` tensored with `G`, followed by the projection formula map of `k`. -/
public theorem homEquiv_comparison_comp_tensorMap
    {A G : _root_.SheafOfModules.{u} (structureRingSheaf Z₂)}
    {Y : _root_.SheafOfModules.{u} (structureRingSheaf Z₁)} (h : (pullbackFunctor k).obj A ⟶ Y) :
    (pullbackAdjunction k).homEquiv _ _ (comparison k A G ≫ tensorMap h (𝟙 _)) =
      tensorMap ((pullbackAdjunction k).homEquiv _ _ h) (𝟙 G) ≫
        Stacks.ProjectionFormula.projectionFormulaMap' k Y G := by
  have hu := Stacks.ProjectionFormula.projectionFormulaMap'_unit k A G
  have hn := Stacks.ProjectionFormula.projectionFormulaMap'_natural k h (𝟙 G)
  have hu' : tensorMap ((pullbackAdjunction k).unit.app A) (𝟙 G) ≫
      Stacks.ProjectionFormula.projectionFormulaMap' k ((pullbackFunctor k).obj A) G =
      (pullbackAdjunction k).homEquiv _ _ (comparison k A G) := hu
  have hn' : tensorMap ((pushforwardFunctor k).map h) (𝟙 G) ≫
      Stacks.ProjectionFormula.projectionFormulaMap' k Y G =
      Stacks.ProjectionFormula.projectionFormulaMap' k ((pullbackFunctor k).obj A) G ≫
        (pushforwardFunctor k).map (tensorMap h (𝟙 _)) := by
    refine hn.trans ?_
    rw [CategoryTheory.Functor.map_id]
  exact (Adjunction.homEquiv_naturality_right _ _ _).trans
    ((congrArg (· ≫ (pushforwardFunctor k).map (tensorMap h (𝟙 _))) hu'.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (tensorMap ((pullbackAdjunction k).unit.app A) (𝟙 G) ≫ ·) hn'.symm).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ Stacks.ProjectionFormula.projectionFormulaMap' k Y G)
              ((tensorMap_comp _ _ _ _).trans (congrArg₂ (tensorMap (Z := Z₂))
                ((pullbackAdjunction k).homEquiv_unit _ _ h).symm (Category.comp_id _))))))))

/-- Tensoring the unit with `G` and applying the projection formula map of `k` is the unit
followed by the comparison `k^*(A ⊗ G) ⟶ k^* A ⊗ k^* G`. -/
public theorem tensorMap_unit_comp_projectionFormulaMap'
    (A G : _root_.SheafOfModules.{u} (structureRingSheaf Z₂)) :
    tensorMap ((pullbackAdjunction k).unit.app A) (𝟙 G) ≫
        Stacks.ProjectionFormula.projectionFormulaMap' k ((pullbackFunctor k).obj A) G =
      (pullbackAdjunction k).unit.app _ ≫ (pushforwardFunctor k).map (comparison k A G) :=
  (Stacks.ProjectionFormula.projectionFormulaMap'_unit k A G).trans
    (Adjunction.homEquiv_unit _ _ _ _)

end RingedSpace

section Square

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- **The base change map attached to a pair, in the indexing by injective resolutions**:
`R^q f_* F ⟶ g_* R^q f'_* M` for `φ : F ⟶ g'_* M`. -/
public def pairBaseChangeNat {F : X.Modules} {M : X'.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g').obj M) (q : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived q).obj F ⟶
      (Scheme.Modules.pushforward g).obj (((Scheme.Modules.pushforward f').rightDerived q).obj M) :=
  (Stacks.DerivedIndexing.rightDerivedIso _ q).hom.app F ≫
    Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pairBaseChange f g f' g' w φ q ≫
    (Scheme.Modules.pushforward g).map ((Stacks.DerivedIndexing.rightDerivedIso _ q).inv.app M)

/-- **The base change map attached to a pair commutes with the connecting morphisms**, in the
indexing by injective resolutions. -/
public theorem δ_comp_pairBaseChangeNat {T : ShortComplex X.Modules} (hT : T.ShortExact)
    {T' : ShortComplex X'.Modules} (hT' : T'.ShortExact)
    (μ : T ⟶ T'.map (Scheme.Modules.pushforward g')) (q : ℕ) :
    (pushDelta f).δ hT q ≫ pairBaseChangeNat f g f' g' w μ.τ₁ (q + 1) =
      pairBaseChangeNat f g f' g' w μ.τ₃ q ≫
        (Scheme.Modules.pushforward g).map ((pushDelta f').δ hT' q) := by
  show ((Stacks.DerivedIndexing.rightDerivedIso _ q).hom.app T.X₃ ≫
        Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f) hT q ≫
        (Stacks.DerivedIndexing.rightDerivedIso _ (q + 1)).inv.app T.X₁) ≫ _ =
    _ ≫ (Scheme.Modules.pushforward g).map ((Stacks.DerivedIndexing.rightDerivedIso _ q).hom.app _ ≫
      Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f') hT' q ≫
      (Stacks.DerivedIndexing.rightDerivedIso _ (q + 1)).inv.app _)
  have h := Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.canonicalδ_comp_pairBaseChange
    f g f' g' w hT hT' μ q
  unfold pairBaseChangeNat
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rw [reassoc_of% h, ← Functor.map_comp_assoc (Scheme.Modules.pushforward g)
    ((Stacks.DerivedIndexing.rightDerivedIso _ q).inv.app _), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

variable (G : S.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]

include f in
/-- **`R^{q+1} f_*((I ⊞ g'_* J) ⊗ f^* G) = 0`** for injective `I` and `J`: `I ⊗ f^* G` is
injective, and `g'_* J ⊗ f^* G ≅ g'_*(J ⊗ g'^* f^* G)` is the direct image of an injective, which
is acyclic for `f_*`. -/
public theorem isZero_projectionSource_biprod (I : X.Modules) [Injective I] (J : X'.Modules)
    [Injective J] (q : ℕ) :
    IsZero (((projectionSourceDelta f G).functor (q + 1)).obj
      (I ⊞ (Scheme.Modules.pushforward g').obj J)) := by
  have := (projectionSourceDelta f G).additive (q + 1)
  suffices h : IsZero (((projectionSourceDelta f G).functor (q + 1)).obj I) ∧
      IsZero (((projectionSourceDelta f G).functor (q + 1)).obj
        ((Scheme.Modules.pushforward g').obj J)) by
    refine IsZero.of_iso ?_ (Iso.refl _)
    rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, ← biprod.total, Functor.map_add,
      Functor.map_comp, Functor.map_comp,
      h.1.eq_zero_of_src (((projectionSourceDelta f G).functor (q + 1)).map biprod.inl),
      h.2.eq_zero_of_src (((projectionSourceDelta f G).functor (q + 1)).map biprod.inr),
      comp_zero, comp_zero, add_zero]
  refine ⟨?_, ?_⟩
  · have := Stacks.ProjectionFormula.injective_tensorRightInvertible_obj_of_isFiniteLocallyFree
      X ((Scheme.Modules.pullback f).obj G) I inferInstance
    exact Functor.isZero_rightDerived_obj_injective_succ _ q _
  · have := Stacks.ProjectionFormula.injective_tensorRightInvertible_obj_of_isFiniteLocallyFree
      X' ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f).obj G)) J inferInstance
    have hac :=
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.rightAcyclic_pushforward_obj_injective
        g' f ((Stacks.ProjectionFormula.tensorRightInvertible X'
          ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f).obj G))).obj J)
    have hz := ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus _ _).1.1 hac).2
      ((q + 1 : ℕ) : ℤ) (by omega)
    refine (hz.of_iso ((Stacks.DerivedIndexing.rightDerivedIso _ (q + 1)).app _)).of_iso ?_
    exact ((Scheme.Modules.pushforward f).rightDerived (q + 1)).mapIso
      ((Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso g'
        ((Scheme.Modules.pullback f).obj G)).app J).symm

/-- `g'^* f^* G ≅ f'^* g^* G`, from `g' ≫ f = f' ≫ g`. -/
public def squarePullbackIso :
    (Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f).obj G) ≅
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj G) :=
  (Scheme.Modules.pullbackComp g' f).app G ≪≫ (Scheme.Modules.pullbackCongr w).app G ≪≫
    ((Scheme.Modules.pullbackComp f' g).app G).symm

/-- The pair `F ⊗ f^* G ⟶ g'_*(M ⊗ f'^* g^* G)` attached to a pair `φ : F ⟶ g'_* M`: tensor `φ`
with `f^* G`, then the projection formula map of `g'`. -/
public def tensorPair {F : X.Modules} {M : X'.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g').obj M) :
    (Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback f).obj G)).obj F ⟶
      (Scheme.Modules.pushforward g').obj
        ((Stacks.ProjectionFormula.tensorRightInvertible X'
          ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj G))).obj M) :=
  (Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback f).obj G)).map φ ≫
    (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans g'
      ((Scheme.Modules.pullback f).obj G)).app M ≫
    (Scheme.Modules.pushforward g').map (tensorMap (𝟙 M) (squarePullbackIso f g f' g' w G).hom)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] in
/-- `tensorPair` is natural in the pair. -/
public theorem tensorPair_naturality {F₁ F₂ : X.Modules} {M₁ M₂ : X'.Modules}
    (φ₁ : F₁ ⟶ (Scheme.Modules.pushforward g').obj M₁)
    (φ₂ : F₂ ⟶ (Scheme.Modules.pushforward g').obj M₂) (a : F₁ ⟶ F₂) (b : M₁ ⟶ M₂)
    (h : a ≫ φ₂ = φ₁ ≫ (Scheme.Modules.pushforward g').map b) :
    (Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback f).obj G)).map a ≫
        tensorPair f g f' g' w G φ₂ =
      tensorPair f g f' g' w G φ₁ ≫ (Scheme.Modules.pushforward g').map
        ((Stacks.ProjectionFormula.tensorRightInvertible X'
          ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj G))).map b) := by
  have hn := (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans g'
    ((Scheme.Modules.pullback f).obj G)).naturality b
  have hc : tensorMap b (𝟙 _) ≫ tensorMap (𝟙 M₂) (squarePullbackIso f g f' g' w G).hom =
      tensorMap (𝟙 M₁) (squarePullbackIso f g f' g' w G).hom ≫ tensorMap b (𝟙 _) :=
    (tensorMap_comp _ _ _ _).trans (((congrArg₂ tensorMap ((Category.comp_id b).trans
      (Category.id_comp b).symm) ((Category.id_comp _).trans (Category.comp_id _).symm))).trans
      (tensorMap_comp _ _ _ _).symm)
  dsimp only [tensorPair, Functor.comp_map] at hn ⊢
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc, reassoc_of% hn, Category.assoc,
    Category.assoc]
  refine congrArg (fun t => _ ≫ _ ≫ t) ?_
  refine ((Scheme.Modules.pushforward g').map_comp _ _).symm.trans ?_
  refine Eq.trans ?_ ((Scheme.Modules.pushforward g').map_comp _ _)
  exact congrArg (Scheme.Modules.pushforward g').map hc

/-- The base change map through the projection formula of `f`:
`R^q f_*(F ⊗ f^* G) ≅ R^q f_* F ⊗ G ⟶ g_* R^q f'_* M ⊗ G ⟶ g_*(R^q f'_* M ⊗ g^* G)`. -/
public def projectionPairRight (q : ℕ) {F : X.Modules} {M : X'.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g').obj M) :
    ((projectionSourceDelta f G).functor q).obj F ⟶
      (Scheme.Modules.pushforward g).obj
        ((Stacks.ProjectionFormula.tensorRightInvertible S' ((Scheme.Modules.pullback g).obj G)).obj
          (((Scheme.Modules.pushforward f').rightDerived q).obj M)) :=
  (projectionFormulaDeltaApp f G F q).hom ≫
    (Stacks.ProjectionFormula.tensorRightInvertible S G).map (pairBaseChangeNat f g f' g' w φ q) ≫
    (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans g G).app _

/-- The base change map through the projection formula of `f'`:
`R^q f_*(F ⊗ f^* G) ⟶ g_* R^q f'_*(M ⊗ f'^* g^* G) ≅ g_*(R^q f'_* M ⊗ g^* G)`. -/
public def projectionPairLeft (q : ℕ) {F : X.Modules} {M : X'.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g').obj M) :
    ((projectionSourceDelta f G).functor q).obj F ⟶
      (Scheme.Modules.pushforward g).obj
        ((Stacks.ProjectionFormula.tensorRightInvertible S' ((Scheme.Modules.pullback g).obj G)).obj
          (((Scheme.Modules.pushforward f').rightDerived q).obj M)) :=
  pairBaseChangeNat f g f' g' w (tensorPair f g f' g' w G φ) q ≫
    (Scheme.Modules.pushforward g).map
      (projectionFormulaDeltaApp f' ((Scheme.Modules.pullback g).obj G) M q).hom

/-- The connecting morphisms of `M ↦ g_*(R^q f'_* M ⊗ g^* G)`. -/
public abbrev projectionPairδ {T' : ShortComplex X'.Modules} (hT' : T'.ShortExact) (q : ℕ) :=
  (Scheme.Modules.pushforward g).map
    ((Stacks.ProjectionFormula.tensorRightInvertible S' ((Scheme.Modules.pullback g).obj G)).map
      ((pushDelta f').δ hT' q))

/-- `projectionPairRight` commutes with the connecting morphisms. -/
public theorem δ_comp_projectionPairRight {T : ShortComplex X.Modules} (hT : T.ShortExact)
    {T' : ShortComplex X'.Modules} (hT' : T'.ShortExact)
    (μ : T ⟶ T'.map (Scheme.Modules.pushforward g')) (q : ℕ) :
    (projectionSourceDelta f G).δ hT q ≫ projectionPairRight f g f' g' w G (q + 1) μ.τ₁ =
      projectionPairRight f g f' g' w G q μ.τ₃ ≫ projectionPairδ g f' G hT' q := by
  have h1 := (projectionFormulaDelta f G).hom.comm hT q
  have h2 := δ_comp_pairBaseChangeNat f g f' g' w hT hT' μ q
  have h3 := (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans g G).naturality
    ((pushDelta f').δ hT' q)
  dsimp only [Functor.comp_map] at h3
  have h1' : (projectionSourceDelta f G).δ hT q ≫ (projectionFormulaDeltaApp f G T.X₁ (q + 1)).hom =
      (projectionFormulaDeltaApp f G T.X₃ q).hom ≫
        (Stacks.ProjectionFormula.tensorRightInvertible S G).map ((pushDelta f).δ hT q) := h1.symm
  unfold projectionPairRight
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1').trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((Functor.map_comp _ _ _).symm.trans
    ((congrArg (Stacks.ProjectionFormula.tensorRightInvertible S G).map h2).trans
      (Functor.map_comp _ _ _)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) h3

/-- `projectionPairLeft` commutes with the connecting morphisms. -/
public theorem δ_comp_projectionPairLeft {T : ShortComplex X.Modules} (hT : T.ShortExact)
    {T' : ShortComplex X'.Modules} (hT' : T'.ShortExact)
    (μ : T ⟶ T'.map (Scheme.Modules.pushforward g')) (q : ℕ) :
    (projectionSourceDelta f G).δ hT q ≫ projectionPairLeft f g f' g' w G (q + 1) μ.τ₁ =
      projectionPairLeft f g f' g' w G q μ.τ₃ ≫ projectionPairδ g f' G hT' q := by
  let μT : T.map (Stacks.ProjectionFormula.tensorRightInvertible X
        ((Scheme.Modules.pullback f).obj G)) ⟶
      (T'.map (Stacks.ProjectionFormula.tensorRightInvertible X'
        ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj G)))).map
        (Scheme.Modules.pushforward g') :=
    { τ₁ := tensorPair f g f' g' w G μ.τ₁
      τ₂ := tensorPair f g f' g' w G μ.τ₂
      τ₃ := tensorPair f g f' g' w G μ.τ₃
      comm₁₂ := (tensorPair_naturality f g f' g' w G μ.τ₁ μ.τ₂ T.f T'.f μ.comm₁₂.symm).symm
      comm₂₃ := (tensorPair_naturality f g f' g' w G μ.τ₂ μ.τ₃ T.g T'.g μ.comm₂₃.symm).symm }
  have h2 := δ_comp_pairBaseChangeNat f g f' g' w (hT.map_of_exact _) (hT'.map_of_exact
    (Stacks.ProjectionFormula.tensorRightInvertible X'
      ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj G)))) μT q
  have h4 := (projectionFormulaDelta f' ((Scheme.Modules.pullback g).obj G)).hom.comm hT' q
  unfold projectionPairLeft
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) (((Functor.map_comp _ _ _).symm.trans
    (congrArg (Scheme.Modules.pushforward g).map h4.symm)).trans (Functor.map_comp _ _ _))

/-- `pullbackCongr h` followed by `pullbackCongr h.symm` is the identity. -/
public theorem pullbackCongr_hom_app_comp_symm {Z₁ Z₂ : Scheme.{u}} {f₁ f₂ : Z₁ ⟶ Z₂} (h : f₁ = f₂)
    (N : Z₂.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app N ≫ (Scheme.Modules.pullbackCongr h.symm).hom.app N =
      𝟙 _ := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] in
/-- `squarePullbackIso` followed by `f'^* g^* G ≅ (f' ≫ g)^* G = (g' ≫ f)^* G` is
`g'^* f^* G ≅ (g' ≫ f)^* G`. -/
private theorem squarePullbackIso_hom_comp :
    (squarePullbackIso f g f' g' w G).hom ≫ (Scheme.Modules.pullbackComp f' g).hom.app G ≫
        (Scheme.Modules.pullbackCongr w.symm).hom.app G =
      (Scheme.Modules.pullbackComp g' f).hom.app G := by
  show ((Scheme.Modules.pullbackComp g' f).hom.app G ≫
      (Scheme.Modules.pullbackCongr w).hom.app G ≫ (Scheme.Modules.pullbackComp f' g).inv.app G) ≫
    (Scheme.Modules.pullbackComp f' g).hom.app G ≫
      (Scheme.Modules.pullbackCongr w.symm).hom.app G = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, pullbackCongr_hom_app_comp_symm,
    Category.comp_id]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] in
/-- The projection formula map of `g' ≫ f` at `M`, through `f_* g'_* ≅ (g' ≫ f)_*`. -/
private theorem projectionFormulaSourceNatTrans_pushforwardComp_app (M : X'.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (S.toRingedSpace).sheaf).flip.obj G).map
      ((Scheme.Modules.pushforwardComp g' f).inv.app M) ≫
    (AlgebraicGeometry.projectionFormulaSourceNatTrans f G).app
      ((Scheme.Modules.pushforward g').obj M) ≫
    (Scheme.Modules.pushforward f).map
      ((AlgebraicGeometry.projectionFormulaSourceNatTrans g'
        ((Scheme.Modules.pullback f).obj G)).app M) ≫
    (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforward g').map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (X'.toRingedSpace).sheaf).obj M).map
        ((Scheme.Modules.pullbackComp g' f).hom.app G))) =
    (AlgebraicGeometry.projectionFormulaSourceNatTrans (g' ≫ f) G).app M ≫
      (Scheme.Modules.pushforwardComp g' f).inv.app _ :=
  congr_app (AlgebraicGeometry.projectionFormulaSourceNatTrans_comp_whisker g' f G) M

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] in
/-- The projection formula map of `g' ≫ f = f' ≫ g` at `M`, through `g_* f'_* ≅ (g' ≫ f)_*`. -/
private theorem projectionFormulaSourceNatTrans_pushforwardCongr_app (M : X'.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (S.toRingedSpace).sheaf).flip.obj G).map
      ((Scheme.Modules.pushforwardCongr w.symm).inv.app M ≫
        (Scheme.Modules.pushforwardComp f' g).inv.app M) ≫
    (AlgebraicGeometry.projectionFormulaSourceNatTrans g G).app
      ((Scheme.Modules.pushforward f').obj M) ≫
    (Scheme.Modules.pushforward g).map
      ((AlgebraicGeometry.projectionFormulaSourceNatTrans f'
        ((Scheme.Modules.pullback g).obj G)).app M) ≫
    (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f').map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (X'.toRingedSpace).sheaf).obj M).map
        ((Scheme.Modules.pullbackComp f' g).hom.app G ≫
          (Scheme.Modules.pullbackCongr w.symm).hom.app G))) =
    (AlgebraicGeometry.projectionFormulaSourceNatTrans (g' ≫ f) G).app M ≫
      (Scheme.Modules.pushforwardCongr w.symm).inv.app _ ≫
      (Scheme.Modules.pushforwardComp f' g).inv.app _ :=
  congr_app (AlgebraicGeometry.projectionFormulaSourceNatTrans_comp' f' g w.symm G
    (ψ := (Scheme.Modules.pullbackComp f' g).hom.app G ≫
      (Scheme.Modules.pullbackCongr w.symm).hom.app G) rfl) M

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] in
/-- `M ⊗ -` applied to `squarePullbackIso_hom_comp`. -/
private theorem tensor_map_squarePullbackIso_hom_comp (M : X'.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (X'.toRingedSpace).sheaf).obj M).map (squarePullbackIso f g f' g' w G).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (X'.toRingedSpace).sheaf).obj M).map ((Scheme.Modules.pullbackComp f' g).hom.app G ≫
        (Scheme.Modules.pullbackCongr w.symm).hom.app G) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (X'.toRingedSpace).sheaf).obj M).map ((Scheme.Modules.pullbackComp g' f).hom.app G) :=
  (Functor.map_comp _ _ _).symm.trans (congrArg _ (squarePullbackIso_hom_comp f g f' g' w G))

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] in
/-- `- ⊗ G` applied to the decomposition of `f_* g'_* ≅ g_* f'_*`. -/
private theorem flip_map_pushforwardSquareIso_hom_app (M : X'.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (S.toRingedSpace).sheaf).flip.obj G).map
      ((Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
        f g f' g' w).hom.app M) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (S.toRingedSpace).sheaf).flip.obj G).map
        ((Scheme.Modules.pushforwardComp g' f).hom.app M) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (S.toRingedSpace).sheaf).flip.obj G).map
        ((Scheme.Modules.pushforwardCongr w.symm).inv.app M ≫
          (Scheme.Modules.pushforwardComp f' g).inv.app M) := Functor.map_comp _ _ _

/-- The diagram chase behind `projectionFormulaMap_square`. -/
private theorem square_chase {C : Type*} [Category C] {P₀ P₁ Q Z Y Y' V V₂ Z₂ : C} {a : P₀ ⟶ P₁}
    {a' : P₁ ⟶ P₀} (ha : a ≫ a' = 𝟙 P₀) {b : P₁ ⟶ Q} {L : Q ⟶ Z} {ph : P₁ ⟶ Y} {bc : Y ⟶ Z}
    (E2 : b ≫ L = ph ≫ bc) {R : P₀ ⟶ V} {k₁ : V ⟶ Y'} {ainv : Y ⟶ Y'} {ahom : Y' ⟶ Y}
    (hY : ainv ≫ ahom = 𝟙 Y) (E1 : a' ≫ R ≫ k₁ = ph ≫ ainv) {kc : V ⟶ V₂} {k₂ : V₂ ⟶ Y'}
    (hc : kc ≫ k₂ = k₁) {sqh : Y' ⟶ Z} (hsqh : sqh = ahom ≫ bc) {sqf : V₂ ⟶ Z₂} {k₂' : Z₂ ⟶ Z}
    (hn : k₂ ≫ sqh = sqf ≫ k₂') :
    (a ≫ b) ≫ L = R ≫ kc ≫ sqf ≫ k₂' := by
  have h1 : R ≫ k₁ = a ≫ ph ≫ ainv := by
    rw [← E1, ← Category.assoc a a', ha, Category.id_comp]
  rw [← hn, reassoc_of% hc, hsqh, reassoc_of% h1, reassoc_of% hY, Category.assoc, E2]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] in
/-- **The projection formula maps of the two sides of a commutative square agree**: for
`M` on `X'`, the projection formula maps `f_* g'_* M ⊗ G ⟶ f_*(g'_* M ⊗ f^* G) ⟶
f_* g'_*(M ⊗ g'^* f^* G)` and `g_* f'_* M ⊗ G ⟶ g_*(f'_* M ⊗ g^* G) ⟶ g_* f'_*(M ⊗ f'^* g^* G)`
correspond under `f_* g'_* ≅ g_* f'_*` and `g'^* f^* G ≅ f'^* g^* G`. -/
public theorem projectionFormulaMap_square (M : X'.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (S.toRingedSpace).sheaf).flip.obj G).map
        ((Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
          f g f' g' w).hom.app M) ≫
      (AlgebraicGeometry.projectionFormulaSourceNatTrans g G).app
        ((Scheme.Modules.pushforward f').obj M) ≫
      (Scheme.Modules.pushforward g).map
        ((AlgebraicGeometry.projectionFormulaSourceNatTrans f'
          ((Scheme.Modules.pullback g).obj G)).app M) =
    (AlgebraicGeometry.projectionFormulaSourceNatTrans f G).app
        ((Scheme.Modules.pushforward g').obj M) ≫
      (Scheme.Modules.pushforward f).map
        ((AlgebraicGeometry.projectionFormulaSourceNatTrans g'
          ((Scheme.Modules.pullback f).obj G)).app M) ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforward g').map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X'.toRingedSpace).sheaf).obj M).map
          (squarePullbackIso f g f' g' w G).hom)) ≫
      (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
          f g f' g' w).hom.app _ := by
  let ψ₂ := (Scheme.Modules.pullbackComp f' g).app G ≪≫ (Scheme.Modules.pullbackCongr w.symm).app G
  have hn := (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
      f g f' g' w).hom.naturality
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X'.toRingedSpace).sheaf).obj M).map ψ₂.hom)
  let κ : (Stacks.ProjectionFormula.tensorRightInvertible X'
        ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f').obj G)).obj M ⟶
      (Stacks.ProjectionFormula.tensorRightInvertible X'
        ((Scheme.Modules.pullback (g' ≫ f)).obj G)).obj M :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (X'.toRingedSpace).sheaf).obj M).map ψ₂.hom
  have : IsIso κ :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X'.toRingedSpace).sheaf).obj
      M).mapIso ψ₂).isIso_hom
  refine (cancel_mono
    ((Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f').map κ))).1 ?_
  have ha : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (S.toRingedSpace).sheaf).flip.obj G).map
        ((Scheme.Modules.pushforwardComp g' f).hom.app M) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (S.toRingedSpace).sheaf).flip.obj G).map
        ((Scheme.Modules.pushforwardComp g' f).inv.app M) = 𝟙 _ :=
    ((Scheme.Modules.pushforwardComp g' f).app M).map_hom_inv_id _
  have hc' : (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforward g').map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X'.toRingedSpace).sheaf).obj M).map
          (squarePullbackIso f g f' g' w G).hom)) ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforward g').map κ) =
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforward g').map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X'.toRingedSpace).sheaf).obj M).map
          ((Scheme.Modules.pullbackComp g' f).hom.app G))) :=
    (Functor.map_comp _ _ _).symm.trans (congrArg (Scheme.Modules.pushforward f).map
      ((Functor.map_comp _ _ _).symm.trans (congrArg (Scheme.Modules.pushforward g').map
        (tensor_map_squarePullbackIso_hom_comp f g f' g' w G M))))
  have key := square_chase ha
    (projectionFormulaSourceNatTrans_pushforwardCongr_app f g f' g' w G M)
    ((Scheme.Modules.pushforwardComp g' f).inv_hom_id_app _)
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      (projectionFormulaSourceNatTrans_pushforwardComp_app f g' G M)) hc' rfl hn
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans ?_
  refine (congrArg (· ≫ _) (flip_map_pushforwardSquareIso_hom_app f g f' g' w G M)).trans ?_
  refine key.trans ?_
  exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))))).symm

/-- **The base change map attached to a pair in degree zero** is `f_* φ` followed by
`f_* g'_* ≅ g_* f'_*`, under `R⁰ f_* = f_*` and `R⁰ f'_* = f'_*`. -/
public theorem pairBaseChangeNat_zero {F : X.Modules} {M : X'.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g').obj M) :
    pairBaseChangeNat f g f' g' w φ 0 =
      (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)).hom.app F ≫
        (Scheme.Modules.pushforward f).map φ ≫
        (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
          f g f' g' w).hom.app M ≫
        (Scheme.Modules.pushforward g).map
          ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f')).inv.app M) := by
  have h :=
    HigherDirectImageBaseChange.rightDerivedPlusZeroIso_inv_comp_pairBaseChange
      f g f' g' w φ
  unfold pairBaseChangeNat rightDerivedZeroIsoPlus
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Category.assoc, Functor.map_comp]
  rw [← reassoc_of% h, Iso.hom_inv_id_app_assoc]

/-- The projection formula of `f` in degree zero, through `R⁰ f_* = f_*`. -/
public theorem projectionFormulaDeltaApp_zero (F : X.Modules) :
    (projectionFormulaDeltaApp f G F 0).hom =
      (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)).hom.app _ ≫
        (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso f G).hom.app F ≫
        (Stacks.ProjectionFormula.tensorRightInvertible S G).map
          ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)).inv.app F) :=
  (congrArg (fun η => η.app F) (DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero
    (projectionFormulaZero f G))).trans rfl

/-- The projection formula map of `Stacks.ProjectionFormula` is that of
`AlgebraicGeometry.projectionFormulaSourceNatTrans`. -/
public theorem projectionFormulaSourceNatTrans_app_eq {T Z : Scheme.{u}} (h : T ⟶ Z) (H : Z.Modules)
    (A : T.Modules) :
    (AlgebraicGeometry.projectionFormulaSourceNatTrans h H).app A =
      (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans h H).app A :=
  Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq_projectionFormulaMap' h A H

/-- Tensoring on the right by `H`, as the flip of the tensor bifunctor at `H` and as
`Stacks.ProjectionFormula.tensorRightInvertible`. -/
public theorem flip_obj_map_eq_tensorRightInvertible_map {Z : Scheme.{u}} (H : Z.Modules)
    {A B : Z.Modules} (x : A ⟶ B) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.toRingedSpace).sheaf).flip.obj
        H).map x =
      (Stacks.ProjectionFormula.tensorRightInvertible Z H).map x :=
  (Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.toRingedSpace).sheaf) x H).symm

/-- The diagram chase behind `projectionPairLeft_zero`. -/
private theorem zero_chase {C : Type*} [Category C] {A₀ A₁ B₁ B₂ B₃ D₁ D₂ D₃ D₄ E₁ E₂ : C}
    (r : A₀ ⟶ A₁) {X₁ : A₁ ⟶ B₁} {X₂ : B₁ ⟶ B₂} {u : B₂ ⟶ B₃} {u' : B₃ ⟶ B₂} (hu : u ≫ u' = 𝟙 _)
    {p' : B₂ ⟶ E₁} {v : E₁ ⟶ E₂} {P : A₁ ⟶ D₁} {pmf : D₁ ⟶ A₁} (hP : P ≫ pmf = 𝟙 _)
    {i : D₁ ⟶ D₂} {i' : D₂ ⟶ D₁} (hi : i ≫ i' = 𝟙 _) {Y : D₁ ⟶ D₃} {W : D₃ ⟶ D₄}
    {πR : D₄ ⟶ E₂} {π : D₃ ⟶ E₁} {q : E₁ ⟶ B₂} (hq : q ≫ p' = 𝟙 _)
    (hcore : pmf ≫ X₁ ≫ X₂ = Y ≫ π ≫ q) (hW : W ≫ πR = π ≫ v) :
    (r ≫ X₁ ≫ X₂ ≫ u) ≫ u' ≫ p' ≫ v = (r ≫ P ≫ i) ≫ (i' ≫ Y ≫ W) ≫ πR := by
  have h1 : X₁ ≫ X₂ ≫ p' = P ≫ Y ≫ π := by
    simpa only [Category.assoc, hq, Category.comp_id, reassoc_of% hP] using
      congrArg (fun t => P ≫ t ≫ p') hcore
  simp only [Category.assoc, reassoc_of% hu, reassoc_of% hi, hW, reassoc_of% h1]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] in
/-- The projection formula map of `f` followed by `f_* tensorPair` and `f_* g'_* ≅ g_* f'_*` is
`(f_* φ ≫ f_* g'_* ≅ g_* f'_*) ⊗ G` followed by the projection formula maps of `g` and `f'`. -/
private theorem pushforwardTensorRightNatTrans_comp_tensorPair {F : X.Modules} {M : X'.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g').obj M) :
    (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans f G).app F ≫
      (Scheme.Modules.pushforward f).map (tensorPair f g f' g' w G φ) ≫
      (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
        f g f' g' w).hom.app _ =
    (Stacks.ProjectionFormula.tensorRightInvertible S G).map
        ((Scheme.Modules.pushforward f).map φ ≫
          (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
            f g f' g' w).hom.app M) ≫
      (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans g G).app
        ((Scheme.Modules.pushforward f').obj M) ≫
      (Scheme.Modules.pushforward g).map
        ((Stacks.ProjectionFormula.pushforwardTensorRightNatTrans f'
          ((Scheme.Modules.pullback g).obj G)).app M) := by
  have hsq := projectionFormulaMap_square f g f' g' w G M
  rw [flip_obj_map_eq_tensorRightInvertible_map, projectionFormulaSourceNatTrans_app_eq,
    projectionFormulaSourceNatTrans_app_eq, projectionFormulaSourceNatTrans_app_eq,
    projectionFormulaSourceNatTrans_app_eq,
    ← Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X'.toRingedSpace).sheaf) M
      (squarePullbackIso f g f' g' w G).hom] at hsq
  have hnf := (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans f G).naturality φ
  dsimp only [Functor.comp_map] at hnf
  unfold tensorPair
  simp only [Functor.map_comp, Category.assoc]
  refine ((reassoc_of% hnf) _).symm.trans ?_
  exact congrArg (_ ≫ ·) hsq.symm

/-- **The two base change maps through the projection formulas agree in degree zero.** -/
public theorem projectionPairLeft_zero {F : X.Modules} {M : X'.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g').obj M) :
    projectionPairLeft f g f' g' w G 0 φ = projectionPairRight f g f' g' w G 0 φ := by
  have hW := (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans g G).naturality
    ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f')).inv.app M)
  dsimp only [Functor.comp_map] at hW
  have hu : (Scheme.Modules.pushforward g).map
        ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f')).inv.app
          ((Stacks.ProjectionFormula.tensorRightInvertible X'
            ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj G))).obj M)) ≫
      (Scheme.Modules.pushforward g).map
        ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f')).hom.app
          ((Stacks.ProjectionFormula.tensorRightInvertible X'
            ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj G))).obj M)) =
      𝟙 _ := by
    simp
  have hi : (Stacks.ProjectionFormula.tensorRightInvertible S G).map
        ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)).inv.app F) ≫
      (Stacks.ProjectionFormula.tensorRightInvertible S G).map
        ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)).hom.app F) = 𝟙 _ := by
    simp
  have hq : (Scheme.Modules.pushforward g).map
      ((Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso
        f' ((Scheme.Modules.pullback g).obj G)).inv.app M) ≫
      (Scheme.Modules.pushforward g).map
      ((Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso
        f' ((Scheme.Modules.pullback g).obj G)).hom.app M) =
      𝟙 _ := by
    simp
  have key := zero_chase ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)).hom.app _) hu
    ((Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso f G).hom_inv_id_app F)
    hi hq (pushforwardTensorRightNatTrans_comp_tensorPair f g f' g' w G φ) hW
  refine Eq.trans ?_ (key.trans ?_)
  · unfold projectionPairLeft
    rw [pairBaseChangeNat_zero, projectionFormulaDeltaApp_zero]
    exact congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).trans
      (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)))
  · unfold projectionPairRight
    rw [pairBaseChangeNat_zero, projectionFormulaDeltaApp_zero]
    refine congrArg (_ ≫ ·) (congrArg (· ≫ _) ?_).symm
    exact (Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·)
      ((congrArg (Stacks.ProjectionFormula.tensorRightInvertible S G).map
        (Category.assoc _ _ _).symm).trans (Functor.map_comp _ _ _)))

/-- **The projection formula is compatible with base change**: for `φ : F ⟶ g'_* M` and every
`q`, the base change map attached to `φ` through the projection formula of `f`,
`R^q f_*(F ⊗ f^* G) ≅ R^q f_* F ⊗ G ⟶ g_* R^q f'_* M ⊗ G ⟶ g_*(R^q f'_* M ⊗ g^* G)`, is the base
change map attached to `φ ⊗ f^* G` through the projection formula of `f'`,
`R^q f_*(F ⊗ f^* G) ⟶ g_* R^q f'_*(M ⊗ f'^* g^* G) ≅ g_*(R^q f'_* M ⊗ g^* G)`. -/
public theorem projectionPairLeft_eq_right (q : ℕ) {F : X.Modules} {M : X'.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g').obj M) :
    projectionPairLeft f g f' g' w G q φ = projectionPairRight f g f' g' w G q φ :=
  pair_ext (Scheme.Modules.pushforward g') (projectionSourceDelta f G)
    (fun q M => (Scheme.Modules.pushforward g).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible S' ((Scheme.Modules.pullback g).obj G)).obj
        (((Scheme.Modules.pushforward f').rightDerived q).obj M)))
    (fun hT' q => projectionPairδ g f' G hT' q)
    (fun I _ J _ q => isZero_projectionSource_biprod f g' G I J q)
    (fun q _ _ φ => projectionPairLeft f g f' g' w G q φ)
    (fun q _ _ φ => projectionPairRight f g f' g' w G q φ)
    (fun hT _ hT' μ q => δ_comp_projectionPairLeft f g f' g' w G hT hT' μ q)
    (fun hT _ hT' μ q => δ_comp_projectionPairRight f g f' g' w G hT hT' μ q)
    (fun φ => projectionPairLeft_zero f g f' g' w G φ) q φ

/-- The base change map attached to a pair is natural in the second module. -/
public theorem pairBaseChangeNat_comp_map {F : X.Modules} {M₁ M₂ : X'.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g').obj M₁) (ψ : M₁ ⟶ M₂) (q : ℕ) :
    pairBaseChangeNat f g f' g' w (φ ≫ (Scheme.Modules.pushforward g').map ψ) q =
      pairBaseChangeNat f g f' g' w φ q ≫
        (Scheme.Modules.pushforward g).map
          (((Scheme.Modules.pushforward f').rightDerived q).map ψ) := by
  unfold pairBaseChangeNat
  rw [Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pairBaseChange_comp_map]
  simp only [Category.assoc, ← Functor.map_comp, NatTrans.naturality]

/-- The base change map in the indexing by injective resolutions is the transpose of the base
change map attached to the unit. -/
public theorem homEquiv_higherBaseChangeNat (q : ℕ) (F : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat f g f' g' w q F) =
      pairBaseChangeNat f g f' g' w
        ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) q := by
  unfold Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
    Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChange pairBaseChangeNat
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] in
/-- `tensorPair` at the unit is the unit followed by the comparison of Tag 01CD. -/
public theorem tensorPair_unit (F : X.Modules) :
    tensorPair f g f' g' w G ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) =
      (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app _ ≫
        (Scheme.Modules.pushforward g').map
          (Stacks.RingedSpace.comparison g'.toLRSHom.toShHom F ((Scheme.Modules.pullback f).obj G) ≫
            tensorMap (𝟙 _) (squarePullbackIso f g f' g' w G).hom) := by
  have h := tensorMap_unit_comp_projectionFormulaMap' g'.toLRSHom.toShHom F
    ((Scheme.Modules.pullback f).obj G)
  unfold tensorPair
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h)).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _).symm)

/-- **The projection formula is compatible with the base change map**: for `F` on `X` and every
`q`, the square
```
g^* R^q f_*(F ⊗ f^* G) ⟶ g^*(R^q f_* F ⊗ G) ⟶ g^* R^q f_* F ⊗ g^* G
        |                                               |
R^q f'_*(g'^*(F ⊗ f^* G)) ⟶ R^q f'_*(g'^* F ⊗ f'^* g^* G) ⟶ R^q f'_*(g'^* F) ⊗ g^* G
```
commutes, the vertical maps being the base change maps. -/
public theorem projectionFormula_higherBaseChangeNat (q : ℕ) (F : X.Modules) :
    (Scheme.Modules.pullback g).map (projectionFormulaDeltaApp f G F q).hom ≫
        Stacks.RingedSpace.comparison g.toLRSHom.toShHom
          (((Scheme.Modules.pushforward f).rightDerived q).obj F) G ≫
        tensorMap
          (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat f g f' g' w q F)
          (𝟙 _) =
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat f g f' g' w q
          ((Stacks.ProjectionFormula.tensorRightInvertible X
            ((Scheme.Modules.pullback f).obj G)).obj
            F) ≫
        ((Scheme.Modules.pushforward f').rightDerived q).map
          (Stacks.RingedSpace.comparison g'.toLRSHom.toShHom F ((Scheme.Modules.pullback f).obj G) ≫
            tensorMap (𝟙 _) (squarePullbackIso f g f' g' w G).hom) ≫
        (projectionFormulaDeltaApp f' ((Scheme.Modules.pullback g).obj G)
          ((Scheme.Modules.pullback g').obj F) q).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  have hR : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullback g).map (projectionFormulaDeltaApp f G F q).hom ≫
        Stacks.RingedSpace.comparison g.toLRSHom.toShHom
          (((Scheme.Modules.pushforward f).rightDerived q).obj F) G ≫
        tensorMap
          (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat f g f' g' w q F)
          (𝟙 _)) =
      projectionPairRight f g f' g' w G q
        ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) := by
    refine (Adjunction.homEquiv_naturality_left _ _ _).trans (congrArg (_ ≫ ·) ?_)
    refine (homEquiv_comparison_comp_tensorMap g.toLRSHom.toShHom _).trans ?_
    exact congrArg (fun t => tensorMap t (𝟙 G) ≫ _) (homEquiv_higherBaseChangeNat f g f' g' w q F)
  have hL : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat f g f' g' w q
          ((Stacks.ProjectionFormula.tensorRightInvertible X
            ((Scheme.Modules.pullback f).obj G)).obj
            F) ≫
        ((Scheme.Modules.pushforward f').rightDerived q).map
          (Stacks.RingedSpace.comparison g'.toLRSHom.toShHom F ((Scheme.Modules.pullback f).obj G) ≫
            tensorMap (𝟙 _) (squarePullbackIso f g f' g' w G).hom) ≫
        (projectionFormulaDeltaApp f' ((Scheme.Modules.pullback g).obj G)
          ((Scheme.Modules.pullback g').obj F) q).hom) =
      projectionPairLeft f g f' g' w G q
        ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) := by
    refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
    refine ((congrArg (· ≫ _) (homEquiv_higherBaseChangeNat f g f' g' w q _)).trans ?_).trans
      (congrArg (fun t => pairBaseChangeNat f g f' g' w t q ≫ _)
        (tensorPair_unit f g f' g' w G F)).symm
    exact (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (pairBaseChangeNat_comp_map f g f' g' w _ _ q).symm))
  exact hR.trans ((projectionPairLeft_eq_right f g f' g' w G q _).symm.trans hL.symm)

end Square

section Naturality

variable {X S : Scheme.{u}} (f : X ⟶ S) {G G' : S.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G'] (γ : G ⟶ G')

/-- Tensoring on the right with `γ : H ⟶ H'`, as a natural transformation
`tensorRightInvertible Z H ⟶ tensorRightInvertible Z H'`. -/
private def tensorRightInvertibleNatTrans (Z : Scheme.{u}) {H H' : Z.Modules} (γ : H ⟶ H') :
    Stacks.ProjectionFormula.tensorRightInvertible Z H ⟶
      Stacks.ProjectionFormula.tensorRightInvertible Z H' where
  app A := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (Z.toRingedSpace).sheaf).flip.map γ).app A
  naturality _ _ x :=
    (congrArg (· ≫ _) (Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.toRingedSpace).sheaf) x H)).trans
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (Z.toRingedSpace).sheaf).map x).naturality γ).symm.trans (congrArg (_ ≫ ·)
        (Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (Z.toRingedSpace).sheaf) x H').symm))

/-- The finite locally free projection formula `f_*(A ⊗ f^* G) ≅ f_* A ⊗ G` is natural in `G`. -/
private theorem pushforwardTensorRightFiniteLocallyFreeNatIso_naturality_right
    (A : X.Modules) :
    (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso f G).hom.app A ≫
        (tensorRightInvertibleNatTrans S γ).app ((Scheme.Modules.pushforward f).obj A) =
      (Scheme.Modules.pushforward f).map
          ((tensorRightInvertibleNatTrans X ((Scheme.Modules.pullback f).map γ)).app A) ≫
        (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso
          f G').hom.app A := by
  have hpm : (tensorRightInvertibleNatTrans S γ).app ((Scheme.Modules.pushforward f).obj A) ≫
      (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans f G').app A =
      (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans f G).app A ≫
        (Scheme.Modules.pushforward f).map
          ((tensorRightInvertibleNatTrans X ((Scheme.Modules.pullback f).map γ)).app A) :=
    Cohomology.ClosedEmbeddingProjectionFormulaComplexes.projectionFormulaMap'_natural_right
      f.toLRSHom.toShHom A γ
  rw [← cancel_mono ((Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso
    f G').inv.app A), Category.assoc, Category.assoc, Iso.hom_inv_id_app]
  refine Eq.trans ?_ (Category.comp_id _).symm
  show _ ≫ (tensorRightInvertibleNatTrans S γ).app _ ≫
    (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans f G').app A = _
  rw [hpm, ← Category.assoc,
    show (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso f G).hom.app A ≫
      (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans f G).app A = 𝟙 _ from
      (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso f G).hom_inv_id_app A,
    Category.id_comp]

/-- **The projection formula is natural in the module on the base**:
`R^q f_*(F ⊗ f^* G) ≅ R^q f_* F ⊗ G` commutes with `γ : G ⟶ G'`. -/
public theorem projectionFormulaDeltaApp_naturality_right (F : X.Modules) (q : ℕ) :
    (projectionFormulaDeltaApp f G F q).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (S.toRingedSpace).sheaf).flip.map γ).app _ =
      ((Scheme.Modules.pushforward f).rightDerived q).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (X.toRingedSpace).sheaf).flip.map ((Scheme.Modules.pullback f).map γ)).app F) ≫
        (projectionFormulaDeltaApp f G' F q).hom := by
  have key : (projectionFormulaDelta f G).hom ≫
        (pushDelta f).postcompNatTrans _ (tensorRightInvertibleNatTrans S γ) =
      (pushDelta f).precompNatTrans
          (tensorRightInvertibleNatTrans X ((Scheme.Modules.pullback f).map γ)) ≫
        (projectionFormulaDelta f G').hom := by
    refine DeltaFunctor.IsUniversal.hom_ext_zero (F := projectionSourceDelta f G) ?_
    refine NatTrans.ext (funext fun A => ?_)
    show (projectionFormulaDeltaApp f G A 0).hom ≫ (tensorRightInvertibleNatTrans S γ).app _ =
      ((Scheme.Modules.pushforward f).rightDerived 0).map
          ((tensorRightInvertibleNatTrans X ((Scheme.Modules.pullback f).map γ)).app A) ≫
        (projectionFormulaDeltaApp f G' A 0).hom
    rw [projectionFormulaDeltaApp_zero, projectionFormulaDeltaApp_zero]
    have hn1 := (tensorRightInvertibleNatTrans S γ).naturality
      ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)).inv.app A)
    have hn2 := (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)).hom.naturality
      ((tensorRightInvertibleNatTrans X ((Scheme.Modules.pullback f).map γ)).app A)
    simp only [Category.assoc]
    rw [hn1, reassoc_of% pushforwardTensorRightFiniteLocallyFreeNatIso_naturality_right f γ A,
      reassoc_of% hn2]
  exact congrArg (fun η : projectionSourceDelta f G ⟶ projectionTargetDelta f G' => (η.app q).app F)
    key

end Naturality


end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
