module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
import StacksCore.Tactic.StacksAttribute

/-!
# Derived limits of inverse systems in a Grothendieck abelian category

Let `A` be a Grothendieck abelian category and let `K` be an object of the derived category of
the category `ℕᵒᵖ ⥤ A` of inverse systems of objects of `A`. Stacks 0941 identifies the value at
`K` of the right derived functor of the ordinary inverse limit `lim : (ℕᵒᵖ ⥤ A) ⥤ A` with the
derived (homotopy) limit, in `D(A)`, of the inverse system `(Kₙ)` of the derived evaluations of
`K`.

The proof follows the source. Represent `K` by a K-injective complex `I` of inverse systems whose
terms are injective objects (`Stacks.Injectives.kInjectiveResolutionFunctor`, Stacks 079P). Then:

* evaluation at an index has an exact left adjoint, so every `Iₙ` is again K-injective
  (`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`, Stacks 08BJ);
* an injective object `J` of `ℕᵒᵖ ⥤ A` has *split* transition maps `Jₙ₊₁ ⟶ Jₙ`. The source gets
  surjectivity from the monomorphism `(U, n) ⟶ (U, n + 1)` of the index category; here the
  splitting is produced directly, by factoring the adjunction morphism out of the free inverse
  system on `Jₙ` concentrated in degrees `≤ n` through the monomorphism relating it to the free
  inverse system concentrated in degrees `≤ n + 1`;
* an inverse system of K-injective complexes with degreewise split transition maps has a limit
  which is K-injective and which represents the derived limit
  (`CochainComplex.isKInjective_limit_and_isDerivedLimit_of_isSplitEpi`, Stacks 070M), and that
  limit is the termwise inverse limit `lim I`.

## Main definitions

* `Stacks.Cohomology.derivedEvaluationTower`: the inverse system in `D(A)` obtained by evaluating
  an object of `D(ℕᵒᵖ ⥤ A)` index by index.

## Main results

* `Stacks.Cohomology.exists_rightDerivedLimit_isDerivedLimit`: the value of the right derived
  functor of the inverse limit at `K` exists, and is a derived limit of the evaluation tower
  of `K`.

## Implementation notes

The source writes abelian sheaves on `C × N` as inverse systems of abelian sheaves on `C`; the
statement here is for an arbitrary Grothendieck abelian category, of which abelian sheaves on a
site are an instance. An object of a derived category has no literal components, so the evaluation
tower is formed from the canonical chosen preimage under the localization functor. The value of
the right derived functor is recorded by its
`CategoryTheory.Functor.IsRightDerivedValueAt` universal property, so the asserted identification
is independent of that choice; `CategoryTheory.Pretriangulated.IsDerivedLimit` is the notion of
derived limit.

Products indexed by `ℕ` are products over a type in `Type 0`, whereas a Grothendieck abelian
category is only assumed to have limits and colimits relative to its own universe; the two are
reconciled once and for all by the shrinking lemmas `has_smallest_products_of_hasProducts` and
`has_smallest_coproducts_of_hasCoproducts`.

## References

* [Stacks Project, Tag 0941](https://stacks.math.columbia.edu/tag/0941)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe wG w v u

namespace Stacks.Cohomology

variable {A : Type u} [Category.{v} A] [Abelian A]

/-! ### Inverse systems in a Grothendieck abelian category -/

section Grothendieck

variable [IsGrothendieckAbelian.{wG} A]

private instance : HasCoproducts.{0} A :=
  has_smallest_coproducts_of_hasCoproducts

private instance : HasProductsOfShape ℕ A :=
  has_smallest_products_of_hasProducts (C := A) ℕ

private instance : LocallySmall.{wG} (ℕᵒᵖ ⥤ A) where
  hom_small F G := by
    let emb (f : F ⟶ G) (i : Shrink.{wG} ℕᵒᵖ) :=
      (equivShrink.{wG} _) (f.app ((equivShrink _).symm i))
    have hemb : Function.Injective emb := fun f g h ↦ by
      ext i
      obtain ⟨i, rfl⟩ := (equivShrink.{wG} _).symm.surjective i
      simpa [emb] using congrFun h i
    exact small_of_injective hemb

private instance : AB5OfSize.{wG, wG} (ℕᵒᵖ ⥤ A) where
  ofShape J _ _ := by
    have : HasExactColimitsOfShape J A := inferInstance
    exact { preservesFiniteLimits := ⟨fun K _ _ ↦ ⟨fun {F} ↦ ⟨fun hc ↦ ⟨
      evaluationJointlyReflectsLimits _ fun n ↦ by
        let e := preservesColimitNatIso (J := J) ((evaluation ℕᵒᵖ A).obj n)
        exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerLeft F e) _).1
          (IsLimit.ofIsoLimit
            (isLimitOfPreserves
              ((Functor.whiskeringRight J _ _).obj ((evaluation ℕᵒᵖ A).obj n) ⋙ colim)
              hc)
            (Cone.ext ((e.symm).app _) (fun k ↦ (NatIso.naturality_2 e.symm _).symm)))⟩⟩⟩⟩ }

private instance : IsGrothendieckAbelian.{wG} (ℕᵒᵖ ⥤ A) where
  hasSeparator := inferInstance

private lemma isKInjective_evaluation
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (n : ℕᵒᵖ) :
    CochainComplex.IsKInjective
      ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have : PreservesFiniteLimits (evaluationLeftAdjoint A n) := by
    refine ⟨fun J _ _ => ?_⟩
    exact preservesLimitsOfShape_of_evaluation _ J (fun m => by
      show PreservesLimitsOfShape J
        ((Functor.const (Discrete (n ⟶ m)) : A ⥤ _) ⋙ colim)
      infer_instance)
  have : (evaluationLeftAdjoint A n).IsLeftAdjoint :=
    ⟨_, ⟨evaluationAdjunctionRight A n⟩⟩
  have : PreservesFiniteColimits (evaluationLeftAdjoint A n) := by infer_instance
  have : (evaluationLeftAdjoint A n).PreservesZeroMorphisms := by infer_instance
  have : (evaluationLeftAdjoint A n).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    ((evaluation ℕᵒᵖ A).obj n) (evaluationLeftAdjoint A n)
    (evaluationAdjunctionRight A n) I

private noncomputable def freeSystemι {n k : ℕᵒᵖ} (M : A) (g : n ⟶ k) :
    M ⟶ ((evaluationLeftAdjoint A n).obj M).obj k :=
  Sigma.ι (fun _ : n ⟶ k => M) g

private lemma freeSystemι_hom_ext {n k : ℕᵒᵖ} (M : A) {P : A}
    {a b : ((evaluationLeftAdjoint A n).obj M).obj k ⟶ P}
    (h : ∀ g : n ⟶ k, freeSystemι M g ≫ a = freeSystemι M g ≫ b) : a = b :=
  Sigma.hom_ext a b h

private lemma freeSystemι_comp_desc {n k : ℕᵒᵖ} (M : A) {P : A}
    (p : (n ⟶ k) → (M ⟶ P)) (g : n ⟶ k) :
    freeSystemι M g ≫ Sigma.desc (f := fun _ : n ⟶ k => M) p = p g :=
  Sigma.ι_desc p g

private lemma freeSystemι_comp_map {n k l : ℕᵒᵖ} (M : A) (g : n ⟶ k) (f : k ⟶ l) :
    freeSystemι M g ≫ ((evaluationLeftAdjoint A n).obj M).map f = freeSystemι M (g ≫ f) :=
  Sigma.ι_desc _ _

private noncomputable def stepFreeApp (n : ℕ) (M : A) (k : ℕᵒᵖ) :
    ((evaluationLeftAdjoint A (Opposite.op n)).obj M).obj k ⟶
      ((evaluationLeftAdjoint A (Opposite.op (n + 1))).obj M).obj k :=
  Sigma.desc fun g : Opposite.op n ⟶ k => freeSystemι M ((homOfLE (Nat.le_succ n)).op ≫ g)

private lemma freeSystemι_comp_stepFreeApp (n : ℕ) (M : A) (k : ℕᵒᵖ) (g : Opposite.op n ⟶ k) :
    freeSystemι M g ≫ stepFreeApp n M k = freeSystemι M ((homOfLE (Nat.le_succ n)).op ≫ g) :=
  freeSystemι_comp_desc M _ g

private noncomputable def stepFree (n : ℕ) (M : A) :
    (evaluationLeftAdjoint A (Opposite.op n)).obj M ⟶
      (evaluationLeftAdjoint A (Opposite.op (n + 1))).obj M where
  app k := stepFreeApp n M k
  naturality k l f := by
    refine freeSystemι_hom_ext M fun g => ?_
    simp only [← Category.assoc, freeSystemι_comp_map, freeSystemι_comp_stepFreeApp]

private lemma freeSystemι_comp_stepFree_app (n : ℕ) (M : A) (k : ℕᵒᵖ) (g : Opposite.op n ⟶ k) :
    freeSystemι M g ≫ (stepFree n M).app k = freeSystemι M ((homOfLE (Nat.le_succ n)).op ≫ g) :=
  freeSystemι_comp_stepFreeApp n M k g

open scoped Classical in
private noncomputable def stepFreeSection (n : ℕ) (M : A) (k : ℕᵒᵖ) :
    ((evaluationLeftAdjoint A (Opposite.op (n + 1))).obj M).obj k ⟶
      ((evaluationLeftAdjoint A (Opposite.op n)).obj M).obj k :=
  Sigma.desc fun _ : Opposite.op (n + 1) ⟶ k =>
    if h : Nonempty (Opposite.op n ⟶ k) then freeSystemι M h.some else 0

private lemma stepFree_app_comp_section (n : ℕ) (M : A) (k : ℕᵒᵖ) :
    (stepFree n M).app k ≫ stepFreeSection n M k = 𝟙 _ := by
  refine freeSystemι_hom_ext M fun g => ?_
  rw [← Category.assoc, freeSystemι_comp_stepFree_app, Category.comp_id, stepFreeSection,
    freeSystemι_comp_desc, dite_eq_left ⟨g⟩]
  exact congrArg (fun b : Opposite.op n ⟶ k => freeSystemι M b) (Subsingleton.elim _ g)

private instance stepFree_app_mono (n : ℕ) (M : A) (k : ℕᵒᵖ) :
    Mono ((stepFree n M).app k) :=
  (⟨stepFreeSection n M k, stepFree_app_comp_section n M k⟩ :
    SplitMono ((stepFree n M).app k)).mono

private instance stepFree_mono (n : ℕ) (M : A) : Mono (stepFree n M) :=
  NatTrans.mono_of_mono_app _

private noncomputable def evalFreeApp (n : ℕᵒᵖ) (J : ℕᵒᵖ ⥤ A) (k : ℕᵒᵖ) :
    ((evaluationLeftAdjoint A n).obj (J.obj n)).obj k ⟶ J.obj k :=
  Sigma.desc fun h : n ⟶ k => J.map h

private lemma freeSystemι_comp_evalFreeApp (n : ℕᵒᵖ) (J : ℕᵒᵖ ⥤ A) (k : ℕᵒᵖ) (g : n ⟶ k) :
    freeSystemι (J.obj n) g ≫ evalFreeApp n J k = J.map g :=
  freeSystemι_comp_desc (J.obj n) _ g

private noncomputable def evalFree (n : ℕᵒᵖ) (J : ℕᵒᵖ ⥤ A) :
    (evaluationLeftAdjoint A n).obj (J.obj n) ⟶ J where
  app k := evalFreeApp n J k
  naturality k l f := by
    refine freeSystemι_hom_ext (J.obj n) fun g => ?_
    simp only [← Category.assoc, freeSystemι_comp_map, freeSystemι_comp_evalFreeApp, ← J.map_comp]

private lemma isSplitEpi_transition_of_injective (J : ℕᵒᵖ ⥤ A) [Injective J] (n : ℕ) :
    IsSplitEpi (J.map ((homOfLE (Nat.le_succ n)).op)) := by
  let M := J.obj (Opposite.op n)
  let g : (evaluationLeftAdjoint A (Opposite.op n)).obj M ⟶ J :=
    evalFree (Opposite.op n) J
  let h := Injective.factorThru g (stepFree n M)
  have hh : stepFree n M ≫ h = g := Injective.comp_factorThru g (stepFree n M)
  refine IsSplitEpi.mk' ⟨freeSystemι M (𝟙 (Opposite.op (n + 1))) ≫
    h.app (Opposite.op (n + 1)), ?_⟩
  have e := freeSystemι_comp_stepFree_app n M (Opposite.op n) (𝟙 _)
  rw [Category.comp_id] at e
  rw [Category.assoc, ← h.naturality, ← Category.assoc, freeSystemι_comp_map, Category.id_comp,
    ← e, Category.assoc, ← NatTrans.comp_app, hh]
  exact (freeSystemι_comp_evalFreeApp _ J _ _).trans (J.map_id _)

end Grothendieck

/-! ### The tower of evaluations of a complex of inverse systems -/

private def evaluationComplexTower
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : ℕᵒᵖ ⥤ CochainComplex A ℤ where
  obj n := (((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  map {m n} f := (NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map f)
    (ComplexShape.up ℤ)).app I
  map_id n := by simp
  map_comp f g := by simp

private def evaluationComplexTowerMap
    {J I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : J ⟶ I) :
    evaluationComplexTower J ⟶ evaluationComplexTower I where
  app n := (((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  naturality n m g := by
    ext i
    exact (f.f i).naturality g

private lemma evaluationComplexTower_splitEpi [IsGrothendieckAbelian.{wG} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hI : ∀ i : ℤ, Injective (I.X i)) (n : ℕ) (i : ℤ) :
    IsSplitEpi (((evaluationComplexTower I).map (homOfLE (Nat.le_succ n)).op).f i) := by
  show IsSplitEpi ((I.X i).map (homOfLE (Nat.le_succ n)).op)
  have := hI i
  exact isSplitEpi_transition_of_injective (I.X i) n

/-- The inverse limit functor on inverse systems is additive, being a right adjoint and hence
preserving binary products. -/
noncomputable local instance limFunctorAdditive [HasLimitsOfShape ℕᵒᵖ A] :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
  Functor.additive_of_preserves_binary_products _

section Limits

variable [HasLimitsOfShape ℕᵒᵖ A]

private noncomputable def limitToEvaluation (n : ℕᵒᵖ) :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⟶ (evaluation ℕᵒᵖ A).obj n where
  app X := limit.π X n
  naturality _ _ f := limMap_π f n

private noncomputable def coneEvaluationComplexTower
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Cone (evaluationComplexTower I) where
  pt := ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  π := {
    app n := (NatTrans.mapHomologicalComplex (limitToEvaluation n) (ComplexShape.up ℤ)).app I
    naturality m n f := by
      ext i
      simp [evaluationComplexTower, limitToEvaluation, HomologicalComplex.comp_f] }

private noncomputable def isLimit_coneEvaluationComplexTower
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsLimit (coneEvaluationComplexTower I) :=
  HomologicalComplex.isLimitOfEval _ _ fun i => limit.isLimit (I.X i)

end Limits

/-! ### Transporting a derived limit along an isomorphism -/

private lemma isDerivedLimit_of_iso {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    {X Y : D} (hX : IsDerivedLimit F X) (e : X ≅ Y) : IsDerivedLimit F Y := by
  obtain ⟨p, δ, hT⟩ := hX
  exact ⟨e.inv ≫ p, δ ≫ e.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp))⟩

private lemma isDerivedLimit_of_natIso {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [HasProductsOfShape ℕ D] (F G : ℕᵒᵖ ⥤ D) (e : F ≅ G)
    (X : D) (hF : IsDerivedLimit F X) : IsDerivedLimit G X := by
  let a : (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ≅ (∏ᶜ fun n : ℕ => G.obj ⟨n⟩) :=
    Pi.mapIso (fun n : ℕ => e.app ⟨n⟩)
  obtain ⟨p, δ, hT⟩ := hF
  refine ⟨p ≫ a.hom, a.inv ≫ δ, ?_⟩
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) a.symm a.symm ?_ ?_ ?_)
  · simp
  · refine Pi.hom_ext _ _ fun n => ?_
    have ha (j : ℕ) : a.inv ≫ Pi.π (fun n : ℕ => F.obj ⟨n⟩) j =
        Pi.π (fun n : ℕ => G.obj ⟨n⟩) j ≫ (e.app ⟨j⟩).inv :=
      Pi.mapIso_inv_π (fun n : ℕ => e.app ⟨n⟩) j
    dsimp only [Triangle.mk_mor₂, Iso.symm_hom]
    simp only [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub]
    rw [ha n]
    simp only [← Category.assoc]
    rw [ha (n + 1)]
    simp only [Pi.lift_comp_π, Preadditive.sub_comp, Category.assoc]
    congr 1
    simpa only [← Category.assoc, Iso.app_inv] using
      congrArg (fun f => Pi.π (fun n : ℕ => G.obj ⟨n⟩) (n + 1) ≫ f)
        (e.inv.naturality ((homOfLE (Nat.le_succ n)).op))
  · simp

private lemma isRightDerivedValueAt_of_terminal
    {D H : Type*} [Category D] [Category H]
    (F : D ⥤ H) (W : MorphismProperty D) (X : D)
    {s : W.Under ⊤ X} (hs : IsTerminal s) :
    F.IsRightDerivedValueAt W X
      (coconeOfDiagramTerminal hs
        (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)) := by
  refine ⟨s, 𝟙 _, ?_, fun t => ⟨s, hs.from t, hs.from s, ?_⟩⟩
  · simp [coconeOfDiagramTerminal]
  · show F.map (hs.from t).right =
      F.map (hs.from t).right ≫ 𝟙 _ ≫ F.map (hs.from s).right
    simp

/-! ### The derived evaluation tower -/

section Derived

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

private noncomputable def evaluationDerivedTowerIso
    {J I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : J ⟶ I) [QuasiIso f] :
    (evaluationComplexTower J ⋙ DerivedCategory.Q) ≅
      (evaluationComplexTower I ⋙ DerivedCategory.Q) := by
  let e : (evaluationComplexTower J ⋙ DerivedCategory.Q) ⟶
      (evaluationComplexTower I ⋙ DerivedCategory.Q) :=
    Functor.whiskerRight (evaluationComplexTowerMap f) DerivedCategory.Q
  have he (n : ℕᵒᵖ) : IsIso (e.app n) := by
    dsimp [e, evaluationComplexTowerMap]
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _
      (show QuasiIso ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) from inferInstance)
  have : IsIso e := NatIso.isIso_of_isIso_app e
  exact asIso e

/-- The tower obtained by applying derived evaluation at every index to an object of the derived
category of inverse systems. -/
noncomputable def derivedEvaluationTower
    (K : DerivedCategory (ℕᵒᵖ ⥤ A)) : ℕᵒᵖ ⥤ DerivedCategory A where
  obj n := DerivedCategory.Q.obj
    ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (DerivedCategory.Q.objPreimage K))
  map {m n} f := DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map f)
      (ComplexShape.up ℤ)).app (DerivedCategory.Q.objPreimage K))
  map_id n := by simp
  map_comp f g := by simp

/-- **Stacks Project Tag 0941.** The value of the right derived functor of ordinary inverse limit
at `K` exists and is a derived limit of the tower of the derived evaluations `Kₙ`. -/
@[stacks 0941]
theorem exists_rightDerivedLimit_isDerivedLimit
    [IsGrothendieckAbelian.{wG} A]
    [HasLimitsOfShape ℕᵒᵖ A]
    (K : DerivedCategory (ℕᵒᵖ ⥤ A)) :
    ∃ (h : HasProduct fun n : ℕ => (derivedEvaluationTower K).obj ⟨n⟩),
      ∃ c : Cocone
        (MorphismProperty.Under.forget
            (HomotopyCategory.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) ⊤
            (DerivedCategory.Qh.objPreimage K) ⋙
          Under.forget (DerivedCategory.Qh.objPreimage K) ⋙
          ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh)),
      (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).IsRightDerivedValueAt
        (HomotopyCategory.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))
        (DerivedCategory.Qh.objPreimage K) c) ∧
      @IsDerivedLimit (DerivedCategory A) _ _ _ _ _ _
        (derivedEvaluationTower K) h c.pt := by
  let J := DerivedCategory.Q.objPreimage K
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor (ℕᵒᵖ ⥤ A)).obj J
  let f := (Stacks.Injectives.kInjectiveResolutionInclusion (ℕᵒᵖ ⥤ A)).app J
  have : I.IsKInjective := by infer_instance
  have hinj (i : ℤ) : Injective (I.X i) := by infer_instance
  let q := HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)
  let W := HomotopyCategory.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)
  have hlocal : W.isLocal (q.obj I) := by
    dsimp [W, q]
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, ObjectProperty.isLocal_trW]
    exact (CochainComplex.isKInjective_iff_rightOrthogonal I).1 inferInstance
  let e : DerivedCategory.Qh.obj (DerivedCategory.Qh.objPreimage K) ≅
      DerivedCategory.Qh.obj (q.obj I) :=
    DerivedCategory.Qh.objObjPreimageIso K ≪≫
      (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫
      ((DerivedCategory.quotientCompQhIso (ℕᵒᵖ ⥤ A)).app I).symm
  have hbij : Function.Bijective
      (DerivedCategory.Qh.map :
        (DerivedCategory.Qh.objPreimage K ⟶ q.obj I) → _) := by
    have : DerivedCategory.Qh.IsLocalization
        (HomotopyCategory.subcategoryAcyclic (ℕᵒᵖ ⥤ A)).trW := inferInstance
    exact (CochainComplex.IsKInjective.rightOrthogonal I).map_bijective_of_isTriangulated
      DerivedCategory.Qh _
  obtain ⟨g, hg⟩ := hbij.2 e.hom
  have hg : W g := by
    dsimp [W]
    rw [← DerivedCategory.isIso_Qh_map_iff, hg]
    infer_instance
  let s : W.Under ⊤ (DerivedCategory.Qh.objPreimage K) := MorphismProperty.Under.mk ⊤ g hg
  have hs : IsTerminal s :=
    IsTerminal.ofUniqueHom
      (fun t => MorphismProperty.Under.homMk _ ((hlocal t.hom t.prop).2 g).choose_spec)
      (fun t m => MorphismProperty.Under.Hom.ext
        ((hlocal t.hom t.prop).1
          ((MorphismProperty.Under.w m).trans
            ((hlocal t.hom t.prop).2 g).choose_spec.symm)))
  let F := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let c := coconeOfDiagramTerminal hs
    (MorphismProperty.Under.forget W ⊤ (DerivedCategory.Qh.objPreimage K) ⋙
      Under.forget (DerivedCategory.Qh.objPreimage K) ⋙ F)
  obtain ⟨_, _, _, hderived, _⟩ :=
    CochainComplex.isKInjective_limit_and_isDerivedLimit_of_isSplitEpi
      (evaluationComplexTower I) (fun n => isKInjective_evaluation I ⟨n⟩)
      (evaluationComplexTower_splitEpi I hinj)
  let eTower : derivedEvaluationTower K ≅ evaluationComplexTower I ⋙ DerivedCategory.Q := by
    show (evaluationComplexTower J ⋙ DerivedCategory.Q) ≅ _
    exact evaluationDerivedTowerIso f
  have : HasProducts.{0} (DerivedCategory A) :=
    has_smallest_products_of_hasProducts (C := DerivedCategory A)
  let eLim :
      ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
        limit (evaluationComplexTower I) :=
    (isLimit_coneEvaluationComplexTower I).conePointUniqueUpToIso
      (limit.isLimit (evaluationComplexTower I))
  refine ⟨inferInstance, c, isRightDerivedValueAt_of_terminal F W _ hs, ?_⟩
  let T := ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  show IsDerivedLimit (derivedEvaluationTower K)
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj T))
  exact isDerivedLimit_of_iso _
    (isDerivedLimit_of_iso _ (isDerivedLimit_of_natIso _ _ eTower.symm _ hderived)
      (DerivedCategory.Q.mapIso eLim.symm))
    ((DerivedCategory.quotientCompQhIso A).app T).symm

end Derived

end Stacks.Cohomology

end
