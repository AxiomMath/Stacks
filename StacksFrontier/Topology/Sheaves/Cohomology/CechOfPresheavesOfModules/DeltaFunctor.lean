module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.ComplexFunctorExactness
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of presheaves as a cohomological delta functor

Let `R` be a presheaf of rings on a space `X`, let `U` be an open subset and let `(Uᵢ)` be a
family of opens contained in `U`. Tag 01EK says that the Čech cohomology functors of that
family, with values in modules over the ring `R(U)` of sections on `U`, form a cohomological
delta functor on presheaves of `R`-modules: every short exact sequence of presheaves of modules
gives natural connecting maps and a long exact sequence in Čech cohomology.

It is deduced from Tag 01EJ, exactness of the Čech complex functor: the homology of an exact
functor from an abelian category into cochain complexes is a cohomological delta functor.

## Main definitions

* `Stacks.Cohomology.CechDeltaFunctor.deltaFunctorOfExactCochainComplex`: the delta functor
  attached to an exact functor into cochain complexes.
* `Stacks.Cohomology.CechDeltaFunctor.cechCohomologyDeltaFunctor`: the fixed-ring form, for a
  family of objects of a category with finite products and presheaves of modules over a single
  ring.
* `Stacks.Cohomology.CechDeltaFunctor.presheafCechCohomologyDeltaFunctor`: the delta functor of
  Tag 01EK, on presheaves of modules over a presheaf of rings on a space.

## Main results

* `Stacks.Cohomology.CechDeltaFunctor.fixedRingCechComplex_exact`: the Čech complex functor of a
  family of objects is exact on presheaves of modules over a fixed ring.

Each delta functor comes with the equality identifying its degree-`n` functor with the degree-`n`
homology of the corresponding complex.

## Implementation notes

The covering equation is not needed, so the result is stated for an arbitrary family of opens
contained in `U`.

`ModuleCat.hasLimits'` and `ModuleCat.hasLimits` are removed as instances around
`cechCohomologyDeltaFunctor` and restored immediately afterwards: the size-polymorphic limits
instance is the one its signature is stated against, and leaving both available makes the two
elaborate to different limit constructions.

## References

* [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Simplicial

universe u v w uR
universe uA vA uB vB
universe u_1

namespace Stacks.Cohomology.CechDeltaFunctor

section FixedRingHelpers

universe uM q

private def cechEvalFamily
    {C : Type u} [Category.{v} C] (R : Type uR) [Ring R]
    (E : FormalCoproduct.{w} C) :
    (Cᵒᵖ ⥤ ModuleCat.{max w uM} R) ⥤ (Discrete E.I ⥤ ModuleCat.{max w uM} R) where
  obj F := Discrete.functor fun i => F.obj (op (E.obj i))
  map f := Discrete.natTrans fun i => f.app (op (E.obj i.as))

private noncomputable def cechEvalProduct
    {C : Type u} [Category.{v} C] (R : Type uR) [Ring R]
    (E : FormalCoproduct.{w} C) :
    (Cᵒᵖ ⥤ ModuleCat.{max w uM} R) ⥤ ModuleCat.{max w uM} R :=
  FormalCoproduct.evalOp.{w} C (ModuleCat.{max w uM} R) ⋙
    (evaluation (FormalCoproduct.{w} C)ᵒᵖ (ModuleCat.{max w uM} R)).obj (op E)

private noncomputable def cechEvalProductIso
    {C : Type u} [Category.{v} C] (R : Type uR) [Ring R]
    (E : FormalCoproduct.{w} C) :
    cechEvalProduct.{u, v, w, uR, max w uM} R E ≅
      cechEvalFamily.{u, v, w, uR, max w uM} R E ⋙ lim := by
  refine NatIso.ofComponents (fun F => ((Limits.piEquivalenceFunctorDiscreteCompLim
    (C := ModuleCat.{max w uM} R) E.I).app (fun i => F.obj (op (E.obj i)))).symm) ?_
  intro F G f
  apply limit.hom_ext; intro i
  simp only [cechEvalProduct, FormalCoproduct.evalOp, Functor.comp_obj, evaluation_obj_obj,
    cechEvalFamily, Discrete.functor_obj_eq_as, lim_obj, Functor.comp_map, evaluation_obj_map,
    Iso.symm_hom, Iso.app_inv, piEquivalenceFunctorDiscreteCompLim_inv_app, Category.comp_id,
    lim_map, Category.id_comp, limMap_π, Discrete.natTrans_app]
  change Limits.Pi.map (fun i : E.I => f.app (op (E.obj i))) ≫
      Limits.Pi.π (fun i : E.I => G.obj (op (E.obj i))) i.as =
    Limits.Pi.π (fun i : E.I => F.obj (op (E.obj i))) i.as ≫ f.app (op (E.obj i.as))
  exact Limits.Pi.map_π (fun i : E.I => f.app (op (E.obj i))) i.as

/-- A functor into a functor category is exact if its composite with every evaluation is. -/
private theorem exactFunctor_of_evaluation
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    (F : C ⥤ D ⥤ E) (h : ∀ d, exactFunctor C E (F ⋙ (evaluation D E).obj d)) :
    exactFunctor C (D ⥤ E) F :=
  ⟨preservesFiniteLimits_of_evaluation F fun d => (h d).1,
    preservesFiniteColimits_of_evaluation F fun d => (h d).2⟩

private theorem cechEvalFamily_exact
    {C : Type u} [Category.{v} C] (R : Type uR) [Ring R]
    (E : FormalCoproduct.{w} C) :
    exactFunctor (Cᵒᵖ ⥤ ModuleCat.{max w uM} R)
      (Discrete E.I ⥤ ModuleCat.{max w uM} R)
      (cechEvalFamily.{u, v, w, uR, max w uM} R E) :=
  exactFunctor_of_evaluation _ fun i =>
    ⟨inferInstanceAs (PreservesFiniteLimits
        ((evaluation Cᵒᵖ (ModuleCat.{max w uM} R)).obj (op (E.obj i.as)))),
      inferInstanceAs (PreservesFiniteColimits
        ((evaluation Cᵒᵖ (ModuleCat.{max w uM} R)).obj (op (E.obj i.as))))⟩

private theorem moduleCatHasExactProducts
    (R : Type uR) [Ring R] :
    AB4StarOfSize.{q} (ModuleCat.{q} R) := by
  constructor
  intro J
  have : AB4StarOfSize.{max uR q} (ModuleCat.{max uR q} R) := by
    constructor; intro J
    exact HasExactLimitsOfShape.domain_of_functor (Discrete J)
      (forget₂ (ModuleCat.{max uR q} R) (AddCommGrpCat.{max uR q}))
  have : AB4StarOfSize.{q} (ModuleCat.{max uR q} R) := AB4StarOfSize_shrink _
  let F : ModuleCat.{q} R ⥤ ModuleCat.{max uR q} R := ModuleCat.uliftFunctor.{uR, q} R
  have : PreservesLimitsOfShape (Discrete J) F := by infer_instance
  have : PreservesFiniteColimits F := inferInstance
  have : ReflectsFiniteColimits F := inferInstance
  exact HasExactLimitsOfShape.domain_of_functor (C := ModuleCat.{q} R)
    (D := ModuleCat.{max uR q} R) (Discrete J) F

private theorem cechEvalProduct_exact
    {C : Type u} [Category.{v} C] (R : Type uR) [Ring R]
    (E : FormalCoproduct.{w} C) :
    exactFunctor (Cᵒᵖ ⥤ ModuleCat.{max w uM} R)
      (ModuleCat.{max w uM} R)
      (cechEvalProduct.{u, v, w, uR, max w uM} R E) := by
  have : AB4StarOfSize.{max w uM} (ModuleCat.{max w uM} R) :=
    moduleCatHasExactProducts.{uR, max w uM} R
  have : AB4StarOfSize.{w} (ModuleCat.{max w uM} R) := AB4StarOfSize_shrink _
  have hF := cechEvalFamily_exact.{u, v, w, uR, max w uM} R E
  rw [exactFunctor_iff] at hF
  have : PreservesFiniteLimits (cechEvalFamily.{u, v, w, uR, max w uM} R E) := hF.1
  have : PreservesFiniteColimits (cechEvalFamily.{u, v, w, uR, max w uM} R E) := hF.2
  have : PreservesFiniteLimits
    (lim : (Discrete E.I ⥤ ModuleCat.{max w uM} R) ⥤ _) := by infer_instance
  have : PreservesFiniteColimits
    (lim : (Discrete E.I ⥤ ModuleCat.{max w uM} R) ⥤ _) := by infer_instance
  exact (exactFunctor_iff _).mpr ⟨
    preservesFiniteLimits_of_natIso (cechEvalProductIso.{u, v, w, uR, max w uM} R E).symm,
    preservesFiniteColimits_of_natIso (cechEvalProductIso.{u, v, w, uR, max w uM} R E).symm⟩

private theorem cechCosimplicial_exact
    {C : Type u} [Category.{v} C] (R : Type uR) [Ring R]
    (E : SimplicialObject (FormalCoproduct.{w} C)) :
    exactFunctor (Cᵒᵖ ⥤ ModuleCat.{max w uM} R)
      (CosimplicialObject (ModuleCat.{max w uM} R))
      (FormalCoproduct.cosimplicialObjectFunctor E) :=
  exactFunctor_of_evaluation _ fun n =>
    cechEvalProduct_exact.{u, v, w, uR, max w uM} R (E.obj (op n))

private theorem alternatingCofaceMapComplex_exact.{uR', uX}
    (R : Type uR') [Ring R] :
    exactFunctor (CosimplicialObject (ModuleCat.{uX} R))
      (CochainComplex (ModuleCat.{uX} R) ℕ)
      (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{uX} R)) := by
  rw [exactFunctor_iff]
  constructor
  · refine ⟨fun J _ _ => ?_⟩
    apply HomologicalComplex.preservesLimitsOfShape_of_eval; intro n
    dsimp [AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj]
    change PreservesLimitsOfShape J
      ((evaluation SimplexCategory (ModuleCat.{uX} R)).obj ⦋n⦌)
    infer_instance
  · refine ⟨fun J _ _ => ?_⟩
    apply HomologicalComplex.preservesColimitsOfShape_of_eval; intro n
    dsimp [AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj]
    change PreservesColimitsOfShape J
      ((evaluation SimplexCategory (ModuleCat.{uX} R)).obj ⦋n⦌)
    infer_instance

/-- The Čech complex functor of a family `U` of objects of a category with finite products is an
exact functor from presheaves of modules over a fixed ring `R` to cochain complexes of `R`-modules.
-/
public theorem fixedRingCechComplex_exact
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    (R : Type uR) [Ring R] {ι : Type w} (U : ι → C) :
    exactFunctor (Cᵒᵖ ⥤ ModuleCat.{max w uM} R)
      (CochainComplex (ModuleCat.{max w uM} R) ℕ)
      (CategoryTheory.cechComplexFunctor.{w, v, max w uM, u, max uR (max w uM + 1)}
        (A := ModuleCat.{max w uM} R) U) := by
  let E : SimplicialObject (FormalCoproduct.{w} C) := (FormalCoproduct.mk _ U).cech
  change exactFunctor _ _ (FormalCoproduct.cochainComplexFunctor E)
  have h := (exactFunctor_iff _).mp (cechCosimplicial_exact.{u, v, w, uR, uM} R E)
  have h' := (exactFunctor_iff _).mp (alternatingCofaceMapComplex_exact.{uR, max w uM} R)
  have : PreservesFiniteLimits (FormalCoproduct.cosimplicialObjectFunctor E) := h.1
  have : PreservesFiniteColimits (FormalCoproduct.cosimplicialObjectFunctor E) := h.2
  have : PreservesFiniteLimits
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{max w uM} R)) := h'.1
  have : PreservesFiniteColimits
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{max w uM} R)) := h'.2
  rw [exactFunctor_iff]
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

/-- An exact functor from an abelian category to cochain complexes in an abelian category
induces a cohomological delta functor, namely its homology in each degree, together with the
equality identifying the functors of that delta functor with those homologies. -/
noncomputable def deltaFunctorOfExactCochainComplex
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : A ⥤ CochainComplex B ℕ)
    (hG : exactFunctor A (CochainComplex B ℕ) G) :
    { F : DeltaFunctor A B //
      ∀ n : ℕ, F.functor n = G ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n } := by
  have hG' := (exactFunctor_iff G).mp hG
  have : PreservesFiniteLimits G := hG'.1
  have : PreservesFiniteColimits G := hG'.2
  have : G.Additive := exactFunctor_le_additiveFunctor _ _ G hG
  let D : DeltaFunctor A B :=
    { functor := fun n => G ⋙ HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n
      additive := fun n => inferInstance
      δ := fun hS n => (hS.map_of_exact G).δ n (n + 1) rfl
      map_g_δ := fun hS n => (hS.map_of_exact G).comp_δ n (n + 1) rfl
      δ_map_f := fun hS n => (hS.map_of_exact G).δ_comp n (n + 1) rfl
      mono_map_f := fun {S} hS => by
        have : Mono (S.map G).f := (hS.map_of_exact G).mono_f
        exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (S.map G).f 0 fun i => by
          simp only [ComplexShape.up_Rel]; omega
      exact_map := fun hS n => (hS.map_of_exact G).homology_exact₂ n
      exact_δ₁ := fun hS n => (hS.map_of_exact G).homology_exact₃ n (n + 1) rfl
      exact_δ₂ := fun hS n => (hS.map_of_exact G).homology_exact₁ n (n + 1) rfl
      δ_naturality := fun hS hT φ n =>
        (HomologicalComplex.HomologySequence.δ_naturality (G.mapShortComplex.map φ)
          (hS.map_of_exact G) (hT.map_of_exact G) n (n + 1) rfl).symm }
  exact ⟨D, fun _ => rfl⟩

attribute [-instance] ModuleCat.hasLimits' ModuleCat.hasLimits

/-- The Čech cohomology functors of a family `U` of objects of a category with finite products form
a cohomological delta functor from presheaves of modules over a fixed ring `R` to `R`-modules; its
degree-`n` functor is the degree-`n` homology of the Čech complex of `U`. -/
public noncomputable def cechCohomologyDeltaFunctor
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    (R : Type uR) [Ring R] {ι : Type w} (U : ι → C) :
    { F : DeltaFunctor (Cᵒᵖ ⥤ ModuleCat R) (ModuleCat R) //
      ∀ n : ℕ, F.functor n = CategoryTheory.cechComplexFunctor (A := ModuleCat.{max w u_1} R) U ⋙
        HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n } :=
  deltaFunctorOfExactCochainComplex
    (CategoryTheory.cechComplexFunctor (A := ModuleCat.{max w u_1} R) U)
    (fixedRingCechComplex_exact.{u, v, w, uR, u_1} R U)

attribute [instance] ModuleCat.hasLimits' ModuleCat.hasLimits

end FixedRingHelpers

variable {X : Type u} [TopologicalSpace X]

local instance (U : Opens X) : HasFiniteProducts (Over U) :=
  Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- **Stacks Project, Tag 01EK.** The Čech cohomology functors of a family of opens form a
cohomological delta functor from presheaves of modules over the structure presheaf to
modules over the ring of sections on the ambient open. -/
@[stacks 01EK]
public noncomputable def presheafCechCohomologyDeltaFunctor
    (R : (Opens X)ᵒᵖ ⥤ RingCat.{uR}) (U : Opens X) {ι : Type w}
    (obj : ι → Opens X) (le : ∀ i, obj i ≤ U) :
    { F : DeltaFunctor (PresheafOfModules.{max v w} R)
        (ModuleCat.{max v w} (R.obj (op U))) //
      ∀ n : ℕ, F.functor n =
        ((PresheafOfModules.pushforward₀ (Over.forget U) R ⋙
          PresheafOfModules.forgetToPresheafModuleCat
            (op (Over.mk (𝟙 U))) (Over.mkIdTerminal.op) :
              PresheafOfModules.{max v w} R ⥤
                (Over U)ᵒᵖ ⥤ ModuleCat.{max v w} (R.obj (op U))) ⋙
          CategoryTheory.cechComplexFunctor
            (fun i ↦ Over.mk (homOfLE (le i)))) ⋙
          HomologicalComplex.homologyFunctor
            (ModuleCat.{max v w} (R.obj (op U))) (ComplexShape.up ℕ) n } :=
  deltaFunctorOfExactCochainComplex _
    (Stacks.Cohomology.CechExactFunctor.presheafCechComplexFunctor_exact R U obj le)

end Stacks.Cohomology.CechDeltaFunctor
