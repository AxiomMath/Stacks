module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Category.TopCat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Exactness of the Čech complex functor

Let `R` be a presheaf of rings on a space, `U` an open, and `(Uᵢ)` a family of
opens contained in `U`. The functor sending a presheaf of `R`-modules to its Čech
cochain complex for `(Uᵢ)`, regarded as a complex of `R(U)`-modules, is exact.

## Main definitions

* `CechOpenCover` records an indexed open covering of an open subset.
* `sectionsOverFunctor` regards sections on opens over `U` as modules over
  `R(U)`.
* `presheafCechComplexFunctor` is the Čech complex functor
  `Č^•(U, -) : PMod(R) ⥤ Comp⁺(Mod_{R(U)})`.

## Main results

* `presheafCechComplexFunctor_exact` asserts exactness of this functor.

## Implementation notes

Passing to opens over `U` makes `U` terminal; restriction of presheaves followed
by `PresheafOfModules.forgetToPresheafModuleCat` therefore puts every section
module over the single ring `R(U)`. The Čech complex is obtained by composing
with `CategoryTheory.cechComplexFunctor`. Neither the functor nor its exactness
requires the family to cover `U`, so the covering equation is omitted from the
exactness statement. The family index universe is independent of the space.

## References

* [Stacks Project, Tag 01EI](https://stacks.math.columbia.edu/tag/01EI)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Simplicial

universe u r v w c a ch ah p m j

namespace Stacks.Cohomology.CechExactFunctor

/-- An open covering `U = ⋃ i, obj i` of an open subset of a topological space. -/
public structure CechOpenCover (X : TopCat.{u}) where
  /-- The type indexing the covering. -/
  ι : Type w
  /-- The open subset being covered. -/
  U : Opens X
  /-- The members of the covering. -/
  obj : ι → Opens X
  /-- Every member is contained in the covered open. -/
  le : ∀ i, obj i ≤ U
  /-- The members cover `U`. -/
  covers : ⨆ i, obj i = U

variable {X : Type u} [TopologicalSpace X]

/-- Restriction of scalars along a ring homomorphism is exact: it preserves finite
limits and finite colimits, because it is the identity on underlying abelian
groups. -/
private theorem restrictScalars_preservesFinite
    {R S : Type r} [Ring R] [Ring S] (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{m} f) ∧
      PreservesFiniteColimits (ModuleCat.restrictScalars.{m} f) := by
  let F := ModuleCat.restrictScalars.{m} f
  have hShort : ∀ (T : ShortComplex (ModuleCat.{m} S)),
      T.ShortExact → (T.map F).ShortExact := fun T hT =>
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).1 hT.exact)
      mono_f := (ModuleCat.mono_iff_injective _).2
        ((ModuleCat.mono_iff_injective T.f).1 hT.mono_f)
      epi_g := (ModuleCat.epi_iff_surjective _).2
        ((ModuleCat.epi_iff_surjective T.g).1 hT.epi_g) }
  exact (Functor.exact_tfae F).out 1 4 |>.mp hShort

/-- Grothendieck's axiom AB4* for module categories: products indexed by any type are
exact. A product of surjective linear maps is surjective, so the limit functor over a
discrete shape preserves epimorphisms, hence is exact. -/
private theorem moduleCat_hasExactLimitsOfShape_discrete
    {R : Type r} [Ring R] (J : Type j) :
    HasExactLimitsOfShape (Discrete J) (ModuleCat.{max j m} R) := by
  have hpe : (lim : (Discrete J ⥤ ModuleCat.{max j m} R) ⥤
      ModuleCat.{max j m} R).PreservesEpimorphisms := by
    constructor
    intro F G η hη
    rw [NatTrans.epi_iff_epi_app] at hη
    rw [ModuleCat.epi_iff_surjective]
    intro y
    choose g hg using fun j =>
      (ModuleCat.epi_iff_surjective (η.app j)).1 (hη j) (ConcreteCategory.hom (limit.π G j) y)
    have hL := isLimitOfPreserves (forget (ModuleCat.{max j m} R)) (limit.isLimit F)
    have hsec : g ∈ (F ⋙ forget (ModuleCat.{max j m} R)).sections := by
      rintro ⟨j⟩ ⟨j'⟩ ⟨⟨(rfl : j = j')⟩⟩
      simp
    refine ⟨(Types.isLimitEquivSections hL).symm ⟨g, hsec⟩, ?_⟩
    apply Concrete.isLimit_ext G (limit.isLimit G)
    intro j
    have hpa : ConcreteCategory.hom (limit.π F j)
        ((Types.isLimitEquivSections hL).symm ⟨g, hsec⟩) = g j :=
      Types.isLimitEquivSections_symm_apply hL ⟨g, hsec⟩ j
    have key := ConcreteCategory.congr_hom (limMap_π η j)
      ((Types.isLimitEquivSections hL).symm ⟨g, hsec⟩)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at key
    change ConcreteCategory.hom (limit.π G j) (ConcreteCategory.hom (limMap η) _)
      = ConcreteCategory.hom (limit.π G j) y
    rw [key, hpa, hg j]
  exact hasExactLimitsOfShape_of_preservesEpi (J := Discrete J)
    (C := ModuleCat.{max j m} R)

/-- `moduleCat_hasExactLimitsOfShape_discrete` in the universe shape used below, so
that the Čech products are found to be exact by instance search. -/
local instance {R : Type r} [Ring R] (J : Type w) :
    HasExactLimitsOfShape (Discrete J) (ModuleCat.{max v w} R) :=
  moduleCat_hasExactLimitsOfShape_discrete J

/-- The value of `sectionsOverFunctor` at an object `Y` of `(Over U)ᵒᵖ`, written as a
composite of an evaluation and a restriction of scalars. In this form both factors are
visibly exact. -/
private noncomputable def sectionsOverFactor
    (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) (U : Opens X)
    (Y : (Over U)ᵒᵖ) :
    PresheafOfModules.{m} R ⥤ ModuleCat.{m} (R.obj (op U)) :=
  PresheafOfModules.evaluation.{m} R ((Over.forget U).op.obj Y) ⋙
    ModuleCat.restrictScalars.{m, r}
      (R.map ((Over.forget U).op.map (Over.mkIdTerminal.op.to Y))).hom

/-- Restriction of presheaves of `R`-modules to opens over `U`, with sections
regarded as modules over `R(U)`. -/
public noncomputable def sectionsOverFunctor
    (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) (U : Opens X) :
    PresheafOfModules.{v} R ⥤ (Over U)ᵒᵖ ⥤ ModuleCat.{v} (R.obj (op U)) :=
  PresheafOfModules.pushforward₀ (Over.forget U) R ⋙
    PresheafOfModules.forgetToPresheafModuleCat
      (op (Over.mk (𝟙 U))) (Over.mkIdTerminal.op)

/-- `sectionsOverFunctor` evaluated at `Y` is `sectionsOverFactor` at `Y`. The
underlying maps agree on the nose; only the packaging differs. -/
private noncomputable def sectionsOverFactorIso
    (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) (U : Opens X)
    (Y : (Over U)ᵒᵖ) :
    sectionsOverFunctor R U ⋙ (evaluation (Over U)ᵒᵖ _).obj Y ≅
      sectionsOverFactor R U Y :=
  NatIso.ofComponents (fun M => Iso.refl _) (by
    intro M N f
    ext x
    rfl)

/-- **Stacks Project, Tag 01EI.** The Čech complex functor
`Č^•(U, -) : PMod(R) ⥤ Comp⁺(Mod_{R(U)})` for a family of opens contained in `U`: a
presheaf of `R`-modules goes to its Čech cochain complex, each term a module over `R(U)`
and each differential `R(U)`-linear. -/
@[stacks 01EI "the family is not required to cover `U`, which neither the functor nor its \
differentials use"]
public noncomputable def presheafCechComplexFunctor
    (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) (U : Opens X) {ι : Type w}
    (obj : ι → Opens X) (le : ∀ i, obj i ≤ U) :
    PresheafOfModules.{max v w} R ⥤
      CochainComplex (ModuleCat.{max v w} (R.obj (op U))) ℕ :=
  sectionsOverFunctor R U ⋙
    CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (homOfLE (le i)))

private def formalCoproductEvalOpCompEvalIso01EJ
    {C : Type c} [Category.{ch} C] {A : Type a} [Category.{ah} A] [HasProducts A]
    (Y : (FormalCoproduct.{p} C)ᵒᵖ) :
    FormalCoproduct.evalOp.{p} C A ⋙
      (evaluation (FormalCoproduct.{p} C)ᵒᵖ A).obj Y ≅
      piDiscreteFunctor
        (fun i : Y.unop.I => (evaluation Cᵒᵖ A).obj (op (Y.unop.obj i))) ⋙ lim :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- `FormalCoproduct.evalOp` preserves finite limits: evaluationwise it is a product of
evaluations, and products of finite-limit-preserving functors preserve finite limits. -/
private theorem formalCoproductEvalOpPreservesFiniteLimits01EJ
    {C : Type c} [Category.{ch} C] {A : Type a} [Category.{ah} A]
    [HasProducts.{p} A]
    [HasFiniteLimits A] :
    PreservesFiniteLimits (FormalCoproduct.evalOp.{p} C A) := by
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro Y
  let F : Y.unop.I → ((Cᵒᵖ ⥤ A) ⥤ A) :=
    fun i => (evaluation Cᵒᵖ A).obj (op (Y.unop.obj i))
  have : PreservesLimitsOfShape J (piDiscreteFunctor F ⋙ lim) :=
    comp_preservesFiniteLimits _ _ |>.preservesFiniteLimits J
  exact preservesLimitsOfShape_of_natIso
    (formalCoproductEvalOpCompEvalIso01EJ Y).symm

/-- `FormalCoproduct.evalOp` preserves finite colimits, given that products indexed by
the summand types of formal coproducts are exact in the target category. -/
private theorem formalCoproductEvalOpPreservesFiniteColimits01EJ
    {C : Type c} [Category.{ch} C] {A : Type a} [Category.{ah} A]
    [HasProducts.{p} A]
    [HasFiniteColimits A]
    (hExact : ∀ J : Type p, HasExactLimitsOfShape (Discrete J) A) :
    PreservesFiniteColimits (FormalCoproduct.evalOp.{p} C A) := by
  constructor
  intro J _ _
  apply preservesColimitsOfShape_of_evaluation
  intro Y
  let F : Y.unop.I → ((Cᵒᵖ ⥤ A) ⥤ A) :=
    fun i => (evaluation Cᵒᵖ A).obj (op (Y.unop.obj i))
  have := hExact Y.unop.I
  have : PreservesColimitsOfShape J (piDiscreteFunctor F ⋙ lim) :=
    comp_preservesFiniteColimits _ _ |>.preservesFiniteColimits J
  exact preservesColimitsOfShape_of_natIso
    (formalCoproductEvalOpCompEvalIso01EJ Y).symm

/-- The degree-`n` term of the alternating coface map complex of a cosimplicial object is
the value of that object at `⦋n⦌`. -/
private def alternatingCofaceMapComplexCompEvalIso01EJ
    {A : Type*} [Category A] [Preadditive A] (n : ℕ) :
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙
      HomologicalComplex.eval A (ComplexShape.up ℕ) n ≅
      (evaluation SimplexCategory A).obj ⦋n⦌ :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- The alternating coface map complex functor preserves finite limits, because limits of
complexes are computed degreewise and each degree is an evaluation. -/
private instance alternatingCofaceMapComplex01EJ_preservesFiniteLimits
    {A : Type*} [Category A] [Preadditive A] [HasFiniteLimits A] :
    PreservesFiniteLimits (AlgebraicTopology.alternatingCofaceMapComplex A) := by
  constructor
  intro J _ _
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro n
  exact preservesLimitsOfShape_of_natIso
    (alternatingCofaceMapComplexCompEvalIso01EJ n).symm

/-- The alternating coface map complex functor preserves finite colimits, because
colimits of complexes are computed degreewise and each degree is an evaluation. -/
private instance alternatingCofaceMapComplex01EJ_preservesFiniteColimits
    {A : Type*} [Category A] [Preadditive A] [HasFiniteColimits A] :
    PreservesFiniteColimits (AlgebraicTopology.alternatingCofaceMapComplex A) := by
  constructor
  intro J _ _
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  exact preservesColimitsOfShape_of_natIso
    (alternatingCofaceMapComplexCompEvalIso01EJ n).symm

/-- **Stacks Project, Tag 01EJ.** The Čech complex functor on presheaves of
modules is exact. -/
@[stacks 01EJ]
public theorem presheafCechComplexFunctor_exact
    (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) (U : Opens X) {ι : Type w}
    (obj : ι → Opens X) (le : ∀ i, obj i ≤ U) :
    exactFunctor (PresheafOfModules.{max v w} R)
      (CochainComplex (ModuleCat.{max v w} (R.obj (op U))) ℕ)
      (presheafCechComplexFunctor R U obj le) := by
  have hSectionsLimits : PreservesFiniteLimits (sectionsOverFunctor R U) := by
    constructor
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation
    intro Y
    have : PreservesFiniteLimits (ModuleCat.restrictScalars.{max v w}
        (R.map ((Over.forget U).op.map (Over.mkIdTerminal.op.to Y))).hom) :=
      (restrictScalars_preservesFinite.{r, max v w} _).1
    have : PreservesLimitsOfShape J (sectionsOverFactor.{u, r, max v w} R U Y) :=
      (comp_preservesFiniteLimits _ _).preservesFiniteLimits J
    exact preservesLimitsOfShape_of_natIso (sectionsOverFactorIso.{u, r, max v w} R U Y).symm
  have hSectionsColimits : PreservesFiniteColimits (sectionsOverFunctor R U) := by
    constructor
    intro J _ _
    apply preservesColimitsOfShape_of_evaluation
    intro Y
    have : PreservesFiniteColimits (ModuleCat.restrictScalars.{max v w}
        (R.map ((Over.forget U).op.map (Over.mkIdTerminal.op.to Y))).hom) :=
      (restrictScalars_preservesFinite.{r, max v w} _).2
    have : PreservesColimitsOfShape J (sectionsOverFactor.{u, r, max v w} R U Y) :=
      (comp_preservesFiniteColimits _ _).preservesFiniteColimits J
    exact preservesColimitsOfShape_of_natIso (sectionsOverFactorIso.{u, r, max v w} R U Y).symm
  have hCechLimits : PreservesFiniteLimits
      (CategoryTheory.cechComplexFunctor
        (A := ModuleCat.{max v w} (R.obj (op U)))
        (fun i : ι ↦ Over.mk (homOfLE (le i)))) := by
    have : PreservesFiniteLimits (FormalCoproduct.evalOp.{w}
        (Over U) (ModuleCat.{max v w} (R.obj (op U)))) :=
      formalCoproductEvalOpPreservesFiniteLimits01EJ
    unfold CategoryTheory.cechComplexFunctor FormalCoproduct.cochainComplexFunctor
      FormalCoproduct.cosimplicialObjectFunctor
    infer_instance
  have hCechColimits : PreservesFiniteColimits
      (CategoryTheory.cechComplexFunctor
        (A := ModuleCat.{max v w} (R.obj (op U)))
        (fun i : ι ↦ Over.mk (homOfLE (le i)))) := by
    have : PreservesFiniteLimits (FormalCoproduct.evalOp.{w}
        (Over U) (ModuleCat.{max v w} (R.obj (op U)))) :=
      formalCoproductEvalOpPreservesFiniteLimits01EJ
    have : PreservesFiniteColimits (FormalCoproduct.evalOp.{w}
        (Over U) (ModuleCat.{max v w} (R.obj (op U)))) :=
      formalCoproductEvalOpPreservesFiniteColimits01EJ moduleCat_hasExactLimitsOfShape_discrete
    unfold CategoryTheory.cechComplexFunctor FormalCoproduct.cochainComplexFunctor
      FormalCoproduct.cosimplicialObjectFunctor
    infer_instance
  rw [exactFunctor_iff]
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

end Stacks.Cohomology.CechExactFunctor

end
