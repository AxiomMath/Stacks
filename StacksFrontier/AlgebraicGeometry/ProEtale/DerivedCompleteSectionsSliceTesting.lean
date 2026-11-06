module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WeaklyContractibleProducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Slice
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SliceTestingFamily
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
import all StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# Testing derived completeness on a slice testing family, in any module universe

`StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections` tests derived completeness of a
complex of sheaves of modules on a ringed site along a sheaf of ideals on derived sections over a
covering family of weakly contractible objects, for a small site and modules in the universe
`max u v` of the site. This file proves the same criterion for a site that is not assumed small,
with the sections of the modules in an arbitrary universe `max u v w` containing the site, the
weakly contractible objects being a `Stacks.WeaklyContractible.SliceTestingFamily` at that
universe. On a small site a covering collection of weakly contractible objects is such a family
by `Stacks.WeaklyContractible.SliceTestingFamily.ofIsWeaklyContractible`; the small pro-étale
site of a scheme, which is not essentially small, carries one in every universe.

The proofs are those of the small case: evaluation on a member of the family is exact, the
evaluations jointly reflect isomorphisms, and derived completeness at a scalar, invertibility of
`1 - f` on a countable product, is reflected by such a family; the structure sheaf of the slice
over a member acts on sheaves of modules there through the terminal object `U ⟶ U`.

## Main results

* `AlgebraicGeometry.RingedSite.evaluation_map_exact_of_sliceTestingFamily`: evaluation on a
  member of a slice testing family carries exact short complexes to exact short complexes.
* `AlgebraicGeometry.RingedSite.evaluation_preservesFiniteColimits_of_sliceTestingFamily`:
  evaluation on such a member preserves finite colimits.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_iff_derivedSections_of_sliceTestingFamily`:
  the testing criterion.

## Implementation notes

The helpers of `DerivedCompleteSections` that do not depend on the universe are used from there
(`import all`); those stated over sheaves of rings in the universe `max u v` are restated here in
the universe `max u v w`, under the suffix `OfSize`/`_ofSize`, and those taking the testing family
under the suffix `_of_sliceTestingFamily`.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace AlgebraicGeometry.RingedSite

private theorem evaluation_additive_ofSize
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v w}) (U : C) :
    (SheafOfModules.evaluation R (op U)).Additive where
  map_add := rfl

attribute [local instance] evaluation_additive_ofSize

private noncomputable def overEvaluationIsoOfSize
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v w})
    (U : C) (V : Over U) :
    SheafOfModules.overFunctor R U ⋙
        SheafOfModules.evaluation (R.over U) (op V) ≅
    SheafOfModules.evaluation R (op V.left) :=
  Iso.refl _

section TerminalSection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{max u v w}) [∀ W, IsMulCommutative (R.obj.obj W)]
  (T : C) (hT : IsTerminal T)

/-- Multiplication by the unit section over a terminal object is the identity. -/
private lemma terminalSectionToEnd_one_ofSize :
    Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v w, max u v w} R T hT 1 = 1 := by
  ext M V x
  show (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) 1) • x = x
  rw [map_one, one_smul]

/-- Multiplication by a product of sections over a terminal object composes the two
multiplications. -/
private lemma terminalSectionToEnd_mul_ofSize (f g : R.obj.obj (op T)) :
    Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v w, max u v w} R T hT (f * g) =
      Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v w, max u v w} R T hT f *
        Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v w, max u v w} R T hT g := by
  ext M V x
  show (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) (f * g)) • x =
    (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) f) •
      (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) g) • x
  rw [map_mul, mul_smul]

/-- Multiplication by the zero section over a terminal object is zero. -/
private lemma terminalSectionToEnd_zero_ofSize :
    Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v w, max u v w} R T hT 0 = 0 := by
  ext M V x
  show (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) 0) • x = 0
  rw [map_zero, zero_smul]

/-- Multiplication by a sum of sections over a terminal object is the sum of the two
multiplications. -/
private lemma terminalSectionToEnd_add_ofSize (f g : R.obj.obj (op T)) :
    Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v w, max u v w} R T hT (f + g) =
      Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v w, max u v w} R T hT f +
        Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v w, max u v w} R T hT g := by
  ext M V x
  show (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) (f + g)) • x =
    (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) f) • x +
      (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) g) • x
  rw [map_add, add_smul]

end TerminalSection

/-- Sections of the structure sheaf over `U` act on sheaves of modules on the slice site over
`U`, by multiplication by the section read over the terminal object `U ⟶ U` of the slice.

That the action is multiplicative, additive and unital is the four lemmas above, stated in the
slice's own vocabulary so that no proof has to identify the sections over `U` with the sections
of the slice structure sheaf over its terminal object. -/
private noncomputable def terminalScalarHomOfSize
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v w}) (U : C)
    [∀ V : (Over U)ᵒᵖ, IsMulCommutative ((R.over U).obj.obj V)] :
    (R.obj.obj (op U)) →+*
      CatCenter (SheafOfModules.{max u v w} (R.over U)) where
  toFun f := Stacks.SheafOfModules.terminalSectionToEnd (R.over U)
    (Over.mk (𝟙 U)) Over.mkIdTerminal f
  map_one' := terminalSectionToEnd_one_ofSize (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal
  map_mul' f g := terminalSectionToEnd_mul_ofSize (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal f g
  map_zero' := terminalSectionToEnd_zero_ofSize (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal
  map_add' f g := terminalSectionToEnd_add_ofSize (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal f g

private theorem terminalScalarHomOfSize_evaluation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v w}) (U : C)
    [CommSemiring (R.obj.obj (op U))]
    [∀ W : (Over U)ᵒᵖ, IsMulCommutative ((R.over U).obj.obj W)]
    (f : R.obj.obj (op U)) (M : SheafOfModules.{max u v w} (R.over U))
    (V : Over U) (x : M.val.obj (op V)) :
    ((((SheafOfModules.evaluation (R.over U) (op V)).map
      ((terminalScalarHomOfSize R U f).app M)).hom) x) =
      ((R.over U).obj.map (Over.mkIdTerminal.from V).op f) • x := by
  show ((((SheafOfModules.evaluation (R.over U) (op V)).map
      ((Stacks.SheafOfModules.terminalSectionToEnd (R.over U) (Over.mk (𝟙 U))
        Over.mkIdTerminal f).asHom.app M)).hom) x) = _
  exact Stacks.SheafOfModules.terminalSectionToEnd_apply (R.over U) (Over.mk (𝟙 U))
    Over.mkIdTerminal f M (op V) x

set_option maxHeartbeats 1000000 in
private theorem overEvaluation_linear_ofSize
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v w}) (U : C)
    [∀ W : (Over U)ᵒᵖ, IsMulCommutative ((R.over U).obj.obj W)]
    (V : Over U) :
    letI : IsMulCommutative (R.obj.obj (op U)) := by
      change IsMulCommutative ((R.over U).obj.obj (op (Over.mk (𝟙 U))))
      infer_instance
    letI : CommSemiring (R.obj.obj (op U)) := inferInstance
    letI : Linear (R.obj.obj (op U)) (SheafOfModules.{max u v w} (R.over U)) :=
      Linear.ofRingMorphism (terminalScalarHomOfSize R U)
    let A := R.obj.obj (op U)
    let B := (R.over U).obj.obj (op V)
    let ρ : A →+* B := ((R.over U).obj.map (Over.mkIdTerminal.from V).op).hom
    letI : IsMulCommutative B := inferInstance
    letI : CommSemiring B := inferInstance
    letI : Algebra A B := ρ.toAlgebra
    letI : Linear A (ModuleCat.{max u v w} B) := ModuleCat.Algebra.instLinear
    Functor.Linear (R.obj.obj (op U))
      (SheafOfModules.evaluation (R.over U) (op V)) := by
  let A := R.obj.obj (op U)
  let B := (R.over U).obj.obj (op V)
  let ρ : A →+* B := ((R.over U).obj.map (Over.mkIdTerminal.from V).op).hom
  let : IsMulCommutative A := by
    show IsMulCommutative ((R.over U).obj.obj (op (Over.mk (𝟙 U))))
    infer_instance
  let : IsMulCommutative B := by
    show IsMulCommutative ((R.over U).obj.obj (op V))
    infer_instance
  let : CommSemiring A := inferInstance
  let : CommSemiring B := inferInstance
  let : Algebra A B := ρ.toAlgebra
  let : Linear A (ModuleCat.{max u v w} B) := ModuleCat.Algebra.instLinear
  let : Linear A (SheafOfModules.{max u v w} (R.over U)) :=
    Linear.ofRingMorphism (terminalScalarHomOfSize R U)
  let E := SheafOfModules.evaluation (R.over U) (op V)
  show Functor.Linear A E
  refine ⟨fun {M N} g a => ?_⟩
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change ((E.map (((terminalScalarHomOfSize R U a).app M) ≫ g)).hom x) = _
  rw [Functor.map_comp]
  change (E.map g).hom ((E.map ((terminalScalarHomOfSize R U a).app M)).hom x) = _
  rw [terminalScalarHomOfSize_evaluation R U a M V x]
  change (E.map g).hom (ρ a • x) = ρ a • (E.map g).hom x
  exact map_smul _ _ _

/-! ### The statements at a weakly contractible testing family

On a `Type v`-small site a weakly contractible testing family supplies the bundles the
statements above consume, by `Stacks.WeaklyContractible.SlicedObjectsSituation.of`; these are
the resulting statements, in the form that only mentions the family. -/

/-- Evaluating a sheaf of modules on the slice site at an object `V ⟶ U`, after restricting it
to the slice, is evaluating it at `V`; this is the induced isomorphism of the functors on
derived categories. -/
private noncomputable def overEvaluationMapDerivedCategoryIsoOfSize
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v w}) [HasSheafify J AddCommGrpCat.{max u v w}]
    (U : C) (V : Over U)
    [(SheafOfModules.overFunctor.{max u v w} R U).Additive]
    [(SheafOfModules.evaluation.{max u v w} (R.over U) (op V)).Additive]
    [(SheafOfModules.evaluation.{max u v w} R (op V.left)).Additive]
    [PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v w} R U)]
    [PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v w} R U)]
    [PreservesFiniteLimits (SheafOfModules.evaluation.{max u v w} (R.over U) (op V))]
    [PreservesFiniteColimits (SheafOfModules.evaluation.{max u v w} (R.over U) (op V))]
    [hEvalLim : PreservesFiniteLimits (SheafOfModules.evaluation.{max u v w} R (op V.left))]
    [hEvalColim : PreservesFiniteColimits (SheafOfModules.evaluation.{max u v w} R (op V.left))] :
    (SheafOfModules.overFunctor.{max u v w} R U).mapDerivedCategory ⋙
        (SheafOfModules.evaluation.{max u v w} (R.over U) (op V)).mapDerivedCategory ≅
      (SheafOfModules.evaluation.{max u v w} R (op V.left)).mapDerivedCategory := by
  let F := SheafOfModules.overFunctor.{max u v w} R U
  let G := SheafOfModules.evaluation.{max u v w} (R.over U) (op V)
  letI : F.Additive := SheafOfModules.overFunctor_additive R U
  letI : G.Additive := evaluation_additive_ofSize (R.over U) V
  letI : (F ⋙ G).Additive := inferInstance
  let e : F ⋙ G ≅ SheafOfModules.evaluation.{max u v w} R (op V.left) :=
    overEvaluationIsoOfSize R U V
  exact CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl (F ⋙ G)) ≪≫
    @CategoryTheory.Functor.mapDerivedCategoryCongr
      (SheafOfModules.{max u v w} R) _ _ _
      (ModuleCat.{max u v w} ((R.over U).obj.obj (op V))) _ _ _
      (F ⋙ G) (SheafOfModules.evaluation.{max u v w} R (op V.left))
      _ _ _ (evaluation_additive_ofSize R V.left) hEvalLim hEvalColim e
private theorem evaluationFamily_jointlyReflectsIsomorphisms_of_sliceTestingFamily
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (R : Sheaf J RingCat.{max u v w})
    (h : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} C J) :
    JointlyReflectIsomorphisms
      (fun V : {U : C // h.B U} =>
        SheafOfModules.evaluation.{max u v w} R (op V.1)) := by
  let : Abelian (SheafOfModules.{max u v w} R) := SheafOfModules.instAbelian R
  let : HasZeroObject (SheafOfModules.{max u v w} R) := by infer_instance
  let : Balanced (SheafOfModules.{max u v w} R) := by infer_instance
  refine ⟨?_⟩
  intro M N g hg
  have hexact : ∀ S : ShortComplex (SheafOfModules.{max u v w} R),
      (∀ V, ∀ hV : h.B V,
        (S.map (SheafOfModules.evaluation.{max u v w} R (op V))).Exact) → S.Exact := fun S hS =>
    (Stacks.WeaklyContractible.SliceTestingFamily.exact_iff_exact_sections J h R S).2
      @fun V hV => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS V hV)
  have hmono : Mono g := by
    let S : ShortComplex (SheafOfModules.{max u v w} R) :=
      ShortComplex.mk (0 : 0 ⟶ M) g (by simp)
    refine (S.exact_iff_mono (by simp [S])).1 (hexact S fun V hV => ?_)
    let : (SheafOfModules.evaluation.{max u v w} R (op V)).Additive :=
      evaluation_additive_ofSize R V
    let : IsIso ((SheafOfModules.evaluation.{max u v w} R (op V)).map g) := hg ⟨V, hV⟩
    exact (ShortComplex.exact_iff_mono _ (by simp [S])).2 (by dsimp [S]; infer_instance)
  have hepi : Epi g := by
    let S : ShortComplex (SheafOfModules.{max u v w} R) :=
      ShortComplex.mk g (0 : N ⟶ 0) (by simp)
    refine (S.exact_iff_epi (by simp [S])).1 (hexact S fun V hV => ?_)
    let : (SheafOfModules.evaluation.{max u v w} R (op V)).Additive :=
      evaluation_additive_ofSize R V
    let : IsIso ((SheafOfModules.evaluation.{max u v w} R (op V)).map g) := hg ⟨V, hV⟩
    exact (ShortComplex.exact_iff_epi _ (by simp [S])).2 (by dsimp [S]; infer_instance)
  exact isIso_of_mono_of_epi g

/-- Evaluation of sheaves of modules on a member of a weakly contractible testing family
preserves finite colimits.

Over such an object exactness of a short complex of sheaves of modules is exactness of the
evaluated complex, and an additive functor between abelian categories carrying short exact
sequences to short exact sequences is exact. -/
theorem evaluation_preservesFiniteColimits_of_sliceTestingFamily
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (R : Sheaf J RingCat.{max u v w})
    (h : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} C J)
    (U : C) (hU : h.B U) :
    PreservesFiniteColimits (SheafOfModules.evaluation.{max u v w} R (op U)) := by
  let E := SheafOfModules.evaluation.{max u v w} R (op U)
  let : Abelian (SheafOfModules.{max u v w} R) := SheafOfModules.instAbelian R
  let : E.Additive := evaluation_additive_ofSize R U
  have hExact : ∀ (S : ShortComplex (SheafOfModules.{max u v w} R)),
      S.Exact → (S.map E).Exact := fun S hS =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map E)).2
      ((Stacks.WeaklyContractible.SliceTestingFamily.exact_iff_exact_sections J h R S).1 hS
        (U := U) hU)
  have hFinite : PreservesFiniteLimits E ∧ PreservesFiniteColimits E :=
    ((Functor.exact_tfae E).out 2 4).mp hExact
  exact hFinite.2

/-- Countable products of sheaves of modules on a site with a weakly contractible testing family
are exact. -/
private theorem exactProducts_sheafOfModules_of_sliceTestingFamily
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (R : Sheaf J RingCat.{max u v w})
    (h : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} C J) :
    HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{max u v w} R) :=
  Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat
    (R := R) h.B h.hasEnoughObjects fun _ hU _ _ φ hφ => h.surjective_app hU φ hφ
private theorem overFunctor_preservesFiniteColimits_of_sliceTestingFamily
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (R : Sheaf J RingCat.{max u v w})
    (h : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} C J) (U : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v w} R U) := by
  let : Abelian (SheafOfModules.{max u v w} R) := SheafOfModules.instAbelian R
  let hOver := Stacks.WeaklyContractible.SliceTestingFamily.over J h U
  let E := fun V : {V : Over U // hOver.B V} =>
    SheafOfModules.evaluation (R.over U) (op V.1)
  let : ∀ V, PreservesFiniteColimits (E V) := fun V =>
    evaluation_preservesFiniteColimits_of_sliceTestingFamily (R.over U) hOver V.1 V.2
  let : ∀ V, PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v w} R U ⋙ E V) :=
    fun V => by
      show PreservesFiniteColimits (SheafOfModules.evaluation R (op V.1.left))
      exact evaluation_preservesFiniteColimits_of_sliceTestingFamily R h V.1.left V.2
  exact preservesFiniteColimits_of_jointlyReflects (SheafOfModules.overFunctor.{max u v w} R U) E
    (evaluationFamily_jointlyReflectsIsomorphisms_of_sliceTestingFamily (R.over U) hOver)

private theorem overFunctor_preservesFiniteLimits_of_sliceTestingFamily
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (R : Sheaf J RingCat.{max u v w})
    (h : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} C J) (U : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v w} R U) := by
  let F := SheafOfModules.overFunctor.{max u v w} R U
  let : F.Additive := SheafOfModules.overFunctor_additive R U
  let hOver := Stacks.WeaklyContractible.SliceTestingFamily.over J h U
  have hExact : ∀ (S : ShortComplex (SheafOfModules.{max u v w} R)),
      S.Exact → (S.map F).Exact := by
    intro complex hExact
    apply (Stacks.WeaklyContractible.SliceTestingFamily.exact_iff_exact_sections (J.over U) hOver
      (R.over U) (complex.map F)).mpr
    intro V hV
    show Function.Exact (complex.f.val.app (op V.left))
      (complex.g.val.app (op V.left))
    exact (Stacks.WeaklyContractible.SliceTestingFamily.exact_iff_exact_sections J h R
      complex).mp hExact hV
  have hFinite : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    ((Functor.exact_tfae F).out 2 4).mp hExact
  exact hFinite.1

/-- Evaluation on a member of a weakly contractible testing family carries an exact short
complex of sheaves of modules to an exact short complex of modules.

Exactness of a short complex of sheaves of modules is exactness of the underlying complex of
abelian sheaves, which weak contractibility detects on sections. -/
theorem evaluation_map_exact_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (U : X.C) (hU : B.B U)
    (S : ShortComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hS : S.Exact) :
    (S.map
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U))).Exact := by
  rw [ShortComplex.exact_iff_exact_map_forget₂]
  rw [ShortComplex.ab_exact_iff_function_exact]
  have hs := (Stacks.WeaklyContractible.SliceTestingFamily.exact_iff_exact_sections X.J B
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) S).mp hS hU
  convert hs using 1 <;> rfl

/-- Derived completeness of a complex of sheaves of modules can be tested on
derived sections over a covering family of weakly contractible objects. -/
public theorem isDerivedComplete_iff_derivedSections_of_sliceTestingFamily
    (X : AlgebraicGeometry.RingedSite.{u, v, max u v w})
    (h : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I K ↔
      ∀ (U : X.C), h.B U →
        let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
        letI : IsMulCommutative R := by
          change IsMulCommutative (X.O.obj.obj (op U))
          infer_instance
        let F := SheafOfModules.evaluation.{max u v w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
        ∃ hAdd : F.Additive,
        ∃ hLim : PreservesFiniteLimits F,
        ∃ hColim : PreservesFiniteColimits F,
        ∃ hProd : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v w} R)),
          letI : F.Additive := hAdd
          letI : PreservesFiniteLimits F := hLim
          letI : PreservesFiniteColimits F := hColim
          letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v w} R)) := hProd
          ∀ f : R, f ∈ I.toSubmodule.obj (op U) →
            IsDerivedCompleteAt (F.mapDerivedCategory.obj K) f := by
  rw [AlgebraicGeometry.RingedSite.isDerivedComplete_iff]
  constructor
  · intro hCompleteAll U hU
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    let : IsMulCommutative R := by
      show IsMulCommutative (X.O.obj.obj (op U))
      infer_instance
    let : CommSemiring R := inferInstance
    let E := SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    let hAdd : E.Additive := evaluation_additive_ofSize _ U
    let hLim : PreservesFiniteLimits E :=
      SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
    let hColim : PreservesFiniteColimits E :=
      evaluation_preservesFiniteColimits_of_sliceTestingFamily
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h U hU
    let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v w} R) :=
      moduleCat_hasExactLimitsOfShape_discrete.{max u v w} R ℕ
    let hProd : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v w} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    refine ⟨hAdd, hLim, hColim, hProd, ?_⟩
    intro f hf
    obtain ⟨hSliceAdd, hSliceLim, hSliceColim, hSliceProd, hSliceComplete⟩ :=
      hCompleteAll U f hf
    let ROver := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U
    let A := SheafOfModules.{max u v w} ROver
    let F := SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let hOver := Stacks.WeaklyContractible.SliceTestingFamily.over X.J h U
    let : ∀ V : (Over U)ᵒᵖ, IsMulCommutative (ROver.obj.obj V) := fun V => by
      show IsMulCommutative (X.O.obj.obj (op V.unop.left))
      infer_instance
    let terminal : Over U := Over.mk (𝟙 U)
    let : ∀ W : (Over terminal)ᵒᵖ,
        IsMulCommutative ((ROver.over terminal).obj.obj W) := fun W => by
      show IsMulCommutative (ROver.obj.obj (op W.unop.left))
      infer_instance
    let : Linear (CatCenter A) A :=
      Linear.ofRingMorphism (RingHom.id (CatCenter A))
    let φ : R →+* CatCenter A :=
      terminalScalarHomOfSize (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let : Linear R A := Linear.ofRingMorphism
      (terminalScalarHomOfSize (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    let : F.Additive := hSliceAdd
    let : PreservesFiniteLimits F := hSliceLim
    let : PreservesFiniteColimits F := hSliceColim
    let : HasProductsOfShape ℕ (DerivedCategory A) := hSliceProd
    let D := DerivedCategory A
    let K' := F.mapDerivedCategory.obj K
    let : Linear R D := inferInstance
    have hφf : φ f =
        Stacks.SheafOfModules.terminalSectionToEnd ROver (Over.mk (𝟙 U)) Over.mkIdTerminal f := rfl
    have hSliceCompleteCenter : IsDerivedCompleteAt K' (φ f) := by
      rw [hφf]
      exact hSliceComplete
    let hCompleteR : IsDerivedCompleteAt K' f := by
      have hsmul : ∀ {Y Z : D} (g : Y ⟶ Z), f • g = (φ f) • g := by
        intro Y Z g
        rfl
      exact (isDerivedCompleteAt_ringHom f (φ f) K' hsmul).mpr hSliceCompleteCenter
    let : HasSheafify (X.J.over U) AddCommGrpCat.{max u v w} := inferInstance
    let : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v w} := inferInstance
    let : HasExactLimitsOfShape (Discrete ℕ) A :=
      exactProducts_sheafOfModules_of_sliceTestingFamily ROver hOver
    let hJoint : JointlyReflectIsomorphisms
        (fun V : {V : Over U // hOver.B V} =>
          SheafOfModules.evaluation.{max u v w} ROver (op V.1)) :=
      evaluationFamily_jointlyReflectsIsomorphisms_of_sliceTestingFamily ROver hOver
    let Eval := fun V : {V : Over U // hOver.B V} =>
      SheafOfModules.evaluation.{max u v w} ROver (op V.1)
    let : ∀ V : {V : Over U // hOver.B V},
        Algebra R (ROver.obj.obj (op V.1)) := fun V => by
      let ρ : R →+* ROver.obj.obj (op V.1) :=
        (ROver.obj.map (Over.mkIdTerminal.from V.1).op).hom
      exact ρ.toAlgebra
    let evaluationLinear : ∀ V : {V : Over U // hOver.B V}, Linear R
        (ModuleCat.{max u v w} (ROver.obj.obj (op V.1))) := fun V => by
      let B := ROver.obj.obj (op V.1)
      let : CommSemiring B := inferInstance
      let ρ : R →+* B :=
        (ROver.obj.map (Over.mkIdTerminal.from V.1).op).hom
      let : Algebra R B := ρ.toAlgebra
      exact @ModuleCat.Algebra.instLinear R (inferInstance : CommSemiring R) B
        (inferInstance : Ring B) (ρ.toAlgebra)
    let : ∀ V : {V : Over U // hOver.B V}, (Eval V).Additive :=
      fun V => evaluation_additive_ofSize ROver V.1
    let : ∀ V : {V : Over U // hOver.B V}, PreservesFiniteLimits (Eval V) :=
      fun V => inferInstance
    let : ∀ V : {V : Over U // hOver.B V}, PreservesFiniteColimits (Eval V) := fun V =>
      evaluation_preservesFiniteColimits_of_sliceTestingFamily ROver hOver V.1 V.2
    let : ∀ V : {V : Over U // hOver.B V}, Functor.Linear R (Eval V) := fun V => by
      show Functor.Linear R
        (SheafOfModules.evaluation
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) (op V.1))
      exact overEvaluation_linear_ofSize (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U V.1
    let : ∀ V : {V : Over U // hOver.B V},
        PreservesLimitsOfShape (Discrete ℕ) (Eval V) := fun V => inferInstance
    let : ∀ V : {V : Over U // hOver.B V}, HasExactLimitsOfShape (Discrete ℕ)
        (ModuleCat.{max u v w} (ROver.obj.obj (op V.1))) := fun V =>
      moduleCat_hasExactLimitsOfShape_discrete.{max u v w} _ ℕ
    let : ∀ V : {V : Over U // hOver.B V}, HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v w} (ROver.obj.obj (op V.1)))) := fun V =>
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let EV := fun V => (Eval V).mapDerivedCategory
    let : ∀ V : {V : Over U // hOver.B V},
        PreservesLimitsOfShape (Discrete ℕ) (EV V) := fun V =>
      Functor.preservesProducts_mapDerivedCategory ℕ (Eval V)
    let hJointD : JointlyReflectIsomorphisms EV :=
      jointlyReflectsIsomorphisms_mapDerivedCategory Eval hJoint
    let hEvalComplete :=
      (isDerivedCompleteAt_iff_of_jointlyReflects EV hJointD).mp hCompleteR
    have hterminal : hOver.B terminal := hU
    let terminalLinear : Linear R (ModuleCat.{max u v w} R) :=
      evaluationLinear ⟨terminal, hterminal⟩
    let : PreservesFiniteColimits
        (SheafOfModules.evaluation ROver (op terminal)) :=
      evaluation_preservesFiniteColimits_of_sliceTestingFamily ROver hOver terminal hterminal
    let : PreservesFiniteLimits E := hLim
    let : PreservesFiniteColimits E := hColim
    let : Linear R (ModuleCat.{max u v w} R) := ModuleCat.instLinear
    let : PreservesFiniteColimits
        (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op terminal.left)) :=
      hColim
    let : Linear R (ModuleCat.{max u v w} (ROver.obj.obj (op terminal))) :=
      ModuleCat.instLinear
    let : HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v w} (ROver.obj.obj (op terminal)))) := hProd
    let : PreservesFiniteLimits
        (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op terminal.left)) :=
      hLim
    let e := overEvaluationMapDerivedCategoryIsoOfSize
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U terminal
    have hglobal : IsDerivedCompleteAt (E.mapDerivedCategory.obj K) f := by
      have hAt := hEvalComplete ⟨terminal, hterminal⟩
      have hIso := e.app K
      have hAtNative : IsDerivedCompleteAt ((EV ⟨terminal, hterminal⟩).obj K') f := by
        apply (@isDerivedCompleteAt_ringHom R R
          (DerivedCategory (ModuleCat.{max u v w} R)) _ _ _ _
          (@DerivedCategory.instLinear R _ (ModuleCat.{max u v w} R) _ _ terminalLinear _)
          (inferInstance : Linear R (DerivedCategory (ModuleCat.{max u v w} R)))
          _ f f _ ?_).mp hAt
        intro Y Z morphism
        apply @derivedCategory_smul_eq R R (ModuleCat.{max u v w} R) _ _ _ _ _
          terminalLinear ModuleCat.instLinear f f ?_ Y Z morphism
        intro M N map
        ext x
        show (show R from ROver.obj.map (Over.mkIdTerminal.from terminal).op f) •
          map.hom x = f • map.hom x
        have hid : Over.mkIdTerminal.from terminal = 𝟙 terminal :=
          Over.mkIdTerminal.hom_ext _ _
        rw [hid, op_id, CategoryTheory.Functor.map_id]
        rfl
      exact (DerivedCompleteRecurrence.isDerivedCompleteAt_iff_of_iso hIso f).mp hAtNative
    exact hglobal
  · intro hSections U f hf
    let ROver := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U
    let A := SheafOfModules.{max u v w} ROver
    let F := SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let hOver := Stacks.WeaklyContractible.SliceTestingFamily.over X.J h U
    let : F.Additive := SheafOfModules.overFunctor_additive _ U
    let : PreservesFiniteLimits F :=
      overFunctor_preservesFiniteLimits_of_sliceTestingFamily
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h U
    let : PreservesFiniteColimits F :=
      overFunctor_preservesFiniteColimits_of_sliceTestingFamily
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h U
    let : HasExactLimitsOfShape (Discrete ℕ) A :=
      exactProducts_sheafOfModules_of_sliceTestingFamily ROver hOver
    let : HasProductsOfShape ℕ (DerivedCategory A) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    let : IsMulCommutative R := by
      show IsMulCommutative (X.O.obj.obj (op U))
      infer_instance
    let : ∀ V : (Over U)ᵒᵖ, IsMulCommutative (ROver.obj.obj V) := fun V => by
      show IsMulCommutative (X.O.obj.obj (op V.unop.left))
      infer_instance
    let φ := terminalScalarHomOfSize (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
    let : Linear R A := Linear.ofRingMorphism φ
    let K' := F.mapDerivedCategory.obj K
    have hφf : φ f =
        Stacks.SheafOfModules.terminalSectionToEnd ROver (Over.mk (𝟙 U)) Over.mkIdTerminal f := rfl
    rw [← hφf]
    apply (isDerivedCompleteAt_ringHom f (φ f) K' (fun g => by
      apply derivedCategory_smul_eq f (φ f)
      intro M N morphism
      rfl)).mp
    let Eval := fun V : {V : Over U // hOver.B V} =>
      SheafOfModules.evaluation.{max u v w} ROver (op V.1)
    let : ∀ V : {V : Over U // hOver.B V},
        Algebra R (ROver.obj.obj (op V.1)) := fun V =>
      (ROver.obj.map (Over.mkIdTerminal.from V.1).op).hom.toAlgebra
    let : ∀ V : {V : Over U // hOver.B V}, Linear R
        (ModuleCat.{max u v w} (ROver.obj.obj (op V.1))) := fun V =>
      ModuleCat.Algebra.instLinear
    let : ∀ V : {V : Over U // hOver.B V}, (Eval V).Additive :=
      fun V => evaluation_additive_ofSize ROver V.1
    let : ∀ V : {V : Over U // hOver.B V}, PreservesFiniteLimits (Eval V) :=
      fun V => inferInstance
    let : ∀ V : {V : Over U // hOver.B V}, PreservesFiniteColimits (Eval V) := fun V =>
      evaluation_preservesFiniteColimits_of_sliceTestingFamily ROver hOver V.1 V.2
    let : ∀ V : {V : Over U // hOver.B V}, Functor.Linear R (Eval V) := fun V =>
      overEvaluation_linear_ofSize (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U V.1
    let : ∀ V : {V : Over U // hOver.B V}, HasExactLimitsOfShape (Discrete ℕ)
        (ModuleCat.{max u v w} (ROver.obj.obj (op V.1))) := fun V =>
      moduleCat_hasExactLimitsOfShape_discrete.{max u v w} _ ℕ
    let : ∀ V : {V : Over U // hOver.B V}, HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v w} (ROver.obj.obj (op V.1)))) := fun V =>
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let EV := fun V => (Eval V).mapDerivedCategory
    let : ∀ V : {V : Over U // hOver.B V},
        PreservesLimitsOfShape (Discrete ℕ) (EV V) := fun V =>
      Functor.preservesProducts_mapDerivedCategory ℕ (Eval V)
    have hJointD : JointlyReflectIsomorphisms EV :=
      jointlyReflectsIsomorphisms_mapDerivedCategory Eval
        (evaluationFamily_jointlyReflectsIsomorphisms_of_sliceTestingFamily ROver hOver)
    apply (isDerivedCompleteAt_iff_of_jointlyReflects EV hJointD).mpr
    intro V
    obtain ⟨hAdd, hLim, hColim, hProd, hComplete⟩ := hSections V.1.left V.2
    let E := SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op V.1.left)
    let : E.Additive := hAdd
    let : PreservesFiniteLimits E := hLim
    let : PreservesFiniteColimits E := hColim
    let : HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v w} (ROver.obj.obj (op V.1)))) := hProd
    let b := ROver.obj.map (Over.mkIdTerminal.from V.1).op f
    have hb : b ∈ I.toSubmodule.obj (op V.1.left) := by
      have hmem := I.toSubmodule.map_mem V.1.hom.op hf
      change (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map V.1.hom.op f ∈
        I.toSubmodule.obj (op V.1.left) at hmem
      show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map
        ((Over.mkIdTerminal.from V.1).left).op f ∈ I.toSubmodule.obj (op V.1.left)
      rw [Over.mkIdTerminal_from_left]
      exact hmem
    have hAt := hComplete b hb
    let : Linear (ROver.obj.obj (op V.1))
        (ModuleCat.{max u v w} (ROver.obj.obj (op V.1))) := ModuleCat.instLinear
    let e := overEvaluationMapDerivedCategoryIsoOfSize
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U V.1
    have hAtSlice : IsDerivedCompleteAt ((EV V).obj K') b :=
      (DerivedCompleteRecurrence.isDerivedCompleteAt_iff_of_iso (e.app K) b).mpr hAt
    apply (isDerivedCompleteAt_ringHom f b ((EV V).obj K') ?_).mpr hAtSlice
    intro Y Z g
    apply derivedCategory_smul_eq f b
    intro M N morphism
    rfl
end AlgebraicGeometry.RingedSite

end
