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
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Slice
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence

/-!
# Testing derived completeness on weakly contractible objects

Derived completeness of a complex of sheaves of modules over a ringed site, along a sheaf of
ideals in its structure sheaf, can be tested on derived sections over a covering family of
weakly contractible objects.

On a weakly contractible object evaluation of a sheaf of modules is exact, because exactness of
a short complex of sheaves of modules is detected on sections there; so the induced functor on
derived categories computes derived sections, and the evaluations on a covering family jointly
reflect isomorphisms. Derived completeness at a scalar is invertibility of `1 - f` on a
countable product, a condition such a family reflects. Transporting the criterion between the
site and its slice over the object is what makes the scalar on the slice a section over the
object itself: the structure sheaf of the slice site acts on sheaves of modules there through
the terminal object `U ⟶ U`, whose sections are the sections over `U`.

## Main results

* `AlgebraicGeometry.RingedSite.evaluation_map_exact`: evaluation on a member of a weakly
  contractible testing family carries exact short complexes to exact short complexes.
* `AlgebraicGeometry.RingedSite.evaluation_preservesFiniteColimits`: evaluation on such an
  object preserves finite colimits.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_iff_derivedSections`: the testing criterion.
* `CategoryTheory.Limits.preservesProducts_of_comp_of_essSurj`: products preserved by a
  composite with an essentially surjective first factor are preserved by the second factor.
* `CategoryTheory.Functor.preservesProducts_mapDerivedCategory`: an exact functor preserving
  products of a given shape induces one on derived categories.

## Implementation notes

The right-hand side of the criterion carries the properties evaluation enjoys over a weakly
contractible object — additivity, exactness, and countable products in the target derived
category — as explicit existentials, since they are consequences of weak contractibility rather
than data available beforehand.

The scalar `f` is a section of the sheaf of ideals over the object, read as an element of the
ring of sections by `AlgebraicGeometry.RingedSite.idealSections`.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory.Limits

/-- If a functor `F` preserves products of shape `J` after precomposition with an essentially
surjective functor `L` which itself preserves them, then `F` preserves them.

Every object in the target of `L` is isomorphic to one of the form `L.obj Y`, and the product
comparison map is an isomorphism on such families by hypothesis; it is then an isomorphism on
every family, since the comparison maps of isomorphic families differ by isomorphisms. -/
theorem preservesProducts_of_comp_of_essSurj
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : Type) [HasProductsOfShape J C] [HasProductsOfShape J D]
    [HasProductsOfShape J E] (L : C ⥤ D) [L.EssSurj] (F : D ⥤ E)
    [PreservesLimitsOfShape (Discrete J) L]
    [PreservesLimitsOfShape (Discrete J) (L ⋙ F)] :
    PreservesLimitsOfShape (Discrete J) F := by
  apply Stacks.DerivedProducts.preservesLimitsOfShape_discrete_of_isIso_piComparison
  intro X
  let Y : J → C := fun j => L.objPreimage (X j)
  let e (j : J) : L.obj (Y j) ≅ X j := L.objObjPreimageIso (X j)
  have h : IsIso (piComparison (L ⋙ F) Y) := inferInstance
  rw [Stacks.DerivedProducts.piComparison_comp_eq] at h
  have : IsIso (piComparison F (fun j => L.obj (Y j))) :=
    IsIso.of_isIso_comp_left (F.map (piComparison L Y)) _
  have hi : IsIso (Limits.Pi.map (fun j => (e j).hom)) := by
    show IsIso (Limits.Pi.mapIso e).hom
    infer_instance
  have hj : IsIso (Limits.Pi.map (fun j => F.map (e j).hom)) := by
    show IsIso (Limits.Pi.mapIso (fun j => F.mapIso (e j))).hom
    infer_instance
  have hc : IsIso (F.map (Limits.Pi.map (fun j => (e j).hom)) ≫ piComparison F X) := by
    rw [← Stacks.DerivedProducts.piComparison_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (Limits.Pi.map (fun j => (e j).hom))) _


end CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- An exact functor of abelian categories preserving products of shape `J` induces a functor of
derived categories preserving products of that shape.

Both derived categories have products of shape `J`, because products are exact there, and the
localization functor preserves them; so the claim follows from the composite
`DerivedCategory.Q ⋙ F.mapDerivedCategory` preserving them, which `mapDerivedCategoryFactors`
identifies with `F.mapHomologicalComplex _ ⋙ DerivedCategory.Q`. -/
theorem preservesProducts_mapDerivedCategory
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (J : Type) [HasProductsOfShape J C] [HasProductsOfShape J D]
    [HasExactLimitsOfShape (Discrete J) C] [HasExactLimitsOfShape (Discrete J) D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete J) F] :
    PreservesLimitsOfShape (Discrete J) F.mapDerivedCategory := by
  let : HasProductsOfShape J (DerivedCategory C) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let : HasProductsOfShape J (DerivedCategory D) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let : PreservesLimitsOfShape (Discrete J) (DerivedCategory.Q (C := C)) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let : PreservesLimitsOfShape (Discrete J) (DerivedCategory.Q (C := D)) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let : PreservesLimitsOfShape (Discrete J) (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact Limits.preservesProducts_of_comp_of_essSurj J DerivedCategory.Q F.mapDerivedCategory

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSite

private theorem jointlyReflectsIsomorphisms_mapDerivedCategory
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {ι : Type*} {D : ι → Type*} [∀ i, Category (D i)] [∀ i, Abelian (D i)]
    [∀ i, HasDerivedCategory (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive]
    [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
    (hF : JointlyReflectIsomorphisms F) :
    JointlyReflectIsomorphisms (fun i => (F i).mapDerivedCategory) where
  isIso {X Y} g hg := by
    rw [DerivedCategory.isIso_iff]
    intro n
    let e₀ (i : ι) :
        (F i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor (D i) (ComplexShape.up ℤ) n ≅
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F i :=
      NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso (F i)) (fun ψ =>
        ShortComplex.mapHomologyIso_hom_naturality
          ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map ψ) (F i))
    let e (i : ι) :
        (F i).mapDerivedCategory ⋙ DerivedCategory.homologyFunctor (D i) n ≅
        DerivedCategory.homologyFunctor C n ⋙ F i :=
      Localization.liftNatIso DerivedCategory.Q
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
        (DerivedCategory.Q ⋙ ((F i).mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor (D i) n))
        (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C n ⋙ F i)) _ _
        (Functor.isoWhiskerRight (F i).mapDerivedCategoryFactors
            (DerivedCategory.homologyFunctor (D i) n) ≪≫
          Functor.isoWhiskerLeft ((F i).mapHomologicalComplex (ComplexShape.up ℤ))
            (DerivedCategory.homologyFunctorFactors (D i) n) ≪≫
          e₀ i ≪≫
          Functor.isoWhiskerRight
            (DerivedCategory.homologyFunctorFactors C n).symm (F i))
    let : ∀ i, IsIso ((F i).map ((DerivedCategory.homologyFunctor C n).map g)) := by
      intro i
      have hi : IsIso (((F i).mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor (D i) n).map g) := by
        show IsIso ((DerivedCategory.homologyFunctor (D i) n).map
          ((F i).mapDerivedCategory.map g))
        infer_instance
      exact (NatIso.isIso_map_iff (e i) g).mp hi
    exact hF.isIso ((DerivedCategory.homologyFunctor C n).map g)

private theorem isDerivedCompleteAt_iff_of_jointlyReflects
    {A : Type*} [CommSemiring A] {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] {ι : Type*} {D : ι → Type*}
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] [∀ i, Linear A (D i)]
    [∀ i, HasProductsOfShape ℕ (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive] [∀ i, (F i).Linear A]
    [∀ i, PreservesLimitsOfShape (Discrete ℕ) (F i)]
    (hF : JointlyReflectIsomorphisms F) {K : C} {f : A} :
    IsDerivedCompleteAt K f ↔ ∀ i, IsDerivedCompleteAt ((F i).obj K) f := by
  have he : ∀ i, (F i).map (oneSubSmulShift K f) ≫ piComparison (F i) (fun _ : ℕ => K) =
      piComparison (F i) (fun _ : ℕ => K) ≫ oneSubSmulShift ((F i).obj K) f := fun i => by
    apply Limits.Pi.hom_ext
    intro n
    calc
      ((F i).map (oneSubSmulShift K f) ≫ piComparison (F i)
          (fun _ : ℕ => K)) ≫ Pi.π (fun _ : ℕ => (F i).obj K) n =
        (F i).map (oneSubSmulShift K f) ≫ (F i).map (Pi.π (fun _ : ℕ => K) n) := by
          rw [Category.assoc, piComparison_comp_π]
      _ = (F i).map (Pi.π (fun _ : ℕ => K) n -
          f • Pi.π (fun _ : ℕ => K) (n + 1)) := by
        rw [← Functor.map_comp, oneSubSmulShift_π]
      _ = (F i).map (Pi.π (fun _ : ℕ => K) n) -
          f • (F i).map (Pi.π (fun _ : ℕ => K) (n + 1)) := by
        rw [Functor.map_sub, Functor.Linear.map_smul]
      _ = (piComparison (F i) (fun _ : ℕ => K) ≫
            oneSubSmulShift ((F i).obj K) f) ≫
          Pi.π (fun _ : ℕ => (F i).obj K) n := by
        simp [oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul, Category.assoc]
  simp only [isDerivedCompleteAt_iff_isIso]
  constructor
  · intro h i
    have : IsIso ((F i).map (oneSubSmulShift K f) ≫ piComparison (F i) fun _ : ℕ => K) := by
      infer_instance
    rw [he i] at this
    exact IsIso.of_isIso_comp_left (piComparison (F i) fun _ : ℕ => K) _
  · intro h
    have : ∀ i, IsIso ((F i).map (oneSubSmulShift K f)) := fun i => by
      have : IsIso (piComparison (F i) (fun _ : ℕ => K) ≫ oneSubSmulShift ((F i).obj K) f) := by
        have := h i
        infer_instance
      rw [← he i] at this
      exact IsIso.of_isIso_comp_right _ (piComparison (F i) fun _ : ℕ => K)
    exact hF.isIso (oneSubSmulShift K f)

private theorem evaluation_additive
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C) :
    (SheafOfModules.evaluation R (op U)).Additive where
  map_add := rfl

attribute [local instance] evaluation_additive

private noncomputable def overEvaluationIso
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v})
    (U : C) (V : Over U) :
    SheafOfModules.overFunctor R U ⋙
        SheafOfModules.evaluation (R.over U) (op V) ≅
    SheafOfModules.evaluation R (op V.left) :=
  Iso.refl _

/-- Evaluating a sheaf of modules on the slice site at an object `V ⟶ U`, after restricting it
to the slice, is evaluating it at `V`; this is the induced isomorphism of the functors on
derived categories. -/
private noncomputable def overEvaluationMapDerivedCategoryIsoOfSliceSheafify
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) [HasSheafify J AddCommGrpCat.{max u v}]
    (U : C) (V : Over U)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(SheafOfModules.overFunctor.{max u v} R U).Additive]
    [(SheafOfModules.evaluation.{max u v} (R.over U) (op V)).Additive]
    [(SheafOfModules.evaluation.{max u v} R (op V.left)).Additive]
    [PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v} R U)]
    [PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v} R U)]
    [PreservesFiniteLimits (SheafOfModules.evaluation.{max u v} (R.over U) (op V))]
    [PreservesFiniteColimits (SheafOfModules.evaluation.{max u v} (R.over U) (op V))]
    [hEvalLim : PreservesFiniteLimits (SheafOfModules.evaluation.{max u v} R (op V.left))]
    [hEvalColim : PreservesFiniteColimits (SheafOfModules.evaluation.{max u v} R (op V.left))] :
    (SheafOfModules.overFunctor.{max u v} R U).mapDerivedCategory ⋙
        (SheafOfModules.evaluation.{max u v} (R.over U) (op V)).mapDerivedCategory ≅
      (SheafOfModules.evaluation.{max u v} R (op V.left)).mapDerivedCategory := by
  let F := SheafOfModules.overFunctor.{max u v} R U
  let G := SheafOfModules.evaluation.{max u v} (R.over U) (op V)
  letI : F.Additive := SheafOfModules.overFunctor_additive R U
  letI : G.Additive := evaluation_additive (R.over U) V
  letI : (F ⋙ G).Additive := inferInstance
  let e : F ⋙ G ≅ SheafOfModules.evaluation.{max u v} R (op V.left) :=
    overEvaluationIso R U V
  exact CategoryTheory.Functor.mapDerivedCategoryCompIso (Iso.refl (F ⋙ G)) ≪≫
    @CategoryTheory.Functor.mapDerivedCategoryCongr
      (SheafOfModules.{max u v} R) _ _ _
      (ModuleCat.{max u v} ((R.over U).obj.obj (op V))) _ _ _
      (F ⋙ G) (SheafOfModules.evaluation.{max u v} R (op V.left))
      _ _ _ (evaluation_additive R V.left) hEvalLim hEvalColim e

section TerminalSection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{max u v}) [∀ W, IsMulCommutative (R.obj.obj W)]
  (T : C) (hT : IsTerminal T)

/-- Multiplication by the unit section over a terminal object is the identity. -/
private lemma terminalSectionToEnd_one :
    Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v, max u v} R T hT 1 = 1 := by
  ext M V x
  show (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) 1) • x = x
  rw [map_one, one_smul]

/-- Multiplication by a product of sections over a terminal object composes the two
multiplications. -/
private lemma terminalSectionToEnd_mul (f g : R.obj.obj (op T)) :
    Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v, max u v} R T hT (f * g) =
      Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v, max u v} R T hT f *
        Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v, max u v} R T hT g := by
  ext M V x
  show (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) (f * g)) • x =
    (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) f) •
      (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) g) • x
  rw [map_mul, mul_smul]

/-- Multiplication by the zero section over a terminal object is zero. -/
private lemma terminalSectionToEnd_zero :
    Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v, max u v} R T hT 0 = 0 := by
  ext M V x
  show (ConcreteCategory.hom (R.obj.map (hT.from (unop V)).op) 0) • x = 0
  rw [map_zero, zero_smul]

/-- Multiplication by a sum of sections over a terminal object is the sum of the two
multiplications. -/
private lemma terminalSectionToEnd_add (f g : R.obj.obj (op T)) :
    Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v, max u v} R T hT (f + g) =
      Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v, max u v} R T hT f +
        Stacks.SheafOfModules.terminalSectionToEnd.{v, u, max u v, max u v} R T hT g := by
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
private noncomputable def terminalScalarHom
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    [∀ V : (Over U)ᵒᵖ, IsMulCommutative ((R.over U).obj.obj V)] :
    (R.obj.obj (op U)) →+*
      CatCenter (SheafOfModules.{max u v} (R.over U)) where
  toFun f := Stacks.SheafOfModules.terminalSectionToEnd (R.over U)
    (Over.mk (𝟙 U)) Over.mkIdTerminal f
  map_one' := terminalSectionToEnd_one (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal
  map_mul' f g := terminalSectionToEnd_mul (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal f g
  map_zero' := terminalSectionToEnd_zero (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal
  map_add' f g := terminalSectionToEnd_add (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal f g

private theorem terminalScalarHom_evaluation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    [CommSemiring (R.obj.obj (op U))]
    [∀ W : (Over U)ᵒᵖ, IsMulCommutative ((R.over U).obj.obj W)]
    (f : R.obj.obj (op U)) (M : SheafOfModules.{max u v} (R.over U))
    (V : Over U) (x : M.val.obj (op V)) :
    ((((SheafOfModules.evaluation (R.over U) (op V)).map
      ((terminalScalarHom R U f).app M)).hom) x) =
      ((R.over U).obj.map (Over.mkIdTerminal.from V).op f) • x := by
  show ((((SheafOfModules.evaluation (R.over U) (op V)).map
      ((Stacks.SheafOfModules.terminalSectionToEnd (R.over U) (Over.mk (𝟙 U))
        Over.mkIdTerminal f).app M)).hom) x) = _
  exact Stacks.SheafOfModules.terminalSectionToEnd_apply (R.over U) (Over.mk (𝟙 U))
    Over.mkIdTerminal f M (op V) x

private theorem overEvaluation_linear
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    [∀ W : (Over U)ᵒᵖ, IsMulCommutative ((R.over U).obj.obj W)]
    (V : Over U) :
    letI : IsMulCommutative (R.obj.obj (op U)) := by
      change IsMulCommutative ((R.over U).obj.obj (op (Over.mk (𝟙 U))))
      infer_instance
    letI : CommSemiring (R.obj.obj (op U)) := inferInstance
    letI : Linear (R.obj.obj (op U)) (SheafOfModules.{max u v} (R.over U)) :=
      Linear.ofRingMorphism (terminalScalarHom R U)
    let A := R.obj.obj (op U)
    let B := (R.over U).obj.obj (op V)
    let ρ : A →+* B := ((R.over U).obj.map (Over.mkIdTerminal.from V).op).hom
    letI : IsMulCommutative B := inferInstance
    letI : CommSemiring B := inferInstance
    letI : Algebra A B := ρ.toAlgebra
    letI : Linear A (ModuleCat.{max u v} B) := ModuleCat.Algebra.instLinear
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
  let : Linear A (ModuleCat.{max u v} B) := ModuleCat.Algebra.instLinear
  let : Linear A (SheafOfModules.{max u v} (R.over U)) :=
    Linear.ofRingMorphism (terminalScalarHom R U)
  let E := SheafOfModules.evaluation (R.over U) (op V)
  show Functor.Linear A E
  exact ⟨fun {M N} g a => by
    ext x
    show ((E.map (((terminalScalarHom R U a).app M) ≫ g)).hom x) = _
    rw [Functor.map_comp]
    show (E.map g).hom ((E.map ((terminalScalarHom R U a).app M)).hom x) = _
    rw [terminalScalarHom_evaluation R U a M V x]
    show (E.map g).hom (ρ a • x) =
      ρ a • (E.map g).hom x
    exact map_smul _ _ _⟩

private theorem evaluationFamily_jointlyReflectsIsomorphisms_of_weaklyContractibleObjectsSituation
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{w, v, u, max u v} C J) :
    JointlyReflectIsomorphisms
      (fun V : {U : C // h.B U} =>
        SheafOfModules.evaluation.{max u v} R (op V.1)) := by
  let : Abelian (SheafOfModules.{max u v} R) := SheafOfModules.instAbelian R
  let : HasZeroObject (SheafOfModules.{max u v} R) := by infer_instance
  let : Balanced (SheafOfModules.{max u v} R) := by infer_instance
  refine ⟨?_⟩
  intro M N g hg
  have hmono : Mono g := by
    let S : ShortComplex (SheafOfModules.{max u v} R) :=
      ShortComplex.mk (0 : 0 ⟶ M) g (by simp)
    apply (S.exact_iff_mono (by simp [S])).1
    apply (Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
      J (h.withRing R) S).2
    intro V hV
    let E := SheafOfModules.evaluation.{max u v} R (op V)
    let : IsIso (E.map g) := hg ⟨V, hV⟩
    have hinj : Function.Injective (E.map g).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    show Function.Exact (E.map (0 : 0 ⟶ M)).hom (E.map g).hom
    intro x
    constructor
    · intro hx
      obtain rfl : x = 0 := hinj (by rw [map_zero]; simpa [E] using hx)
      exact ⟨0, by simp⟩
    · rintro ⟨y, hy⟩
      have hzero : E.map (0 : 0 ⟶ M) = 0 := Functor.map_zero E _ _
      rw [hzero] at hy
      have hx0 : x = 0 := by simpa using hy.symm
      simp [hx0]
  have hepi : Epi g := by
    let S : ShortComplex (SheafOfModules.{max u v} R) :=
      ShortComplex.mk g (0 : N ⟶ 0) (by simp)
    apply (S.exact_iff_epi (by simp [S])).1
    apply (Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
      J (h.withRing R) S).2
    intro V hV
    let E := SheafOfModules.evaluation.{max u v} R (op V)
    let : IsIso (E.map g) := hg ⟨V, hV⟩
    have hsurj : Function.Surjective (E.map g).hom :=
      (ModuleCat.epi_iff_surjective _).1 inferInstance
    show Function.Exact (E.map g).hom (E.map (0 : N ⟶ 0)).hom
    intro z
    let z' : E.obj N := z
    constructor
    · intro _
      obtain ⟨x, hx⟩ := hsurj z'
      let x' : S.X₁.val.obj (op V) := x
      exact ⟨x', by simpa [S, E, x', z'] using hx⟩
    · intro _
      have hzero : E.map (0 : N ⟶ 0) = 0 := Functor.map_zero E _ _
      rw [hzero]
      simp
  exact isIso_of_mono_of_epi g

/-- Evaluation of sheaves of modules on a member of a weakly contractible testing family
preserves finite colimits.

Over such an object exactness of a short complex of sheaves of modules is exactness of the
evaluated complex, and an additive functor between abelian categories carrying short exact
sequences to short exact sequences is exact. -/
theorem evaluation_preservesFiniteColimits_of_weaklyContractibleObjectsSituation
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{w, v, u, max u v} C J)
    (U : C) (hU : h.B U) :
    PreservesFiniteColimits (SheafOfModules.evaluation.{max u v} R (op U)) := by
  let E := SheafOfModules.evaluation.{max u v} R (op U)
  let : Abelian (SheafOfModules.{max u v} R) := SheafOfModules.instAbelian R
  let : E.Additive := evaluation_additive R U
  have hExact : ∀ (S : ShortComplex (SheafOfModules.{max u v} R)),
      S.Exact → (S.map E).Exact := by
    intro S hS
    have hsec :=
      (Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
        J (h.withRing R) S).1 hS (U := U) hU
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map E)).2
    show Function.Exact (S.f.val.app (op U)).hom (S.g.val.app (op U)).hom
    exact hsec
  have hFinite : PreservesFiniteLimits E ∧ PreservesFiniteColimits E :=
    ((Functor.exact_tfae E).out 2 4).mp hExact
  exact hFinite.2

private theorem preservesFiniteColimits_of_jointlyReflects
    {C D : Type*} [Category C] [Category D] [HasFiniteColimits C]
    [HasFiniteColimits D] {ι : Type*} {E : ι → Type*}
    [∀ index, Category (E index)]
    (F : C ⥤ D) (G : ∀ index, D ⥤ E index)
    [∀ index, PreservesFiniteColimits (G index)]
    [∀ index, PreservesFiniteColimits (F ⋙ G index)]
    (hG : JointlyReflectIsomorphisms G) : PreservesFiniteColimits F := by
  constructor
  intro J category finite
  constructor
  intro diagram
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit diagram)
  apply hG.jointlyReflectsColimit
  intro index
  exact isColimitOfPreserves (F ⋙ G index) (colimit.isColimit diagram)

/-- Countable products of sheaves of modules on a site with a weakly contractible testing family
are exact. -/
private theorem exactProducts_sheafOfModules_of_weaklyContractibleObjectsSituation
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{w, v, u, max u v} C J) :
    HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{max u v} R) :=
  Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat
    (R := R) h.B h.hasEnoughObjects fun _ hU => h.isWeaklyContractible hU

private theorem overFunctor_preservesFiniteColimits_of_slicedObjectsSituation
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v} C J) (U : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v} R U) := by
  let : HasSheafify (J.over U) AddCommGrpCat.{max u v} :=
    RingedSite.hasSheafifyAddCommGroup (J.over U)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    RingedSite.wEqualsLocallyBijectiveAddCommGroup (J.over U)
  let : Abelian (SheafOfModules.{max u v} R) := SheafOfModules.instAbelian R
  let : Abelian (SheafOfModules.{max u v} (R.over U)) := SheafOfModules.instAbelian _
  let hOver := h.over U (R.over U)
  let E := fun V : {V : Over U // hOver.B V} =>
    SheafOfModules.evaluation (R.over U) (op V.1)
  let : ∀ V, PreservesFiniteColimits (E V) := fun V =>
    evaluation_preservesFiniteColimits_of_weaklyContractibleObjectsSituation (R.over U) hOver
      V.1 V.2
  let : ∀ V, PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v} R U ⋙ E V) :=
    fun V => by
      show PreservesFiniteColimits (SheafOfModules.evaluation R (op V.1.left))
      exact evaluation_preservesFiniteColimits_of_weaklyContractibleObjectsSituation R
        h.toWeaklyContractibleObjectsSituation
        V.1.left V.2
  exact preservesFiniteColimits_of_jointlyReflects (SheafOfModules.overFunctor.{max u v} R U) E
    (evaluationFamily_jointlyReflectsIsomorphisms_of_weaklyContractibleObjectsSituation
      (R.over U) hOver)

private theorem overFunctor_preservesFiniteLimits_of_slicedObjectsSituation
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v} C J) (U : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v} R U) := by
  let : HasSheafify (J.over U) AddCommGrpCat.{max u v} :=
    RingedSite.hasSheafifyAddCommGroup (J.over U)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    RingedSite.wEqualsLocallyBijectiveAddCommGroup (J.over U)
  let : Abelian (SheafOfModules.{max u v} R) := SheafOfModules.instAbelian R
  let : Abelian (SheafOfModules.{max u v} (R.over U)) := SheafOfModules.instAbelian _
  let F := SheafOfModules.overFunctor.{max u v} R U
  let : F.Additive := SheafOfModules.overFunctor_additive R U
  let hOver := h.over U (R.over U)
  have hExact : ∀ (S : ShortComplex (SheafOfModules.{max u v} R)),
      S.Exact → (S.map F).Exact := by
    intro complex hExact
    let S' : ShortComplex (SheafOfModules.{max u v} (R.over U)) := complex.map F
    apply (Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
      (J.over U) hOver S').mpr
    intro V hV
    show Function.Exact (complex.f.val.app (op V.left))
      (complex.g.val.app (op V.left))
    exact (Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
      J (h.withRing R) complex).mp hExact hV
  have hFinite : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    ((Functor.exact_tfae F).out 2 4).mp hExact
  exact hFinite.1

private theorem oneSubSmulShift_ringHom
    {A B C : Type*} [CommSemiring A] [CommSemiring B]
    [Category C] [Preadditive C] [Linear A C] [Linear B C]
    [HasProductsOfShape ℕ C] (a : A) (b : B) (K : C)
    (hsmul : ∀ {X Y : C} (g : X ⟶ Y), a • g = b • g) :
    oneSubSmulShift K a = oneSubSmulShift K b := by
  apply Limits.Pi.hom_ext
  intro n
  rw [oneSubSmulShift_π, oneSubSmulShift_π, hsmul]

private theorem isDerivedCompleteAt_ringHom
    {A B C : Type*} [CommSemiring A] [CommSemiring B]
    [Category C] [Preadditive C] [Linear A C] [Linear B C]
    [HasProductsOfShape ℕ C] (a : A) (b : B) (K : C)
    (hsmul : ∀ {X Y : C} (g : X ⟶ Y), a • g = b • g) :
    IsDerivedCompleteAt K a ↔ IsDerivedCompleteAt K b := by
  rw [isDerivedCompleteAt_iff_isIso, isDerivedCompleteAt_iff_isIso,
    oneSubSmulShift_ringHom a b K hsmul]

private theorem derivedCategory_smul_eq
    {A B C : Type*} [Ring A] [Ring B]
    [Category C] [Abelian C] [HasDerivedCategory C] [Linear A C] [Linear B C]
    (a : A) (b : B)
    (hsmul : ∀ {Y Z : C} (g : Y ⟶ Z), a • g = b • g)
    {Y Z : DerivedCategory C} (g : Y ⟶ Z) : a • g = b • g := by
  have hcenter : Linear.toCatCenter A (DerivedCategory C) a =
      Linear.toCatCenter B (DerivedCategory C) b := by
    apply CatCenter.ext_of_localization DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    intro complex
    show a • 𝟙 (DerivedCategory.Q.obj complex) =
      b • 𝟙 (DerivedCategory.Q.obj complex)
    calc
      a • 𝟙 (DerivedCategory.Q.obj complex) =
          DerivedCategory.Q.map (a • 𝟙 complex) := by
        rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
      _ = DerivedCategory.Q.map (b • 𝟙 complex) := by
        apply congrArg DerivedCategory.Q.map
        apply HomologicalComplex.hom_ext
        intro degree
        exact hsmul _
      _ = b • 𝟙 (DerivedCategory.Q.obj complex) := by
        rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  simpa only [Linear.toCatCenter_apply_app, Linear.smul_comp, Category.id_comp] using
    congrArg (fun s : CatCenter (DerivedCategory C) => s.app Y ≫ g) hcenter

/-- Derived completeness of an object of the derived category at two scalars acting by the same
endomorphisms of the abelian category is equivalent. -/
private theorem isDerivedCompleteAt_derivedCategory_iff
    {A B C : Type*} [Ring A] [Ring B] [IsMulCommutative A] [IsMulCommutative B]
    [Category C] [Abelian C] [HasDerivedCategory C] [Linear A C] [Linear B C]
    [HasProductsOfShape ℕ (DerivedCategory C)] (a : A) (b : B)
    (hsmul : ∀ {Y Z : C} (g : Y ⟶ Z), a • g = b • g) (K : DerivedCategory C) :
    IsDerivedCompleteAt K a ↔ IsDerivedCompleteAt K b :=
  isDerivedCompleteAt_ringHom a b K fun g => derivedCategory_smul_eq a b hsmul g

/-- Evaluation on a member of a weakly contractible testing family carries an exact short
complex of sheaves of modules to an exact short complex of modules.

Exactness of a short complex of sheaves of modules is exactness of the underlying complex of
abelian sheaves, which weak contractibility detects on sections. -/
theorem evaluation_map_exact_of_weaklyContractibleObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (B : Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{w, v, u, max u v}
      X.C X.J)
    (U : X.C) (hU : B.B U)
    (S : ShortComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hS : S.Exact) :
    (S.map
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U))).Exact := by
  rw [ShortComplex.exact_iff_exact_map_forget₂, ShortComplex.ab_exact_iff_function_exact]
  convert (Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
    X.J (B.withRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) S).mp hS hU using 1 <;> rfl

/-- Derived completeness of a complex of sheaves of modules can be tested on
derived sections over a covering family of weakly contractible objects. -/
public theorem isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation
    (X : AlgebraicGeometry.RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (h : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory
      (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v, max u v} X I K ↔
      ∀ (U : X.C), h.B U →
        let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
        letI : IsMulCommutative R := by
          change IsMulCommutative (X.O.obj.obj (op U))
          infer_instance
        let F := SheafOfModules.evaluation.{max u v}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
        ∃ hAdd : F.Additive,
        ∃ hLim : PreservesFiniteLimits F,
        ∃ hColim : PreservesFiniteColimits F,
        ∃ hProd : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)),
          letI : F.Additive := hAdd
          letI : PreservesFiniteLimits F := hLim
          letI : PreservesFiniteColimits F := hColim
          letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)) := hProd
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
    let hAdd : E.Additive := evaluation_additive _ U
    let hLim : PreservesFiniteLimits E :=
      SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
    let hColim : PreservesFiniteColimits E :=
      evaluation_preservesFiniteColimits_of_weaklyContractibleObjectsSituation
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        h.toWeaklyContractibleObjectsSituation U hU
    let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} R) :=
      moduleCat_hasExactLimitsOfShape_discrete.{max u v} R ℕ
    let hProd : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    refine ⟨hAdd, hLim, hColim, hProd, ?_⟩
    intro f hf
    obtain ⟨hSliceAdd, hSliceLim, hSliceColim, hSliceProd, hSliceComplete⟩ :=
      hCompleteAll U f hf
    let ROver := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U
    let A := SheafOfModules.{max u v} ROver
    let F := SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let : HasSheafify (X.J.over U) AddCommGrpCat.{max u v} :=
      RingedSite.hasSheafifyAddCommGroup (X.J.over U)
    let : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
      RingedSite.wEqualsLocallyBijectiveAddCommGroup (X.J.over U)
    let hOver := h.over U ROver
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
      terminalScalarHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let : Linear R A := Linear.ofRingMorphism
      (terminalScalarHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
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
    let hCompleteR : IsDerivedCompleteAt K' f :=
      (isDerivedCompleteAt_derivedCategory_iff f (φ f) (fun _ => rfl) K').mpr
        hSliceCompleteCenter
    let : HasExactLimitsOfShape (Discrete ℕ) A :=
      exactProducts_sheafOfModules_of_weaklyContractibleObjectsSituation ROver hOver
    let hJoint : JointlyReflectIsomorphisms
        (fun V : {V : Over U // hOver.B V} =>
          SheafOfModules.evaluation.{max u v} ROver (op V.1)) :=
      evaluationFamily_jointlyReflectsIsomorphisms_of_weaklyContractibleObjectsSituation ROver hOver
    let Eval := fun V : {V : Over U // hOver.B V} =>
      SheafOfModules.evaluation.{max u v} ROver (op V.1)
    let : ∀ V : {V : Over U // hOver.B V},
        Algebra R (ROver.obj.obj (op V.1)) := fun V => by
      let ρ : R →+* ROver.obj.obj (op V.1) :=
        (ROver.obj.map (Over.mkIdTerminal.from V.1).op).hom
      exact ρ.toAlgebra
    let evaluationLinear : ∀ V : {V : Over U // hOver.B V}, Linear R
        (ModuleCat.{max u v} (ROver.obj.obj (op V.1))) := fun V => by
      let B := ROver.obj.obj (op V.1)
      let : CommSemiring B := inferInstance
      let ρ : R →+* B :=
        (ROver.obj.map (Over.mkIdTerminal.from V.1).op).hom
      let : Algebra R B := ρ.toAlgebra
      exact @ModuleCat.Algebra.instLinear R (inferInstance : CommSemiring R) B
        (inferInstance : Ring B) (ρ.toAlgebra)
    let : ∀ V : {V : Over U // hOver.B V}, (Eval V).Additive :=
      fun V => evaluation_additive ROver V.1
    let : ∀ V : {V : Over U // hOver.B V}, PreservesFiniteLimits (Eval V) :=
      fun V => inferInstance
    let : ∀ V : {V : Over U // hOver.B V}, PreservesFiniteColimits (Eval V) := fun V =>
      evaluation_preservesFiniteColimits_of_weaklyContractibleObjectsSituation ROver hOver V.1 V.2
    let : ∀ V : {V : Over U // hOver.B V}, Functor.Linear R (Eval V) := fun V => by
      show Functor.Linear R
        (SheafOfModules.evaluation
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) (op V.1))
      exact overEvaluation_linear (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U V.1
    let : ∀ V : {V : Over U // hOver.B V},
        PreservesLimitsOfShape (Discrete ℕ) (Eval V) := fun V => inferInstance
    let : ∀ V : {V : Over U // hOver.B V}, HasExactLimitsOfShape (Discrete ℕ)
        (ModuleCat.{max u v} (ROver.obj.obj (op V.1))) := fun V =>
      moduleCat_hasExactLimitsOfShape_discrete.{max u v} _ ℕ
    let : ∀ V : {V : Over U // hOver.B V}, HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v} (ROver.obj.obj (op V.1)))) := fun V =>
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
    let terminalLinear : Linear R (ModuleCat.{max u v} R) :=
      evaluationLinear ⟨terminal, hterminal⟩
    let : PreservesFiniteColimits
        (SheafOfModules.evaluation ROver (op terminal)) :=
      evaluation_preservesFiniteColimits_of_weaklyContractibleObjectsSituation ROver hOver terminal
        hterminal
    let : PreservesFiniteLimits E := hLim
    let : PreservesFiniteColimits E := hColim
    let : Linear R (ModuleCat.{max u v} R) := ModuleCat.instLinear
    let : PreservesFiniteColimits
        (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op terminal.left)) :=
      hColim
    let : Linear R (ModuleCat.{max u v} (ROver.obj.obj (op terminal))) :=
      ModuleCat.instLinear
    let : HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v} (ROver.obj.obj (op terminal)))) := hProd
    let : PreservesFiniteLimits
        (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op terminal.left)) :=
      hLim
    let e := overEvaluationMapDerivedCategoryIsoOfSliceSheafify
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U terminal
    have hglobal : IsDerivedCompleteAt (E.mapDerivedCategory.obj K) f := by
      have hAt := hEvalComplete ⟨terminal, hterminal⟩
      have hIso := e.app K
      have hAtNative : IsDerivedCompleteAt ((EV ⟨terminal, hterminal⟩).obj K') f := by
        refine (@isDerivedCompleteAt_derivedCategory_iff R R (ModuleCat.{max u v} R) _ _ _ _ _ _ _
          terminalLinear ModuleCat.instLinear _ f f ?_ _).mp hAt
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
    let A := SheafOfModules.{max u v} ROver
    let F := SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let : HasSheafify (X.J.over U) AddCommGrpCat.{max u v} :=
      RingedSite.hasSheafifyAddCommGroup (X.J.over U)
    let : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
      RingedSite.wEqualsLocallyBijectiveAddCommGroup (X.J.over U)
    let hOver := h.over U ROver
    let : F.Additive := SheafOfModules.overFunctor_additive _ U
    let : PreservesFiniteLimits F :=
      overFunctor_preservesFiniteLimits_of_slicedObjectsSituation
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h U
    let : PreservesFiniteColimits F :=
      overFunctor_preservesFiniteColimits_of_slicedObjectsSituation
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h U
    let : HasExactLimitsOfShape (Discrete ℕ) A :=
      exactProducts_sheafOfModules_of_weaklyContractibleObjectsSituation ROver hOver
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
    let φ := terminalScalarHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
    let : Linear R A := Linear.ofRingMorphism φ
    let K' := F.mapDerivedCategory.obj K
    have hφf : φ f =
        Stacks.SheafOfModules.terminalSectionToEnd ROver (Over.mk (𝟙 U)) Over.mkIdTerminal f := rfl
    rw [← hφf]
    apply (isDerivedCompleteAt_derivedCategory_iff f (φ f) (fun _ => rfl) K').mp
    let Eval := fun V : {V : Over U // hOver.B V} =>
      SheafOfModules.evaluation.{max u v} ROver (op V.1)
    let : ∀ V : {V : Over U // hOver.B V},
        Algebra R (ROver.obj.obj (op V.1)) := fun V =>
      (ROver.obj.map (Over.mkIdTerminal.from V.1).op).hom.toAlgebra
    let : ∀ V : {V : Over U // hOver.B V}, Linear R
        (ModuleCat.{max u v} (ROver.obj.obj (op V.1))) := fun V =>
      ModuleCat.Algebra.instLinear
    let : ∀ V : {V : Over U // hOver.B V}, (Eval V).Additive :=
      fun V => evaluation_additive ROver V.1
    let : ∀ V : {V : Over U // hOver.B V}, PreservesFiniteLimits (Eval V) :=
      fun V => inferInstance
    let : ∀ V : {V : Over U // hOver.B V}, PreservesFiniteColimits (Eval V) := fun V =>
      evaluation_preservesFiniteColimits_of_weaklyContractibleObjectsSituation ROver hOver V.1 V.2
    let : ∀ V : {V : Over U // hOver.B V}, Functor.Linear R (Eval V) := fun V =>
      overEvaluation_linear (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U V.1
    let : ∀ V : {V : Over U // hOver.B V}, HasExactLimitsOfShape (Discrete ℕ)
        (ModuleCat.{max u v} (ROver.obj.obj (op V.1))) := fun V =>
      moduleCat_hasExactLimitsOfShape_discrete.{max u v} _ ℕ
    let : ∀ V : {V : Over U // hOver.B V}, HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v} (ROver.obj.obj (op V.1)))) := fun V =>
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let EV := fun V => (Eval V).mapDerivedCategory
    let : ∀ V : {V : Over U // hOver.B V},
        PreservesLimitsOfShape (Discrete ℕ) (EV V) := fun V =>
      Functor.preservesProducts_mapDerivedCategory ℕ (Eval V)
    have hJointD : JointlyReflectIsomorphisms EV :=
      jointlyReflectsIsomorphisms_mapDerivedCategory Eval
        (evaluationFamily_jointlyReflectsIsomorphisms_of_weaklyContractibleObjectsSituation
          ROver hOver)
    apply (isDerivedCompleteAt_iff_of_jointlyReflects EV hJointD).mpr
    intro V
    obtain ⟨hAdd, hLim, hColim, hProd, hComplete⟩ := hSections V.1.left V.2
    let E := SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op V.1.left)
    let : E.Additive := hAdd
    let : PreservesFiniteLimits E := hLim
    let : PreservesFiniteColimits E := hColim
    let : HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v} (ROver.obj.obj (op V.1)))) := hProd
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
        (ModuleCat.{max u v} (ROver.obj.obj (op V.1))) := ModuleCat.instLinear
    let e := overEvaluationMapDerivedCategoryIsoOfSliceSheafify
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U V.1
    have hAtSlice : IsDerivedCompleteAt ((EV V).obj K') b :=
      (DerivedCompleteRecurrence.isDerivedCompleteAt_iff_of_iso (e.app K) b).mpr hAt
    exact (isDerivedCompleteAt_derivedCategory_iff f b (fun _ => rfl) _).mpr hAtSlice

/-! ### The statements at a weakly contractible testing family

On a `Type v`-small site a weakly contractible testing family supplies the bundles the
statements above consume, by `Stacks.WeaklyContractible.SlicedObjectsSituation.of`; these are
the resulting statements, in the form that only mentions the family. -/

/-- Evaluating a sheaf of modules on the slice site at an object `V ⟶ U`, after restricting it
to the slice, is evaluating it at `V`; this is the induced isomorphism of the functors on
derived categories. -/
private noncomputable def overEvaluationMapDerivedCategoryIso
    {C : Type u} [Category.{v} C] [Small.{v} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) [HasSheafify J AddCommGrpCat.{max u v}]
    (U : C) (V : Over U)
    [(SheafOfModules.overFunctor.{max u v} R U).Additive]
    [(SheafOfModules.evaluation.{max u v} (R.over U) (op V)).Additive]
    [(SheafOfModules.evaluation.{max u v} R (op V.left)).Additive]
    [PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v} R U)]
    [PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v} R U)]
    [PreservesFiniteLimits (SheafOfModules.evaluation.{max u v} (R.over U) (op V))]
    [PreservesFiniteColimits (SheafOfModules.evaluation.{max u v} (R.over U) (op V))]
    [hEvalLim : PreservesFiniteLimits (SheafOfModules.evaluation.{max u v} R (op V.left))]
    [hEvalColim : PreservesFiniteColimits (SheafOfModules.evaluation.{max u v} R (op V.left))] :
    (SheafOfModules.overFunctor.{max u v} R U).mapDerivedCategory ⋙
        (SheafOfModules.evaluation.{max u v} (R.over U) (op V)).mapDerivedCategory ≅
      (SheafOfModules.evaluation.{max u v} R (op V.left)).mapDerivedCategory :=
  overEvaluationMapDerivedCategoryIsoOfSliceSheafify R U V

private theorem evaluationFamily_jointlyReflectsIsomorphisms
    {C : Type u} [Category.{v} C] [Small.{v} C]
    {J : GrothendieckTopology C} [HasSheafify J (Type v)]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.WeaklyContractibleTestingFamily C J) :
    JointlyReflectIsomorphisms
      (fun V : {U : C // h.B U} =>
        SheafOfModules.evaluation.{max u v} R (op V.1)) :=
  evaluationFamily_jointlyReflectsIsomorphisms_of_weaklyContractibleObjectsSituation R
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of h R).toWeaklyContractibleObjectsSituation

/-- Evaluation of sheaves of modules on a member of a weakly contractible testing family
preserves finite colimits.

Over such an object exactness of a short complex of sheaves of modules is exactness of the
evaluated complex, and an additive functor between abelian categories carrying short exact
sequences to short exact sequences is exact. -/
theorem evaluation_preservesFiniteColimits
    {C : Type u} [Category.{v} C] [Small.{v} C]
    {J : GrothendieckTopology C} [HasSheafify J (Type v)]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.WeaklyContractibleTestingFamily C J)
    (U : C) (hU : h.B U) :
    PreservesFiniteColimits (SheafOfModules.evaluation.{max u v} R (op U)) :=
  evaluation_preservesFiniteColimits_of_weaklyContractibleObjectsSituation R
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of h R).toWeaklyContractibleObjectsSituation
    U hU

/-- Countable products of sheaves of modules on a site with a weakly contractible testing family
are exact. -/
private theorem exactProducts_sheafOfModules
    {C : Type u} [Category.{v} C] [Small.{v} C]
    {J : GrothendieckTopology C} [HasSheafify J (Type v)]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.WeaklyContractibleTestingFamily C J) :
    HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{max u v} R) :=
  exactProducts_sheafOfModules_of_weaklyContractibleObjectsSituation R
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of h R).toWeaklyContractibleObjectsSituation

private theorem overFunctor_preservesFiniteColimits
    {C : Type u} [Category.{v} C] [Small.{v} C]
    {J : GrothendieckTopology C} [HasSheafify J (Type v)]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.WeaklyContractibleTestingFamily C J) (U : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v} R U) :=
  overFunctor_preservesFiniteColimits_of_slicedObjectsSituation R
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of h R) U

private theorem overFunctor_preservesFiniteLimits
    {C : Type u} [Category.{v} C] [Small.{v} C]
    {J : GrothendieckTopology C} [HasSheafify J (Type v)]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (h : Stacks.WeaklyContractible.WeaklyContractibleTestingFamily C J) (U : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v} R U) :=
  overFunctor_preservesFiniteLimits_of_slicedObjectsSituation R
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of h R) U

/-- Evaluation on a member of a weakly contractible testing family carries an exact short
complex of sheaves of modules to an exact short complex of modules.

Exactness of a short complex of sheaves of modules is exactness of the underlying complex of
abelian sheaves, which weak contractibility detects on sections. -/
theorem evaluation_map_exact
    (X : RingedSite.{u, v, max u v}) [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (B : Stacks.WeaklyContractible.WeaklyContractibleTestingFamily X.C X.J)
    (U : X.C) (hU : B.B U)
    (S : ShortComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hS : S.Exact) :
    (S.map
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U))).Exact :=
  evaluation_map_exact_of_weaklyContractibleObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of B
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).toWeaklyContractibleObjectsSituation
    U hU S hS

/-- Derived completeness of a complex of sheaves of modules can be tested on
derived sections over a covering family of weakly contractible objects. -/
public theorem isDerivedComplete_iff_derivedSections
    (X : AlgebraicGeometry.RingedSite.{u, v, max u v})
    [Small.{v} X.C] [HasSheafify X.J (Type v)]
    (h : Stacks.WeaklyContractible.WeaklyContractibleTestingFamily X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory
      (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v, max u v} X I K ↔
      ∀ (U : X.C), h.B U →
        let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
        letI : IsMulCommutative R := by
          change IsMulCommutative (X.O.obj.obj (op U))
          infer_instance
        let F := SheafOfModules.evaluation.{max u v}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
        ∃ hAdd : F.Additive,
        ∃ hLim : PreservesFiniteLimits F,
        ∃ hColim : PreservesFiniteColimits F,
        ∃ hProd : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)),
          letI : F.Additive := hAdd
          letI : PreservesFiniteLimits F := hLim
          letI : PreservesFiniteColimits F := hColim
          letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)) := hProd
          ∀ f : R, f ∈ I.toSubmodule.obj (op U) →
            IsDerivedCompleteAt (F.mapDerivedCategory.obj K) f :=
  isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of h
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I K

end AlgebraicGeometry.RingedSite

end
