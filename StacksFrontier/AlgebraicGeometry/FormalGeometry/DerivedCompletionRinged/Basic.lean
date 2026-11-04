module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Center.Preadditive
public import Mathlib.CategoryTheory.Center.Linear
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Homology.DerivedComplete
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived completeness on a ringed site

A derived sheaf of modules is complete along a sheaf of ideals when, on every slice site, the
derived inverse limit of multiplication by each local ideal section vanishes.

## Main definitions

* `AlgebraicGeometry.RingedSite.IsDerivedComplete`: derived completeness along a sheaf of
  ideals.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_iff`: the local criterion.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_iff_of_iso`: invariance under isomorphism in
  the derived category.

## Implementation notes

The site, coefficient ring, and module universes are independent. An ideal sheaf is a submodule
of the structure sheaf as a module over itself. The condition `T(K|_U, f) = 0` is expressed using
the equivalent invertibility of the Milnor difference map `1 - f·shift` on the countable product,
that is by `IsDerivedCompleteAt`. Multiplication by `f` is the natural endomorphism of module
sheaves given by a section over a terminal object of the slice site. Restriction uses the functor
induced on derived categories by the exact restriction functor, so it is independent of a
representative. The exactness data and the existence of the countable product are included in the
predicate's specification. The characterizing lemma and invariance under isomorphism are the basic
API for full subcategories of complete derived objects.

This predicate is the ringed-site analogue of the predicate `IsDerivedComplete` for an ideal of a
commutative ring acting on a linear category; the two are different objects and are kept apart by
the namespace.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u v r w

namespace AlgebraicGeometry.RingedSite

/-- Sheafification in any module universe containing the site universes. -/
instance moduleHasSheafify
    {C : Type u} [Category.{v} C] [Small.{w} C] [LocallySmall.{w} C]
    (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall J

/-- Sheafification detects local bijections in the enlarged module universe. -/
instance moduleWEqualsLocallyBijective
    {C : Type u} [Category.{v} C] [Small.{w} C] [LocallySmall.{w} C]
    (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{w} := by
  let C' := SmallModel.{w} C
  let e : C ≌ C' := equivSmallModel.{w} C
  let J' : GrothendieckTopology C' := e.inverse.inducedTopology J
  let : SmallCategory C' := inferInstance
  have : J'.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.transport J J' e.inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

/-- Sheafification of abelian groups, for a site whose size is recorded by `UnivLE`. -/
theorem hasSheafifyAddCommGroup
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{u, w}] [UnivLE.{v, w}] :
    HasSheafify J AddCommGrpCat.{w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall J

/-- Sheafification detects local bijections, for a site whose size is recorded by `UnivLE`. -/
theorem wEqualsLocallyBijectiveAddCommGroup
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{u, w}] [UnivLE.{v, w}] :
    J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  moduleWEqualsLocallyBijective J

/-- Derived completeness at a single element is invariant under isomorphism. -/
theorem isDerivedCompleteAt_iff_of_iso
    {A : Type*} [CommSemiring A] {C : Type*} [Category C] [Preadditive C]
    [Linear A C] [HasProductsOfShape ℕ C] {K L : C} (e : K ≅ L) (f : A) :
    IsDerivedCompleteAt K f ↔ IsDerivedCompleteAt L f := by
  have hPi : IsIso (Limits.Pi.map (fun _ : ℕ ↦ e.hom)) := by
    refine ⟨⟨Limits.Pi.map (fun _ : ℕ ↦ e.inv), ?_, ?_⟩⟩
    all_goals
      apply Pi.hom_ext
      intro n
      simp [Category.assoc]
  rw [isDerivedCompleteAt_iff_isIso, isDerivedCompleteAt_iff_isIso,
    ← isIso_comp_right_iff _ (Limits.Pi.map (fun _ : ℕ ↦ e.hom)),
    oneSubSmulShift_naturality, isIso_comp_left_iff]

/-- Derived completeness of a complex of sheaves of modules along an ideal sheaf. -/
@[stacks 0999]
def IsDerivedComplete (X : RingedSite.{u, v, r})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (K : DerivedCategory
      (SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) : Prop :=
  ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (Opposite.op U)),
    f ∈ I.toSubmodule.obj (Opposite.op U) →
      let R := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U
      let A := SheafOfModules.{max u v w} R
      letI : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
      letI : ∀ V : (Over U)ᵒᵖ, IsMulCommutative (R.obj.obj V) := fun V ↦ by
        change IsMulCommutative (X.O.obj.obj (Opposite.op V.unop.left))
        infer_instance
      let F :=
        SheafOfModules.overFunctor.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
      ∃ hAdd : F.Additive,
      ∃ hLim : PreservesFiniteLimits F,
      ∃ hColim : PreservesFiniteColimits F,
        letI : F.Additive := hAdd
        letI : PreservesFiniteLimits F := hLim
        letI : PreservesFiniteColimits F := hColim
      ∃ h : HasProductsOfShape ℕ (DerivedCategory A),
        letI : HasProductsOfShape ℕ (DerivedCategory A) := h
        IsDerivedCompleteAt
          (F.mapDerivedCategory.obj K)
          (Stacks.SheafOfModules.terminalSectionToEnd R (Over.mk (𝟙 U))
            Over.mkIdTerminal f)

/-- The local criterion for derived completeness, in terms of the exact
derived restriction to every slice site. -/
theorem isDerivedComplete_iff (X : RingedSite.{u, v, r})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (K : DerivedCategory
      (SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsDerivedComplete.{u, v, r, w} X I K ↔
      ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (Opposite.op U)),
        f ∈ I.toSubmodule.obj (Opposite.op U) →
          let R := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U
          let A := SheafOfModules.{max u v w} R
          letI : Linear (CatCenter A) A :=
            Linear.ofRingMorphism (RingHom.id (CatCenter A))
          letI : ∀ V : (Over U)ᵒᵖ, IsMulCommutative (R.obj.obj V) := fun V ↦ by
            change IsMulCommutative (X.O.obj.obj (Opposite.op V.unop.left))
            infer_instance
          let F :=
            SheafOfModules.overFunctor.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
          ∃ hAdd : F.Additive,
          ∃ hLim : PreservesFiniteLimits F,
          ∃ hColim : PreservesFiniteColimits F,
            letI : F.Additive := hAdd
            letI : PreservesFiniteLimits F := hLim
            letI : PreservesFiniteColimits F := hColim
          ∃ h : HasProductsOfShape ℕ (DerivedCategory A),
            letI : HasProductsOfShape ℕ (DerivedCategory A) := h
            IsDerivedCompleteAt (F.mapDerivedCategory.obj K)
              (Stacks.SheafOfModules.terminalSectionToEnd R (Over.mk (𝟙 U))
                Over.mkIdTerminal f) :=
  Iff.rfl

/-- Derived completeness is invariant under isomorphism in the derived
category of sheaves of modules. -/
theorem isDerivedComplete_iff_of_iso (X : RingedSite.{u, v, r})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {K L : DerivedCategory
      (SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (e : K ≅ L) :
    IsDerivedComplete.{u, v, r, w} X I K ↔ IsDerivedComplete.{u, v, r, w} X I L := by
  unfold IsDerivedComplete
  constructor <;> intro h U f hf
  all_goals
    let R := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U
    let A := SheafOfModules.{max u v w} R
    let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
    let : ∀ V : (Over U)ᵒᵖ, IsMulCommutative (R.obj.obj V) := fun V ↦ by
      show IsMulCommutative (X.O.obj.obj (Opposite.op V.unop.left))
      infer_instance
    let F := SheafOfModules.overFunctor.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
    obtain ⟨hAdd, hLim, hColim, hProducts, hComplete⟩ := h U f hf
    let : F.Additive := hAdd
    let : PreservesFiniteLimits F := hLim
    let : PreservesFiniteColimits F := hColim
    let : HasProductsOfShape ℕ (DerivedCategory A) := hProducts
    refine ⟨hAdd, hLim, hColim, hProducts, ?_⟩
    let q := isDerivedCompleteAt_iff_of_iso (F.mapDerivedCategory.mapIso e)
      (Stacks.SheafOfModules.terminalSectionToEnd R (Over.mk (𝟙 U)) Over.mkIdTerminal f)
    first | exact q.mp hComplete | exact q.mpr hComplete

end AlgebraicGeometry.RingedSite
