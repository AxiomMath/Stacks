module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.ForgetfulInclusionCohomologyPresheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology on a scheme over a field is invariant under an isomorphism of schemes

Let `f : X ⟶ Y` be an isomorphism of schemes and `g : Y ⟶ Spec k`. For a module `M` on `X`, the
`k`-vector space `Hⁿ(X, M)` and the `k`-vector space `Hⁿ(Y, f_* M)` have the same dimension.

`AlgebraicGeometry.cohomologyOverField` is the `n`-th right derived functor of evaluation on the
whole space, with scalars restricted along the structure morphism. Three steps carry it across
`f`:

* evaluation on the whole space of a direct image **is** evaluation on the whole space with
  scalars restricted along `f` on global sections: `f ⁻¹ᵁ ⊤ = ⊤` definitionally, so the two
  functors `X.Modules ⥤ ModuleCat Γ(Y, ⊤)` are equal, not merely isomorphic;
* restriction of scalars is exact, so it may be pulled out of a right derived functor
  (`Stacks.Cohomology.DerivedForget.rightDerivedCompIso`);
* direct image along an isomorphism is an equivalence, hence exact and injective-preserving, so
  the right derived functor of a composite beginning with it collapses
  (`Stacks.RightDerivedComp.objIso`).

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.isEquivalence_pushforward_of_isIso`: direct image along an
  isomorphism of schemes is an equivalence of the categories of sheaves of modules, as an
  instance. The equivalence itself is `AlgebraicGeometry.Scheme.Modules.pushforwardEquivOfIso`.
* `AlgebraicGeometry.cohomologyOverFieldPushforwardIso`: the isomorphism
  `Hⁿ(X, M) ≅ Hⁿ(Y, f_* M)` of `k`-vector spaces attached to an isomorphism `f : X ⟶ Y`.

## Main results

* `Stacks.RightDerivedTransport.isZero_rightDerived_succ_of_preservesHomology`: a functor
  preserving homology has no higher right derived functors.
* `Stacks.RightDerivedTransport.rightDerivedRestrictScalarsObjIso` and
  `rightDerivedPrecomposeEquivObjIso`: the two transport steps, over abstract categories.
* `AlgebraicGeometry.finrank_cohomologyOverField_pushforward`: `Hⁿ(X, M)` and `Hⁿ(Y, f_* M)` have
  the same dimension over `k`.

## Implementation notes

The two transport steps are stated over abstract abelian categories and applied, rather than
being proved in place for the evaluation functors: the `CategoryTheory.Functor.Additive` instance
for `ModuleCat.restrictScalars` along a morphism of `CommRingCat` is not found by instance search
when the `CategoryTheory.Preadditive` structure reaches the goal through `CategoryTheory.Abelian`,
which is how it reaches the goal inside `Stacks.Cohomology.DerivedForget.rightDerivedCompIso`.
Stated over a bare ring homomorphism between types carrying `Ring` instances, the Mathlib instance
applies, and the abstract lemma can then be instantiated at the concrete functors with the two
evaluation instances supplied positionally.

`Stacks.RightDerivedComp.objIso` asks for acyclicity of the object rather than exactness of the
functor, so the vanishing of the higher right derived functors of an equivalence is proved here;
its route is `CategoryTheory.Functor.mapHomologicalComplexHomologyIso`, which moves the homology
of the image of an injective resolution past the functor, where it is the image of zero.

`AlgebraicGeometry.Scheme.Modules.isEquivalence_pushforward_of_isIso` reads the equivalence
`AlgebraicGeometry.Scheme.Modules.pushforwardEquivOfIso` as a property of the direct image
along an isomorphism.

## References

* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u w

namespace Stacks.RightDerivedTransport

/-- Restriction of scalars along a ring homomorphism preserves finite limits. -/
local instance restrictScalarsPreservesFiniteLimits {R S : Type u} [Ring R] [Ring S]
    (φ : R →+* S) : PreservesFiniteLimits (ModuleCat.restrictScalars.{v} φ) := by
  constructor; intro J _ _; constructor; intro F; infer_instance

/-- Restriction of scalars along a ring homomorphism preserves finite colimits. -/
local instance restrictScalarsPreservesFiniteColimits {R S : Type u} [Ring R] [Ring S]
    (φ : R →+* S) : PreservesFiniteColimits (ModuleCat.restrictScalars.{v} φ) := by
  constructor; intro J _ _; constructor; intro F; infer_instance

/-- **A functor preserving homology has no higher right derived functors.** -/
theorem isZero_rightDerived_succ_of_preservesHomology {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D]
    (G : C ⥤ D) [G.Additive] [G.PreservesHomology] (n : ℕ) (A : C) :
    IsZero ((G.rightDerived (n + 1)).obj A) := by
  have hex : (injectiveResolution A).cocomplex.ExactAt (n + 1) := by
    rw [← quasiIsoAt_iff_exactAt (injectiveResolution A).ι (n + 1)
      (CochainComplex.exactAt_succ_single_obj _ _)]
    infer_instance
  refine IsZero.of_iso ?_ ((injectiveResolution A).isoRightDerivedObj G (n + 1))
  refine IsZero.of_iso ?_
    ((G.mapHomologicalComplexHomologyIso (ComplexShape.up ℕ) (n + 1)).app
      (injectiveResolution A).cocomplex)
  exact G.map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hex)

/-- Restriction of scalars may be pulled out of a right derived functor, one object at a time. -/
def rightDerivedRestrictScalarsObjIso {A : Type w} [Category* A] [Abelian A]
    [HasInjectiveResolutions A] {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (F : A ⥤ ModuleCat.{v} S) [F.Additive] (M : A) (n : ℕ) :
    (ModuleCat.restrictScalars φ).obj ((F.rightDerived n).obj M) ≅
      ((F ⋙ ModuleCat.restrictScalars φ).rightDerived n).obj M :=
  (Stacks.Cohomology.DerivedForget.rightDerivedCompIso F (ModuleCat.restrictScalars φ) n).app M

/-- The right derived functor of a composite whose first factor is an equivalence collapses onto
the right derived functor of the second factor. -/
def rightDerivedPrecomposeEquivObjIso {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Abelian C] [Abelian D] [Abelian E]
    [HasInjectiveResolutions C] [HasInjectiveResolutions D]
    (G : C ⥤ D) [G.Additive] [G.IsEquivalence] (T : D ⥤ E) [T.Additive] (A : C) (n : ℕ) :
    ((G ⋙ T).rightDerived n).obj A ≅ (T.rightDerived n).obj (G.obj A) :=
  Stacks.RightDerivedComp.objIso G (injectiveResolution A)
    (fun m hm => by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
      exact isZero_rightDerived_succ_of_preservesHomology _ _ _) T n

end Stacks.RightDerivedTransport

namespace AlgebraicGeometry

/-- The map on global sections of a morphism of schemes is its `Scheme.Hom.appLE` from the top
open to the top open. -/
theorem Scheme.Hom.appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ h = f.app ⊤ :=
  (Scheme.Hom.app_eq_appLE (U := (⊤ : Y.Opens)) f).symm

/-- On global sections a composite of morphisms of schemes acts by the two maps in turn. -/
theorem Scheme.Hom.appLE_comp_top {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : (⊤ : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ ⊤) (h' : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤) :
    (f ≫ g).appLE ⊤ ⊤ h = g.appLE ⊤ ⊤ h' ≫ f.app ⊤ := by
  rw [Scheme.Hom.appLE_top_top, Scheme.Hom.appLE_top_top, Scheme.Hom.comp_app]
  rfl

namespace Scheme.Modules

/-- Direct image of sheaves of modules along an isomorphism of schemes is an equivalence of
categories. -/
instance isEquivalence_pushforward_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (Scheme.Modules.pushforward f).IsEquivalence := by
  have h : (pushforwardEquivOfIso (asIso f)).functor = Scheme.Modules.pushforward f := rfl
  exact h ▸ (pushforwardEquivOfIso (asIso f)).isEquivalence_functor

end Scheme.Modules

/-- Evaluation on the whole space of a direct image, with its `Γ(Y, ⊤)`-module structure, is
evaluation on the whole space of the source followed by restriction of scalars along the map on
global sections. The two functors are equal. -/
theorem pushforward_comp_evaluation_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pushforward f ⋙
        SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens)) =
      SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙
        ModuleCat.restrictScalars (f.app (⊤ : Y.Opens)).hom :=
  rfl

/-- **Cohomology on the whole space transported along an isomorphism of schemes**, before the
scalars are restricted to the base field: `Hⁿ(X, M)`, regarded over `Γ(Y, ⊤)`, is `Hⁿ(Y, f_* M)`.
-/
def rightDerivedEvaluationTopPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (M : X.Modules) (n : ℕ) :
    (ModuleCat.restrictScalars (f.app (⊤ : Y.Opens)).hom).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj M) ≅
      ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).rightDerived n).obj
        ((Scheme.Modules.pushforward f).obj M) :=
  @Stacks.RightDerivedTransport.rightDerivedRestrictScalarsObjIso
      _ _ _ _ _ _ _ _ (f.app (⊤ : Y.Opens)).hom
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))) ⟨by intros; rfl⟩ M n ≪≫
    @Stacks.RightDerivedTransport.rightDerivedPrecomposeEquivObjIso _ _ _ _ _ _ _ _ _ _ _
      (Scheme.Modules.pushforward f) _ _
      (SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))) ⟨by intros; rfl⟩ M n

/-- **Cohomology is invariant under an isomorphism of schemes over the base**: the isomorphism
`Hⁿ(X, M) ≅ Hⁿ(Y, f_* M)` of `k`-vector spaces attached to an isomorphism `f : X ⟶ Y` and a
structure morphism `g : Y ⟶ Spec k`. -/
def cohomologyOverFieldPushforwardIso (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (g : Y ⟶ Spec (.of k)) (M : X.Modules) (n : ℕ) :
    cohomologyOverField k (f ≫ g) M n ≅
      cohomologyOverField k g ((Scheme.Modules.pushforward f).obj M) n :=
  ModuleCat.restrictScalarsComp'App
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom
      (f.app (⊤ : Y.Opens)).hom
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ g).appLE ⊤ ⊤ (by simp)).hom
      (by
        rw [← CommRingCat.hom_comp]
        refine congrArg CommRingCat.Hom.hom ?_
        rw [Category.assoc, Scheme.Hom.appLE_comp_top f g (by simp) (by simp)]
        rfl) _ ≪≫
    (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom).mapIso
      (rightDerivedEvaluationTopPushforwardIso f M n)

/-- **Cohomology on a scheme over a field has the same dimension as the cohomology of the direct
image along an isomorphism.** -/
theorem finrank_cohomologyOverField_pushforward (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Spec (.of k)) (M : X.Modules) (n : ℕ) :
    Module.finrank k (cohomologyOverField k (f ≫ g) M n) =
      Module.finrank k (cohomologyOverField k g ((Scheme.Modules.pushforward f).obj M) n) :=
  (cohomologyOverFieldPushforwardIso k f g M n).toLinearEquiv.finrank_eq

end AlgebraicGeometry

end
