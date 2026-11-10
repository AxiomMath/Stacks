module

public import StacksFrontier.AlgebraicGeometry.Cohomology.HypercoveringModuleComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology

/-!
# The `k`-structure of `cohomologyOverField`, read on the abelian-group-valued cohomology

Let `X` be a scheme over a field `k`. The `k`-vector space `AlgebraicGeometry.cohomologyOverField`
has the same underlying group as the abelian-group-valued cohomology `Hgroup X.ringCatSheaf ⊤ n F`,
and the action of a scalar `a` is the map induced on cohomology by multiplication by the image of
`a` in `Γ(X, ⊤)`, an endomorphism of `F` in the `Γ(X, ⊤)`-linear category of `𝒪_X`-modules.

So an additive map between two such cohomology groups which commutes with the maps induced by
these scalar endomorphisms is `k`-linear — in particular every component of a natural
transformation between cohomology functors — and finite dimensionality can be moved along it.

## Main definitions

* `AlgebraicGeometry.CohomologyScalars.scalarEndo`: multiplication by a global function.
* `AlgebraicGeometry.CohomologyScalars.toHgroup`: `cohomologyOverField k f F n ≃+ Hgroup ⊤ n F`.
* `AlgebraicGeometry.CohomologyScalars.linearMapOfHgroup`: the `k`-linear map attached to an
  additive map of cohomology groups commuting with the scalar endomorphisms.

## Main results

* `AlgebraicGeometry.CohomologyScalars.toHgroup_smul`: the action of `a : k` is the map induced
  by `scalarEndo F a`.
* `AlgebraicGeometry.CohomologyScalars.finiteDimensional_of_surjective` and
  `AlgebraicGeometry.CohomologyScalars.finiteDimensional_of_injective`: finite dimensionality
  along such a map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HypercoveringModules

universe u

namespace AlgebraicGeometry.CohomologyScalars

variable {X : Scheme.{u}}

/-- **Multiplication by a global function**, as an endomorphism of an `𝒪_X`-module: the action
of `r` in the `Γ(X, ⊤)`-linear category of `𝒪_X`-modules. -/
def scalarEndo (F : X.Modules) (r : Γ(X, ⊤)) : F ⟶ F :=
  letI := globalSectionsLinear X
  ((show X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)) from r) •
    𝟙 (show SheafOfModules.{u} X.ringCatSheaf from F) :)

/-- **The right derived functors of global sections act on `scalarEndo F r` by `r`.** -/
theorem rightDerived_map_scalarEndo_apply (F : X.Modules) (r : Γ(X, ⊤)) (n : ℕ)
    (w : ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj
      F) :
    ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).map
        (scalarEndo F r) w =
      (show X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)) from r) • w := by
  let := globalSectionsLinear X
  have h := Functor.Linear.map_smul
    (F := (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n)
    (𝟙 (show SheafOfModules.{u} X.ringCatSheaf from F))
    (show X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)) from r)
  rw [CategoryTheory.Functor.map_id] at h
  exact congrArg (fun φ => φ.hom w) h

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- The ring map `k ⟶ Γ(X, ⊤)` along which `AlgebraicGeometry.cohomologyOverField` restricts
scalars. -/
def fieldScalar : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

/-- `cohomologyOverField` has the abelian-group-valued cohomology as its underlying group. -/
def toHgroup (F : X.Modules) (n : ℕ) :
    cohomologyOverField k f F n ≃+ Hgroup X.ringCatSheaf ⊤ n F :=
  ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
    n).app F).addCommGroupIsoToAddEquiv

/-- **The scalar action of `cohomologyOverField` is the map induced by `scalarEndo`.** -/
theorem toHgroup_smul (F : X.Modules) (n : ℕ) (a : k) (v : cohomologyOverField k f F n) :
    toHgroup k f F n (a • v) =
      (Hfunctor X.ringCatSheaf ⊤ n).map (scalarEndo F (fieldScalar k f a))
        (toHgroup k f F n v) := by
  have h := ConcreteCategory.congr_hom
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
      n).hom.naturality (scalarEndo F (fieldScalar k f a))) v
  refine Eq.trans (congrArg ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
    X.ringCatSheaf ⊤ n).hom.app F) ?_) h
  exact (rightDerived_map_scalarEndo_apply F (fieldScalar k f a) n v).symm

variable {k f}

/-- **An additive map of cohomology groups commuting with the scalar endomorphisms is
`k`-linear.** -/
def linearMapOfHgroup {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of k)} {F : X.Modules}
    {F' : X'.Modules} {n n' : ℕ}
    (e : Hgroup X.ringCatSheaf ⊤ n F →+ Hgroup X'.ringCatSheaf ⊤ n' F')
    (he : ∀ (a : k) x, e ((Hfunctor X.ringCatSheaf ⊤ n).map (scalarEndo F (fieldScalar k f a)) x) =
      (Hfunctor X'.ringCatSheaf ⊤ n').map (scalarEndo F' (fieldScalar k f' a)) (e x)) :
    cohomologyOverField k f F n →ₗ[k] cohomologyOverField k f' F' n' where
  toFun v := (toHgroup k f' F' n').symm (e (toHgroup k f F n v))
  map_add' v w := by simp
  map_smul' a v := by
    apply (toHgroup k f' F' n').injective
    simp only [AddEquiv.apply_symm_apply, toHgroup_smul, he, RingHom.id_apply]

/-- `linearMapOfHgroup e he` is surjective when `e` is. -/
theorem linearMapOfHgroup_surjective {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of k)}
    {F : X.Modules} {F' : X'.Modules} {n n' : ℕ}
    (e : Hgroup X.ringCatSheaf ⊤ n F →+ Hgroup X'.ringCatSheaf ⊤ n' F') (he)
    (hs : Function.Surjective e) :
    Function.Surjective (linearMapOfHgroup (f := f) (f' := f') e he) := by
  intro w
  obtain ⟨x, hx⟩ := hs (toHgroup k f' F' n' w)
  refine ⟨(toHgroup k f F n).symm x, ?_⟩
  change (toHgroup k f' F' n').symm (e (toHgroup k f F n ((toHgroup k f F n).symm x))) = w
  rw [AddEquiv.apply_symm_apply, hx, AddEquiv.symm_apply_apply]

/-- `linearMapOfHgroup e he` is injective when `e` is. -/
theorem linearMapOfHgroup_injective {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of k)}
    {F : X.Modules} {F' : X'.Modules} {n n' : ℕ}
    (e : Hgroup X.ringCatSheaf ⊤ n F →+ Hgroup X'.ringCatSheaf ⊤ n' F') (he)
    (hi : Function.Injective e) :
    Function.Injective (linearMapOfHgroup (f := f) (f' := f') e he) := by
  intro v w h
  have h' := (toHgroup k f' F' n').symm.injective h
  exact (toHgroup k f F n).injective (hi h')

/-- **Finite dimensionality passes to the target of a surjection of cohomology groups commuting
with the scalar endomorphisms.** -/
theorem finiteDimensional_of_surjective {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of k)}
    {F : X.Modules} {F' : X'.Modules} {n n' : ℕ}
    (e : Hgroup X.ringCatSheaf ⊤ n F →+ Hgroup X'.ringCatSheaf ⊤ n' F')
    (he : ∀ (a : k) x, e ((Hfunctor X.ringCatSheaf ⊤ n).map (scalarEndo F (fieldScalar k f a)) x) =
      (Hfunctor X'.ringCatSheaf ⊤ n').map (scalarEndo F' (fieldScalar k f' a)) (e x))
    (hs : Function.Surjective e) [FiniteDimensional k (cohomologyOverField k f F n)] :
    FiniteDimensional k (cohomologyOverField k f' F' n') :=
  Module.Finite.of_surjective (linearMapOfHgroup e he) (linearMapOfHgroup_surjective e he hs)

/-- **Finite dimensionality passes to the source of an injection of cohomology groups commuting
with the scalar endomorphisms.** -/
theorem finiteDimensional_of_injective {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of k)}
    {F : X.Modules} {F' : X'.Modules} {n n' : ℕ}
    (e : Hgroup X.ringCatSheaf ⊤ n F →+ Hgroup X'.ringCatSheaf ⊤ n' F')
    (he : ∀ (a : k) x, e ((Hfunctor X.ringCatSheaf ⊤ n).map (scalarEndo F (fieldScalar k f a)) x) =
      (Hfunctor X'.ringCatSheaf ⊤ n').map (scalarEndo F' (fieldScalar k f' a)) (e x))
    (hi : Function.Injective e) [FiniteDimensional k (cohomologyOverField k f' F' n')] :
    FiniteDimensional k (cohomologyOverField k f F n) :=
  FiniteDimensional.of_injective (linearMapOfHgroup e he) (linearMapOfHgroup_injective e he hi)

end AlgebraicGeometry.CohomologyScalars

end
