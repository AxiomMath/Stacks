module

public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# The two spellings of cohomology, compared on morphisms

`AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup` compares the `k`-module
`Hⁿ(X, ℱ)` of `AlgebraicGeometry.cohomologyOverField` with the abelian group `Hⁿ(X, ℱ)` of
`Hgroup` at the level of *objects*: one vanishes exactly when the other does. The arguments that
mix the two need more than that. The eventual annihilation of [Stacks, Tag 01XR] is proved in
the `Hgroup` spelling, because that is where the twisted localization of [Stacks, Tag 09MR]
lives; the long exact sequence, finite dimensionality and `Module.finrank` are available only in
the `cohomologyOverField` spelling, because only there is there a ground field. A dimension
count that consumes both needs the two to agree *on morphisms*.

This file supplies that: an additive equivalence between the two, natural in the module.

## Main results

* `AlgebraicGeometry.cohomologyOverFieldAddEquivHgroup`: the additive equivalence
  `Hⁿ(X, ℱ) ≃+ Hⁿ(X, ℱ)` between the two spellings.
* `AlgebraicGeometry.cohomologyOverFieldAddEquivHgroup_naturality`: **it is natural in the
  module**, so a morphism of modules induces the same map on cohomology in either spelling.
* `AlgebraicGeometry.injective_hfunctorMap_of_injective_cohomologyOverFieldMap` and
  `AlgebraicGeometry.surjective_hfunctorMap_of_surjective_cohomologyOverFieldMap`: the
  transports of injectivity and surjectivity that the dimension count uses.

## Where the equivalence comes from

`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` is the canonical half of
[Stacks, Tag 01F1] part (1): deriving the module-valued sections functor and then forgetting the
module structure agrees, naturally, with deriving the abelian-group-valued sections functor. The
equivalence below is that natural isomorphism read on carriers, and its naturality is
`CategoryTheory.NatTrans.naturality_apply` for it.

## Implementation notes

**`cohomologyOverFieldMap` has to be unfolded by hand.** Its body is the restriction of scalars
of the derived map, and `ModuleCat.restrictScalars` changes neither the carrier nor the
underlying function, so the comparison with the derived map is `rfl` in principle. In practice
the unifier does not find it: the two sides carry different `ConcreteCategory` instances — one
over `k`, one over `Γ(X, ⊤)` — and reducing them to a common term times out. The `unfold`
followed by Mathlib's `ModuleCat.restrictScalars.map_apply`, itself proved by `rfl`, is the same
equation stated where the instances are already aligned. The docstring of
`AlgebraicGeometry.cohomologyOverFieldMap` anticipates exactly this use, which is why that
definition carries `@[expose]`.

**The forgetful functor is crossed silently.** `(forget₂ (ModuleCat R) AddCommGrpCat).map g` has
the same underlying function as `g`, definitionally and cheaply, so the composite functor the
comparison isomorphism is stated over needs no lemma of its own.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The two spellings of `Hⁿ(X, ℱ)` are the same abelian group.** The `k`-module of
`AlgebraicGeometry.cohomologyOverField` and the group of `Hgroup` are identified by the
canonical comparison of [Stacks, Tag 01F1] part (1). -/
public def cohomologyOverFieldAddEquivHgroup (F : X.Modules) (n : ℕ) :
    (cohomologyOverField k f F n : Type u) ≃+ (Hgroup X.ringCatSheaf ⊤ n F : Type u) :=
  ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
    X.ringCatSheaf ⊤ n).app F).addCommGroupIsoToAddEquiv

/-- **`AlgebraicGeometry.cohomologyOverFieldMap` is the derived map.** Restriction of scalars
changes neither the carrier nor the underlying function. -/
public theorem cohomologyOverFieldMap_apply {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (x : (cohomologyOverField k f F n : Type u)) :
    cohomologyOverFieldMap k f φ n x =
      (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).map φ) x := by
  unfold cohomologyOverFieldMap
  exact ModuleCat.restrictScalars.map_apply _ _ x

/-- The module-valued cohomology functor with the module structure forgotten, which is the
source of the comparison isomorphism. -/
public abbrev derivedSectionsForget (X : Scheme.{u}) (n : ℕ) :=
  (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n ⋙
    forget₂ (ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat.{u}

/-- **Forgetting the module structure does not change the induced map.** -/
public theorem derivedSectionsForget_map_apply {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (y : ((derivedSectionsForget X n).obj F : Type u)) :
    (derivedSectionsForget X n).map φ y =
      (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).map φ) y :=
  rfl

/-- The naturality square of the comparison isomorphism, read on a class. -/
public theorem rightDerivedEvaluationForgetIso_naturality_apply {F G : X.Modules} (φ : F ⟶ G)
    (n : ℕ) (y : ((derivedSectionsForget X n).obj F : Type u)) :
    (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        X.ringCatSheaf ⊤ n).hom.app G ((derivedSectionsForget X n).map φ y) =
      (Hfunctor X.ringCatSheaf ⊤ n).map φ
        ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
          X.ringCatSheaf ⊤ n).hom.app F y) :=
  NatTrans.naturality_apply
    (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
      X.ringCatSheaf ⊤ n).hom φ y

/-- **The comparison is natural in the module.** A morphism of modules induces the same map on
cohomology in either spelling. -/
public theorem cohomologyOverFieldAddEquivHgroup_naturality {F G : X.Modules} (φ : F ⟶ G)
    (n : ℕ) (x : (cohomologyOverField k f F n : Type u)) :
    cohomologyOverFieldAddEquivHgroup k f G n (cohomologyOverFieldMap k f φ n x) =
      (Hfunctor X.ringCatSheaf ⊤ n).map φ
        (cohomologyOverFieldAddEquivHgroup k f F n x) :=
  (congrArg (cohomologyOverFieldAddEquivHgroup k f G n)
      ((cohomologyOverFieldMap_apply k f φ n x).trans
        (derivedSectionsForget_map_apply φ n x).symm)).trans
    (rightDerivedEvaluationForgetIso_naturality_apply φ n x)

/-- The map on `Hgroup` is the `cohomologyOverField` map conjugated by the comparison. -/
private theorem hfunctorMap_apply_eq_addEquiv_cohomologyOverFieldMap {F G : X.Modules}
    (φ : F ⟶ G) (n : ℕ) (a : (Hgroup X.ringCatSheaf ⊤ n F : Type u)) :
    (Hfunctor X.ringCatSheaf ⊤ n).map φ a = cohomologyOverFieldAddEquivHgroup k f G n
      (cohomologyOverFieldMap k f φ n ((cohomologyOverFieldAddEquivHgroup k f F n).symm a)) := by
  rw [cohomologyOverFieldAddEquivHgroup_naturality, AddEquiv.apply_symm_apply]

/-- **Injectivity transports from the `k`-module spelling to the group spelling.** -/
public theorem injective_hfunctorMap_of_injective_cohomologyOverFieldMap {F G : X.Modules}
    (φ : F ⟶ G) (n : ℕ) (h : Function.Injective (cohomologyOverFieldMap k f φ n)) :
    Function.Injective ((Hfunctor X.ringCatSheaf ⊤ n).map φ) := by
  intro a b hab
  rw [hfunctorMap_apply_eq_addEquiv_cohomologyOverFieldMap k f,
    hfunctorMap_apply_eq_addEquiv_cohomologyOverFieldMap k f] at hab
  exact (cohomologyOverFieldAddEquivHgroup k f F n).symm.injective
    (h ((cohomologyOverFieldAddEquivHgroup k f G n).injective hab))

/-- **Surjectivity transports from the `k`-module spelling to the group spelling.** -/
public theorem surjective_hfunctorMap_of_surjective_cohomologyOverFieldMap {F G : X.Modules}
    (φ : F ⟶ G) (n : ℕ) (h : Function.Surjective (cohomologyOverFieldMap k f φ n)) :
    Function.Surjective ((Hfunctor X.ringCatSheaf ⊤ n).map φ) := by
  intro b
  obtain ⟨a, ha⟩ := h ((cohomologyOverFieldAddEquivHgroup k f G n).symm b)
  refine ⟨cohomologyOverFieldAddEquivHgroup k f F n a, ?_⟩
  rw [hfunctorMap_apply_eq_addEquiv_cohomologyOverFieldMap k f, AddEquiv.symm_apply_apply, ha,
    AddEquiv.apply_symm_apply]

end AlgebraicGeometry

end
