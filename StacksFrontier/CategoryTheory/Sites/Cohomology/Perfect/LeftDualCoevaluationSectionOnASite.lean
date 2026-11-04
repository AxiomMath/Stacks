module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CochainEvaluationTotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualCoevaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOnTheSlices
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalPureTensorSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalPureTensorSectionsOfTensorComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitComplexMapsOverAnObject

/-!
# The coevaluation of a left dual as a local section, on a ringed site

Let `(C, O)` be a ringed site, let `M^•` and `N^•` be K-flat complexes of `O`-modules and let

`η : 𝟙 ⟶ Q(M^•) ⊗^L Q(N^•)`

be a morphism of `D(O)` out of the monoidal unit of Stacks 0FPT — for instance the coevaluation
of an exact pairing, which is the hypothesis of [Stacks, Tag 0FPV]. This file carries out the
first two steps of the second paragraph of the proof of that tag, on a ringed site:

* `η` is, along the arrows `f : W ⟶ V` of a covering sieve of any object `V`, **the section
  `η(1)`**: a degree-zero cocycle section of `Tot(M^• ⊗_O N^•)` over `W` inducing `η`; and
* that section is, after a further covering, a **finite sum of pure tensors**
  `∑ᵢ fᵢ ⊗ gᵢ` of sections of the terms of `M^•` and `N^•`.

Together these are the source's *"after replacing `X` by the members of a covering, we can find
an integer `N` and for `i = 1, …, N` integers `nᵢ` and sections `fᵢ` and `gᵢ` of `M^{nᵢ}` and
`N^{-nᵢ}` such that `η(1) = ∑ᵢ fᵢ ⊗ gᵢ`"*.

Nothing below is a clause of a tag; these are steps of a proof, so no `@[stacks …]` attribute is
attached.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_cocycleHomOver`: a morphism of `D(O)` out of
  the structure sheaf in degree zero is, along the arrows of a covering sieve, induced by a
  degree-zero cocycle section.
* `AlgebraicGeometry.RingedSite.exists_coveringSieve_coevaluationSection`: the same for `η`,
  which is the section `η(1)`.
* `AlgebraicGeometry.RingedSite.cocycleOfOver_restrictComplexMapAlong`: the degree-zero cocycle
  section of a chain-level representative restricts along an arrow of the site, which is what
  lets the two coverings below be composed.
* `AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorComplexSection`, imported here: a section
  of `Tot(A ⊗_O B)` is, on a covering sieve, a finite sum of pure tensors — the statement of
  `AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection` read at the spelling
  `Stacks.SheafOfModules.Tensor.tensorComplex` of the total tensor complex, which is the tensor
  product of the monoidal category of complexes of Stacks 0FPQ and hence the one the derived
  tensor product of Stacks 0FPT is compared with.

## Implementation notes

**Reading a morphism as a section.** The passage from a morphism of complexes `O|_W[0] ⟶ A|_W` to
a degree-zero cocycle section of `A` over `W` is
`StacksFrontier.CategoryTheory.Sites.Modules.UnitComplexMapsOverAnObject`: the slice `C/W` has the
terminal object `Over.mk (𝟙 W)`, so a morphism out of the structure sheaf of the slice is
determined by, and determines, the image of `1` there. No terminal object of `C` is used
anywhere, which is what makes the argument work on a site rather than only on a space.

**Why a second covering is needed for the sum of pure tensors, and how the two are composed.**
The degree-zero term of `Tot(M^• ⊗_O N^•)` is a coproduct of *sheafified* tensor products, so a
section of it is a finite sum of pure tensors only locally; that is the one localization
`AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection` performs. To compose the two
coverings into one — which is what the retract step of [Stacks, Tag 0FPV] needs, since it wants
the cocycle statement and the decomposition over the *same* object — the cocycle statement at `W`
has to be restricted along a further arrow `g : W' ⟶ W`, **with the section restricted along
`g`**. Choosing a fresh representative at `W'` does not help: the covering sieve is closed under
precomposition, so `g ≫ f` carries its own cocycle section, but that section is not the
restriction of the one at `W`, and only the restriction is known to decompose.

Both halves of that restriction are available. The *morphism of complexes* restricts along any
arrow of the site by
`AlgebraicGeometry.RingedSite.mapDerivedCategory_map_eq_restrictComplexMapAlong`, and its
degree-zero cocycle section restricts accordingly by
`AlgebraicGeometry.RingedSite.cocycleOfOver_restrictComplexMapAlong` below.

**The two spellings of the total tensor complex.** `exists_sieve_sum_tensorTotalSection` is
stated at `AlgebraicGeometry.RingedSite.tensorTotal` and the monoidal structure of Stacks 0FPQ
uses `Stacks.SheafOfModules.Tensor.tensorComplex`; the two are identified by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, which matches the two local pure
tensors by `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex_hom_tensorTotalSectionAt`.
That comparison is the whole content of the transport below.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
variable [HasSheafify X.J AddCommGrpCat.{u}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
variable [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hCoevDer : ∀ W : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))]

/-- The category of sheaves of modules over the restriction of `O` to the slice `C/W` has a
derived category. -/
local instance coevHasDerivedOver (W : X.C) :
    HasDerivedCategory.{d}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
  hCoevDer W

/-- Restriction of sheaves of `O`-modules to the slice `C/W` preserves finite limits. -/
local instance coevPreservesFiniteLimits (W : X.C) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W

/-- Restriction of sheaves of `O`-modules to the slice `C/W` preserves finite colimits. -/
local instance coevPreservesFiniteColimits (W : X.C) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W

/-- **A morphism of `D(O)` out of the structure sheaf in degree zero is, along the arrows of a
covering sieve of any object `V`, induced by a degree-zero cocycle section.** For `α : O[0] ⟶ F`
in `D(O)` there is a covering sieve of `V` along each of whose arrows `f : W ⟶ V` there is a
section `t` of `F^0` over `W` with `d(t) = 0` such that the restriction of `α` to the slice
`C/W` is the image of the morphism of complexes `O|_W[0] ⟶ F|_W` attached to `t`.

This is Stacks 08FR (1) at the strictly perfect complex `O[0]`, read through the correspondence
between morphisms out of the structure sheaf of a slice and cocycle sections,
`SheafOfModules.cocycleHomOver`. -/
theorem exists_coveringSieve_cocycleHomOver (V : X.C)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (α : DerivedCategory.Q.obj (structureSheafComplex X) ⟶ DerivedCategory.Q.obj F) :
    ∃ S : Sieve V, S ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (f : W ⟶ V), S f →
        ∃ (t : (F.X 0).val.obj (op W)) (ht : (F.d 0 1).val.app (op W) t = 0),
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            W).mapDerivedCategory.map α ≫
              (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                W).mapDerivedCategoryFactors.hom.app F =
            (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              W).mapDerivedCategoryFactors.hom.app
                (structureSheafComplex X) ≫
              DerivedCategory.Q.map
                ((SheafOfModules.overFunctorUnitComplexIso
                    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).hom ≫
                  SheafOfModules.cocycleHomOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                    F W t ht) := by
  obtain ⟨S, hS, hβ⟩ := exists_coveringSieve_restrictComplexMap X V
    (isStrictlyPerfect_restrictComplex_structureSheafComplex X V) 0
    (fun i hi => by
      have h : IsZero ((structureSheafComplex X).X i) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i (by omega)
      exact Functor.map_isZero
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) h) α
  refine ⟨S, hS, ?_⟩
  intro W f hf
  obtain ⟨β, hβW⟩ := hβ f hf
  refine ⟨SheafOfModules.cocycleOfOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      ((SheafOfModules.overFunctorUnitComplexIso
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).inv ≫ β),
    SheafOfModules.cocycleOfOver_d (Stacks.SheafOfModules.Tensor.ringSheaf X.O) _, hβW.trans ?_⟩
  refine congrArg (fun φ => _ ≫ DerivedCategory.Q.map φ) ?_
  rw [← SheafOfModules.eq_cocycleHomOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    ((SheafOfModules.overFunctorUnitComplexIso
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).inv ≫ β), ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- **The degree-zero cocycle section of a chain-level representative restricts along an arrow
of the site.** Let `β : O|_V[0] ⟶ F|_V` be a morphism of complexes out of the restriction of the
structure sheaf in degree zero and let `g : W ⟶ V` be any arrow of `C`. The degree-zero cocycle
section that
`AlgebraicGeometry.RingedSite.restrictComplexMapAlong`, the restriction of `β` along `g`,
corresponds to is the restriction along `g` of the one `β` corresponds to.

This is what composes the two coverings of the proof of [Stacks, Tag 0FPV]: the derived half of
the restriction is
`AlgebraicGeometry.RingedSite.mapDerivedCategory_map_eq_restrictComplexMapAlong`, and this is
its section half, so that the cocycle statement obtained over `W` can be refined to a further
covering *with its section restricted* — which is the form in which the section is known to be a
finite sum of pure tensors.

The proof is naturality of `β` in degree zero along `Over.homMk g : Over.mk (𝟙 W ≫ g) ⟶
Over.mk (𝟙 V)` in `C/V` together with `PresheafOfModules.unit_map_one`. Everything else is
definitional: the components of `SheafOfModules.overFunctorMap` and of
`SheafOfModules.overFunctorUnitIso` are the identity on sections, the comparisons
`HomologicalComplex.singleObjXSelf` and `HomologicalComplex.singleMapHomologicalComplex` are
`eqToHom`s between definitionally equal objects, and restriction to a slice reindexes sections
along `Over.forget`. -/
theorem cocycleOfOver_restrictComplexMapAlong {V W : X.C} (g : W ⟶ V)
    {F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (β : X.restrictComplex (structureSheafComplex X) V ⟶ X.restrictComplex F V) :
    SheafOfModules.cocycleOfOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((SheafOfModules.overFunctorUnitComplexIso
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).inv ≫
          restrictComplexMapAlong X g β) =
      (F.X 0).val.map g.op
        (SheafOfModules.cocycleOfOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((SheafOfModules.overFunctorUnitComplexIso
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).inv ≫ β)) := by
  obtain ⟨h, hh⟩ : ∃ h : (Over.map g).obj (Over.mk (𝟙 W)) ⟶ Over.mk (𝟙 V),
      h = Over.homMk g (by simp) := ⟨_, rfl⟩
  have hone : ((X.restrictComplex (structureSheafComplex X) V).X 0).val.map h.op
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)) =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) := by
    subst hh
    exact PresheafOfModules.unit_map_one (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj g.op
  have hnat := PresheafOfModules.naturality_apply (β.f 0).val h.op
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))
  have hL : SheafOfModules.cocycleOfOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((SheafOfModules.overFunctorUnitComplexIso
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).inv ≫
          restrictComplexMapAlong X g β) =
      (β.f 0).val.app (op ((Over.map g).obj (Over.mk (𝟙 W))))
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) := rfl
  have hR : SheafOfModules.cocycleOfOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((SheafOfModules.overFunctorUnitComplexIso
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).inv ≫ β) =
      (β.f 0).val.app (op (Over.mk (𝟙 V)))
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)) := rfl
  rw [hL, hR, ← hone, hnat]
  subst hh
  rfl

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
variable [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
variable [∀ (K L : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
  HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)]

variable [∀ W : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
    (X.O.over W)))]

/-- **The section `η(1)` of [Stacks, Tag 0FPV], on a ringed site.** Let `M^•` and `N^•` be K-flat
complexes of `O`-modules and let `η : 𝟙 ⟶ Q(M^•) ⊗^L Q(N^•)` be a morphism of `D(O)` out of the
monoidal unit of Stacks 0FPT — for instance the coevaluation of an exact pairing. Then every
object `V` of `C` admits a covering sieve along each of whose arrows `f : W ⟶ V` there is a
degree-zero cocycle section `t` of `Tot(M^• ⊗_O N^•)` over `W` inducing the restriction of `η` to
the slice `C/W`.

This is the step of the proof of [Stacks, Tag 0FPV] at which the coevaluation of a left dual
becomes a chain-level datum, so that the sections `fᵢ` and `gᵢ` of the source's
`η(1) = ∑ᵢ fᵢ ⊗ gᵢ` can be extracted from it by
`AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorComplexSection`. -/
theorem exists_coveringSieve_coevaluationSection (V : X.C)
    (Mc Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)
    (hM : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Mc)
    (hN : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Nc)
    (η : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
      𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O) ⟶
        DerivedCategory.Q.obj Mc ⊗ DerivedCategory.Q.obj Nc) :
    ∃ S : Sieve V, S ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (f : W ⟶ V), S f →
        ∃ (t : (((Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)).X
            0).val.obj (op W))
          (ht : (((Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)).d
            0 1).val.app (op W) t = 0),
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            W).mapDerivedCategory.map
                (coevaluationUnitHom X Mc Nc hM hN η) ≫
              (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                W).mapDerivedCategoryFactors.hom.app
                ((Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)) =
            (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              W).mapDerivedCategoryFactors.hom.app
                (structureSheafComplex X) ≫
              DerivedCategory.Q.map
                ((SheafOfModules.overFunctorUnitComplexIso
                    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).hom ≫
                  SheafOfModules.cocycleHomOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                    ((Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O))
                    W t ht) :=
  exists_coveringSieve_cocycleHomOver X V _ (coevaluationUnitHom X Mc Nc hM hN η)

end AlgebraicGeometry.RingedSite

end
