module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The lower shriek of the structure sheaf of a full subsite, and `g_!O_{𝒳'} = O_𝒳`

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids carrying the site of **Stacks 06TP** and
let `P` cut out a full subcategory whose inclusion is continuous and cocontinuous for the
inherited topology, so that `StacksFrontier/AlgebraicGeometry/Stacks/SubcategoryRingedTopos.lean`
builds the morphism of ringed topoi `g : (Sh(𝒳'), O_{𝒳'}) ⟶ (Sh(𝒳), O_𝒳)` and
`StacksFrontier/AlgebraicGeometry/Stacks/SubcategoryModuleLowerShriek.lean` builds the lower shriek
`g_!` on sheaves of modules left adjoint to `g^*`.

This file is about the value of `g_!` on the structure sheaf. The identification
`O_{𝒳'} ≅ g^*O_𝒳` of **Stacks 0788** (f) has an adjoint transpose

`g_!O_{𝒳'} ⟶ O_𝒳`,

and **Stacks 078A** asserts that it is an isomorphism, for the lisse-étale site in part (1) and
for the flat-fppf site in part (2).

## What is proved

Two of the three results below hold for every full subsite, with no further hypothesis:

* restricting the canonical map back to the subsite gives an isomorphism — so `g_!O_{𝒳'} = O_𝒳`
  holds after applying `g^*`; and
* the canonical map is an isomorphism exactly when `O_𝒳` lies in the essential image of `g_!`.

Both come from `g^*g_! = id` (**Stacks 0789**), which makes `g_!` fully faithful and identifies
the canonical map, up to an isomorphism, with the counit of `g_! ⊣ g^*` at `O_𝒳`.

The assertion of Stacks 078A itself is proved from the hypothesis that **restriction along `g`
is bijective on morphisms out of `O_𝒳`**, i.e. that the structure sheaf of modules of `𝒳` is the
left Kan extension along the inclusion of its own restriction. That hypothesis is the geometric
content of the source and is carried as a named hypothesis; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Stack.subsiteUnitLowerShriekMap`: the canonical map `g_!O_{𝒳'} ⟶ O_𝒳`, the
  adjoint transpose of the identification `O_{𝒳'} = g^{-1}O_𝒳`.

## Main results

* `AlgebraicGeometry.Stack.isIso_map_subsiteUnitLowerShriekMap`: `g^*` of the canonical map is an
  isomorphism.
* `AlgebraicGeometry.Stack.isIso_subsiteUnitLowerShriekMap_iff_mem_essImage`: the canonical map is
  an isomorphism if and only if `O_𝒳` is in the essential image of `g_!`.
* `AlgebraicGeometry.Stack.isIso_subsiteUnitLowerShriekMap`: it is an isomorphism when restriction
  along `g` is bijective on morphisms out of `O_𝒳`.
* `AlgebraicGeometry.Stack.LisseEtale.isIso_unitLowerShriekMap` and
  `AlgebraicGeometry.Stack.FlatFppf.isIso_unitLowerShriekMap`: the two clauses of
  **Stacks 078A**, under that hypothesis.

## Implementation notes

The hypothesis of `AlgebraicGeometry.Stack.isIso_subsiteUnitLowerShriekMap` is the universal
property which
`StacksFrontier/AlgebraicGeometry/Topologies/SubcategoryStructureSheafLowerShriek.lean`
establishes for full subcategories of the big fppf category over a *scheme* `X`
(`AlgebraicGeometry.bijective_whiskerLeft_bigOverPresheafAb`, the presheaf half of
**Stacks 07AJ** (b)): there the structure presheaf is *represented* by the affine line over `X`
and its square by the affine plane, and those two objects lie in the subcategory. Over a stack
that argument is unavailable in this global form, because `𝒳 × 𝐀¹` is not an object of `𝒳` — the
objects of `𝒳` are schemes. The source accordingly proves Stacks 078A by a local argument with
the colimit presentation of `g_{p!}O_{𝒳'}`: a function on `V` is classified by a morphism
`V ⟶ U × 𝐀¹` after an étale covering of `V` refining through a smooth (resp. flat) `U`, and a
function vanishing on `V` is pushed into the vanishing locus of a coordinate. Carrying out that
localisation is what remains; the hypothesis isolates it, and everything downstream of it is
proved here.

The transposition is the one of `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`,
which identifies `g^*O_𝒳` with `O_{𝒳'}` by corepresentability rather than by computing the tensor
product, so the canonical map is pinned down with nothing chosen.

## References

* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 078A](https://stacks.math.columbia.edu/tag/078A)
* [Stacks Project, Tag 07AJ](https://stacks.math.columbia.edu/tag/07AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Subsite

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (P : ObjectProperty X)
  [EssentiallySmall.{u} X]
  [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- **The identification `O_{𝒳'} = g^{-1}O_𝒳` of Stacks 0788 (f), read on sheaves of modules.**
The pullback of sheaves of modules along the morphism of ringed topoi of a full subsite carries
the structure sheaf of `𝒳` to the structure sheaf of `𝒳'`, both read as the free module of rank
one over themselves. -/
abbrev subsiteUnitPullbackIso :
    SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS p hp τ hτ P).O) ≅
      (subsiteModulePullback B S hS p hp τ hτ P).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O)) :=
  pullbackModulesObjUnitIso (subsiteRingedToposHom B S hS p hp τ hτ P).toModulesHom

/-- **The canonical map `g_!O_{𝒳'} ⟶ O_𝒳`** for a full subsite: the transpose, under the
adjunction `g_! ⊣ g^*` of **Stacks 0789**, of the identification `O_{𝒳'} = g^{-1}O_𝒳` of
**Stacks 0788** (f). This is the map **Stacks 078A** asserts to be an isomorphism. -/
def subsiteUnitLowerShriekMap :
    (subsiteModuleLowerShriek B S hS p hp τ hτ P).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS p hp τ hτ P).O)) ⟶
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O) :=
  ((subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P).homEquiv _ _).symm
    (subsiteUnitPullbackIso B S hS p hp τ hτ P).hom

/-- The transpose of the canonical map is the identification `O_{𝒳'} = g^{-1}O_𝒳`, by
definition. -/
lemma homEquiv_subsiteUnitLowerShriekMap :
    (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P).homEquiv _ _
        (subsiteUnitLowerShriekMap B S hS p hp τ hτ P) =
      (subsiteUnitPullbackIso B S hS p hp τ hτ P).hom :=
  Equiv.apply_symm_apply _ _

/-- The canonical map is the counit of `g_! ⊣ g^*` at `O_𝒳`, precomposed with `g_!` of the
identification `O_{𝒳'} = g^{-1}O_𝒳`. -/
lemma subsiteUnitLowerShriekMap_eq :
    subsiteUnitLowerShriekMap B S hS p hp τ hτ P =
      (subsiteModuleLowerShriek B S hS p hp τ hτ P).map
          (subsiteUnitPullbackIso B S hS p hp τ hτ P).hom ≫
        (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P).counit.app _ :=
  Adjunction.homEquiv_counit _ _ _ _

/-- Postcomposition with the canonical map is restriction of morphisms out of `O_𝒳` along `g`,
read through the adjunction `g_! ⊣ g^*` and the identification `O_{𝒳'} = g^{-1}O_𝒳`. -/
lemma comp_subsiteUnitLowerShriekMap
    (T : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O))
    (x : SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O) ⟶ T) :
    subsiteUnitLowerShriekMap B S hS p hp τ hτ P ≫ x =
      ((subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P).homEquiv _ T).symm
        ((subsiteUnitPullbackIso B S hS p hp τ hτ P).hom ≫
          (subsiteModulePullback B S hS p hp τ hτ P).map x) := by
  rw [Equiv.eq_symm_apply, Adjunction.homEquiv_naturality_right,
    homEquiv_subsiteUnitLowerShriekMap]

/-- `g_!` is full and faithful, because `g^*g_! = id` (**Stacks 0789**). -/
private theorem full_and_faithful_subsiteModuleLowerShriek :
    (subsiteModuleLowerShriek B S hS p hp τ hτ P).Full ∧
      (subsiteModuleLowerShriek B S hS p hp τ hτ P).Faithful := by
  have := isIso_subsiteModuleLowerShriekAdjunction_unit B S hS p hp τ hτ P
  have h := Adjunction.fullyFaithfulLOfIsIsoUnit
    (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P)
  exact ⟨h.full, h.faithful⟩

/-- **`g^*` of the canonical map `g_!O_{𝒳'} ⟶ O_𝒳` is an isomorphism**, for every full subsite
and with no further hypothesis: so the assertion of **Stacks 078A** holds after restricting back
to the subsite.

The canonical map is `g_!` of an isomorphism followed by the counit of `g_! ⊣ g^*`, and the right
triangle of the adjunction makes `g^*` of that counit a retract of the unit, which is an
isomorphism by **Stacks 0789**. -/
theorem isIso_map_subsiteUnitLowerShriekMap :
    IsIso ((subsiteModulePullback B S hS p hp τ hτ P).map
      (subsiteUnitLowerShriekMap B S hS p hp τ hτ P)) := by
  have := isIso_subsiteModuleLowerShriekAdjunction_unit B S hS p hp τ hτ P
  obtain ⟨_, _⟩ := full_and_faithful_subsiteModuleLowerShriek B S hS p hp τ hτ P
  rw [subsiteUnitLowerShriekMap_eq, Functor.map_comp]
  infer_instance

/-- **The canonical map `g_!O_{𝒳'} ⟶ O_𝒳` is an isomorphism if and only if `O_𝒳` lies in the
essential image of `g_!`**, for every full subsite and with no further hypothesis. This is the
assertion of **Stacks 078A** read as a statement about the essential image of `g_!`.

`g_!` is fully faithful because `g^*g_! = id` (**Stacks 0789**), so the counit of `g_! ⊣ g^*` is
invertible at an object exactly when that object is in the essential image; and the canonical map
differs from the counit at `O_𝒳` by `g_!` of an isomorphism. -/
theorem isIso_subsiteUnitLowerShriekMap_iff_mem_essImage :
    IsIso (subsiteUnitLowerShriekMap B S hS p hp τ hτ P) ↔
      (subsiteModuleLowerShriek B S hS p hp τ hτ P).essImage
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O)) := by
  have := isIso_subsiteModuleLowerShriekAdjunction_unit B S hS p hp τ hτ P
  obtain ⟨_, _⟩ := full_and_faithful_subsiteModuleLowerShriek B S hS p hp τ hτ P
  rw [← Adjunction.isIso_counit_app_iff_mem_essImage
    (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P), subsiteUnitLowerShriekMap_eq]
  exact ⟨fun _ ↦ IsIso.of_isIso_comp_left
      ((subsiteModuleLowerShriek B S hS p hp τ hτ P).map
        (subsiteUnitPullbackIso B S hS p hp τ hτ P).hom) _,
    fun _ ↦ inferInstance⟩

/-- **The canonical map `g_!O_{𝒳'} ⟶ O_𝒳` is an isomorphism** for a full subsite along which
restriction is bijective on morphisms out of `O_𝒳`, that is, for which the structure sheaf of
modules of `𝒳` is the left Kan extension along the inclusion of its own restriction.

This is the assertion of **Stacks 078A**, stated once for an arbitrary continuous and
cocontinuous full subsite. Postcomposition with the canonical map is, by the adjunction
`g_! ⊣ g^*` and the identification `O_{𝒳'} = g^{-1}O_𝒳`, exactly that restriction. -/
theorem isIso_subsiteUnitLowerShriekMap
    (hres : ∀ T : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O),
      Function.Bijective fun x : SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O) ⟶ T =>
        (subsiteModulePullback B S hS p hp τ hτ P).map x) :
    IsIso (subsiteUnitLowerShriekMap B S hS p hp τ hτ P) := by
  refine isIso_of_coyoneda_map_bijective _ fun T ↦ ?_
  have key : Function.Bijective
      (fun y : (subsiteModulePullback B S hS p hp τ hτ P).obj (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O)) ⟶
          (subsiteModulePullback B S hS p hp τ hτ P).obj T =>
        (subsiteUnitPullbackIso B S hS p hp τ hτ P).hom ≫ y) := by
    refine ⟨fun y₁ y₂ hy ↦ ?_,
      fun z ↦ ⟨(subsiteUnitPullbackIso B S hS p hp τ hτ P).inv ≫ z, by simp⟩⟩
    simpa using congrArg (fun z ↦ (subsiteUnitPullbackIso B S hS p hp τ hτ P).inv ≫ z) hy
  have h : (fun x : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O) ⟶ T =>
      subsiteUnitLowerShriekMap B S hS p hp τ hτ P ≫ x) =
      ((subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P).homEquiv _ T).symm ∘
        ((fun y => (subsiteUnitPullbackIso B S hS p hp τ hτ P).hom ≫ y) ∘
          (fun x => (subsiteModulePullback B S hS p hp τ hτ P).map x)) :=
    funext fun x ↦ comp_subsiteUnitLowerShriekMap B S hS p hp τ hτ P T x
  rw [h]
  exact ((subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P).homEquiv _ T).symm.bijective.comp
    (key.comp (hres T))

end Subsite

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS) [EssentiallySmall.{u} 𝒳.val.val.obj]

-- the inclusion of the smooth objects is continuous and cocontinuous for the topology inherited
-- from `𝒳_{étale}`, the closure property of **Stacks 07AK** (1) holding for every algebraic
-- stack; the general subsite declarations ask for the two as instances
attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **The canonical map `g_!O_{𝒳_{lisse,étale}} ⟶ O_𝒳`**: the transpose, under the adjunction
`g_! ⊣ g^*` of **Stacks 0789** (1), of the identification `O_{𝒳_{lisse,étale}} = g^{-1}O_𝒳`. -/
noncomputable abbrev unitLowerShriekMap :=
  subsiteUnitLowerShriekMap B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳)

/-- **Stacks 078A (1)**: `g_!O_{𝒳_{lisse,étale}} = O_𝒳`, the canonical map from the lower shriek
of the structure sheaf of the lisse-étale site to the structure sheaf of `𝒳` being an
isomorphism. -/
@[stacks 078A "part (1); conditional on essential smallness of the category underlying the \
algebraic stack and on restriction along the lisse-étale inclusion being bijective on morphisms \
out of the structure sheaf of modules of the stack"]
theorem isIso_unitLowerShriekMap
    (hres : ∀ T : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).O),
      Function.Bijective fun x : SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).O) ⟶ T =>
        (subsiteModulePullback B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          (etaleTopology B) (etaleTopology_le_topology B)
          (smoothObject.{u, t} B S hS 𝒳)).map x) :
    IsIso (unitLowerShriekMap.{u, t} B S hS 𝒳) :=
  isIso_subsiteUnitLowerShriekMap B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳) hres

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS) [EssentiallySmall.{u} 𝒳.val.val.obj]

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **The canonical map `g_!O_{𝒳_{flat,fppf}} ⟶ O_𝒳`**: the transpose, under the adjunction
`g_! ⊣ g^*` of **Stacks 0789** (2), of the identification `O_{𝒳_{flat,fppf}} = g^{-1}O_𝒳`. -/
noncomputable abbrev unitLowerShriekMap :=
  subsiteUnitLowerShriekMap B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
    (objectProperty B S hS 𝒳)

/-- **Stacks 078A (2)**: `g_!O_{𝒳_{flat,fppf}} = O_𝒳`, the canonical map from the lower shriek of
the structure sheaf of the flat-fppf site to the structure sheaf of `𝒳` being an
isomorphism. -/
@[stacks 078A "part (2); conditional on essential smallness of the category underlying the \
algebraic stack and on restriction along the flat-fppf inclusion being bijective on morphisms \
out of the structure sheaf of modules of the stack"]
theorem isIso_unitLowerShriekMap
    (hres : ∀ T : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids B.topology le_rfl).O),
      Function.Bijective fun x : SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids B.topology le_rfl).O) ⟶ T =>
        (subsiteModulePullback B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
          (objectProperty B S hS 𝒳)).map x) :
    IsIso (unitLowerShriekMap B S hS 𝒳) :=
  isIso_subsiteUnitLowerShriekMap B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
    (objectProperty B S hS 𝒳) hres

end FlatFppf

end AlgebraicGeometry.Stack

end
