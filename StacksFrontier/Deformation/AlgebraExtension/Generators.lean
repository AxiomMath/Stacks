module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.Deformation.AlgebraExtension.MapOfLift

/-!
# Lifting a family of generators to an extension of algebras

Let `a : 𝒜 ⟶ 𝒪` be a morphism of sheaves of commutative rings on a small site and let
`α : ℰ ⟶ 𝒪` be a family of generators of `𝒪` over `𝒜`, so that `𝒜[ℰ] ⟶ 𝒪` is locally
surjective. A *lift* of `α` to an extension `P` of `𝒜`-algebras of `𝒪` is a map `ℰ ⟶ 𝒪'_P`
over `𝒪`; it determines the homomorphism `𝒜[ℰ] ⟶ 𝒪'_P` of `𝒜`-algebras which presents `P`.

This file records Steps 2 and 3 of the proof of [Stacks Project, Tag 08UG] in terms of lifts:

* Step 2: a morphism of extensions `k : P ⟶ Q` along `φ` carries a lift `β` to `P` to the lift
  `β ≫ k` to `Q`, whose restriction to the relations `ℐ = Ker(𝒜[ℰ] ⟶ 𝒪)` is `φ` of that of `β`;
* Step 3: conversely, if two lifts `β` to `P` and `β'` to `Q` have restrictions to `ℐ` related
  by `φ`, there is a morphism `P ⟶ Q` along `φ`.

## Main definitions

* `Deformation.AlgebraExtension.GeneratorLift`: a lift of `α` to an extension.
* `Deformation.AlgebraExtension.GeneratorLift.hom`: the homomorphism `𝒜[ℰ] ⟶ 𝒪'` it determines.
* `Deformation.AlgebraExtension.GeneratorLift.restriction`: its restriction `ℐ ⟶ ℳ`.
* `Deformation.AlgebraExtension.GeneratorLift.comp`: the lift transported along a morphism.

## Main results

* `Deformation.AlgebraExtension.GeneratorLift.restriction_comp`: Step 2.
* `Deformation.AlgebraExtension.GeneratorLift.nonempty_mapAlong`: Step 3.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.Conormal (kernelIdeal)
open Stacks.Sites.FreeAlgebra

universe u

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)}
  {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}

variable (α) in
/-- **A lift of the family of generators `α : ℰ ⟶ 𝒪` to an extension `P`**: a map `ℰ ⟶ 𝒪'_P`
whose composite with the reduction is `α`. -/
structure GeneratorLift (P : AlgebraExtension a M) where
  /-- The lift. -/
  lift : E ⟶ underlyingPresheaf J P.extension
  /-- It lies over `α`. -/
  lift_comp : lift ≫ Functor.whiskerRight P.reduction.hom (forget CommRingCat.{u}) = α

namespace GeneratorLift

variable {P : AlgebraExtension a M} {Q : AlgebraExtension a N} (β : GeneratorLift α P)

/-- The homomorphism `𝒜[ℰ] ⟶ 𝒪'_P` of `𝒜`-algebras determined by a lift. -/
noncomputable def hom : freeAlgebraSheaf J A E ⟶ P.extension :=
  freeAlgebraSheafDesc J A P.extension E P.algebraMap β.lift

/-- The homomorphism determined by a lift restricts to the structure map `𝒜 ⟶ 𝒪'_P` on
coefficients. -/
theorem coefficientMap_hom : freeAlgebraSheafCoefficientMap J A E ≫ β.hom = P.algebraMap :=
  freeAlgebraSheafCoefficientMap_comp_desc J A P.extension E P.algebraMap β.lift

/-- The homomorphism determined by a lift sends the variables `ℰ ⟶ 𝒜[ℰ]` to the lift. -/
theorem variable_hom : freeAlgebraSheafVariable J A E ≫ Functor.whiskerRight
    ((sheafToPresheaf J CommRingCat.{u}).map β.hom) (forget CommRingCat.{u}) = β.lift :=
  freeAlgebraSheafVariable_comp_desc J A P.extension E P.algebraMap β.lift

/-- The homomorphism determined by a lift lies over the presentation `𝒜[ℰ] ⟶ 𝒪`. -/
theorem hom_reduction :
    β.hom ≫ P.reduction = Stacks.SheafOfModules.presentation J A O a E α := by
  refine freeAlgebraSheaf_hom_ext J A O E ?_ ?_
  · rw [← Category.assoc, β.coefficientMap_hom, P.algebraMap_reduction,
      freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      β.variable_hom, freeAlgebraSheafVariable_comp_desc]
    exact β.lift_comp

variable [hα : Presheaf.IsLocallySurjective J
  (Stacks.SheafOfModules.presentation J A O a E α).hom]

/-- The composite of the homomorphism determined by a lift with the reduction `𝒪'_P ⟶ 𝒪` is
locally surjective. -/
instance isLocallySurjective_hom_reduction :
    Presheaf.IsLocallySurjective J (β.hom ≫ P.reduction).hom := by
  rw [β.hom_reduction]
  exact hα

/-- **The restriction of a lift to the relations**, `ℐ = Ker(𝒜[ℰ] ⟶ 𝒪) ⟶ ℳ`. -/
noncomputable def restriction (U : Cᵒᵖ)
    (g : kernelIdeal (Stacks.SheafOfModules.presentation J A O a E α).hom U) : M.val.obj U :=
  P.liftKernel β.hom U ⟨g.1, by
    have h : (β.hom ≫ P.reduction).hom.app U g.1 = 0 := by
      rw [β.hom_reduction]
      exact g.2
    exact h⟩

omit hα in
/-- The inclusion `ℳ ⟶ 𝒪'_P` sends the restriction of a lift at a relation `g` to the image of
`g` under the homomorphism determined by the lift. -/
theorem incl_restriction (U : Cᵒᵖ)
    (g : kernelIdeal (Stacks.SheafOfModules.presentation J A O a E α).hom U) :
    P.incl (β.restriction U g) = β.hom.hom.app U (g : (freeAlgebraSheaf J A E).obj.obj U) :=
  P.incl_liftKernel β.hom U _

/-- The lift transported along a morphism of extensions. -/
noncomputable def comp {φ : M ⟶ N} (k : MapAlong φ P Q) : GeneratorLift α Q where
  lift := β.lift ≫ Functor.whiskerRight k.hom.hom (forget CommRingCat.{u})
  lift_comp := by
    rw [Category.assoc, ← Functor.whiskerRight_comp]
    have h : k.hom.hom ≫ Q.reduction.hom = P.reduction.hom :=
      congrArg (fun t : P.extension ⟶ O => t.hom) k.reduction_comm
    rw [h, β.lift_comp]

omit hα in
/-- The homomorphism determined by the transported lift `β.comp k` is the composite of that
determined by `β` with `k`. -/
theorem comp_hom {φ : M ⟶ N} (k : MapAlong φ P Q) : (β.comp k).hom = β.hom ≫ k.hom := by
  refine freeAlgebraSheaf_hom_ext J A Q.extension E ?_ ?_
  · rw [coefficientMap_hom, ← Category.assoc, β.coefficientMap_hom, k.algebraMap_comm]
  · rw [variable_hom, CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp,
      ← Category.assoc, β.variable_hom]
    rfl

omit hα in
/-- **Step 2 of the proof of [Stacks Project, Tag 08UG].** Transporting a lift along a morphism
of extensions along `φ` composes its restriction to the relations with `φ`. -/
theorem restriction_comp {φ : M ⟶ N} (k : MapAlong φ P Q) (U : Cᵒᵖ)
    (g : kernelIdeal (Stacks.SheafOfModules.presentation J A O a E α).hom U) :
    (β.comp k).restriction U g = φ.val.app U (β.restriction U g) := by
  refine Q.incl_injective ?_
  rw [incl_restriction, comp_hom]
  refine Eq.trans ?_ (k.kernel_comm U (β.restriction U g))
  change k.hom.hom.app U (β.hom.hom.app U _) = k.hom.hom.app U (P.incl (β.restriction U g))
  rw [incl_restriction]

variable [J.WEqualsLocallyBijective CommRingCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]

/-- **Step 3 of the proof of [Stacks Project, Tag 08UG].** If a lift `β` to `P` and a lift `β'`
to `Q` have restrictions to the relations related by `φ`, there is a morphism of extensions
`P ⟶ Q` along `φ`. -/
theorem nonempty_mapAlong {φ : M ⟶ N} (β' : GeneratorLift α Q)
    (h : ∀ (U : Cᵒᵖ) (g : kernelIdeal (Stacks.SheafOfModules.presentation J A O a E α).hom U),
      β'.restriction U g = φ.val.app U (β.restriction U g)) :
    Nonempty (MapAlong φ P Q) :=
  P.nonempty_mapAlong_of_lift β.hom (freeAlgebraSheafCoefficientMap J A E) β.coefficientMap_hom φ
    β'.hom (by rw [β'.hom_reduction, β.hom_reduction]) β'.coefficientMap_hom fun U g => by
      have hg : (g : (freeAlgebraSheaf J A E).obj.obj U) ∈
          kernelIdeal (Stacks.SheafOfModules.presentation J A O a E α).hom U := by
        have h0 : (β.hom ≫ P.reduction).hom.app U g.1 = 0 := g.2
        have h1 : (β.hom ≫ P.reduction).hom.app U g.1 =
            (Stacks.SheafOfModules.presentation J A O a E α).hom.app U g.1 :=
          congrArg (fun t : freeAlgebraSheaf J A E ⟶ O => t.hom.app U g.1) β.hom_reduction
        exact h1.symm.trans h0
      rw [← β'.incl_restriction U ⟨g.1, hg⟩, h U ⟨g.1, hg⟩]
      rfl

end GeneratorLift

end Deformation.AlgebraExtension

end
