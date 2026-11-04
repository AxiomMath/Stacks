module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalConstructions
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.LeftDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.AcyclicCoversInALargerUniverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacementDegreeZero
import StacksCore.Tactic.StacksAttribute

/-!
# The simplicial replacement computes the derived colimits

Let `C` be a small category. Stacks 08PG computes the homology `H_n(C, F)` of an
abelian-group-valued presheaf on `C` — the left derived functors of `colim_{Cᵒᵖ}`, by Stacks
08PF — as the homology of the simplicial replacement complex `K_•(F)`. This file constructs that
comparison as the unique isomorphism of homological δ-functors extending the identification of
both sides with `colim F` in degree zero, hence as an isomorphism of functors in every degree.

## Main definitions

* `Stacks.CategoryHomology.replacementHomologyDeltaFunctor`: the homology of the simplicial
  replacement, as a homological δ-functor on abelian presheaves.
* `Stacks.CategoryHomology.derivedColimitDeltaFunctor`: the left derived functors of
  `colim_{Cᵒᵖ}`, as a homological δ-functor.
* `Stacks.CategoryHomology.replacementHomologyZeroNatIso`: the degree-zero comparison
  `H_0(K_•(-)) ≅ colim`, as an isomorphism of functors.
* `Stacks.CategoryHomology.derivedColimitZeroComparison`: the degree-zero comparison of the two
  δ-functors, `L_0 colim ≅ H_0(K_•(-))`.
* `Stacks.CategoryHomology.derivedColimitReplacementDeltaIso`: the resulting isomorphism of
  δ-functors.
* `Stacks.CategoryHomology.categoryHomologyReplacementNatIso` and
  `Stacks.CategoryHomology.categoryHomologyReplacementIso`: the comparison in degree `n`, as an
  isomorphism of functors and at a single presheaf.

## Main results

* `Stacks.CategoryHomology.replacementComplexFunctor_map_shortExact`: the simplicial replacement
  functor on presheaves preserves short exact sequences.
* `Stacks.CategoryHomology.derivedColimitDeltaFunctor_isUniversal` and
  `Stacks.CategoryHomology.replacementHomologyDeltaFunctor_isUniversal`: both δ-functors are
  universal.
* `Stacks.CategoryHomology.categoryHomologyReplacementIso_naturality`: the comparison is natural
  in the presheaf.
* `Stacks.CategoryHomology.categoryHomologyReplacementIso_zero`: in degree zero the comparison is
  the composite of `colim`'s right exactness with the cokernel presentation of `H_0(K_•(F))`.

## Implementation notes

Everything is stated for presheaves valued in `AddCommGrpCat.{max u v}`. The acyclic cover is
built for presheaves valued in `AddCommGrpCat.{u}`; it is the hypothesis of
`replacementHomologyDeltaFunctor_isUniversal_of_acyclicCover`, supplied by
`Stacks.CategoryHomology.exists_acyclic_epi_of_presheaf`.

The δ-functor `replacementHomologyDeltaFunctor` is built on presheaves, not on abelian sheaves
for the chaotic topology as `Stacks.CategoryHomology.simplicialReplacementHomologyDeltaFunctor`
is, so that it is stated in the spelling of `categoryHomology`.

## References

* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v

namespace Stacks.CategoryHomology

variable {C : Type u} [SmallCategory C]

/-! ### The simplicial replacement as a homological δ-functor on presheaves -/

/-- The simplicial replacement complex functor carries a short exact sequence of abelian
presheaves to a short exact sequence of complexes. -/
theorem replacementComplexFunctor_map_shortExact
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})} (hS : S.ShortExact) :
    (S.map (replacementComplexFunctor (C := C))).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hcomp (i : ComposableArrows C n) :
      (S.map ((evaluation Cᵒᵖ AddCommGrpCat).obj (op i.right))).ShortExact :=
    hS.map_of_exact _
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · show (ShortComplex.mk (replacementGroupMap S.f n) (replacementGroupMap S.g n) _).Exact
    rw [ShortComplex.ab_exact_iff_function_exact]
    exact directSum_exact _ _ fun i =>
      (ShortComplex.ab_exact_iff_function_exact _).1 (hcomp i).exact
  · show Mono (replacementGroupMap S.f n)
    rw [AddCommGrpCat.mono_iff_injective]
    exact (DirectSum.map_injective _).2 fun i =>
      (AddCommGrpCat.mono_iff_injective _).1 (hcomp i).mono_f
  · show Epi (replacementGroupMap S.g n)
    rw [AddCommGrpCat.epi_iff_surjective]
    exact (DirectSum.map_surjective _).2 fun i =>
      (AddCommGrpCat.epi_iff_surjective _).1 (hcomp i).epi_g

/-- The homology of the simplicial replacement, with the connecting morphisms of the long exact
sequence of a degreewise short exact sequence of complexes, as a homological δ-functor on
abelian presheaves. -/
def replacementHomologyDeltaFunctor :
    HomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v} :=
  HomologicalDeltaFunctor.ofChainComplexFunctor (replacementComplexFunctor (C := C))
    fun hS => replacementComplexFunctor_map_shortExact hS

/-- The degree-`n` functor of `Stacks.CategoryHomology.replacementHomologyDeltaFunctor` is
homology of the simplicial replacement in degree `n`. -/
lemma replacementHomologyDeltaFunctor_functor (n : ℕ) :
    (replacementHomologyDeltaFunctor.{u, v} (C := C)).functor n =
      replacementComplexFunctor (C := C) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.down ℕ) n :=
  rfl

/-- The left derived functors of `colim_{Cᵒᵖ}`, as a homological δ-functor. -/
abbrev derivedColimitDeltaFunctor :
    HomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v} :=
  (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerivedHomologicalDeltaFunctor

/-! ### The degree-zero comparison -/

/-- The value of `Stacks.CategoryHomology.replacementGroupMap` on a summand, in the spelling
`Stacks.CategoryHomology.replacementSummand`: it is the component of the morphism of presheaves
at the right endpoint of the index, in the same summand. -/
lemma replacementGroupMap_summand {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (η : F ⟶ G) (n : ℕ)
    (x : ComposableArrows C n) (s : F.obj (op x.right)) :
    (replacementGroupMap η n).hom (replacementSummand F n x s) =
      replacementSummand G n x ((η.app (op x.right)).hom s) := by
  classical
  show (DirectSum.map fun z => (η.app (op z.right)).hom)
    (DirectSum.of (fun z : ComposableArrows C n => F.obj (op z.right)) x s) = _
  rw [DirectSum.map_of]
  rfl

/-- **The augmentation `K_0(F) ⟶ colim F` is natural in `F`.** -/
lemma replacementGroupMap_comp_replacementAugmentation
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (η : F ⟶ G) :
    replacementGroupMap η 0 ≫ replacementAugmentation G =
      replacementAugmentation F ≫ colim.map η := by
  refine replacementGroup_hom_ext 0 fun x s => ?_
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, replacementGroupMap_summand,
    replacementAugmentation_summand, replacementAugmentation_summand]
  exact (ConcreteCategory.congr_hom (colimit.ι_map η (op x.right)) s).symm

/-- The degree-zero homology of the simplicial replacement is the colimit, as an isomorphism of
functors with components `Stacks.CategoryHomology.replacementHomologyZeroIsoColimit`. -/
def replacementHomologyZeroNatIso :
    replacementComplexFunctor (C := C) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.down ℕ) 0 ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _) :=
  NatIso.ofComponents (fun F => replacementHomologyZeroIsoColimit F) fun {F _G} η =>
    replacementHomologyZeroIsoColimit_naturality F ((replacementComplexFunctor (C := C)).map η)
      (colim.map η) (by
        rw [replacementComplexFunctor_map_f]
        exact replacementGroupMap_comp_replacementAugmentation η)

/-- **The degree-zero comparison of the two δ-functors**, `L_0 colim ≅ colim ≅ H_0(K_•(-))`,
the second isomorphism being the inverse of
`Stacks.CategoryHomology.replacementHomologyZeroNatIso`. -/
def derivedColimitZeroComparison :
    (derivedColimitDeltaFunctor.{u, v} (C := C)).functor 0 ≅
      (replacementHomologyDeltaFunctor.{u, v} (C := C)).functor 0 :=
  Functor.leftDerivedZeroIsoSelf _ ≪≫ (replacementHomologyZeroNatIso.{u, v} (C := C)).symm

/-! ### Universality of the two δ-functors -/

/-- **The left derived functors of `colim` form a universal homological δ-functor.** -/
theorem derivedColimitDeltaFunctor_isUniversal :
    (derivedColimitDeltaFunctor.{u, v} (C := C)).IsUniversal := by
  have := presheafEnoughProjectives.{u, v} C
  exact HomologicalDeltaFunctor.isUniversal_of_isZero_projective _
    fun n P _ => Functor.isZero_leftDerived_obj_projective_succ _ n P

/-- **The homology δ-functor of the simplicial replacement is universal as soon as every presheaf
admits an acyclic epimorphic cover**, that is an epimorphism from a presheaf whose replacement
has vanishing homology in degree `n + 1`. -/
theorem replacementHomologyDeltaFunctor_isUniversal_of_acyclicCover
    (h : ∀ (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ),
      ∃ (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (π : P ⟶ X), Epi π ∧
        IsZero ((simplicialReplacementComplex P).homology (n + 1))) :
    (replacementHomologyDeltaFunctor.{u, v} (C := C)).IsUniversal :=
  have := HomologicalDeltaFunctor.Coeffaceable.of_exists_epi_isZero
    (replacementHomologyDeltaFunctor.{u, v} (C := C)) h
  HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

/-- **The homology δ-functor of the simplicial replacement is universal.** -/
theorem replacementHomologyDeltaFunctor_isUniversal :
    (replacementHomologyDeltaFunctor.{u, v} (C := C)).IsUniversal :=
  replacementHomologyDeltaFunctor_isUniversal_of_acyclicCover.{u, v}
    exists_acyclic_epi_of_presheaf

/-! ### The comparison -/

/-- The isomorphism of homological δ-functors between the left derived functors of `colim_{Cᵒᵖ}`
and the homology of the simplicial replacement extending the degree-zero comparison
`Stacks.CategoryHomology.derivedColimitZeroComparison`. -/
def derivedColimitReplacementDeltaIso :
    derivedColimitDeltaFunctor.{u, v} (C := C) ≅ replacementHomologyDeltaFunctor.{u, v} (C := C) :=
  have := derivedColimitDeltaFunctor_isUniversal.{u, v} (C := C)
  have := replacementHomologyDeltaFunctor_isUniversal.{u, v} (C := C)
  HomologicalDeltaFunctor.IsUniversal.isoOfIso (derivedColimitZeroComparison.{u, v} (C := C))

/-- The `n`th left derived functor of `colim_{Cᵒᵖ}` is the `n`th homology of the simplicial
replacement, as an isomorphism of functors. -/
def categoryHomologyReplacementNatIso (n : ℕ) :
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerived n ≅
      replacementComplexFunctor (C := C) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.down ℕ) n :=
  HomologicalDeltaFunctor.isoApp (derivedColimitReplacementDeltaIso.{u, v} (C := C)) n

/-- The homology of the simplicial replacement complex of an abelian-group-valued presheaf
computes the left derived functors of the colimit, that is the homology groups `H_n(C, F)`: the
component at `F` of `Stacks.CategoryHomology.categoryHomologyReplacementNatIso`. -/
@[stacks 08PG "derived_colimits"]
def categoryHomologyReplacementIso (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    categoryHomology.{u, v} F n ≅ (simplicialReplacementComplex F).homology n :=
  (categoryHomologyReplacementNatIso.{u, v} (C := C) n).app F

/-- **The comparison `categoryHomologyReplacementIso` is natural in the presheaf.** -/
theorem categoryHomologyReplacementIso_naturality {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (η : F ⟶ G) (n : ℕ) :
    ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerived n).map η ≫
        (categoryHomologyReplacementIso.{u, v} (C := C) G n).hom =
      (categoryHomologyReplacementIso.{u, v} (C := C) F n).hom ≫
        HomologicalComplex.homologyMap ((replacementComplexFunctor (C := C)).map η) n :=
  (categoryHomologyReplacementNatIso.{u, v} (C := C) n).hom.naturality η

/-- In degree zero the comparison `categoryHomologyReplacementIso` is the composite of the right
exactness of `colim` with the cokernel presentation of `H_0(K_•(F))`. -/
@[simp]
theorem categoryHomologyReplacementIso_zero (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (categoryHomologyReplacementIso.{u, v} (C := C) F 0).hom =
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).fromLeftDerivedZero.app F ≫
        (replacementHomologyZeroIsoColimit F).inv := by
  have := derivedColimitDeltaFunctor_isUniversal.{u, v} (C := C)
  have := replacementHomologyDeltaFunctor_isUniversal.{u, v} (C := C)
  exact congrArg (fun α => NatTrans.app α F)
    (HomologicalDeltaFunctor.IsUniversal.isoOfIso_hom_app_zero
      (derivedColimitZeroComparison.{u, v} (C := C)))

end Stacks.CategoryHomology

end
