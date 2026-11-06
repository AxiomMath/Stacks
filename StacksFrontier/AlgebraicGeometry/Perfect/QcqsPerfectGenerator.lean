module

public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundedAboveGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsPerfectIsCompact
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
import StacksCore.Tactic.StacksAttribute

/-!
# A perfect generator of `D_QCoh(𝒪_X)` for a quasi-compact quasi-separated scheme

Let `X` be a quasi-compact and quasi-separated scheme. Then `D_QCoh(𝒪_X)` has a perfect generator
([Stacks, Tag 09IS]): a perfect object `G` of `D(𝒪_X)` such that an object of `D_QCoh(𝒪_X)`
receiving no nonzero morphism from any shift of `G` is zero.

## The proof

The induction over a finite affine cover of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCompactGeneration.lean` produces a
*finite* family of compact generators of `D_QCoh(𝒪_X)`
(`Stacks.Duality.QcqsGeneration.exists_finite_compact_generators`): the affine case has a single
generator and each inductive step adds one. Each of them is perfect, by the implication
*compact ⟹ perfect* of [Stacks, Tag 09M1] proved here: restriction to an affine open preserves
compactness because its right adjoint commutes with direct sums ([Stacks, Tag 08DZ]), compact
objects on an affine scheme are perfect, and perfectness is local ([Stacks, Tag 08CN]). The direct
sum of the family is then a single perfect generator.

## Main results

* `Stacks.Duality.QcqsPerfect.isPerfect_of_isCompactObject_of_qcqs` — a compact object of
  `D_QCoh(𝒪_X)` is perfect, for `X` quasi-compact and quasi-separated.
* `Stacks.Duality.QcqsPerfect.exists_finite_perfect_generators` — finitely many perfect objects
  jointly generating `D_QCoh(𝒪_X)`, at the locally small model.
* `Stacks.SheafOfModules.exists_isPerfect_generator_modules` — a single perfect generator, at the
  standard model and in the `X.Modules` spelling.
* `Stacks.SheafOfModules.exists_isPerfect_generator` — **[Stacks, Tag 09IS]**, in the spelling of
  the generator hypotheses of Stacks 0GEN (`DetectingBoundedAboveGenerator.lean`).

## Implementation notes

Compactness is meaningful only at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, where direct sums indexed by the morphism
universe exist; the generator is consumed at `CategoryTheory.HasDerivedCategory.standard`. It is
carried across by the comparison equivalence `StacksDraft.DerivedModel.modelEquiv`, which commutes
with the shift (`StacksDraft.Perfect.derivedEquivalenceCommShift`); perfectness and
quasi-coherence of cohomology, both conditions on a representing complex, are carried by
`StacksDraft.DerivedModel.modelCompQIso`.

## References

* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry
open TopologicalSpace CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality.QcqsPerfect

open Stacks.Duality.OpenImmersion Stacks.Duality.QcqsGeneration

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- Perfectness at the standard model is local over the open subschemes of `X`. -/
private theorem isPerfect_q_of_restrict {X : Scheme.{u}} (C : CochainComplex X.Modules ℤ)
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := V.toScheme.toRingedSpace)
        ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj (DerivedCategory.Q.obj C))) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace)
      (DerivedCategory.Q.obj C) := by
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect
    (X := X.toRingedSpace) _ fun x => ?_
  obtain ⟨V, hx, hV⟩ := h x
  exact ⟨V, hx, Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (X := V.toScheme.toRingedSpace)
    ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor X V).app _).symm hV⟩

/-- Perfectness at the standard model passes from the restriction along `Spec Γ(X, V) ⟶ X` to the
restriction along `V ⟶ X`, for an affine open `V`. -/
private theorem isPerfect_restrict_of_fromSpec {X : Scheme.{u}} (C : CochainComplex X.Modules ℤ)
    {V : X.Opens} (hV : IsAffineOpen V)
    (h : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := (Spec Γ(X, V)).toRingedSpace)
      (DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor hV.fromSpec).mapHomologicalComplex _).obj C))) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := V.toScheme.toRingedSpace)
      ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj (DerivedCategory.Q.obj C)) := by
  have h' := Stacks.DerivedQCoh.isPerfect_derivedRestrict_of_isOpenImmersion_of_model
    hV.isoSpec.hom _ h
  have hcomp : hV.isoSpec.hom ≫ hV.fromSpec = V.ι := by
    rw [← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (X := V.toScheme.toRingedSpace) ?_ h'
  exact (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.mapIso
      ((Scheme.Modules.restrictFunctor hV.fromSpec).mapDerivedCategoryFactors.app C).symm ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso
      (Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).symm).app _ ≪≫
    (Functor.mapDerivedCategoryCongr (Scheme.Modules.restrictFunctorCongr hcomp)).app _

end Standard

/-- **[Stacks, Tag 09M1], the implication *compact ⟹ perfect*, on a quasi-compact quasi-separated
scheme.** Let `X` be a quasi-compact quasi-separated scheme and let `K` be a compact object of
`D_QCoh(𝒪_X)`, the direct sums being indexed by types of the universe of `X`. Then `K` is a perfect
object of `D(𝒪_X)`.

For an affine open `V` of `X`, restriction along `Spec Γ(X, V) ⟶ X` has a right adjoint `Rj_*`
commuting with direct sums ([Stacks, Tag 08DZ]), so it preserves compactness; on the affine scheme
`Spec Γ(X, V)` compact objects are perfect (the affine case of [Stacks, Tag 09M1]); so `K` is
perfect on every affine open, and perfectness is local ([Stacks, Tag 08CN]). The derived category
is the locally small `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`; perfectness, a
condition on a representing complex, is carried to and from the standard model, where locality is
available. -/
theorem isPerfect_of_isCompactObject_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hK : IsCompactObject.{u} K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj := by
  obtain ⟨C, ⟨eC⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q K.obj
  refine (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model _ _ (by exact Iso.refl _)
    eC).1 (isPerfect_q_of_restrict C fun x => ?_)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  refine ⟨V, hxV, isPerfect_restrict_of_fromSpec C hV ?_⟩
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward hV.fromSpec
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs hV.fromSpec)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward hV.fromSpec
  let adj := restrictedDerivedRestrictAdjunction hV.fromSpec
  have : (Stacks.Duality.quasiCoherentDerivedPushforward hV.fromSpec
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs hV.fromSpec)).Additive :=
    adj.right_adjoint_additive
  have hc : IsCompactObject.{u} ((restrictedDerivedRestrict hV.fromSpec).obj K) :=
    isCompactObject_map_of_adjunction adj hK
  have hp := (AlgebraicGeometry.isCompactObject_iff_isPerfect_spec_of_model Γ(X, V) _).1 hc
  have hp' : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec Γ(X, V)).toRingedSpace)
      (DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor hV.fromSpec).mapHomologicalComplex _).obj C)) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (Spec Γ(X, V)).toRingedSpace)
      ((restrictedDerivedRestrictCompιIso hV.fromSpec).app K ≪≫
        (derivedRestrict hV.fromSpec).mapIso eC.symm ≪≫
        ((Scheme.Modules.restrictFunctor hV.fromSpec).mapDerivedCategoryFactors.app C)) hp
  exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model _ _ (by exact Iso.refl _)
    (by exact Iso.refl _)).1 hp'

/-! ### A finite family of perfect generators, at the locally small model -/

/-- **A finite family of perfect compact generators of `D_QCoh(𝒪_X)`**, at the locally small model:
for `X` quasi-compact and quasi-separated, finitely many objects of `D(𝒪_X)`, each perfect, such
that an object of `D(𝒪_X)` with quasi-coherent cohomology receiving no nonzero morphism from any
shift of any of them is zero. The family is that of
`Stacks.Duality.QcqsGeneration.exists_finite_compact_generators`, perfect by
`Stacks.Duality.QcqsPerfect.isPerfect_of_isCompactObject_of_qcqs`. -/
theorem exists_finite_perfect_generators (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (E : ι → DerivedCategory X.Modules),
      (∀ i, Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (E i)) ∧
      ∀ K : DerivedCategory X.Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) →
        (∀ (i : ι) (n : ℤ) (g : (E i)⟦n⟧ ⟶ K), g = 0) → IsZero K := by
  obtain ⟨ι, hι, E, hEc, hEgen⟩ := Stacks.Duality.QcqsGeneration.exists_finite_compact_generators X
  refine ⟨ι, hι, fun i => (E i).obj, fun i => isPerfect_of_isCompactObject_of_qcqs X (E i) (hEc i),
    fun K hK hKE => ?_⟩
  let ιQ := (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι
  let K' : Stacks.Duality.quasiCoherentDerivedCategory X := ⟨K, hK⟩
  have hz : IsZero K' := by
    refine hEgen _ ?_
    rw [rightOrthogonal_shiftClosure_ofObj_iff]
    intro i n g
    apply ιQ.map_injective
    rw [Functor.map_zero, ← cancel_epi ((ιQ.commShiftIso n).inv.app (E i)), comp_zero]
    exact hKE i n _
  exact ιQ.map_isZero hz

end Stacks.Duality.QcqsPerfect

/-! ### A single perfect generator, at the standard model -/

namespace Stacks.SheafOfModules

open StacksDraft.DerivedModel

section Generator

attribute [local instance 10000] HasDerivedCategory.standard

/-- A morphism out of a shift of a summand vanishes if every morphism out of the same shift of
the biproduct does. -/
theorem eq_zero_of_shift_biproduct_ι {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasShift C ℤ] {ι : Type*} (F : ι → C) [HasBiproduct F] {K : C} (n : ℤ)
    (h : ∀ f : (⨁ F)⟦n⟧ ⟶ K, f = 0) (i : ι) (g : (F i)⟦n⟧ ⟶ K) : g = 0 :=
  calc g = ((shiftFunctor C n).map (biproduct.ι F i) ≫
        (shiftFunctor C n).map (biproduct.π F i)) ≫ g := by
        rw [← Functor.map_comp, biproduct.ι_π_self, CategoryTheory.Functor.map_id,
          Category.id_comp]
    _ = 0 := by rw [Category.assoc, h ((shiftFunctor C n).map (biproduct.π F i) ≫ g), comp_zero]

/-- **A perfect generator of `D_QCoh(𝒪_X)`, in the `X.Modules` spelling.** For `X` quasi-compact
and quasi-separated there is a perfect object `G` of `D(𝒪_X)` such that an object of `D(𝒪_X)`
with quasi-coherent cohomology receiving no nonzero morphism from any shift of `G` is zero.

`G` is the direct sum of the finite family of perfect generators of
`Stacks.Duality.QcqsPerfect.exists_finite_perfect_generators`, carried from the locally small
model to the standard one by `StacksDraft.DerivedModel.modelEquiv`; perfect objects are closed
under finite direct sums. -/
theorem exists_isPerfect_generator_modules (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ G : DerivedCategory X.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) G ∧
      ∀ K : DerivedCategory X.Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K := by
  obtain ⟨ι, hι, E, hEp, hEgen⟩ := Stacks.Duality.QcqsPerfect.exists_finite_perfect_generators X
  let := Fintype.ofFinite ι
  let e := modelEquiv (Scheme.Modules.hasDerivedCategory X) (HasDerivedCategory.standard X.Modules)
  let : e.functor.CommShift ℤ := StacksDraft.Perfect.derivedEquivalenceCommShift _ _
  let F : ι → DerivedCategory X.Modules := fun i => e.functor.obj (E i)
  have hF : ∀ i, Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := X.toRingedSpace) (F i) := fun i => by
    obtain ⟨C, ⟨eC⟩⟩ :=
      Functor.EssSurj.mem_essImage
        (@DerivedCategory.Q _ _ _ (Scheme.Modules.hasDerivedCategory X)) (E i)
    have e₂ : DerivedCategory.Q.obj C ≅ F i :=
      ((modelCompQIso (Scheme.Modules.hasDerivedCategory X)
        (HasDerivedCategory.standard X.Modules)).app C).symm ≪≫ e.functor.mapIso eC
    exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model _ _ (by exact eC)
      (by exact e₂)).1 (hEp i)
  let P : ObjectProperty (DerivedCategory X.Modules) := fun K =>
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) K
  have : P.IsTriangulated :=
    Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect X.toRingedSpace
  have : P.IsClosedUnderIsomorphisms :=
    Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect.{u, u, u + 1}
  refine ⟨⨁ F, P.prop_of_isLimit_fan (biproduct.isLimit F) hF, fun K hK hKG => ?_⟩
  obtain ⟨C, ⟨eK⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q K
  have eK' : e.inverse.obj K ≅
      (@DerivedCategory.Q _ _ _ (Scheme.Modules.hasDerivedCategory X)).obj C :=
    e.inverse.mapIso eK.symm ≪≫ (modelInverseCompQIso (Scheme.Modules.hasDerivedCategory X)
      (HasDerivedCategory.standard _)).app C
  have hK' : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor _ _ _
      (Scheme.Modules.hasDerivedCategory X) i).obj (e.inverse.obj K)).IsQuasicoherent := fun i =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor X.Modules i).mapIso eK.symm ≪≫
        (DerivedCategory.homologyFunctorFactors X.Modules i).app C ≪≫
        ((@DerivedCategory.homologyFunctorFactors _ _ _
          (Scheme.Modules.hasDerivedCategory X) i).app C).symm ≪≫
        (@DerivedCategory.homologyFunctor _ _ _
          (Scheme.Modules.hasDerivedCategory X) i).mapIso eK'.symm) (hK i)
  have hz := hEgen (e.inverse.obj K) hK' fun i n g => by
    apply e.functor.map_injective
    rw [Functor.map_zero, ← cancel_epi ((e.functor.commShiftIso n).inv.app (E i)),
      ← cancel_mono (e.counitIso.hom.app K), comp_zero, zero_comp]
    simpa only [Category.assoc] using eq_zero_of_shift_biproduct_ι F n (hKG n) i
      ((e.functor.commShiftIso n).inv.app (E i) ≫ e.functor.map g ≫ e.counitIso.hom.app K)
  exact (e.functor.map_isZero hz).of_iso (e.counitIso.app K).symm

/-- **[Stacks, Tag 09IS].** Let `X` be a quasi-compact and quasi-separated scheme. Then
`D_QCoh(𝒪_X)` has a perfect generator: there is a perfect object `G` of `D(𝒪_X)` such that every
object `K` of `D(𝒪_X)` with quasi-coherent cohomology sheaves which receives no nonzero morphism
from any shift `G⟦n⟧` is zero.

This is `Stacks.SheafOfModules.exists_isPerfect_generator_modules` read in the spelling
`StructureSheafModules X.sheaf` with perfectness for the ringed site of opens, the spelling of the
generator hypotheses of Stacks 0GEN in `DetectingBoundedAboveGenerator`; the two notions of
perfectness agree by `Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect`.

The proof is the source's: induction over a finite affine cover produces finitely many compact
generators of `D_QCoh(𝒪_X)` (`Stacks.Duality.QcqsGeneration.exists_finite_compact_generators`),
compact objects of `D_QCoh(𝒪_X)` are perfect
(`Stacks.Duality.QcqsPerfect.isPerfect_of_isCompactObject_of_qcqs`), and their direct sum is a
single perfect generator. -/
@[stacks 09IS]
theorem exists_isPerfect_generator {X : Scheme.{u}}
    [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X) :
    ∃ G : DerivedCategory (StructureSheafModules X.sheaf), (ringedSite X.sheaf).IsPerfect G ∧
      ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
          K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K := by
  obtain ⟨G, hG, hgen⟩ := exists_isPerfect_generator_modules X
  exact ⟨G,
    Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace G hG, hgen⟩

end Generator

end Stacks.SheafOfModules

end
