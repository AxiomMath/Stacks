module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.LocalCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationQuasicoherentOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteFiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# Coherence on a locally Noetherian algebraic space, read on the equi-universe model

On a locally Noetherian algebraic space `F` an `𝒪_F`-module is coherent (Stacks 07UA) if and
only if it is of finite presentation in the sense of Mathlib's
`SheafOfModules.IsFinitePresentation` (Stacks 07UB, (1) ⇔ (3)), and finite presentation is
invariant under the transport to the equi-universe model of the small étale ringed site. So
`D_Coh(𝒪_F)` corresponds to the objects of the derived category of the model whose cohomology
sheaves are of finite presentation (`AlgebraicGeometry.RingedSite.coherentDerived`).

## Main results

* `AlgebraicGeometry.Space.isCoherent_iff_isFinitePresentation`.
* `AlgebraicGeometry.Space.isFinitePresentation_modulesEquivModelModules_iff`.
* `AlgebraicGeometry.Space.coherentDerived_iff_model`: `D_Coh(𝒪_F)` read on the model.

## References

* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks.SheafOfModules

variable {C : Type*} [Category C] {C' : Type*} [Category C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{u})

/-- The second triangle identity of the structure maps of `reindexEquivalence`. -/
theorem reindexBackSharp_triangle :
    ((𝟙 (reindexRing J' e R) : reindexRing J' e R ⟶ reindexRing J' e R)).hom ≫
      e.functor.op.whiskerLeft (reindexBackSharp (J' := J') e R).hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) (reindexRing J' e R).obj = 𝟙 _ := by
  ext A : 2
  show 𝟙 _ ≫ R.obj.map _ ≫ R.obj.map _ = 𝟙 _
  rw [Category.id_comp, ← R.obj.map_comp, ← R.obj.map_id]
  congr 1
  simp [← op_comp]

/-- The structure map of the inverse transport is invertible. -/
instance isIso_reindexBackSharp : IsIso (reindexBackSharp (J' := J') e R) := by
  haveI : IsIso ((sheafToPresheaf _ _).map (reindexBackSharp (J' := J') e R)) :=
    (Functor.isoWhiskerRight (NatIso.op e.counitIso) R.obj).isIso_hom
  exact isIso_of_fully_faithful (sheafToPresheaf _ _) _

/-- **Finite presentation is invariant under `reindexEquivalence`.** -/
theorem isFinitePresentation_reindexEquivalence_functor_obj_iff
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X : C', HasSheafify (J'.over X) AddCommGrpCat.{u}]
    [∀ X : C', (J'.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [e.functor.IsDenseSubsite J' J] [e.inverse.IsDenseSubsite J J'] [HasPullbacks C]
    [HasPullbacks C'] (M : SheafOfModules.{u} R) :
    ((reindexEquivalence (J' := J') e R).functor.obj M).IsFinitePresentation ↔
      M.IsFinitePresentation :=
  ModelFinitePresentation.isFinitePresentation_pushforward_iff_of_equivalence e (𝟙 _)
    (reindexBackSharp e R) (by rfl) (reindexBackSharp_triangle (J' := J') e R) M

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (hN : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T))

include hN in
/-- **Stacks 07UB, (1) ⇔ (3), in Mathlib's spelling of finite presentation**: on a locally
Noetherian algebraic space an `𝒪_F`-module is coherent if and only if it is of finite
presentation. -/
theorem isCoherent_iff_isFinitePresentation (M : Modules.{u, u} B S hS F hF) :
    IsCoherent B S hS F hF M ↔ M.IsFinitePresentation := by
  have : Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hN⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' M
      ((isCoherent_iff_isFinitePresentationOnSite B S hS F hF M).1 h)
  · exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS F hF M).2
      ⟨Stacks.SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentation M,
        Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType M inferInstance⟩

/-- **Finite presentation is invariant under the transport to the equi-universe model.** -/
theorem isFinitePresentation_modulesEquivModelModules_iff (M : Modules.{u, u} B S hS F hF) :
    ((modulesEquivModelModules B S hS F hF).functor.obj M).IsFinitePresentation ↔
      M.IsFinitePresentation := by
  have : (smallEtaleModelEquivalence B S hS F).inverse.IsDenseSubsite
      (smallEtaleRingedSite B S hS F hF).J (smallEtaleModelTopology B S hS F) :=
    smallEtaleModelEquivalence_inverse_isDenseSubsite B S hS F
  have : HasPullbacks (smallEtaleRingedSite B S hS F hF).C := SmallEtale.instHasPullbacks B S hS F
  have : (smallEtaleModelEquivalence B S hS F).functor.IsDenseSubsite
      (smallEtaleModelTopology B S hS F) (smallEtaleRingedSite B S hS F hF).J :=
    smallEtaleModelEquivalence_functor_isDenseSubsite B S hS F
  exact Stacks.SheafOfModules.isFinitePresentation_reindexEquivalence_functor_obj_iff
    (J := (smallEtaleRingedSite B S hS F hF).J) (J' := smallEtaleModelTopology B S hS F)
    (smallEtaleModelEquivalence B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) M

/-- The cohomology sheaves of the transport of an object of `D(𝒪_F)` to the model are the
transports of its cohomology sheaves. -/
def modelDerivedHomologyIso (n : ℤ) (L : DerivedModules B S hS F hF) :
    (RingedSite.stdHomology (smallEtaleModelRingedSite B S hS F hF) n).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj L) ≅
      (modulesEquivModelModules B S hS F hF).functor.obj ((derivedHomology B S hS F hF n).obj L) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  letI := HasDerivedCategory.standard (ModelModules B S hS F hF)
  letI := additive_modulesEquivModelModules_functor B S hS F hF
  (((modulesEquivModelModules B S hS F hF).functor.mapDerivedCategoryHomologyIso n).app L)

include hN in
/-- **`D_Coh(𝒪_F)` read on the model**: an object of `D(𝒪_F)` has coherent cohomology sheaves
if and only if its transport to the equi-universe model has cohomology sheaves of finite
presentation. -/
theorem coherentDerived_iff_model (L : DerivedModules B S hS F hF) :
    coherentDerived B S hS F hF L ↔
      RingedSite.coherentDerived (smallEtaleModelRingedSite B S hS F hF)
        ((modelDerivedEquivalence B S hS F hF).functor.obj L) := by
  refine forall_congr' fun n => ?_
  rw [isCoherent_iff_isFinitePresentation B S hS F hF hN,
    ← isFinitePresentation_modulesEquivModelModules_iff B S hS F hF]
  exact ⟨fun h => Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      (modelDerivedHomologyIso B S hS F hF n L).symm h,
    fun h => Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      (modelDerivedHomologyIso B S hS F hF n L) h⟩

end AlgebraicGeometry.Space

end
