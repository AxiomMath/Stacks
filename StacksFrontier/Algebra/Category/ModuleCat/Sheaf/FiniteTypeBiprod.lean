module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.LocalGeneration

/-!
# The direct sum of two sheaves of modules of finite type

Let `R` be a sheaf of rings on a site.  The direct sum of two sheaves of `R`-modules of finite
type is of finite type: the two covering families carrying finite generating families are refined
against each other, and on a member of the refinement the two restricted generating families
together generate the restriction of the direct sum, restriction to a slice preserving the
binary product.

## Main results

* `Stacks.SheafOfModules.overFunctor_preservesLimit_pair`: restriction to a slice of the site
  preserves a binary product of sheaves of modules.
* `Stacks.SheafOfModules.isFiniteType_biprod`: the direct sum of two sheaves of modules of finite
  type is of finite type.

## Implementation notes

The argument is the one of the `private` lemma of the same name in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeQuasicoherentSubobjects.lean`, which is not
accessible outside that file; it is stated here for every consumer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules

section Biprod

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restriction to a slice of the site preserves a binary product of sheaves of modules: it is
computed sectionwise, and the inclusion of sheaves of modules into presheaves of modules
reflects limits. -/
theorem overFunctor_preservesLimit_pair {M N : SheafOfModules.{u} R} (U : C) :
    PreservesLimit (pair M N) (SheafOfModules.overFunctor R U) := by
  refine ⟨fun {c} hc => ⟨isLimitOfReflects (SheafOfModules.forget (R.over U)) ?_⟩⟩
  refine PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun V => ?_
  let V' : Cᵒᵖ := Opposite.op ((Over.forget U).obj V.unop)
  change IsLimit ((ModuleCat.restrictScalars (RingHom.id ((R.obj).obj V'))).mapCone
    ((SheafOfModules.evaluation R V').mapCone c))
  exact isLimitOfPreserves _ (isLimitOfPreserves (SheafOfModules.evaluation R V') hc)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The direct sum of two sheaves of modules of finite type is of finite type.

The two covering families are refined against each other: an object of the refinement comes
with a morphism to a member of each, along which both generating families restrict, and the
sum of the two restricted families generates the direct sum because restriction to a slice
preserves it. -/
theorem isFiniteType_biprod {M N : SheafOfModules.{u} R} [HasBinaryBiproduct M N]
    [M.IsFiniteType] [N.IsFiniteType] : (M ⊞ N).IsFiniteType := by
  classical
  obtain ⟨p, hp⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData N
  let I := Σ Z : C, Σ i : p.I, Σ j : q.I, (Z ⟶ p.X i) × (Z ⟶ q.X j)
  let W : I → C := fun ij => ij.1
  have hW : J.CoversTop W := by
    intro Z
    refine J.superset_covering ?_ (J.intersection_covering (p.coversTop Z) (q.coversTop Z))
    rintro T f ⟨hfM, hfN⟩
    obtain ⟨i, ⟨fM⟩⟩ := (Sieve.mem_ofObjects_iff p.X f).mp hfM
    obtain ⟨j, ⟨fN⟩⟩ := (Sieve.mem_ofObjects_iff q.X f).mp hfN
    exact (Sieve.mem_ofObjects_iff W f).mpr ⟨⟨T, i, j, fM, fN⟩, ⟨𝟙 T⟩⟩
  let genAt (ij : I) :
      {g : ((M ⊞ N).over (W ij)).GeneratingSections // g.IsFiniteType} := by
    rcases ij with ⟨Z, i, j, fM, fN⟩
    change {g : ((M ⊞ N).over Z).GeneratingSections // g.IsFiniteType}
    have : (p.generators i).IsFiniteType := hp.isFiniteType i
    have : (q.generators j).IsFiniteType := hq.isFiniteType j
    let sM := Stacks.SheafOfModules.generatingSectionsOverMap M fM (p.generators i)
    let sN := Stacks.SheafOfModules.generatingSectionsOverMap N fN (q.generators j)
    have : sM.IsFiniteType := ⟨inferInstanceAs (Finite (p.generators i).I)⟩
    have : sN.IsFiniteType := ⟨inferInstanceAs (Finite (q.generators j).I)⟩
    let Rw := R.over Z
    let E := SheafOfModules.overFunctor R Z
    have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
    have : PreservesLimit (pair M N) E := overFunctor_preservesLimit_pair Z
    have : PreservesBinaryBiproduct M N E :=
      preservesBinaryBiproduct_of_preservesBinaryProduct E
    let p0 : SheafOfModules.free (R := Rw) (Sum sM.I sN.I) ⟶ (M ⊞ N).over Z :=
      (SheafOfModules.freeSumIso (R := Rw) sM.I sN.I).inv ≫
        (biprod.isoCoprod _ _).inv ≫ biprod.map sM.π sN.π ≫ (E.mapBiprod M N).inv
    let τ : ((M ⊞ N).over Z).GeneratingSections :=
      { I := Sum sM.I sN.I
        s := ((M ⊞ N).over Z).freeHomEquiv p0
        epi := by
          rw [((M ⊞ N).over Z).freeHomEquiv.symm_apply_apply]
          infer_instance }
    exact ⟨τ, ⟨inferInstanceAs (Finite (Sum sM.I sN.I))⟩⟩
  exact ⟨⟨{ I := I, X := W, coversTop := hW, generators := fun ij => (genAt ij).val },
    ⟨fun ij => (genAt ij).property⟩⟩⟩

end Biprod

end Stacks.SheafOfModules

end
