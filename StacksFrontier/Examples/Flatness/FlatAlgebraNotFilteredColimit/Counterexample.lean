module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Basic.Countable.Defs
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Set.Countable
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.OfPrime
public import Mathlib.RingTheory.Trace.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import StacksFrontier.Examples.Flatness.FlatAlgebraNotFilteredColimit.ColimitObstruction
public import StacksFrontier.Examples.Flatness.FlatAlgebraNotFilteredColimit.FerrandRaynaud

/-!
# A flat algebra which is not a filtered colimit of finitely presented flat algebras

The main results of `StacksFrontier.Examples.Flatness.FlatAlgebraNotFilteredColimit`.

## Main results

* `Stacks.Examples.exists_flat_algebra_not_filteredColimit_finitePresentation_flat`: a
  commutative ring carrying a flat algebra which is the colimit of no filtered diagram of
  finitely presented flat algebras.
* `Stacks.Examples.exists_charZero_local_flat_algebra_not_filteredColimit`: the same with the
  base ring a one-dimensional Noetherian local ring whose residue field has characteristic
  zero.
* `Stacks.Examples.isEmpty_isColimit_of_isEmpty_hom_finite_free`: over a Henselian local ring,
  a faithfully flat algebra receiving a finitely presented algebra with no map to a nonzero
  finite free algebra is the colimit of no filtered diagram of finitely presented flat
  algebras.

## References

* [Stacks Project, Tag 0ATF](https://stacks.math.columbia.edu/tag/0ATF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Examples.FlatAlgebraNotFilteredColimit

open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin
open scoped RatFunc LaurentSeries

/-- Forgetting a commutative algebra preserves small filtered colimits. -/
private lemma preservesColimitsOfShape_forget_commAlgCat
    (R : Type u) [CommRing R] (J : Type v) [SmallCategory J] [IsFiltered J] [UnivLE.{v, u}] :
    PreservesColimitsOfShape J (forget (CommAlgCat.{u} R)) := by
  have := preservesColimitsOfShape_forget_commRingCat.{u, v} J
  have : IsConnected J := IsFiltered.isConnected J
  have := preservesColimitsOfShape_forget₂_commAlgCat R J
  show PreservesColimitsOfShape J
    (forget₂ (CommAlgCat.{u} R) CommRingCat.{u} ⋙ forget CommRingCat.{u})
  infer_instance

/-- A finitely presented algebra which admits no map to a nonzero finite free algebra
obstructs the approximation of any faithfully flat algebra receiving it, over a Henselian
local base. -/
private lemma isEmpty_isColimit_of_isEmpty_hom_finite_free_of_preservesColimit
    {A : Type u} [CommRing A] [HenselianLocalRing A] {S B : CommAlgCat.{u} A}
    [Algebra.FinitePresentation A S] [Module.FaithfullyFlat A B] (g : S ⟶ B)
    (hS : ∀ T : CommAlgCat.{u} A, Module.Free A T → Module.Finite A T → Nontrivial T →
      IsEmpty (S ⟶ T))
    {J : Type v} [SmallCategory J] [IsFiltered J]
    [PreservesColimitsOfShape J (forget CommRingCat.{u})]
    (F : J ⥤ CommAlgCat.{u} A)
    (hF : ∀ j, Algebra.FinitePresentation A (F.obj j) ∧ Module.Flat A (F.obj j))
    (c : Cocone F) (hpt : c.pt = B) : IsEmpty (IsColimit c) := by
  subst hpt
  refine ⟨fun hc => ?_⟩
  obtain ⟨i, ⟨h⟩⟩ := exists_stage_hom_of_finitePresentation F hc S g
  obtain ⟨_, _⟩ := hF i
  have : Module.FaithfullyFlat A (F.obj i) :=
    faithfullyFlat_stage_of_faithfullyFlat_cocone F c c.pt rfl i
  obtain ⟨T, hfree, hfin, hne, ⟨k⟩⟩ :=
    exists_finite_free_factor_of_faithfullyFlat_finitePresentation (R := A) (S := F.obj i)
  exact (hS T hfree hfin hne).false (h ≫ k)

end Stacks.Examples.FlatAlgebraNotFilteredColimit

namespace Stacks.Examples

open FlatAlgebraNotFilteredColimit

/-- The characteristic-zero alternative of Stacks 0ATF: there is a one-dimensional
Noetherian local ring whose residue field has characteristic zero carrying a flat algebra
which is the colimit of no filtered diagram of finitely presented flat algebras. -/
theorem exists_charZero_local_flat_algebra_not_filteredColimit :
    ∃ A : CommRingCat.{max u v}, ∃ hloc : IsLocalRing A,
      letI : IsLocalRing A := hloc
      IsNoetherianRing A ∧ ringKrullDim A = 1 ∧
        CharZero (IsLocalRing.ResidueField A) ∧
          ∃ B : CommAlgCat.{max u v} A, Module.Flat A B ∧
            ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
              (F : J ⥤ CommAlgCat.{max u v} A),
              (∀ j, Algebra.FinitePresentation A (F.obj j) ∧
                Module.Flat A (F.obj j)) →
                ∀ c : Cocone F, c.pt = B → IsEmpty (IsColimit c) := by
  obtain ⟨A, hloc, hnoeth, hdim, hchar, B, hflat, hB⟩ :=
    exists_charZero_local_example_of_preservesColimit.{max u v, v}
  refine ⟨A, hloc, hnoeth, hdim, hchar, B, hflat, ?_⟩
  intro J _ _ F hF c hpt
  have := preservesColimitsOfShape_forget_commAlgCat A J
  exact hB J F hF c hpt

/-- Over a Henselian local ring, a faithfully flat algebra receiving a finitely presented
algebra which admits no map to a nonzero finite free algebra is the colimit of no filtered
diagram of finitely presented flat algebras. -/
theorem isEmpty_isColimit_of_isEmpty_hom_finite_free
    {A : Type max u v} [CommRing A] [HenselianLocalRing A]
    {S B : CommAlgCat.{max u v} A} [Algebra.FinitePresentation A S]
    [Module.FaithfullyFlat A B] (g : S ⟶ B)
    (hS : ∀ T : CommAlgCat.{max u v} A, Module.Free A T → Module.Finite A T →
      Nontrivial T → IsEmpty (S ⟶ T)) :
    ∀ (J : Type v) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommAlgCat.{max u v} A),
      (∀ j, Algebra.FinitePresentation A (F.obj j) ∧ Module.Flat A (F.obj j)) →
        ∀ c : Cocone F, c.pt = B → IsEmpty (IsColimit c) := by
  intro J _ _ F hF c hpt
  have : PreservesColimitsOfShape J (forget CommRingCat.{max u v}) :=
    preservesColimitsOfShape_forget_commRingCat.{max u v, v} J
  exact isEmpty_isColimit_of_isEmpty_hom_finite_free_of_preservesColimit g hS F hF c hpt

/-- There is a commutative ring together with a flat algebra over it which is the colimit of
no filtered diagram of finitely presented flat algebras. -/
theorem exists_flat_algebra_not_filteredColimit_finitePresentation_flat :
    ∃ (A : CommRingCat.{max u v}) (B : CommAlgCat.{max u v} A), Module.Flat A B ∧
      ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
        (F : J ⥤ CommAlgCat.{max u v} A),
        (∀ j, Algebra.FinitePresentation A (F.obj j) ∧ Module.Flat A (F.obj j)) →
          ∀ c : Cocone F, c.pt = B → IsEmpty (IsColimit c) := by
  obtain ⟨A, _, _, _, _, B, hflat, hB⟩ :=
    exists_charZero_local_flat_algebra_not_filteredColimit.{u, v}
  exact ⟨A, B, hflat, hB⟩

end Stacks.Examples

end
