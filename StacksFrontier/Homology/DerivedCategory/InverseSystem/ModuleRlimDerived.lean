module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.LeftResolution
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleKFlatComparison
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRepresentatives
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.KFlat.LargeUniverse

/-!
# K-flat representatives of derived inverse systems

Every object of the derived category of inverse systems of modules over an inverse system of
commutative rings is represented by a compatible system of complexes whose complex at every
index is K-flat.

## Main results

* `ModuleSystemKFlat.exists_representative_with_kFlat_components` gives a representative of a
  derived inverse system whose evaluated complex is K-flat at every index.

## Implementation notes

An inverse system of commutative rings is a functor `A : Functor ℕᵒᵖ CommRingCat`. Its underlying
ring-valued functor defines the category of compatible module systems. The representing system of
complexes is encoded as one complex in that category, and its component at an index is obtained by
applying the evaluation functor degreewise. The source indexes systems starting at one; index `n`
here represents source index `n + 1`.

The representative is produced in two steps: Stacks 091F gives a representative with surjective
transition maps, and the ladder of truncations of Stacks 05T7 (in the form of
`CochainComplex.exists_sequence_quasiIso_truncLE`) resolves it by a sequence of complexes which
are degreewise pointwise projective, hence degreewise pointwise flat; each stage is bounded
above so Stacks 064K applies, and the colimit of the ladder is K-flat by Stacks 06Y3.

## References

* [Stacks Project, Tag 091G](https://stacks.math.columbia.edu/tag/091G)
-/

open Stacks.HomologyColimit

namespace ModuleSystemKFlat

section Construction

open CategoryTheory Limits Opposite MonoidalCategory
open scoped ZeroObject

universe u

private abbrev Rsys (A : ℕᵒᵖ ⥤ CommRingCat.{u}) : ℕᵒᵖ ⥤ RingCat.{u} :=
  A ⋙ forget₂ CommRingCat RingCat

section HomologyColimit

universe v w

variable {A : Type v} [Category.{w} A] [Abelian A]

end HomologyColimit

private lemma pointwise_kFlat_resolution (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    (M : CochainComplex (PresheafOfModules.{u} (Rsys A)) ℤ) :
    ∃ (K : CochainComplex (PresheafOfModules.{u} (Rsys A)) ℤ)
      (f : K ⟶ M), QuasiIso f ∧
      ∀ n : ℕ, CochainComplex.KFlat
        (show CochainComplex (ModuleCat (A.obj (op n))) ℤ from
          ((PresheafOfModules.evaluation.{u} (Rsys A) (op n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) := by
  let P := ModuleSystemKFlatComparison.pointwiseProjective.{u, u} A
  have : P.ContainsZero := ModuleSystemKFlatComparison.zero_prop A
  obtain ⟨Q, q, g, hq, _, hle, hproj, _, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P
      (ModuleSystemKFlatComparison.projective_biprod A)
      (ModuleSystemKFlatComparison.free_cover A) M
  let D := Functor.ofSequence g
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  let s : Cocone D := Cocone.mk M
    (NatTrans.ofSequence (fun n => q n ≫ M.ιTruncLE (n : ℤ)) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  have : AB5OfSize.{0, 0, u, u + 1} AddCommGrpCat.{u} :=
    AB5OfSize_of_univLE.{0, 0, u, u} AddCommGrpCat.{u}
  have : HasExactColimitsOfShape ℕ (PresheafOfModules.{u} (Rsys A)) :=
    ⟨⟨fun K _ _ ↦ ⟨fun {F} ↦
      have : PreservesLimit F (colim (J := ℕ) ⋙ PresheafOfModules.toPresheaf (Rsys A)) :=
        preservesLimit_of_natIso _
          (preservesColimitNatIso (PresheafOfModules.toPresheaf (Rsys A))).symm
      preservesLimit_of_reflects_of_preserves _
        (PresheafOfModules.toPresheaf (Rsys A))⟩⟩⟩
  refine ⟨c.pt, hc.desc s,
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE
      q hq hc (hc.desc s) (hc.fac s), fun n => ?_⟩
  let E : CochainComplex (PresheafOfModules.{u} (Rsys A)) ℤ ⥤
      CochainComplex (ModuleCat (A.obj (op n))) ℤ :=
    (PresheafOfModules.evaluation.{u} (Rsys A) (op n)).mapHomologicalComplex
      (ComplexShape.up ℤ)
  have hkQ (j : ℕ) : (E.obj (Q j)).KFlat := by
    have : (E.obj (Q j)).IsStrictlyLE (j : ℤ) :=
      (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
        (PresheafOfModules.evaluation.{u} (Rsys A) (op n)).map_isZero
          ((CochainComplex.isStrictlyLE_iff (Q j) (j : ℤ)).mp (hle j) i hi)
    have (i : ℤ) : Module.Flat (A.obj (op n)) ((E.obj (Q j)).X i) := by
      show Module.Flat (A.obj (op n)) (((Q j).X i).obj (op n))
      have := hproj j i n
      have := (((Q j).X i).obj (op n)).projective_of_module_projective
      infer_instance
    exact CochainComplex.KFlat.kFlat_of_flat.{u, u} (E.obj (Q j)) j
  exact CochainComplex.KFlat.of_iso (preservesColimitIso E D).symm
    (CochainComplex.KFlat.kFlat_colimit.{u, 0, 0, u} (D ⋙ E) hkQ)

end Construction

section Main

open CategoryTheory Opposite

universe u w

/-- **Stacks 091G.** Every object of the derived category of inverse systems of modules over an
inverse system of commutative rings has a representative whose complex at every index is
K-flat. -/
@[stacks 091G]
public theorem exists_representative_with_kFlat_components
    {A : Functor ℕᵒᵖ CommRingCat.{u}}
    [HasDerivedCategory.{w}
      (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))]
    (K : DerivedCategory
      (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))) :
    ∃ (M : CochainComplex
        (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n : ℕ,
        CochainComplex.KFlat
          (show CochainComplex (ModuleCat (A.obj (op n))) ℤ from
            ((PresheafOfModules.evaluation
              (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M) := by
  obtain ⟨M, e, _⟩ :=
    ModuleSystemRepresentative.exists_representative_with_surjective_transition_maps
      (A := Rsys A) K
  obtain ⟨P, f, _, hflat⟩ := pointwise_kFlat_resolution A M
  exact ⟨P, asIso (DerivedCategory.Q.map f) ≪≫ e, hflat⟩

end Main

end ModuleSystemKFlat
