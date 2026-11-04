module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatSliceExtension
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.SequentialColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionByExtensionsByZero

/-!
# K-flat resolutions on a ringed site

Every cochain complex of sheaves of modules on a ringed site receives a termwise epimorphic
quasi-isomorphism from a K-flat complex whose terms are flat.

The resolution is the one of Stacks 077J: a sequential ladder of complexes resolving the upper
truncations of the given complex, whose terms are direct sums of extensions by zero of the
structure sheaves of the slice sites, together with a quasi-isomorphism from its colimit. Each
such direct sum is flat, because an extension by zero of a structure sheaf is flat (Stacks 03EV)
and flatness is stable under arbitrary direct sums (Stacks 05NG); each stage of the ladder is
bounded above with flat terms, hence K-flat (Stacks 06YQ); and K-flatness and flatness are both
stable under sequential colimits (Stacks 06YE, Stacks 05NG). Termwise surjectivity of the
augmentation comes from termwise surjectivity of each stage of the ladder, since in each fixed
degree the inclusion of a high enough upper truncation is an isomorphism.

## Main definitions

* `Stacks.Cohomology.kFlatResolution`: a chosen K-flat resolution complex.
* `Stacks.Cohomology.kFlatResolutionHom`: its augmentation to the given complex.

## Main results

* `Stacks.Cohomology.exists_kFlatResolution`: existence of the resolution.
* `Stacks.Cohomology.kFlatResolution_kFlat`, `Stacks.Cohomology.kFlatResolution_flat`,
  `Stacks.Cohomology.kFlatResolutionHom_quasiIso` and
  `Stacks.Cohomology.kFlatResolutionHom_epi`: the four properties of the chosen resolution.

## Implementation notes

Surjectivity of a morphism of sheaves of modules is expressed by `Epi` in every degree. The
exactness and tensor-product hypotheses are those under which flat sheaves of modules and
K-flat complexes are defined.

The site, its morphisms and the module universe are all taken to be the same universe. That is
the generality in which the resolution of Stacks 077J and the K-flatness criterion of Stacks
06YQ are available: Stacks 077J produces the ladder only for a ringed site whose three
universes agree, and Stacks 06YQ only when the structure rings and the modules live in one
universe. Everything else in the statement is as in the source.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace Stacks.Cohomology

universe u

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})

/-- A direct sum of extensions by zero of the structure sheaves of the slice sites is a flat
sheaf of modules. -/
theorem isFlat_of_isSumOfExtensionByZeroStructureSheaves
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hM : Stacks.SheafOfModules.IsSumOfExtensionByZeroStructureSheaves X M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) M := by
  classical
  obtain ⟨ι, U, ⟨e⟩⟩ := hM
  have hsum : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      (∐ fun i : ι =>
        (SheafOfModules.pullback.{u} (F := Over.forget (U i))
          (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over (U i)))).obj
            (SheafOfModules.unit
              (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over (U i)))) :=
    Stacks.SheafOfModules.FlatColimits.isFlat_coproduct (O := X.O) _
      (fun i => Stacks.Sites.OverModules.sheafExtensionUnit_isFlat X.J X.O (U i))
  exact (exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.mapIso e) hsum

variable
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O :
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
          SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive]
  [∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks Project, Tag 06YS.** A complex of sheaves of modules on a ringed site receives a
termwise epimorphic quasi-isomorphism from a K-flat complex whose terms are flat. -/
theorem exists_kFlatResolution
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (f : K ⟶ G),
      Stacks.SheafOfModules.IsKFlat X.O K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) ∧
      QuasiIso f ∧
      (∀ i : ℤ, Epi (f.f i)) := by
  classical
  obtain ⟨L⟩ := Stacks.SheafOfModules.exists_resolutionByDirectSumsExtensionsByZero X G
  refine ⟨colimit L.system, L.colimitComparison, ?_, ?_, L.colimit_quasiIso, ?_⟩
  · exact Stacks.SheafOfModules.kFlat_colimit _ _ fun n =>
      Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O (L.system.obj n) (L.boundedAbove n)
        fun i => isFlat_of_isSumOfExtensionByZeroStructureSheaves X _ (L.term_isSum n i)
  · intro i
    let ev : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
      HomologicalComplex.eval _ (ComplexShape.up ℤ) i
    let stages := L.system ⋙ ev
    let eEval : (colimit L.system).X i ≅ colimit stages := preservesColimitIso ev L.system
    let e := ULiftHomULiftCategory.equiv.{u, u} ℕ
    let stages' := e.inverse ⋙ stages
    have hstages' : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
        (colimit stages') :=
      Stacks.SheafOfModules.FlatColimits.isFlat_colimit (O := X.O) stages' (fun n =>
        isFlat_of_isSumOfExtensionByZeroStructureSheaves X _
          (L.term_isSum (e.inverse.obj n) i))
    let eCol : colimit stages' ≅ colimit stages :=
      HasColimit.isoOfEquivalence e.symm (Iso.refl _)
    exact (exactFunctor _ _).prop_of_iso
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.mapIso
        (eCol ≪≫ eEval.symm)) hstages'
  · intro i
    let n : ℕ := i.toNat
    have hle : i < (n : ℤ) + 1 := by dsimp [n]; omega
    let q := L.toTruncation n ≫ G.ιTruncLE ((n : ℤ) + 1)
    have hq : Epi (q.f i) := by
      have h₁ : Epi ((L.toTruncation n).f i) := L.epi_f n i
      have h₂ : IsIso ((G.ιTruncLE ((n : ℤ) + 1)).f i) :=
        Stacks.SheafOfModules.isIso_ιTruncLE_f_of_lt _ _ _ hle
      show Epi ((L.toTruncation n).f i ≫ (G.ιTruncLE ((n : ℤ) + 1)).f i)
      infer_instance
    have hcomp : (colimit.ι L.system n).f i ≫ L.colimitComparison.f i = q.f i := by
      simpa [q] using congrArg (fun g => HomologicalComplex.Hom.f g i)
        (L.colimitComparison_fac n)
    exact epi_of_epi_fac hcomp

/-- A chosen K-flat resolution complex of a complex of sheaves of modules. -/
noncomputable def kFlatResolution
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  Classical.choose (exists_kFlatResolution X G)

/-- The augmentation from the chosen K-flat resolution. -/
noncomputable def kFlatResolutionHom
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    kFlatResolution X G ⟶ G :=
  Classical.choose (Classical.choose_spec (exists_kFlatResolution X G))

private theorem chosenResolution_properties
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Stacks.SheafOfModules.IsKFlat X.O (kFlatResolution X G) ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
        ((kFlatResolution X G).X i)) ∧
      QuasiIso (kFlatResolutionHom X G) ∧
      (∀ i : ℤ, Epi ((kFlatResolutionHom X G).f i)) :=
  Classical.choose_spec (Classical.choose_spec (exists_kFlatResolution X G))

/-- The chosen resolution is K-flat. -/
@[stacks 06YS "K-flatness of the chosen resolution"]
theorem kFlatResolution_kFlat
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Stacks.SheafOfModules.IsKFlat X.O (kFlatResolution X G) :=
  (chosenResolution_properties X G).1

/-- Every term of the chosen resolution is flat. -/
@[stacks 06YS "flatness of the terms of the chosen resolution"]
theorem kFlatResolution_flat
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((kFlatResolution X G).X i) :=
  (chosenResolution_properties X G).2.1 i

/-- The augmentation from the chosen resolution is a quasi-isomorphism. -/
@[stacks 06YS "quasi-isomorphism of the augmentation"]
theorem kFlatResolutionHom_quasiIso
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (kFlatResolutionHom X G) :=
  (chosenResolution_properties X G).2.2.1

/-- The augmentation from the chosen resolution is epimorphic in each degree. -/
@[stacks 06YS "termwise surjectivity of the augmentation"]
theorem kFlatResolutionHom_epi
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (i : ℤ) :
    Epi ((kFlatResolutionHom X G).f i) :=
  (chosenResolution_properties X G).2.2.2 i

end Stacks.Cohomology

end
