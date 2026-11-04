module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CountablePerfectHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.SquareZeroExtensionDerivedHom
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup

/-!
# `Rf_* 𝒪_U` is a derived colimit of perfect complexes, over countable rings

Let `f : U ⟶ X` be a quasi-compact and quasi-separated morphism between quasi-compact and
quasi-separated schemes whose rings of sections over affine opens are countable. Then the derived
direct image `Rf_* 𝒪_U` is a derived colimit `hocolim Eₙ` of perfect objects of `D(𝒪_X)`.

## Main results

* `Stacks.Cohomology.CountableSections.isPerfect_derivedUnitObject`,
  `isQuasicoherent_homology_derivedUnitObject`,
  `countable_sections_homology_derivedUnitObject`: `𝒪_X[0]` is perfect, with quasi-coherent
  cohomology sheaves, which have countable sections over affines when `𝒪_X` does.
* `exists_isHomotopyColimit_derivedPushforward_unit_of_countable`:
  `Rf_* 𝒪_U = hocolim Eₙ` with `Eₙ` perfect.

## Implementation notes

`exists_isHomotopyColimit_derivedPushforward_unit_of_countable` is stated at
`HasDerivedCategory.standard`, with the model scoped to that declaration.

## References

* [Stacks Project, Tag 0CRR](https://stacks.math.columbia.edu/tag/0CRR)
* [Stacks Project, Tag 0CRQ](https://stacks.math.columbia.edu/tag/0CRQ)
* [Stacks Project, Tag 0CRP](https://stacks.math.columbia.edu/tag/0CRP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated

universe w u

namespace Stacks.Cohomology.CountableSections

/-! ### The structure sheaf in degree zero -/

section Unit

variable (X : Scheme.{u}) [h : HasDerivedCategory.{w} X.Modules]

/-- `𝒪_X[0]` is perfect, at every model. -/
theorem isPerfect_derivedUnitObject :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h (derivedUnitObject X) :=
  ⟨(CochainComplex.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf),
    isPerfectComplex_single_of_isFiniteLocallyFree X _ (isFiniteLocallyFree_unit X),
    ⟨((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm⟩⟩

/-- A property of modules invariant under isomorphism, holding for `𝒪_X` and for zero modules,
holds for every cohomology sheaf of `𝒪_X[0]`. -/
private theorem prop_homology_derivedUnitObject (P : X.Modules → Prop)
    (hiso : ∀ {M N : X.Modules}, (M ≅ N) → P M → P N) (hzero : ∀ M : X.Modules, IsZero M → P M)
    (hunit : P (SheafOfModules.unit X.ringCatSheaf)) (i : ℤ) :
    P ((DerivedCategory.homologyFunctor X.Modules i).obj (derivedUnitObject X)) := by
  by_cases hi : i = 0
  · subst hi
    exact hiso ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app _).symm hunit
  · exact hzero _ (Stacks.SquareZeroExt.isZero_homology_singleFunctor (C := X.Modules) _ hi)

/-- The cohomology sheaves of `𝒪_X[0]` are quasi-coherent: `𝒪_X` in degree zero and zero
elsewhere. -/
theorem isQuasicoherent_homology_derivedUnitObject (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj (derivedUnitObject X)).IsQuasicoherent := by
  have : (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero :=
    ⟨SheafOfModules.free (R := X.ringCatSheaf) (PEmpty : Type u),
      (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun n => n.elim), inferInstance⟩
  exact prop_homology_derivedUnitObject X (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (fun e => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e)
    (fun _ => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero)
    inferInstance i

/-- The cohomology sheaves of `𝒪_X[0]` have countable sections over every affine open when `𝒪_X`
does. -/
theorem countable_sections_homology_derivedUnitObject
    (hO : ∀ V : X.Opens, IsAffineOpen V → Countable Γ(X, V)) (V : X.Opens) (hV : IsAffineOpen V)
    (i : ℤ) :
    Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj (derivedUnitObject X), V) := by
  have := hO V hV
  refine prop_homology_derivedUnitObject X (fun M => Countable Γ(M, V))
    (fun e => countable_sections_of_iso e V) (fun M hz => ?_) this i
  suffices Subsingleton Γ(M, V) from inferInstance
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : Γ(M, V), z = 0 := fun z => by
    simpa using congrArg (fun φ => (Scheme.Modules.Hom.app φ V).hom z) (hz.eq_of_src (𝟙 M) 0)
  rw [hx x, hx y]

end Unit

/-! ### The derived direct image of the structure sheaf -/

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`Rf_* 𝒪_U` is a derived colimit of perfect complexes** when `U` and `X` are quasi-compact
and quasi-separated with countable rings of sections over affine opens and `f` is quasi-compact
and quasi-separated. It is stated at `HasDerivedCategory.standard`. -/
theorem exists_isHomotopyColimit_derivedPushforward_unit_of_countable {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U] [QuasiSeparatedSpace U]
    (hOX : ∀ V : X.Opens, IsAffineOpen V → Countable Γ(X, V))
    (hOU : ∀ V : U.Opens, IsAffineOpen V → Countable Γ(U, V))
    (f : U ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    ∃ F : ℕ ⥤ DerivedCategory X.Modules,
      (∀ n, Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (F.obj n)) ∧
        IsHomotopyColimit F
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            f.toLRSHom.toShHom).obj (derivedUnitObject U)) := by
  let adj := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
    f.toLRSHom.toShHom
  refine exists_isHomotopyColimit_isPerfect_of_countable_hom hOX _
    (fun i => AlgebraicGeometry.isQuasicoherent_derivedPushforward f
      ⟨derivedUnitObject U, isQuasicoherent_homology_derivedUnitObject U⟩ i) ?_
  intro G hG m
  have hG' := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    f.toLRSHom.toShHom G hG
  have hc := countable_hom_shift_of_isPerfect _ (derivedUnitObject U) hG'
    (isQuasicoherent_homology_derivedUnitObject U)
    (countable_sections_homology_derivedUnitObject U hOU) m
  exact @Countable.of_equiv _ _ hc ((Iso.homCongr
    (((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).commShiftIso m).app G).symm (Iso.refl _)).trans (adj.homEquiv _ _))

end Stacks.Cohomology.CountableSections

end
