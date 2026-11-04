module

public import StacksFrontier.AlgebraicGeometry.Cohomology.PushforwardUnitHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Limits.CountableFlatModel
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison

/-!
# `Rf_* 𝒪_U` is a derived colimit of perfect complexes, for `f` flat of finite presentation

Let `A` be a ring, `X` a scheme of finite presentation over `A` and `f : U ⟶ X` a flat morphism
of finite presentation. Then `Rf_* 𝒪_U = hocolim Eₙ` for a system of perfect objects `Eₙ` of
`D(𝒪_X)`.

## Main results

* `Stacks.Cohomology.CountableSections.exists_isHomotopyColimitWith_derivedPushforward_unit`:
  `Rf_* 𝒪_U = hocolim Eₙ` with explicit coprojections `Eₙ ⟶ Rf_* 𝒪_U`.

## Implementation notes

The statement is made at `HasDerivedCategory.standard`, with the model scoped to the declaration.

## References

* [Stacks Project, Tag 0CRR](https://stacks.math.columbia.edu/tag/0CRR)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.Cohomology.CountableSections

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`Rf_* 𝒪_U` is a derived colimit of perfect complexes**, with explicit coprojections, for
`f : U ⟶ X` flat of finite presentation and `X` of finite presentation over a ring `A`: there are
a system `E : ℕ ⥤ D(𝒪_X)` of perfect objects and maps `cₙ : Eₙ ⟶ Rf_* 𝒪_U` exhibiting
`Rf_* 𝒪_U = hocolim Eₙ`. It is stated at `HasDerivedCategory.standard`. -/
theorem exists_isHomotopyColimitWith_derivedPushforward_unit {A : Type u} [CommRing A]
    {X U : Scheme.{u}} (p : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation p] [QuasiCompact p]
    [QuasiSeparated p] (f : U ⟶ X) [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] :
    ∃ (E : ℕ ⥤ DerivedCategory X.Modules)
      (c : ∀ n, E.obj n ⟶ (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        f.toLRSHom.toShHom).obj (derivedUnitObject U)),
      (∀ n, Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (E.obj n)) ∧
        IsHomotopyColimitWith E
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            f.toLRSHom.toShHom).obj (derivedUnitObject U)) c := by
  obtain ⟨X₀, U₀, g, g', f₀, hpb, hflat, hqc, hqs, hX₀c, hX₀s, hU₀c, hU₀s, hcX, hcU⟩ :=
    exists_countable_flat_model p f
  obtain ⟨F₀, hF₀p, hF₀⟩ := exists_isHomotopyColimit_derivedPushforward_unit_of_countable
    hcX hcU f₀
  let Lg : DerivedCategory X₀.Modules ⥤ DerivedCategory X.Modules :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom
  let : Lg.CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift g.toLRSHom.toShHom
  have : Lg.IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated g.toLRSHom.toShHom
  have : PreservesColimitsOfSize.{0, 0} Lg :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      g.toLRSHom.toShHom).leftAdjoint_preservesColimits
  have hmap := hF₀.map Lg
  have hsq : g'.toLRSHom.toShHom ≫ f₀.toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ g.toLRSHom.toShHom := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      congrArg (fun k : U ⟶ X₀ => k.toLRSHom.toShHom) hpb.w
  have hbc : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      g'.toLRSHom.toShHom f.toLRSHom.toShHom f₀.toLRSHom.toShHom g.toLRSHom.toShHom hsq
      (derivedUnitObject U₀)) :=
    derivedBaseChangeIsIsoOnQuasicoherent g' f f₀ g hpb hqc hqs
      (torIndependent_of_flat_left f₀ g) hsq _ (isQuasicoherent_homology_derivedUnitObject U₀)
  let φ : Lg.obj ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        f₀.toLRSHom.toShHom).obj (derivedUnitObject U₀)) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        f.toLRSHom.toShHom).obj (derivedUnitObject U) :=
    @asIso _ _ _ _ (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      g'.toLRSHom.toShHom f.toLRSHom.toShHom f₀.toLRSHom.toShHom g.toLRSHom.toShHom hsq
      (derivedUnitObject U₀)) hbc ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
      f.toLRSHom.toShHom).mapIso
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso g'.toLRSHom.toShHom)
  obtain ⟨c, hc⟩ := hmap.exists_isHomotopyColimitWith
  exact ⟨F₀ ⋙ Lg, _, fun n =>
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      g.toLRSHom.toShHom _ (hF₀p n), hc.of_iso φ⟩

end Stacks.Cohomology.CountableSections

end
