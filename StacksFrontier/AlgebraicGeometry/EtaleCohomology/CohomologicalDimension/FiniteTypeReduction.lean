module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.MorphismReduction
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueFieldTrdegBound

/-!
# Schemes of finite type over a field: finiteness of `cd(f)` reduced to the affine case

This file contains the reduction step of part (1) of [Stacks, Tag 0F10], together with the
finiteness properties of schemes of finite type over a field that the definitions of `cd`
need. The affine case and the tag itself are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteType`.

A scheme of finite type over a field is Noetherian, so it is quasi-compact and
quasi-separated, and so is every morphism between such schemes.

## Main results

* `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_lt_top_of_finiteType_of_isAffine`:
  `cd(f) < ∞` for a morphism `f` of schemes of finite type over a field, once every morphism
  of affine schemes of finite type over that field has a finite bound.

## References

* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme of finite type over a field is Noetherian. -/
theorem isNoetherian_of_finiteType (K : Type u) [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) [LocallyOfFiniteType x] [QuasiCompact x] : IsNoetherian X :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace x
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian x
  ⟨⟩

/-- A scheme of finite type over a field is quasi-compact. -/
theorem compactSpace_of_finiteType (K : Type u) [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) [LocallyOfFiniteType x] [QuasiCompact x] : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace x

/-- A scheme of finite type over a field is quasi-separated. -/
theorem quasiSeparatedSpace_of_finiteType (K : Type u) [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) [LocallyOfFiniteType x] [QuasiCompact x] : QuasiSeparatedSpace X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian x
  IsLocallyNoetherian.quasiSeparatedSpace

/-- A morphism of schemes of finite type over a field is quasi-compact. -/
theorem quasiCompact_of_finiteType (K : Type u) [Field K] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) [LocallyOfFiniteType x] [QuasiCompact x]
    (y : Y ⟶ Spec (.of K)) [LocallyOfFiniteType y] [QuasiCompact y] (f : X ⟶ Y) :
    QuasiCompact f :=
  @quasiCompact_of_compactSpace _ _ f (compactSpace_of_finiteType K x)
    (quasiSeparatedSpace_of_finiteType K y)

/-- A morphism of schemes of finite type over a field is quasi-separated. -/
theorem quasiSeparated_of_finiteType (K : Type u) [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) [LocallyOfFiniteType x] [QuasiCompact x] {Y : Scheme.{u}}
    (f : X ⟶ Y) : QuasiSeparated f :=
  @QuasiSeparated.of_quasiSeparatedSpace _ _ f (quasiSeparatedSpace_of_finiteType K x)

/-- **The reduction of part (1) of [Stacks, Tag 0F10] to the affine case.** Let `f : X ⟶ Y` be
a morphism of schemes of finite type over a field `K`. If every morphism of affine schemes of
finite type over `K` has a finite bound on the higher direct images of torsion sheaves, then
`cd(f) < ∞`. The question is local on `Y`
(`Scheme.Hom.etaleCohomologicalDimension_lt_top_of_openCover`), and over an affine open of `Y`
the induction principle with the relative Mayer--Vietoris sequence reduces to affine sources
(`Scheme.Hom.etaleCohomologicalDimension_lt_top_of_isAffine_source`). -/
theorem Hom.etaleCohomologicalDimension_lt_top_of_finiteType_of_isAffine
    (K : Type u) [Field K]
    {X Y : Scheme.{u}} (x : X ⟶ Spec (.of K)) [LocallyOfFiniteType x] [QuasiCompact x]
    (y : Y ⟶ Spec (.of K)) [LocallyOfFiniteType y] [QuasiCompact y] (f : X ⟶ Y)
    (hf : f ≫ y = x)
    (haff : ∀ {Z V : Scheme.{u}} [IsAffine Z] [IsAffine V] (gX : Z ⟶ Spec (.of K))
      [LocallyOfFiniteType gX] (gY : V ⟶ Spec (.of K)) [LocallyOfFiniteType gY] (g : Z ⟶ V),
      g ≫ gY = gX → ∃ d : ℕ, IsEtaleHigherDirectImageBound g d) :
    haveI := quasiCompact_of_finiteType K x y f
    haveI := quasiSeparated_of_finiteType K x f
    f.etaleCohomologicalDimension < ⊤ := by
  have := quasiCompact_of_finiteType K x y f
  have := quasiSeparated_of_finiteType K x f
  have := isNoetherian_of_finiteType K x
  have := isNoetherian_of_finiteType K y
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := Y) (U := ⊤)).mp
      (by simpa using (isCompact_univ : IsCompact (Set.univ : Set Y)))
  have : Finite s := hs.to_subtype
  let V : s → Y.Opens := fun i => i.1.1
  have hV (z : Y) : ∃ i, z ∈ V i := by
    have hz : z ∈ (⨆ i ∈ s, (i : Y.Opens)) := hcover ▸ trivial
    simpa [V] using hz
  refine Hom.etaleCohomologicalDimension_lt_top_of_openCover f V hV fun i => ?_
  have : IsAffine (V i).toScheme := i.1.2
  have : CompactSpace (f ⁻¹ᵁ V i) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have hcd := Hom.etaleCohomologicalDimension_lt_top_of_isAffine_source (f ∣_ V i)
    fun Z _ j _ => haff (j ≫ (f ⁻¹ᵁ V i).ι ≫ x) ((V i).ι ≫ y) (j ≫ f ∣_ V i) (by simp [hf])
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hcd.ne
  exact ⟨d, hd ▸ isEtaleHigherDirectImageBound_etaleCohomologicalDimension (f ∣_ V i)⟩

end AlgebraicGeometry.Scheme

end
