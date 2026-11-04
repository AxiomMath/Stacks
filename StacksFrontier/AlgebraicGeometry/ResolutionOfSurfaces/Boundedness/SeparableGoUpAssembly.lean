module

public import Mathlib.RingTheory.LocalRing.Length
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ModificationATorsion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpFiniteCase
public import
StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpFirstCohomologyInjective
public import
StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionVanishingDescends
public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic

/-!
# Assembling [Stacks, Tag 0AXL] from the finite case

Let `A → B` be a finite local map of local domains with `A` normal. Suppose that

* the trace identity `d σ = ∑ⱼ Trace(bⱼ σ) eⱼ` holds (`Stacks.Trace.exists_traceIdentity`);
* the lengths of the `d`-torsion of `H¹(Y, 𝒪_Y)` are bounded over the normal modifications `Y`
  of `Spec B` (this is what [Stacks, Tags 0AXJ and 0AXK] give);
* every normal modification `Y` of `Spec B` is dominated by a normal modification `Y'` of
  `Spec B` which is finite over a normal modification `X'` of `Spec A` (the reduction step of
  the source's proof).

Then reduction to rational singularities possible for `A` implies it for `B`: the length of
`H¹(Y, 𝒪_Y)` is at most that of `H¹(Y', 𝒪_{Y'})` (`q_* 𝒪_{Y'} = 𝒪_Y`), which over `A` is at most
`n · length H¹(X', 𝒪_{X'})` plus the length of its `d`-torsion, and over `A` a `B`-module has
length `[κ_B : κ_A]` times its length over `B`.

## Main results

* `AlgebraicGeometry.SeparableGoUp.length_firstCohomology_le_of_isModification`: lengths of
  `H¹(𝒪)` grow along a modification of a normal integral scheme over `Spec B`.
* `AlgebraicGeometry.SeparableGoUp.isReductionToRationalSingularitiesPossible_of_dominated`:
  the assembly described above.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SeparableGoUp

/-- **A factor of a modification through a modification is a modification.** If `g : Y ⟶ S` and
`q ≫ g` are modifications then so is `q`: it is proper because `g` is separated, and birational
because the generic point of `Y` is the exact preimage of that of `S`. -/
theorem isModification_of_comp {Z Y S : Scheme.{u}} [IsIntegral S] [IsIntegral Y] {q : Z ⟶ Y}
    {g : Y ⟶ S} (hg : IsModification g) (hqg : IsModification (q ≫ g)) : IsModification q := by
  have hgp : IsProper g := hg.isProper
  have hqgp : IsProper (q ≫ g) := hqg.isProper
  have hfin : ∀ (X : Scheme.{u}) [IsIntegral X], Finite (irreducibleComponents X) := fun X _ => by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have := hfin Y
  have := hfin S
  exact ⟨isBirational_of_comp_of_isBirational q g hqg.isBirational hg.isBirational
    (preimage_genericPoints_eq_genericPoints_of_isBirational g hg.isBirational),
    IsProper.of_comp q g, hqg.source_isIntegral⟩

/-- **Stacks Project, Tag 0AXF, the injectivity in the first conclusion, read on lengths.** For
a modification `q : Y' ⟶ Y` of a normal integral scheme over `Spec B`, the length of
`H¹(Y, 𝒪_Y)` over `B` is at most that of `H¹(Y', 𝒪_{Y'})`. -/
theorem length_firstCohomology_le_of_isModification {B : Type u} [CommRing B]
    {Y Y' : Scheme.{u}} [IsIntegral Y] [IsNormal Y] (g : Y ⟶ Spec (.of B)) (q : Y' ⟶ Y)
    (hq : IsModification q) :
    Module.length B (firstCohomologyAsBaseModule Y g) ≤
      Module.length B (firstCohomologyAsBaseModule Y' (q ≫ g)) := by
  have : IsIntegral Y' := hq.source_isIntegral
  have : IsProper q := hq.isProper
  have := isIso_c_of_isBirational_of_isNormal q hq.isBirational
  exact length_firstCohomology_le_of_isIso_c q g

/-- Over a finite local map `A → B` of local rings, the length over `A` of a `B`-module with
scalars restricted is `[κ_B : κ_A]` times its length over `B`, and in particular at most that
multiple of any bound for the length over `B`. -/
theorem length_restrictScalars_torsionBy_le {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (M : ModuleCat.{u} B) (d : A) :
    Module.length A (Submodule.torsionBy A ((ModuleCat.restrictScalars (algebraMap A B)).obj M) d)
      = Module.length B (Submodule.torsionBy B M (algebraMap A B d)) *
        Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  let N := Submodule.torsionBy B M (algebraMap A B d)
  let : Module A N := Module.compHom N (algebraMap A B)
  have : IsScalarTower A B N := ⟨fun a b x => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  rw [← IsLocalRing.length_restrictScalars A B N]
  refine LinearEquiv.length_eq ?_
  exact
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The reduction step of [Stacks, Tag 0AXL], as a property of `A → B`: every normal modification
`Y` of `Spec B` is dominated by a normal modification `Y'` of `Spec B` which is finite and
surjective over a normal modification `X'` of `Spec A`, compatibly with `Spec B ⟶ Spec A`. -/
def IsDominatedByFiniteOverBase (A B : Type u) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] : Prop :=
  ∀ (Y : Scheme.{u}) [IsNormal Y] (g : Y ⟶ Spec (.of B)), IsModification g →
    ∃ (Y' X' : Scheme.{u}) (g' : Y' ⟶ Spec (.of B)) (f' : X' ⟶ Spec (.of A)) (π : Y' ⟶ X')
      (q : Y' ⟶ Y), IsNormal Y' ∧ IsNormal X' ∧ IsModification g' ∧ IsModification f' ∧
        IsFinite π ∧ Surjective π ∧
        π ≫ f' = g' ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧ q ≫ g = g'

/-- **[Stacks, Tag 0AXL], assembled from its three inputs.** For a finite local map `A → B` of
local domains with `A` normal: the trace identity for `b, e : Fin n → B` and `d ∈ A`, a uniform
bound on the `d`-torsion of `H¹(Y, 𝒪_Y)` over the normal modifications of `Spec B`, and the
reduction step `IsDominatedByFiniteOverBase A B` carry reduction to rational singularities from
`A` to `B`. -/
theorem isReductionToRationalSingularitiesPossible_of_dominated (A B : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [CommRing B] [IsLocalRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] [IsLocalHom (algebraMap A B)] {n : ℕ} (b e : Fin n → B) (d : A)
    (hid : ∀ (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
        [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
        [IsScalarTower A B L] (σ : L),
        algebraMap A L d * σ =
          ∑ j, algebraMap K L (Algebra.trace K L (algebraMap B L (b j) * σ)) *
            algebraMap B L (e j))
    (htors : ∃ N : ℕ, ∀ (Y : Scheme.{u}) [IsNormal Y] (g : Y ⟶ Spec (.of B)), IsModification g →
      Module.length B (Submodule.torsionBy B (firstCohomologyAsBaseModule Y g)
        (algebraMap A B d)) ≤ N)
    (hdom : IsDominatedByFiniteOverBase A B)
    (hA : IsReductionToRationalSingularitiesPossible A) :
    IsReductionToRationalSingularitiesPossible B := by
  obtain ⟨NA, hNA⟩ := hA
  obtain ⟨NT, hNT⟩ := htors
  have hκ : Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    Module.length_eq_finrank _ _
  refine ⟨n * NA + NT * Module.finrank (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B), fun Y _ g hg => ?_⟩
  have : IsIntegral Y := hg.source_isIntegral
  obtain ⟨Y', X', g', f', π, q, hY', hX', hg', hf', hπ, hπs, hcomm, hq⟩ := hdom Y g hg
  have := hY'
  have := hX'
  have := hπ
  have := hπs
  have : IsIntegral Y' := hg'.source_isIntegral
  have : IsIntegral X' := hf'.source_isIntegral
  have hqmod : IsModification q := by
    subst hq
    exact isModification_of_comp hg hg'
  have h1 := length_firstCohomology_le_of_isModification g q hqmod
  rw [hq] at h1
  have h2 := Module.length_le_length_restrictScalars B B (RingHom.id B)
    (firstCohomologyAsBaseModule Y' g')
  have h3 := length_firstCohomology_le_of_isFinite b e d hid f' g' π hf'.isBirational
    hg'.isBirational hcomm
  have h4 := length_restrictScalars_torsionBy_le (firstCohomologyAsBaseModule Y' g') d
  have h5 : Module.length B (firstCohomologyAsBaseModule Y' g') ≤
      Module.length A ((ModuleCat.restrictScalars (algebraMap A B)).obj
        (firstCohomologyAsBaseModule Y' g')) :=
    Module.length_le_length_restrictScalars A B (algebraMap A B) _
  refine h1.trans (h5.trans (h3.trans ?_))
  rw [h4, hκ]
  push_cast
  gcongr
  · exact hNA X' f' hf'
  · exact hNT Y' g' hg'

end AlgebraicGeometry.SeparableGoUp

end
