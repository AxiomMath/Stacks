module

public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Components
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtension.FiniteSet
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections

/-!
# Glueing ample sheaves along the components of a one-dimensional scheme

This file carries out the second and third steps of the proof of
[Stacks, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX).  Given the closed cover by
irreducible components of `StacksDraft.AlgebraicGeometry.F3b.AmpleReducedDimensionOne.Components`:

* on each component choose an ample invertible sheaf
  ([Tag 09ND](https://stacks.math.columbia.edu/tag/09ND), in the form formalized as
  `StacksTag09NX.exists_isAmple_subscheme_vanishingIdeal_irreducibleComponent`) and then a global
  section of a *power* of it whose nonvanishing locus is affine and contains the part of `T` lying
  on that component ([Tag 09NV](https://stacks.math.columbia.edu/tag/09NV));
* glue the powers and the sections into one invertible sheaf `M` on `X` with a global section `t`
  restricting to the chosen sections ([Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)).

## Main results

* `Stacks.AmpleReducedDimensionOne.exists_power_section_isAmple_of_finite`: the two-tag step
  "replace `L` by a power and choose a section nonvanishing on a finite set", for a single scheme.
* `Stacks.AmpleReducedDimensionOne.exists_componentSections`: the same for every component of `X`
  at once.
* `Stacks.AmpleReducedDimensionOne.exists_glued_invertible_section`: `M`, `t` and the family of
  comparison isomorphisms.

## Implementation notes

**The exponents are not equalised across the components.**  Tag 09NE accepts an arbitrary family
of invertible sheaves, so the proof's "possibly after replacing `L_i` by a power" may be carried
out independently on each component; nothing has to be raised to a common exponent.  This is why
`exists_componentSections` keeps the powers inside the existential rather than returning an
exponent.

**The two invertibility classes.**  Tag 01CS is developed twice in this repository.  Tag 09NV and
Tag 09NE are stated for `AlgebraicGeometry.SheafOfModules.IsInvertible` while
`Stacks.SheafOfModules.nonvanishingOpen` is defined for `Stacks.SheafOfModules.IsInvertible`; the
crossing is supplied as an instance by
`StacksTag09NE.isInvertible_stacks_of_isInvertible`, in the import closure here, so no statement
below has to carry both hypotheses.  Both classes are `Prop`s, so which witness is used does not
affect what any statement says.

The exponent is raised with `AlgebraicGeometry.Scheme.Modules.tensorPowerModules`, an `abbrev` for
the same term that Tag 09NV's `Stacks.SheafOfModules.Invertible.tensorPowerModule'` names, so the
two spellings need no conversion.

## References

* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Topology.Irreducible
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AmpleReducedDimensionOne

/-! ### A section of a power, nonvanishing on a finite set -/

/-- **Step (B) of the proof of Tag 09NX, for one scheme.**  If `L` is ample on `Y` and `E ⊆ Y` is
finite then some power `L^{⊗ m}`, `m ≥ 1`, carries a global section whose nonvanishing locus is
affine and contains `E` — and that power is again ample.

The section is Tag 09NV applied with the open `W` taken to be everything, so the containment
`Y_s ⊆ W` of that statement is dropped here; ampleness of the power is Tag 01PT. -/
theorem exists_power_section_isAmple_of_finite {Y : Scheme.{u}} (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple Y L) {E : Set Y} (hE : E.Finite) :
    ∃ (m : ℕ) (_ : 1 ≤ m)
      (s : (AlgebraicGeometry.Scheme.Modules.tensorPowerModules L (m : ℤ)).sections),
      IsAffineOpen (nonvanishingOpen (X := Y.toRingedSpace)
          (AlgebraicGeometry.Scheme.Modules.tensorPowerModules L (m : ℤ)) s) ∧
        E ⊆ (nonvanishingOpen (X := Y.toRingedSpace)
          (AlgebraicGeometry.Scheme.Modules.tensorPowerModules L (m : ℤ)) s : Set Y) ∧
        AlgebraicGeometry.Scheme.Modules.IsAmple Y
          (AlgebraicGeometry.Scheme.Modules.tensorPowerModules L (m : ℤ)) := by
  obtain ⟨m, hm, s, haff, hEs, -⟩ :=
    exists_sections_finite_subset_nonvanishingOpen_le_of_isAmple L hL hE ⊤ fun _ _ => trivial
  exact ⟨m, hm, s, haff, hEs,
    (AlgebraicGeometry.isAmple_iff_tensorPower_isAmple _ L m hm).mp hL⟩

variable (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X]

/-- **Step (B) of the proof of Tag 09NX, for every irreducible component at once.**  On each
component there is an ample invertible sheaf with a global section whose nonvanishing locus is
affine and contains the part of `T` lying on that component.

The sheaf returned is already the power: the exponents chosen on different components are
unrelated, and nothing downstream needs them. -/
theorem exists_componentSections [X.IsSeparated] (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (L : ∀ C : irreducibleComponents (X : Type u), (componentScheme X C).Modules)
      (_ : ∀ C, AlgebraicGeometry.SheafOfModules.IsInvertible
            (componentScheme X C).presheaf (componentScheme X C).ringCatSheaf.2 (L C))
      (s : ∀ C, (L C).sections),
      (∀ C, IsAffineOpen (nonvanishingOpen (X := (componentScheme X C).toRingedSpace)
          (L C) (s C))) ∧
        (∀ C, AlgebraicGeometry.Scheme.Modules.IsAmple (componentScheme X C) (L C)) ∧
        (∀ C, (componentι X C).base ⁻¹' componentOverlap X ⊆
          (nonvanishingOpen (X := (componentScheme X C).toRingedSpace) (L C) (s C) : Set _)) := by
  classical
  choose L₀ hL₀ hample₀ using fun C : irreducibleComponents (X : Type u) =>
    StacksTag09NX.exists_isAmple_subscheme_vanishingIdeal_irreducibleComponent X C.2 hdim
  have hinst : ∀ C, AlgebraicGeometry.SheafOfModules.IsInvertible
      (componentScheme X C).toRingedSpace.presheaf
      (structureSheafRing (componentScheme X C).toRingedSpace).property (L₀ C) := hL₀
  choose m hm s haff hEs using fun C : irreducibleComponents (X : Type u) =>
    exists_power_section_isAmple_of_finite (L₀ C) (hample₀ C)
      (finite_preimage_componentOverlap X hdim C)
  exact ⟨fun C => AlgebraicGeometry.Scheme.Modules.tensorPowerModules (L₀ C) ((m C : ℕ) : ℤ),
    fun C => inferInstance, s, haff, fun C => (hEs C).2, fun C => (hEs C).1⟩

/-! ### The glued sheaf and its global section -/

/-- **Step (C) of the proof of Tag 09NX: the glueing.**  On a Noetherian reduced separated scheme
of dimension at most one there are an invertible sheaf `M` and a global section `t` of it which
restrict, on every irreducible component, to an ample invertible sheaf with an affine nonvanishing
locus containing the part of `T` on that component.

The comparison with the component data is recorded exactly as Tag 09NE delivers it: an isomorphism
`(componentι X C)^* M ≅ L C` carrying the image of `t` under the unit of the pullback–pushforward
adjunction to `s C`, over `⊤`.  That is enough to identify the preimage of `X_t` in the component
with `(Z_C)_{s C}`, which is what the affineness step needs. -/
theorem exists_glued_invertible_section [AlgebraicGeometry.IsReduced X] [X.IsSeparated]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (M : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
      (t : M.sections)
      (L : ∀ C : irreducibleComponents (X : Type u), (componentScheme X C).Modules)
      (_ : ∀ C, AlgebraicGeometry.SheafOfModules.IsInvertible
            (componentScheme X C).presheaf (componentScheme X C).ringCatSheaf.2 (L C))
      (s : ∀ C, (L C).sections),
      (∀ C, IsAffineOpen (nonvanishingOpen (X := (componentScheme X C).toRingedSpace)
          (L C) (s C))) ∧
        (∀ C, AlgebraicGeometry.Scheme.Modules.IsAmple (componentScheme X C) (L C)) ∧
        (∀ C, (componentι X C).base ⁻¹' componentOverlap X ⊆
          (nonvanishingOpen (X := (componentScheme X C).toRingedSpace) (L C) (s C) : Set _)) ∧
        (∀ C, ∃ e : (modulePullback (componentι X C).toLRSHom.toShHom).obj M ≅ L C,
          e.hom.val.app (op ⊤)
            (((modulePullbackPushforwardAdjunction
                (componentι X C).toLRSHom.toShHom).unit.app M).val.app (op ⊤)
              (t.eval (op ⊤))) = (s C).eval (op ⊤)) := by
  have : Finite (irreducibleComponents (X : Type u)) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  obtain ⟨L, hL, s, haff, hample, hEs⟩ := exists_componentSections X hdim
  have := hL
  have hs : ∀ C D : irreducibleComponents (X : Type u), C ≠ D →
      ∀ z : componentScheme X C, (componentι X C) z ∈ Set.range (componentι X D) →
        z ∈ nonvanishingLocus (X := (componentScheme X C).toRingedSpace) (L C) (s C) :=
    fun C D hCD z hz => hEs C (mem_componentOverlap_of_mem_range X hCD z hz)
  obtain ⟨M, hM, t, he⟩ :=
    StacksTag09NE.exists_invertible_with_sections_of_closed_cover_discrete_intersections
      X (componentScheme X) (componentι X) (exists_componentι_eq X)
      (discreteTopology_range_inter_componentι X hdim) L s hs
  exact ⟨M, hM, t, L, hL, s, haff, hample, hEs, he⟩

end Stacks.AmpleReducedDimensionOne

end
