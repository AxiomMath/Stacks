module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Locality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimension

/-!
# The finite-type clause of Tag 0EX4 is its own affine-base case

[Stacks, Tag 0EX4] asserts, for `f : X ⟶ Y` proper all of whose fibres have dimension at most
`d` and `F` quasi-coherent of finite type, that `R ᵈ f_* F` is quasi-coherent of finite type.
The base `Y` carries **no** Noetherian hypothesis, and the source's proof opens — before any of
its limit argument — by replacing `Y` with an affine open: the conclusion is local on `Y`, and
over an affine base the limit presentation `R = colim R_i` by Noetherian rings is available.

This file proves that opening reduction at the tag's own shape, and shows it loses nothing: the
finite-type clause over an arbitrary base and the finite-type clause over affine bases, each
quantified over all of its own data, are **equivalent**.

**Why this is not already the locality statement in
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/Locality.lean`.** That file's
`…ProperCohomologyFinite.isFiniteType_rightDerivedPlus_of_forall_isAffineOpen` is the locality of
finite type for `CategoryTheory.Functor.rightDerivedPlus` and carries no hypothesis on the fibres
of `f`, while the tag's clause is about `CategoryTheory.Functor.rightDerived` and the
fibre-dimension bound is one of its hypotheses. The bound has to be *transported* to `f ∣_ V`,
and it is: the fibres of `f ∣_ V` over points of `V` are the fibres of `f`
(`AlgebraicGeometry.topologicalKrullDim_fiber_morphismRestrict_le`, [Stacks, Tag 02FY] part (1)).
Without that transport the restricted morphism satisfies no bound and the hypothesis of the
affine case cannot be met.

**What this does and does not reduce.** Over a *locally Noetherian* base the clause is already
known to be exactly [Stacks, Tag 02O6], with the fibre-dimension bound provably inert
(`…TopDegreeFiniteType.forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology`).
What the tag asks beyond that is the case of a base with no Noetherian hypothesis, and this file
moves that case from an arbitrary base to an affine one — which is where the source's limit
argument ([Stacks, Tags 09ZR, 05M5, 01ZM, 081F, 01ZR, 0EX3, 086M]) takes place, `Y = Spec R`
being written as the limit of the `Spec R_i` for the Noetherian subrings `R_i ⊆ R`. It does not
discharge any part of that argument, and it does not touch
[Stacks, Tag 02O6]. After this file the residue of the clause is the affine-base case alone.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeFiniteType`'s
  `isFiniteType_rightDerived_of_forall_isAffineOpen`: finiteness of type of `R ᵈ f_* F` is local
  on the base, in the `ℕ`-indexing the tag uses, for a quasi-compact quasi-separated `f` and a
  quasi-coherent `F`.
* `…isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase`: **the
  finite-type clause of [Stacks, Tag 0EX4] over an arbitrary base, from its own affine case** —
  the tag's statement with the base of the assumed case restricted to be affine, and with the
  fibre-dimension bound transported to the restricted morphism.
* `…forall_isFiniteType_rightDerived_iff_forall_isAffineBase`: **the two are equivalent.** The
  forward direction is instantiation; so the reduction is not a weakening.

## Implementation notes

**No `@[stacks 0EX4]` attribute is attached to anything here.** Every statement below either
carries the affine case as a hypothesis or is an equivalence between two families, and none of
them asserts the tag. The quasi-coherence clause of the tag is tagged in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcqs/Qcqs.lean`; the finite-type clause
carries one over a locally Noetherian base in
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/NoetherianBaseUnconditional.lean`.

**The `ℕ`- and `ℤ`-indexings are bridged twice, in opposite directions.**
`Stacks.DerivedIndexing.rightDerivedIso F n` runs from `F.rightDerived n` to
`F.rightDerivedPlus ↑n`, so the hypothesis of
`isFiniteType_rightDerived_of_forall_isAffineOpen` is transported along it as it stands and its
conclusion along its `symm`. `Stacks.SheafOfModules.isFiniteType_of_iso` carries finiteness of
type across either.

**Properness of `f` is used only through its two consequences.** The locality statement needs
`AlgebraicGeometry.QuasiCompact f` and `AlgebraicGeometry.QuasiSeparated f`; the fibre transport
needs `AlgebraicGeometry.LocallyOfFiniteType f`. All three are instances of `IsProper f`, and
`IsProper (f ∣_ V)` is found by instance search, so the assumed affine case may be stated for a
proper morphism without weakening.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.ProperCohomologyFinite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

attribute [local instance] HasDerivedCategory.standard

/-! ### Finiteness of type of a higher direct image is local on the base -/

/-- **Finiteness of type of `R ᵈ f_* F` is local on the base, in the `ℕ`-indexing.** If
`R ᵈ (f ∣_ V)_*` of the restriction of `F` is of finite type for every affine open `V` of `Y`,
then `R ᵈ f_* F` is of finite type.

This is `…ProperCohomologyFinite.isFiniteType_rightDerivedPlus_of_forall_isAffineOpen` — the
first sentence of the source's proof, that the question is local on the base — read through
`Stacks.DerivedIndexing.rightDerivedIso` at both ends, because [Stacks, Tag 0EX4] is stated for
`CategoryTheory.Functor.rightDerived`. No hypothesis on the fibres of `f` and none on `Y`. -/
theorem isFiniteType_rightDerived_of_forall_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (d : ℕ)
    (h : ∀ V : Y.affineOpens,
      (((Scheme.Modules.pushforward (f ∣_ (V : Y.Opens))).rightDerived d).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : Y.Opens)).ι).obj F)).IsFiniteType) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType := by
  have := isFiniteType_rightDerivedPlus_of_forall_isAffineOpen f F d fun V => by
    have := h V
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward (f ∣_ (V : Y.Opens))) d).app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : Y.Opens)).ι).obj F))
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) d).app F).symm

/-! ### The finite-type clause of Tag 0EX4 from its affine case -/

/-- **The finite-type clause of [Stacks, Tag 0EX4] over an arbitrary base, from its own affine
case.** For `f : X ⟶ Y` proper whose fibres all have dimension at most `d` and `F` quasi-coherent
of finite type, `R ᵈ f_* F` is of finite type as soon as the same conclusion is granted for every
proper morphism onto an **affine** base all of whose fibres have dimension at most `d`.

Both hypotheses of the assumed case have to be produced for `f ∣_ V`. Properness is instance
search; the fibre-dimension bound is
`AlgebraicGeometry.topologicalKrullDim_fiber_morphismRestrict_le`, the fibres of `f ∣_ V` over
points of `V` being the fibres of `f` ([Stacks, Tag 02FY] part (1)). The restricted module is
quasi-coherent by `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor` and of
finite type by `…CoherentTFAE.isFiniteType_restrict`.

No `@[stacks 0EX4]` attribute: `haff` is a hypothesis the tag does not carry. -/
theorem isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (haff : ∀ (X₀ Y₀ : Scheme.{u}) (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
        ∀ G : X₀.Modules, G.IsQuasicoherent → G.IsFiniteType →
          (((Scheme.Modules.pushforward g).rightDerived d).obj G).IsFiniteType) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType := by
  refine isFiniteType_rightDerived_of_forall_isAffineOpen f F d fun V => ?_
  exact haff _ _ (f ∣_ (V : Y.Opens)) inferInstance V.2
    (topologicalKrullDim_fiber_morphismRestrict_le f (V : Y.Opens) d (fun y _ => hdim y))
    _ (Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ (V : Y.Opens)).ι F)
    (isFiniteType_restrict (f ⁻¹ᵁ (V : Y.Opens)).ι F)

/-! ### The reduction is an equivalence -/

/-- **The finite-type clause of [Stacks, Tag 0EX4] is equivalent to its own affine-base case.**
Each side is quantified over all of its own data; the right-hand side adds `IsAffine Y` and
nothing else.

The forward direction is instantiation, so the reduction proved above is not a weakening: an
arbitrary base contributes nothing to the clause beyond an affine one. Together with
`…TopDegreeFiniteType.forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology`, which
identifies the clause over a *locally Noetherian* base with [Stacks, Tag 02O6], this locates the
whole of what the tag asks beyond that theorem in one place: a proper morphism onto `Spec R` for
a ring `R` with no Noetherian hypothesis. -/
theorem forall_isFiniteType_rightDerived_iff_forall_isAffineBase :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsProper f → ∀ d : ℕ,
        (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) →
          ∀ F : X.Modules, F.IsQuasicoherent → F.IsFiniteType →
            (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType) ↔
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsProper f → IsAffine Y → ∀ d : ℕ,
        (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) →
          ∀ F : X.Modules, F.IsQuasicoherent → F.IsFiniteType →
            (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType) := by
  refine ⟨fun h X Y f hf _ => h X Y f hf, fun h X Y f _ d hdim F _ _ => ?_⟩
  exact isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase f d hdim F
    fun X₀ Y₀ g hg hY₀ => h X₀ Y₀ g hg hY₀ d

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
