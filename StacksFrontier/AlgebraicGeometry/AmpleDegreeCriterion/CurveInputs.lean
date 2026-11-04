module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Curve
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Components
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IntegralGenericWitness
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inputs of Tag 0B5X on a proper curve, proved

`AlgebraicGeometry.isAmple_iff_degree_pos` of `./Curve.lean` reaches both directions of
[Stacks, Tag 0B5X] from five inputs. Four of them are theorems of this library, and this file
proves each of the four at exactly the shape that statement asks for, so that the forward
direction of the tag — an ample invertible module on a proper curve over a field has positive
degree — holds with no hypothesis beyond the tag's own.

## Main results

* `AlgebraicGeometry.coherentDevissage_of_isCurve`: the dévissage of [Stacks, Tag 01YH] on a
  proper curve: a two-out-of-three property of coherent modules which holds on the modules
  supported in a proper closed subset and on `𝒪_X` holds on every coherent module.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_closed_supp`: [Stacks, Tag 02O6]
  at the coherent modules supported in a proper closed subset.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_unit_of_isProper`:
  [Stacks, Tag 02O6] at the structure sheaf.
* `AlgebraicGeometry.invertibleCurveDegree_tensorPower_pos_of_nonvanishingLocus_ne_univ`:
  [Stacks, Tag 0B40] part (2), at the positive tensor powers.
* `AlgebraicGeometry.hasCurveDegreePositivityInputs_of_isCurve`: the four together, in the
  bundled form `AlgebraicGeometry.HasCurveDegreePositivityInputs` of `./Components.lean`.
* `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_isCurve`: **the forward direction
  of [Stacks, Tag 0B5X]**, at the source's hypotheses and with nothing assumed.
* `AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul_of_isCurve`:
  `deg(𝓛^{⊗ n}) = n · deg(𝓛)` on a proper curve, the invertible case of [Stacks, Tag 0AYX],
  with nothing assumed.
* `AlgebraicGeometry.isAmple_iff_degree_pos_of_vanishing`: both directions of
  [Stacks, Tag 0B5X] from the source's second and third paragraphs alone.
* `AlgebraicGeometry.isZero_cohomologyOverField_two_le`: Grothendieck vanishing
  ([Stacks, Tag 02UZ]) on a proper curve, at the degree bound the Euler characteristic uses.
* `AlgebraicGeometry.le_finrank_cohomologyOverField_zero_tensorPower`: **the opening line of
  the converse**, `n · deg(𝓛) + χ(X, 𝒪_X) ≤ dim_k H⁰(X, 𝓛^{⊗ n})`, with nothing assumed.

## How each input is proved

**The dévissage.** A curve is integral, being a variety, and it is Noetherian: properness gives
quasi-compactness and finite type gives local Noetherianness. On an integral Noetherian scheme
the dévissage is `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_isIntegral`
— [Stacks, Tag 01YI] with its family of generic test objects supplied, which is the form
[Stacks, Tag 01YH] takes when the ambient space is irreducible with `𝒪_X` as the generic test
object.

**Finite dimensionality.** [Stacks, Tag 02O6] over a field is
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`, which asks only
that the module be coherent. The two instances the forward direction uses differ only in how
coherence is obtained: `hclosed` is handed it, and at the structure sheaf it is
`Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent`, available because a
scheme of finite type over a field is locally Noetherian. Neither instance uses the hypothesis
on the support, which is why the statement below discards it.

**Positivity from a section.** [Stacks, Tag 0B40] part (2) is
`AlgebraicGeometry.invertibleCurveDegree_pos_of_eval_top_ne_zero`: a nonzero global section of
an invertible module on a proper integral scheme of dimension at most one which vanishes
somewhere forces the degree positive. The shape asked for here speaks of the nonvanishing locus
instead of the section's value, and the two translations are
`AlgebraicGeometry.eval_top_ne_zero_of_mem_nonvanishingLocus` — a section not vanishing at a
point is nonzero — and `Set.ne_univ_iff_exists_notMem`.

## Implementation notes

**The degree of a tensor power is no longer conditional.**
`AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul_of_devissage` of
`../CurveDegreeTensor/Basic.lean` takes the dévissage and the two finiteness inputs in exactly
the shapes proved here, so `deg(𝓛^{⊗ n}) = n · deg(𝓛)` follows with nothing assumed.

**What the converse still needs** is the `hvan` of
`AlgebraicGeometry.isAmple_iff_degree_pos`: the source's second paragraph, which turns the
growth of `h⁰` recorded below into a global section of some `𝓛^{⊗ n}` whose nonvanishing locus
is affine, and its third paragraph, which turns such a section into the vanishing of
`H¹(X, ℐ ⊗ 𝓛^{⊗ e n})`. `isAmple_iff_degree_pos_of_vanishing` below is the biconditional with
the other four inputs substituted, so it rests on those two paragraphs alone.

**Grothendieck vanishing needs no hypothesis here.**
`AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le` of
`../Curves/VanishingResults/DualizingExtension.lean` is [Stacks, Tag 02UZ] in the
`cohomologyOverField` spelling, for a proper scheme over a field of dimension at most `d` and
degrees above `d`. Several files in this tree carry the one-dimensional case as a hypothesis —
`AlgebraicGeometry.HasVanishingAboveDimensionOne` of `../Curves/LargeDegreeVanishing.lean` is
one — and `isZero_cohomologyOverField_two_le` below is that theorem instantiated at `d = 1`.

**The `h⁰` bound avoids the Euler characteristic.**
`AlgebraicGeometry.eulerCharacteristic` carries a coherence instance argument, and the
coherence of `𝓛^{⊗ n}` is not found by instance search at the `tensorPower` spelling. The
bound below is therefore read off
`AlgebraicGeometry.invertibleCurveDegree_eq_sub_of_isZero`, which states the degree as
`(h⁰ - h¹) - (h⁰(𝒪_X) - h¹(𝒪_X))` in `Module.finrank` and needs only the two vanishings, so no
coherence instance appears.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (nonvanishingLocus)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A scheme proper and of finite type over a field is Noetherian.** Finite type gives local
Noetherianness and properness gives a compact space. -/
public theorem isNoetherian_of_isProper_of_locallyOfFiniteType [IsProper f] : IsNoetherian X :=
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  AlgebraicGeometry.IsNoetherian.mk

/-- **The dévissage of [Stacks, Tag 01YH] on a proper curve.** Let `P` be a property of coherent
`𝒪_X`-modules such that two out of three in a short exact sequence of coherent modules force the
third, which holds on every module supported in a proper closed subset of `X` and which holds on
`𝒪_X`. Then `P` holds on every coherent `𝒪_X`-module.

A curve is integral and, being proper and of finite type over the field, Noetherian; on such a
scheme this is `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_isIntegral`.

This is the `hdev` of `AlgebraicGeometry.isAmple_iff_degree_pos`, written at that statement's
shape. -/
public theorem coherentDevissage_of_isCurve [IsCurve k f] [IsProper f] :
    ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G :=
  have _ : IsNoetherian X := isNoetherian_of_isProper_of_locallyOfFiniteType k f
  fun P hexact hproper hunit =>
    Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_isIntegral X P hexact
      hproper hunit

/-- **[Stacks, Tag 02O6] at a coherent module supported in a proper closed subset.** Over a
field the finite dimensionality holds for every coherent module, so the condition on the support
is not used; it is present because this is the `hclosed` of
`AlgebraicGeometry.isAmple_iff_degree_pos`, written at that statement's shape. -/
public theorem finiteDimensional_cohomologyOverField_of_closed_supp [IsProper f] :
    ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m) :=
  fun G _ _ _ _ hG m => forall_finiteDimensional_cohomologyOverField_of_isProper k f G hG m

/-- **[Stacks, Tag 02O6] at the structure sheaf.** A scheme proper over a field is locally
Noetherian, so its structure sheaf is coherent and the finite dimensionality over a field
applies.

This is the `hunit` of `AlgebraicGeometry.isAmple_iff_degree_pos`. -/
@[sga "4½ Fonctions_L 3.7" "special case"]
public theorem forall_finiteDimensional_cohomologyOverField_unit_of_isProper [IsProper f] :
    ∀ m, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m) :=
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  fun m => forall_finiteDimensional_cohomologyOverField_of_isProper k f _
    (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X) m

/-- **[Stacks, Tag 0B40] part (2) at the positive tensor powers of an invertible module.** A
global section of `𝓛^{⊗ n}` whose nonvanishing locus is nonempty but not everything forces
`deg(𝓛^{⊗ n}) > 0`.

Part (2) asks for a nonzero section vanishing at a point: the section is nonzero because it does
not vanish at some point, and it vanishes at a point because its nonvanishing locus is not the
whole space.

This is the `hpos` of `AlgebraicGeometry.isAmple_iff_degree_pos`. -/
public theorem invertibleCurveDegree_tensorPower_pos_of_nonvanishingLocus_ne_univ [IsCurve k f]
    [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∀ n : ℕ, 1 ≤ n → ∀ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        (∃ x : X, x ∈ nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) →
        nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ≠ Set.univ →
        0 < @invertibleCurveDegree k _ X f _ hdim
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ))
          (tensorPower_isInvertible X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) := by
  intro n _ s ⟨x, hx⟩ hne
  exact invertibleCurveDegree_pos_of_eval_top_ne_zero
    (hL := tensorPower_isInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (n : ℤ)) k f hdim _ s
    (eval_top_ne_zero_of_mem_nonvanishingLocus _ s hx)
    (Set.ne_univ_iff_exists_notMem _ |>.mp hne)

/-- **`deg(𝓛^{⊗ n}) = n · deg(𝓛)` on a proper curve over a field**, for every integer `n`.

This is `AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul_of_devissage` with its three
inputs supplied by the theorems above, so the invertible case of [Stacks, Tag 0AYX] holds here
with nothing assumed. -/
public theorem invertibleCurveDegree_tensorPower_eq_mul_of_isCurve [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (n : ℤ) :
    @invertibleCurveDegree k _ X f _ hdim
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n)
        (tensorPower_isInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n) =
      n * invertibleCurveDegree k f hdim L :=
  invertibleCurveDegree_tensorPower_eq_mul_of_devissage k f (coherentDevissage_of_isCurve k f)
    (finiteDimensional_cohomologyOverField_of_closed_supp k f)
    (forall_finiteDimensional_cohomologyOverField_unit_of_isProper k f) hdim L n

/-- **The forward direction of [Stacks, Tag 0B5X], at the source's hypotheses.** On a proper
curve over a field an ample invertible module has positive degree.

This is `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_devissage` with each of its
four inputs supplied by the theorems above.

The converse implication is `AlgebraicGeometry.isAmple_iff_invertibleCurveDegree_pos` of
`CurveAmple.lean`, which states both directions. -/
@[stacks 0B5X "the implication: `L` ample ⟹ `deg(L) > 0`, with no hypothesis beyond the tag's \
own; both directions are registered on `isAmple_iff_invertibleCurveDegree_pos`"]
public theorem invertibleCurveDegree_pos_of_isAmple_of_isCurve [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    0 < invertibleCurveDegree k f hdim L :=
  invertibleCurveDegree_pos_of_isAmple_of_devissage k f (coherentDevissage_of_isCurve k f)
    (finiteDimensional_cohomologyOverField_of_closed_supp k f)
    (forall_finiteDimensional_cohomologyOverField_unit_of_isProper k f) hdim L
    (invertibleCurveDegree_tensorPower_pos_of_nonvanishingLocus_ne_univ k f hdim L) hL

/-- **The four inputs of the forward direction, in their bundled form.** This inhabits
`AlgebraicGeometry.HasCurveDegreePositivityInputs` on every proper curve over a field, so the
statements of `./Components.lean` that take it as a hypothesis hold outright. -/
public theorem hasCurveDegreePositivityInputs_of_isCurve {C : Scheme.{u}} (g : C ⟶ Spec (.of k))
    [IsCurve k g] [IsProper g] (hdim : topologicalKrullDim C ≤ 1) (M : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M] :
    HasCurveDegreePositivityInputs k g hdim M :=
  ⟨coherentDevissage_of_isCurve k g, finiteDimensional_cohomologyOverField_of_closed_supp k g,
    forall_finiteDimensional_cohomologyOverField_unit_of_isProper k g,
    invertibleCurveDegree_tensorPower_pos_of_nonvanishingLocus_ne_univ k g hdim M⟩

/-- **Both directions of [Stacks, Tag 0B5X] from the source's third paragraph alone.** The
statement of `AlgebraicGeometry.isAmple_iff_degree_pos` with its other four inputs substituted:
on a proper curve over a field an invertible module is ample exactly when its degree is
positive, given that positivity of the degree yields, for every closed subscheme, a positive
power of `𝓛` killing `H¹` of that subscheme's ideal sheaf twisted by the same power. -/
public theorem isAmple_iff_degree_pos_of_vanishing [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hvan : 0 < invertibleCurveDegree k f hdim L →
      ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → ∃ n : ℕ, 1 ≤ n ∧
        IsZero (((moduleGlobalSections X).rightDerived 1).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
            ((tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ))))))) :
    Scheme.Modules.IsAmple X L ↔ 0 < invertibleCurveDegree k f hdim L :=
  isAmple_iff_degree_pos k f (coherentDevissage_of_isCurve k f)
    (finiteDimensional_cohomologyOverField_of_closed_supp k f)
    (forall_finiteDimensional_cohomologyOverField_unit_of_isProper k f) hdim L
    (invertibleCurveDegree_tensorPower_pos_of_nonvanishingLocus_ne_univ k f hdim L) hvan

/-! ### The growth of `h⁰` along the powers, the opening line of the converse -/

/-- **Grothendieck vanishing on a proper curve, at the shape the Euler characteristic uses.**
The cohomology of every module on a proper scheme of dimension at most one over a field
vanishes in every degree above the first. -/
public theorem isZero_cohomologyOverField_two_le [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (F : X.Modules) (m : ℕ) (hm : 2 ≤ m) :
    IsZero (cohomologyOverField k f F m) :=
  isZero_cohomologyOverField_of_topologicalKrullDim_le k f F (d := 1)
    (by exact_mod_cast hdim) (by omega)

/-- **`h⁰(X, 𝓛^{⊗ n})` grows at least linearly in `n`**, which is the opening line of the "if"
direction of [Stacks, Tag 0B5X]:

`n · deg(𝓛) + h⁰(X, 𝒪_X) - h¹(X, 𝒪_X) ≤ dim_k H⁰(X, 𝓛^{⊗ n})`.

On a proper curve the cohomology vanishes above degree one, so the degree of an invertible
module is `(h⁰ - h¹) - (h⁰(𝒪_X) - h¹(𝒪_X))`; applying that to `𝓛^{⊗ n}`, whose degree is
`n · deg(𝓛)`, and discarding the non-negative `h¹(𝓛^{⊗ n})` gives the bound. The right-hand
side is `χ(X, 𝒪_X)` written out, so when `deg(𝓛) > 0` the left-hand side grows without bound
and `𝓛^{⊗ n}` has a nonzero global section for every large `n`.

Nothing is assumed. -/
public theorem le_finrank_cohomologyOverField_zero_tensorPower [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (n : ℤ) :
    n * invertibleCurveDegree k f hdim L +
          (Module.finrank k
            (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) : ℤ) -
        (Module.finrank k
          (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ) ≤
      (Module.finrank k (cohomologyOverField k f
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n) 0) : ℤ) := by
  have hdeg := invertibleCurveDegree_tensorPower_eq_mul_of_isCurve k f hdim L n
  have hsub := @invertibleCurveDegree_eq_sub_of_isZero k _ X f _ hdim _
    (tensorPower_isInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L n)
    (isZero_cohomologyOverField_two_le k f hdim _)
    (isZero_cohomologyOverField_two_le k f hdim _)
  have hnn : (0 : ℤ) ≤ (Module.finrank k (cohomologyOverField k f
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L n) 1) : ℤ) := Int.natCast_nonneg _
  linarith [hdeg, hsub, hnn]

end AlgebraicGeometry

end
