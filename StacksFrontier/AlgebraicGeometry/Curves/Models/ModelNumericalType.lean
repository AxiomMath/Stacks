module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaSpecialFiber
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
import StacksCore.Tactic.StacksAttribute

/-!
# The numerical type of a regular proper model

In the situation of [Stacks, Tag 0C61] let `C₁, …, Cₙ` be the irreducible components of the
special fibre of a regular proper model `X ⟶ Spec(R)`, let `mᵢ` be their multiplicities,
`κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})` and `gᵢ` the genus of `Cᵢ`. [Stacks, Tag 0CA4] asserts that the data

`n, mᵢ, (Cᵢ · Cⱼ), [κᵢ : k], gᵢ`

is a numerical type in the sense of [Stacks, Tag 0C6Z] whose genus is the genus of `C`.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.specialFiberNumericalType` — **the numerical type
  of the model**, with all fourteen fields of `AlgebraicGeometry.NumericalType` supplied.
* `Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix` — the intersection
  matrix `(C_Z · C_Y) = deg(𝒪_X(C_Y)|_{C_Z})` of the special fibre.
* `Stacks.Models.RegularProperModelSituation.specialFiberComponentGenus` — the component genus
  `g_Z`, the genus of `C_Z` over its own field of global functions.

The numerical type associated to `X` of [Stacks, Tag 0CA5], the numerical type above at the two
families just named with every hypothesis discharged, is
`Stacks.Models.RegularProperModelSituation.associatedNumericalType` in
`StacksFrontier/AlgebraicGeometry/Curves/Models/AssociatedNumericalType.lean`: discharging the
hypotheses uses the symmetry and the properties of the intersection matrix proved in
`StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean` and
`StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberIntersectionForm.lean`, which build on
this file.

## Main results

* `Stacks.Models.RegularProperModelSituation.specialFiberComponentWeight_dvd_componentDegree`
  and `..._dvd_specialFiberDivisorDegree` — `[κᵢ : k]` divides the degree on `Cᵢ` of any
  invertible module on the model, which is the `weight_dvd_intersection` law. This is
  [Stacks, Tag 0C6P] at the component.
* `Stacks.Models.RegularProperModelSituation.specialFiberNumericalType_componentCount`,
  `..._multiplicity`, `..._intersection`, `..._weight`, `..._componentGenus` — the five families
  of the numerical type are the model's data, so that what has been built can be checked against
  the statement of the tag.
* `Stacks.Models.RegularProperModelSituation.genus_specialFiberNumericalType` — a conditional
  helper: the genus of that numerical type is the genus of `C`, given the three inputs of the
  genus formula as hypotheses.
* `Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix_eq_of_expansion` —
  the abstract matrix `N` of Tag 0CA4 *is* the geometric one, so instantiating it loses nothing.

## Implementation notes

**The index set.** `AlgebraicGeometry.NumericalType` is indexed by `Fin n`, while the components
of the special fibre carry no ordering: they are
`irreducibleComponents S.specialFiber`. An enumeration `e : Fin n ≃ irreducibleComponents X_k`
is therefore an argument, and the five families of the numerical type are the model's data read
through `e`. Nothing is chosen: `e` is given, and
no field is obtained by `Classical.choose` of an existence statement.

**Which of the fourteen fields are proved and which are hypotheses.** For the general
`Stacks.Models.RegularProperModelSituation.specialFiberNumericalType` nine laws are proved and
three come from the hypotheses `hm`, `hoffDiag` and `hconnected` (with `hdec` the decomposition
`X_k = Σ mᵢCᵢ`). For the numerical type associated to `X`,
`Stacks.Models.RegularProperModelSituation.associatedNumericalType`, every hypothesis is
discharged: `hdec` and `hm` by part (3) of [Stacks, Tag 0C5Z]
(`Stacks.Models.RegularModelSituation.specialFiberIdeal_eq_prod`,
`Stacks.Models.RegularModelSituation.specialFiberMultiplicity_pos`), `hexpand` by additivity of
the degree ([Stacks, Tag 0AYX]), `hsymm` by the symmetry of the intersection numbers, and
`hoffDiag` and `hconnected` by parts (1) and (3) of [Stacks, Tag 0C66].

**The intersection matrix.** As in
`Stacks.Models.sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion`, it is an abstract
family `N` pinned by the bilinear expansion `hexpand` of [Stacks, Tag 0AYX]; `hsymm` is
[Stacks, Tag 0C65]. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Curves/Models/GenusFormulaSpecialFiber.lean`.

**The genus clause is [Stacks, Tag 0CA3] and nothing more.** The helper here,
`genus_specialFiberNumericalType`, transports
`Stacks.Models.RegularProperModelSituation.cast_genus_eq_sum_specialFiberComponents` along `e`
and compares with `AlgebraicGeometry.NumericalType.cast_genus`, taking the three inputs of the
genus formula — `hrec`, `hbasic`, `hchi` — as hypotheses. Tag 0CA3 itself is proved
unconditionally in `StacksFrontier/AlgebraicGeometry/Curves/Models/GenusFormulaModel.lean`, as
`Stacks.Models.RegularProperModelSituation.cast_genus_eq_one_add_sum_specialFiberComponent`, and
the genus clause of Tag 0CA4 is obtained from it with no hypothesis in
`StacksFrontier/AlgebraicGeometry/Curves/Models/ModelNumericalTypeGenus.lean`, as
`Stacks.Models.RegularProperModelSituation.associatedNumericalType_spec_and_genus`.

## References

* [Stacks Project, Tag 0CA5](https://stacks.math.columbia.edu/tag/0CA5)
* [Stacks Project, Tag 0CA4](https://stacks.math.columbia.edu/tag/0CA4)
* [Stacks Project, Tag 0CA3](https://stacks.math.columbia.edu/tag/0CA3)
* [Stacks Project, Tag 0C70](https://stacks.math.columbia.edu/tag/0C70)
* [Stacks Project, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z)
* [Stacks Project, Tag 0C71](https://stacks.math.columbia.edu/tag/0C71)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 0C62](https://stacks.math.columbia.edu/tag/0C62)
* [Stacks Project, Tag 0C66](https://stacks.math.columbia.edu/tag/0C66)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-! ### The weight divides every degree on the component -/

/-- **`[κᵢ : k]` divides the degree on `Cᵢ` of an invertible module on the model.** This is
clause (1) of [Stacks, Tag 0C6P] at the component: the component is proper over `k`, reduced and
connected because it is integral, and at most one-dimensional, and an invertible module is finite
locally free of rank one. -/
public theorem specialFiberComponentWeight_dvd_componentDegree
    (Z : irreducibleComponents S.specialFiber) (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) :
    (S.specialFiberComponentWeight Z : ℤ) ∣ S.specialFiberComponentDegree Z L hL := by
  rw [specialFiberComponentDegree, componentDegree,
    @invertibleCurveDegree_eq_curveDegree_one S.k _ _ (S.specialFiberComponentToSpec Z)
      (S.isProper_specialFiberComponentToSpec Z) _ _
      (isInvertible_restrict (S.specialFiberComponentIdeal Z) L hL)]
  exact @finrank_globalSections_dvd_curveDegree S.k _ _ (S.specialFiberComponentToSpec Z)
    (S.isProper_specialFiberComponentToSpec Z) _ _ _ _ 1 _

variable [Fintype (irreducibleComponents S.specialFiber)]
  [DecidableEq (irreducibleComponents S.specialFiber)]

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **`[κᵢ : k]` divides `deg(𝒪_X(Σⱼ cⱼCⱼ)|_{Cᵢ})`**, the case of
`Stacks.Models.RegularProperModelSituation.specialFiberComponentWeight_dvd_componentDegree` at
the invertible module of a nonnegative combination of the components. -/
public theorem specialFiberComponentWeight_dvd_specialFiberDivisorDegree
    (Z : irreducibleComponents S.specialFiber)
    (c : irreducibleComponents S.specialFiber → ℕ) :
    (S.specialFiberComponentWeight Z : ℤ) ∣ S.specialFiberDivisorDegree Z c :=
  S.specialFiberComponentWeight_dvd_componentDegree Z _ _

/-- **The bilinear expansion of [Stacks, Tag 0AYX] reads the intersection matrix off as a single
degree**, `N i j = deg(𝒪_X(Cⱼ)|_{Cᵢ})`. -/
public theorem intersectionMatrix_eq_specialFiberDivisorDegree_single
    (N : irreducibleComponents S.specialFiber → irreducibleComponents S.specialFiber → ℤ)
    (hexpand : ∀ c Z, S.specialFiberDivisorDegree Z c = ∑ Y, (c Y : ℤ) * N Z Y)
    (Z Y : irreducibleComponents S.specialFiber) :
    N Z Y = S.specialFiberDivisorDegree Z (Pi.single Y 1) := by
  rw [hexpand, Finset.sum_eq_single_of_mem Y (Finset.mem_univ Y)
    (fun W _ hW => by rw [Pi.single_eq_of_ne hW]; norm_num), Pi.single_eq_same]
  norm_num

/-! ### The numerical type of the model -/

/-- **The numerical type of the model.** In the situation of [Stacks, Tag 0C61] the data
`n, mᵢ, (Cᵢ · Cⱼ), [κᵢ : k], gᵢ` of the special fibre of the model is a numerical type in the
sense of [Stacks, Tag 0C6Z].

The components are enumerated by `e`, the numerical type being indexed by `Fin n`, and the
intersection matrix is the abstract family `N` pinned by the expansion `hexpand` of
[Stacks, Tag 0AYX]. Nine of the fourteen laws are proved; the other three substantive ones are
the hypotheses `hm` (positivity of the multiplicities, [Stacks, Tag 0C5Z]), `hoffDiag`
(nonnegativity of the off-diagonal intersection numbers, the first clause of
[Stacks, Tag 0C66], i.e. the second assertion of [Stacks, Tag 0AYY]) and `hconnected`
(connectedness of the intersection graph, which the source deduces from [Stacks, Tag 0C62]
*through* `hoffDiag`). See the module documentation. -/
public def specialFiberNumericalType (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (m : irreducibleComponents S.specialFiber → ℕ)
    (N : irreducibleComponents S.specialFiber → irreducibleComponents S.specialFiber → ℤ)
    (gcomp : irreducibleComponents S.specialFiber → ℕ)
    (hdec : S.specialFiberIdeal = ∏ Z, S.specialFiberComponentIdeal Z ^ m Z)
    (hm : ∀ Z, 0 < m Z)
    (hexpand : ∀ c Z, S.specialFiberDivisorDegree Z c = ∑ Y, (c Y : ℤ) * N Z Y)
    (hsymm : ∀ Z Y, N Z Y = N Y Z)
    (hoffDiag : ∀ Z Y, Z ≠ Y → 0 ≤ N Z Y)
    (hconnected : ∀ I : Set (irreducibleComponents S.specialFiber), I.Nonempty →
      I ≠ Set.univ → ¬ ∀ Z ∈ I, ∀ Y ∉ I, N Z Y = 0) :
    AlgebraicGeometry.NumericalType where
  componentCount := n
  componentCount_pos := by
    obtain ⟨Z, -⟩ := exists_multiplicity_ne_zero S
      (fun Y => S.specialFiberComponentIdeal Y) m hdec
    exact (e.symm Z).pos
  multiplicity i := (m (e i) : ℤ)
  intersection i j := N (e i) (e j)
  weight i := (S.specialFiberComponentWeight (e i) : ℤ)
  componentGenus i := (gcomp (e i) : ℤ)
  multiplicity_pos i := Int.natCast_pos.2 (hm (e i))
  weight_pos i := Int.natCast_pos.2 (S.specialFiberComponentWeight_pos (e i))
  componentGenus_nonneg i := Int.natCast_nonneg _
  intersection_symm i j := hsymm (e i) (e j)
  intersection_nonneg i j hij := hoffDiag (e i) (e j) (fun h => hij (e.injective h))
  connected := by
    rintro ⟨I, hIne, hIuniv, hzero⟩
    refine hconnected (e.symm ⁻¹' I) ?_ ?_ ?_
    · obtain ⟨i, hi⟩ := hIne
      exact ⟨e i, by simpa using hi⟩
    · intro h
      exact hIuniv (Set.eq_univ_of_forall fun i => by
        simpa using (Set.eq_univ_iff_forall.1 h) (e i))
    · intro Z hZ Y hY
      simpa using hzero (e.symm Z) hZ (e.symm Y) hY
  intersection_mul_multiplicity i :=
    calc ∑ j, N (e i) (e j) * (m (e j) : ℤ)
        = ∑ Y, N (e i) Y * (m Y : ℤ) :=
          Fintype.sum_equiv e _ (fun Y => N (e i) Y * (m Y : ℤ)) (fun _ => rfl)
      _ = ∑ Y, (m Y : ℤ) * N (e i) Y := Finset.sum_congr rfl fun Y _ => mul_comm _ _
      _ = 0 := sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion S
          (fun Y => S.specialFiberComponentIdeal Y) (fun Y => S.specialFiberComponentToSpec Y)
          (fun Y => S.isProper_specialFiberComponentToSpec Y)
          (fun Y => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Y) N m
          (fun Y => S.isEffectiveCartierDivisor_specialFiberComponent Y) hexpand hdec (e i)
  weight_dvd_intersection i j := by
    rw [S.intersectionMatrix_eq_specialFiberDivisorDegree_single N hexpand]
    exact S.specialFiberComponentWeight_dvd_specialFiberDivisorDegree (e i) _

section Fields

variable (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
  (m : irreducibleComponents S.specialFiber → ℕ)
  (N : irreducibleComponents S.specialFiber → irreducibleComponents S.specialFiber → ℤ)
  (gcomp : irreducibleComponents S.specialFiber → ℕ)
  (hdec : S.specialFiberIdeal = ∏ Z, S.specialFiberComponentIdeal Z ^ m Z)
  (hm : ∀ Z, 0 < m Z)
  (hexpand : ∀ c Z, S.specialFiberDivisorDegree Z c = ∑ Y, (c Y : ℤ) * N Z Y)
  (hsymm : ∀ Z Y, N Z Y = N Y Z)
  (hoffDiag : ∀ Z Y, Z ≠ Y → 0 ≤ N Z Y)
  (hconnected : ∀ I : Set (irreducibleComponents S.specialFiber), I.Nonempty →
    I ≠ Set.univ → ¬ ∀ Z ∈ I, ∀ Y ∉ I, N Z Y = 0)

/-- The numerical type of the model has one component for each irreducible component of the
special fibre. -/
@[simp] public theorem specialFiberNumericalType_componentCount :
    (S.specialFiberNumericalType n e m N gcomp hdec hm hexpand hsymm hoffDiag
      hconnected).componentCount = n := rfl

/-- The multiplicities of the numerical type of the model are the multiplicities `mᵢ` of the
components of the special fibre. -/
@[simp] public theorem specialFiberNumericalType_multiplicity (i : Fin n) :
    (S.specialFiberNumericalType n e m N gcomp hdec hm hexpand hsymm hoffDiag
      hconnected).multiplicity i = (m (e i) : ℤ) := rfl

/-- The intersection matrix of the numerical type of the model is `(Cᵢ · Cⱼ)`. -/
@[simp] public theorem specialFiberNumericalType_intersection (i j : Fin n) :
    (S.specialFiberNumericalType n e m N gcomp hdec hm hexpand hsymm hoffDiag
      hconnected).intersection i j = N (e i) (e j) := rfl

/-- The weights of the numerical type of the model are the degrees `[κᵢ : k]`. -/
@[simp] public theorem specialFiberNumericalType_weight (i : Fin n) :
    (S.specialFiberNumericalType n e m N gcomp hdec hm hexpand hsymm hoffDiag
      hconnected).weight i = (S.specialFiberComponentWeight (e i) : ℤ) := rfl

/-- The component genera of the numerical type of the model are the genera `gᵢ`. -/
@[simp] public theorem specialFiberNumericalType_componentGenus (i : Fin n) :
    (S.specialFiberNumericalType n e m N gcomp hdec hm hexpand hsymm hoffDiag
      hconnected).componentGenus i = (gcomp (e i) : ℤ) := rfl

/-- **The genus of the numerical type of the model, conditionally.** The genus of the numerical
type of the model is the genus of the generic curve `C`, given the three inputs of the genus
formula as hypotheses.

This is [Stacks, Tag 0CA3] — `cast_genus_eq_sum_specialFiberComponents` — transported along the
enumeration `e` and compared with `AlgebraicGeometry.NumericalType.cast_genus`, so it carries
exactly the three hypotheses of that tag: `hrec`, the recursion of [Stacks, Tag 0CA2]; `hbasic`,
the identity `1 - g_C = χ(X_k, 𝒪_{X_k})` of [Stacks, Tag 0B9T]; and `hchi`, the identity
`χ(Cᵢ, 𝒪_{Cᵢ}) = [κᵢ : k](1 - gᵢ)`. See the module documentation. -/
public theorem genus_specialFiberNumericalType
    (chi : irreducibleComponents S.specialFiber → ℤ) (gC : ℤ)
    (E : (irreducibleComponents S.specialFiber → ℕ) → ℤ)
    (hrec : S.SpecialFiberEulerRecursion chi E)
    (hbasic : 1 - gC = E m)
    (hchi : ∀ Z, chi Z = (S.specialFiberComponentWeight Z : ℤ) * (1 - (gcomp Z : ℤ))) :
    (S.specialFiberNumericalType n e m N gcomp hdec hm hexpand hsymm hoffDiag
      hconnected).genus = gC := by
  have hq : ((S.specialFiberNumericalType n e m N gcomp hdec hm hexpand hsymm hoffDiag
      hconnected).genus : ℚ) = (gC : ℚ) := by
    rw [AlgebraicGeometry.NumericalType.cast_genus,
      S.cast_genus_eq_sum_specialFiberComponents m N chi (fun Z => (gcomp Z : ℤ)) gC E hdec
        hexpand hsymm hrec hbasic hchi]
    refine congrArg (fun x : ℚ => 1 + x) ?_
    refine Fintype.sum_equiv e _ _ (fun i => ?_)
    simp only [specialFiberNumericalType_multiplicity, specialFiberNumericalType_weight,
      specialFiberNumericalType_componentGenus, specialFiberNumericalType_intersection]
    push_cast
    ring
  exact_mod_cast hq

end Fields

/-! ### The two families of the numerical type associated to the model

[Stacks, Tag 0CA5] names the numerical type of [Stacks, Tag 0CA4] *the numerical type associated
to `X`*. Its abstract intersection matrix `N` is the geometric matrix
`(C_Z · C_Y) = deg(𝒪_X(C_Y)|_{C_Z})` — the very matrix the expansion `hexpand` pins `N` to — and
its abstract component genus `gcomp` is the genus of the component over its own field of global
functions. Both are defined here; the numerical type itself is
`Stacks.Models.RegularProperModelSituation.associatedNumericalType`.
-/

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **The component genus `g_Z` of an irreducible component of the special fibre**: the genus of
`C_Z` as a curve over its own field of global functions `κ_Z = Γ(C_Z, 𝒪_{C_Z})`, taken through
the canonical morphism `C_Z ⟶ Spec(κ_Z)`.

The genus of the source is a `κ_Z`-dimension, not a `k`-dimension: the proof of
[Stacks, Tag 0CA3] uses `χ(C_Z, 𝒪_{C_Z}) = [κ_Z : k](1 - g_Z)`, which for `[κ_Z : k] > 1` is
false for the `k`-dimension. That `κ_Z` is a field is [Stacks, Tag 0C6P] at the component, in the
form `RegularProperModelSituation.isField_and_finite_globalSections_specialFiberComponent`. -/
public def specialFiberComponentGenus (Z : irreducibleComponents S.specialFiber) : ℕ :=
  letI := (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
  AlgebraicGeometry.genus (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ

/-- **The intersection matrix `(C_Z · C_Y) = deg(𝒪_X(C_Y)|_{C_Z})` of the special fibre**: the
degree on `C_Z` of the invertible module of the single component `C_Y`.

This is the matrix to which the abstract family `N` of
`Stacks.Models.RegularProperModelSituation.specialFiberNumericalType` is pinned by the expansion
`hexpand` of [Stacks, Tag 0AYX] — see
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix_eq_of_expansion`. -/
public def specialFiberIntersectionMatrix
    (Z Y : irreducibleComponents S.specialFiber) : ℤ :=
  S.specialFiberDivisorDegree Z (Pi.single Y 1)

/-- **The abstract intersection matrix of [Stacks, Tag 0CA4] is the geometric one.** Any family
`N` satisfying the bilinear expansion of [Stacks, Tag 0AYX] is `(C_Z · C_Y)`, so replacing `N` by
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix` below loses nothing:
it only writes down the matrix that `hexpand` had already determined. -/
public theorem specialFiberIntersectionMatrix_eq_of_expansion
    (N : irreducibleComponents S.specialFiber → irreducibleComponents S.specialFiber → ℤ)
    (hexpand : ∀ c Z, S.specialFiberDivisorDegree Z c = ∑ Y, (c Y : ℤ) * N Z Y)
    (Z Y : irreducibleComponents S.specialFiber) :
    N Z Y = S.specialFiberIntersectionMatrix Z Y :=
  S.intersectionMatrix_eq_specialFiberDivisorDegree_single N hexpand Z Y

end RegularProperModelSituation

end Stacks.Models

end
