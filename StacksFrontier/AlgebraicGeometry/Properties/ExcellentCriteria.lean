module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.AlgebraicGeometry.Properties.Excellent
public import StacksFrontier.AlgebraicGeometry.Properties.GScheme
public import StacksFrontier.AlgebraicGeometry.RecoveryCatenary.LocalCriteria
public import StacksFrontier.AlgebraicGeometry.SchemeJTwoLocal.JTwoTFAE

/-!
# Criteria for quasi-excellent and excellent schemes

A scheme is quasi-excellent exactly when it is a G-scheme and J-2, and excellent exactly when it
is quasi-excellent and universally catenary. Both conditions are local: they hold on every affine
open, or on the members of one affine open covering, or on the members of one open covering,
and they pass to open subschemes. A quasi-excellent scheme is Nagata.

## Main results

* `AlgebraicGeometry.isQuasiExcellentScheme_iff_exists_isGScheme_isJ2`: a scheme is
  quasi-excellent if and only if it is a G-scheme and J-2.
* `AlgebraicGeometry.IsQuasiExcellentScheme.isNagataScheme`: a quasi-excellent scheme is Nagata.
* `AlgebraicGeometry.isExcellentScheme_iff_exists_isQuasiExcellentScheme_isUniversallyCatenary`:
  a scheme is excellent if and only if it is quasi-excellent and universally catenary.
* `AlgebraicGeometry.isQuasiExcellentScheme_tfae` and `AlgebraicGeometry.isExcellentScheme_tfae`:
  the local characterizations of (quasi-)excellence.
* `AlgebraicGeometry.IsQuasiExcellentScheme.restrict` and
  `AlgebraicGeometry.IsExcellentScheme.restrict`: every open subscheme of a (quasi-)excellent
  scheme is (quasi-)excellent.

## Implementation notes

The J-2 condition `AlgebraicGeometry.Scheme.IsJ2` and universal catenarity
`AlgebraicGeometry.Scheme.IsUniversallyCatenary` are only defined for a locally Noetherian
scheme. In the characterization of quasi-excellent schemes the J-2 condition refers to the local
Noetherianity supplied by the G-scheme condition, and in the characterization of excellent
schemes universal catenarity refers to the local Noetherianity supplied by quasi-excellence.
The variants `isQuasiExcellentScheme_iff_isGScheme_and_isJ2` and
`isExcellentScheme_iff_isQuasiExcellentScheme_and_isUniversallyCatenary` are the same statements
for a scheme already known to be locally Noetherian.

A covering is a family of opens whose supremum is `⊤`, indexed by a type in the universe of the
scheme, as in `AlgebraicGeometry.isGScheme_tfae_cover` and `AlgebraicGeometry.Scheme.isJ2_tfae`.

## References

* [Stacks Project, Tag 0HA8](https://stacks.math.columbia.edu/tag/0HA8)
* [Stacks Project, Tag 0HA9](https://stacks.math.columbia.edu/tag/0HA9)
* [Stacks Project, Tag 0HAA](https://stacks.math.columbia.edu/tag/0HAA)
* [Stacks Project, Tag 0HAB](https://stacks.math.columbia.edu/tag/0HAB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- An excellent scheme is quasi-excellent. -/
theorem IsExcellentScheme.isQuasiExcellentScheme (h : IsExcellentScheme X) :
    IsQuasiExcellentScheme X := fun x =>
  (h x).imp fun _ hU => ⟨hU.1, hU.2.1⟩

/-- A scheme covered by affine opens whose rings of sections are quasi-excellent is
quasi-excellent. -/
theorem isQuasiExcellentScheme_of_iSup_eq_top {ι : Type*} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) (hS' : ∀ i, IsQuasiExcellent Γ(X, S i)) :
    IsQuasiExcellentScheme X := fun x => by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hS ▸ trivial : x ∈ ⨆ i, (S i : X.Opens))
  exact ⟨S i, hi, hS' i⟩

/-- A scheme covered by affine opens whose rings of sections are excellent is excellent. -/
theorem isExcellentScheme_of_iSup_eq_top {ι : Type*} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) (hS' : ∀ i, IsExcellent Γ(X, S i)) :
    IsExcellentScheme X := fun x => by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hS ▸ trivial : x ∈ ⨆ i, (S i : X.Opens))
  exact ⟨S i, hi, hS' i⟩

/-- A quasi-excellent scheme is locally Noetherian. -/
theorem IsQuasiExcellentScheme.isLocallyNoetherian (h : IsQuasiExcellentScheme X) :
    IsLocallyNoetherian X :=
  isLocallyNoetherian_of_affine_cover (S := fun x => (h x).choose)
    (eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, (h x).choose_spec.1⟩)
    fun x => (h x).choose_spec.2.1

/-- An excellent scheme is locally Noetherian. -/
theorem IsExcellentScheme.isLocallyNoetherian (h : IsExcellentScheme X) :
    IsLocallyNoetherian X :=
  h.isQuasiExcellentScheme.isLocallyNoetherian

/-- A G-scheme is locally Noetherian. -/
theorem IsGScheme.isLocallyNoetherian (h : IsGScheme X) : IsLocallyNoetherian X := by
  have e := (isGScheme_tfae X).out 1 2
  exact (e.mp h).1

/-- A quasi-excellent scheme is a G-scheme. -/
theorem IsQuasiExcellentScheme.isGScheme (h : IsQuasiExcellentScheme X) : IsGScheme X :=
  fun x => (h x).imp fun _ hU => ⟨hU.1, hU.2.2.1⟩

/-- A quasi-excellent scheme is J-2. -/
theorem IsQuasiExcellentScheme.isJ2 (h : IsQuasiExcellentScheme X) :
    letI := h.isLocallyNoetherian
    Scheme.IsJ2 X := by
  let := h.isLocallyNoetherian
  have e := (Scheme.isJ2_tfae X).out 1 4
  exact e.mpr ⟨X, fun x => (h x).choose,
    eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, (h x).choose_spec.1⟩,
    fun x => (h x).choose_spec.2.2.2⟩

/-- A G-scheme which is J-2 is quasi-excellent. -/
theorem IsGScheme.isQuasiExcellentScheme (hG : IsGScheme X)
    (hJ : letI := hG.isLocallyNoetherian; Scheme.IsJ2 X) : IsQuasiExcellentScheme X := by
  let := hG.isLocallyNoetherian
  have e := (Scheme.isJ2_tfae X).out 1 3
  exact fun x => (hG x).imp fun U hU => ⟨hU.1, hU.2.1, hU.2, e.mp hJ U⟩

/-- A scheme is quasi-excellent if and only if it is a G-scheme and J-2. Here the J-2 condition
refers to the local Noetherianity which the G-scheme condition provides. -/
@[stacks 0HA8]
theorem isQuasiExcellentScheme_iff_exists_isGScheme_isJ2 :
    IsQuasiExcellentScheme X ↔
      ∃ h : IsGScheme X, letI := h.isLocallyNoetherian; Scheme.IsJ2 X :=
  ⟨fun h => ⟨h.isGScheme, h.isJ2⟩, fun ⟨hG, hJ⟩ => hG.isQuasiExcellentScheme hJ⟩

/-- A locally Noetherian scheme is quasi-excellent if and only if it is a G-scheme and J-2. -/
theorem isQuasiExcellentScheme_iff_isGScheme_and_isJ2 [IsLocallyNoetherian X] :
    IsQuasiExcellentScheme X ↔ IsGScheme X ∧ Scheme.IsJ2 X :=
  isQuasiExcellentScheme_iff_exists_isGScheme_isJ2.trans exists_prop

/-- A quasi-excellent scheme is Nagata. -/
@[stacks 0HA9]
theorem IsQuasiExcellentScheme.isNagataScheme (h : IsQuasiExcellentScheme X) :
    IsNagataScheme X := fun x =>
  (h x).imp fun _ hU => ⟨hU.1, isNagataRing_of_isQuasiExcellent hU.2⟩

/-- An excellent scheme is universally catenary. -/
theorem IsExcellentScheme.isUniversallyCatenary (h : IsExcellentScheme X) :
    letI := h.isLocallyNoetherian
    Scheme.IsUniversallyCatenary X :=
  letI := h.isLocallyNoetherian
  Scheme.isUniversallyCatenary_of_affineOpenCover X (fun x => (h x).choose)
    (IsOpenCover.mk (eq_top_iff.mpr fun x _ =>
      Opens.mem_iSup.mpr ⟨x, (h x).choose_spec.1⟩))
    fun x => (h x).choose_spec.2.2

/-- A quasi-excellent scheme which is universally catenary is excellent. -/
theorem IsQuasiExcellentScheme.isExcellentScheme (h : IsQuasiExcellentScheme X)
    (hc : letI := h.isLocallyNoetherian; Scheme.IsUniversallyCatenary X) :
    IsExcellentScheme X := fun x =>
  letI := h.isLocallyNoetherian
  (h x).imp fun U hU => ⟨hU.1, hU.2, Scheme.ringIsUniversallyCatenary_of_isUniversallyCatenary hc U⟩

/-- A scheme is excellent if and only if it is quasi-excellent and universally catenary. Here
universal catenarity refers to the local Noetherianity which quasi-excellence provides. -/
@[stacks 0HAA]
theorem isExcellentScheme_iff_exists_isQuasiExcellentScheme_isUniversallyCatenary :
    IsExcellentScheme X ↔
      ∃ h : IsQuasiExcellentScheme X,
        letI := h.isLocallyNoetherian; Scheme.IsUniversallyCatenary X :=
  ⟨fun h => ⟨h.isQuasiExcellentScheme, h.isUniversallyCatenary⟩,
    fun ⟨h, hc⟩ => h.isExcellentScheme hc⟩

/-- A locally Noetherian scheme is excellent if and only if it is quasi-excellent and
universally catenary. -/
theorem isExcellentScheme_iff_isQuasiExcellentScheme_and_isUniversallyCatenary
    [IsLocallyNoetherian X] :
    IsExcellentScheme X ↔ IsQuasiExcellentScheme X ∧ Scheme.IsUniversallyCatenary X :=
  isExcellentScheme_iff_exists_isQuasiExcellentScheme_isUniversallyCatenary.trans exists_prop

/-- Every open subscheme of a quasi-excellent scheme is quasi-excellent. -/
@[stacks 0HAB "open subschemes, quasi-excellent case"]
theorem IsQuasiExcellentScheme.restrict (h : IsQuasiExcellentScheme X) (U : X.Opens) :
    IsQuasiExcellentScheme U.toScheme :=
  letI := h.isLocallyNoetherian
  (h.isGScheme.restrict U).isQuasiExcellentScheme
    (Scheme.isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian h.isJ2 U.ι)

/-- A scheme is quasi-excellent if and only if the ring of sections on every affine open is
quasi-excellent, if and only if it is quasi-excellent on the members of one affine open covering,
if and only if the scheme has an open covering by quasi-excellent open subschemes. -/
@[stacks 0HAB "equivalent conditions, quasi-excellent case"]
theorem isQuasiExcellentScheme_tfae (X : Scheme.{u}) :
    List.TFAE [
      IsQuasiExcellentScheme X,
      ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U),
      ∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).val) = ⊤ ∧ ∀ i, IsQuasiExcellent Γ(X, U i),
      ∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧ ∀ i, IsQuasiExcellentScheme (U i).toScheme] := by
  tfae_have 1 → 2 := by
    intro h U
    let := h.isLocallyNoetherian
    have eG := (isGScheme_tfae_cover X).out 1 2
    have eJ := (Scheme.isJ2_tfae X).out 1 3
    exact ⟨IsLocallyNoetherian.component_noetherian U, eG.mp h.isGScheme U, eJ.mp h.isJ2 U⟩
  tfae_have 2 → 3 := fun h => ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, h⟩
  tfae_have 3 → 1 := fun ⟨_, _, hS, hS'⟩ => isQuasiExcellentScheme_of_iSup_eq_top hS hS'
  tfae_have 1 → 4 := fun h => ⟨PUnit.{u + 1}, fun _ => ⊤, by simp, fun _ => h.restrict ⊤⟩
  tfae_have 4 → 1 := by
    rintro ⟨I, U, hU, h⟩
    have eG := (isGScheme_tfae_cover X).out 1 4
    have hG : IsGScheme X := eG.mpr ⟨I, U, hU, fun i => (h i).isGScheme⟩
    let := hG.isLocallyNoetherian
    have eJ := (Scheme.isJ2_tfae X).out 1 2
    exact hG.isQuasiExcellentScheme (eJ.mpr ⟨I, U, hU, fun i => (h i).isJ2⟩)
  tfae_finish

/-- Every open subscheme of an excellent scheme is excellent. -/
@[stacks 0HAB "open subschemes, excellent case"]
theorem IsExcellentScheme.restrict (h : IsExcellentScheme X) (U : X.Opens) :
    IsExcellentScheme U.toScheme :=
  letI := h.isLocallyNoetherian
  (h.isQuasiExcellentScheme.restrict U).isExcellentScheme
    (Scheme.isUniversallyCatenary_of_locallyOfFiniteType U.ι h.isUniversallyCatenary)

/-- A scheme is excellent if and only if the ring of sections on every affine open is excellent,
if and only if it is excellent on the members of one affine open covering, if and only if the
scheme has an open covering by excellent open subschemes. -/
@[stacks 0HAB "equivalent conditions, excellent case"]
theorem isExcellentScheme_tfae (X : Scheme.{u}) :
    List.TFAE [
      IsExcellentScheme X,
      ∀ U : X.affineOpens, IsExcellent Γ(X, U),
      ∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).val) = ⊤ ∧ ∀ i, IsExcellent Γ(X, U i),
      ∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧ ∀ i, IsExcellentScheme (U i).toScheme] := by
  tfae_have 1 → 2 := by
    intro h U
    let := h.isLocallyNoetherian
    have e := (isQuasiExcellentScheme_tfae X).out 1 2
    exact ⟨e.mp h.isQuasiExcellentScheme U,
      Scheme.ringIsUniversallyCatenary_of_isUniversallyCatenary h.isUniversallyCatenary U⟩
  tfae_have 2 → 3 := fun h => ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, h⟩
  tfae_have 3 → 1 := fun ⟨_, _, hS, hS'⟩ => isExcellentScheme_of_iSup_eq_top hS hS'
  tfae_have 1 → 4 := fun h => ⟨PUnit.{u + 1}, fun _ => ⊤, by simp, fun _ => h.restrict ⊤⟩
  tfae_have 4 → 1 := by
    rintro ⟨I, U, hU, h⟩
    have e := (isQuasiExcellentScheme_tfae X).out 1 4
    have hQ : IsQuasiExcellentScheme X := e.mpr ⟨I, U, hU, fun i => (h i).isQuasiExcellentScheme⟩
    let := hQ.isLocallyNoetherian
    exact hQ.isExcellentScheme (Scheme.isUniversallyCatenary_of_openCover X U (IsOpenCover.mk hU)
      fun i => (h i).isUniversallyCatenary)
  tfae_finish

end AlgebraicGeometry
