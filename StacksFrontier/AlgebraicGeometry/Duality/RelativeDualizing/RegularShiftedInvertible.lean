module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Restriction
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.RingTheory.Dualizing.InjectiveHullTor
public import StacksFrontier.RingTheory.Dualizing.Ubiquity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# On a regular scheme of pure dimension `n`, an invertible module in degree `-n` is dualizing

Let `P` be a locally Noetherian scheme all of whose local rings are regular, and all of whose
closed points have local rings of Krull dimension exactly `n`; for instance `P = ℙⁿ_k` over a
field `k`. For an invertible `𝒪_P`-module `L`, the complex `L[n]`, that is `L` placed in degree
`-n`, is a dualizing complex on `P` ([Stacks, Tag 0A87]), and its derived stalk at every closed
point `p` is a normalized dualizing complex over `𝒪_{P,p}`.

## Main results

* `Stacks.Duality.hasDualizingModelOn_shift` and `Stacks.Duality.isDualizingComplex_shift`: a
  shift of a dualizing complex on a locally Noetherian scheme is a dualizing complex.
* `Stacks.Duality.ringKrullDim_stalk_le_of_specializes`,
  `Stacks.Duality.ringKrullDim_stalk_le_of_isClosed` and `Stacks.Duality.ringKrullDim_sections_le`:
  the dimension of a local ring grows along specializations, so a bound at the closed points of a
  locally Noetherian scheme bounds every local ring and the ring of sections of every affine open.
* `Stacks.Duality.isRegularRing_sections` and
  `Stacks.Duality.isDualizingComplex_single_self_of_isRegularRing`: on a scheme with regular local
  rings the sections over an affine open form a regular ring, and a regular ring of finite Krull
  dimension is a dualizing complex for itself in degree zero.
* `Stacks.Duality.isDualizingComplex_single_of_isRegularLocalRing`: on `P` as above, `L` in
  degree zero is a dualizing complex.
* `Stacks.Duality.isDualizingComplex_single_shift_of_isRegularLocalRing`: `L[n]` is a dualizing
  complex.
* `Stacks.Duality.derivedStalkSingleShiftIso`: the derived stalk of `L[0]⟦m⟧` at a point `x` is
  `𝒪_{P,x}[0]⟦m⟧`.
* `Stacks.Duality.isNormalizedDualizingComplex_derivedStalk_single_shift`: at a closed point `p`,
  the derived stalk of `L[n]` is a normalized dualizing complex over `𝒪_{P,p}`.

## Implementation notes

*Dualizing.* By [Stacks, Tag 0A86] it is enough to exhibit a dualizing model of `L` in degree
zero on the members of one affine open cover, and the cover is taken to trivialize `L`. On a
member `V` with `L|_V ≅ 𝒪_V` the model is the ring `Γ(P, V)` in degree zero, which is a
dualizing complex over itself because it is a regular ring of finite Krull dimension
([Stacks, Tag 00OE] bounds its injective dimension). The finiteness of the Krull dimension comes
from the closed points: every point specializes to a closed point ([Stacks, Tag 02IL]), and the
dimension of the local ring can only grow along a specialization.

*Normalized.* The derived stalk of `L[n]` at `p` is `L_p` placed in degree `-n`, and `L_p` is
free of rank one over `𝒪_{P,p}`. So it is `𝒪_{P,p}[0]⟦n⟧`, which is normalized because
`𝒪_{P,p}` is a Gorenstein local ring of dimension `n`
(`Dualizing.LocalDuality.isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing`).

*Models.* Every derived category is read at `HasDerivedCategory.standard`, the model of the
consumers of these statements; see
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DualizingComplexModel.lean` for the
comparison with the locally small model.

## References

* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
* [Stacks Project, Tag 00OE](https://stacks.math.columbia.edu/tag/00OE)
* [Stacks Project, Tag 02IL](https://stacks.math.columbia.edu/tag/02IL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance high] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-! ### Shifts -/

/-- **A shift of a complex with a dualizing model at an affine open has one there**, namely the
same shift of the model: restriction to the open and the associated-sheaf functor both commute
with shifts. -/
theorem hasDualizingModelOn_shift {K : DerivedCategory X.Modules} {U : X.Opens}
    {hU : IsAffineOpen U} (h : HasDualizingModelOn K U hU) (n : ℤ) :
    HasDualizingModelOn (K⟦n⟧) U hU := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  exact ⟨ω⟦n⟧, Dualizing.isDualizingComplex_shift ω hω n,
    ⟨((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.commShiftIso n).app K ≪≫
      (shiftFunctor _ n).mapIso e ≪≫
      (((tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.commShiftIso n).app
          ω).symm⟩⟩

/-- **A shift of a dualizing complex on a locally Noetherian scheme is a dualizing complex.** -/
theorem isDualizingComplex_shift {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (n : ℤ) : IsDualizingComplex (K⟦n⟧) :=
  fun U hU => hasDualizingModelOn_shift (hK U hU) n

/-! ### Regular rings of sections -/

/-- **The local ring at a point is at most as large as the local ring at a specialization.** The
Krull dimension of `𝒪_{X,x}` is the coheight of `x` in the specialization order, which can only
grow along a specialization. -/
@[ega "IV 5.10.13" "more general"]
theorem ringKrullDim_stalk_le_of_specializes {Y : Scheme.{u}} {x y : Y} (h : x ⤳ y) :
    ringKrullDim (Y.presheaf.stalk x) ≤ ringKrullDim (Y.presheaf.stalk y) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact WithBot.coe_le_coe.mpr (Order.coheight_anti (Scheme.le_iff_specializes.mpr h))

/-- **A bound on the local rings at the closed points bounds every local ring**, on a locally
Noetherian scheme: every point specializes to a closed point ([Stacks, Tag 02IL]). -/
theorem ringKrullDim_stalk_le_of_isClosed {n : WithBot ℕ∞}
    (hdim : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) ≤ n) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ n := by
  obtain ⟨y, hy, hxy⟩ := exists_specializes_closedPoint X x
  exact (ringKrullDim_stalk_le_of_specializes hxy).trans (hdim y hy)

/-- Every prime of the sections over an affine open has a stalk of which it is the prime. -/
private theorem exists_isLocalization_stalk {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (p : Ideal Γ(Y, U)) [hp : p.IsPrime] :
    ∃ (x : Y) (_ : Algebra Γ(Y, U) (Y.presheaf.stalk x)),
      IsLocalization.AtPrime (Y.presheaf.stalk x) p := by
  let z : PrimeSpectrum Γ(Y, U) := ⟨p, hp⟩
  have hx : hU.fromSpec z ∈ U := hU.fromSpec_preimage_self.ge trivial
  exact ⟨hU.fromSpec z, Y.presheaf.algebra_section_stalk ⟨hU.fromSpec z, hx⟩,
    hU.isLocalization_stalk' z hx⟩

omit [IsLocallyNoetherian X] in
/-- **The sections over an affine open are no larger than the local rings.** Every prime of
`Γ(X, U)` is the prime of a point `x ∈ U`, and its height is the dimension of `𝒪_{X,x}`, which
is the localization at it. -/
theorem ringKrullDim_sections_le {U : X.Opens} (hU : IsAffineOpen U) {n : WithBot ℕ∞}
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ n) : ringKrullDim Γ(X, U) ≤ n := by
  rw [ringKrullDim_le_iff_height_le]
  intro p hp
  obtain ⟨x, _, _⟩ := exists_isLocalization_stalk hU p
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (X.presheaf.stalk x)]
  exact hdim _

/-- **The sections over an affine open of a scheme with regular local rings form a regular
ring**: the localization at a prime is the local ring at the corresponding point. -/
theorem isRegularRing_sections (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) : IsRegularRing Γ(X, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  rw [isRegularRing_iff]
  intro p hp
  obtain ⟨x, _, _⟩ := exists_isLocalization_stalk hU p
  have : IsRegularLocalRing (X.presheaf.stalk x) := hreg _
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)).toRingEquiv).symm

/-- **A regular ring of Krull dimension at most `n` is a dualizing complex for itself in degree
zero**: by [Stacks, Tag 00OE] its regular module has injective dimension at most its Krull
dimension. -/
theorem isDualizingComplex_single_self_of_isRegularRing (A : Type u) [CommRing A]
    [IsRegularRing A] (n : ℕ) (hdim : ringKrullDim A ≤ n) :
    Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  refine (Dualizing.isDualizingComplex_single_self_iff A).2 ?_
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : HasInjectiveDimensionLT (ModuleCat.of A A) 0 :=
      (ModuleCat.isZero_of_subsingleton _).hasInjectiveDimensionLT_zero
    exact ⟨0, hasInjectiveDimensionLT_of_ge _ 0 1 (by omega)⟩
  · obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp
      (ne_bot_of_le_ne_bot WithBot.zero_ne_bot (ringKrullDim_nonneg_of_nontrivial (R := A)))
    have hne : e ≠ ⊤ := by
      rintro rfl
      rw [← he] at hdim
      exact absurd (WithBot.coe_le_coe.mp hdim) (by simp)
    obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp hne
    exact ⟨d, Dualizing.hasInjectiveDimensionLE_of_isRegularRing A d he.symm⟩

/-! ### The invertible module in degree zero -/

variable (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (n : ℕ)
  (hdim : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = n)

include hreg hdim in
/-- At an affine open on which `L` is trivial, `L` in degree zero has the dualizing model
`Γ(X, V)` in degree zero. -/
theorem hasDualizingModelOn_single_of_iso_unit {L : X.Modules} {V : X.Opens} (hV : IsAffineOpen V)
    (e : (Scheme.Modules.restrictFunctor V.ι).obj L ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    HasDualizingModelOn ((DerivedCategory.singleFunctor X.Modules 0).obj L) V hV := by
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsRegularRing Γ(X, V) := isRegularRing_sections hreg hV
  refine ⟨(DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, V)) 0).obj
    (ModuleCat.of Γ(X, V) Γ(X, V)),
    isDualizingComplex_single_self_of_isRegularRing Γ(X, V) n
      (ringKrullDim_sections_le hV
        (ringKrullDim_stalk_le_of_isClosed fun x hx => (hdim x hx).le)), ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor V.toScheme.Modules 0).mapIso
      (e ≪≫ (Scheme.Modules.restrictUnitIso hV.isoSpec.hom).symm ≪≫
        (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso
          (tildeSelf (R := Γ(X, V))).symm) ≪≫
    (((tilde.functor Γ(X, V) ⋙
      Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategorySingleFunctor 0).app _).symm

include hreg hdim in
/-- **On a locally Noetherian scheme with regular local rings whose closed points have local
rings of dimension `n`, an invertible module in degree zero is a dualizing complex.** It is
checked on an affine open cover trivializing the module ([Stacks, Tag 0A86]). -/
theorem isDualizingComplex_single_of_isRegularLocalRing (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules 0).obj L) := by
  choose W hxW e using fun x : X => Stacks.InvertibleRankOneScheme.exists_mem_isoUnit_over X L x
  choose V hV hxV hVW using fun x : X => exists_isAffineOpen_mem_and_subset (hxW x)
  refine isDualizingComplex_of_hasDualizingModelOn_cover V hV ?_ fun x =>
    hasDualizingModelOn_single_of_iso_unit hreg n hdim (hV x)
      (Stacks.SheafOfModules.restrictIsoUnitOfLE L (hVW x)
        (Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit (W x) L
          (e x).some))
  exact eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩

include hreg hdim in
/-- **On a locally Noetherian scheme with regular local rings whose closed points have local
rings of dimension `n`, an invertible module `L` placed in degree `-n` is a dualizing
complex** ([Stacks, Tag 0A87]). -/
theorem isDualizingComplex_single_shift_of_isRegularLocalRing (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    IsDualizingComplex (((DerivedCategory.singleFunctor X.Modules 0).obj L)⟦(n : ℤ)⟧) :=
  isDualizingComplex_shift (isDualizingComplex_single_of_isRegularLocalRing hreg n hdim L) n

/-! ### Normalization at the closed points -/

/-- **The derived stalk of a shifted invertible module is the shifted local ring**: at `x`, the
derived stalk of `L[0]⟦m⟧` is `𝒪_{X,x}[0]⟦m⟧`, the stalk `L_x` being free of rank one. -/
def derivedStalkSingleShiftIso (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (x : X)
    (m : ℤ) :
    (derivedStalkFunctor x).obj (((DerivedCategory.singleFunctor X.Modules 0).obj L)⟦m⟧) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))⟦m⟧ :=
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := ‹_›
  ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategorySingleFunctor
          0).app L ≪≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).mapIso
          (Stacks.InvertibleStalk.nonempty_linearEquiv_stalk L x).some.toModuleIso)

include hreg hdim in
/-- **At a closed point, the derived stalk of an invertible module in degree `-n` is a normalized
dualizing complex**, on a locally Noetherian scheme with regular local rings whose closed points
have local rings of dimension `n`. The derived stalk is `𝒪_{X,p}[0]⟦n⟧`, and `𝒪_{X,p}` is a
Gorenstein local ring of dimension `n` ([Stacks, Tag 0AWX]). -/
theorem isNormalizedDualizingComplex_derivedStalk_single_shift (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (p : X) (hp : IsClosed ({p} : Set X)) :
    Dualizing.IsNormalizedDualizingComplex.{u, 0}
      ((derivedStalkFunctor p).obj
        (((DerivedCategory.singleFunctor X.Modules 0).obj L)⟦(n : ℤ)⟧)) := by
  have : IsRegularLocalRing (X.presheaf.stalk p) := hreg p
  refine (Dualizing.isNormalizedDualizingComplex_congr.{u, 0}
    (derivedStalkSingleShiftIso L p n)).2 ?_
  exact Dualizing.LocalDuality.isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing
    _ (Dualizing.IsRegularLocalRing.isGorensteinLocalRing _) n (hdim p hp)

end Stacks.Duality

end
