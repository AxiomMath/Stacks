module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCohomologyDeRhamConormal
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.KoszulRegularIdealSheaf.Stalkwise
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.KoszulFlatVanishingLocal
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Generators

/-!
# Stacks 0G8B with the vanishing derived

Let `π : X ⟶ S` be a *smooth* morphism of schemes and let `i : Z ⟶ X` be as in
[Stacks, Tag 0G86]: a closed immersion of finite presentation whose conormal sheaf is finite
locally free of rank `c`, an arbitrary natural number.  Suppose moreover that `i` is
Koszul-regular.
[Stacks, Tag 0G8B] says that the cohomological Gysin maps `γ^{p, q}` of [Stacks, Tag 0G8A]
attached to the glued `γ^p` of [Stacks, Tag 0G86] are compatible with the de Rham differentials.

`Stacks.DeRham.GysinCohomologyDeRhamConormal.conormalGysinCohomologyMap_comm_deRham` proves that
square, but with the vanishing `ℋ^j_Z(Ω^{p+c}_{X/S}) = 0` for `j < c` — the hypothesis of
[Stacks, Tag 0G8A], without which the cohomological Gysin map does not exist — still assumed.
The source of [Stacks, Tag 0G8B] does not assume it: it *derives* it from smoothness and
Koszul-regularity through [Stacks, Tag 0G7P].  This file carries out that derivation and
discharges the hypothesis, so that the tag sits on a statement assuming only the hypotheses the
source assumes.

## Main results

* `Stacks.DeRham.GysinCohomologyDeRhamKoszul.exists_affineOpen_koszulRegular_equations`: every
  point of `X` has an affine open neighbourhood on which `Z` is cut out by a family of **exactly
  `c`** sections of `𝒪_X` which is Koszul-regular in the ring of sections.
* `Stacks.DeRham.GysinCohomologyDeRhamKoszul.exists_koszulRegular_equationsClosedSet`: the same
  data in the shape [Stacks, Tag 0G7P] consumes, the equations read as global sections of the
  chart and the subscheme as their common zero locus.
* `Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms`:
  **the vanishing of [Stacks, Tag 0G8A], derived**, for `Ω^{m + c}_{X/S}`.
* `Stacks.DeRham.GysinCohomologyDeRhamKoszul.koszulGysinCohomologyMap_comm_deRham`:
  **[Stacks, Tag 0G8B].**

## Implementation notes

**Where the count comes from.**  [Stacks, Tag 0G7P] needs its local equations indexed by `Fin c`
for the *same* `c` as the degree of the vanishing, uniformly over every point of `X`, and the
three facts that are available do not compose by themselves: the conormal rank gives exactly `c`
equations everywhere but no regularity; Koszul-regularity of `i` gives regularity with an
existentially quantified length, and only over `Z`; and [Stacks, Tag 066A] transfers regularity
only between families of *equal* length.  What matches the lengths is [Stacks, Tag 067N] part (3),
`Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_koszulRegular_generators_of_basis`, which turns
a *basis* of the cotangent fibre `ℐ_x / 𝔪_x ℐ_x` into local generators of the ideal sheaf that are
Koszul-regular and as many as the basis is long.  The basis, indexed by `Fin c`, is
`Stacks.AlgebraicGeometry.ConormalEquations.exists_basis_idealCotangentFiber_of_conormalRank`.

**Away from `Z`.**  There the cotangent fibre is the residue field, of dimension one, so no basis
indexed by `Fin c` exists and 067N is unavailable.  The ideal sheaf is the unit ideal instead, and
the constant family `1, …, 1` of length `c` both generates it
(`Stacks.AlgebraicGeometry.ConormalEquations.exists_affineOpen_unit_equations`) and is
Koszul-regular, a sequence one of whose terms is a unit being so.  This is where `c ≠ 0` is used;
it is a hypothesis of `exists_affineOpen_koszulRegular_equations` and of the lemmas built on it,
and `supportVanishing_relativeDifferentialForms` supplies it by splitting on `c` — at `c = 0` no
equations are needed, the degrees the vanishing speaks of being those with `j < 0`.

**Reading the equations on the chart.**  [Stacks, Tag 0G7P] wants the equations as global sections
of the chart `W.toScheme`, while everything above produces them in `Γ(X, W)`.  The two rings are
identified by `AlgebraicGeometry.Scheme.Opens.topIso`, and `Stacks.Gysin.restrictEquations` is the
image of a family under that identification, so the transport is
`Stacks.AlgebraicGeometry.isKoszulRegular_map_ringEquiv`.

**The flatness is over `𝒪_X`, not over `S`.**  [Stacks, Tag 0G7P] asks for flatness of `Ω^{p+c}`
as a sheaf of `𝒪_X`-modules, which for a smooth `π` holds because that sheaf is finite locally
free.  It does *not* ask for flatness over `S` along `π`.

## References

* [Stacks Project, Tag 0G8B](https://stacks.math.columbia.edu/tag/0G8B)
* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
* [Stacks Project, Lemma 31.20.5 (Tag 067N)](https://stacks.math.columbia.edu/tag/067N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.RingedSpace

universe u

namespace Stacks.DeRham.GysinCohomologyDeRhamKoszul

open AlgebraicGeometry.Scheme.Hom
open Stacks.DeRham.CohomologicalGysin
open Stacks.DeRham.GysinCohomologyDeRham
open Stacks.DeRham.GysinCohomologyDeRhamConormal
open Stacks.Gysin
open Stacks.Perfect.LocalCohomologyDegrees
open scoped AlgebraicGeometry

variable {Z X S : Scheme.{u}}

/-! ### Koszul-regular equations of length `c` -/

/-- **Koszul-regular equations of exactly `c` sections around every point of `X`.**  Let
`i : Z ⟶ X` be a Koszul-regular closed immersion of finite presentation whose conormal sheaf is
finite locally free of rank `c ≠ 0`.  Then every point of `X` has an affine open neighbourhood `W`
carrying `c` sections of the ideal sheaf of `Z` which generate it on `W` and form a Koszul-regular
sequence in `Γ(X, W)`.

At a point of `Z` this is [Stacks, Tag 067N] part (3) fed with the basis of the cotangent fibre
that the conormal rank provides; its output is a Koszul-regular generating family on some open,
which is then shrunk to an affine one, where germwise Koszul-regularity is Koszul-regularity of
the sections.  Away from `Z` the ideal sheaf is the unit ideal and the family is `1, …, 1`. -/
theorem exists_affineOpen_koszulRegular_equations (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (hkos : IsKoszulRegularImmersion i) (c : ℕ) (hc : c ≠ 0)
    (hE : ConormalRank i c) (p : X) :
    ∃ (W : X.Opens) (_ : IsAffineOpen W) (_ : p ∈ W) (f : Fin c → Γ(X, W)),
      (∀ a, f a ∈ (definingIdealOfHom i).obj (op W)) ∧
        IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f ∧
          Koszul.IsKoszulRegular f := by
  by_cases hp : p ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hp
    obtain ⟨g, b, hb⟩ := exists_basis_idealCotangentFiber_of_conormalRank i c z hE
    obtain ⟨U, hxU, fU, -, hK, hgen⟩ :=
      exists_koszulRegular_generators_of_basis (definingIdealOfHom i) (i.base z) g b hb
        (isKoszulRegularIdealSheaf_definingIdealOfHom i hkos)
    obtain ⟨W, hW, hpW, hWU0⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := i.base z) (U := U) hxU
    have hWU : W ≤ U := hWU0
    refine ⟨W, hW, hpW, fun a => X.presheaf.map (homOfLE hWU).op (fU a).1,
      fun a => restrict_mem _ _ (fU a).2, isGeneratedByOn_of_le U _ hgen W hWU, ?_⟩
    refine (AlgebraicGeometry.forall_isKoszulRegular_germFamily_iff X hW _).mp ?_
    exact (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular X.toRingedSpace W _).mp
      (hK.of_le W hWU)
  · obtain ⟨W, hW, hpW, hmem, hWgen, -⟩ := exists_affineOpen_unit_equations i c hc hp
    exact ⟨W, hW, hpW, fun _ => 1, hmem, hWgen,
      isKoszulRegular_of_isUnit_apply _ ⟨0, Nat.pos_of_ne_zero hc⟩ isUnit_one⟩

/-- **The closed subset `Z` is locally the zero locus of a Koszul-regular family of `c`
equations**, in the shape [Stacks, Tag 0G7P] consumes: an affine open `U` around every point of
`X`, a Koszul-regular `f : Fin c → Γ(U, 𝒪)` and the identification of the part of `Z` lying in
`U` with the common zero locus of `f`. -/
theorem exists_koszulRegular_equationsClosedSet (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (hkos : IsKoszulRegularImmersion i) (c : ℕ) (hc : c ≠ 0)
    (hE : ConormalRank i c) (p : X) :
    ∃ U : X.Opens, p ∈ U ∧ IsAffineOpen U ∧
      ∃ f : Fin c → Γ(U.toScheme, ⊤), Koszul.IsKoszulRegular f ∧
        U.ι ⁻¹' Set.range i.base = equationsClosedSet f := by
  obtain ⟨W, hW, hpW, f, hmemf, hgen, hreg⟩ :=
    exists_affineOpen_koszulRegular_equations i hkos c hc hE p
  have hcut : IsCutOutByEquationsOn i W f :=
    isCutOutByEquationsOn_of_isGeneratedByOn i hgen fun V hV j =>
      (mem_definingIdealOfHom_iff_app_eq_zero i V _).mp
        (restrict_mem _ (homOfLE hV) (hmemf j))
  exact ⟨W, hpW, hW, restrictEquations W f,
    Stacks.AlgebraicGeometry.isKoszulRegular_map_ringEquiv
      W.topIso.symm.commRingCatIsoToRingEquiv hreg,
    (equationsClosedSet_restrictEquations i W hcut).symm⟩

/-! ### The vanishing of Stacks 0G8A, derived -/

/-- **The vanishing hypothesis of [Stacks, Tag 0G8A], derived from smoothness and
Koszul-regularity.**  For `π` smooth and `i` a Koszul-regular closed immersion of finite
presentation whose conormal sheaf has rank `c`,

`ℋ^j_Z(Ω^{m + c}_{X/S}) = 0` for every `j < c`.

**The rank is unrestricted**, as in [Stacks, Tag 0G8A], which says `c ≥ 0`.  The two cases are
genuinely different and neither is a reindex of the other:

* for `c ≠ 0` this is [Stacks, Tag 0G7P] in the form `Stacks.Perfect.LocalCohomologyDegrees`
  `.isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_ne`, whose conclusion
  is already the one `Stacks.DeRham.GysinCohomologyDeRham.SupportVanishing` asks for.  Of its
  three hypotheses the local Koszul-regular equations are
  `exists_koszulRegular_equationsClosedSet` — which is where `c ≠ 0` is consumed, a family of
  `c` equations having to generate the unit ideal away from `Z` — quasi-coherence is an instance,
  and flatness over `𝒪_X` holds because `Ω^{m + c}_{X/S}` is finite locally free for a smooth
  `π`;
* for `c = 0` there is nothing to prove about local cohomology with supports at all: the degrees
  asked about are those with `j < 0`, and in those the local cohomology of a module placed in
  degree `0` vanishes outright, by
  `Stacks.DeRham.CohomologicalGysin.isZero_localCohomologySheafOfComplex_of_neg`.  No Koszul
  regularity, no smoothness and no equations enter. -/
theorem supportVanishing_relativeDifferentialForms (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) [Smooth π]
    (hkos : IsKoszulRegularImmersion i) (c : ℕ) (hE : ConormalRank i c) (m : ℕ) :
    SupportVanishing X.toRingedSpace (Set.range i.base) (isClosed_range_base i) c
      (relativeDifferentialForms π ((m : ℤ) + (c : ℤ))) := by
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · intro j hj
    exact isZero_localCohomologySheafOfComplex_of_neg (Set.range i.base)
      (isClosed_range_base i) (relativeDifferentialForms π ((m : ℤ) + ((0 : ℕ) : ℤ))) j
      (by exact_mod_cast hj)
  · have hc : c ≠ 0 := Nat.pos_iff_ne_zero.mp hcpos
    have hfl : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (relativeDifferentialForms π ((m : ℤ) + (c : ℤ))) := by
      rw [show ((m : ℤ) + (c : ℤ)) = ((m + c : ℕ) : ℤ) by push_cast; ring]
      exact AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms
        π (m + c)
    intro j hj
    exact isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_ne
      (Set.range i.base) (isClosed_range_base i) c
      (exists_koszulRegular_equationsClosedSet i hkos c hc hE)
      (relativeDifferentialForms π ((m : ℤ) + (c : ℤ)))
      (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _ hfl) j (by omega)

/-! ### Stacks 0G8B -/

/-- **Stacks Project, Tag 0G8B.**  Let `π : X ⟶ S` be a *smooth* morphism of schemes and let
`i : Z ⟶ X` be as in [Stacks, Tag 0G86] — a closed immersion of finite presentation whose
conormal sheaf is finite locally free of rank `c` — and *Koszul-regular*.  The
cohomological Gysin maps `γ^{p, q} : H^q(X, i_*Ω^p_{Z/S}) ⟶ H^{q + c}(X, Ω^{p + c}_{X/S})` of
[Stacks, Tag 0G8A] attached to the glued `γ^p` of [Stacks, Tag 0G86] are compatible with the de
Rham differentials on `Ω^•_{X/S}` and `Ω^•_{Z/S}`: the square

```
H^q(X, i_*Ω^p_{Z/S}) ----γ^{p, q}----→ H^{q+c}(X, Ω^{p+c}_{X/S})
        ↓ d                                     ↓ d
H^q(X, i_*Ω^{p+1}_{Z/S}) --γ^{p+1, q}→ H^{q+c}(X, Ω^{p+c+1}_{X/S})
```

commutes, the verticals being the arrows the de Rham differentials induce on cohomology through
`Stacks.DeRham.GysinCohomologyDeRham.abelianHgroupMap`.

The square itself is
`Stacks.DeRham.GysinCohomologyDeRhamConormal.conormalGysinCohomologyMap_comm_deRham`, which
assumes the vanishing of [Stacks, Tag 0G8A]; here that vanishing is
`supportVanishing_relativeDifferentialForms`, derived from the hypotheses of this tag through
[Stacks, Tag 0G7P], so that nothing beyond them is assumed.  That the map the square is about is
the tagged `γ^{p, q}` of [Stacks, Tag 0G8A] and not a second construction is
`Stacks.DeRham.GysinCohomologyDeRhamConormal.gysinHodgeFormsMapOfConormalRank_eq`.

**The rank is an arbitrary natural number**, as [Stacks, Tag 0G86] states it and
[Stacks, Tag 0G8A] says explicitly (`c ≥ 0`); neither `c ≠ 0` nor a rank of the form `d + 1` is
assumed.  Both inputs are already general: the vanishing
`supportVanishing_relativeDifferentialForms` handles `c = 0` separately — in degrees `j < 0`
there is nothing to vanish — and the square
`Stacks.DeRham.GysinCohomologyDeRhamConormal.conormalGysinCohomologyMap_comm_deRham` rests on
[Stacks, Tag 0G87] at an arbitrary rank,
`Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank`. -/
@[stacks 0G8B]
theorem koszulGysinCohomologyMap_comm_deRham (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) [Smooth π]
    (hkos : IsKoszulRegularImmersion i) {c : ℕ} (p q : ℕ)
    (hE : ConormalRank i c) :
    gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
          (pushforwardRelativeForms i π (p : ℤ))
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
          (supportVanishing_relativeDifferentialForms i π hkos c hE p)
          (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) q ≫
        abelianHgroupMap X.toRingedSpace (0 : ℤ) ((q : ℤ) + (c : ℤ)) (q + c)
          (by omega) (ambientDeRhamShiftAbHom π c p) =
      abelianHgroupMap X.toRingedSpace (c : ℤ) ((q : ℤ) + (c : ℤ)) q
          (by omega) (pushforwardDeRhamDifferentialAbHom i π p) ≫
        gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
          (pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ))
          (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ)))
          (supportVanishing_relativeDifferentialForms i π hkos c hE
            (p + 1))
          (conormalGysinHom i π (p + 1) hE ≫
            (conormalGysinTargetIso i π c (p + 1)).hom) q :=
  conormalGysinCohomologyMap_comm_deRham i π p q hE _ _

end Stacks.DeRham.GysinCohomologyDeRhamKoszul

end
