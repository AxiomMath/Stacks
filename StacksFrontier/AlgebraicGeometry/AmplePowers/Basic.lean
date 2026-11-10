module

public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Ample invertible sheaves

Stacks Tag 01PS defines an invertible `𝒪_X`-module `L` on a scheme `X` to be *ample* when

1. `X` is quasi-compact, and
2. for every `x ∈ X` there are `n ≥ 1` and `s ∈ Γ(X, L^{⊗ n})` with `x ∈ X_s` and `X_s` affine,

where `X_s = {x ∈ X ∣ s ∉ 𝔪_x L_x}` is the nonvanishing locus of the global section `s`, open by
Stacks Tag 01CY.

This file defines `X_s` for an arbitrary `𝒪_X`-module (`Stacks.Ample.nonvanishingLocus`),
develops its API, and defines ampleness (`Stacks.Ample.IsAmpleForPowers`).

## Main definitions

* `Stacks.Ample.nonvanishingLocus M s`: the set `X_s` of points where the germ of the global
  section `s` of `M` avoids `𝔪_x M_x`.
* `Stacks.Ample.IsAmpleForPowers X pow`: ampleness, condition (1) and (2) above, read off a
  family `pow : ℤ → X.Modules` of tensor powers.

## Main results

* `Stacks.Ample.nonvanishingLocus_smul`:
  `X_{r · s} = X.basicOpen r ∩ X_s` for `r` a global section of the structure sheaf. This is the
  Stacks remark `X_s ∩ X_{s'} = X_{s s'}` preceding Tag 01PS, in the case `s' ∈ Γ(X, 𝒪_X)`.
* `Stacks.Ample.nonvanishingLocus_congr`: `X_s` is unchanged by transporting `s` along an
  isomorphism of `𝒪_X`-modules.
* `Stacks.Ample.isAmpleForPowers_iff_isOpen`: **unconditionally**, ampleness as defined here is
  equivalent to the literal shape of Tag 01PS, in which `X_s` is packaged as an open set and
  `IsAffineOpen` is applied to that open set.
* `Stacks.Ample.isAmpleForPowers_congr`: ampleness depends on the family of tensor powers only
  up to isomorphism in each degree. This is what makes the choice of `pow` below safe.

## Design choices, and how this differs from the Stacks statement

Four decisions were forced, and each is a deliberate departure in *spelling* only. A direct
transcription of Tag 01PS reads `IsAmple (X : Scheme) (L : X.Modules) [IsInvertible … L]`; the
differences are:

**1. The tensor powers are a parameter, not a construction.** Ampleness quantifies over
`Γ(X, L^{⊗ n})`, so it needs the integer tensor powers of `L`, which are Stacks Tag 01CU and are
being built elsewhere in this repository (`AlgebraicGeometry.SheafOfModules.tensorPow` in
`StacksFrontier/AlgebraicGeometry/TensorPowers/Basic.lean`). Rather than duplicate that
construction, `IsAmpleForPowers X pow` takes the family `pow : ℤ → X.Modules` as an explicit
argument. `tensorPow` has exactly this shape once its base sheaf is written as
`Stacks.SheafInternalHom.structureSheaf_eq_ringCatSheaf` allows, so the intended instantiation is
a one-liner, and `isAmpleForPowers_congr` shows nothing depends on which construction of the
powers is used. The hazard of an explicit parameter is that it can be instantiated with a family
that is *not* the tensor powers, in which case `IsAmpleForPowers` says something else; this is
the price of not duplicating Tag 01CU, and `isAmpleForPowers_congr` is the mitigation.

**2. Global sections are `Γ(M, ⊤)`, not the categorical `M.sections`.** The direct transcription
uses `SheafOfModules.sections`, a compatible family of sections over every open, and evaluates it at
`⊤`. For a *sheaf* the two are equivalent, and `Γ(M, ⊤)` is literally the `Γ(X, L)` of the source.
A consumer holding `s : M.sections` passes `s.eval (Opposite.op ⊤)`.

**3. The affine open is produced existentially instead of by `Opens`-packaging a sorried
openness theorem.** The direct transcription writes
`x ∈ nonvanishingOpen X L s ∧ IsAffineOpen (nonvanishingOpen
X L s)`, where `nonvanishingOpen` is `X_s` bundled with the openness theorem of Tag 01CY. That
theorem is not available in the library: it needs an invertible module to be locally free
of rank one, which is clause 2 of Tag 0B8M, and the library's form of that clause
(`Stacks.InvertibleRankOne.exists_trivialization_of_tensorLeft`) is hypothesised on invertibility
of the *presheaf* tensor functor, a different hypothesis from
`AlgebraicGeometry.SheafOfModules.IsInvertible`. So condition (2) is phrased as
`∃ U : X.Opens, ↑U = X_s ∧ x ∈ U ∧ IsAffineOpen U`. This is not a weakening: `U` is forced to be
`X_s` by the first conjunct, so the condition *implies* that `X_s` is open, and
`isAmpleForPowers_iff_isOpen` proves — with no hypothesis — that the result is equivalent to the
transcription's literal shape.

**4. No invertibility hypothesis.** The direct transcription carries `[IsInvertible … L]` because
`nonvanishingOpen` cannot be written without it. `nonvanishingLocus` needs no such hypothesis, so
none appears here. This is strictly more general and loses nothing: as in the source, the
predicate is only the Stacks notion of ampleness when applied to the tensor powers of an
invertible module, and a consumer that wants to record invertibility states it alongside.

## Implementation notes

`nonvanishingLocus` is stated with `TopCat.Presheaf.Γgerm`, as in the direct transcription. The
module structure on the stalk, and the submodule `𝔪_x M_x`, come from
`StacksFrontier/AlgebraicGeometry/AmplePowers/ModuleStalk.lean`, whose `scoped instance` must be in
scope to *unfold* the definition — hence the `open Stacks.ModuleStalk` below. Statements that
only mention `nonvanishingLocus` as a black box, as every result in the ampleness section does,
do not need it.

The arithmetic of `nonvanishingLocus_smul` lives entirely in
`Stacks.ModuleStalk.smul_mem_maximalSmul_iff`; here it is only combined with
`AlgebraicGeometry.Scheme.mem_basicOpen_top`, which is Mathlib's identification of the basic open
of a global section with the locus where its germ is a unit.

## References

* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [EGA II, Definition 4.5.3]

## What is not done

Openness of `X_s` (Stacks Tag 01CY) is not proved here; see design choice 3. It is proved in
`../NonvanishingOpen/Basic.lean`, as `Stacks.NonvanishingOpen.isOpen_nonvanishingLocus`. The remark
`X_s ∩ X_{s'} = X_{s ⊗ s'}` is proved only in the case where `s'` is a section of the structure
sheaf, because the general case is a statement about the tensor product of two modules and so
belongs with Tag 01CU. Nothing downstream of Tag 01PS is proved here: not Tag 01PT (`L` is ample
iff `L^{⊗ n}` is), not Tag 01Q2 (a positive twist is ample on a quasi-compact open of `Proj`), not
Tag 01Q3 (the ten equivalent characterisations), not Tag 01QE (`X` is quasi-affine iff `𝒪_X` is
ample). Of those, Tag 01Q2 is proved elsewhere in the repository, as
`Stacks.AlgebraicGeometry.ProjAmpleTwist.exists_isAmple_pullback_twistingSheaf`, and so are Tags
01PT and 01QE; Tag 01Q3 is not proved anywhere. Getting Tag 01QE out of the material of this file
would instead need the stalk of the structure sheaf *as an abelian group* identified with `𝒪_{X,x}`
*as a ring*, so that `X_r` for `r ∈ Γ(X, 𝒪_X)` could be computed to be `X.basicOpen r`;
`nonvanishingLocus_smul` is the half of that computation which does not need the identification.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Stacks.ModuleStalk

universe u

namespace Stacks.Ample

variable {X : Scheme.{u}} {M N : X.Modules}

/-! ### The nonvanishing locus of a global section -/

/-- The nonvanishing locus `X_s` of a global section `s` of an `𝒪_X`-module `M`: the points at
which the germ of `s` is not in `𝔪_x M_x`. For `M` invertible this is the open set of Stacks
Tag 01CY, on which `s` trivialises `M`; openness is not proved here. -/
noncomputable def nonvanishingLocus (M : X.Modules) (s : Γ(M, ⊤)) : Set X :=
  {x | (M.presheaf.Γgerm x).hom s ∉ maximalSmul M x}

/-- A point `x` lies in `X_s` exactly when the germ of `s` at `x` is not in `𝔪_x M_x`. -/
theorem mem_nonvanishingLocus_iff (M : X.Modules) (s : Γ(M, ⊤)) (x : X) :
    x ∈ nonvanishingLocus M s ↔ (M.presheaf.Γgerm x).hom s ∉ maximalSmul M x :=
  Iff.rfl

/-- The zero section vanishes everywhere. -/
@[simp] theorem nonvanishingLocus_zero (M : X.Modules) :
    nonvanishingLocus M (0 : Γ(M, ⊤)) = ∅ := by
  ext x
  simp only [mem_nonvanishingLocus_iff, Set.mem_empty_iff_false, iff_false, not_not, map_zero]
  exact Submodule.zero_mem _

/-- A section whose germ at `x` vanishes does not belong to its own nonvanishing locus. -/
theorem Γgerm_ne_zero_of_mem_nonvanishingLocus {M : X.Modules} {s : Γ(M, ⊤)} {x : X}
    (hx : x ∈ nonvanishingLocus M s) : (M.presheaf.Γgerm x).hom s ≠ 0 :=
  fun h => hx (h ▸ Submodule.zero_mem _)

/-- A section and its negative have the same nonvanishing locus. -/
@[simp] theorem nonvanishingLocus_neg (M : X.Modules) (s : Γ(M, ⊤)) :
    nonvanishingLocus M (-s) = nonvanishingLocus M s := by
  ext x
  simp only [mem_nonvanishingLocus_iff, map_neg, Submodule.neg_mem_iff]

/-- A sum of sections can only fail to vanish where one of the summands does. -/
theorem nonvanishingLocus_add_subset (M : X.Modules) (s t : Γ(M, ⊤)) :
    nonvanishingLocus M (s + t) ⊆ nonvanishingLocus M s ∪ nonvanishingLocus M t := by
  intro x hx
  by_contra hc
  simp only [Set.mem_union, not_or, mem_nonvanishingLocus_iff, not_not] at hc
  exact hx (map_add (M.presheaf.Γgerm x).hom s t ▸ Submodule.add_mem _ hc.1 hc.2)

/-- **The Stacks remark `X_s ∩ X_{s'} = X_{s s'}`, for `s'` a section of the structure sheaf.**
Scaling a section by `r ∈ Γ(X, 𝒪_X)` intersects its nonvanishing locus with the basic open of
`r`. -/
theorem nonvanishingLocus_smul (M : X.Modules) (r : Γ(X, ⊤)) (s : Γ(M, ⊤)) :
    nonvanishingLocus M (r • s) = ↑(X.basicOpen r) ∩ nonvanishingLocus M s := by
  ext x
  have hb : x ∈ X.basicOpen r ↔ IsUnit ((X.presheaf.Γgerm x).hom r) := X.mem_basicOpen_top r x
  rw [mem_nonvanishingLocus_iff, Γgerm_smul, Set.mem_inter_iff, SetLike.mem_coe, hb,
    mem_nonvanishingLocus_iff, smul_mem_maximalSmul_iff, not_or, not_not]

/-- Scaling a section by `r ∈ Γ(X, 𝒪_X)` can only shrink its nonvanishing locus. -/
theorem nonvanishingLocus_smul_subset (M : X.Modules) (r : Γ(X, ⊤)) (s : Γ(M, ⊤)) :
    nonvanishingLocus M (r • s) ⊆ nonvanishingLocus M s :=
  (nonvanishingLocus_smul M r s).subset.trans Set.inter_subset_right

/-- The nonvanishing locus is unchanged by transporting the section along an isomorphism of
`𝒪_X`-modules. -/
theorem nonvanishingLocus_congr (e : M ≅ N) (s : Γ(M, ⊤)) :
    nonvanishingLocus N (e.hom.app ⊤ s) = nonvanishingLocus M s := by
  ext x
  rw [mem_nonvanishingLocus_iff, mem_nonvanishingLocus_iff, ← mapFun_Γgerm,
    mem_maximalSmul_mapFun_iff]

/-! ### Ampleness -/

/-- **Stacks Tag 01PS.** An invertible `𝒪_X`-module is *ample* when `X` is quasi-compact and
every point of `X` lies in an affine nonvanishing locus of a global section of a positive tensor
power. Here the family of tensor powers is the explicit argument `pow`, and the affine open is
produced existentially rather than by bundling the nonvanishing locus with the openness theorem
of Tag 01CY; see the design choices in the module documentation, and
`isAmpleForPowers_iff_isOpen` for the equivalence with the bundled shape. -/
def IsAmpleForPowers (X : Scheme.{u}) (pow : ℤ → X.Modules) : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(pow (n : ℤ), ⊤), ∃ U : X.Opens,
    (U : Set X) = nonvanishingLocus (pow (n : ℤ)) s ∧ x ∈ U ∧ IsAffineOpen U

/-- Unfolding of `IsAmpleForPowers`: `X` is quasi-compact and every point lies in an affine open
equal to the nonvanishing locus of a global section of a positive tensor power. -/
theorem isAmpleForPowers_iff (X : Scheme.{u}) (pow : ℤ → X.Modules) :
    IsAmpleForPowers X pow ↔ CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : Γ(pow (n : ℤ), ⊤), ∃ U : X.Opens,
        (U : Set X) = nonvanishingLocus (pow (n : ℤ)) s ∧ x ∈ U ∧ IsAffineOpen U :=
  Iff.rfl

/-- The underlying space of a scheme carrying an ample invertible sheaf is quasi-compact. -/
theorem IsAmpleForPowers.compactSpace {X : Scheme.{u}} {pow : ℤ → X.Modules}
    (h : IsAmpleForPowers X pow) : CompactSpace X := h.1

/-- Every point of `X` lies in an affine nonvanishing locus of a global section of a positive
tensor power. -/
theorem IsAmpleForPowers.exists_affine_nonvanishingLocus {X : Scheme.{u}} {pow : ℤ → X.Modules}
    (h : IsAmpleForPowers X pow) (x : X) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(pow (n : ℤ), ⊤), ∃ U : X.Opens,
      (U : Set X) = nonvanishingLocus (pow (n : ℤ)) s ∧ x ∈ U ∧ IsAffineOpen U := h.2 x

/-- **Ampleness in the literal shape of Stacks Tag 01PS**, where the nonvanishing locus itself
carries the openness witness. The equivalence holds with no hypothesis: openness of the relevant
nonvanishing loci is part of what ampleness asserts, rather than an input to stating it. -/
theorem isAmpleForPowers_iff_isOpen (X : Scheme.{u}) (pow : ℤ → X.Modules) :
    IsAmpleForPowers X pow ↔ CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : Γ(pow (n : ℤ), ⊤), ∃ ho : IsOpen (nonvanishingLocus (pow (n : ℤ)) s),
        x ∈ nonvanishingLocus (pow (n : ℤ)) s ∧ IsAffineOpen ⟨_, ho⟩ := by
  refine and_congr_right fun _ => forall_congr' fun x => ?_
  constructor
  · rintro ⟨n, hn, s, U, hU, hxU, hUaff⟩
    have ho : IsOpen (nonvanishingLocus (pow (n : ℤ)) s) := hU ▸ U.isOpen
    refine ⟨n, hn, s, ho, by rwa [← hU], ?_⟩
    rwa [show (⟨_, ho⟩ : X.Opens) = U from Opens.ext hU.symm]
  · rintro ⟨n, hn, s, ho, hx, hoaff⟩
    exact ⟨n, hn, s, ⟨_, ho⟩, rfl, hx, hoaff⟩

/-- **Ampleness depends on the tensor powers only up to isomorphism.** Consequently the explicit
`pow` argument of `IsAmpleForPowers` may be instantiated with any construction of the tensor
powers of a given invertible module. -/
theorem isAmpleForPowers_congr {X : Scheme.{u}} {pow pow' : ℤ → X.Modules}
    (e : ∀ n : ℤ, pow n ≅ pow' n) : IsAmpleForPowers X pow ↔ IsAmpleForPowers X pow' := by
  have key : ∀ (p q : ℤ → X.Modules), (∀ n : ℤ, p n ≅ q n) →
      IsAmpleForPowers X p → IsAmpleForPowers X q := by
    rintro p q f ⟨hc, h⟩
    refine ⟨hc, fun x => ?_⟩
    obtain ⟨n, hn, s, U, hU, hxU, hUaff⟩ := h x
    exact ⟨n, hn, (f (n : ℤ)).hom.app ⊤ s, U,
      hU.trans (nonvanishingLocus_congr (f (n : ℤ)) s).symm, hxU, hUaff⟩
  exact ⟨key pow pow' e, key pow' pow fun n => (e n).symm⟩

end Stacks.Ample

end
