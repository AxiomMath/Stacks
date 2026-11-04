module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealSheafPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal

/-!
# Powers of a quasi-coherent sheaf of ideals on an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`ℐ ⊆ 𝒪_X` be a sheaf of ideals on its small étale site, that is, a sheaf submodule of the unit
module `SheafOfModules.unit (structureRingSheaf B S hS X)` — the form in which
`AlgebraicGeometry.Space.IsFiniteTypeQuasicoherentIdeal` and the `I` field of
`AlgebraicGeometry.Space.ResolutionPropertyDescentSituation` record an ideal sheaf, and the form
`AlgebraicGeometry.Space.IdealSheaves` already abbreviates.

No power is constructed here.  The development already has **two**, both of them landing in that
same type of sheaf submodules of `𝒪_X`:

* `SheafOfModules.idealSheafPow`, defined by the sieve of arrows along which a section restricts
  into the `n`-th power of the ideal of sections.  The graded algebra
  `AlgebraicGeometry.Space.kernelIdealGradedAlgebra` and the conormal algebra are built on it.
* `Stacks.Sites.idealPow`, the smallest sheaf of ideals with local membership containing those
  objectwise powers.  The affine-chart computation of its sections and the quasi-coherence of
  `ℐⁿ ·ℳ` are stated for it.

The point of this file is that these are the same object, and that the two bodies of API
therefore apply to one notion of `ℐⁿ`.

## Main definitions

* `AlgebraicGeometry.Space.idealSheafPowPushforward` is the direct image `π_*(ℐⁿ)` of the `n`-th
  power of an ideal sheaf on `Y` along a morphism `π : Y ⟶ X` of algebraic spaces, as an
  `𝒪_X`-module.

## Main results

* `AlgebraicGeometry.Space.idealSheafPow_eq_idealPow`: **the two power constructions agree.**
* `AlgebraicGeometry.Space.mul_mem_idealAt_idealSheafPow_add`: a product of local sections of
  `ℐⁿ` and `ℐᵐ` is a local section of `ℐ^(n+m)`.
* `AlgebraicGeometry.Space.idealUnitLocus_idealSheafPow` and
  `AlgebraicGeometry.Space.idealZeroLocus_idealSheafPow`: **a positive power of an ideal sheaf
  has the same unit locus, and hence the same zero locus, as the ideal sheaf itself**, and
  `AlgebraicGeometry.Space.idealZeroLocus_idealSheafPow_zero`: the zero locus of the zeroth power
  is empty.

## Implementation notes

The two powers agree because `SheafOfModules.powSieve` is the *largest* sieve witnessing the
local membership that defines the closure: a section lies in `Stacks.Sites.idealPow` exactly when
*some* covering sieve carries it into the objectwise powers, and any such sieve is contained in
`powSieve`, which is then covering too.  So the comparison needs no descent and no finiteness —
it is `Stacks.SheafOfModules.mem_sheafifySubmodule_iff` against
`SheafOfModules.mem_idealSheafPow_iff` in both directions.

Everything else below is a consequence of that comparison together with API already in the
development, and is stated for `SheafOfModules.idealSheafPow` because that is the spelling the
graded-algebra side uses:

* the zeroth power being everything is `Stacks.Sites.idealPow_zero`, and that a power is
  everything wherever `ℐ` is, is `Stacks.Sites.idealPow_obj_eq_top`.  Neither is restated for
  `SheafOfModules.idealSheafPow`, and neither is `SheafOfModules.idealSheafPow_one` or
  `SheafOfModules.idealSheafPow_antitone`, which already give `ℐ¹ = ℐ` and `ℐⁿ⁺¹ ≤ ℐⁿ`;
* commutativity of the sections of the structure sheaf, which the site-level statements about
  products carry as a hypothesis because `SheafOfModules` is indexed by a `RingCat`-valued sheaf,
  is the existing `AlgebraicGeometry.Space.structureRingSheaf_mul_comm`.

The comparison of the loci is an equality, not just an inclusion.  One half is
`AlgebraicGeometry.Space.idealUnitLocus_mono` along `ℐⁿ ≤ ℐ`.  The other needs no monotonicity:
the unit locus is cut out by the condition `ℐ(V) = 𝒪_X(V)` on an étale chart, and that condition
passes to every power.  So the positive powers of an ideal sheaf cut out the same point set,
which is why a condition such as clause (3) of Stacks 0855 is insensitive to replacing `ℐ`
by `ℐⁿ`.

## What is not proved

**`AlgebraicGeometry.Space.IsFiniteTypeQuasicoherentIdeal` is not shown to be inherited by the
powers** — neither its quasi-coherence half nor its finite-type half.  The mathematics for both
is already in the development, and what blocks the transport is an elaboration mismatch, not a
missing argument.

The results that would supply them —
`AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPowSubmodule` and the affine-chart
computation `AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_of_isAffine`, from which
finite type would follow by `AlgebraicGeometry.Space.fg_chartIdeal_of_isFiniteTypeOnSite`,
`Ideal.FG.pow` and `AlgebraicGeometry.Space.isFiniteTypeOnSite_iff_forall_fg_chartIdeal` — are
stated for `AlgebraicGeometry.Space.idealPowSubmodule`, that is for `ℐⁿ · ℳ`, and reaching `ℐⁿ`
from them means specializing to `ℳ = 𝒪_X` and using `Stacks.Sites.idealSmul_top_eq` to cancel the
`· 𝒪_X`.  That specialization is where it stops: `AlgebraicGeometry.Space.idealPowSubmodule` is
typed through `AlgebraicGeometry.Space.IdealSheaves`, whose site is spelled with the fields of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, whereas an ideal sheaf reaches this file spelled
through `AlgebraicGeometry.Space.structureRingSheaf` and `AlgebraicGeometry.Space.SmallEtale`'s
own topology and full-subcategory instance.  The two are definitionally equal but not
syntactically so, `rewrite` does not see through them, and the defeq check that would close the
gap does not terminate within the heartbeat limit.  Reconciling the two spellings — by restating
the `idealPowSubmodule` results in the `structureRingSheaf` spelling, or by giving a cheap
transport between the two site presentations — is the whole of the remaining work.

`AlgebraicGeometry.Space.idealSheafPow_eq_idealPow` is not affected: it is proved between two
constructions that are both reached through the `structureRingSheaf` spelling.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two constructions of `ℐⁿ` agree -/

/-- **The two powers of a sheaf of ideals on an algebraic space are the same sheaf of ideals.**
`SheafOfModules.idealSheafPow` is defined by the sieve of arrows along which a section restricts
into the `n`-th power of the ideal of sections; `Stacks.Sites.idealPow` is the smallest sheaf of
ideals with local membership containing those objectwise powers.

They agree because `SheafOfModules.powSieve` is the largest sieve witnessing that local
membership: a section lies in the closure exactly when some covering sieve witnesses it, and such
a sieve is contained in `powSieve`, which is therefore covering as well.

This reconciles the development's two power constructions, so that what has been proved of
either is available for the other. -/
theorem idealSheafPow_eq_idealPow (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) (n : ℕ) :
    SheafOfModules.idealSheafPow I n = Stacks.Sites.idealPow I n := by
  refine SheafOfModules.idealSheaf_ext fun V => le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · exact Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem hx fun _ _ hf => hf
  · obtain ⟨T, hT, hmem⟩ := Stacks.SheafOfModules.mem_sheafifySubmodule_iff.1 hx
    exact (SmallEtale.topology B S hS X.1).superset_covering (fun _ f hf => hmem f hf) hT

/-! ### Products of local sections of the powers -/

/-- **The product of a local section of `ℐⁿ` and a local section of `ℐᵐ` is a local section of
`ℐ^(n+m)`**, for a sheaf of ideals on an algebraic space.  The commutativity hypothesis of
`SheafOfModules.mul_mem_idealSheafPow_add` is discharged by the existing
`AlgebraicGeometry.Space.structureRingSheaf_mul_comm`. -/
theorem mul_mem_idealAt_idealSheafPow_add (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) (n m : ℕ)
    {V : (SmallEtale B S hS X.1)ᵒᵖ}
    {x y : ToType ((structureRingSheaf B S hS X).obj.obj V)}
    (hx : x ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I n) V)
    (hy : y ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I m) V) :
    x * y ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I (n + m)) V :=
  SheafOfModules.mul_mem_idealSheafPow_add I (structureRingSheaf_mul_comm B S hS X) n m hx hy

/-! ### The loci of the powers -/

/-- **A positive power of a sheaf of ideals has the same unit locus as the sheaf of ideals
itself.**  One inclusion is monotonicity of the unit locus along `ℐⁿ ≤ ℐ`; the other is that the
condition `ℐ(V) = 𝒪_X(V)` cutting out the unit locus passes to every power, which is
`Stacks.Sites.idealPow_obj_eq_top`. -/
theorem idealUnitLocus_idealSheafPow (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) {n : ℕ} (hn : 0 < n) :
    idealUnitLocus B S hS X (SheafOfModules.idealSheafPow I n) =
      idealUnitLocus B S hS X I := by
  have hle : SheafOfModules.idealSheafPow I n ≤ I := by
    have h := SheafOfModules.idealSheafPow_antitone I hn
    rwa [SheafOfModules.idealSheafPow_one] at h
  refine Set.Subset.antisymm (idealUnitLocus_mono B S hS X hle) ?_
  rintro x ⟨V, hV, hx⟩
  refine ⟨V, ?_, hx⟩
  rw [idealSheafPow_eq_idealPow B S hS X I n]
  exact Stacks.Sites.idealPow_obj_eq_top I hV n

/-- **A positive power of a sheaf of ideals has the same zero locus as the sheaf of ideals
itself**: `|V(ℐⁿ)| = |V(ℐ)|` for `n ≥ 1`. -/
theorem idealZeroLocus_idealSheafPow (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) {n : ℕ} (hn : 0 < n) :
    idealZeroLocus B S hS X (SheafOfModules.idealSheafPow I n) =
      idealZeroLocus B S hS X I := by
  rw [idealZeroLocus, idealZeroLocus, idealUnitLocus_idealSheafPow B S hS X I hn]

/-- **The zero locus of the zeroth power of a sheaf of ideals is empty**, the zeroth power being
the whole structure sheaf by `Stacks.Sites.idealPow_zero`. -/
theorem idealZeroLocus_idealSheafPow_zero (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) :
    idealZeroLocus B S hS X (SheafOfModules.idealSheafPow I 0) = ∅ := by
  have h : SheafOfModules.idealSheafPow I 0 = ⊤ :=
    (idealSheafPow_eq_idealPow B S hS X I 0).trans (Stacks.Sites.idealPow_zero I)
  rw [h, idealZeroLocus_top]

/-! ### The direct image of a power -/

/-- **The direct image `π_*(ℐⁿ)`** of the `n`-th power of a sheaf of ideals `ℐ ⊆ 𝒪_Y` along a
morphism `π : Y ⟶ X` of algebraic spaces, as an `𝒪_X`-module: the power read as a sheaf of
modules and pushed forward along `AlgebraicGeometry.Space.modulePushforward`. -/
noncomputable abbrev idealSheafPowPushforward {X Y : AlgebraicSpaces B S hS} (π : Y ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule) (n : ℕ) :
    Modules.{u, u} B S hS X.1 X.2 :=
  (modulePushforward B S hS π).obj (SheafOfModules.idealSheafPow I n).toSheafOfModules

/-- The direct image of the first power is the direct image of the sheaf of ideals itself. -/
theorem idealSheafPowPushforward_one {X Y : AlgebraicSpaces B S hS} (π : Y ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule) :
    idealSheafPowPushforward B S hS π I 1 =
      (modulePushforward B S hS π).obj I.toSheafOfModules := by
  rw [idealSheafPowPushforward, SheafOfModules.idealSheafPow_one]

end AlgebraicGeometry.Space

end
