module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerArbitraryIndex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import Mathlib.Data.Set.PowersetCard
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of an exterior power of a finite locally free sheaf of modules

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `F` a sheaf of modules over
the underlying sheaf of rings which is finite locally free of rank `r`. Then the degree-`n`
exterior power `⋀ⁿ F` is finite locally free of rank `binom(r, n)`.

The proof is local. Finite local freeness of rank `r` provides a covering `{U i}` of the terminal
object together with isomorphisms `F|_{U i} ≅ ⨁_{γ i} O♯|_{U i}` whose index types `γ i` are
equivalent to `Fin r`. Over each member of that covering the exterior power is computed by two
isomorphisms that are already available:

* `Stacks.SheafOfModules.exteriorPowerOverIso`, which identifies `(⋀ⁿ F)|_U` with the degree-`n`
  exterior power computed on the slice site `(Over U, J.over U)`;
* `Stacks.SheafOfModules.exteriorPowerFreeIsoOfIsoAnyIndex`, which identifies the degree-`n`
  exterior power of a sheaf of modules isomorphic to the free module on `γ` with the free module
  on `Set.powersetCard γ n`, the `n`-element subsets of `γ`.

Composing them exhibits `⋀ⁿ F` as free over each member of the covering, on an index type of
cardinality `binom(r, n)` because `γ i ≃ Fin r`. The rank count is `Set.powersetCard.card`.

For `n = r` the rank is `binom(r, r) = 1`, so the top exterior power of a sheaf of modules of
rank `r` on a scheme is invertible — the determinant line bundle.

## Main results

* `Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower`: on a site, the degree-`n`
  exterior power of a sheaf of modules that is finite locally free of rank `r` is finite locally
  free of rank `binom(r, n)`.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower`: the same statement
  for `AlgebraicGeometry.Scheme.Modules.exteriorPower` on a scheme.
* `AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self`: the top exterior power
  `⋀^r F` of a sheaf of modules of rank `r` on a scheme is invertible.

## Implementation notes

**The exterior algebra is a hypothesis at the site level.** Section 17.21 pins the exterior
algebra of a sheaf of modules only up to canonical isomorphism, so the general statement
quantifies over a package `A : SheafOfModules.TensorExteriorSymmetricAlgebras J F` and concerns
`A.exteriorPower n`; the comparison between two packages is
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso`. The scheme-level statements
are about the chosen package `SheafOfModules.algebras`, which is the one
`AlgebraicGeometry.Scheme.Modules.exteriorPower` is defined from.

**The two spellings of the structure sheaf of rings.** A scheme's sheaf of modules lives over
`AlgebraicGeometry.Scheme.ringCatSheaf`, which is `sheafCompose` applied to `X.sheaf`, whereas
the site-level development works over `CategoryTheory.Sheaf.toRingCat`, whose underlying presheaf
of rings is syntactically `X.sheaf.obj ⋙ forget₂ _ _`. The two are definitionally equal but do
not match at reducible transparency, so the hypothesis of finite local freeness has to be
restated at the second spelling before the site-level theorem applies; that is the one `haveI` in
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower`.

**Arbitrary index types are available but not needed.** `exteriorPowerFreeIsoOfIsoAnyIndex`
carries no finiteness hypothesis on the index type, so the local index types `γ i` are used as
they come rather than being transported to `Fin r` first; the linear order Mathlib's exterior
basis needs is supplied by well-ordering each `γ i`, and the equivalence `γ i ≃ Fin r` enters
only through the cardinality count.

**No `@[stacks]` attribute.** Tag 01CK clause (6) asserts that the tensor, exterior and symmetric
powers of a *locally free* sheaf of modules are again locally free, with no claim about ranks and
with arbitrary index sets allowed; what is proved here is the fixed-finite-rank statement for the
exterior power alone, so it is neither that clause nor a clause of Tag 01C6, which only defines
the three notions. The clause itself is
`Stacks.SheafOfModules.isLocallyFree_exteriorPower` and its two companions in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePowers`, which use
`Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree` below with the rank bookkeeping
deleted. Tag 0FEE is the Chern-class identity for the alternating product of the
exterior powers, and the rank computation is a step in its proof rather than its statement; the
same holds for Tag 0B3T, whose invertibility assertion is about the reflexive hull of the top
exterior power of a coherent sheaf on an integral regular surface. These results are
infrastructure for 0FEE and 0B3T, not formalizations of them.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe v u₁ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}

/-- The degree-`n` exterior power of a sheaf of modules, restricted to an object `U` over which
the module becomes free on an index type `γ`, is free on the `n`-element subsets of `γ`.

This is the composite of `Stacks.SheafOfModules.exteriorPowerOverIso`, which passes from the
exterior power computed on `(C, J)` to the one computed on the slice site over `U`, and
`Stacks.SheafOfModules.exteriorPowerFreeIsoOfIsoAnyIndex`, which computes the exterior power of a
free module. The exterior algebra on the slice site is taken to be the chosen one,
`SheafOfModules.algebras`, so no second package has to be supplied by the caller. -/
noncomputable def exteriorPowerOverFreeIsoOfIsoFree
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (U : C) (n : ℕ)
    (γ : Type u) [LinearOrder γ]
    (e : F.over U ≅ _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over U) γ) :
    (A.exteriorPower n).over U ≅
      _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over U)
        ↥(Set.powersetCard γ n) :=
  let B := _root_.SheafOfModules.algebras (Osharp := Osharp.over U) (J.over U)
    (show _root_.SheafOfModules.{u} (Sheaf.toRingCat (J.over U) (Osharp.over U)) from F.over U)
  (exteriorPowerOverIso F U n A.exterior A.exteriorGenerator A.exterior_isExteriorAlgebra
      B.exterior B.exteriorGenerator B.exterior_isExteriorAlgebra).trans
    (exteriorPowerFreeIsoOfIsoAnyIndex (J.over U) γ n B e)

/-- **The degree-`n` exterior power of a sheaf of modules that is finite locally free of rank `r`
is finite locally free of rank `binom(r, n)`.**

A trivializing covering for `F` with index types `γ i ≃ Fin r` is a trivializing covering for
`⋀ⁿ F` with index types the `n`-element subsets of `γ i`, of which there are `binom(r, n)`. -/
@[ega "0 5.5.4" "more general", sga "6 X 6.1" "special case"]
theorem isFiniteLocallyFreeOfRank_exteriorPower
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (r n : ℕ)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, v, u₁} F r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, v, u₁}
      (A.exteriorPower n) (r.choose n) := by
  classical
  obtain ⟨q, hq, hr⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  let : ∀ i : q.I, LinearOrder ((q.generators i).I) :=
    fun _ => IsWellOrder.linearOrder WellOrderingRel
  have E : ∀ i : q.I, _root_.SheafOfModules.free
      (R := (Sheaf.toRingCat J Osharp).over (q.X i)) ↥(Set.powersetCard ((q.generators i).I) n) ≅
      (A.exteriorPower n).over (q.X i) := fun i =>
    (exteriorPowerOverFreeIsoOfIsoFree A (q.X i) n ((q.generators i).I)
      (asIso (q.generators i).π).symm).symm
  have hcard : ∀ i : q.I,
      Nonempty (↥(Set.powersetCard ((q.generators i).I) n) ≃ Fin (r.choose n)) := fun i => by
    obtain ⟨e⟩ := hr i
    have : Finite ((q.generators i).I) := Finite.of_equiv _ e.symm
    exact ⟨Finite.equivFinOfCardEq
      (by rw [Set.powersetCard.card, Nat.card_eq_of_equiv_fin e])⟩
  exact ⟨⟨q.I, q.X, q.coversTop, fun i =>
      ⟨↥(Set.powersetCard ((q.generators i).I) n),
        ((A.exteriorPower n).over (q.X i)).freeHomEquiv (E i).hom,
        by rw [Equiv.symm_apply_apply]; infer_instance⟩⟩,
    ⟨fun i => by
      dsimp only [_root_.SheafOfModules.GeneratingSections.π]
      rw [Equiv.symm_apply_apply]
      infer_instance⟩,
    hcard⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- **The degree-`n` exterior power of a sheaf of modules on a scheme that is finite locally free
of rank `r` is finite locally free of rank `binom(r, n)`.** -/
@[ega "0 5.5.4" "special case"]
theorem isFiniteLocallyFreeOfRank_exteriorPower {X : Scheme.{u}} (F : X.Modules) (r n : ℕ)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.exteriorPower F n) (r.choose n) :=
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (_root_.Opens.grothendieckTopology X) X.sheaf) F r := hF
  Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower
    (J := _root_.Opens.grothendieckTopology X) (Osharp := X.sheaf)
    (_root_.SheafOfModules.algebras _ F) r n

/-- **The determinant line bundle.** The top exterior power `⋀^r F` of a sheaf of modules on a
scheme that is finite locally free of rank `r` is invertible: its rank is `binom(r, r) = 1`, and a
sheaf of modules of rank one on a ringed space is invertible by clause 1 of Tag 0B8M. -/
@[ega "0 5.5.4" "Case p=n", sga "6 X 5.1" "special case", sga "6 X 6.2" "special case"]
theorem isInvertible_exteriorPower_self {X : Scheme.{u}} (F : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property
      (Scheme.Modules.exteriorPower F r) :=
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.exteriorPower F r) 1 := by
    simpa only [Nat.choose_self] using isFiniteLocallyFreeOfRank_exteriorPower F r r
  Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

end AlgebraicGeometry.Scheme.Modules

end
