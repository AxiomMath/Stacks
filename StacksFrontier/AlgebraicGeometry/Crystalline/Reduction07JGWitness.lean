module

public import Mathlib.Algebra.Module.PUnit
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionTensor
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiToposMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorCrystal07JG

/-!
# The degenerate datum over the empty object, and why it is not a reduction datum

`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG` is the clauses of the
reduction datum of [Stacks, Tag 07JG] with no condition on the system of levels of `Cris(X/S)`
over which the sections are taken.  This file exhibits an inhabitant of it, for every global
crystalline situation, and proves that the inhabitant does **not** extend to
`...SmallSite.Reduction07JG` — the bundle through which [Stacks, Proposition 60.17.4, Tag 07JH]
and [Stacks, Proposition 60.21.3, Tag 07LG] are stated, which adds the field
`levelSystem_isLevel`.

The inhabitant is **degenerate**, and deliberately so: its system of levels is constant at the
object `(∅, ∅, ∅)` of `Cris(X/S)`, the empty open of `X` thickened by itself, whose ring of
sections is the zero ring.  Both halves of the file are therefore statements about the *strength
of the clauses*, not mathematics about [Stacks, Tag 07JG]: they hold for a system at which every
statement the tags make is false, and the extra field is what excludes it.

This module previously presented the datum as a witness of `...SmallSite.Reduction07JG` itself
and said that it "settles" the nonemptiness of the hypothesis of the two tags.  That reading was
the defect, not the fix: it is the clauses that are satisfied, and the extra field is now there
precisely so that nothing degenerate satisfies the bundle.  This note also previously spoke of
"ten clauses" over a single object `site` and of the field `site_isLevel`; the bundle has since
been reshaped to run over a system of levels, so the degenerate datum is now the constant system
at the empty object and the field it fails is `levelSystem_isLevel`.

## Main definitions

Everything is in the namespace `Crystalline`, the crystalline material in its subnamespace
`GlobalCrystallineSituation.SmallSite`.

* `Crystalline.ringHomOfSubsingleton`, `Crystalline.ringEquivOfSubsingleton`,
  `Crystalline.addEquivOfSubsingleton`, `Crystalline.addMonoidHomOfSubsingleton` and
  `Crystalline.linearEquivOfSubsingleton` — the unique maps into, and between, zero rings and
  subsingleton additive groups and modules.
* `Crystalline.trivialDividedPowerRing` — the zero ring with its zero divided power ideal, as a
  `DividedPowerRing`.
* `Crystalline.trivialBaseHom` and `Crystalline.trivialDerivation` — the structure map of any
  base ring into it, and the zero divided power derivation into the zero module.
* `Crystalline.trivialFirstOrderCrystal` — the zero module as an object of
  `Crystalline.FirstOrderCrystal` over that ring, with all four of the items of
  [Stacks, Tag 07JG] that structure takes as fields discharged.
* `Crystalline.trivialBasis` and `Crystalline.trivialTaylorCrystal` — a basis of the zero module
  on any index type, and the zero module as an object of `Crystalline.TaylorCrystal`, the source
  of the functor `Crystalline.taylorCrystalsToPairs` (an algebraic model of the functor of
  [Stacks, Tag 07JG]); so that category is not empty either.
* `...SmallSite.botLevelSystem` — the constant system of levels at the empty object.
* `Crystalline.GlobalCrystallineSituation.SmallSite.preReduction07JGBot` — **the degenerate
  datum satisfying the clauses, over the constant system at the empty object of `Cris(X/S)`**.
* `...SmallSite.sectionsDividedPowerRing` and `...SmallSite.sectionsDifferentials` — the divided
  power ring `Γ(T, 𝒪_T)` and the module `Γ(T, Ω_{T/S,δ})` of an arbitrary object of `Cris(X/S)`,
  with the three module instances a trivial square-zero extension over them needs.

## Main results

* `Crystalline.subsingleton_of_ringHom` — a ring receiving a map from the zero ring is the zero
  ring.
* `Crystalline.hasSum_of_subsingleton` — every family sums to everything in a subsingleton
  topological additive monoid.  This is what discharges the coordinate expansion of the zero
  connection.
* `Crystalline.finite_notMem_pSmul_of_subsingleton` — in a subsingleton module no family has a
  member outside `p M`, which discharges the `p`-adic convergence clause of the composite
  coordinate operators.
* `...SmallSite.subsingleton_sections_opensFree_bot` — the ring of sections of `𝒪_{X/S}` over the
  object `(∅, ∅, ∅)` of `Cris(X/S)` is the zero ring.
* `...SmallSite.subsingleton_sections_firstOrderThickening` — and so is the ring of sections over
  the first-order universal thickening of any object whose own section ring is zero, because the
  first projection of [Stacks, Tag 07J2] restricts sections from the one to the other.
* `...SmallSite.subsingleton_levelRingLimit` and `...SmallSite.subsingleton_levelSectionsLimit` —
  the limits over a system of levels whose section rings and modules of sections all vanish
  vanish too, being subobjects of products of zero objects.  These are what make the two limit
  identifications of the degenerate datum available.
* `...SmallSite.nonempty_preReduction07JG` — **the clauses are inhabited**, for every global
  crystalline situation, every base ring, every prime and every index type of coordinates.
* `...SmallSite.not_isOverWholeSpace_botObject` — **the empty object is not a thickening of the
  whole of `X`** as soon as `X` has a point, and `...SmallSite.not_isIsomorphic_botObject_level` —
  it is therefore isomorphic to no finite level of the system of [Stacks, Tag 07JN].
* `...SmallSite.not_levelSystem_isLevel_preReduction07JGBot` — **the degenerate datum does not
  satisfy the field `...SmallSite.Reduction07JG.levelSystem_isLevel`**, and
  `...SmallSite.levelSystem_obj_ne_botObject` — no level of a reduction datum is the empty
  object.
* `...SmallSite.sectionsDividedPowerRingEquiv` and `...SmallSite.firstOrderSectionsRingEquiv` —
  at an arbitrary object of `Cris(X/S)` the section ring of `(U, T, δ)` *is* the divided power
  ring `Γ(T, 𝒪_T)` and the section ring of its first-order universal thickening of
  [Stacks, Tag 07J2] *is* the trivial square-zero extension `Γ(T, 𝒪_T) ⊕ Γ(T, Ω_{T/S,δ})`, both
  by `RingEquiv.refl`.

## What is and is not proved

Four things are proved.  First, the clauses of `...SmallSite.PreReduction07JG` form a nonempty
type.  Second — and this is what the module is for now — the datum that inhabits them does **not**
satisfy the extra field of `...SmallSite.Reduction07JG`, so no statement quantified over reduction
data is refuted by it.  Third, the section rings of an arbitrary object of `Cris(X/S)` and of its
first-order thickening are the divided power ring and its trivial square-zero extension on the
nose.  Fourth, the two algebraic source categories of the functor of [Stacks, Tag 07JG] —
`Crystalline.FirstOrderCrystal` and `Crystalline.TaylorCrystal` — are nonempty, so neither
functor is a functor out of an empty category.

Nothing here proves any part of [Stacks, Tag 07JG], [Stacks, Tag 07JH] or [Stacks, Tag 07LG],
and no attribute is placed.  Those tags are `...SmallSite.crystalPairFunctor`,
`...SmallSite.crystalPairFunctor_isEquivalence` and
`...SmallSite.crystalPairDeRhamComplex_computesCohomology`, built directly from the whole-space
system of [Stacks, Tag 07JN] and not through a reduction datum.

The datum is the degenerate one, and the reader should read it as a *diagnosis of the clauses*
rather than as mathematics about the tag.  Three things follow from it and should be said plainly.

1. **The clauses alone are not the hypothesis of either tag.**  The witness does not show that
   `...SmallSite.Equivalence07JH R` and `...SmallSite.Computes07LG ... R ...` are statements
   about a nonempty type in any reassuring sense: it shows that the clauses are satisfied where
   the tags' conclusions are false, so being inhabited is no reassurance; the clauses form a
   structure of their own and the two tags are stated against the bundle that adds
   `levelSystem_isLevel`.

2. **The clauses do not pin down the setting of the source, and both statements are false at
   this datum.**  Over the empty object every ring and every module of sections is zero, hence so
   is every limit over the constant system at it, so the reduction functor is constant at the zero
   first-order crystal.  For a situation whose site has any nonzero cohomology, the complex
   `...SmallSite.crystalDeRhamComplex` built from this datum is zero while `H^j(Cris(X/S), ℱ)` is
   not, so the conclusion of [Stacks, Tag 07LG] fails; and the constant functor is not an
   equivalence onto the pairs, so that of [Stacks, Tag 07JH] fails too.  Neither failure is proved
   here — proving it needs a situation with computed cohomology, which this library does not have.
   What **is** proved here is the statement that makes the failure harmless:
   `...SmallSite.not_levelSystem_isLevel_preReduction07JGBot`, that this datum's system is
   isomorphic to the system of [Stacks, Tag 07JN] for no situation with a point.  The route is
   `...SmallSite.not_isOverWholeSpace_botObject`: an isomorphism of systems is in particular an
   isomorphism in degree zero, every object of that system is a thickening of the whole of `X`,
   and the empty open is not.

3. **The two ring identifications are available over every object, but they discharge no
   clause of the datum.**  What is true, and proved here, is that `...SmallSite.sectionsDividedPowerRingEquiv` and
   `...SmallSite.firstOrderSectionsRingEquiv` produce an identification of the section ring of an
   arbitrary `B : CrystallineThickening S` with the divided power ring `Γ(T, 𝒪_T)`, and of the
   section ring of its first-order universal thickening with
   `Γ(T, 𝒪_T) ⊕ Γ(T, Ω_{T/S,δ})`, as the identity.  That `Γ(T', 𝒪_{T'})` is that trivial
   square-zero extension is the construction of the first-order universal thickening in
   `StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickenings.lean`.

   This does not discharge a clause.  The bundle's `ringEquiv`
   asks for `D` to be the *inverse limit* `lim_e Γ(T_e, 𝒪_{T_e})` of the section rings of the
   levels, which is the identification of the `p`-adically completed divided power envelope of
   [Stacks, Tag 07J8] that [Stacks, Tag 07JN] supplies, and the bundle asks only for
   the weaker `thickeningRingHom`, a compatible family of reductions, because the
   limit of the section rings of the first-order thickenings is `D ⊕ Ω̂` with the forms completed.
   Neither is available at a single object.  The fields that have no inhabitant for a general
   system are therefore `ringEquiv`, `baseChange` and `baseChange_tmul` — the last two being the
   inverse of the canonical map `Crystalline.GlobalCrystallineSituation.diffAction`, carried as
   `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` and constructed only for
   `ℱ = 𝒪_{X/S}` — together with the four carried items of `Crystalline.FirstOrderCrystal`, which
   enter through `functor`.

   For the *particular* system that `Crystalline.GlobalCrystallineSituation.SmallSite`
   `.Reduction07JG` pins, `ringEquiv` is not among them: it is
   `...SmallSite.envelopeLevelRingLimitEquiv` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemLevelRings.lean`, which
   identifies the completed envelope `D(n)` with the limit of the section rings of the levels of
   `...SmallSite.wholeSpaceSystem`.  It is unavailable at a single object and for a general
   system, which is what this point says, but it is available at the system the source uses.

The degenerate witness avoids all of those because a module over the zero ring is zero, so every
clause of the datum is an equation between elements of a subsingleton.  That is the whole content
of the construction and the reason it is cheap.

## Implementation notes

The empty object is `(Crystalline.GlobalCrystallineSituation.opensFree S).obj ⊥`, the object
`(V, V, ∅)` of [Stacks, Tag 07I8] for `V` the empty open of `X`; its ambient scheme is the empty
scheme and `Γ(∅, 𝒪) = 0` by `AlgebraicGeometry.Scheme.Opens.topIso` and the Mathlib instance
`Subsingleton Γ(X, ⊥)`.

Triviality of the section ring over the first-order thickening is obtained from the restriction
ring homomorphism along `Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysP₀`
rather than from the square-zero description, so the proof needs nothing about the thickening
beyond the existence of that projection.

The subsingleton facts the record needs are stated in the indexed shape
`Subsingleton Γ((botLevelSystem S).obj e, -)`, as
`...SmallSite.subsingleton_sections_botLevelSystem` and
`...SmallSite.subsingleton_sections_firstOrderThickening_botLevelSystem`, rather than at
`botObject S`: the two are definitionally equal, but instance synthesis does not unfold
`CategoryTheory.Functor.const` and so does not find a fact stated at the latter when the former
is asked for.

The divided power ring is `PUnit` with the zero ideal, and the module of differentials is `PUnit`
as well, which is what makes all three of `Module D Ω`, `Module Dᵐᵒᵖ Ω` and
`IsCentralScalar D Ω` available from Mathlib's `PUnit` instances with nothing to prove.

The refutation runs through the thickened scheme rather than through the section ring: the empty
object fails `...SmallSite.IsOverWholeSpace` because an isomorphism from the empty open subscheme
of `X` to `X` would carry a point of `X` into an empty scheme, which needs nothing about rings.
The condition is read up to isomorphism of `Cris(X/S)`, which is what
`...SmallSite.isOverWholeSpace_of_isIsomorphic` is for, and an isomorphism of level systems is
restricted to one degree by `CategoryTheory.Iso.app`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07I8](https://stacks.math.columbia.edu/tag/07I8)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u v w uI

namespace Crystalline

/-! ### Maps between subsingletons -/

/-- **The unique ring homomorphism into the zero ring.**  Every value is `0`, and every law is an
equation in a subsingleton. -/
def ringHomOfSubsingleton (R : Type v) (T : Type w) [NonAssocSemiring R] [NonAssocSemiring T]
    [Subsingleton T] : R →+* T where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

/-- **The unique ring isomorphism between two zero rings.** -/
def ringEquivOfSubsingleton (R : Type v) (T : Type w) [NonAssocSemiring R] [NonAssocSemiring T]
    [Subsingleton R] [Subsingleton T] : R ≃+* T where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _

/-- **The unique additive isomorphism between two subsingleton additive monoids.** -/
def addEquivOfSubsingleton (M : Type v) (N : Type w) [AddZeroClass M] [AddZeroClass N]
    [Subsingleton M] [Subsingleton N] : M ≃+ N where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _

/-- **The unique additive map into a subsingleton additive monoid.** -/
def addMonoidHomOfSubsingleton (M : Type v) (N : Type w) [AddZeroClass M] [AddZeroClass N]
    [Subsingleton N] : M →+ N where
  toFun _ := 0
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

/-- **A ring that receives a homomorphism from the zero ring is the zero ring**, because `1` is
the image of `0`. -/
theorem subsingleton_of_ringHom {R : Type v} {T : Type w} [NonAssocSemiring R]
    [NonAssocSemiring T] [Subsingleton R] (f : R →+* T) : Subsingleton T :=
  subsingleton_of_zero_eq_one
    (by rw [← f.map_zero, Subsingleton.elim (0 : R) 1, f.map_one])

/-- **A module over the zero ring is the zero module**, stated for the carrier of an object of
`ModuleCat`, which is the shape in which the sections of a sheaf of modules appear. -/
theorem subsingleton_moduleCat {R : Type v} [Ring R] [Subsingleton R] (M : ModuleCat.{w} R) :
    Subsingleton (M : Type w) :=
  Module.subsingleton R (M : Type w)

/-- **In a subsingleton topological additive monoid every family sums to every element.**  The
partial sums are constant, so they converge to anything.  This is what makes the coordinate
expansion of [Stacks, Tag 07JG] hold for the zero connection without choosing operators.

The topology is an explicit argument because the one the coordinate expansion of
`Crystalline.IsCoordinateExpansion` uses is introduced by a `letI` inside that definition, so it
has to be recovered by unification rather than by instance synthesis. -/
theorem hasSum_of_subsingleton {M : Type v} {ι : Type w} [AddCommMonoid M]
    (t : TopologicalSpace M) [Subsingleton M] (f : ι → M) (a : M) : HasSum f a :=
  Filter.Tendsto.congr (fun _ ↦ Subsingleton.elim a _) tendsto_const_nhds

/-- **In a subsingleton module nothing is outside `p M`**, so every family of its elements has
finitely many members outside it — the empty set of them.  This discharges the `p`-adic
convergence clause of the composite coordinate operators of [Stacks, Tag 07JG] for the zero
module. -/
theorem finite_notMem_pSmul_of_subsingleton (p : ℕ) (D : Type u) [CommRing D] (M : Type v)
    [AddCommGroup M] [Module D M] [Subsingleton M] {α : Type w} (f : α → M) :
    {a : α | f a ∉ pSmul p D M}.Finite := by
  refine Set.Finite.subset Set.finite_empty fun a ha ↦ absurd ?_ ha
  rw [Subsingleton.elim (f a) 0]
  exact Submodule.zero_mem _

/-- **A linear equivalence between two subsingleton modules**, the unique map in either
direction. -/
def linearEquivOfSubsingleton (D : Type u) [CommRing D] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module D M] [AddCommGroup N] [Module D N] [Subsingleton M]
    [Subsingleton N] : M ≃ₗ[D] N where
  toFun _ := 0
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-! ### The zero divided power ring and the zero first-order crystal -/

/-- **The zero ring with its zero divided power ideal.**  This is the divided power ring over
which the degenerate reduction datum is written: every module over it vanishes. -/
noncomputable def trivialDividedPowerRing : DividedPowerRing.{u} :=
  .of PUnit.{u + 1} ⊥ (dividedPowersBot _)

/-- The zero divided power ring is the zero ring. -/
instance instSubsingletonTrivialDividedPowerRing :
    Subsingleton (trivialDividedPowerRing.{u} : Type u) :=
  inferInstanceAs (Subsingleton PUnit.{u + 1})

/-- Every module over `Crystalline.trivialDividedPowerRing` is the zero module. -/
instance instSubsingletonTrivialDividedPowerModule (M : Type v) [AddCommMonoid M]
    [Module (trivialDividedPowerRing.{u} : Type u) M] : Subsingleton M :=
  Module.subsingleton (trivialDividedPowerRing.{u} : Type u) M

/-- **The structure map of any base ring into the zero divided power ring.** -/
noncomputable def trivialBaseHom (A : Type u) [CommRing A] :
    A →+* (trivialDividedPowerRing.{u} : Type u) :=
  ringHomOfSubsingleton A _

/-- **The zero divided power derivation of the zero divided power ring into the zero module.**
Both the Leibniz rule and the divided power chain rule are equations in a subsingleton. -/
noncomputable def trivialDerivation (A : Type u) [CommRing A] :
    DividedPowerDerivation A trivialDividedPowerRing.{u} (trivialBaseHom A) PUnit.{u + 1} where
  toDerivation := 0
  map_ringHom' _ := Subsingleton.elim _ _
  map_dpow' _ _ _ _ := Subsingleton.elim _ _

/-- **The zero module as a first-order crystal datum over the zero divided power ring.**  The
comparison map is zero; `p`-adic completeness is Mathlib's
`IsAdicComplete.of_subsingleton`; the coordinate operators are the identities, which expand the
connection by `Crystalline.hasSum_of_subsingleton`; and integrability and topological
quasi-nilpotence hold because the module is zero, the latter because the set of pairs `(i, k)`
with `θ_i^k m ∉ p M` is empty. -/
noncomputable def trivialFirstOrderCrystal (A : Type u) [CommRing A] (p : ℕ) {ι : Type uI}
    (dx : ι → PUnit.{u + 1}) :
    FirstOrderCrystal.{u, u, u, uI, u} A trivialDividedPowerRing.{u} (trivialBaseHom A)
      PUnit.{u + 1} (trivialDerivation A) p dx where
  carrier := PUnit.{u + 1}
  comparison :=
    { toFun _ := 0
      map_add' _ _ := Subsingleton.elim _ _
      reduction' _ := Subsingleton.elim _ _
      semilinear' _ _ := Subsingleton.elim _ _ }
  isPAdicallyComplete := IsAdicComplete.of_subsingleton _ _
  hasCoordinateOperators := ⟨fun _ ↦ id, fun _ ↦ hasSum_of_subsingleton _ _ _⟩
  isIntegrable _ _ _ _ := funext fun _ ↦ Subsingleton.elim _ _
  isTopologicallyQuasiNilpotent _ _ m := by
    have h : {q : ι × ℕ | q.2 ≠ 0 ∧
        ((fun _ ↦ id) q.1 : PUnit.{u + 1} → PUnit.{u + 1})^[q.2] m ∉
          pSmul p (trivialDividedPowerRing.{u} : Type u) PUnit.{u + 1}} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun q hq ↦ hq.2 (by
        rw [Subsingleton.elim (((fun _ ↦ id) q.1 : PUnit.{u + 1} → PUnit.{u + 1})^[q.2] m) 0]
        exact Submodule.zero_mem _)
    rw [h]
    exact Set.finite_empty

/-- **A basis of the zero module over the zero divided power ring**, on any index type at all.
Over the zero ring every module vanishes, including `ι →₀ D`, so the unique linear map between
them is an equivalence.  This is what lets the index type of the coordinates stay arbitrary in
`Crystalline.trivialTaylorCrystal`, where a basis of the differentials is a parameter. -/
noncomputable def trivialBasis {ι : Type uI} :
    Module.Basis ι (trivialDividedPowerRing.{u} : Type u) PUnit.{u + 1} :=
  Module.Basis.ofRepr (linearEquivOfSubsingleton _ _ _)

/-- **The zero module as a `Crystalline.TaylorCrystal` over the zero divided power ring.**  Its
tower of levels is constant at the zero module, so the annihilation of the levels and the
identification with the limit are equations between subsingletons; its composite coordinate
operators are the identities, which form a monomial family and expand the zero connection by
`Crystalline.hasSum_of_subsingleton`; and the convergence clause holds because no element lies
outside `p M`, by `Crystalline.finite_notMem_pSmul_of_subsingleton`.

It plays for `Crystalline.taylorCrystalsToPairs` the role that
`Crystalline.trivialFirstOrderCrystal` plays for `Crystalline.firstOrderCrystalsToPairs`: the
source category of that functor is not empty, so the functor is not a functor out of nothing.
It is degenerate, and like `Crystalline.trivialFirstOrderCrystal` it is **not** a claim that the
category is inhabited over a nonzero ring; that needs the geometric input listed in the module
documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCrystal07JG.lean`. -/
noncomputable def trivialTaylorCrystal (A : Type u) [CommRing A] (p : ℕ) {ι : Type uI}
    (dx : ι → PUnit.{u + 1}) :
    TaylorCrystal.{u, u, u, uI, u} A trivialDividedPowerRing.{u} (trivialBaseHom A)
      PUnit.{u + 1} (trivialDerivation A) p dx trivialBasis
      (fun _ ↦ Subsingleton.elim _ _) where
  carrier := PUnit.{u + 1}
  comparison :=
    { toFun _ := 0
      map_add' _ _ := Subsingleton.elim _ _
      reduction' _ := Subsingleton.elim _ _
      semilinear' _ _ := Subsingleton.elim _ _ }
  levels _ := PUnit.{u + 1}
  transition _ := 0
  shift := 0
  level_annihilate _ :=
    le_antisymm (fun x _ ↦ (Submodule.mem_bot _).mpr (Subsingleton.elim x 0)) bot_le
  levelEquiv := linearEquivOfSubsingleton _ _ _
  theta _ := id
  thetaPow _ := id
  isThetaMonomialFamily := ⟨rfl, fun _ _ ↦ rfl⟩
  isCoordinateExpansion _ := hasSum_of_subsingleton _ _ _
  finite_thetaPow_notMem_pSmul m :=
    finite_notMem_pSmul_of_subsingleton p (trivialDividedPowerRing.{u} : Type u)
      PUnit.{u + 1} fun _ : ι →₀ ℕ ↦ (id m : PUnit.{u + 1})

namespace GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The empty object of `Cris(X/S)` -/

/-- **The empty open of `X`, thickened by itself, as an object of `Cris(X/S)`.**  This is the
object `(V, V, ∅)` of [Stacks, Tag 07I8] for `V = ∅`, which lies in the small site because the
inclusion of an open is an open immersion. -/
noncomputable abbrev botObject : CrystallineThickening S :=
  (opensFree S).obj ⊥

/-- **The ring of sections of `𝒪_{X/S}` over the empty object of `Cris(X/S)` is the zero ring.**
The ambient scheme of `Crystalline.GlobalCrystallineSituation.SmallSite.botObject` is the empty
open subscheme of `X`, whose global sections are the sections of `𝒪_X` over `⊥`. -/
theorem subsingleton_sections_opensFree_bot :
    Subsingleton ((structureSheaf S).obj.obj (op (botObject S))) :=
  (Scheme.Opens.topIso (⊥ : S.X.Opens)).commRingCatIsoToRingEquiv.toEquiv.subsingleton

/-- **If the sections of `𝒪_{X/S}` over an object of `Cris(X/S)` form the zero ring then so do
the sections over its first-order universal thickening of [Stacks, Tag 07J2]**: the first
projection of the thickening restricts sections from the one ring to the other. -/
theorem subsingleton_sections_firstOrderThickening (B : CrystallineThickening S)
    (hB : Subsingleton ((structureSheaf S).obj.obj (op B))) :
    Subsingleton ((structureSheaf S).obj.obj (op (firstOrderThickeningCrysObject S B))) :=
  have := hB
  subsingleton_of_ringHom ((structureSheaf S).obj.map (firstOrderThickeningCrysP₀ S B).op).hom

/-- **The sections of a crystal over an object of `Cris(X/S)` whose section ring is the zero ring
form the zero module**, being a module over that ring. -/
theorem subsingleton_crystalSections {B : CrystallineThickening S}
    (hB : Subsingleton ((structureSheaf S).obj.obj (op B))) (F : QuasiCoherentCrystal S) :
    Subsingleton (F.obj.val.obj (op B)) :=
  have := hB
  subsingleton_moduleCat _

/-- **The ring `lim_e Γ(T_e, 𝒪_{T_e})` of a system of levels whose section rings all vanish is
the zero ring**, being a subring of a product of zero rings. -/
theorem subsingleton_levelRingLimit (T : ℕ ⥤ CrystallineThickening S)
    (h : ∀ e : ℕ, Subsingleton ((structureSheaf S).obj.obj (op (T.obj e)))) :
    Subsingleton (levelRingLimit S T) :=
  have := h
  inferInstance

/-- **The module `lim_e Γ(T_e, ℱ_{T_e})` of a crystal over a system of levels whose modules of
sections all vanish is the zero module**, being a subgroup of a product of zero groups. -/
theorem subsingleton_levelSectionsLimit (T : ℕ ⥤ CrystallineThickening S)
    (F : QuasiCoherentCrystal S)
    (h : ∀ e : ℕ, Subsingleton (F.obj.val.obj (op (T.obj e)))) :
    Subsingleton (levelSectionsLimit S T F) :=
  have := h
  inferInstance

/-! ### The two ring identifications, at an arbitrary object of `Cris(X/S)` -/

section RingIdentifications

attribute [local instance] PresheafOfModules.moduleMulOpposite
attribute [local instance] PresheafOfModules.isCentralScalar_of_commRing

/-- **The divided power ring of sections of an object of `Cris(X/S)`**: the ring
`Γ(T, 𝒪_T)` of global sections of the ambient scheme, with the divided power structure that `T`
carries on its ideal over the whole space.  This is the ring the field
`Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG.ringEquiv` identifies with the
section ring — at an arbitrary object, with no appeal to [Stacks, Tag 07JN]. -/
noncomputable abbrev sectionsDividedPowerRing (B : CrystallineThickening S) :
    DividedPowerRing.{u} :=
  B.obj.thickening.target.dividedPowers.toDividedPowerRing (op ⊤)

/-- **The module of divided power differentials of an object of `Cris(X/S)`, on sections**:
`Γ(T, Ω_{T/S,δ})`, the module `Ω` of [Stacks, Tag 07J2] and of the connection of
[Stacks, Tag 07J6]. -/
noncomputable abbrev sectionsDifferentials (B : CrystallineThickening S) : Type u :=
  crysDiffSections B.obj

/-- The differentials on sections are a module over the divided power ring of sections: the two
rings are the same, but a divided power ring is a bundled object, so the instance is supplied by
name, as in `Crystalline.GlobalCrystallineSituation.crysDifferentialsObjModule`. -/
noncomputable instance instModuleSectionsDifferentials (B : CrystallineThickening S) :
    Module ((sectionsDividedPowerRing S B : Type u)) (sectionsDifferentials S B) :=
  inferInstanceAs (Module (crysSheafRing S B.obj) (crysDiffSections B.obj))

/-- The right action of the divided power ring of sections on the differentials, obtained from the
left action through `Rᵐᵒᵖ ≅ R`; this is the same recipe
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SqZeroExt.lean` uses to give the square-zero
extension of a presheaf of modules its ring structure, which is what makes the identification
below definitional. -/
noncomputable instance instModuleOpSectionsDifferentials (B : CrystallineThickening S) :
    Module ((sectionsDividedPowerRing S B : Type u))ᵐᵒᵖ (sectionsDifferentials S B) :=
  PresheafOfModules.moduleMulOpposite _ _

/-- The two actions of the divided power ring of sections on the differentials agree. -/
instance instIsCentralScalarSectionsDifferentials (B : CrystallineThickening S) :
    IsCentralScalar ((sectionsDividedPowerRing S B : Type u)) (sectionsDifferentials S B) :=
  PresheafOfModules.isCentralScalar_of_commRing _ _

/-- **The section ring of an object of `Cris(X/S)` is the divided power ring `Γ(T, 𝒪_T)`**, at an
arbitrary object and on the nose: the identity, not merely an isomorphism.

This used to be read as the field `ringEquiv` of the reduction datum, available for free.  It is
not that field any more: since the datum was reshaped to run over a system of levels, `ringEquiv`
asks for `D` to be the inverse limit `lim_e Γ(T_e, 𝒪_{T_e})`, which no single object supplies. -/
noncomputable def sectionsDividedPowerRingEquiv (B : CrystallineThickening S) :
    (sectionsDividedPowerRing S B : Type u) ≃+* (structureSheaf S).obj.obj (op B) :=
  RingEquiv.refl _

/-- **The section ring of the first-order universal thickening of an object of `Cris(X/S)` is the
trivial square-zero extension `Γ(T, 𝒪_T) ⊕ Γ(T, Ω_{T/S,δ})`**, at an arbitrary object and on the
nose, by the construction of that thickening of [Stacks, Tag 07J2] as the square-zero extension of
the structure sheaf by the differentials in
`StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickenings.lean`.

Together with `Crystalline.GlobalCrystallineSituation.SmallSite.sectionsDividedPowerRingEquiv`
this used to settle that three of the ten fields of
`Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG` — `site`, `ringEquiv` and
`thickeningRingEquiv` — were available over every object of `Cris(X/S)` and were not what the
datum was missing.  That is withdrawn: the reshaped datum has no field `site` and no field
`thickeningRingEquiv`, its `ringEquiv` identifies `D` with the limit of the section rings of a
system of levels, and its `thickeningRingHom` is a compatible family of reductions, the limit of
the section rings of the first-order thickenings being `D ⊕ Ω̂` with the forms completed.  What
[Stacks, Tag 07JN] supplies is the identification of the limit with the `p`-adically completed
divided power envelope `D` of [Stacks, Tag 07J8], and the reshaped `ringEquiv` does ask for
it. -/
noncomputable def firstOrderSectionsRingEquiv (B : CrystallineThickening S) :
    firstOrderExtension (sectionsDividedPowerRing S B) (sectionsDifferentials S B) ≃+*
      (structureSheaf S).obj.obj (op (firstOrderThickeningCrysObject S B)) :=
  RingEquiv.refl _

end RingIdentifications

/-! ### The witness -/

/-- **The constant system of levels at the empty object of `Cris(X/S)`**, the degenerate
inhabitant of the field
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG.levelSystem`: every level is
the empty open of `X` thickened by itself and every structure map is the identity. -/
noncomputable abbrev botLevelSystem : ℕ ⥤ CrystallineThickening S :=
  (Functor.const ℕ).obj (botObject S)

/-- **Every level of the constant system at the empty object has the zero ring for its ring of
sections**, stated in the indexed shape the clauses of the reduction datum ask for. -/
theorem subsingleton_sections_botLevelSystem (e : ℕ) :
    Subsingleton ((structureSheaf S).obj.obj (op ((botLevelSystem S).obj e))) :=
  subsingleton_sections_opensFree_bot S

/-- **And so does the first-order universal thickening of every level of that system.** -/
theorem subsingleton_sections_firstOrderThickening_botLevelSystem (e : ℕ) :
    Subsingleton ((structureSheaf S).obj.obj
      (op (firstOrderThickeningCrysObject S ((botLevelSystem S).obj e)))) :=
  subsingleton_sections_firstOrderThickening S _ (subsingleton_sections_botLevelSystem S e)

/-- **A datum satisfying the clauses of [Stacks, Tag 07JG] over the constant system of levels at
the empty object of `Cris(X/S)`.**  All are discharged for the degenerate reason: the ring of
sections over `Crystalline.GlobalCrystallineSituation.SmallSite.botObject` is the zero ring, hence
so is the ring of sections over its first-order thickening, hence every module of sections of
every crystal over either object vanishes — and so does every limit over the constant system at
it — as does every module over the zero divided power ring
`Crystalline.trivialDividedPowerRing`.  The reduction functor is therefore the constant functor
at `Crystalline.trivialFirstOrderCrystal` and each clause of the datum is an equation between
elements of a subsingleton.

This is **not** a reduction datum of [Stacks, Tag 07JG]: it inhabits
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG`, the clauses with no
condition on the system of levels the sections are taken over, and
`Crystalline.GlobalCrystallineSituation.SmallSite.not_levelSystem_isLevel_preReduction07JGBot`
below is the proof that its system does not satisfy the field
`...SmallSite.Reduction07JG.levelSystem_isLevel`.  See the "What is and is not proved" section of
the module documentation. -/
noncomputable def preReduction07JGBot (A : Type u) [CommRing A] (p : ℕ) {ι : Type uI}
    (dx : ι → PUnit.{u + 1}) :
    PreReduction07JG S A trivialDividedPowerRing.{u} (trivialBaseHom A) PUnit.{u + 1}
      (trivialDerivation A) p dx :=
  haveI : Subsingleton (levelRingLimit S (botLevelSystem S)) :=
    subsingleton_levelRingLimit S _ (subsingleton_sections_botLevelSystem S)
  { levelSystem := botLevelSystem S
    functor := (Functor.const (QuasiCoherentCrystal S)).obj (trivialFirstOrderCrystal A p dx)
    ringEquiv := ringEquivOfSubsingleton _ _
    thickeningRingHom := fun e ↦
      haveI := subsingleton_sections_firstOrderThickening_botLevelSystem S e
      ringHomOfSubsingleton _ _
    thickeningRingHom_p₀ := fun e _ ↦
      haveI := subsingleton_sections_firstOrderThickening_botLevelSystem S e
      Subsingleton.elim _ _
    sections := fun F ↦
      haveI := subsingleton_levelSectionsLimit S _ F fun e ↦
        subsingleton_crystalSections S (subsingleton_sections_botLevelSystem S e) F
      addEquivOfSubsingleton _ _
    sections_smul := fun F _ _ e ↦
      haveI := subsingleton_crystalSections S (subsingleton_sections_botLevelSystem S e) F
      Subsingleton.elim _ _
    sections_naturality := fun {_ G} _ _ e ↦
      haveI := subsingleton_crystalSections S (subsingleton_sections_botLevelSystem S e) G
      Subsingleton.elim _ _
    baseChange := fun F e ↦
      haveI := subsingleton_crystalSections S
        (subsingleton_sections_firstOrderThickening_botLevelSystem S e) F
      addMonoidHomOfSubsingleton _ _
    baseChange_tmul := fun F e _ _ ↦
      haveI := subsingleton_crystalSections S
        (subsingleton_sections_firstOrderThickening_botLevelSystem S e) F
      Subsingleton.elim _ _
    comparison_eq := fun F e _ ↦
      haveI := subsingleton_crystalSections S
        (subsingleton_sections_firstOrderThickening_botLevelSystem S e) F
      Subsingleton.elim _ _ }

/-- **The clauses of the reduction datum of [Stacks, Tag 07JG] are inhabited**, for every
global crystalline situation, every base ring, every prime and every family of coordinate
differentials.  This is a measurement of the strength of those clauses and nothing else: the
inhabitant is the degenerate one, so they cannot be the hypothesis of a statement of
[Stacks, Tag 07JH] or of [Stacks, Tag 07LG], and `...SmallSite.Reduction07JG` adds the condition
on the system of levels that rules this inhabitant out.  See the module documentation. -/
theorem nonempty_preReduction07JG (A : Type u) [CommRing A] (p : ℕ) {ι : Type uI}
    (dx : ι → PUnit.{u + 1}) :
    Nonempty (PreReduction07JG S A trivialDividedPowerRing.{u} (trivialBaseHom A) PUnit.{u + 1}
      (trivialDerivation A) p dx) :=
  ⟨preReduction07JGBot S A p dx⟩

/-! ### The empty object is not the object [Stacks, Tag 07JN] works over -/

/-- **The empty object of `Cris(X/S)` is not a thickening of the whole of `X`**, as soon as `X`
has a point: the thickened scheme of
`Crystalline.GlobalCrystallineSituation.SmallSite.botObject` is the empty open subscheme of `X`,
so the inverse of an isomorphism from it to `X` would carry the point into an empty scheme.  This
is the failure that the field `...SmallSite.Reduction07JG.levelSystem_isLevel` detects. -/
theorem not_isOverWholeSpace_botObject (x : S.X) : ¬ IsOverWholeSpace S (botObject S) := by
  intro h
  have : IsIso ((botObject S).obj.toX) := h
  simpa using ((inv ((botObject S).obj.toX)) x).2

/-- **The empty object is isomorphic to no finite level of the system of [Stacks, Tag 07JN].**
Every object of `...SmallSite.wholeSpaceSystem` is a thickening of the whole of `X`, by
`...SmallSite.isWholeSpaceSystem_wholeSpaceSystem`, that property is invariant under isomorphism,
and the empty object does not have it. -/
theorem not_isIsomorphic_botObject_level [IsAffine S.X] [IsAffine S.S.scheme]
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (x : S.X) (e : ℕ) :
    ¬ IsIsomorphic (botObject S)
      (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0))).obj e) := fun h ↦
  not_isOverWholeSpace_botObject S x
    (isOverWholeSpace_of_isIsomorphic h (isWholeSpaceSystem_wholeSpaceSystem S hp 0 e))

/-- **The degenerate datum does not satisfy the field
`...SmallSite.Reduction07JG.levelSystem_isLevel`**, so it does not extend to a reduction datum of
[Stacks, Tag 07JG].  This is the whole point of the field: the clauses of
`...SmallSite.PreReduction07JG` hold for the constant system at the empty object and the extra
field does not.  An isomorphism of systems is in particular an isomorphism in degree zero, and
the empty object is isomorphic to no level of the system of [Stacks, Tag 07JN]. -/
theorem not_levelSystem_isLevel_preReduction07JGBot [IsAffine S.X] [IsAffine S.S.scheme]
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (x : S.X) (A : Type u) [CommRing A] (p : ℕ)
    {ι : Type uI} (dx : ι → PUnit.{u + 1}) :
    ¬ IsIsomorphic (preReduction07JGBot S A p dx).levelSystem
      ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0))) := by
  rintro ⟨iso⟩
  exact not_isIsomorphic_botObject_level S hp x 0 ⟨iso.app 0⟩

section Refutation

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}

/-- **No level of a reduction datum of [Stacks, Tag 07JG] is the empty object**, as soon as `X`
has a point.  So a statement quantified over `...SmallSite.Reduction07JG` is not refuted by the
degenerate datum, which is what a statement quantified over the clauses alone was. -/
theorem levelSystem_obj_ne_botObject [IsAffine S.X] [IsAffine S.S.scheme]
    {hp : IsNilpotent (S.p : Γ(S.X, ⊤))} (R : Reduction07JG S A D g Omega d p dx hp) (x : S.X)
    (e : ℕ) : R.levelSystem.obj e ≠ botObject S := fun h ↦
  not_isOverWholeSpace_botObject S x (h ▸ R.isOverWholeSpace_levelSystem e)

end Refutation

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
