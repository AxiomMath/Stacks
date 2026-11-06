module

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullbackIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksCore.Tactic.StacksAttribute

/-!
# Exterior powers and K-groups: the lambda operations

Let `X` be a scheme and let `K₀(Vect(X))` be the Grothendieck ring
`AlgebraicGeometry.VectorBundleKZero` of finite locally free `𝒪_X`-modules, whose addition comes
from short exact sequences, whose multiplication is induced by tensor product and whose unit is
the class of the structure sheaf. For every `r` there is an operation

`λ^r : K₀(Vect(X)) → K₀(Vect(X))`

which sends `[ℰ]` to `[⋀^r ℰ]` for a finite locally free module `ℰ` and which is compatible with
pullback along a morphism of schemes.

Following the source, the operations are read off from the *total exterior-power class*

`c(ℰ) = ∑_{i ≥ 0} [⋀ⁱ ℰ] tⁱ ∈ K₀(Vect(X))⟦t⟧`.

Its constant coefficient is `[⋀⁰ ℰ] = [𝒪_X] = 1`, so `c(ℰ)` is a unit of the power series ring;
the geometric input is that `c` turns a short exact sequence into a product,
`c(ℱ) = c(ℰ) c(𝒢)`, and that is exactly the additivity that the universal property
`AlgebraicGeometry.VectorBundleKZero.liftAddHom` of the Grothendieck group consumes. So `c`
descends to a homomorphism from the additive group `K₀(Vect(X))` to the multiplicative group of
units of `K₀(Vect(X))⟦t⟧`, and `λ^r` is the `r`-th coefficient of the descended `c`.

## Main definitions

* `AlgebraicGeometry.VectorBundleKZero.exteriorClassSeries`: the power series
  `c(ℰ) = ∑ [⋀ⁱ ℰ] tⁱ`, and `exteriorClassUnit` the unit of `K₀(Vect(X))⟦t⟧` it is.
* `AlgebraicGeometry.VectorBundleKZero.ExteriorPowersData`: the geometric input of the source's
  proof, and its only hypothesis — the relation in `K₀(Vect(X))` that the filtration of `⋀ⁿ ℱ`
  along a short exact sequence produces.
* `AlgebraicGeometry.VectorBundleKZero.exteriorClassAddHom`: the descent of `c` to a
  homomorphism `K₀(Vect(X)) →+ Additive (K₀(Vect(X))⟦t⟧)ˣ`.
* `AlgebraicGeometry.VectorBundleKZero.lambdaOperation`: **the operation `λ^r`**, the `r`-th
  coefficient of `exteriorClassAddHom`.
* `AlgebraicGeometry.VectorBundleKZero.pullbackExteriorPowerIso`: `f^*(⋀ⁿ ℰ) ≅ ⋀ⁿ(f^*ℰ)` for a
  morphism of schemes, Tag 01CI in an arbitrary degree.

## Main results

* `Stacks.SheafOfModules.isFiniteLocallyFree_exteriorPower` and
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_exteriorPower`: an exterior power of a
  finite locally free sheaf of modules is finite locally free, with no hypothesis on the rank.
* `AlgebraicGeometry.VectorBundleKZero.classOf_exteriorPower_zero`: `[⋀⁰ ℰ] = 1`, because the
  degree-zero piece of an exterior algebra is the structure sheaf.
* `AlgebraicGeometry.VectorBundleKZero.exteriorClassSeries_shortExact`: `c(ℱ) = c(ℰ) c(𝒢)` along
  a short exact sequence, the source's claim, read off coefficientwise from
  `ExteriorPowersData`.
* `AlgebraicGeometry.VectorBundleKZero.lambdaOperation_classOf`: `λ^r([ℰ]) = [⋀^r ℰ]` for a
  finite locally free module.
* `AlgebraicGeometry.VectorBundleKZero.lambdaOperation_pullback`: the compatibility with
  pullback, in the form it is proved in.
* `AlgebraicGeometry.VectorBundleKZero.exists_lambdaOperations`: **Tag 0FIC**, the three clauses
  of the source asserted together.

## Implementation notes

**`λ^r` is constructed, not chosen.** `lambdaOperation` has a body: it is the composite of the
additive homomorphism `exteriorClassAddHom`, which is `liftAddHom` applied to the explicit
function `ℰ ↦ c(ℰ)`, with the `r`-th coefficient map of the power series ring. It is not
extracted from an existence statement. `exists_lambdaOperations` is a wrapper that states the
source's lemma; it is proved by exhibiting `lambdaOperation`.

**Why a power series and not an induction.** The source's `c` is the only place the mixing of
degrees happens: additivity of a single `λ^r` is false, while multiplicativity of the whole
series is exactly the relation the filtration gives. Carrying `c` as an element of
`K₀(Vect(X))⟦t⟧`, and `λ^r` as its coefficient, is therefore the construction and not a
reformulation of it. The target of the descended `c` is `Additive (K₀(Vect(X))⟦t⟧)ˣ` because
`liftAddHom` maps into an additive group, and the multiplicative group it is the `Additive`
tag of is the unit group of the power series ring. The unit `exteriorClassUnit` is written down
rather than extracted from `IsUnit`: its underlying series is `c(ℰ)` and its inverse is
`PowerSeries.invOfUnit c(ℰ) 1`, which is legitimate because the constant coefficient is
`[⋀⁰ ℰ] = 1` (`classOf_exteriorPower_zero`, proved here from
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPieceIso_zero`). So no part of the
construction passes through a choice.

**The one hypothesis, and exactly what is missing.** The source's claim `c(ℱ) = c(ℰ) c(𝒢)` is
proved by viewing the short exact sequence as a two-step filtration of `ℱ`, which induces a
filtration of `⋀ⁿ ℱ` with `n + 1` steps and graded pieces `⋀ⁱ ℰ ⊗ ⋀^{n - i} 𝒢`. Neither that
filtration nor its graded identification is constructed anywhere in the library, and it is the
*sole* obstruction to proving Tag 0FIC outright: everything else the source's proof uses is
proved here. What constructing it needs is

1. the subobjects `Fᵖ(⋀ⁿ ℱ) = im(⋀ᵖ ℰ ⊗ ⋀^{n - p} ℱ ⟶ ⋀ⁿ ℱ)`, formed from
   `SheafOfModules.prodWedgeHom` in the abelian category of sheaves of modules;
2. finite local freeness of each `Fᵖ`, which follows from 3 by descending induction together
   with the fact that an extension of finite locally free modules is finite locally free;
3. the graded identification `Fᵖ / Fᵖ⁺¹ ≅ ⋀ᵖ ℰ ⊗ ⋀^{n - p} 𝒢`, whose surjectivity is Tag 01CJ
   (`SheafOfModules.ExtPresentation.exteriorPresentation_exact`, which identifies
   `⋀^k 𝒢` as `⋀^k ℱ` modulo the image of `ℰ ⊗ ⋀^{k - 1} ℱ`) and whose injectivity has to be
   checked on stalks, where the sequence splits;
4. hence, at the module level, the filtration of `⋀ⁿ(M' ⊕ M'')` by the
   `⨁_{j ≥ p} ⋀ʲ M' ⊗ ⋀^{n - j} M''`, which is in neither Mathlib's
   `Mathlib/LinearAlgebra/ExteriorPower/` nor this library.

Tag 01CJ supplies only step `p = 1`, and the only decomposition of an exterior power available
is the *split* one, `SheafOfModules.exteriorPowerBiprodIso`; a short exact sequence of finite
locally free modules on a scheme is only locally split, so the split decomposition does not give
the global relation. (This is why `liftAddHom` cannot be fed the split case alone: it demands
additivity on *every* short exact sequence of finite locally free modules. In fact the relation
is not merely used by the source's proof but implied by its statement: any well-defined function
on `K₀(Vect(X))` sending `[ℰ]` to `[⋀^r ℰ]` must respect `[ℱ] = [ℰ] + [𝒢]`.) The relation is
therefore the single field of `ExteriorPowersData`, named in the Stacks attribute. It is recorded
as the equality of classes in `K₀(Vect(X))` that the defining relation of the Grothendieck group
turns the filtration into, rather than as a tower of short exact sequences of sheaves, because
that equality is all that is consumed and is therefore the weaker hypothesis. The same device,
under the name `AlgebraicGeometry.VectorBundleKZero.SquarePowersData`, carries the degree-two
case of the same filtration for the second Adams operator of Tag 0FEJ, so the two can be
discharged together.

**Finite local freeness of `⋀ⁿ ℰ` is proved, not assumed.** The library had it only for a module
of *constant* rank (`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower`: `⋀ⁿ` of a
module of rank `r` has rank `binom(r, n)`), whereas the predicate
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` that `K₀(Vect(X))` is built over asks only for a
trivializing covering with finite — not equicardinal — index types. The rankless form is
`Stacks.SheafOfModules.isFiniteLocallyFree_exteriorPower` here: a trivializing covering with
index types `γ i` is one for `⋀ⁿ ℰ` with index types the `n`-element subsets of `γ i`, again
finite, and the cardinalities are never compared across the covering. The local trivialization it
runs on is the one the rank statement runs on,
`Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree`.

**The pullback.** The comparison `f^*(⋀ⁿ ℰ) ≅ ⋀ⁿ(f^*ℰ)` is not assumed: it is
`pullbackExteriorPowerIso`, the degree-`n` component of
`Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso` (Tag 01CI) applied to the universal
properties carried by the chosen packages `SheafOfModules.algebras`. What
`lambdaOperation_pullback` does take as hypotheses are the pullback homomorphism of Grothendieck
rings itself — a ring map sending `[ℰ]` to `[f^*ℰ]` on finite locally free modules — and the
stability of finite local freeness under pullback. The functoriality of `K₀(Vect(-))` is not
constructed anywhere in the library, and the source does not prove it either: Derived Categories
of Schemes, Section 36.38 defines `K₀(Vect(X))` by its universal property with the words "We
omit the detailed construction". The compatibility proved here is therefore the assertion that
`λ^r` commutes with any ring homomorphism realising pullback, which is the content of the
source's clause once that functoriality is available.

**Which `⋀ⁿ`.** `AlgebraicGeometry.Scheme.Modules.exteriorPower ℰ n` is the degree-`n` piece of
the exterior algebra of the chosen package `SheafOfModules.algebras`, the same spelling the
library's statements about ranks, finiteness and invertibility of exterior powers are written
against. Its degree argument is an integer; the series is indexed by `ℕ` and casts.

## References

* [Stacks Project, Tag 0FIC](https://stacks.math.columbia.edu/tag/0FIC)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0FDE](https://stacks.math.columbia.edu/tag/0FDE)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.FiniteLocallyFree

universe v u₁ u

/-! ### Finite local freeness of an exterior power, with no hypothesis on the rank -/

namespace Stacks.SheafOfModules

section Rankless

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}

/-- **The degree-`n` exterior power of a finite locally free sheaf of modules is finite locally
free.**

A trivializing covering for `F` with finite index types `γ i` is a trivializing covering for
`⋀ⁿ F` with index types the `n`-element subsets of `γ i`, which are again finite. No rank is
mentioned: the `γ i` are used as they come, so they are allowed to have different cardinalities
over different members of the covering, which is what the predicate
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` permits and what
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower` does not cover. -/
@[ega "0 5.5.4" "partial", sga "6 X 6.1" "special case"]
theorem isFiniteLocallyFree_exteriorPower
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (n : ℕ)
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, v, u₁} F) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, v, u₁} (A.exteriorPower n) := by
  classical
  have _hP : ∀ (U : C) (K : Type u), HasColimitsOfShape (Discrete K)
      (PresheafOfModules.{u} ((Sheaf.toRingCat J Osharp).over U).obj) :=
    fun _ _ => PresheafOfModules.hasColimitsOfShape _ _
  obtain ⟨q, hq, hft⟩ := hF.exists_isFiniteLocallyFreeData
  let _lo : ∀ i : q.I, LinearOrder ((q.generators i).I) :=
    fun _ => IsWellOrder.linearOrder WellOrderingRel
  have E : ∀ i : q.I, _root_.SheafOfModules.free
      (R := (Sheaf.toRingCat J Osharp).over (q.X i)) ↥(Set.powersetCard ((q.generators i).I) n) ≅
      (A.exteriorPower n).over (q.X i) := fun i =>
    (exteriorPowerOverFreeIsoOfIsoFree A (q.X i) n ((q.generators i).I)
      (asIso (q.generators i).π).symm).symm
  refine ⟨⟨q.I, q.X, q.coversTop, fun i =>
      ⟨↥(Set.powersetCard ((q.generators i).I) n),
        ((A.exteriorPower n).over (q.X i)).freeHomEquiv (E i).hom,
        by rw [Equiv.symm_apply_apply]; exact IsIso.epi_of_iso _⟩⟩,
    ⟨fun i => by
      dsimp only [_root_.SheafOfModules.GeneratingSections.π]
      rw [Equiv.symm_apply_apply]
      infer_instance⟩,
    ⟨fun i => ?_⟩⟩
  have : Finite ((q.generators i).I) := (hft.isFiniteType i).finite
  exact ⟨inferInstance⟩

end Rankless

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- **The degree-`n` exterior power of a finite locally free sheaf of modules on a scheme is
finite locally free**, at the spelling of finite local freeness that `K₀(Vect(X))` is built
over. -/
theorem isFiniteLocallyFree_exteriorPower {X : Scheme.{u}} (F : X.Modules) (n : ℕ)
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Modules.exteriorPower F (n : ℤ)) :=
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := Sheaf.toRingCat (_root_.Opens.grothendieckTopology X) X.sheaf) F := hF
  Stacks.SheafOfModules.isFiniteLocallyFree_exteriorPower
    (J := _root_.Opens.grothendieckTopology X) (Osharp := X.sheaf)
    (_root_.SheafOfModules.algebras _ F) n this

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.VectorBundleKZero

variable (X : Scheme.{u})

/-! ### The zeroth exterior power -/

/-- The zeroth exterior power of a sheaf of modules on a scheme is the structure sheaf: it is
the degree-zero piece of the exterior algebra of the chosen package, which that package
identifies with the zeroth tensor power, and the zeroth tensor power is the unit. -/
noncomputable def exteriorPowerZeroIsoUnit (E : X.Modules) :
    Scheme.Modules.exteriorPower E 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.algebras _ E).exteriorPieceIso_zero

/-- The zeroth exterior power of a sheaf of modules on a scheme is finite locally free, being
isomorphic to the structure sheaf. -/
theorem isFiniteLocallyFree_exteriorPower_zero (E : X.Modules) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Modules.exteriorPower E 0) :=
  @IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _
    (exteriorPowerZeroIsoUnit X E).symm (isFiniteLocallyFree_unit X)

/-- `[⋀⁰ ℰ] = 1` in `K₀(Vect(X))`: the zeroth exterior power is the structure sheaf, whose
class is the unit of the ring. -/
@[simp] theorem classOf_exteriorPower_zero (E : X.Modules) :
    classOf X (Scheme.Modules.exteriorPower E 0) = 1 :=
  (classOf_eq_of_iso (exteriorPowerZeroIsoUnit X E)
    (isFiniteLocallyFree_exteriorPower_zero X E)).trans (classOf_unit X)

/-! ### The total exterior-power class -/

/-- **The total exterior-power class** `c(ℰ) = ∑_{i ≥ 0} [⋀ⁱ ℰ] tⁱ` of a sheaf of modules on a
scheme, an element of the power series ring `K₀(Vect(X))⟦t⟧`. -/
@[sga "6 VI 4.5"]
noncomputable def exteriorClassSeries (E : X.Modules) :
    PowerSeries (VectorBundleKZero X) :=
  PowerSeries.mk fun i => classOf X (Scheme.Modules.exteriorPower E (i : ℤ))

@[simp] theorem coeff_exteriorClassSeries (E : X.Modules) (i : ℕ) :
    PowerSeries.coeff i (exteriorClassSeries X E) =
      classOf X (Scheme.Modules.exteriorPower E (i : ℤ)) :=
  PowerSeries.coeff_mk i _

/-- The constant coefficient of the total exterior-power class is `1`. -/
@[simp] theorem constantCoeff_exteriorClassSeries (E : X.Modules) :
    PowerSeries.constantCoeff (exteriorClassSeries X E) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_exteriorClassSeries]
  exact_mod_cast classOf_exteriorPower_zero X E

/-- **The total exterior-power class as a unit of `K₀(Vect(X))⟦t⟧`.** Its inverse is written
down: a power series whose constant coefficient is a unit is inverted by
`PowerSeries.invOfUnit`, and the constant coefficient here is `[⋀⁰ ℰ] = 1`. -/
noncomputable def exteriorClassUnit (E : X.Modules) :
    (PowerSeries (VectorBundleKZero X))ˣ where
  val := exteriorClassSeries X E
  inv := PowerSeries.invOfUnit (exteriorClassSeries X E) 1
  val_inv := PowerSeries.mul_invOfUnit _ 1
    (by rw [constantCoeff_exteriorClassSeries, Units.val_one])
  inv_val := PowerSeries.invOfUnit_mul _ 1
    (by rw [constantCoeff_exteriorClassSeries, Units.val_one])

@[simp] theorem exteriorClassUnit_val (E : X.Modules) :
    (exteriorClassUnit X E : PowerSeries (VectorBundleKZero X)) = exteriorClassSeries X E :=
  rfl

/-- The total exterior-power class is a unit of `K₀(Vect(X))⟦t⟧`. -/
theorem isUnit_exteriorClassSeries (E : X.Modules) : IsUnit (exteriorClassSeries X E) :=
  ⟨exteriorClassUnit X E, rfl⟩

/-! ### The geometric input of the source's proof -/

/-- **The geometric input of Tag 0FIC**, and the only thing in the source's proof that the
library does not supply: along a short exact sequence `0 → ℰ → ℱ → 𝒢 → 0` of finite locally
free modules, `⋀ⁿ ℱ` carries a filtration with `n + 1` steps whose graded pieces are the
`⋀ⁱ ℰ ⊗ ⋀^{n - i} 𝒢`.

It is recorded as the equality of classes in `K₀(Vect(X))` that the defining relation of the
Grothendieck group turns the filtration into, which is what the Grothendieck group consumes;
the product of two classes is the class of the tensor product
(`AlgebraicGeometry.VectorBundleKZero.classOf_mul`). -/
structure ExteriorPowersData (X : Scheme.{u}) : Prop where
  /-- The filtration of `⋀ⁿ` along a short exact sequence of finite locally free modules:
  `[⋀ⁿ ℱ] = ∑_{i = 0}^{n} [⋀ⁱ ℰ] [⋀^{n - i} 𝒢]`. -/
  classOf_exteriorPower_shortExact : ∀ {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0), IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G →
          Mono f → Epi g → (ShortComplex.mk f g w).Exact → ∀ n : ℕ,
            classOf X (Scheme.Modules.exteriorPower F (n : ℤ)) =
              ∑ i ∈ Finset.range (n + 1),
                classOf X (Scheme.Modules.exteriorPower E (i : ℤ)) *
                  classOf X (Scheme.Modules.exteriorPower G ((n - i : ℕ) : ℤ))

variable {X}

/-- **The source's claim.** Along a short exact sequence `0 → ℰ → ℱ → 𝒢 → 0` of finite locally
free modules the total exterior-power class is multiplicative, `c(ℱ) = c(ℰ) c(𝒢)`. Coefficient
by coefficient this is the relation produced by the filtration of `⋀ⁿ ℱ`. -/
theorem exteriorClassSeries_shortExact (h : ExteriorPowersData X) {E F G : X.Modules}
    (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    exteriorClassSeries X F = exteriorClassSeries X E * exteriorClassSeries X G := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_exteriorClassSeries, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    h.classOf_exteriorPower_shortExact f g w hE hF hG hmono hepi hex n]
  exact Finset.sum_congr rfl fun i _ => by
    rw [coeff_exteriorClassSeries, coeff_exteriorClassSeries]

/-- The total exterior-power class is multiplicative on short exact sequences, as an identity of
units of `K₀(Vect(X))⟦t⟧`. -/
theorem exteriorClassUnit_shortExact (h : ExteriorPowersData X) {E F G : X.Modules}
    (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    exteriorClassUnit X F = exteriorClassUnit X E * exteriorClassUnit X G :=
  Units.ext <| by
    rw [Units.val_mul, exteriorClassUnit_val, exteriorClassUnit_val, exteriorClassUnit_val,
      exteriorClassSeries_shortExact h f g w hE hF hG hmono hepi hex]

/-! ### The descent to the Grothendieck group -/

open scoped Classical in
/-- The total exterior-power class of a finite locally free module, viewed in the additive group
`Additive (K₀(Vect(X))⟦t⟧)ˣ`, and zero on the sheaves of modules that are not finite locally
free. This is the function on sheaves of modules of which `c` is the descent. -/
noncomputable def exteriorClassElt (X : Scheme.{u}) (E : X.Modules) :
    Additive (PowerSeries (VectorBundleKZero X))ˣ :=
  if IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E then
    Additive.ofMul (exteriorClassUnit X E) else 0

/-- On a finite locally free module, `exteriorClassElt` is the total exterior-power class. -/
theorem exteriorClassElt_of_isFiniteLocallyFree (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    exteriorClassElt X E = Additive.ofMul (exteriorClassUnit X E) :=
  by simp [exteriorClassElt, hE]

/-- `exteriorClassElt` vanishes off the finite locally free modules. -/
theorem exteriorClassElt_eq_zero (E : X.Modules)
    (hE : ¬ IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    exteriorClassElt X E = 0 :=
  by simp [exteriorClassElt, hE]

/-- `exteriorClassElt` is additive along a short exact sequence of finite locally free modules,
because the total exterior-power class is multiplicative along one. -/
theorem exteriorClassElt_shortExact (h : ExteriorPowersData X) {E F G : X.Modules}
    (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    exteriorClassElt X F = exteriorClassElt X E + exteriorClassElt X G := by
  rw [exteriorClassElt_of_isFiniteLocallyFree E hE,
    exteriorClassElt_of_isFiniteLocallyFree F hF,
    exteriorClassElt_of_isFiniteLocallyFree G hG,
    exteriorClassUnit_shortExact h f g w hE hF hG hmono hepi hex]
  exact ofMul_mul _ _

/-- **The total exterior-power class as a homomorphism out of `K₀(Vect(X))`.** It turns addition
in the Grothendieck group into multiplication of power series, which is the source's `c`. -/
noncomputable def exteriorClassAddHom (h : ExteriorPowersData X) :
    VectorBundleKZero X →+ Additive (PowerSeries (VectorBundleKZero X))ˣ :=
  liftAddHom (exteriorClassElt X) exteriorClassElt_eq_zero (exteriorClassElt_shortExact h)

/-- The value of `c` on the class of a finite locally free module is its total exterior-power
class. -/
theorem exteriorClassAddHom_classOf (h : ExteriorPowersData X) (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    exteriorClassAddHom h (classOf X E) = Additive.ofMul (exteriorClassUnit X E) :=
  (liftAddHom_classOf (exteriorClassElt X) exteriorClassElt_eq_zero
    (exteriorClassElt_shortExact h) E).trans
      (exteriorClassElt_of_isFiniteLocallyFree E hE)

/-! ### The lambda operations -/

/-- **The operation `λ^r` on `K₀(Vect(X))`.** It is the `r`-th coefficient of the total
exterior-power class `c`, which is `exteriorClassAddHom`. -/
@[sga "6 X 1.2"]
noncomputable def lambdaOperation (h : ExteriorPowersData X) (r : ℕ) :
    VectorBundleKZero X → VectorBundleKZero X := fun a =>
  PowerSeries.coeff r
    ((Additive.toMul (exteriorClassAddHom h a) : (PowerSeries (VectorBundleKZero X))ˣ) :
      PowerSeries (VectorBundleKZero X))

/-- **`λ^r` sends `[ℰ]` to `[⋀^r ℰ]`** for a finite locally free module `ℰ`. -/
theorem lambdaOperation_classOf (h : ExteriorPowersData X) (r : ℕ) (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    lambdaOperation h r (classOf X E) =
      classOf X (Scheme.Modules.exteriorPower E (r : ℤ)) := by
  rw [lambdaOperation, exteriorClassAddHom_classOf h E hE]
  show PowerSeries.coeff r (exteriorClassUnit X E : PowerSeries (VectorBundleKZero X)) = _
  rw [exteriorClassUnit_val, coeff_exteriorClassSeries]

/-- `λ⁰` is the constant map `1`: the zeroth exterior power of any finite locally free module
is the structure sheaf. -/
theorem lambdaOperation_zero_classOf (h : ExteriorPowersData X) (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    lambdaOperation h 0 (classOf X E) = 1 := by
  rw [lambdaOperation_classOf h 0 E hE]
  exact_mod_cast classOf_exteriorPower_zero X E

/-! ### Compatibility with pullback -/

section Pullback

variable {Y : Scheme.{u}}

/-- **Tag 01CI in degree `n`.** `f^*(⋀ⁿ ℰ) ≅ ⋀ⁿ(f^*ℰ)` for a morphism of schemes `f : X ⟶ Y`,
the degree-`n` component of `Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso` applied
to the universal properties carried by the chosen packages. -/
noncomputable def pullbackExteriorPowerIso (f : X ⟶ Y) (E : Y.Modules) (n : ℤ) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.exteriorPower E n) ≅
      Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj E) n :=
  (Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso f.toLRSHom.toShHom
    (SheafOfModules.algebras (Opens.grothendieckTopology (Y : TopCat)) E).exterior
    (SheafOfModules.algebras (Opens.grothendieckTopology (Y : TopCat)) E).exteriorGenerator
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat))
      ((Scheme.Modules.pullback f).obj E)).exterior
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat))
      ((Scheme.Modules.pullback f).obj E)).exteriorGenerator
    (SheafOfModules.algebras (Opens.grothendieckTopology (Y : TopCat))
      E).exterior_isExteriorAlgebra
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat))
      ((Scheme.Modules.pullback f).obj E)).exterior_isExteriorAlgebra).app n

/-- The group homomorphism on units of power series rings induced by a ring homomorphism of
Grothendieck rings, written additively, so that it can be compared with the descents of the two
total exterior-power classes. -/
noncomputable def mapClassAddHom (p : VectorBundleKZero Y →+* VectorBundleKZero X) :
    Additive (PowerSeries (VectorBundleKZero Y))ˣ →+
      Additive (PowerSeries (VectorBundleKZero X))ˣ :=
  MonoidHom.toAdditive (Units.map (PowerSeries.map p).toMonoidHom)

/-- **`λ^r` is compatible with pullback.** Let `f : X ⟶ Y` be a morphism of schemes and let `p`
be a ring homomorphism `K₀(Vect(Y)) → K₀(Vect(X))` sending the class of a finite locally free
module `ℰ` to the class of `f^*ℰ`. Granted that pullback preserves finite local freeness, every
`λ^r` commutes with `p`. The comparison `f^*(⋀ⁿ ℰ) ≅ ⋀ⁿ(f^*ℰ)` of Tag 01CI is not assumed: it is
`pullbackExteriorPowerIso`. -/
@[sga "6 0 2.9" "partial", sga "6 V 2.2.1" "special case", sga "6 X 7.7" "partial"]
theorem lambdaOperation_pullback (f : X ⟶ Y)
    (hX : ExteriorPowersData X) (hY : ExteriorPowersData Y)
    (p : VectorBundleKZero Y →+* VectorBundleKZero X)
    (hp : ∀ E : Y.Modules, IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
      p (classOf Y E) = classOf X ((Scheme.Modules.pullback f).obj E))
    (hflf : ∀ E : Y.Modules, IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        ((Scheme.Modules.pullback f).obj E))
    (r : ℕ) (a : VectorBundleKZero Y) :
    lambdaOperation hX r (p a) = p (lambdaOperation hY r a) := by
  have hcomp : (exteriorClassAddHom hX).comp
        (p : VectorBundleKZero Y →+ VectorBundleKZero X) =
      (mapClassAddHom p).comp (exteriorClassAddHom hY) := by
    refine addHom_ext fun E hE => ?_
    have hpE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        ((Scheme.Modules.pullback f).obj E) := hflf E hE
    have hseries : exteriorClassSeries X ((Scheme.Modules.pullback f).obj E) =
        PowerSeries.map p (exteriorClassSeries Y E) := by
      refine PowerSeries.ext fun i => ?_
      have hi := Scheme.Modules.isFiniteLocallyFree_exteriorPower E i hE
      rw [coeff_exteriorClassSeries, PowerSeries.coeff_map, coeff_exteriorClassSeries, hp _ hi]
      exact (classOf_eq_of_iso (pullbackExteriorPowerIso f E (i : ℤ)) (hflf _ hi)).symm
    have hunit : exteriorClassUnit X ((Scheme.Modules.pullback f).obj E) =
        Units.map (PowerSeries.map p).toMonoidHom (exteriorClassUnit Y E) := by
      refine Units.ext ?_
      rw [exteriorClassUnit_val, hseries]
      rfl
    show exteriorClassAddHom hX (p (classOf Y E)) =
      mapClassAddHom p (exteriorClassAddHom hY (classOf Y E))
    rw [hp E hE, exteriorClassAddHom_classOf hX _ hpE,
      exteriorClassAddHom_classOf hY E hE, hunit]
    rfl
  have happ : exteriorClassAddHom hX (p a) =
      mapClassAddHom p (exteriorClassAddHom hY a) :=
    congrArg
      (fun φ : VectorBundleKZero Y →+ Additive (PowerSeries (VectorBundleKZero X))ˣ => φ a) hcomp
  have key : ((Additive.toMul (exteriorClassAddHom hX (p a)) :
        (PowerSeries (VectorBundleKZero X))ˣ) : PowerSeries (VectorBundleKZero X)) =
      PowerSeries.map p
        ((Additive.toMul (exteriorClassAddHom hY a) :
          (PowerSeries (VectorBundleKZero Y))ˣ) : PowerSeries (VectorBundleKZero Y)) := by
    rw [happ]; rfl
  simp only [lambdaOperation, key, PowerSeries.coeff_map]

end Pullback

/-! ### The theorem -/

/-- **Stacks Project, Tag 0FIC.** Let `X` be a scheme. There are maps
`λ^r : K₀(Vect(X)) → K₀(Vect(X))` which send `[ℰ]` to `[⋀^r ℰ]` when `ℰ` is a finite locally
free `𝒪_X`-module and which are compatible with pullbacks.

All three clauses of the source are present: the operations are produced as a family of maps,
the second conjunct is their value on the class of a finite locally free module, and the third
is their commutation with any ring map of Grothendieck rings realising pullback of finite
locally free modules.

The sole hypothesis `ExteriorPowersData X` is the geometric input of the source's proof: the
filtration of `⋀ⁿ` along a short exact sequence, which the library does not construct. Finite
local freeness of `⋀ⁿ ℰ` and the comparison `f^*(⋀^r ℰ) ≅ ⋀^r(f^*ℰ)` of Tag 01CI are not
assumed; both are proved. -/
@[stacks 0FIC "all three clauses, granted one hypothesis: the filtration of `⋀ⁿ` along a short \
  exact sequence of finite locally free modules, which the library does not construct. The \
  pullback homomorphism of `K₀(Vect(-))`, whose construction the source omits, is also a \
  hypothesis", sga "6 0 2.9" "partial", sga "6 V 2.2.1" "Second conjunct only"]
theorem exists_lambdaOperations (X : Scheme.{u}) (h : ExteriorPowersData X) :
    ∃ lam : ℕ → VectorBundleKZero X → VectorBundleKZero X,
      (∀ (r : ℕ) (E : X.Modules), IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
          lam r (classOf X E) = classOf X (Scheme.Modules.exteriorPower E (r : ℤ))) ∧
        (∀ (Y : Scheme.{u}) (f : Y ⟶ X) (hY : ExteriorPowersData Y)
            (p : VectorBundleKZero X →+* VectorBundleKZero Y),
          (∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
              p (classOf X E) = classOf Y ((Scheme.Modules.pullback f).obj E)) →
            (∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
              IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
                ((Scheme.Modules.pullback f).obj E)) →
              ∀ (r : ℕ) (a : VectorBundleKZero X),
                lambdaOperation hY r (p a) = p (lambdaOperation h r a)) :=
  ⟨lambdaOperation h,
    fun r E hE => lambdaOperation_classOf h r E hE,
    fun _Y f hY p hp hflf r a => lambdaOperation_pullback f hY h p hp hflf r a⟩

end AlgebraicGeometry.VectorBundleKZero

end
