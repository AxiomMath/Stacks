module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.WittVector.IsPoly

/-!
# Flat base change for the naive cotangent complex

Let `α : P → S` be a presentation of an `R`-algebra `S`, let `R → R'` be a flat ring map,
and let `α' : P ⊗_R R' → S' = S ⊗_R R'` be the induced presentation.  Then the two
termwise base changes `NL(α) ⊗_R R'` and `NL(α) ⊗_S S'` of the naive cotangent complex
agree with `NL(α')`, and the canonical map `NL_{S/R} ⊗_S S' → NL_{S'/R'}` is a homotopy
equivalence.  (Stacks Lemma 10.134.8, tag `00S4`.)

All rings are commutative with unit; all ring maps are unital ring homomorphisms.
Tensor products are over the indicated base ring.

## Main definitions

* (Definition 1) A *presentation* of `S` over `R` is a surjective `R`-algebra
  homomorphism `alpha : P -> S` with `P` a *polynomial* `R`-algebra (on an arbitrary
  index set of variables); `I = ker alpha`.

  In Mathlib a polynomial presentation is `Algebra.Generators R S ι`: its underlying
  presentation ring `(Algebra.Generators R S ι).Ring` is the polynomial algebra
  `MvPolynomial ι R`, with a surjection onto `S` and a section.  More generally,
  `Algebra.Extension R S` packages any commutative ring `P := P.Ring`, an `R`-algebra
  structure on `P`, a surjective `R`-algebra map `P -> S` (with `P.ker` its kernel),
  and a section.  Statements 1 and 2 below are stated for an arbitrary
  `Algebra.Extension` (a faithful generalization of the polynomial case: for an
  extension `P`, `P.baseChange (T := R')` is `P' = R' ⊗_R P`, matching `P ⊗_R R'`);
  Statement 3, which refers to the *canonical* naive cotangent complexes `NL_{S/R}`
  and `NL_{S'/R'}`, is stated for the canonical polynomial presentations
  `Algebra.Generators.self _ _`.

* (Definition 2) The *naive cotangent complex* `NL(alpha)` is the two-term complex of
  `S`-modules `I/I² → Ω_{P/R} ⊗_P S`, with `I/I²` in degree `1` and `Ω_{P/R} ⊗_P S`
  in degree `0`, the differential sending `[f]` to `df ⊗ 1`.

  In Mathlib: degree `1` is `P.Cotangent` (`≅ I/I²`), degree `0` is `P.CotangentSpace`
  (`≅ S ⊗_P Ω_{P/R}`), and the differential is
  `P.cotangentComplex : P.Cotangent →ₗ[S] P.CotangentSpace`.  A two-term chain complex
  of `T`-modules concentrated in degrees `1, 0` is recorded by its differential
  `d : C₁ →ₗ[T] C₀`; isomorphisms and homotopy equivalences of such are defined below
  (`TwoComplexEquiv`, `HtpyEquiv`).

* (Definitions 3, 4) For a ring map `R → R'`, set `S' = R' ⊗_R S` and `P' = R' ⊗_R P`.
  Applying `R' ⊗_R -` to `alpha` yields the *base-changed presentation* `alpha' : P' → S'`.
  In Mathlib this is `P.baseChange (T := R') : Algebra.Extension R' (R' ⊗_R S)`, whose
  ring is `R' ⊗_R P.Ring` and whose kernel is `(P.baseChange).ker`.

  Two termwise base changes of `NL(α)` are relevant: `NL(α) ⊗_R R'` (terms
  `R' ⊗_R M`, an `R'`-complex) and `NL(α) ⊗_S S'` (terms `S' ⊗_S M`, an `S'`-complex).
  Because `S' = R' ⊗_R S`, for every `S`-module `M` there is a *canonical* `R'`-linear
  isomorphism `R' ⊗_R M ≅ S' ⊗_S M` (the named comparison
  `IsPushout.cancelBaseChange`), identifying the two flavours of termwise base change.
  Note that `R' ⊗_R M` has only a canonical `R'`-module structure; its `S'`-module
  structure is the one *transported* across this very identification, so the canonical
  comparison of the two flavours is naturally formalized as an `R'`-linear isomorphism
  of complexes (`statement2_flavor_iso`).

## On "=" versus "≅"

The Stacks Project writes equalities; these are canonical isomorphisms, formalized
below as explicit, *named* Mathlib comparison maps packaged as `LinearEquiv`s of
two-term complexes (`TwoComplexEquiv`), or homotopy equivalences (`HtpyEquiv`), not
literal definitional equalities.
-/

@[expose] public section
-- needed file-wide: `statement1_kerEquiv`, `cotComparison1_bijective`, `bridge_surj_comm` and
-- `bridgeGH_id` all elaborate through `Algebra.Extension.ker`/`Cotangent.map`/`liftBaseChange`
-- and the `R' ⊗[R] P.Ring` base-change coercions; their rewrites and instance searches only
-- succeed when defeq unfolds that bundling, so a per-declaration form would cover most of the
-- file anyway.
set_option backward.isDefEq.respectTransparency false

open Algebra TensorProduct

namespace FlatBaseChangeNL

/-! ## Two-term chain complexes: isomorphisms and homotopy equivalences.

A two-term chain complex of `T`-modules concentrated in homological degrees `1`
(source) and `0` (target) is recorded by its differential `d : C₁ →ₗ[T] C₀`.  The
naive cotangent complex `NL(α)` is, in these terms, `P.cotangentComplex`. -/

/-- A *chain map* between two-term complexes with differentials `dC : C1 →ₗ C0` and
`dD : D1 →ₗ D0`: a pair `(f1, f0)` (degrees `1` and `0`) with `dD ∘ f1 = f0 ∘ dC`. -/
structure ChainMap {T : Type*} [CommRing T]
    {C1 C0 D1 D0 : Type*}
    [AddCommGroup C1] [Module T C1] [AddCommGroup C0] [Module T C0]
    [AddCommGroup D1] [Module T D1] [AddCommGroup D0] [Module T D0]
    (dC : C1 →ₗ[T] C0) (dD : D1 →ₗ[T] D0) where
  /-- Degree-`1` component. -/
  f1 : C1 →ₗ[T] D1
  /-- Degree-`0` component. -/
  f0 : C0 →ₗ[T] D0
  /-- Chain-map (commuting square) condition `dD ∘ f1 = f0 ∘ dC`. -/
  comm : dD ∘ₗ f1 = f0 ∘ₗ dC

/-- A `T`-linear *isomorphism of two-term complexes* (differentials `dC : C1 →ₗ C0`
and `dD : D1 →ₗ D0`): a pair of `T`-linear equivalences `e1` (degree `1`) and `e0`
(degree `0`) commuting with the differentials, `dD ∘ e1 = e0 ∘ dC`.  This is a genuine
isomorphism of complexes (compatible with the differentials), not merely a chain map
with bijective components. -/
structure TwoComplexEquiv {T : Type*} [CommRing T]
    {C1 C0 D1 D0 : Type*}
    [AddCommGroup C1] [Module T C1] [AddCommGroup C0] [Module T C0]
    [AddCommGroup D1] [Module T D1] [AddCommGroup D0] [Module T D0]
    (dC : C1 →ₗ[T] C0) (dD : D1 →ₗ[T] D0) where
  /-- Degree-`1` component, a `T`-linear equivalence. -/
  e1 : C1 ≃ₗ[T] D1
  /-- Degree-`0` component, a `T`-linear equivalence. -/
  e0 : C0 ≃ₗ[T] D0
  /-- Compatibility with the differentials: `dD ∘ e1 = e0 ∘ dC`. -/
  comm : dD ∘ₗ (e1 : C1 →ₗ[T] D1) = (e0 : C0 →ₗ[T] D0) ∘ₗ dC

/-- A *homotopy equivalence* of two-term complexes (differentials `dC`, `dD`): a chain
map `f`, a chain map `g` back, and chain homotopies witnessing `g ∘ f ≃ id` and
`f ∘ g ≃ id`.  For complexes in degrees `0,1`, a degree-`+1` homotopy is a single map
`(degree 0) → (degree 1)`, and the relation `id - g∘f = d∘h + h∘d` unfolds to the two
equations recorded in each degree. -/
structure HtpyEquiv {T : Type*} [CommRing T]
    {C1 C0 D1 D0 : Type*}
    [AddCommGroup C1] [Module T C1] [AddCommGroup C0] [Module T C0]
    [AddCommGroup D1] [Module T D1] [AddCommGroup D0] [Module T D0]
    (dC : C1 →ₗ[T] C0) (dD : D1 →ₗ[T] D0) where
  /-- Forward chain map. -/
  toFun : ChainMap dC dD
  /-- Backward chain map. -/
  invFun : ChainMap dD dC
  /-- Degree-`0`-to-`1` homotopy witnessing `g ∘ f ≃ id_C`. -/
  hC : C0 →ₗ[T] C1
  /-- Degree-`0`-to-`1` homotopy witnessing `f ∘ g ≃ id_D`. -/
  hD : D0 →ₗ[T] D1
  /-- `g∘f ≃ id_C`, degree `1`. -/
  htpyC1 : LinearMap.id - invFun.f1 ∘ₗ toFun.f1 = hC ∘ₗ dC
  /-- `g∘f ≃ id_C`, degree `0`. -/
  htpyC0 : LinearMap.id - invFun.f0 ∘ₗ toFun.f0 = dC ∘ₗ hC
  /-- `f∘g ≃ id_D`, degree `1`. -/
  htpyD1 : LinearMap.id - toFun.f1 ∘ₗ invFun.f1 = hD ∘ₗ dD
  /-- `f∘g ≃ id_D`, degree `0`. -/
  htpyD0 : LinearMap.id - toFun.f0 ∘ₗ invFun.f0 = dD ∘ₗ hD

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (R' : Type*) [CommRing R'] [Algebra R R']

/- Local `P.Ring`-algebra structure on `P' = R' ⊗_R P.Ring` (via the right inclusion
`P.Ring → R' ⊗_R P.Ring`), making `P'` a `P.Ring`-algebra; used to express the
`P'`-module structures of Statement 1. -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## Definition 1 (correctness): a polynomial presentation is a polynomial algebra. -/

/-- Correctness statement for Definition 1: a polynomial presentation
`Algebra.Generators R S ι` has, as its underlying presentation ring, the polynomial
algebra `MvPolynomial ι R` over `R`.  This certifies that the `Algebra.Extension`
obtained from `P.toExtension` is a presentation in the sense of the problem. -/
theorem presentation_ring_is_polynomial {ι : Type*} (P : Algebra.Generators R S ι) :
    P.Ring = MvPolynomial ι R := rfl

/-! ## Statement 1 (Kernel computation — the crux).

`P' = R' ⊗_R P.Ring` is the ring of the base-changed presentation, with kernel
`I' = (P.baseChange).ker`.  We formalize the claim that the canonical map
`R' ⊗_R I → I'` is an isomorphism of `P'`-modules.

The genuine `P'`-module realization of the source `R' ⊗_R I` is the base change
`P' ⊗_{P.Ring} I` (this carries a canonical `P'`-module structure, see
`Algebra.TensorProduct.rightAlgebra`); it is `R'`-linearly identified with `R' ⊗_R I`
by the named comparison `IsPushout.cancelBaseChange` (see `statement1_source_iso`).
We provide the canonical `P'`-linear map `P' ⊗_{P.Ring} I → P'` (`kerMapPrime`) and
assert (Statement 1) that it is a `P'`-linear equivalence onto the kernel ideal
`I'`. -/

/-- The `P.Ring`-linear map `I = P.ker → P' = R' ⊗_R P.Ring` given by the inclusion
`I ↪ P.Ring` followed by the structure map `P.Ring → P'`. -/
noncomputable def inclToPrime (P : Algebra.Extension R S) :
    P.ker →ₗ[P.Ring] (R' ⊗[R] P.Ring) :=
  (Algebra.linearMap P.Ring (R' ⊗[R] P.Ring)) ∘ₗ P.ker.subtype

/-- The canonical `P'`-linear map `R' ⊗_R I = P' ⊗_{P.Ring} I → P'`, the base change of
the inclusion `I ↪ P.Ring`.  Its range is the kernel ideal `I' = (P.baseChange).ker`,
and Statement 1 asserts it induces a `P'`-linear isomorphism onto `I'`. -/
noncomputable def kerMapPrime (P : Algebra.Extension R S) :
    (R' ⊗[R] P.Ring) ⊗[P.Ring] P.ker →ₗ[R' ⊗[R] P.Ring] (R' ⊗[R] P.Ring) :=
  (inclToPrime R' P).liftBaseChange (R' ⊗[R] P.Ring)

/-- The canonical `R'`-linear identification of the source of Statement 1: the genuine
`P'`-module `P' ⊗_{P.Ring} I` is `R'`-linearly the base change `R' ⊗_R I`, via the
named comparison `IsPushout.cancelBaseChange`.  This certifies that `P' ⊗_{P.Ring} I`
is the correct formal realization of "`R' ⊗_R I`". -/
noncomputable def statement1_source_iso (P : Algebra.Extension R S) :
    ((R' ⊗[R] P.Ring) ⊗[P.Ring] P.ker) ≃ₗ[R'] (R' ⊗[R] P.ker) :=
  IsPushout.cancelBaseChange R R' P.Ring (R' ⊗[R] P.Ring) P.ker

/-- **Statement 1** (kernel computation, the crux). Because `R → R'` is flat, the
canonical map `R' ⊗_R I → I'` is an isomorphism of `P' = R' ⊗_R P.Ring`-modules:
`(R' ⊗_R I =) P' ⊗_{P.Ring} I  ≃ₗ[P']  I' = (P.baseChange).ker`
(so the equivalence is the canonical comparison, restricted to its range `I'`).  This
genuinely records the `P'`-linearity of the isomorphism `R' ⊗_R I ≃ I'` of the
problem (the source `P' ⊗_{P.Ring} I` is `R'`-linearly `R' ⊗_R I`, see
`statement1_source_iso`). -/
@[sga "2 III 2.11" "more general",
  sga "3 III 0.14" "partial",
  sga "3 V 9.1" "more general",
  sga "6 VIII 2.2" "(I), special case"]
theorem statement1_kerEquiv [Module.Flat R R'] (P : Algebra.Extension R S) :
    ∃ e : ((R' ⊗[R] P.Ring) ⊗[P.Ring] P.ker) ≃ₗ[R' ⊗[R] P.Ring]
        (P.baseChange (T := R')).ker,
      ((P.baseChange (T := R')).ker.subtype) ∘ₗ (e : _ →ₗ[R' ⊗[R] P.Ring] _)
        = kerMapPrime R' P := by
  -- Math argument: flatness of `R → R'` makes `R' ⊗_R -` exact; applied to the SES
  -- `0 → I → P.Ring → S → 0` it shows `kerMapPrime` is injective with range `I'`.
  -- The `R`-linear inclusion `I ↪ P.Ring` and the structure map `P.Ring → S`.
  set incl : P.ker →ₗ[R] P.Ring := (P.ker.subtype).restrictScalars R with hincl
  set α : P.Ring →ₗ[R] S := (Algebra.linearMap P.Ring S).restrictScalars R with hα
  -- Key identification: `kerMapPrime`, as an `R'`-linear map, is `(lTensor R' incl) ∘ source_iso`.
  have hcomp : (kerMapPrime R' P).restrictScalars R'
      = (AlgebraTensorModule.lTensor R' R' incl) ∘ₗ
          (statement1_source_iso R' P : _ →ₗ[R'] _) := by
    have key : (kerMapPrime R' P).restrictScalars R' ∘ₗ
        (statement1_source_iso R' P).symm.toLinearMap
          = (AlgebraTensorModule.lTensor R' R' incl) := by
      apply TensorProduct.AlgebraTensorModule.curry_injective
      ext s
      show (kerMapPrime R' P) ((statement1_source_iso R' P).symm ((1:R') ⊗ₜ[R] s)) = _
      rw [statement1_source_iso, IsPushout.cancelBaseChange_symm_tmul,
        kerMapPrime, LinearMap.liftBaseChange_tmul, map_one, one_smul]
      show inclToPrime R' P s = (1:R') ⊗ₜ[R] (incl s)
      simp only [inclToPrime, hincl, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.coe_restrictScalars, Algebra.linearMap_apply, Submodule.coe_subtype]
      rw [right_algebraMap_apply]
    rw [← key, LinearMap.comp_assoc]
    simp
  -- (1) `hrange`: range of `kerMapPrime` equals `I' = (P.baseChange).ker`.
  have hrange : LinearMap.range (kerMapPrime R' P) = (P.baseChange (T := R')).ker := by
    have hrangeIncl : LinearMap.range incl = α.ker := by
      have h : α.ker = (P.ker.restrictScalars R) := by
        ext x; simp [hα, Algebra.Extension.ker, RingHom.mem_ker]
      rw [h, hincl, LinearMap.range_restrictScalars]; ext x; simp [Submodule.range_subtype]
    apply SetLike.coe_injective
    show (LinearMap.range (kerMapPrime R' P) : Set (R' ⊗[R] P.Ring)) = _
    -- Identify `range (kerMapPrime R' P)` (as a Set) with `range (AlgebraTensorModule.lTensor R'
    -- R' incl)`:
    -- coerce-equate `range km` with `range (km.restrictScalars R')`, then use `hcomp` and the
    -- `range_comp` / `LinearEquiv.range` / `Submodule.map_top` chain.
    have stepA : (LinearMap.range (kerMapPrime R' P) : Set (R' ⊗[R] P.Ring))
        = (LinearMap.range (AlgebraTensorModule.lTensor R' R' incl) : Set (R' ⊗[R] P.Ring)) := by
      have e1 : (LinearMap.range (kerMapPrime R' P) : Set (R' ⊗[R] P.Ring))
          = (LinearMap.range ((kerMapPrime R' P).restrictScalars R') : Set (R' ⊗[R] P.Ring)) :=
        Set.Subset.antisymm (fun ⦃a⦄ h => h) (fun ⦃a⦄ h => h)
      rw [e1, hcomp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    rw [stepA]
    have eAlgLin : ∀ (f : P.ker →ₗ[R] P.Ring),
        (LinearMap.range (AlgebraTensorModule.lTensor R' R' f) : Set (R' ⊗[R] P.Ring))
          = (LinearMap.range (LinearMap.lTensor R' f) : Set (R' ⊗[R] P.Ring)) :=
      fun f => Set.Subset.antisymm (fun ⦃a⦄ h => h) (fun ⦃a⦄ h => h)
    rw [eAlgLin, LinearMap.lTensor_range, hrangeIncl]
    have eAlgLin2 :
        (LinearMap.range (LinearMap.lTensor R' (α.ker.subtype)) : Set (R' ⊗[R] P.Ring))
          = (LinearMap.range (AlgebraTensorModule.lTensor R' R' (α.ker.subtype)) : Set (R' ⊗[R]
              P.Ring)) :=
      Set.Subset.antisymm (fun ⦃a⦄ h => h) (fun ⦃a⦄ h => h)
    rw [eAlgLin2, ← Module.Flat.ker_lTensor_eq R' R' α]
    ext x
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Algebra.Extension.ker]
    rfl
  -- (2) `hinj`: `kerMapPrime` is injective.
  have hinj : Function.Injective (kerMapPrime R' P) := by
    have hinclInj : Function.Injective incl := by
      rw [hincl]; exact Submodule.injective_subtype P.ker
    have hlt : Function.Injective (LinearMap.lTensor R' incl) :=
      Module.Flat.lTensor_preserves_injective_linearMap incl hinclInj
    have halg : Function.Injective (AlgebraTensorModule.lTensor R' R' incl) := by
      intro a b hab; exact hlt hab
    have hcomp' : Function.Injective ((kerMapPrime R' P).restrictScalars R') := by
      rw [hcomp]; exact halg.comp (statement1_source_iso R' P).injective
    exact hcomp'
  -- ASSEMBLY: build the equivalence onto the range and transport to `I'`.
  refine ⟨(LinearEquiv.ofInjective (kerMapPrime R' P) hinj).trans
      (LinearEquiv.ofEq _ _ hrange), ?_⟩
  letI : Module (P.baseChange (T := R')).Ring ((R' ⊗[R] P.Ring) ⊗[P.Ring] P.ker) :=
    (inferInstance : Module (R' ⊗[R] P.Ring) ((R' ⊗[R] P.Ring) ⊗[P.Ring] P.ker))
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    Submodule.subtype_apply]
  rfl

/-! ## Statements 2 and 3 use the natural `S`-algebra structure on `S' = R' ⊗_R S`,
together with the local `P.Ring`-algebra structure on `P'` declared above.

### Degree-`1` and degree-`0` comparison maps `NL(α) ⊗_S S' → NL(α')`.

These are the `S'`-linear lifts of `Cotangent.map (P.toBaseChange R')` and
`CotangentSpace.map (P.toBaseChange R')`. -/

/-- Degree-`0` component of the canonical comparison `NL(α) ⊗_S S' → NL(α')`:
the `S'`-linear lift of `CotangentSpace.map (P.toBaseChange R')`, i.e.
`S' ⊗_S (Ω_{P/R} ⊗_P S) → Ω_{P'/R'} ⊗_{P'} S'`. -/
noncomputable def cotComparison0 (P : Algebra.Extension R S) :
    (R' ⊗[R] S) ⊗[S] P.CotangentSpace →ₗ[R' ⊗[R] S]
      (P.baseChange (T := R')).CotangentSpace :=
  (Algebra.Extension.CotangentSpace.map (P.toBaseChange R')).liftBaseChange (R' ⊗[R] S)

/-- Degree-`1` component of the canonical comparison `NL(α) ⊗_S S' → NL(α')`:
the `S'`-linear lift of `Cotangent.map (P.toBaseChange R')`, i.e.
`S' ⊗_S (I/I²) → I'/(I')²`. -/
noncomputable def cotComparison1 (P : Algebra.Extension R S) :
    (R' ⊗[R] S) ⊗[S] P.Cotangent →ₗ[R' ⊗[R] S]
      (P.baseChange (T := R')).Cotangent :=
  (Algebra.Extension.Cotangent.map (P.toBaseChange R')).liftBaseChange (R' ⊗[R] S)

/-- The differential of the base-changed complex `NL(α) ⊗_S S'`:
`1 ⊗ d = lTensor S' P.cotangentComplex`. -/
@[sga "3 III 4.8" "(iii), special case"]
noncomputable def cotDiffBaseChangeS (P : Algebra.Extension R S) :
    (R' ⊗[R] S) ⊗[S] P.Cotangent →ₗ[R' ⊗[R] S]
      (R' ⊗[R] S) ⊗[S] P.CotangentSpace :=
  AlgebraTensorModule.lTensor (R' ⊗[R] S) (R' ⊗[R] S) P.cotangentComplex

/-! ### The `⊗_R R'` flavour and the comparison of the two flavours.

The `⊗_R R'` flavour of `NL(α)` has terms `R' ⊗_R M` (an `R'`-complex), differential
`1 ⊗ d` (`R'`-linear).  For each term the canonical `R'`-linear comparison
`R' ⊗_R M ≅ S' ⊗_S M` is the named `IsPushout.cancelBaseChange`. -/

/-- The differential of the `⊗_R R'` flavour `NL(α) ⊗_R R'` (an `R'`-complex):
`1 ⊗ d = baseChange R' P.cotangentComplex`. -/
@[sga "3 III 4.8" "(iii), special case"]
noncomputable def cotDiffBaseChangeR (P : Algebra.Extension R S) :
    (R' ⊗[R] P.Cotangent) →ₗ[R'] (R' ⊗[R] P.CotangentSpace) :=
  LinearMap.baseChange R' P.cotangentComplex

/-- Degree-`1` canonical `R'`-linear comparison of the two flavours
`R' ⊗_R (I/I²) ≅ S' ⊗_S (I/I²)`, the named `IsPushout.cancelBaseChange`. -/
noncomputable def flavorEquiv1 (P : Algebra.Extension R S) :
    (R' ⊗[R] P.Cotangent) ≃ₗ[R'] ((R' ⊗[R] S) ⊗[S] P.Cotangent) :=
  (IsPushout.cancelBaseChange R R' S (R' ⊗[R] S) P.Cotangent).symm

/-- Degree-`0` canonical `R'`-linear comparison of the two flavours
`R' ⊗_R (Ω ⊗_P S) ≅ S' ⊗_S (Ω ⊗_P S)`, the named `IsPushout.cancelBaseChange`. -/
noncomputable def flavorEquiv0 (P : Algebra.Extension R S) :
    (R' ⊗[R] P.CotangentSpace) ≃ₗ[R'] ((R' ⊗[R] S) ⊗[S] P.CotangentSpace) :=
  (IsPushout.cancelBaseChange R R' S (R' ⊗[R] S) P.CotangentSpace).symm

/-- **Statement 2, part (a): the two flavours of base change agree.**

The canonical comparison `NL(α) ⊗_R R' → NL(α) ⊗_S S'` is an isomorphism of two-term
complexes, with degree-`1`/`0` components the named canonical `R'`-linear
identifications `flavorEquiv1`/`flavorEquiv0` (`= IsPushout.cancelBaseChange`).  This
is the `R'`-linear isomorphism of complexes `NL(α) ⊗_R R' ≅ NL(α) ⊗_S S'`, compatible
with the differentials (the `R'` differential `cotDiffBaseChangeR` and the `S'`
differential `cotDiffBaseChangeS`).  It holds without any flatness hypothesis.

(The `S'`-module structure of `NL(α) ⊗_R R'` is, per Definition 4, the one transported
across this very identification; we record the canonical comparison at the `R'`-linear
level, which is its natural home in Mathlib.) -/
theorem statement2_flavor_iso (P : Algebra.Extension R S) :
    ∃ iso : TwoComplexEquiv (cotDiffBaseChangeR R' P) (cotDiffBaseChangeS R' P),
      iso.e1 = flavorEquiv1 R' P ∧ iso.e0 = flavorEquiv0 R' P := by
  /-
  Proof outline (no flatness needed).
  For every `S`-module `M`, the canonical `R'`-linear iso `R' ⊗_R M ≅ S' ⊗_S M`
  (`IsPushout.cancelBaseChange`, `S' = R' ⊗_R S`) is natural in `M`. Applying it
  termwise to `NL(α)` (degrees `1`: `M = P.Cotangent`, degree `0`: `M = P.CotangentSpace`)
  gives the two component equivalences `flavorEquiv1`, `flavorEquiv0`. Naturality of
  `cancelBaseChange` applied to the `S`-linear differential `d = P.cotangentComplex`
  (degree 1 → degree 0) is exactly the commuting square
      `cotDiffBaseChangeS ∘ flavorEquiv1 = flavorEquiv0 ∘ cotDiffBaseChangeR`,
  i.e. `(1_{S'} ⊗ d) ∘ cancelBaseChange.symm = cancelBaseChange.symm ∘ (1_{R'} ⊗ d)`.

  Mathlib realization. Provide the `TwoComplexEquiv` with `e1 := flavorEquiv1 R' P`,
  `e0 := flavorEquiv0 R' P`, and prove `comm` (the naturality square). Both
  `cotDiffBaseChangeR` (`= LinearMap.baseChange R' d`) and `cotDiffBaseChangeS`
  (`= AlgebraTensorModule.lTensor S' d`) are `id ⊗ d` on the respective tensor factors;
  `flavorEquiv0/1 = (cancelBaseChange ...).symm`. The square is the naturality of
  `IsPushout.cancelBaseChange` in its module argument, which holds on elementary tensors
  `r' ⊗ₜ m ↦ (r' • 1) ⊗ₜ m` and commutes with `id ⊗ d` by `TensorProduct.ext`/`lift`.
  -/
  -- One named sub-goal: the naturality/commuting square. The two components are the
  -- already-defined `flavorEquiv1`, `flavorEquiv0`; the `∧` is then `rfl`.
  refine ⟨{ e1 := flavorEquiv1 R' P, e0 := flavorEquiv0 R' P, comm := ?_ }, rfl, rfl⟩
  -- SUB-GOAL (`comm`): naturality of `cancelBaseChange` against `d = P.cotangentComplex`.
  -- Reduce to a `TensorProduct.ext` check on elementary tensors `r' ⊗ₜ x`; both sides
  -- send `r' ⊗ₜ x ↦ algebraMap R' (R'⊗S) r' ⊗ₜ d x` via the `_tmul` simp lemmas.
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext'
  intro r' x
  show (cotDiffBaseChangeS R' P) (flavorEquiv1 R' P (r' ⊗ₜ[R] x))
      = flavorEquiv0 R' P (cotDiffBaseChangeR R' P (r' ⊗ₜ[R] x))
  simp only [cotDiffBaseChangeR, cotDiffBaseChangeS, flavorEquiv0, flavorEquiv1,
    LinearMap.baseChange_tmul, IsPushout.cancelBaseChange_symm_tmul,
    AlgebraTensorModule.lTensor_tmul]
  rfl

/-- **Degree-0 comparison is bijective** (no flatness needed). `cotComparison0 R' P`
is `(CotangentSpace.map (P.toBaseChange R')).liftBaseChange (R'⊗S)`; it factors as the
named Mathlib base-change iso `Algebra.Extension.tensorCotangentSpace P R'` composed
with the flavour-comparison `IsPushout.cancelBaseChange`, hence is bijective.

Proof outline: by `TensorProduct.induction_on`, `cotComparison0 R' P` agrees pointwise with
`(P.tensorCotangentSpace R') ∘ IsPushout.cancelBaseChange R R' S (R'⊗S) P.CotangentSpace`;
both factors are bijective. -/
@[ega "0 22.4.8" "more general"]
theorem cotComparison0_bijective (P : Algebra.Extension R S) :
    Function.Bijective (cotComparison0 R' P) := by
  set g := IsPushout.cancelBaseChange R R' S (R' ⊗[R] S) P.CotangentSpace with hg
  have key : ∀ y : R' ⊗[R] P.CotangentSpace,
      cotComparison0 R' P (g.symm y) = P.tensorCotangentSpace R' y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
        show cotComparison0 R' P (g.symm 0) = P.tensorCotangentSpace R' 0
        simp only [LinearEquiv.map_zero, LinearMap.map_zero]
    | tmul r' x =>
        rw [hg, IsPushout.cancelBaseChange_symm_tmul]
        rw [cotComparison0, LinearMap.liftBaseChange_tmul,
          Algebra.Extension.tensorCotangentSpace_tmul, algebraMap_smul]
    | add a b ha hb => simp [ha, hb]
  have hfun : ⇑(cotComparison0 R' P) = ⇑(P.tensorCotangentSpace R') ∘ ⇑g := by
    funext z
    have := key (g z)
    rw [LinearEquiv.symm_apply_apply] at this
    simpa using this
  rw [hfun]
  exact (P.tensorCotangentSpace R').bijective.comp g.bijective

/-- **Degree-1 comparison is bijective** (uses flatness `Module.Flat R R'`).
`cotComparison1 R' P` is `(Cotangent.map (P.toBaseChange R')).liftBaseChange (R'⊗S)`.
Under flatness it is the underlying map of the Mathlib iso
`Algebra.Extension.tensorCotangent (P.toBaseChange R') halg hbk`
(`Mathlib.RingTheory.Etale.Kaehler`), whose `toLinearMap` is *definitionally*
`liftBaseChange (Cotangent.map (P.toBaseChange R'))`, where:
- `halg : algebraMap P.Ring (P.baseChange).Ring = (P.toBaseChange R').toRingHom`
  (via `Algebra.Extension.toBaseChange_toRingHom` + `RingHom.algebraMap_toAlgebra`,
  with `letI := Algebra.Extension.algebraBaseChange P R'`);
- `hbk : Function.Bijective (((P.toBaseChange R').mapKer halg).liftBaseChange (P.baseChange).Ring)`
  reuses `statement1_kerEquiv`: `subtype ∘ₗ Hm = kerMapPrime` (via `LinearMap.liftBaseChange_comp`,
  `Algebra.Extension.Hom.mapKer`, `toBaseChange_toRingHom`), so `Hm`'s bijectivity transfers
  from `kerMapPrime`'s (range = I', injective).

Rather than invoking `tensorCotangent` itself, bijectivity is proved here in two halves:
injectivity by comparing the map with `Ideal.tensorCotangentEquiv R R' P.ker` (which is where
flatness enters) across the flavour iso `flavorEquiv1` and the transport `Tr` along
`Algebra.Extension.ker_baseChange`, and surjectivity from
`Algebra.Extension.Cotangent.mk_surjective` together with `hbk`. -/
@[sga "3 I 6.8.5" "affine case", sga "3 III 0.14" "partial"]
theorem cotComparison1_bijective [Module.Flat R R'] (P : Algebra.Extension R S) :
    Function.Bijective (cotComparison1 R' P) := by
  let : Algebra P.Ring (P.baseChange (T := R')).Ring := Algebra.Extension.algebraBaseChange P R'
  have halg : algebraMap P.Ring (P.baseChange (T := R')).Ring = (P.toBaseChange R').toRingHom := by
    rw [Algebra.Extension.toBaseChange_toRingHom]; exact RingHom.algebraMap_toAlgebra _
  have hbijKer : Function.Bijective
      ⇑(LinearMap.liftBaseChange (P.baseChange (T := R')).Ring
        ((P.toBaseChange R').mapKer halg)) := by
    obtain ⟨ek, hek⟩ := statement1_kerEquiv R' P
    set Hm := LinearMap.liftBaseChange (P.baseChange (T := R')).Ring
        ((P.toBaseChange R').mapKer halg) with hHm
    have hsub : (P.baseChange (T := R')).ker.subtype ∘ₗ Hm = kerMapPrime R' P := by
      rw [hHm, LinearMap.liftBaseChange_comp]
      congr 1
    have hkmInj : Function.Injective (kerMapPrime R' P) := by
      rw [← hek]
      exact (Submodule.injective_subtype _).comp ek.injective
    have hHmInj : Function.Injective Hm := by
      have h2 : Function.Injective ((P.baseChange (T := R')).ker.subtype ∘ₗ Hm) := by
        rw [hsub]; exact hkmInj
      exact fun a b hab => h2 (by simp only [LinearMap.comp_apply]; rw [hab])
    have hHmSurj : Function.Surjective Hm := by
      intro y
      have hy : ((P.baseChange (T := R')).ker.subtype y) ∈ LinearMap.range (kerMapPrime R' P) := by
        refine ⟨ek.symm y, ?_⟩
        rw [← hek]
        show (P.baseChange (T := R')).ker.subtype (ek (ek.symm y)) = _
        rw [LinearEquiv.apply_symm_apply]
      obtain ⟨z, hz⟩ := hy
      refine ⟨z, ?_⟩
      apply (Submodule.injective_subtype (P.baseChange (T := R')).ker)
      have h3 : ((P.baseChange (T := R')).ker.subtype ∘ₗ Hm) z
          = (P.baseChange (T := R')).ker.subtype (Hm z) := rfl
      rw [hsub] at h3
      rw [← h3]; exact hz
    exact ⟨hHmInj, hHmSurj⟩
  -- With `hbijKer` (the kernel base-change iso, from `statement1_kerEquiv`) in hand, we prove
  -- `cotComparison1 = liftBaseChange (Cotangent.map f)` bijective by splitting into surjectivity
  -- and injectivity.  The direct route through
  -- `Algebra.Extension.tensorCotangent (P.toBaseChange R') halg hbijKer`
  -- is mathematically clean (its `toLinearMap` is *definitionally* `cotComparison1`) but its
  -- elaboration is prohibitively expensive, so the two halves are proved separately below:
  -- injectivity from flatness of `R → R'`, surjectivity from surjectivity of `Cotangent.mk`
  -- together with `hbijKer`.
  set f := P.toBaseChange R' with hf
  refine ⟨?_, ?_⟩
  · -- INJECTIVITY (the crux; the genuine flat-base-change content).
    -- `Ideal.tensorCotangentHom_injective_of_flat` (module
    -- `Mathlib.RingTheory.Ideal.CotangentBaseChange`) gives, for `I = P.ker`, `T = R'`,
    -- `Function.Injective (P.ker.tensorCotangentHom R R')`, where
    -- `P.ker.tensorCotangentHom R R' : R' ⊗[R] P.ker.Cotangent → (Ideal.map includeRight
    -- P.ker).Cotangent`
    -- and `P.Cotangent = P.ker.Cotangent`, `(Ideal.map includeRight P.ker) = (P.baseChange).ker`
    -- (propositionally; `(P.baseChange).Cotangent = (P.baseChange).ker.Cotangent`).
    -- Compose with the flavour iso `flavorEquiv1 : R' ⊗[R] P.Cotangent ≃ₗ[R'] (R'⊗S) ⊗[S]
    -- P.Cotangent`
    -- (= `IsPushout.cancelBaseChange`): showing `(cotComparison1) ∘ₗ flavorEquiv1` equals
    -- `tensorCotangentHom` up to the (injective) `Ideal.Cotangent`-transport across the ideal
    -- equality transfers injectivity (the `Ideal.instModuleCotangentOfAlgebra` ≠
    -- `Extension.instModuleCotangent` mismatch only obstructs a *direct* equality, not an
    -- injectivity-only transfer).
    -- Bridge the cotangent diamond `P.Cotangent` (Extension module) vs `P.ker.Cotangent`
    -- (Ideal module) by the identity-type-synonym maps `Cotangent.val`/`of` (`R`-linear iso).
    let bridgeC : P.Cotangent ≃ₗ[R] P.ker.Cotangent :=
      { toFun := Algebra.Extension.Cotangent.val
        invFun := Algebra.Extension.Cotangent.of
        left_inv := Algebra.Extension.Cotangent.of_val
        right_inv := Algebra.Extension.Cotangent.val_of
        map_add' := Algebra.Extension.Cotangent.val_add
        map_smul' := fun r a => by
          obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective a
          simp only [RingHom.id_apply]
          rw [algebra_compatible_smul P.Ring r (Algebra.Extension.Cotangent.mk y),
              algebra_compatible_smul P.Ring r (Algebra.Extension.Cotangent.mk y).val,
              ← map_smul, Algebra.Extension.Cotangent.val_mk,
              Algebra.Extension.Cotangent.val_mk, ← map_smul] }
    -- Tensor it up to `R`-linear iso on the base-changed source.
    let bridge : (R' ⊗[R] P.Cotangent) ≃ₗ[R] (R' ⊗[R] P.ker.Cotangent) :=
      TensorProduct.congr (LinearEquiv.refl R R') bridgeC
    -- The transport equiv across the ideal equality.
    set Tr := Ideal.Cotangent.equivOfEq
        (Ideal.map (Algebra.TensorProduct.includeRight.toRingHom : P.Ring →+* R' ⊗[R] P.Ring) P.ker)
        (P.baseChange (T := R')).ker
        (Algebra.Extension.ker_baseChange P R').symm with hTr
    -- It suffices to show `⇑(cotComparison1) ∘ ⇑(flavorEquiv1)` is injective, since `flavorEquiv1`
    -- is surjective.
    have hsuff : Function.Injective (⇑(cotComparison1 R' P) ∘ ⇑(flavorEquiv1 R' P)) →
        Function.Injective ⇑(cotComparison1 R' P) := by
      intro hcomp
      have hsurj : Function.Surjective ⇑(flavorEquiv1 R' P) := (flavorEquiv1 R' P).surjective
      intro a b hab
      obtain ⟨a', rfl⟩ := hsurj a
      obtain ⟨b', rfl⟩ := hsurj b
      have he : (⇑(cotComparison1 R' P) ∘ ⇑(flavorEquiv1 R' P)) a'
          = (⇑(cotComparison1 R' P) ∘ ⇑(flavorEquiv1 R' P)) b' := hab
      simpa using congrArg (flavorEquiv1 R' P) (hcomp he)
    apply hsuff
    -- Identify `⇑(cotComparison1) ∘ ⇑(flavorEquiv1) ∘ ⇑(bridge.symm)` with
    -- `⇑Tr ∘ ⇑(tensorCotangentEquiv R R' P.ker)` (as plain functions on
    -- `R' ⊗[R] P.ker.Cotangent`).
    have hfun : ⇑(cotComparison1 R' P) ∘ ⇑(flavorEquiv1 R' P) ∘ ⇑(bridge.symm)
        = ⇑Tr ∘ ⇑(Ideal.tensorCotangentEquiv R R' P.ker) := by
      funext c
      simp only [Function.comp_apply]
      induction c using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add a b ha hb =>
          rw [map_add (Ideal.tensorCotangentEquiv R R' P.ker), map_add Tr, ← ha, ← hb,
            map_add bridge.symm, map_add (flavorEquiv1 R' P), map_add (cotComparison1 R' P)]
      | tmul r' x =>
          induction x using P.ker.toCotangent_surjective.forall.mpr with
          | _ z =>
              -- LHS: simplify bridge.symm then flavorEquiv1 then cotComparison1.
              have hbs : bridge.symm (r' ⊗ₜ[R] P.ker.toCotangent z)
                  = r' ⊗ₜ[R] Algebra.Extension.Cotangent.mk z := by
                show (TensorProduct.congr (LinearEquiv.refl R R') bridgeC).symm
                    (r' ⊗ₜ[R] P.ker.toCotangent z) = _
                rw [TensorProduct.congr_symm_tmul]
                rfl
              rw [hbs]
              -- flavorEquiv1 on the pure tensor.
              have hfe : flavorEquiv1 R' P (r' ⊗ₜ[R] Algebra.Extension.Cotangent.mk z)
                  = (algebraMap R' (R' ⊗[R] S)) r' ⊗ₜ[S] Algebra.Extension.Cotangent.mk z := by
                rw [flavorEquiv1, IsPushout.cancelBaseChange_symm_tmul]
              rw [hfe]
              -- cotComparison1 on the pure tensor.
              rw [cotComparison1, LinearMap.liftBaseChange_tmul]
              -- RHS: tensorCotangentEquiv on the pure tensor.
              rw [Ideal.tensorCotangentEquiv_tmul]
              -- Match the generators: `Cotangent.map f (mk z) = Tr ((Ideal.map ..).toCotangent
              -- ⟨1⊗ₜz,_⟩)`.
              have heq : (Algebra.Extension.Cotangent.map (Algebra.Extension.toBaseChange R'))
                    (Algebra.Extension.Cotangent.mk z)
                  = Tr ((Ideal.map (Algebra.TensorProduct.includeRight.toRingHom :
                        P.Ring →+* R' ⊗[R] P.Ring) P.ker).toCotangent
                      ⟨1 ⊗ₜ[R] (z : P.Ring), Ideal.mem_map_of_mem _ z.property⟩) := by
                rw [Algebra.Extension.Cotangent.map_mk, Ideal.Cotangent.equivOfEq_toCotangent]
                rfl
              -- Push `Tr` through the `r'`-scalar via its `R'`-linearity, then `heq`.
              have hsm : Tr (r' • (Ideal.map (Algebra.TensorProduct.includeRight.toRingHom :
                    P.Ring →+* R' ⊗[R] P.Ring) P.ker).toCotangent
                      ⟨1 ⊗ₜ[R] (z : P.Ring), Ideal.mem_map_of_mem _ z.property⟩)
                  = r' • Tr ((Ideal.map (Algebra.TensorProduct.includeRight.toRingHom :
                        P.Ring →+* R' ⊗[R] P.Ring) P.ker).toCotangent
                      ⟨1 ⊗ₜ[R] (z : P.Ring), Ideal.mem_map_of_mem _ z.property⟩) :=
                map_smul (Tr.restrictScalars R') r' _
              -- Reduce to the underlying `Ideal.Cotangent` via the injective `val`, where the
              -- `R'`-action (through `R' ⊗ P.Ring`) is the unambiguous one; the LHS `S'`-scalar
              -- becomes `σ (algebraMap R' (R'⊗S) r')` by `val_smul`, matching the `R'`-action on
              -- the RHS through `algebra_compatible_smul`.
              rw [hsm]
              -- Goal: `(algebraMap R' (R'⊗S)) r' •[Ext] (Cotangent.map f (mk z))
              --        = r' •[Ideal] Tr (toCotangent ⟨1⊗ₜz⟩)`.  Both `R'`-actions live on
              -- `P.baseChange.Cotangent` (defeq `P.baseChange.ker.Cotangent`) but via the
              -- two diamond-conflicting module instances (`Extension.instModuleCotangent`
              -- through `S'`, `Ideal.instModuleCotangentOfAlgebra` through `R'⊗P.Ring`).
              -- Prove equal by applying the injective `Cotangent.val`, pushing the
              -- smul/`Tr`/`toCotangent` through, and closing in the cotangent quotient:
              -- the two underlying ideal elements differ by
              -- `(σ(r'⊗1) - r'⊗1)·(1⊗ₜz) ∈ I'·I' = I'²`.
              have hvalinj : Function.Injective
                  (Algebra.Extension.Cotangent.val (P := P.baseChange (T := R'))) :=
                Function.LeftInverse.injective Algebra.Extension.Cotangent.of_val
              apply hvalinj
              rw [Algebra.Extension.Cotangent.val_smul, Algebra.Extension.Cotangent.map_mk,
                Algebra.Extension.Cotangent.val_mk]
              show _ = (r' • Tr ((Ideal.map (Algebra.TensorProduct.includeRight.toRingHom :
                  P.Ring →+* R' ⊗[R] P.Ring) P.ker).toCotangent
                    ⟨1 ⊗ₜ[R] (z : P.Ring), Ideal.mem_map_of_mem _ z.property⟩))
              rw [← algebraMap_smul (R' ⊗[R] P.Ring) r', hTr,
                ← map_smul (Ideal.Cotangent.equivOfEq _ _ _),
                ← map_smul ((Ideal.map (Algebra.TensorProduct.includeRight.toRingHom :
                  P.Ring →+* R' ⊗[R] P.Ring) P.ker).toCotangent),
                Ideal.Cotangent.equivOfEq_toCotangent,
                ← map_smul ((P.baseChange (T := R')).ker.toCotangent)]
              apply (Ideal.toCotangent_eq _).mpr
              have hdiff : P.baseChange.σ ((algebraMap R' (R' ⊗[R] S)) r')
                  - (algebraMap R' ((P.baseChange (T := R')).Ring)) r'
                    ∈ (P.baseChange (T := R')).ker := by
                rw [Algebra.Extension.ker, RingHom.mem_ker, map_sub, sub_eq_zero,
                  Algebra.Extension.algebraMap_σ,
                  ← IsScalarTower.algebraMap_apply R' (P.baseChange (T := R')).Ring (R' ⊗[R] S)]
              have h1z : (1 ⊗ₜ[R] (z : P.Ring) : R' ⊗[R] P.Ring)
                  ∈ (P.baseChange (T := R')).ker := by
                rw [Algebra.Extension.ker_baseChange]; exact Ideal.mem_map_of_mem _ z.property
              have hmem : ((P.baseChange.σ ((algebraMap R' (R' ⊗[R] S)) r')
                    - (algebraMap R' ((P.baseChange (T := R')).Ring)) r' : (P.baseChange (T :=
                        R')).Ring)
                  * (⟨1 ⊗ₜ[R] (z : P.Ring), h1z⟩ : (P.baseChange (T := R')).ker))
                  ∈ (P.baseChange (T := R')).ker ^ 2 := by
                rw [pow_two]; exact Ideal.mul_mem_mul hdiff h1z
              rw [LinearEquiv.coe_ofEq_apply, SetLike.val_smul, SetLike.val_smul,
                smul_eq_mul, smul_eq_mul]
              convert hmem using 1
              rw [sub_mul]
              rfl
    -- Conclude injectivity of the composite (without bridge) from that of `Tr ∘
    -- tensorCotangentEquiv`.
    have hcompInj : Function.Injective
        (⇑(cotComparison1 R' P) ∘ ⇑(flavorEquiv1 R' P) ∘ ⇑(bridge.symm)) := by
      rw [hfun]
      exact Tr.injective.comp (Ideal.tensorCotangentEquiv R R' P.ker).injective
    -- `bridge.symm` is bijective, so the composite without it is injective too.
    intro a b hab
    apply bridge.injective
    apply hcompInj
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
    exact hab
  · -- SURJECTIVITY: every generator `mk y` of `(P.baseChange).Cotangent` is hit.  Since `mk` is
    -- surjective and (by `hbijKer`) every `y ∈ (P.baseChange).ker` is `liftBaseChange (mapKer f)
    -- w`,
    -- and `mk (mapKer f x) = Cotangent.map f (mk x)`, the `P'.Ring`-scalar action factors through
    -- `S'` (`algebraMap_smul`), giving `mk y` in the range of `cotComparison1`.
    have key : ∀ w : (R' ⊗[R] P.Ring) ⊗[P.Ring] P.ker,
        Algebra.Extension.Cotangent.mk
            (LinearMap.liftBaseChange (P.baseChange (T := R')).Ring (f.mapKer halg) w)
          ∈ LinearMap.range (cotComparison1 R' P) := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
      | tmul a x =>
          rw [LinearMap.liftBaseChange_tmul, map_smul]
          have hmk : Algebra.Extension.Cotangent.mk ((f.mapKer halg) x)
              = Algebra.Extension.Cotangent.map f (Algebra.Extension.Cotangent.mk x) := by
            rw [Algebra.Extension.Cotangent.map_mk]; rfl
          rw [hmk]
          refine ⟨(algebraMap (P.baseChange (T := R')).Ring (R' ⊗[R] S) a)
            ⊗ₜ[S] Algebra.Extension.Cotangent.mk x, ?_⟩
          rw [cotComparison1, LinearMap.liftBaseChange_tmul]
          exact algebraMap_smul (R' ⊗[R] S) (show (P.baseChange (T := R')).Ring from a)
            (Algebra.Extension.Cotangent.map f (Algebra.Extension.Cotangent.mk x))
    intro c
    obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective c
    obtain ⟨w, hw⟩ := hbijKer.right y
    rw [← hw]
    exact key w

/-- Naturality of the cotangent complex for a hom `f : P.Hom Q` of extensions, after
`liftBaseChange` along `S → S' = R' ⊗_R S`. -/
private theorem cotangentComplex_comp_liftBaseChange_map (P : Algebra.Extension R S)
    (Q : Algebra.Extension R' (R' ⊗[R] S)) (f : P.Hom Q) :
    Q.cotangentComplex ∘ₗ (Algebra.Extension.Cotangent.map f).liftBaseChange (R' ⊗[R] S)
      = (Algebra.Extension.CotangentSpace.map f).liftBaseChange (R' ⊗[R] S)
        ∘ₗ cotDiffBaseChangeS R' P := by
  apply LinearMap.restrictScalars_injective S
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext s x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    cotDiffBaseChangeS, TensorProduct.AlgebraTensorModule.lTensor_tmul, map_smul,
    LinearMap.liftBaseChange_tmul]
  congr 1
  exact (Algebra.Extension.CotangentSpace.map_cotangentComplex f x).symm

/-- **The differential square commutes**: `(P.baseChange).cotangentComplex ∘ₗ cotComparison1
= cotComparison0 ∘ₗ cotDiffBaseChangeS`. This is naturality of the cotangent complex for the
hom `P.toBaseChange R'` after `liftBaseChange`.

Proof outline: reduce to elementary tensors and apply
`Algebra.Extension.CotangentSpace.map_cotangentComplex (P.toBaseChange R')`. -/
theorem cotComparison_comm (P : Algebra.Extension R S) :
    (P.baseChange (T := R')).cotangentComplex ∘ₗ cotComparison1 R' P
      = cotComparison0 R' P ∘ₗ cotDiffBaseChangeS R' P :=
  cotangentComplex_comp_liftBaseChange_map R' P _ (P.toBaseChange R')

/-- **Statement 2, part (b): the canonical comparison is an isomorphism.**

If `R → R'` is flat, the canonical comparison `NL(α) ⊗_S S' → NL(α')` is an isomorphism of
two-term complexes of `S' = R' ⊗_R S`-modules, with degree-`1` component `cotComparison1`
(bijective by flatness) and degree-`0` component `cotComparison0` (always bijective). -/
@[stacks 00S4,
  ega "IV 16.2.2" "(iii)",
  ega "IV 16.2.4" "affine case",
  sga "3 I 6.8.5" "special case",
  sga "3 III 0.14" "partial"]
theorem statement2_complex_iso [Module.Flat R R'] (P : Algebra.Extension R S) :
    ∃ iso : TwoComplexEquiv (cotDiffBaseChangeS R' P)
        (P.baseChange (T := R')).cotangentComplex,
      (iso.e1 : _ →ₗ[R' ⊗[R] S] _) = cotComparison1 R' P ∧
        (iso.e0 : _ →ₗ[R' ⊗[R] S] _) = cotComparison0 R' P := by
  /-
  Proof outline (uses flatness; degree 1 reuses Statement 1).
  The canonical comparison `NL(α) ⊗_S S' → NL(α')` has
  degree-1 component `cotComparison1` (iso under flatness) and degree-0 component
  `cotComparison0` (always iso), commuting with the differentials. Build `e0`,`e1` via
  `LinearEquiv.ofBijective` of the comparison maps themselves, so that the `∧`
  components `he0`/`he1` are `rfl`; the `comm` field is `cotComparison_comm`.
  -/
  -- Build the component equivalences directly from the bijectivity helpers, so the
  -- underlying-map equalities are `rfl` (dodging the defeq/elaboration wall on `he1`).
  refine ⟨{ e1 := LinearEquiv.ofBijective (cotComparison1 R' P) (cotComparison1_bijective R' P),
            e0 := LinearEquiv.ofBijective (cotComparison0 R' P) (cotComparison0_bijective R' P),
            comm := cotComparison_comm R' P }, rfl, rfl⟩

/-! ## Statement 3 (Homotopy equivalence; flat base change for `NL_{S/R}`).

If `R → R'` is flat, the canonical comparison map of *naive cotangent complexes*

  `NL_{S/R} ⊗_S S' → NL_{S'/R'}`

is a *homotopy equivalence* of two-term complexes of `S'`-modules; in particular a
quasi-isomorphism.  We use the canonical polynomial presentations:

* `NL_{S/R}` is `NL` of `(Generators.self R S).toExtension`;
* `NL_{S'/R'}` is `NL` of `(Generators.self R' (R' ⊗_R S)).toExtension` — the
  **canonical** presentation of `S' = R' ⊗_R S` over `R'`, as required by the problem.

The comparison is the chain map whose degree-`1`/`0` components are the `S'`-linear
lifts (`liftBaseChange`) of `Cotangent.map h`, `CotangentSpace.map h`, for
`h : Pc.Hom Pc'` the canonical `defaultHom` between the two canonical presentations.
`NL_{S/R} ⊗_S S'` is `(S' ⊗_S Cotangent) → (S' ⊗_S CotangentSpace)` with differential
`1 ⊗ cotangentComplex`. -/

/-- The canonical homomorphism of extensions from the canonical presentation of `S`
over `R` to the canonical presentation of `S' = R' ⊗_R S` over `R'`. -/
noncomputable def canHom :
    ((Algebra.Generators.self R S).toExtension).Hom
      ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension) :=
  ((Algebra.Generators.self R S).defaultHom
    (Algebra.Generators.self R' (R' ⊗[R] S))).toExtensionHom

/-- The differential of `NL_{S/R} ⊗_S S'`. -/
noncomputable def nlCanDiffBaseChange :
    (R' ⊗[R] S) ⊗[S] ((Algebra.Generators.self R S).toExtension).Cotangent →ₗ[R' ⊗[R] S]
      (R' ⊗[R] S) ⊗[S] ((Algebra.Generators.self R S).toExtension).CotangentSpace :=
  AlgebraTensorModule.lTensor (R' ⊗[R] S) (R' ⊗[R] S)
    ((Algebra.Generators.self R S).toExtension).cotangentComplex

/-- Degree-`1` component of the canonical comparison chain map
`NL_{S/R} ⊗_S S' → NL_{S'/R'}`: the `S'`-linear lift of `Cotangent.map (canHom)`. -/
noncomputable def statement3_f1 :
    (R' ⊗[R] S) ⊗[S] ((Algebra.Generators.self R S).toExtension).Cotangent
      →ₗ[R' ⊗[R] S]
      ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).Cotangent :=
  (Algebra.Extension.Cotangent.map (canHom R')).liftBaseChange (R' ⊗[R] S)

/-- Degree-`0` component of the canonical comparison chain map
`NL_{S/R} ⊗_S S' → NL_{S'/R'}`: the `S'`-linear lift of `CotangentSpace.map (canHom)`. -/
noncomputable def statement3_f0 :
    (R' ⊗[R] S) ⊗[S] ((Algebra.Generators.self R S).toExtension).CotangentSpace
      →ₗ[R' ⊗[R] S]
      ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).CotangentSpace :=
  (Algebra.Extension.CotangentSpace.map (canHom R')).liftBaseChange (R' ⊗[R] S)

/-- The base-changed canonical presentation `α'` of `S' = R' ⊗_R S` over `R'`
(`Generators` flavor): `α' = (Generators.self R S).baseChange R'`, with `α'.vars = S`
and `α'.Ring = R' ⊗_R (Generators.self R S).Ring`.  This is the presentation through
which the canonical comparison `canHom : Pc → Pc'` factors: `canHom = (defaultHom) ∘ (base-change
hom)`. -/
noncomputable def alphaPrime : Algebra.Generators R' (R' ⊗[R] S) S :=
  (Algebra.Generators.self R S).baseChange R'

/-! ### Bridge between the two flavors of base change (for SUB-LEMMA A).

`statement3_baseChangeComplexIso` compares `NL_{S/R} ⊗_S S'` (the source differential
`nlCanDiffBaseChange R'`) with `NL(α')` for `α' = (Generators.self R S).baseChange R'`
(the *Generators*-flavor base change).  The already-proven `statement2_complex_iso`,
applied to `P := (Generators.self R S).toExtension`, instead lands on the
*Extension*-flavor base change `P.baseChange (T := R')`, and crucially
`nlCanDiffBaseChange R' = cotDiffBaseChangeS R' P` *syntactically* (both are
`AlgebraTensorModule.lTensor (R'⊗S) (R'⊗S) P.cotangentComplex`).  So `A` reduces to a
**bridge isomorphism** of complexes between the two flavors' targets,
`pbc = P.baseChange R'` and `pap = α'.toExtension`, composed with `statement2_complex_iso`.

The bridge is a genuine iso of extensions: both present `S' = R' ⊗_R S` over `R'`, with
`pbc.Ring = R' ⊗_R MvPolynomial S R` and `pap.Ring = MvPolynomial S R'`, identified by the
`AlgEquiv` `MvPolynomial.algebraTensorAlgEquiv R R'`. -/

/-- The Extension-flavor base change `P.baseChange R'` of the canonical presentation. -/
noncomputable abbrev FlatBC.pbc : Algebra.Extension R' (R' ⊗[R] S) :=
  ((Algebra.Generators.self R S).toExtension).baseChange (T := R')

/-- The Generators-flavor base change `α'.toExtension`. -/
noncomputable abbrev FlatBC.pap : Algebra.Extension R' (R' ⊗[R] S) :=
  (alphaPrime (R := R) (S := S) R').toExtension

/-- The ring-level identification
`pbc.Ring = R' ⊗_R MvPolynomial S R ≃ₐ MvPolynomial S R' = pap.Ring`. -/
noncomputable def bridgeE : (FlatBC.pbc (R := R) (S := S) R').Ring ≃ₐ[R'] (MvPolynomial S R') :=
  MvPolynomial.algebraTensorAlgEquiv R R'

/-- The presentation surjection of `pap` (Generators flavor). -/
noncomputable def surjAp : (FlatBC.pap (R := R) (S := S) R').Ring →ₐ[R'] (R' ⊗[R] S) :=
  IsScalarTower.toAlgHom R' _ _
/-- The presentation surjection of `pbc` (Extension flavor). -/
noncomputable def surjBc : (FlatBC.pbc (R := R) (S := S) R').Ring →ₐ[R'] (R' ⊗[R] S) :=
  IsScalarTower.toAlgHom R' _ _

/-- The bridge `AlgEquiv` `bridgeE` is compatible with the two presentation surjections:
`surjAp ∘ bridgeE = surjBc`.  Proven by `MvPolynomial.induction_on` on the underlying
polynomial. -/
theorem bridge_surj_comm :
    (surjAp (R := R) (S := S) R').comp (bridgeE R').toAlgHom = surjBc R' := by
  have hE : ∀ p : MvPolynomial S R,
      bridgeE R' ((1:R') ⊗ₜ[R] p) = MvPolynomial.map (algebraMap R R') p := fun p => by
    rw [bridgeE]; erw [MvPolynomial.algebraTensorAlgEquiv_tmul]; simp
  have hAp : ∀ q : MvPolynomial S R', (surjAp (R := R) (S := S) R') q
      = MvPolynomial.aeval (fun s => (1:R') ⊗ₜ[R] s) q := fun q => by
    change (algebraMap (alphaPrime (R := R) (S := S) R').toExtension.Ring (R' ⊗[R] S)) q = _
    exact Algebra.Generators.algebraMap_apply (alphaPrime (R := R) (S := S) R') q
  have hBc : ∀ p : MvPolynomial S R, (surjBc (R := R) (S := S) R') ((1:R') ⊗ₜ[R] p)
      = algebraMap S (R' ⊗[R] S) (MvPolynomial.aeval id p) := fun p => by
    change (algebraMap (FlatBC.pbc (R := R) (S := S) R').Ring (R' ⊗[R] S)) ((1:R') ⊗ₜ[R] p) = _
    have hb : ((1:R') ⊗ₜ[R] p : (FlatBC.pbc (R := R) (S := S) R').Ring)
        = ((Algebra.Generators.self R S).toExtension.toBaseChange R').toRingHom p := by
      rw [Algebra.Extension.toBaseChange_toRingHom]; rfl
    rw [hb, ((Algebra.Generators.self R S).toExtension.toBaseChange R').algebraMap_toRingHom]
    rfl
  have key : ∀ p : MvPolynomial S R,
      (surjAp (R := R) (S := S) R') (bridgeE R' ((1:R') ⊗ₜ[R] p))
        = (surjBc (R := R) (S := S) R') ((1:R') ⊗ₜ[R] p) := by
    intro p
    rw [hE, hAp, hBc, MvPolynomial.aeval_map_algebraMap,
      ← MvPolynomial.aeval_algebraMap_apply]
    rfl
  apply Algebra.TensorProduct.ext'
  intro r p
  have hfac : (r ⊗ₜ[R] p : (FlatBC.pbc (R := R) (S := S) R').Ring) = r • ((1:R') ⊗ₜ[R] p) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hfac, map_smul, map_smul, AlgHom.comp_apply]
  exact congrArg (r • ·) (key p)

/-- The bridge hom of extensions `bridgeG : pbc → pap` (Extension flavor → Generators flavor),
with underlying ring map `bridgeE`.  `toRingHom_algebraMap` by `AlgEquiv.commutes`;
`algebraMap_toRingHom` is `bridge_surj_comm` applied pointwise. -/
noncomputable def bridgeG :
    (FlatBC.pbc (R := R) (S := S) R').Hom (FlatBC.pap (R := R) (S := S) R') where
  toRingHom := (bridgeE (R := R) (S := S) R').toAlgHom.toRingHom
  toRingHom_algebraMap := by
    intro x
    change (bridgeE (R := R) (S := S) R').toAlgHom ((algebraMap R' _) x) = _
    rw [AlgHom.commutes]
    rfl
  algebraMap_toRingHom := by
    intro x
    have h := DFunLike.congr_fun (bridge_surj_comm (R := R) (S := S) R') x
    simp only [AlgHom.comp_apply, surjAp, surjBc,
      IsScalarTower.coe_toAlgHom'] at h
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    exact h

/-- The reverse bridge hom `bridgeH : pap → pbc`, with underlying ring map `bridgeE.symm`.
Symmetric to `bridgeG`. -/
noncomputable def bridgeH :
    (FlatBC.pap (R := R) (S := S) R').Hom (FlatBC.pbc (R := R) (S := S) R') where
  toRingHom := (bridgeE (R := R) (S := S) R').symm.toAlgHom.toRingHom
  toRingHom_algebraMap := by
    intro x
    change (bridgeE (R := R) (S := S) R').symm.toAlgHom ((algebraMap R' _) x) = _
    rw [AlgHom.commutes]
    rfl
  algebraMap_toRingHom := by
    intro x
    have h := DFunLike.congr_fun (bridge_surj_comm (R := R) (S := S) R')
      ((bridgeE (R := R) (S := S) R').symm x)
    simp only [AlgHom.comp_apply, surjAp, surjBc,
      IsScalarTower.coe_toAlgHom'] at h
    have hx : (bridgeE (R := R) (S := S) R') ((bridgeE (R := R) (S := S) R').symm x) = x :=
      AlgEquiv.apply_symm_apply _ _
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    conv_rhs => rw [← hx]
    exact h.symm

/-- Round-trip `bridgeG ∘ bridgeH = id` (on `pap`).  Hom-ext on `toRingHom` +
`bridgeE.symm`/`bridgeE` round trip. -/
theorem bridgeGH_id :
    (bridgeG (R := R) (S := S) R').comp (bridgeH (R := R) (S := S) R')
      = Algebra.Extension.Hom.id (FlatBC.pap (R := R) (S := S) R') := by
  apply Algebra.Extension.Hom.ext
  rw [Algebra.Extension.Hom.comp_toRingHom, Algebra.Extension.Hom.id_toRingHom]
  apply RingHom.ext
  intro x
  show (bridgeE (R := R) (S := S) R') ((bridgeE (R := R) (S := S) R').symm x) = x
  rw [AlgEquiv.apply_symm_apply]

/-- Round-trip `bridgeH ∘ bridgeG = id` (on `pbc`). -/
theorem bridgeHG_id :
    (bridgeH (R := R) (S := S) R').comp (bridgeG (R := R) (S := S) R')
      = Algebra.Extension.Hom.id (FlatBC.pbc (R := R) (S := S) R') := by
  apply Algebra.Extension.Hom.ext
  rw [Algebra.Extension.Hom.comp_toRingHom, Algebra.Extension.Hom.id_toRingHom]
  apply RingHom.ext
  intro x
  show (bridgeE (R := R) (S := S) R').symm ((bridgeE (R := R) (S := S) R') x) = x
  rw [AlgEquiv.symm_apply_apply]

/-- The bridge isomorphism of two-term complexes `NL(pbc) ≅ NL(pap)` (no flatness;
a genuine iso of extensions induces an iso of cotangent complexes).  Degree-`1`/`0`
equivalences via `Cotangent.map`/`CotangentSpace.map` of `bridgeG`/`bridgeH`
(`LinearEquiv.ofLinear` + `map_comp`/`map_id` from the round-trips); `comm` via
`CotangentSpace.map_cotangentComplex bridgeG`. -/
noncomputable def bridgeTwoComplexEquiv :
    TwoComplexEquiv ((FlatBC.pbc (R := R) (S := S) R').cotangentComplex)
      ((FlatBC.pap (R := R) (S := S) R').cotangentComplex) where
  e1 := LinearEquiv.ofLinearMap
    (Algebra.Extension.Cotangent.map (bridgeG (R := R) (S := S) R'))
    (Algebra.Extension.Cotangent.map (bridgeH (R := R) (S := S) R'))
    (by
      ext y
      have h := DFunLike.congr_fun (Algebra.Extension.Cotangent.map_comp _
        (bridgeH (R := R) (S := S) R') (bridgeG (R := R) (S := S) R')).symm y
      rw [bridgeGH_id, Algebra.Extension.Cotangent.map_id] at h
      exact h)
    (by
      ext y
      have h := DFunLike.congr_fun (Algebra.Extension.Cotangent.map_comp _
        (bridgeG (R := R) (S := S) R') (bridgeH (R := R) (S := S) R')).symm y
      rw [bridgeHG_id, Algebra.Extension.Cotangent.map_id] at h
      exact h)
  e0 := LinearEquiv.ofLinearMap
    (Algebra.Extension.CotangentSpace.map (bridgeG (R := R) (S := S) R'))
    (Algebra.Extension.CotangentSpace.map (bridgeH (R := R) (S := S) R'))
    (by
      refine LinearMap.ext fun y => ?_
      have h := DFunLike.congr_fun (Algebra.Extension.CotangentSpace.map_comp
        (bridgeH (R := R) (S := S) R') (bridgeG (R := R) (S := S) R')).symm y
      rw [bridgeGH_id, Algebra.Extension.CotangentSpace.map_id] at h
      exact h)
    (by
      refine LinearMap.ext fun y => ?_
      have h := DFunLike.congr_fun (Algebra.Extension.CotangentSpace.map_comp
        (bridgeG (R := R) (S := S) R') (bridgeH (R := R) (S := S) R')).symm y
      rw [bridgeHG_id, Algebra.Extension.CotangentSpace.map_id] at h
      exact h)
  comm := by
    ext x
    exact (Algebra.Extension.CotangentSpace.map_cotangentComplex
      (bridgeG (R := R) (S := S) R') x).symm

/-- **Statement 3, part (A)** (flatness; the genuine analytic kernel).  The
`Generators`-flavor flat base-change isomorphism of two-term complexes
`NL_{S/R} ⊗_S S' ≅ NL(α')`.

Proof outline: `nlCanDiffBaseChange R' = cotDiffBaseChangeS R' P` syntactically for
`P := (Generators.self R S).toExtension`, so `statement2_complex_iso R' P` gives a
`TwoComplexEquiv (nlCanDiffBaseChange R') (pbc.cotangentComplex)`.  Compose with the
flavor-`bridgeTwoComplexEquiv : pbc ≅ pap` (`= alphaPrime.toExtension`) by composing the
degree-`1`/`0` `LinearEquiv`s and chaining the two `comm` squares. -/
theorem statement3_baseChangeComplexIso (R' : Type*) [CommRing R'] [Algebra R R']
    [Module.Flat R R'] :
    Nonempty (TwoComplexEquiv (nlCanDiffBaseChange (R := R) (S := S) R')
      ((alphaPrime (R := R) (S := S) R').toExtension).cotangentComplex) := by
  obtain ⟨iso2, _, _⟩ := statement2_complex_iso R' ((Algebra.Generators.self R S).toExtension)
  refine ⟨{
    e1 := iso2.e1 ≪≫ₗ (bridgeTwoComplexEquiv (R := R) (S := S) R').e1,
    e0 := iso2.e0 ≪≫ₗ (bridgeTwoComplexEquiv (R := R) (S := S) R').e0,
    comm := ?_ }⟩
  have h2 := iso2.comm
  have hb := (bridgeTwoComplexEquiv (R := R) (S := S) R').comm
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, ← LinearMap.comp_assoc, hb,
    LinearMap.comp_assoc, h2, ← LinearMap.comp_assoc]
  rfl

/-- **Statement 3, part (B)** (no flatness).  The homotopy
equivalence between the naive cotangent complexes of the two presentations of the SAME
`R'`-algebra `S'`, `NL(α') ≃ NL(Pc')`, where `Pc' = Generators.self R' (R' ⊗_R S)`.

Proof outline (no flatness; entirely within the Mathlib `Hom` API):
let `dHom := α'.defaultHom Pc'` and `eHom := Pc'.defaultHom α'` (as extension homs via
`toExtensionHom`).  Take
  `toFun := { f1 := Cotangent.map dHom, f0 := CotangentSpace.map dHom, comm := … }`,
  `invFun := { f1 := Cotangent.map eHom, f0 := CotangentSpace.map eHom, comm := … }`,
  `hC := (Hom.id (α'.toExtension)).sub (eHom.comp dHom)`,
  `hD := (Hom.id (Pc'.toExtension)).sub (dHom.comp eHom)`.
Each `comm` is `Algebra.Extension.CotangentSpace.map_cotangentComplex`.  Each of the four
homotopy identities `id - map(g)∘map(f) = h∘d` / `d∘h` reduces, via
`Algebra.Extension.Cotangent.map_id`, `Cotangent.map_comp` (rewriting `id` as
`Cotangent.map Hom.id` and `map g ∘ map f` as `Cotangent.map (g.comp f)`), to
`Algebra.Extension.Cotangent.map_sub_map` (degree 1) and
`Algebra.Extension.CotangentSpace.map_sub_map` (degree 0) for the pairs `(Hom.id, g.comp f)`. -/
noncomputable def statement3_presentationHtpyEquiv :
    HtpyEquiv ((alphaPrime R').toExtension).cotangentComplex
      ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).cotangentComplex :=
  let Pc' := Algebra.Generators.self R' (R' ⊗[R] S)
  let α' := alphaPrime (R := R) (S := S) R'
  let dHom : α'.toExtension.Hom Pc'.toExtension := (α'.defaultHom Pc').toExtensionHom
  let eHom : Pc'.toExtension.Hom α'.toExtension := (Pc'.defaultHom α').toExtensionHom
  { toFun :=
      { f1 := Algebra.Extension.Cotangent.map dHom
        f0 := Algebra.Extension.CotangentSpace.map dHom
        comm := by
          ext x
          exact (Algebra.Extension.CotangentSpace.map_cotangentComplex dHom x).symm }
    invFun :=
      { f1 := Algebra.Extension.Cotangent.map eHom
        f0 := Algebra.Extension.CotangentSpace.map eHom
        comm := by
          ext x
          exact (Algebra.Extension.CotangentSpace.map_cotangentComplex eHom x).symm }
    hC := (Algebra.Extension.Hom.id (α'.toExtension)).sub (eHom.comp dHom)
    hD := (Algebra.Extension.Hom.id (Pc'.toExtension)).sub (dHom.comp eHom)
    htpyC1 := by
      change LinearMap.id - (Algebra.Extension.Cotangent.map eHom) ∘ₗ
          (Algebra.Extension.Cotangent.map dHom) = _
      have hcomp : (Algebra.Extension.Cotangent.map eHom) ∘ₗ
          (Algebra.Extension.Cotangent.map dHom)
          = Algebra.Extension.Cotangent.map (eHom.comp dHom) :=
        (Algebra.Extension.Cotangent.map_comp _ dHom eHom).symm
      rw [hcomp, ← Algebra.Extension.Cotangent.map_id (P := α'.toExtension)]
      exact Algebra.Extension.Cotangent.map_sub_map _ _
    htpyC0 := by
      change LinearMap.id - (Algebra.Extension.CotangentSpace.map eHom) ∘ₗ
          (Algebra.Extension.CotangentSpace.map dHom) = _
      have hcomp : (Algebra.Extension.CotangentSpace.map eHom) ∘ₗ
          (Algebra.Extension.CotangentSpace.map dHom)
          = Algebra.Extension.CotangentSpace.map (eHom.comp dHom) :=
        (Algebra.Extension.CotangentSpace.map_comp dHom eHom).symm
      rw [hcomp, ← Algebra.Extension.CotangentSpace.map_id (P := α'.toExtension)]
      exact Algebra.Extension.CotangentSpace.map_sub_map _ _
    htpyD1 := by
      change LinearMap.id - (Algebra.Extension.Cotangent.map dHom) ∘ₗ
          (Algebra.Extension.Cotangent.map eHom) = _
      have hcomp : (Algebra.Extension.Cotangent.map dHom) ∘ₗ
          (Algebra.Extension.Cotangent.map eHom)
          = Algebra.Extension.Cotangent.map (dHom.comp eHom) :=
        (Algebra.Extension.Cotangent.map_comp _ eHom dHom).symm
      rw [hcomp, ← Algebra.Extension.Cotangent.map_id (P := Pc'.toExtension)]
      exact Algebra.Extension.Cotangent.map_sub_map _ _
    htpyD0 := by
      change LinearMap.id - (Algebra.Extension.CotangentSpace.map dHom) ∘ₗ
          (Algebra.Extension.CotangentSpace.map eHom) = _
      have hcomp : (Algebra.Extension.CotangentSpace.map dHom) ∘ₗ
          (Algebra.Extension.CotangentSpace.map eHom)
          = Algebra.Extension.CotangentSpace.map (dHom.comp eHom) :=
        (Algebra.Extension.CotangentSpace.map_comp eHom dHom).symm
      rw [hcomp, ← Algebra.Extension.CotangentSpace.map_id (P := Pc'.toExtension)]
      exact Algebra.Extension.CotangentSpace.map_sub_map _ _ }

/-- Compose a strict isomorphism of two-term complexes (zero homotopy) on the left of a
homotopy equivalence: `A : C ≅ E`, `G : E ≃ D` gives `C ≃ D`.  The forward components are
`G.toFun ∘ A.e`, the backward `A.e.symm ∘ G.invFun`, the homotopy `hC` is `G.hC` conjugated
by `A.e`, and `hD := G.hD`. -/
noncomputable def htpyComposeIsoLeft {T : Type*} [CommRing T]
    {C1 C0 E1 E0 D1 D0 : Type*}
    [AddCommGroup C1] [Module T C1] [AddCommGroup C0] [Module T C0]
    [AddCommGroup E1] [Module T E1] [AddCommGroup E0] [Module T E0]
    [AddCommGroup D1] [Module T D1] [AddCommGroup D0] [Module T D0]
    {dC : C1 →ₗ[T] C0} {dE : E1 →ₗ[T] E0} {dD : D1 →ₗ[T] D0}
    (A : TwoComplexEquiv dC dE) (G : HtpyEquiv dE dD) : HtpyEquiv dC dD where
  toFun :=
    { f1 := G.toFun.f1 ∘ₗ (A.e1 : C1 →ₗ[T] E1)
      f0 := G.toFun.f0 ∘ₗ (A.e0 : C0 →ₗ[T] E0)
      comm := by
        rw [← LinearMap.comp_assoc, G.toFun.comm, LinearMap.comp_assoc, A.comm,
          ← LinearMap.comp_assoc] }
  invFun :=
    { f1 := (A.e1.symm : E1 →ₗ[T] C1) ∘ₗ G.invFun.f1
      f0 := (A.e0.symm : E0 →ₗ[T] C0) ∘ₗ G.invFun.f0
      comm := by
        have hsymm : dC ∘ₗ (A.e1.symm : E1 →ₗ[T] C1)
            = (A.e0.symm : E0 →ₗ[T] C0) ∘ₗ dE := by
          apply LinearMap.ext; intro x
          apply A.e0.injective
          have hcm := DFunLike.congr_fun A.comm (A.e1.symm x)
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
            LinearEquiv.apply_symm_apply] at hcm ⊢
          rw [← hcm]
        rw [← LinearMap.comp_assoc, hsymm, LinearMap.comp_assoc, G.invFun.comm,
          ← LinearMap.comp_assoc] }
  hC := (A.e1.symm : E1 →ₗ[T] C1) ∘ₗ G.hC ∘ₗ (A.e0 : C0 →ₗ[T] E0)
  hD := G.hD
  htpyC1 := by
    -- `dE ∘ A.e1 = A.e0 ∘ dC`
    have hcomm := A.comm
    -- `G.invFun.f1 ∘ G.toFun.f1 = id - G.hC ∘ dE`
    have hG : G.invFun.f1 ∘ₗ G.toFun.f1 = LinearMap.id - G.hC ∘ₗ dE := by
      have h := G.htpyC1
      rw [sub_eq_iff_eq_add] at h
      rw [h]; abel
    change LinearMap.id - ((A.e1.symm : E1 →ₗ[T] C1) ∘ₗ G.invFun.f1)
        ∘ₗ (G.toFun.f1 ∘ₗ (A.e1 : C1 →ₗ[T] E1)) = _
    have hexp : ((A.e1.symm : E1 →ₗ[T] C1) ∘ₗ G.invFun.f1)
          ∘ₗ (G.toFun.f1 ∘ₗ (A.e1 : C1 →ₗ[T] E1))
        = (A.e1.symm : E1 →ₗ[T] C1) ∘ₗ (G.invFun.f1 ∘ₗ G.toFun.f1) ∘ₗ (A.e1 : C1 →ₗ[T] E1) := by
      simp only [LinearMap.comp_assoc]
    rw [hexp, hG]
    have hcancel : (A.e1.symm : E1 →ₗ[T] C1) ∘ₗ (A.e1 : C1 →ₗ[T] E1) = LinearMap.id := by
      apply LinearMap.ext; intro x; simp
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp, LinearMap.comp_assoc,
      hcancel]
    -- goal: id - (id - A.e1.symm ∘ G.hC ∘ dE ∘ A.e1) = (A.e1.symm ∘ G.hC ∘ A.e0) ∘ dC
    have hdEe1 : dE ∘ₗ (A.e1 : C1 →ₗ[T] E1) = (A.e0 : C0 →ₗ[T] E0) ∘ₗ dC := hcomm
    apply LinearMap.ext; intro x
    have hd := DFunLike.congr_fun hdEe1 x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe] at hd ⊢
    rw [hd]; abel
  htpyC0 := by
    have hG : G.invFun.f0 ∘ₗ G.toFun.f0 = LinearMap.id - dE ∘ₗ G.hC := by
      have h := G.htpyC0
      rw [sub_eq_iff_eq_add] at h
      rw [h]; abel
    change LinearMap.id - ((A.e0.symm : E0 →ₗ[T] C0) ∘ₗ G.invFun.f0)
        ∘ₗ (G.toFun.f0 ∘ₗ (A.e0 : C0 →ₗ[T] E0)) = _
    have hexp : ((A.e0.symm : E0 →ₗ[T] C0) ∘ₗ G.invFun.f0)
          ∘ₗ (G.toFun.f0 ∘ₗ (A.e0 : C0 →ₗ[T] E0))
        = (A.e0.symm : E0 →ₗ[T] C0) ∘ₗ (G.invFun.f0 ∘ₗ G.toFun.f0) ∘ₗ (A.e0 : C0 →ₗ[T] E0) := by
      simp only [LinearMap.comp_assoc]
    rw [hexp, hG]
    have hcancel : (A.e0.symm : E0 →ₗ[T] C0) ∘ₗ (A.e0 : C0 →ₗ[T] E0) = LinearMap.id := by
      apply LinearMap.ext; intro x; simp
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp, LinearMap.comp_assoc,
      hcancel]
    -- need `A.e0.symm ∘ dE = dC ∘ A.e1.symm`
    have hsymm : (A.e0.symm : E0 →ₗ[T] C0) ∘ₗ dE = dC ∘ₗ (A.e1.symm : E1 →ₗ[T] C1) := by
      apply LinearMap.ext; intro x
      apply A.e0.injective
      have hcm := DFunLike.congr_fun A.comm (A.e1.symm x)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at hcm ⊢
      rw [← hcm]
    apply LinearMap.ext; intro x
    have hd := DFunLike.congr_fun hsymm (G.hC (A.e0 x))
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe] at hd ⊢
    rw [hd]; abel
  htpyD1 := by
    change LinearMap.id - (G.toFun.f1 ∘ₗ (A.e1 : C1 →ₗ[T] E1)) ∘ₗ ((A.e1.symm : E1 →ₗ[T] C1) ∘ₗ
        G.invFun.f1) = _
    have hthis : (G.toFun.f1 ∘ₗ (A.e1 : C1 →ₗ[T] E1)) ∘ₗ ((A.e1.symm : E1 →ₗ[T] C1) ∘ₗ G.invFun.f1)
        = G.toFun.f1 ∘ₗ G.invFun.f1 := by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hthis]; exact G.htpyD1
  htpyD0 := by
    change LinearMap.id - (G.toFun.f0 ∘ₗ (A.e0 : C0 →ₗ[T] E0)) ∘ₗ ((A.e0.symm : E0 →ₗ[T] C0) ∘ₗ
        G.invFun.f0) = _
    have hthis : (G.toFun.f0 ∘ₗ (A.e0 : C0 →ₗ[T] E0)) ∘ₗ ((A.e0.symm : E0 →ₗ[T] C0) ∘ₗ G.invFun.f0)
        = G.toFun.f0 ∘ₗ G.invFun.f0 := by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hthis]; exact G.htpyD0

/-- Transport a homotopy equivalence along a chain homotopy of forward maps: given
`he0 : HtpyEquiv dC dD` and a chain map `F : ChainMap dC dD` chain-homotopic to `he0.toFun`
via `s : C0 →ₗ D1` (so `he0.toFun.f1 - F.f1 = s ∘ dC` and `he0.toFun.f0 - F.f0 = dD ∘ s`),
produce a homotopy equivalence whose forward map is exactly `F`. -/
noncomputable def htpyEquivOfHomotopicToFun {T : Type*} [CommRing T]
    {C1 C0 D1 D0 : Type*}
    [AddCommGroup C1] [Module T C1] [AddCommGroup C0] [Module T C0]
    [AddCommGroup D1] [Module T D1] [AddCommGroup D0] [Module T D0]
    {dC : C1 →ₗ[T] C0} {dD : D1 →ₗ[T] D0}
    (he0 : HtpyEquiv dC dD) (F : ChainMap dC dD) (s : C0 →ₗ[T] D1)
    (hs1 : he0.toFun.f1 - F.f1 = s ∘ₗ dC)
    (hs0 : he0.toFun.f0 - F.f0 = dD ∘ₗ s) : HtpyEquiv dC dD where
  toFun := F
  invFun := he0.invFun
  hC := he0.hC + he0.invFun.f1 ∘ₗ s
  hD := he0.hD + s ∘ₗ he0.invFun.f0
  htpyC1 := by
    have hF1 : F.f1 = he0.toFun.f1 - s ∘ₗ dC := by rw [← hs1]; abel
    have h := he0.htpyC1
    rw [hF1, LinearMap.comp_sub, LinearMap.add_comp, ← LinearMap.comp_assoc]
    rw [show LinearMap.id - (he0.invFun.f1 ∘ₗ he0.toFun.f1 - (he0.invFun.f1 ∘ₗ s) ∘ₗ dC)
        = (LinearMap.id - he0.invFun.f1 ∘ₗ he0.toFun.f1) + (he0.invFun.f1 ∘ₗ s) ∘ₗ dC by abel]
    rw [h]
  htpyC0 := by
    have hF0 : F.f0 = he0.toFun.f0 - dD ∘ₗ s := by rw [← hs0]; abel
    have h := he0.htpyC0
    have hcomm := he0.invFun.comm
    rw [hF0, LinearMap.comp_sub, LinearMap.comp_add]
    rw [show LinearMap.id - (he0.invFun.f0 ∘ₗ he0.toFun.f0 - he0.invFun.f0 ∘ₗ dD ∘ₗ s)
        = (LinearMap.id - he0.invFun.f0 ∘ₗ he0.toFun.f0) + (he0.invFun.f0 ∘ₗ dD) ∘ₗ s by
      rw [LinearMap.comp_assoc]; abel]
    rw [h, ← hcomm, LinearMap.comp_assoc]
  htpyD1 := by
    have hF1 : F.f1 = he0.toFun.f1 - s ∘ₗ dC := by rw [← hs1]; abel
    have h := he0.htpyD1
    have hcomm := he0.invFun.comm
    rw [hF1, LinearMap.sub_comp, LinearMap.add_comp]
    rw [show LinearMap.id - (he0.toFun.f1 ∘ₗ he0.invFun.f1 - (s ∘ₗ dC) ∘ₗ he0.invFun.f1)
        = (LinearMap.id - he0.toFun.f1 ∘ₗ he0.invFun.f1) + s ∘ₗ (dC ∘ₗ he0.invFun.f1) by
      rw [LinearMap.comp_assoc]; abel]
    rw [h, hcomm, ← LinearMap.comp_assoc]
  htpyD0 := by
    have hF0 : F.f0 = he0.toFun.f0 - dD ∘ₗ s := by rw [← hs0]; abel
    have h := he0.htpyD0
    rw [hF0, LinearMap.sub_comp, LinearMap.comp_add, ← LinearMap.comp_assoc]
    rw [show LinearMap.id - (he0.toFun.f0 ∘ₗ he0.invFun.f0 - (dD ∘ₗ s) ∘ₗ he0.invFun.f0)
        = (LinearMap.id - he0.toFun.f0 ∘ₗ he0.invFun.f0) + dD ∘ₗ (s ∘ₗ he0.invFun.f0) by
      rw [LinearMap.comp_assoc]; abel]
    rw [h, LinearMap.comp_assoc]

/-- The canonical `defaultHom` from `α'` to the canonical presentation `Pc'`, as an
extension hom (degree-`0`/`1` maps of `B = statement3_presentationHtpyEquiv`). -/
noncomputable def statement3_dHom :
    (alphaPrime (R := R) (S := S) R').toExtension.Hom
      ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension) :=
  ((alphaPrime (R := R) (S := S) R').defaultHom
    (Algebra.Generators.self R' (R' ⊗[R] S))).toExtensionHom

/-- The composite hom `Pc → α' → Pc'` realized by `B.toFun ∘ A` at the presentation level:
`statement3_g = dHom ∘ bridgeG ∘ (P.toBaseChange R')`.  Its `Cotangent.map`/`CotangentSpace.map`,
lifted via `liftBaseChange`, are the forward components of the composite `he0 = A ∘ B`. -/
noncomputable def statement3_g :
    ((Algebra.Generators.self R S).toExtension).Hom
      ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension) :=
  ((statement3_dHom R').comp (bridgeG (R := R) (S := S) R')).comp
    (((Algebra.Generators.self R S).toExtension).toBaseChange R')

/-- Degree-`1` forward-component identification: the composite forward `f1` of `A ∘ B`
equals the `liftBaseChange` of `Cotangent.map statement3_g`. -/
theorem statement3_hcomp1
    (iso2 : TwoComplexEquiv (cotDiffBaseChangeS R' ((Algebra.Generators.self R S).toExtension))
      (((Algebra.Generators.self R S).toExtension).baseChange (T := R')).cotangentComplex)
    (hiso1 : (iso2.e1 : _ →ₗ[R' ⊗[R] S] _)
      = cotComparison1 R' ((Algebra.Generators.self R S).toExtension)) :
    (Algebra.Extension.Cotangent.map (statement3_dHom R'))
        ∘ₗ (↑(iso2.e1 ≪≫ₗ (bridgeTwoComplexEquiv (R := R) (S := S) R').e1)
          : (R' ⊗[R] S) ⊗[S] ((Algebra.Generators.self R S).toExtension).Cotangent
            →ₗ[R' ⊗[R] S] _)
      = (Algebra.Extension.Cotangent.map (statement3_g R')).liftBaseChange (R' ⊗[R] S) := by
  set P := (Algebra.Generators.self R S).toExtension with hP
  rw [LinearEquiv.coe_trans, hiso1]
  apply LinearMap.restrictScalars_injective S
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext a y
  show (Algebra.Extension.Cotangent.map (statement3_dHom R'))
      ((Algebra.Extension.Cotangent.map (bridgeG (R := R) (S := S) R'))
        (cotComparison1 R' P (a ⊗ₜ[S] y)))
    = a • (Algebra.Extension.Cotangent.map (statement3_g R')) y
  rw [cotComparison1, LinearMap.liftBaseChange_tmul, map_smul, map_smul]
  congr 1
  show (Algebra.Extension.Cotangent.map (statement3_dHom R'))
      ((Algebra.Extension.Cotangent.map (bridgeG (R := R) (S := S) R'))
        ((Algebra.Extension.Cotangent.map (P.toBaseChange R')) y))
    = (Algebra.Extension.Cotangent.map (statement3_g R')) y
  rw [statement3_g, statement3_dHom] at *
  rw [Algebra.Extension.Cotangent.map_comp _ (P.toBaseChange R')
      (((alphaPrime R').defaultHom _).toExtensionHom.comp (bridgeG R')),
    Algebra.Extension.Cotangent.map_comp _ (bridgeG (R := R) (S := S) R')
      ((alphaPrime R').defaultHom _).toExtensionHom]
  rfl

/-- Degree-`0` forward-component identification: the composite forward `f0` of `A ∘ B`
equals the `liftBaseChange` of `CotangentSpace.map statement3_g`. -/
theorem statement3_hcomp0
    (iso2 : TwoComplexEquiv (cotDiffBaseChangeS R' ((Algebra.Generators.self R S).toExtension))
      (((Algebra.Generators.self R S).toExtension).baseChange (T := R')).cotangentComplex)
    (hiso0 : (iso2.e0 : _ →ₗ[R' ⊗[R] S] _)
      = cotComparison0 R' ((Algebra.Generators.self R S).toExtension)) :
    (Algebra.Extension.CotangentSpace.map (statement3_dHom R'))
        ∘ₗ (↑(iso2.e0 ≪≫ₗ (bridgeTwoComplexEquiv (R := R) (S := S) R').e0)
          : (R' ⊗[R] S) ⊗[S] ((Algebra.Generators.self R S).toExtension).CotangentSpace
            →ₗ[R' ⊗[R] S] _)
      = (Algebra.Extension.CotangentSpace.map (statement3_g R')).liftBaseChange (R' ⊗[R] S) := by
  set P := (Algebra.Generators.self R S).toExtension with hP
  rw [LinearEquiv.coe_trans, hiso0]
  apply LinearMap.restrictScalars_injective S
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext a y
  show (Algebra.Extension.CotangentSpace.map (statement3_dHom R'))
      ((Algebra.Extension.CotangentSpace.map (bridgeG (R := R) (S := S) R'))
        (cotComparison0 R' P (a ⊗ₜ[S] y)))
    = a • (Algebra.Extension.CotangentSpace.map (statement3_g R')) y
  rw [cotComparison0, LinearMap.liftBaseChange_tmul, map_smul, map_smul]
  congr 1
  show (Algebra.Extension.CotangentSpace.map (statement3_dHom R'))
      ((Algebra.Extension.CotangentSpace.map (bridgeG (R := R) (S := S) R'))
        ((Algebra.Extension.CotangentSpace.map (P.toBaseChange R')) y))
    = (Algebra.Extension.CotangentSpace.map (statement3_g R')) y
  rw [statement3_g, statement3_dHom] at *
  rw [Algebra.Extension.CotangentSpace.map_comp (P.toBaseChange R')
      (((alphaPrime R').defaultHom _).toExtensionHom.comp (bridgeG R')),
    Algebra.Extension.CotangentSpace.map_comp (bridgeG (R := R) (S := S) R')
      ((alphaPrime R').defaultHom _).toExtensionHom]
  rfl

/-- The degree-`1` chain-homotopy witness for Statement 3: the composite forward `f1`
(`Cotangent.map dHom ∘ₗ A.e1`) differs from the canonical comparison `statement3_f1`
by `s ∘ₗ d`, where `s = (Hom.sub statement3_g canHom).liftBaseChange`.  Combines
`statement3_hcomp1` with `Cotangent.map_sub_map` and `liftBaseChange` naturality. -/
theorem statement3_hs1
    (iso2 : TwoComplexEquiv (cotDiffBaseChangeS R' ((Algebra.Generators.self R S).toExtension))
      (((Algebra.Generators.self R S).toExtension).baseChange (T := R')).cotangentComplex)
    (hiso1 : (iso2.e1 : _ →ₗ[R' ⊗[R] S] _)
      = cotComparison1 R' ((Algebra.Generators.self R S).toExtension)) :
    (Algebra.Extension.Cotangent.map (statement3_dHom R'))
        ∘ₗ (↑(iso2.e1 ≪≫ₗ (bridgeTwoComplexEquiv (R := R) (S := S) R').e1)
          : (R' ⊗[R] S) ⊗[S] ((Algebra.Generators.self R S).toExtension).Cotangent
            →ₗ[R' ⊗[R] S] _)
        - statement3_f1 R'
      = ((Algebra.Extension.Hom.sub (statement3_g R') (canHom R')).liftBaseChange (R' ⊗[R] S))
        ∘ₗ nlCanDiffBaseChange R' := by
  rw [statement3_hcomp1 R' iso2 hiso1, statement3_f1]
  have hmsm :
      Algebra.Extension.Cotangent.map (statement3_g R')
          - Algebra.Extension.Cotangent.map (canHom R')
        = (Algebra.Extension.Hom.sub (statement3_g R') (canHom R'))
          ∘ₗ ((Algebra.Generators.self R S).toExtension).cotangentComplex :=
    Algebra.Extension.Cotangent.map_sub_map (statement3_g R') (canHom R')
  apply LinearMap.restrictScalars_injective S
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext a x
  have hx := DFunLike.congr_fun hmsm x
  simp only [nlCanDiffBaseChange, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.restrictScalars_apply,
    TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.sub_apply, LinearMap.liftBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.lTensor_tmul] at hx ⊢
  rw [← smul_sub, hx]

/-- The degree-`0` chain-homotopy witness for Statement 3.  Combines `statement3_hcomp0`
with `CotangentSpace.map_sub_map` and `liftBaseChange` naturality. -/
theorem statement3_hs0
    (iso2 : TwoComplexEquiv (cotDiffBaseChangeS R' ((Algebra.Generators.self R S).toExtension))
      (((Algebra.Generators.self R S).toExtension).baseChange (T := R')).cotangentComplex)
    (hiso0 : (iso2.e0 : _ →ₗ[R' ⊗[R] S] _)
      = cotComparison0 R' ((Algebra.Generators.self R S).toExtension)) :
    (Algebra.Extension.CotangentSpace.map (statement3_dHom R'))
        ∘ₗ (↑(iso2.e0 ≪≫ₗ (bridgeTwoComplexEquiv (R := R) (S := S) R').e0)
          : (R' ⊗[R] S) ⊗[S] ((Algebra.Generators.self R S).toExtension).CotangentSpace
            →ₗ[R' ⊗[R] S] _)
        - statement3_f0 R'
      = ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).cotangentComplex
        ∘ₗ ((Algebra.Extension.Hom.sub (statement3_g R') (canHom R')).liftBaseChange
          (R' ⊗[R] S)) := by
  rw [statement3_hcomp0 R' iso2 hiso0, statement3_f0]
  have hmsm :
      Algebra.Extension.CotangentSpace.map (statement3_g R')
          - Algebra.Extension.CotangentSpace.map (canHom R')
        = (((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).cotangentComplex.restrictScalars
            S)
          ∘ₗ (Algebra.Extension.Hom.sub (statement3_g R') (canHom R')) :=
    Algebra.Extension.CotangentSpace.map_sub_map (statement3_g R') (canHom R')
  apply LinearMap.restrictScalars_injective S
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext a x
  have hx := DFunLike.congr_fun hmsm x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.sub_apply, LinearMap.liftBaseChange_tmul, map_smul] at hx ⊢
  rw [← smul_sub, hx]

/-- Helper for Statement 3: from the flat base-change iso `iso2` (Statement 2 applied to
the canonical presentation) build the homotopy equivalence whose forward map is exactly the
canonical comparison `statement3_f1/f0`. -/
noncomputable def statement3_he
    (iso2 : TwoComplexEquiv (cotDiffBaseChangeS R' ((Algebra.Generators.self R S).toExtension))
      (((Algebra.Generators.self R S).toExtension).baseChange (T := R')).cotangentComplex)
    (hiso1 : (iso2.e1 : _ →ₗ[R' ⊗[R] S] _)
      = cotComparison1 R' ((Algebra.Generators.self R S).toExtension))
    (hiso0 : (iso2.e0 : _ →ₗ[R' ⊗[R] S] _)
      = cotComparison0 R' ((Algebra.Generators.self R S).toExtension))
    (fwdComm : ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).cotangentComplex
        ∘ₗ statement3_f1 R' = statement3_f0 R' ∘ₗ nlCanDiffBaseChange R') :
    HtpyEquiv (nlCanDiffBaseChange R')
      ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).cotangentComplex :=
  let P := (Algebra.Generators.self R S).toExtension
  let A : TwoComplexEquiv (nlCanDiffBaseChange (R := R) (S := S) R')
      ((alphaPrime (R := R) (S := S) R').toExtension).cotangentComplex :=
    { e1 := iso2.e1 ≪≫ₗ (bridgeTwoComplexEquiv (R := R) (S := S) R').e1,
      e0 := iso2.e0 ≪≫ₗ (bridgeTwoComplexEquiv (R := R) (S := S) R').e0,
      comm := by
        have h2 := iso2.comm
        have hb := (bridgeTwoComplexEquiv (R := R) (S := S) R').comm
        rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, ← LinearMap.comp_assoc, hb,
          LinearMap.comp_assoc, h2, ← LinearMap.comp_assoc]
        rfl }
  let B := statement3_presentationHtpyEquiv (R := R) (S := S) R'
  let he0 := htpyComposeIsoLeft A B
  let fwd : ChainMap (nlCanDiffBaseChange R')
      ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).cotangentComplex :=
    { f1 := statement3_f1 R', f0 := statement3_f0 R', comm := fwdComm }
  let g : P.Hom ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension) := statement3_g R'
  let s : (R' ⊗[R] S) ⊗[S] P.CotangentSpace →ₗ[R' ⊗[R] S]
      ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).Cotangent :=
    (Algebra.Extension.Hom.sub g (canHom R')).liftBaseChange (R' ⊗[R] S)
  htpyEquivOfHomotopicToFun he0 fwd s
    (statement3_hs1 R' iso2 hiso1)
    (statement3_hs0 R' iso2 hiso0)

/-- **Statement 3**: under flatness of `R → R'`, the canonical comparison chain map of
naive cotangent complexes `NL_{S/R} ⊗_S S' → NL_{S'/R'}` (with `NL_{S'/R'}` the
canonical presentation of `S' = R' ⊗_R S` over `R'`) is a homotopy equivalence of
two-term complexes of `S'`-modules; in particular a quasi-isomorphism.

The asserted homotopy equivalence has as its forward chain map the canonical comparison,
i.e. the `ChainMap` whose degree-`1`/`0` components are the canonical comparisons
`statement3_f1`/`statement3_f0` (the `S'`-linear lifts of `Cotangent.map (canHom)`,
`CotangentSpace.map (canHom)`). -/
@[stacks 00S4]
theorem statement3_homotopy_equiv [Module.Flat R R'] :
    ∃ he : HtpyEquiv (nlCanDiffBaseChange R')
        ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).cotangentComplex,
      he.toFun.f1 = statement3_f1 R' ∧ he.toFun.f0 = statement3_f0 R' := by
  /-
  Proof outline.
  Write `Pc = (Generators.self R S)` (canonical presentation of `S/R`), so
  `NL_{S/R} = NL(Pc)`, and `Pc' = (Generators.self R' (R' ⊗_R S))` (canonical
  presentation of `S'/R'`), so `NL_{S'/R'} = NL(Pc')`. Let `α' = Pc.baseChange (T:=R')`
  be the base-changed presentation of `S'` over `R'`. There are two facts:
  (A) [Statement 2, flat] `NL(Pc) ⊗_S S' ≅ NL(α')` is an ISO of complexes
      (`statement2_complex_iso` applied to `P := Pc.toExtension`). In particular a
      homotopy equivalence.
  (B) [Stacks 10.134.2, well-definedness up to homotopy] `α'` and `Pc'` are two
      presentations of the SAME `R'`-algebra `S'`; hence `NL(α')` and `NL(Pc')` are
      homotopy equivalent, with the homotopy equivalence given by the canonical
      `defaultHom` maps in both directions (`Cotangent.map`/`CotangentSpace.map` of
      `α'.defaultHom Pc'` and back), the homotopies built from the section difference.
  The canonical comparison `NL_{S/R} ⊗_S S' → NL_{S'/R'}` (components `statement3_f1/f0`,
  the `S'`-lifts of `Cotangent.map (canHom)`, `CotangentSpace.map (canHom)`) factors as
  (A) followed by (B) up to homotopy, because `canHom` is the composite
  `Pc → α' → Pc'` of base-change and `defaultHom` at the level of presentations
  (`defaultHom` is unique up to homotopy). Hence it is a homotopy equivalence.

  Relevant Mathlib API: `Algebra.Generators.H1Cotangent.equiv` (presentations agree on H1),
  `Algebra.Generators.defaultHom`, `Algebra.Extension.Cotangent.map`/`CotangentSpace.map`
  functoriality, and `statement2_complex_iso` for (A).
  -/
  -- Forward chain map: the canonical comparison (components fixed as `statement3_f1/f0`).
  have fwdComm : ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).cotangentComplex
        ∘ₗ statement3_f1 R' = statement3_f0 R' ∘ₗ nlCanDiffBaseChange R' :=
    cotangentComplex_comp_liftBaseChange_map R' _ _ (canHom R')
  obtain ⟨iso2, hiso1, hiso0⟩ := statement2_complex_iso R' ((Algebra.Generators.self R
      S).toExtension)
  exact ⟨statement3_he R' iso2 hiso1 hiso0 fwdComm, rfl, rfl⟩

end

end FlatBaseChangeNL

-- ===== merged from StacksDraft.Ch10.Sec134.Tag06RQ =====

/-!
# The base-change square for the naive cotangent complex

The display records the commutative square of commutative unital rings

    S ──φ──▶ S'
    ▲        ▲
    │        │
    R ─────▶ R'

used to compare the naive cotangent complexes of `S/R` and `S'/R'`. It introduces no
object beyond the square itself, so it carries no separate Lean statement.
-/

@[expose] public section
