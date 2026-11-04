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
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.Homology.Double

/-!
# The naive cotangent complex

Let `R → S` be a ring map. Write `R[S]` for the polynomial ring over `R` on the set of
variables `[s]`, one for each `s ∈ S`, and let `I ⊆ R[S]` be the kernel of the canonical
surjection `R[S] → S`, `[s] ↦ s` (Stacks 07BL). The *naive cotangent complex* of `S` over `R`
is the two-term chain complex of `S`-modules
```
NL_{S/R} = (I/I² ⟶ Ω_{R[S]/R} ⊗_{R[S]} S)
```
with `I/I²` in homological degree `1`, `Ω_{R[S]/R} ⊗_{R[S]} S` in homological degree `0`, and
the canonical map of Stacks 07BM as its differential: the class of `f ∈ I` is sent to
`df ⊗ 1`. The degree-`0` term is free on the classes `d[s]`, `s ∈ S`, the degree-`0` homology
is `Ω_{S/R}` (Stacks 00RU), and the degree-`1` homology is written `H₁(L_{S/R})`, the notation
being justified by the fact that `NL_{S/R}` is the truncation `τ_{≤ 1} L_{S/R}` of the full
cotangent complex.

More generally, a presentation `α : P → S` (with `P = R[x_a : a ∈ A]` a polynomial `R`-algebra
and `α` surjective with kernel `I`) has the naive cotangent complex
`NL(α) : I/I² --d_α--> Ω_{P/R} ⊗_P S`. A commutative square of rings (`R → S`, `R' → S'`,
`R → R'`, `φ : S → S'`) together with presentations `α` of `S/R` and `α'` of `S'/R'` gives rise,
via a morphism of presentations `varphi : P → P'`, to a chain map
`NL(varphi) : NL(α) → NL(α')`, and this is unique up to homotopy (Stacks 00S1).

## Main definitions

* `Algebra.naiveCotangentComplex R S`: the naive cotangent complex `NL_{S/R}`, as an object of
  `ChainComplex (ModuleCat S) ℕ` (Stacks 07BN).
* `NaiveCotangent.NL P`: the naive cotangent complex `NL(α)` of a presentation, as a
  `NaiveCotangent.TwoTerm S`, and `NaiveCotangent.nlMap P P' φ` the chain map induced by a
  morphism of presentations.

## Main results

Stacks 00S1:
* `NaiveCotangent.exists_hom`: (1) a morphism of presentations covering the square exists;
* `NaiveCotangent.nlMap_homotopic`: (2) any two induce homotopic chain maps;
* `NaiveCotangent.nlMapBase_comp_nlMapBase`: (3) compatibility with composition;
* `NaiveCotangent.nlMap_isHomotopyEquiv_and_isQuasiIso`: (4) if `R → R'` and `S → S'` are
  isomorphisms, `NL(varphi)` is a homotopy equivalence and a quasi-isomorphism;
* `NaiveCotangent.nlMap_canonical_isQuasiIso`: the comparison `NL(α) → NL_{S/R}` with the
  canonical presentation is a quasi-isomorphism.

## Implementation notes

The three ingredients of `Algebra.naiveCotangentComplex` are Mathlib's, taken for the canonical
presentation `Algebra.Generators.self R S : Algebra.Generators R S S`, which is `R[S] → S`,
`[s] ↦ s`, with `R[S]` spelled `MvPolynomial S R`: writing `P` for its `Algebra.Extension`, the
modules `P.Cotangent` and `P.CotangentSpace` are `I/I²` and `Ω_{R[S]/R} ⊗_{R[S]} S`, and
`P.cotangentComplex` is the map of Stacks 07BM. What this definition adds is the packaging as a
single chain complex carrying the source's homological degrees; Mathlib keeps the differential
and its kernel `Algebra.H1Cotangent R S`, which is by construction the degree-`1` homology of
this complex, but not the complex itself.

The construction is `HomologicalComplex.double`, so the complex is zero outside degrees `1`
and `0`, and `HomologicalComplex.doubleXIso₀`, `doubleXIso₁`, `double_d`, `double_d_eq_zero₀`
and `isZero_double_X` describe its objects and differentials without unfolding it;
`mkHomFromDouble` maps out of it.

`P.CotangentSpace` is `S ⊗_{R[S]} Ω_{R[S]/R}`, the source's module with the tensor factors in
Mathlib's order; the two agree by `TensorProduct.comm`.

For `R : Type u` and `S : Type v` both terms live in `Type (max u v)`, which is why they are
objects of a single `ModuleCat.{max u v} S`. This is also what confines the definition to the
canonical presentation: for a general `P : Algebra.Extension.{w} R S` the two modules live in
`Type w` and `Type (max v w)`, so they lie in one `ModuleCat S` only when `v ≤ w`; the complex
`NL(α)` of an arbitrary presentation `α` is therefore carried by the pair of modules together
with `Algebra.Extension.cotangentComplex`, which is what `NaiveCotangent.TwoTerm` packages.

Faithfulness of `Algebra.naiveCotangentComplex`. (1) The hypotheses are exactly `CommRing R`,
`CommRing S` and `Algebra R S`, the ring map `R → S` of the source, and all three are used, to
form `R[S]`, its ideal `I` and the differential; none is inert. (2) The scalars and the base are
the source's: the complex is one of `S`-modules over the given `S`, and `Ω_{R[S]/R}` is the
module of differentials of `R[S]` relative to the given `R` — not relative to `R[S]`, nor to a
localization of `R`. (3) The canonical map of Stacks 07BM is pinned rather than asserted to
exist: the differential is `Algebra.Extension.cotangentComplex` of the canonical presentation,
placed from degree `1` to degree `0`, so `f ∈ I` goes to `df ⊗ 1` on the nose. (4) The
instantiation is not degenerate: the presentation used is the polynomial one `R[S] → S`, not the
trivial extension `Algebra.Extension.self R S`, for which `I = 0` and `Ω_{S/S} = 0` and the
complex would be zero in both degrees; here the degree-`0` term is free on the classes `d[s]`,
`s ∈ S`, hence nonzero for every `R → S`, and for `R = ℤ`, `S = ℤ[x]` the degree-`0` homology is
`Ω_{S/R} ≅ S ≠ 0`, so the complex is not acyclic either.

For Stacks 00S1 we use Mathlib's `Algebra.Generators R S ι` as the notion of *presentation*: a
polynomial ring `MvPolynomial ι R` with chosen generators `val : ι → S` and a section `σ'`, the
algebra map `MvPolynomial ι R → S` being `MvPolynomial.aeval val`, which is surjective. A
*morphism of presentations* is `Algebra.Generators.Hom`, whose `aeval_val` field encodes the
commutativity `φ ∘ α = α' ∘ varphi`. The commutative square is encoded by the instances
`[Algebra R R'] [Algebra S S'] [Algebra R S']` together with the scalar-tower laws
`[IsScalarTower R R' S'] [IsScalarTower R S S']`. The induced maps on the two-term complexes are
`Algebra.Extension.Cotangent.map` and `Algebra.Extension.CotangentSpace.map`; these are
`S'`-linear, and the target complex `NL(α')` is viewed over `S` by restricting scalars along
`algebraMap S S'`. The homotopy of statement (2) is `Algebra.Extension.Hom.sub`, characterized by
`Cotangent.map_sub_map` and `CotangentSpace.map_sub_map`.

## References

* [StacksProject 07BN](https://stacks.math.columbia.edu/tag/07BN)
* [StacksProject 07BM](https://stacks.math.columbia.edu/tag/07BM)
* [StacksProject 07BL](https://stacks.math.columbia.edu/tag/07BL)
* [StacksProject 00RU](https://stacks.math.columbia.edu/tag/00RU)
* [StacksProject 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public section

universe u v

/-- **The naive cotangent complex** (Stacks 07BN): for a ring map `R → S`, the two-term chain
complex of `S`-modules
```
NL_{S/R} = (I/I² ⟶ Ω_{R[S]/R} ⊗_{R[S]} S)
```
where `I` is the kernel of the canonical surjection `R[S] → S`, `[s] ↦ s`, with `I/I²` in
homological degree `1`, `Ω_{R[S]/R} ⊗_{R[S]} S` in homological degree `0`, and the canonical
map of Stacks 07BM, sending the class of `f ∈ I` to `df ⊗ 1`, as its differential. It is zero
in all other degrees. Its degree-`0` homology is `Ω_{S/R}` and its degree-`1` homology is
`H₁(L_{S/R}) = Algebra.H1Cotangent R S`. -/
@[stacks 07BN "The complex itself; Mathlib has its differential
(`Algebra.Extension.cotangentComplex` at `Algebra.Generators.self R S`) and its degree-`1`
homology (`Algebra.H1Cotangent`), but not the two-term complex. See the module docstring.",
  sga "6 VIII 2.1" "affine case, R[S]"]
public noncomputable def Algebra.naiveCotangentComplex (R : Type u) (S : Type v) [CommRing R]
    [CommRing S] [Algebra R S] : ChainComplex (ModuleCat.{max u v} S) ℕ :=
  HomologicalComplex.double
    (ModuleCat.ofHom (Algebra.Generators.self R S).toExtension.cotangentComplex)
    (show (ComplexShape.down ℕ).Rel 1 0 from rfl)

namespace NaiveCotangent

/-! ## Generic two-term complexes -/

-- `X₁` and `X₀` are independent module types, so their universes stay separate in this
-- bundled structure (works around the checkUnivs linter).
/-- A two-term chain complex of `S`-modules `X₁ --d--> X₀`, with `X₁` in homological
degree `1` and `X₀` in homological degree `0`. -/
structure TwoTerm (S : Type*) [CommRing S] where
  /-- The module in homological degree `1`. -/
  X₁ : Type*
  /-- The module in homological degree `0`. -/
  X₀ : Type*
  [inst₁ : AddCommGroup X₁]
  [inst₀ : AddCommGroup X₀]
  [mod₁ : Module S X₁]
  [mod₀ : Module S X₀]
  /-- The differential from degree `1` to degree `0`. -/
  d : X₁ →ₗ[S] X₀

attribute [instance] TwoTerm.inst₁ TwoTerm.inst₀ TwoTerm.mod₁ TwoTerm.mod₀

/-- The two degrees `-1` and `0`, in which a two-term complex sits when it is read as a
cochain complex over `ComplexShape.up ℤ`, are distinct. -/
theorem TwoTerm.negOne_ne_zero : (-1 : ℤ) ≠ 0 := by decide

/-- A chain map of two-term complexes: a pair `(f₁, f₀)` of module maps with
`d_B ∘ f₁ = f₀ ∘ d_A`. -/
structure ChainMap {S : Type*} [CommRing S] (A B : TwoTerm S) where
  /-- The component of the chain map in degree `1`. -/
  f₁ : A.X₁ →ₗ[S] B.X₁
  /-- The component of the chain map in degree `0`. -/
  f₀ : A.X₀ →ₗ[S] B.X₀
  comm : B.d ∘ₗ f₁ = f₀ ∘ₗ A.d

variable {S : Type*} [CommRing S]

/-- The identity chain map. -/
def ChainMap.id (A : TwoTerm S) : ChainMap A A where
  f₁ := LinearMap.id
  f₀ := LinearMap.id
  comm := by
    ext x
    simp

/-- Composition of chain maps. -/
def ChainMap.comp {A B C : TwoTerm S} (g : ChainMap B C) (f : ChainMap A B) : ChainMap A C where
  f₁ := g.f₁ ∘ₗ f.f₁
  f₀ := g.f₀ ∘ₗ f.f₀
  comm := by
    ext x
    have h1 := congrArg (fun m => m (f.f₁ x)) g.comm
    have h2 := congrArg (fun m => m x) f.comm
    simp only [LinearMap.coe_comp, Function.comp_apply] at h1 h2 ⊢
    rw [h1, h2]

/-- The degree-`1` component of the identity chain map is the identity. -/
@[simp] lemma ChainMap.id_f₁ (A : TwoTerm S) : (ChainMap.id A).f₁ = LinearMap.id := rfl

/-- The degree-`0` component of the identity chain map is the identity. -/
@[simp] lemma ChainMap.id_f₀ (A : TwoTerm S) : (ChainMap.id A).f₀ = LinearMap.id := rfl

/-- The degree-`1` component of a composite is the composite of the degree-`1` components. -/
@[simp] lemma ChainMap.comp_f₁ {A B C : TwoTerm S} (g : ChainMap B C) (f : ChainMap A B) :
    (g.comp f).f₁ = g.f₁ ∘ₗ f.f₁ := rfl

/-- The degree-`0` component of a composite is the composite of the degree-`0` components. -/
@[simp] lemma ChainMap.comp_f₀ {A B C : TwoTerm S} (g : ChainMap B C) (f : ChainMap A B) :
    (g.comp f).f₀ = g.f₀ ∘ₗ f.f₀ := rfl

/-- Two chain maps `(f₁, f₀)` and `(g₁, g₀)` between the same two-term complexes are
*homotopic* if there is `h : A.X₀ → B.X₁` with `f₁ - g₁ = h ∘ d_A` and
`f₀ - g₀ = d_B ∘ h`. -/
def Homotopic {A B : TwoTerm S} (f g : ChainMap A B) : Prop :=
  ∃ h : A.X₀ →ₗ[S] B.X₁, f.f₁ - g.f₁ = h ∘ₗ A.d ∧ f.f₀ - g.f₀ = B.d ∘ₗ h

/-- A chain map is a *homotopy equivalence* if it has an inverse up to homotopy. -/
@[ega "III 6.1.4" "special case"]
def IsHomotopyEquiv {A B : TwoTerm S} (f : ChainMap A B) : Prop :=
  ∃ g : ChainMap B A, Homotopic (g.comp f) (ChainMap.id A) ∧ Homotopic (f.comp g) (ChainMap.id B)

/-- Degree-`1` homology of a two-term complex: `H₁ = ker d`. -/
@[ega "III 7.6.11"]
def H₁ (A : TwoTerm S) : Submodule S A.X₁ :=
  LinearMap.ker A.d

/-- Map induced on `H₁ = ker d` by a chain map. -/
def ChainMap.onH₁ {A B : TwoTerm S} (f : ChainMap A B) : H₁ A →ₗ[S] H₁ B :=
  f.f₁.restrict
    (fun x hx => by
      have hcomm : B.d (f.f₁ x) = f.f₀ (A.d x) := by
        simpa using congrArg (fun m => m x) f.comm
      simp only [H₁, LinearMap.mem_ker] at hx ⊢
      rw [hcomm, hx, map_zero])

/-- Degree-`0` homology of a two-term complex: `H₀ = coker d`. -/
abbrev H₀ (A : TwoTerm S) := A.X₀ ⧸ LinearMap.range A.d

/-- Map induced on `H₀ = coker d` by a chain map. -/
def ChainMap.onH₀ {A B : TwoTerm S} (f : ChainMap A B) : H₀ A →ₗ[S] H₀ B :=
  Submodule.mapQ _ _ f.f₀
    (by
      rintro y ⟨x, rfl⟩
      simp only [Submodule.mem_comap, LinearMap.mem_range]
      refine ⟨f.f₁ x, ?_⟩
      simpa using congrArg (fun m => m x) f.comm)

/-- A chain map of two-term complexes is a *quasi-isomorphism* if it induces
isomorphisms on both `H₁ = ker d` and `H₀ = coker d`. -/
def IsQuasiIso {A B : TwoTerm S} (f : ChainMap A B) : Prop :=
  Function.Bijective f.onH₁ ∧ Function.Bijective f.onH₀

/-! ## The naive cotangent complex via `Algebra.Generators` -/

open Algebra

/-- The naive cotangent complex `NL(P) : I/I² ⟶ Ω[P/R] ⊗[P] S` of an extension `P → S` of an
`R`-algebra `S` with kernel `I`, as a two-term complex of `S`-modules: Mathlib's
`Algebra.Extension.Cotangent`, `Algebra.Extension.CotangentSpace` and
`Algebra.Extension.cotangentComplex` packaged as a `TwoTerm`. -/
noncomputable def nlOfExtension {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension R S) : TwoTerm S where
  X₁ := P.Cotangent
  X₀ := P.CotangentSpace
  d := P.cotangentComplex

/-- `NL(α)` of a presentation `P` (`= Generators R S ι`), viewed as a two-term complex
of `S`-modules.  Concretely this is `NL(α) : I/I² → Ω_{P/R} ⊗_P S`, with `I/I²` in
homological degree `1` and `Ω_{P/R} ⊗_P S` in homological degree `0`, and differential
`d_α = cotangentComplex`.  It is `nlOfExtension` at the extension the presentation
presents. -/
@[ega "0 20.6.26", sga "6 0 4.4" "special case"]
noncomputable def NL {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Generators R S ι) : TwoTerm S :=
  nlOfExtension P.toExtension

/-- The target complex `NL(α')` of a presentation `P' : Generators R' S' ι'`, viewed as a
two-term complex of `S`-modules along `φ : S → S'` (where `S` acts on `Cotangent` and
`CotangentSpace` through `algebraMap S S'`).  The underlying objects and differential
agree with `NL P'`, only the scalars are restricted from `S'` to `S`. -/
noncomputable abbrev nlRestrict {R' S' ι' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
    (S : Type*) [CommRing S] [Algebra S S'] (P' : Generators R' S' ι') : TwoTerm S
    where
  X₁ := P'.toExtension.Cotangent
  X₀ := P'.toExtension.CotangentSpace
  d := P'.toExtension.cotangentComplex.restrictScalars S

variable {R ι : Type*} [CommRing R] [Algebra R S]
variable {R' S' ι' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
variable [Algebra R R'] [Algebra S S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S']

/-- The chain map `NL(varphi) : NL(α) → NL(α')` induced by a morphism of presentations
`varphi : P → P'` covering the commutative square, with both complexes viewed over a
common base ring `Sb` (mapping compatibly into `S` and `S'`).  The maps on cotangent
data are `S'`-linear; we restrict scalars to `Sb`.  The principal case is `Sb = S` (the
source ring), in which case the target `NL(α')` is viewed over `S` via `φ : S → S'`. -/
noncomputable def nlMapBase (Sb : Type*) [CommRing Sb] [Algebra Sb S] [Algebra Sb S']
    [IsScalarTower Sb S S'] (P : Generators R S ι) (P' : Generators R' S' ι') (φ : P.Hom P') :
    ChainMap (nlRestrict Sb P) (nlRestrict Sb P')
    where
  f₁ := (Extension.Cotangent.map φ.toExtensionHom).restrictScalars Sb
  f₀ := (Extension.CotangentSpace.map φ.toExtensionHom).restrictScalars Sb
  comm := by
    ext x
    have h := Extension.CotangentSpace.map_cotangentComplex φ.toExtensionHom x
    simp only [nlRestrict]
    exact h.symm

/-- The degree-`1` component of `nlMapBase` is the induced map on `Cotangent`. -/
@[simp] lemma nlMapBase_f₁ (Sb : Type*) [CommRing Sb] [Algebra Sb S] [Algebra Sb S']
    [IsScalarTower Sb S S'] (P : Generators R S ι) (P' : Generators R' S' ι') (φ : P.Hom P') :
    (nlMapBase Sb P P' φ).f₁ = (Extension.Cotangent.map φ.toExtensionHom).restrictScalars Sb :=
  rfl

/-- The degree-`0` component of `nlMapBase` is the induced map on `CotangentSpace`. -/
@[simp] lemma nlMapBase_f₀ (Sb : Type*) [CommRing Sb] [Algebra Sb S] [Algebra Sb S']
    [IsScalarTower Sb S S'] (P : Generators R S ι) (P' : Generators R' S' ι') (φ : P.Hom P') :
    (nlMapBase Sb P P' φ).f₀ =
      (Extension.CotangentSpace.map φ.toExtensionHom).restrictScalars Sb :=
  rfl

/-- The chain map `NL(varphi) : NL(α) → NL(α')` induced by a morphism of presentations
`varphi : P → P'` covering the commutative square, viewed over the source ring `S`.  The
target complex `NL(α')` is viewed over `S` via `φ : S → S'`.  This is `nlMapBase`
specialized to base `Sb = S`. -/
noncomputable def nlMap (P : Generators R S ι) (P' : Generators R' S' ι') (φ : P.Hom P') :
    ChainMap (nlRestrict S P) (nlRestrict S P') :=
  nlMapBase S P P' φ

/-! ## The canonical presentation and `NL_{S/R}` -/

/-- The canonical presentation `α_can : R[S] → S`, `[s] ↦ s`. -/
noncomputable abbrev canonicalGenerators (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Generators R S S :=
  Generators.self R S

/-! ## Functoriality over a base ring -/

/-- A `ChainMap` is determined by its two component maps `f₁` and `f₀`. -/
@[ext]
lemma ChainMap.ext {A B : TwoTerm S} {p q : ChainMap A B} (h1 : p.f₁ = q.f₁) (h0 : p.f₀ = q.f₀) :
    p = q := by
  cases p; cases q; congr

/-- Compatibility of `nlMapBase` with composition of morphisms of presentations, over an
arbitrary base ring `Sb`. -/
theorem nlMapBase_comp (Sb : Type*) [CommRing Sb] [Algebra Sb S] [Algebra Sb S']
    [IsScalarTower Sb S S'] {R'' S'' ι'' : Type*} [CommRing R''] [CommRing S''] [Algebra R'' S'']
    [Algebra R' R''] [Algebra R' S''] [Algebra S' S''] [Algebra S S''] [Algebra Sb S'']
    [IsScalarTower Sb S' S''] [IsScalarTower Sb S S''] [IsScalarTower R' R'' S'']
    [IsScalarTower R' S' S''] [IsScalarTower S S' S''] [Algebra R R''] [Algebra R S'']
    [IsScalarTower R R' R''] [IsScalarTower R R'' S''] [IsScalarTower R S S'']
    (P : Generators R S ι) (P' : Generators R' S' ι') (P'' : Generators R'' S'' ι'') (φ : P.Hom P')
    (φ' : P'.Hom P'') :
    (nlMapBase Sb P' P'' φ').comp (nlMapBase Sb P P' φ) = nlMapBase Sb P P'' (φ'.comp φ) := by
  have hcomp : (φ'.comp φ).toExtensionHom = φ'.toExtensionHom.comp φ.toExtensionHom :=
    Generators.Hom.toExtensionHom_comp P P' P'' φ' φ
  refine ChainMap.ext ?_ ?_ <;> ext x
  · simp [hcomp, Extension.Cotangent.map_comp]
  · simp [hcomp, Extension.CotangentSpace.map_comp]

/-- Any two morphisms of presentations `P → P'` induce homotopic chain maps `nlMapBase`, over
an arbitrary base ring `Sb`. -/
theorem nlMapBase_homotopic (Sb : Type*) [CommRing Sb] [Algebra Sb S] [Algebra Sb S']
    [IsScalarTower Sb S S'] (P : Generators R S ι) (P' : Generators R' S' ι') (φ φ' : P.Hom P') :
    Homotopic (nlMapBase Sb P P' φ) (nlMapBase Sb P P' φ') := by
  refine ⟨(Extension.Hom.sub φ.toExtensionHom φ'.toExtensionHom).restrictScalars Sb, ?_, ?_⟩
  · have h := Extension.Cotangent.map_sub_map φ.toExtensionHom φ'.toExtensionHom
    exact LinearMap.ext fun x => by simpa [nlMapBase, nlRestrict] using LinearMap.congr_fun h x
  · have h := Extension.CotangentSpace.map_sub_map φ.toExtensionHom φ'.toExtensionHom
    exact LinearMap.ext fun x => by simpa [nlMapBase, nlRestrict] using LinearMap.congr_fun h x

/-- The identity morphism of presentations induces the identity chain map. -/
theorem nlMapBase_id (Sb : Type*) [CommRing Sb] [Algebra Sb S] (P : Generators R S ι) :
    nlMapBase Sb P P (Generators.Hom.id P) = ChainMap.id (nlRestrict Sb P) := by
  apply ChainMap.ext
  · rw [nlMapBase_f₁, ChainMap.id_f₁, Generators.Hom.toExtensionHom_id,
      Extension.Cotangent.map_id]
    rfl
  · rw [nlMapBase_f₀, ChainMap.id_f₀, Generators.Hom.toExtensionHom_id,
      Extension.CotangentSpace.map_id]
    rfl

/-! ## Main statements -/

omit [Algebra R R'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] in
/-- **Existence.** There exists a morphism of presentations `varphi` from `α` to `α'`
covering the square. -/
@[stacks 00S1 "(1)"]
theorem exists_hom (P : Generators R S ι) (P' : Generators R' S' ι') : Nonempty (P.Hom P') :=
  ⟨P.defaultHom P'⟩

/-- **Homotopy uniqueness.** Any two morphisms of presentations `varphi, varphi'` from `α` to
`α'` induce homotopic chain maps `NL(varphi), NL(varphi')` (over the source base `S`). The
homotopy is the `S`-linear map `h : Ω_{P/R} ⊗_P S → I'/(I')²`
(`= P.CotangentSpace →ₗ[S] P'.Cotangent`) given by `Algebra.Extension.Hom.sub` of the two
extension homs; the two homotopy relations are `Cotangent.map_sub_map` and
`CotangentSpace.map_sub_map`. -/
@[stacks 00S1 "(2)"]
theorem nlMap_homotopic (P : Generators R S ι) (P' : Generators R' S' ι') (φ φ' : P.Hom P') :
    Homotopic (nlMap P P' φ) (nlMap P P' φ') :=
  nlMapBase_homotopic S P P' φ φ'

/-- **Compatibility with composition.** Given a commutative diagram of two squares and
compatible morphisms of presentations `varphi : P → P'`, `varphi' : P' → P''`, the composite
`varphi' ∘ varphi` is a morphism of presentations from `α` to `α''` and, viewing everything
over the base ring `S`, `NL(varphi') ∘ NL(varphi) = NL(varphi' ∘ varphi)`. -/
@[stacks 00S1 "(3)"]
theorem nlMapBase_comp_nlMapBase {R'' S'' ι'' : Type*} [CommRing R''] [CommRing S'']
    [Algebra R'' S''] [Algebra R' R''] [Algebra R' S''] [Algebra S' S''] [Algebra S S'']
    [IsScalarTower R' R'' S''] [IsScalarTower R' S' S''] [IsScalarTower S S' S''] [Algebra R R'']
    [Algebra R S''] [IsScalarTower R R' R''] [IsScalarTower R R'' S''] [IsScalarTower R S S'']
    (P : Generators R S ι) (P' : Generators R' S' ι') (P'' : Generators R'' S'' ι'') (φ : P.Hom P')
    (φ' : P'.Hom P'') :
    (nlMapBase S P' P'' φ').comp (nlMapBase S P P' φ) = nlMapBase S P P'' (φ'.comp φ) :=
  nlMapBase_comp S P P' P'' φ φ'

/-- Functoriality of `onH₁` with respect to composition. -/
@[simp]
lemma ChainMap.onH₁_comp {A B C : TwoTerm S} (g : ChainMap B C) (f : ChainMap A B) :
    (g.comp f).onH₁ = g.onH₁ ∘ₗ f.onH₁ := by
  ext x
  rfl

/-- `onH₁` sends the identity chain map to the identity. -/
@[simp]
lemma ChainMap.onH₁_id (A : TwoTerm S) : (ChainMap.id A).onH₁ = LinearMap.id := by
  ext x
  rfl

/-- Functoriality of `onH₀` with respect to composition. -/
@[simp]
lemma ChainMap.onH₀_comp {A B C : TwoTerm S} (g : ChainMap B C) (f : ChainMap A B) :
    (g.comp f).onH₀ = g.onH₀ ∘ₗ f.onH₀ := by
  ext x
  rfl

/-- `onH₀` sends the identity chain map to the identity. -/
@[simp]
lemma ChainMap.onH₀_id (A : TwoTerm S) : (ChainMap.id A).onH₀ = LinearMap.id := by
  ext x
  rfl

/-- Homotopic chain maps induce the same map on `H₁ = ker d`. -/
lemma ChainMap.onH₁_eq_of_homotopic {A B : TwoTerm S} {p q : ChainMap A B} (hpq : Homotopic p q) :
    p.onH₁ = q.onH₁ := by
  obtain ⟨h, h1, h0⟩ := hpq
  ext x
  have hx : A.d (x : A.X₁) = 0 := x.property
  have key : (p.f₁ - q.f₁) (x : A.X₁) = (h ∘ₗ A.d) (x : A.X₁) := by rw [h1]
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, hx, map_zero] at key
  simpa [ChainMap.onH₁] using sub_eq_zero.mp key

/-- Homotopic chain maps induce the same map on `H₀ = coker d`. -/
lemma ChainMap.onH₀_eq_of_homotopic {A B : TwoTerm S} {p q : ChainMap A B} (hpq : Homotopic p q) :
    p.onH₀ = q.onH₀ := by
  obtain ⟨h, h1, h0⟩ := hpq
  ext x
  refine (Submodule.Quotient.eq _).mpr ?_
  have key : (p.f₀ - q.f₀) x = (B.d ∘ₗ h) x := by rw [h0]
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at key
  rw [key]
  exact ⟨h x, rfl⟩

/-- A linear map with a two-sided linear inverse is bijective. -/
private theorem bijective_of_comp_eq_id {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] {f : M →ₗ[S] N} {g : N →ₗ[S] M} (h₁ : g ∘ₗ f = LinearMap.id)
    (h₂ : f ∘ₗ g = LinearMap.id) : Function.Bijective f :=
  ⟨Function.LeftInverse.injective (g := g) (LinearMap.congr_fun h₁),
    Function.RightInverse.surjective (g := g) (LinearMap.congr_fun h₂)⟩

/-- A homotopy equivalence of two-term complexes is a quasi-isomorphism: homotopic chain maps
agree on `H₁` and `H₀`, so the homotopy inverse gives two-sided inverses on homology. -/
@[ega "III 6.1.4" "special case"]
lemma isQuasiIso_of_isHomotopyEquiv {A B : TwoTerm S} {f : ChainMap A B} (hf : IsHomotopyEquiv f) :
    IsQuasiIso f := by
  obtain ⟨g, hgf, hfg⟩ := hf
  exact ⟨bijective_of_comp_eq_id
      (by rw [← ChainMap.onH₁_comp, ChainMap.onH₁_eq_of_homotopic hgf, ChainMap.onH₁_id])
      (by rw [← ChainMap.onH₁_comp, ChainMap.onH₁_eq_of_homotopic hfg, ChainMap.onH₁_id]),
    bijective_of_comp_eq_id
      (by rw [← ChainMap.onH₀_comp, ChainMap.onH₀_eq_of_homotopic hgf, ChainMap.onH₀_id])
      (by rw [← ChainMap.onH₀_comp, ChainMap.onH₀_eq_of_homotopic hfg, ChainMap.onH₀_id])⟩

/-- **Isomorphism case.** If `R → R'` and `φ : S → S'` are isomorphisms, then for any morphism
of presentations `varphi` from `α` to `α'` the induced chain map `NL(varphi)` (over `S`) is
both a homotopy equivalence and a quasi-isomorphism. -/
@[stacks 00S1 "(4)"]
theorem nlMap_isHomotopyEquiv_and_isQuasiIso (hR : Function.Bijective (algebraMap R R'))
    (hS : Function.Bijective (algebraMap S S')) (P : Generators R S ι) (P' : Generators R' S' ι')
    (φ : P.Hom P') : IsHomotopyEquiv (nlMap P P' φ) ∧ IsQuasiIso (nlMap P P' φ) := by
  suffices h : IsHomotopyEquiv (nlMap P P' φ) from ⟨h, isQuasiIso_of_isHomotopyEquiv h⟩
  let eR : R ≃+* R' := RingEquiv.ofBijective (algebraMap R R') hR
  let eS : S ≃+* S' := RingEquiv.ofBijective (algebraMap S S') hS
  let : Algebra R' R := (eR.symm.toRingHom).toAlgebra
  let : Algebra S' S := (eS.symm.toRingHom).toAlgebra
  let : Algebra R' S := ((algebraMap R S).comp eR.symm.toRingHom).toAlgebra
  let : IsScalarTower R' R S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R' S' S := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    have heS : (eS : S → S') = ⇑(algebraMap S S') := rfl
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.coe_toRingHom]
    rw [eq_comm, RingEquiv.symm_apply_eq, heS, ← IsScalarTower.algebraMap_apply R S S',
      IsScalarTower.algebraMap_apply R R' S']
    congr 1
    exact (eR.apply_symm_apply x).symm
  let : IsScalarTower S S' S :=
    IsScalarTower.of_algebraMap_eq (fun x => (eS.symm_apply_apply x).symm)
  let : IsScalarTower R R' R :=
    IsScalarTower.of_algebraMap_eq (fun x => (eR.symm_apply_apply x).symm)
  let : IsScalarTower S' S S' :=
    IsScalarTower.of_algebraMap_eq (fun x => (eS.apply_symm_apply x).symm)
  let : IsScalarTower R' R R' :=
    IsScalarTower.of_algebraMap_eq (fun x => (eR.apply_symm_apply x).symm)
  let ψ : P'.Hom P := P'.defaultHom P
  have h₁ : (nlMapBase S P' P ψ).comp (nlMap P P' φ) = nlMapBase S P P (ψ.comp φ) :=
    nlMapBase_comp S P P' P φ ψ
  have h₂ : (nlMap P P' φ).comp (nlMapBase S P' P ψ) = nlMapBase S P' P' (φ.comp ψ) :=
    nlMapBase_comp S P' P P' ψ φ
  refine ⟨nlMapBase S P' P ψ, ?_, ?_⟩
  · rw [h₁, ← nlMapBase_id S P]
    exact nlMapBase_homotopic S P P (ψ.comp φ) (Generators.Hom.id P)
  · rw [h₂, ← nlMapBase_id S P']
    exact nlMapBase_homotopic S P' P' (φ.comp ψ) (Generators.Hom.id P')

/-- **Comparison with the canonical complex.** Any morphism of presentations `varphi` from a
presentation `α` of `S/R` to the canonical presentation `α_can : R[S] → S` induces a
quasi-isomorphism `NL(α) → NL_{S/R}`. -/
@[stacks 00S1]
theorem nlMap_canonical_isQuasiIso (P : Generators R S ι) (φ : P.Hom (canonicalGenerators R S)) :
    IsQuasiIso (nlMap P (canonicalGenerators R S) φ) :=
  (nlMap_isHomotopyEquiv_and_isQuasiIso (R' := R) (S' := S)
      Function.bijective_id Function.bijective_id
      P (canonicalGenerators R S) φ).right

end NaiveCotangent

/-! ## The differential of the naive cotangent complex (Stacks 07BM) -/

add_to_stacks 07BM "the naive cotangent differential" Algebra.Extension.cotangentComplex
add_to_sga "1 II 5.9" "more general" Algebra.Extension.cotangentComplex
add_to_sga "6 0 4.4" "special case" Algebra.Extension.cotangentComplex
add_to_ega "IV 17.15.9" Algebra.Extension.cotangentComplex
add_to_sga "6 VIII 2.1" "affine case" Algebra.Extension.cotangentComplex
