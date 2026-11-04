module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartCocycleMatch
public import StacksFrontier.AlgebraicGeometry.ProjF1DegreeOneChart.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Proj` of a graded ring generated in degree one

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring which is generated as an `𝒜 0`-algebra by `𝒜 1`, and
let `X = Proj A`. Stacks Tag 01NA classifies the morphisms of a scheme `Y` into `X` by the pairs
`(L, ψ)` with `L` an invertible `𝒪_Y`-module and `ψ : A ⟶ Γ_*(Y, L)` a graded ring map whose
degree-one part generates `L`: the source's proof is the one sentence *"we have `X = U_1` and
the lemma is a reformulation of Lemma 27.12.2"*.

This file supplies both halves of that sentence over the whole of `Proj A`.

* `X = U_1`: the standard opens of the degree-one elements cover `Proj A`, so the open
  `U_1 = ⋃_{f ∈ 𝒜 1} D₊(f)` of Equation 27.12.0.1 is all of `X`. Consequently the universal
  family lives on `X` itself: `𝒪_X(1)` is an invertible `𝒪_X`-module and the global sections
  attached to the degree-one elements generate it.
* the universal property: for a pair `(L, ψ)` as above there is one and only one pair
  `(φ, α)` consisting of a morphism `φ : Y ⟶ X` and an isomorphism `α : φ⁎𝒪_X(1) ≅ L ^⊗ 1`
  compatible with `ψ`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.pullbackTwistOne` — `φ⁎𝒪_X(1)` for a
  morphism `φ : Y ⟶ Proj A`.
* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.pullbackSectionOne` — the pullback along `φ`
  of the global section of `𝒪_X(1)` attached to a degree-one element.
* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.Pair` — a pair `(φ, α)` with `φ` a morphism
  into the whole of `Proj A`.
* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.Classifies` — the three clauses saying that
  `(φ, α)` classifies the pair `(L, ψ)`: the preimage of each `D₊(f)` is the nonvanishing open
  `Y_{ψ(f)}`, the isomorphism carries the pulled-back degree-one section of `f` to `ψ(f)`, and
  the ring map induced by `φ` on `D₊(f)` is the dehomogenization `ψ_{(f)}` of `ψ`.
* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.factorThroughDegreeOpenOne` — a morphism
  into `Proj A` read as a morphism into `U_1`, when `U_1` is everything.

## Main results

* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.degreeOpen_one_eq_top` — **`X = U_1`**, the
  input the source's proof of Tag 01NA names;
  `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.degreeOpen_eq_top` — **`X = U_d`** in every
  positive degree; and
  `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.whereInvertible_eq_top` — **`X = W_d`**, so
  the `d`-divisible twists are invertible on all of `Proj A`.
* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen`
  — **`X_f = D₊(f)`** with no hypothesis on the point, for `f` homogeneous of degree `nd`.
* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.isInvertibleModule_twistingSheafOne` and
  `iSup_nonvanishingOpen_degreeSection_eq_top` — **the universal family of Tag 01NA on `X`**:
  `𝒪_X(1)` is invertible on all of `Proj A`, and the global sections attached to the degree-one
  elements generate it, their nonvanishing opens covering `X`.
* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.exists_classifies` — existence of the
  classifying pair.
* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.hom_eq_of_classifies` and
  `iso_eq_of_classifies` — the two uniqueness clauses.
* `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.existsUnique_classifies` — **the universal
  property of `Proj A` of Tag 01NA**: one and only one classifying pair.

## Implementation notes

**The graded map `ψ` is taken in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`**, which at `d = 1` is a family
of additive maps `𝒜 n ⟶ Γ(Y, L ^⊗ n)`, one for each `n`, multiplicative across degrees. This is
the graded ring map `A = A^{(1)} ⟶ Γ_*(Y, L)` of the source written out componentwise, with the
unit axiom `ψ(1) = 1` not required; since `ψ` is a hypothesis of every statement below,
dropping that axiom strengthens them. It is also the spelling the existence half of
[Stacks, Tag 01N8] is stated in, so no bridge is introduced.

**Where the compatibility between `φ` and `ψ` lives.** The source states it as the commuting
square `α ∘ ψ^1_φ = ψ` of graded ring maps. The graded ring map `ψ^1_φ` into `Γ_*(Y, φ⁎𝒪_X(1))`
is *not* available: `Stacks.AlgebraicGeometry.MorphismsIntoProj.psiPullbackVeroneseHom` has
`Γ(Y, φ⁎𝒪_X(n))` as its degree-`n` target rather than `Γ(Y, (φ⁎𝒪_X(1)) ^⊗ n)`, and the graded
ring isomorphism identifying the two is the open problem recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjDegreeOpenSections.lean` — a coherent family of
module isomorphisms `𝒪_{U_d}(d) ^⊗ n ≅ 𝒪_{U_d}(nd)` exists
(`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta`) but its multiplicativity is
known only in bidegree `(n, 1)`. So `Classifies` states the square in the equivalent form the
source's own proof establishes and uses: clause `app_pullbackSectionOne` is the square in degree
one, and clause `appLE_awayToSection` is the square in all degrees after dividing by the
trivializing section — it says that the ring map `Γ(X, D₊(f)) ⟶ Γ(Y, Y_{ψ(f)})` induced by `φ`
is the dehomogenization `ψ_{(f)} : A_{(f)} ⟶ Γ(Y, Y_{ψ(f)})`, `a/f^n ↦ ψ(a)/ψ(f)^n`, which is
how the source defines `φ` in the first place.

**`α` lands in `L ^⊗ 1`, not in `L`.** The two differ by the left unitor, and the sections
`ψ(f)` are by construction sections of `L ^⊗ 1`; carrying the unitor through every statement
would add a transport that says nothing. This is the convention of the whole `Proj` chart
development, see `StacksFrontier/AlgebraicGeometry/Constructions/ProjChartAlphaInstance.lean`.

**Where the degree-one generation hypothesis is used.** Only to put the universal family on `X`
and to turn a morphism into `X` into a morphism into `U_1`; the existence of the classifying
pair needs no hypothesis on `A`, because clause `preimage_basicOpen` forces `φ` to factor
through `U_1` whatever `A` is. That is exactly the division of labour in the source, where Tag
01NA adds `X = U_1` to Tag 01N9 and nothing else.

## References

* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Equation 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01N6](https://stacks.math.columbia.edu/tag/01N6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjDegreeOneRepresents

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### `X = U_1` -/

/-- **`X = U_1`.** When `A` is generated as an `𝒜 0`-algebra by its degree-one part, the open
`U_1 = ⋃_{f ∈ 𝒜 1} D₊(f)` of Equation 27.12.0.1 is all of `Proj A`. This is the one input the
source's proof of [Stacks, Tag 01NA] names, and it is
`Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top` read through the
definition of `U_1`. -/
@[stacks 01NA "X = U₁"]
theorem degreeOpen_one_eq_top (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) :
    degreeOpen 𝒜 1 = ⊤ :=
  Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top 𝒜 hgen

/-- **`X = U_d` in every positive degree**, for `A` generated as an `𝒜 0`-algebra by its
degree-one part. The degree-one case is `degreeOpen_one_eq_top`, and `U_1 ⊆ U_d` for `0 < d`
because `D₊(f) = D₊(f ^ d)` with `f ^ d` of degree `d`
(`AlgebraicGeometry.Proj.degreeOpen_le_of_dvd`).

The twisting sheaves of a common degree `d` and their tensor-power comparison are constructed on
`U_d`, so this is what makes them global in the setting of [Stacks, Tag 03GM], where `A` is a
polynomial ring over its degree-zero part. -/
theorem degreeOpen_eq_top (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) {d : ℕ}
    (hd : 0 < d) : degreeOpen 𝒜 d = ⊤ :=
  top_unique ((degreeOpen_one_eq_top 𝒜 hgen).ge.trans
    (AlgebraicGeometry.Proj.degreeOpen_le_of_dvd 𝒜 (one_dvd d) hd))

/-- **`W_d = X` in every positive degree**, for `A` generated as an `𝒜 0`-algebra by its
degree-one part: the `d`-divisible twists are invertible everywhere and every multiplication map
between them is an isomorphism, because `U_d ⊆ W_d` and `U_d` is all of `Proj A`. -/
@[ega "II 8.14.4" "special case"]
theorem whereInvertible_eq_top (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) {d : ℕ}
    (hd : 0 < d) : ProjInvertibleLocus.whereInvertible 𝒜 d = ⊤ :=
  top_unique ((degreeOpen_eq_top 𝒜 hgen hd).ge.trans (degreeOpen_le_whereInvertible 𝒜 d))

/-- **Stacks Tag 01MV with no hypothesis on the point**, for `A` generated in degree one: the
nonvanishing locus of the global section of `𝒪(nd)` attached to a homogeneous `f` of degree `nd`
is exactly the standard open `D₊(f)`.

Tag 01MV is stated on the invertible locus `W_d`, which `whereInvertible_eq_top` makes all of
`Proj A` here; this is the form `X_f = D₊(f)` in which the sheaf-of-modules theory of
[Stacks, Tag 01PW] consumes a homogeneous element as a global section of an invertible
module. -/
@[ega "II 2.6.3" "Case n = 1", ega "II 3.3.3" "affine base Y = Spec A"]
theorem nonvanishingLocus_degreeSection_eq_basicOpen
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) {d : ℕ} (hd : 0 < d) (n : ℕ)
    (f : 𝒜 (n * d)) :
    Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒜)
        (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ)) (degreeSection 𝒜 (n * d) f) =
      (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) : Set (AlgebraicGeometry.Proj 𝒜)) := by
  ext x
  exact Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    𝒜 d n f ((whereInvertible_eq_top 𝒜 hgen hd).ge (TopologicalSpace.Opens.mem_top x))

variable {Y : Scheme.{u}}

/-- **A morphism into `Proj A` read as a morphism into `U_1`**, available as soon as `U_1` is all
of `Proj A`. The factorization is through the open immersion `U_1 ⟶ Proj A`. -/
def factorThroughDegreeOpenOne (htop : degreeOpen 𝒜 1 = ⊤) (φ : Y ⟶ Proj 𝒜) :
    Y ⟶ (degreeOpen 𝒜 1).toScheme :=
  ProjF1DegreeOneChart.opensHomEquiv (degreeOpen 𝒜 1) ⟨φ, by rw [htop]; simp⟩

/-- The factorization of `factorThroughDegreeOpenOne` really is one. -/
theorem toProj_factorThroughDegreeOpenOne (htop : degreeOpen 𝒜 1 = ⊤) (φ : Y ⟶ Proj 𝒜) :
    toProj 𝒜 (factorThroughDegreeOpenOne 𝒜 htop φ) = φ :=
  congrArg Subtype.val
    ((ProjF1DegreeOneChart.opensHomEquiv (X := Y) (degreeOpen 𝒜 1)).symm_apply_apply
      ⟨φ, by rw [htop]; simp⟩)

/-- Every morphism into `Proj A` factors through `U_1`, when `U_1` is everything. -/
theorem exists_toProj_eq (htop : degreeOpen 𝒜 1 = ⊤) (φ : Y ⟶ Proj 𝒜) :
    ∃ φ₀ : Y ⟶ (degreeOpen 𝒜 1).toScheme, toProj 𝒜 φ₀ = φ :=
  ⟨factorThroughDegreeOpenOne 𝒜 htop φ, toProj_factorThroughDegreeOpenOne 𝒜 htop φ⟩

/-! ### The universal family on `X` -/

/-- **`𝒪_X(1)` is an invertible `𝒪_X`-module on all of `Proj A`** when `A` is generated in degree
one over `𝒜 0`. Without that hypothesis the twist is invertible only on `U_1`; this is
`Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf`, read in the
`Stacks.Ample.IsInvertibleModule` spelling that triples and their trivializations are stated
in. -/
@[stacks 01NA "the universal family on X: 𝒪_X(1) is invertible",
  ega "II 2.6.1",
  ega "II 3.2.5" "special case"]
theorem isInvertibleModule_twistingSheafOne
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) :
    Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜)
      (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      (AlgebraicGeometry.Proj 𝒜).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf _) _).mp
    (Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf 𝒜 hgen _)

/-- **The universal family of [Stacks, Tag 01NA] generates `𝒪_X(1)` on all of `X`.** The global
section of `𝒪_X(1)` attached to a degree-one element `f` is nonvanishing exactly on `D₊(f)`
([Stacks, Tag 01MV], available because `U_1 ⊆ W_1`), and those opens cover `Proj A` by
`degreeOpen_one_eq_top`. So the degree-one part of `ψ^1` generates `𝒪_X(1)`, which is the second
assertion of [Stacks, Tag 01N9] transported to `X` by `X = U_1`. -/
@[stacks 01NA "the universal family on X: global generation in degree one"]
theorem exists_mem_nonvanishingLocus_degreeSection
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) (x : ProjectiveSpectrum.top 𝒜) :
    ∃ f : 𝒜 1, x ∈ Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒜)
      (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) (degreeSection 𝒜 1 f) := by
  have hx := (degreeOpen_one_eq_top 𝒜 hgen).ge (Opens.mem_top x)
  obtain ⟨f, hf⟩ := Opens.mem_iSup.mp hx
  exact ⟨f, mem_nonvanishingLocus_degreeSection 𝒜 (one_mul 1).symm f
    (degreeOpen_le_whereInvertible 𝒜 1 hx) hf⟩

/-! ### The classifying pairs -/

/-- **`φ⁎𝒪_X(1)`** for a morphism `φ` into the whole of `Proj A`. -/
abbrev pullbackTwistOne (φ : Y ⟶ AlgebraicGeometry.Proj 𝒜) : Y.Modules :=
  (Scheme.Modules.pullback φ).obj (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))

/-- **The pullback along `φ` of the global section of `𝒪_X(1)` attached to a degree-one element.**
For a `φ` factoring through `U_1` this is
`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.pullbackDegreeSection`. -/
def pullbackSectionOne (φ : Y ⟶ AlgebraicGeometry.Proj 𝒜) (f : 𝒜 1) :
    Γ(pullbackTwistOne 𝒜 φ, ⊤) :=
  pullbackSectionHom φ (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) ⊤ ⊤ (by simp) (degreeSection 𝒜 1 f)

variable {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]

/-- **`Y_{ψ(f)}`**, the nonvanishing open of the degree-one section `ψ(f)` of `L ^⊗ 1`. -/
abbrev nvOpen (ψ : VeroneseSections 𝒜 1 L) (f : 𝒜 1) : Y.Opens :=
  nonvanishingOpen Y (natTensorPow L 1) (ψ.pow f.2 1)

/-- **A pair `(φ, α)` as in [Stacks, Tag 01N8], with `φ` a morphism into the whole of
`Proj A`**: a morphism `φ : Y ⟶ Proj A` together with an isomorphism `φ⁎𝒪_X(1) ≅ L ^⊗ 1`.
Bundling the two makes the uniqueness assertion a single equality. -/
abbrev Pair (L : Y.Modules) : Type u :=
  Σ φ : Y ⟶ AlgebraicGeometry.Proj 𝒜, pullbackTwistOne 𝒜 φ ≅ natTensorPow L 1

/-- **The pair `(φ, α)` classifies `(L, ψ)`**, in three clauses.

* `φ ⁻¹ᵁ D₊(f) = Y_{ψ(f)}` for every `f ∈ 𝒜 1` — clause (a) of [Stacks, Tag 01N8]. It forces `φ`
  to factor through `U_1`, since the `Y_{ψ(f)}` cover `Y`.
* `α(φ⁎f) = ψ(f)` for every `f ∈ 𝒜 1` — the commuting square of [Stacks, Tag 01N8] in degree
  one.
* the ring map `Γ(X, D₊(f)) ⟶ Γ(Y, Y_{ψ(f)})` induced by `φ` is the dehomogenization
  `ψ_{(f)} : A_{(f)} ⟶ Γ(Y, Y_{ψ(f)})`, `a/f^n ↦ ψ(a)/ψ(f)^n` — the commuting square in all
  degrees, in the form the source's proof establishes it and in which it determines `φ`. -/
def Classifies (ψ : VeroneseSections 𝒜 1 L) (p : Pair 𝒜 L) : Prop :=
  (∀ f : 𝒜 1, p.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = nvOpen 𝒜 ψ f) ∧
  (∀ f : 𝒜 1, p.2.hom.app ⊤ (pullbackSectionOne 𝒜 p.1 f) = ψ.pow f.2 1) ∧
  (∀ (f : 𝒜 1) (hle : nvOpen 𝒜 ψ f ≤ p.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
      (u : Away 𝒜 (f : A)),
    p.1.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (nvOpen 𝒜 ψ f) hle
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A)).hom u) =
      (ψ.homogeneousRatios f.2 (le_refl (nvOpen 𝒜 ψ f))).lift Nat.one_pos u)

/-! ### Existence -/

/-- **The classifying pair of [Stacks, Tag 01NA] exists.** Given an invertible `𝒪_Y`-module `L`
and a graded map `ψ : A ⟶ Γ_*(Y, L)` whose degree-one sections generate `L`, the charts of `ψ`
glue to a morphism `φ : Y ⟶ U_1 ⊆ Proj A` (`Stacks.AlgebraicGeometry.ProjChartCocycle.glued`)
and the per-chart trivializations glue to an isomorphism `α : φ⁎𝒪_X(1) ≅ L ^⊗ 1`
(`Stacks.AlgebraicGeometry.ProjChartCocycleMatch.alphaGlued`); the three clauses of `Classifies`
are clause (a) of [Stacks, Tag 01N8], the normalisation of `α`, and the identification of `φ^♯`
with the chart's ring map. No hypothesis on `A` is needed: the glued morphism lands in `U_1` by
construction. -/
theorem exists_classifies (ψ : VeroneseSections 𝒜 1 L)
    (hcover : ⨆ f : 𝒜 1, nvOpen 𝒜 ψ f = ⊤) :
    ∃ p : Pair 𝒜 L, Classifies 𝒜 ψ p := by
  have hWle : ∀ g : 𝒜 1, nvOpen 𝒜 ψ g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1) :=
    fun _ => le_rfl
  refine ⟨⟨toProj 𝒜 (ProjChartCocycle.glued 𝒜 ψ Nat.one_pos hWle hcover),
    ProjChartCocycleMatch.alphaGlued 𝒜 ψ Nat.one_pos hWle hcover⟩, ?_, ?_, ?_⟩
  · exact fun f => ProjChartCocycle.preimage_basicOpen_glued 𝒜 ψ Nat.one_pos hWle hcover f
  · exact fun f =>
      ProjChartCocycleMatch.alphaGlued_hom_app_top 𝒜 ψ Nat.one_pos hWle hcover f
  · exact fun f hle u =>
      ProjChartGluing.appLE_awayToSection (ψ.homogeneousRatios f.2 (hWle f)) Nat.one_pos
        (ProjChartCocycleMatch.ι_comp_toProj 𝒜 ψ Nat.one_pos hWle
          (ProjChartCocycle.ι_glued 𝒜 ψ Nat.one_pos hWle hcover) f) hle u

/-! ### Uniqueness -/

/-- **The morphism is determined**, the first uniqueness clause of [Stacks, Tag 01N8] read on
`Proj A`. Two classifying pairs have the same morphism: both factor through `U_1`, their
preimages of each `D₊(f)` are one and the same open `Y_{ψ(f)}`, and on the fractions `a/f^n` both
induce the dehomogenization `ψ_{(f)}`, so
`Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_appLE_eq_on_away` applies. -/
theorem hom_eq_of_classifies (htop : degreeOpen 𝒜 1 = ⊤) (ψ : VeroneseSections 𝒜 1 L)
    {p q : Pair 𝒜 L} (hp : Classifies 𝒜 ψ p) (hq : Classifies 𝒜 ψ q) : p.1 = q.1 := by
  obtain ⟨φ, α⟩ := p
  obtain ⟨φ', α'⟩ := q
  obtain ⟨φ₀, rfl⟩ := exists_toProj_eq 𝒜 htop φ
  obtain ⟨φ₀', rfl⟩ := exists_toProj_eq 𝒜 htop φ'
  refine congrArg (toProj 𝒜) (ProjSectionsUnique.eq_of_appLE_eq_on_away 𝒜 Nat.one_pos
    (W := fun f => nvOpen 𝒜 ψ f) (fun f => hp.1 f) (fun f => hq.1 f) fun f n a ha => ?_)
  exact (hp.2.2 f (hp.1 f).ge (Away.mk 𝒜 f.2 n a ha)).trans
    (hq.2.2 f (hq.1 f).ge (Away.mk 𝒜 f.2 n a ha)).symm

/-- **The trivialization is determined**, the second uniqueness clause of [Stacks, Tag 01N8]:
two isomorphisms `φ⁎𝒪_X(1) ≅ L ^⊗ 1` carrying the pulled-back degree-one sections to the
sections `ψ(f)` are equal, because those sections generate `L ^⊗ 1`. This is
`Stacks.AlgebraicGeometry.ProjSectionsUnique.iso_eq_of_app_eq`, the clause whose verification the
source omits. -/
theorem iso_eq_of_classifies (ψ : VeroneseSections 𝒜 1 L)
    (hcover : ⨆ f : 𝒜 1, nvOpen 𝒜 ψ f = ⊤) {φ : Y ⟶ AlgebraicGeometry.Proj 𝒜}
    {α α' : pullbackTwistOne 𝒜 φ ≅ natTensorPow L 1}
    (hα : ∀ f : 𝒜 1, α.hom.app ⊤ (pullbackSectionOne 𝒜 φ f) = ψ.pow f.2 1)
    (hα' : ∀ f : 𝒜 1, α'.hom.app ⊤ (pullbackSectionOne 𝒜 φ f) = ψ.pow f.2 1) : α = α' :=
  ProjSectionsUnique.iso_eq_of_app_eq (m := pullbackSectionOne 𝒜 φ)
    (t := fun f : 𝒜 1 => ψ.pow f.2 1) hcover α α' hα hα'

/-- **The universal property of `Proj A` of [Stacks, Tag 01NA].** Let `A` be a graded ring
generated as an `𝒜 0`-algebra by its degree-one part, let `Y` be a scheme, `L` an invertible
`𝒪_Y`-module and `ψ : A ⟶ Γ_*(Y, L)` a graded map whose degree-one part generates `L`. Then
there is one and only one pair `(φ, α)` consisting of a morphism `φ : Y ⟶ Proj A` and an
isomorphism `α : φ⁎𝒪_X(1) ≅ L ^⊗ 1` classifying `(L, ψ)`.

This is [Stacks, Tag 01N8] at `d = 1` with the target raised from `U_1` to the whole of
`Proj A`, which is the content of [Stacks, Tag 01NA]: `X = U_1` by `degreeOpen_one_eq_top`, so
every morphism into `X` is a morphism into `U_1` and the uniqueness assertion holds among all
morphisms into `X`. -/
@[stacks 01NA "the universal property of Proj"]
theorem existsUnique_classifies (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤)
    (ψ : VeroneseSections 𝒜 1 L) (hcover : ⨆ f : 𝒜 1, nvOpen 𝒜 ψ f = ⊤) :
    ∃! p : Pair 𝒜 L, Classifies 𝒜 ψ p := by
  obtain ⟨p, hp⟩ := exists_classifies 𝒜 ψ hcover
  refine ⟨p, hp, fun q hq => ?_⟩
  obtain ⟨φ, α⟩ := p
  obtain ⟨φ', α'⟩ := q
  have hφ : φ' = φ := hom_eq_of_classifies 𝒜 (degreeOpen_one_eq_top 𝒜 hgen) ψ hq hp
  subst hφ
  exact congrArg _ (iso_eq_of_classifies 𝒜 ψ hcover hq.2.1 hp.2.1)

end Stacks.AlgebraicGeometry.ProjDegreeOneRepresents

end
