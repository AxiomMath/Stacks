module

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic

/-!
# The morphism to projective space attached to a generating family of global sections

Stacks Tag 01NE says that `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]` *represents* the functor sending a scheme
`Y` to the set of pairs `(L, (s₀, …, sₙ))` with `L` an invertible `𝒪_Y`-module and the `sᵢ`
global sections of `L` generating it, two pairs being identified when an isomorphism of
invertible modules matches the sections. The half of that bijection with geometric content is the
passage from such a pair to a morphism `Y ⟶ ℙⁿ_ℤ`, and this file builds it in the case the
general construction is glued from, and reduces the general case to two named statements about
Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections`.

## The case that is built here

When the invertible module is `𝒪_X` itself — equivalently, when a trivialization has been chosen
— the sections `sᵢ` are elements of `Γ(X, 𝒪_X)`, they determine a ring homomorphism
`ℤ[T₀, …, Tₙ] → Γ(X, 𝒪_X)`, and `AlgebraicGeometry.Proj.fromOfGlobalSections` turns that into the
morphism. `Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse` is that morphism, landing
in the repository's `AlgebraicGeometry.projectiveSpaceAtUniverse` of Tag 01NF, and
`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver` is its companion over a base scheme,
through `Stacks.AmpleProjectiveImmersion.liftOver`.

**The hypothesis is `Ideal.span (Set.range s) = ⊤`, not "the `sᵢ` generate `𝒪_X`".** These differ:
on `X = 𝔸²_k ∖ {0}` the sections `x, y` of `𝒪_X` generate `𝒪_X` as a sheaf — their nonvanishing
loci cover `X` — while `Ideal.span {x, y} = (x, y) ≠ ⊤` inside `Γ(X, 𝒪_X) = k[x, y]`. Mathlib's
`AlgebraicGeometry.Proj.fromOfGlobalSections` takes the stronger spanning hypothesis, and so does
everything below. The hypothesis *is* satisfied in the situation the general construction needs it,
because there one of the sections is `1`; see "The reduction of the general case". The weaker
hypothesis `⨆ i, X.basicOpen (sᵢ) = ⊤` is what Mathlib's own proof actually consumes — it uses
`hf` only through `AlgebraicGeometry.Proj.openCoverOfMapIrrelevantEqTop` — so a version of
`fromOfGlobalSections` under it is a separate, genuinely missing Mathlib declaration.

## The reduction of the general case

For a nontrivial invertible `L` with generating sections `s₀, …, sₙ`, the source glues over the
cover of `X` by the nonvanishing loci `U i = X_{sᵢ}`. On `U i` the section `sᵢ` is a basis of `L`
— that is Stacks Tag 01CY, formalized here as
`Stacks.NonvanishingTrivialize.isIso_over_nonvanishingOpen` and `bijective_smul` — so there are
unique `t i k ∈ Γ(U i, 𝒪_X)` with `t i k • sᵢ = s_k` on `U i`. They satisfy `t i i = 1`, whence
`Ideal.span (Set.range (t i)) = ⊤` on `U i`, and the cocycle identity `t i k = t j k · t i j` on
`U i ∩ U j`, whence `t i j` is a unit there. So the families `t i` and `t j` agree up to a unit on
the overlap.

`Stacks.SectionsToProjectiveSpace.exists_hom_of_cover` glues the chart morphisms under exactly
that hypothesis, and it is conditional on two statements about `fromOfGlobalSections` that Mathlib
does not have:

* `Stacks.SectionsToProjectiveSpace.HasPullbackNaturality` — naturality in the source scheme:
  precomposing with `g : Y ⟶ X` is the morphism of the pulled-back sections.
* `Stacks.SectionsToProjectiveSpace.HasUnitInvariance` — invariance under scaling the whole
  family by a unit of `Γ(X, 𝒪_X)`.

Both are expected, both are false-free as stated (each is an instance of the corresponding
property of the chart maps `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`, whose ring map
`p / rᵏ ↦ f(p) / f(r)ᵏ` visibly has both), and neither is proved here; see "What is not done".

## Main definitions

* `Stacks.SectionsToProjectiveSpace.coordRing`, `coordGrading`: `ℤ[T₀, …, Tₙ]` in the universe of
  the base, with its grading by total degree — the homogeneous coordinate ring of the integral
  model `AlgebraicGeometry.projectiveSpaceAtUniverse`.
* `Stacks.SectionsToProjectiveSpace.sectionsHom`: the ring homomorphism `Tᵢ ↦ sᵢ`.
* `Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse`: **the morphism
  `X ⟶ ℙⁿ_ℤ` attached to a family of global sections of `𝒪_X` spanning the unit ideal.**
* `Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver`: the same over a base scheme.
* `Stacks.SectionsToProjectiveSpace.HasPullbackNaturality`,
  `Stacks.SectionsToProjectiveSpace.HasUnitInvariance`: **the two missing statements.**

## Main results

* `Stacks.SectionsToProjectiveSpace.map_irrelevant_eq_top`: a spanning family of sections
  satisfies Mathlib's hypothesis on the irrelevant ideal. The variables are homogeneous of degree
  one, so the span of the `sᵢ` is already contained in the image of the irrelevant ideal.
* `Stacks.SectionsToProjectiveSpace.preimage_basicOpen`: the preimage of the `i`-th standard chart
  `D₊(Tᵢ)` of projective space is `X.basicOpen (sᵢ)`. This is what makes the morphism the one the
  source describes rather than some other morphism.
* `Stacks.SectionsToProjectiveSpace.iSup_basicOpen_eq_top`: those preimages cover `X`.
* `Stacks.SectionsToProjectiveSpace.exists_hom_of_cover`: **the glueing step of Tag 01NE**, from
  the two statements above: a family of charts with spanning sections, agreeing up to a unit on
  each overlap, glues to a morphism `X ⟶ ℙⁿ_ℤ` restricting to each chart morphism.
* `Stacks.SectionsToProjectiveSpace.span_range_unit_smul`,
  `Stacks.SectionsToProjectiveSpace.span_range_appTop`: the spanning hypothesis is stable under
  scaling by a unit and under pullback, so neither of the two missing statements has to carry a
  side condition.

## Implementation notes

**The grading instance.** `MvPolynomial.gradedAlgebra` is an `abbrev`, not an instance, and
`AlgebraicGeometry.projectiveSpaceAtUniverse` supplies it with a `letI` inside its own body. It is
reintroduced here with `attribute [local instance]`, and that is enough for
`X ⟶ projectiveSpaceAtUniverse n` to be accepted for `X ⟶ Proj (coordGrading n)` with no
transport: the two instance terms are the same.

**No `@[stacks 01NE]` is claimed.** Tag 01NE is a representability statement. Even the direction
built here is incomplete without the inverse construction, which needs the pullback of the
twisting sheaf `𝒪(1)` of Tag 01MN along the morphism, and that comparison exists nowhere in the
repository.

## What is not done

`HasPullbackNaturality` and `HasUnitInvariance` are proved as
`Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality` and `.hasUnitInvariance`
(`StacksFrontier/AlgebraicGeometry/ProjGlobalSectionsAppTop/Consumers.lean`), and the `appTop`
computation is `Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop`
(`ProjGlobalSectionsAppTop/Basic.lean`), with `projAwayHom`, `projAwayHom_apply_mk` and
`away_ringHom_ext` beside it. Nothing below is blocked on a missing `appTop` lemma.

The superseded text follows.

Neither `Stacks.SectionsToProjectiveSpace.HasPullbackNaturality` nor
`Stacks.SectionsToProjectiveSpace.HasUnitInvariance` is proved. Both are statements about
Mathlib's construction alone — no object of this repository occurs in either — and both reduce,
through `AlgebraicGeometry.Proj.fromOfGlobalSections_resLE` and
`AlgebraicGeometry.Scheme.Cover.hom_ext`, to an identity of ring homomorphisms
`AlgebraicGeometry.Proj.Away 𝒜 Tᵢ ⟶ Γ(X, X.basicOpen sᵢ)` into which
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` is built out of `IsLocalization.map`. The
target `AlgebraicGeometry.Proj.basicOpen 𝒜 Tᵢ` is affine, so
`AlgebraicGeometry.Scheme.ext_of_isAffine` applies; what is missing is the computation of
`Scheme.Hom.appTop` of `toBasicOpenOfGlobalSections`, which Mathlib does not expose.

The module-theoretic half — producing the ratios `t i k` and their cocycle identity from an
invertible `L` and generating sections, by Tag 01CY — is also not done here. It needs no new
mathematics: `Stacks.NonvanishingTrivialize.bijective_smul` is exactly the statement that
`a ↦ a • sᵢ` is bijective over every open inside `X_{sᵢ}`, so `t i k` is its inverse applied to
`s_k`, and the cocycle identity follows from injectivity. It is left out only because it is a
second, independent body of work.

Tag 01CV, the graded ring `Γ_*(X, L) = ⨁_{d ≥ 0} Γ(X, L^{⊗d})`, is **not** needed for the
construction above, and it is not absent as a mathematical object even though the tag is unplaced:
`Stacks.GradedSections.sectionRing` is `⨁_{d ≥ 0} (𝟙 ⟶ L^{⊗d})` with its ring structure
(`Stacks.GradedSections.instRing`), `Stacks.SectionRingGeometric.sectionCommRing` proves it
commutative for an invertible sheaf of modules, and
`Stacks.SectionRingGeometric.unitModuleSectionCommRing` is the case `L = 𝒪_X`. What it is *not* is
a `GradedRing` of submodules of a ring, which is the shape `AlgebraicGeometry.Proj` consumes; it
is a `DirectSum.GRing` on an external family. Anything wanting `Proj Γ_*(X, L)` would have to
bridge the two shapes first.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SectionsToProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The homogeneous coordinate ring -/

/-- The homogeneous coordinate ring `ℤ[T₀, …, Tₙ]` of the integral model of `ℙⁿ`, in the universe
of the base scheme. -/
abbrev coordRing (n : ℕ) : Type u := MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)

/-- The grading by total degree on `Stacks.SectionsToProjectiveSpace.coordRing`. This is the
grading `AlgebraicGeometry.projectiveSpaceAtUniverse` takes `Proj` of. -/
abbrev coordGrading (n : ℕ) : ℕ → Submodule (ULift.{u} ℤ) (coordRing.{u} n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)

/-- The unique ring homomorphism out of the universe copy of `ℤ`. -/
def coeffHom (R : Type*) [Ring R] : ULift.{u} ℤ →+* R :=
  (Int.castRingHom R).comp (ULift.ringEquiv).toRingHom

/-- Each variable is homogeneous of degree one. This is why a spanning family of sections meets
Mathlib's hypothesis on the irrelevant ideal. -/
theorem X_mem_coordGrading_one {n : ℕ} (i : Fin (n + 1)) :
    (MvPolynomial.X i : coordRing.{u} n) ∈ coordGrading.{u} n 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X _ i)

/-! ### Stability of the spanning hypothesis -/

section Span

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

/-- Scaling a family by a unit does not change the ideal it spans. -/
theorem span_range_unit_smul (u : Rˣ) (s : Fin m → R) :
    Ideal.span (Set.range fun i => (u : R) * s i) = Ideal.span (Set.range s) := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro - ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro - ⟨i, rfl⟩
    have h : s i = (↑u⁻¹ : R) * ((u : R) * s i) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [SetLike.mem_coe, h]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- A family spanning the unit ideal still spans the unit ideal after a ring homomorphism. -/
theorem span_range_comp (φ : R →+* S) (s : Fin m → R)
    (hs : Ideal.span (Set.range s) = ⊤) :
    Ideal.span (Set.range fun i => φ (s i)) = ⊤ := by
  have h : (Set.range fun i => φ (s i)) = φ '' Set.range s := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Ideal.map_span, hs, Ideal.map_top]

end Span

/-! ### The morphism -/

variable {X : Scheme.{u}} {n : ℕ}

/-- The ring homomorphism `ℤ[T₀, …, Tₙ] → Γ(X, 𝒪_X)` sending `Tᵢ` to `sᵢ`. -/
def sectionsHom (s : Fin (n + 1) → Γ(X, ⊤)) : coordRing.{u} n →+* Γ(X, ⊤) :=
  MvPolynomial.eval₂Hom (coeffHom _) s

/-- The homomorphism `sectionsHom s` sends the variable `Tᵢ` to `sᵢ`. -/
@[simp] theorem sectionsHom_X (s : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) :
    sectionsHom s (MvPolynomial.X i) = s i := by
  simp [sectionsHom]

/-- **A family of sections spanning the unit ideal satisfies Mathlib's hypothesis on the
irrelevant ideal.** The variables are homogeneous of degree one, so they already lie in the
irrelevant ideal and their images are the `sᵢ`. -/
theorem map_irrelevant_eq_top (s : Fin (n + 1) → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) :
    (HomogeneousIdeal.irrelevant (coordGrading.{u} n)).toIdeal.map (sectionsHom s) = ⊤ := by
  rw [eq_top_iff, ← hs, Ideal.span_le]
  rintro - ⟨i, rfl⟩
  rw [SetLike.mem_coe, ← sectionsHom_X s i]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem_coordGrading_one i))

/-- **The morphism to projective space attached to a family of global sections of `𝒪_X` spanning
the unit ideal**: the direction of Stacks Tag 01NE with geometric content, in the case the general
construction is glued from. -/
def toProjectiveSpaceAtUniverse (s : Fin (n + 1) → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) : X ⟶ projectiveSpaceAtUniverse.{u} n :=
  Proj.fromOfGlobalSections (coordGrading.{u} n) (sectionsHom s) (map_irrelevant_eq_top s hs)

/-- The morphism depends on the family of sections only, not on the proof that it spans. -/
theorem toProjectiveSpaceAtUniverse_congr {s s' : Fin (n + 1) → Γ(X, ⊤)} (h : s = s')
    (hs : Ideal.span (Set.range s) = ⊤) (hs' : Ideal.span (Set.range s') = ⊤) :
    toProjectiveSpaceAtUniverse s hs = toProjectiveSpaceAtUniverse s' hs' := by
  subst h; rfl

variable (s : Fin (n + 1) → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)

/-- **The preimage of the `i`-th standard chart `D₊(Tᵢ)` of projective space is the nonvanishing
locus of `sᵢ`.** This is what identifies the morphism as the one Tag 01NE describes. -/
theorem preimage_basicOpen (i : Fin (n + 1)) :
    toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n)
        (MvPolynomial.X i) = X.basicOpen (s i) := by
  rw [show X.basicOpen (s i) = X.basicOpen (sectionsHom s (MvPolynomial.X i)) by
    rw [sectionsHom_X]]
  exact Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom s)
    (map_irrelevant_eq_top s hs) Nat.one_pos (X_mem_coordGrading_one i)

include hs in
/-- The nonvanishing loci of the `sᵢ`, that is the preimages of the standard charts, cover `X`. -/
theorem iSup_basicOpen_eq_top : ⨆ i, X.basicOpen (s i) = ⊤ :=
  (iSup_range (g := fun t : Γ(X, ⊤) => X.basicOpen t) (f := s)).symm.trans
    (iSup_basicOpen_of_span_eq_top (X := X) ⊤ (Set.range s) hs)

/-- The morphism `X ⟶ ℙⁿ_S` over a base `S` attached to a structure morphism and a family of
global sections of `𝒪_X` spanning the unit ideal. No compatibility has to be checked: `ℙⁿ_S` is a
fibre product over the terminal scheme, which is
`Stacks.AmpleProjectiveImmersion.liftOver`. -/
def toProjectiveSpaceOver {S : Scheme.{u}} (f : X ⟶ S) : X ⟶ projectiveSpaceOver n S :=
  Stacks.AmpleProjectiveImmersion.liftOver f (toProjectiveSpaceAtUniverse s hs)

/-- The morphism `X ⟶ ℙⁿ_S` composed with the projection to `S` is the structure morphism `f`. -/
@[simp] theorem toProjectiveSpaceOver_fst {S : Scheme.{u}} (f : X ⟶ S) :
    toProjectiveSpaceOver s hs f ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f :=
  Stacks.AmpleProjectiveImmersion.liftOver_fst _ _

/-- The morphism `X ⟶ ℙⁿ_S` composed with the projection to the integral model is
`toProjectiveSpaceAtUniverse s hs`. -/
@[simp] theorem toProjectiveSpaceOver_snd {S : Scheme.{u}} (f : X ⟶ S) :
    toProjectiveSpaceOver s hs f ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse s hs :=
  Stacks.AmpleProjectiveImmersion.liftOver_snd _ _

/-- **The restriction of the morphism to the `i`-th standard chart**, which is Mathlib's
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` — the map built directly out of the ring
homomorphism, with no glueing. -/
theorem resLE_toProjectiveSpaceAtUniverse (i : Fin (n + 1)) :
    (toProjectiveSpaceAtUniverse s hs).resLE
        (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
        (X.basicOpen (sectionsHom s (MvPolynomial.X i)))
        (Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom s)
          (map_irrelevant_eq_top s hs) Nat.one_pos (X_mem_coordGrading_one i)).ge =
      Proj.toBasicOpenOfGlobalSections (coordGrading.{u} n) (sectionsHom s) rfl Nat.one_pos
        (X_mem_coordGrading_one i) :=
  Proj.fromOfGlobalSections_resLE (coordGrading.{u} n) (sectionsHom s)
    (map_irrelevant_eq_top s hs) Nat.one_pos (X_mem_coordGrading_one i)

section Universe0

/-- The morphism to the literal integral model `Proj ℤ[T₀, …, Tₙ]` at universe zero, through
`AlgebraicGeometry.projectiveSpaceIntegralIso`. -/
def toProjectiveSpace {X : Scheme.{0}} {n : ℕ} (s : Fin (n + 1) → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) : X ⟶ projectiveSpace n :=
  toProjectiveSpaceAtUniverse s hs ≫ (projectiveSpaceIntegralIso n).inv

/-- The morphism to `ℙⁿ_S` at universe zero, through the repository's
`AlgebraicGeometry.projectiveSpaceOver.lift`. -/
def toProjectiveSpaceOverZero {X S : Scheme.{0}} {n : ℕ} (f : X ⟶ S)
    (s : Fin (n + 1) → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤) :
    X ⟶ projectiveSpaceOver n S :=
  projectiveSpaceOver.lift n f (toProjectiveSpace s hs)

/-- The morphism `X ⟶ ℙⁿ_S` composed with the projection to `S` is the structure morphism `f`. -/
@[simp] theorem toProjectiveSpaceOverZero_fst {X S : Scheme.{0}} {n : ℕ} (f : X ⟶ S)
    (s : Fin (n + 1) → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤) :
    toProjectiveSpaceOverZero f s hs ≫ pullback.fst _ _ = f :=
  projectiveSpaceOver.lift_fst n f _

/-- The morphism `X ⟶ ℙⁿ_S` composed with the projection to `Proj ℤ[T₀, …, Tₙ]` is
`toProjectiveSpace s hs`. -/
@[simp] theorem toProjectiveSpaceOverZero_toIntegral {X S : Scheme.{0}} {n : ℕ} (f : X ⟶ S)
    (s : Fin (n + 1) → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤) :
    toProjectiveSpaceOverZero f s hs ≫ projectiveSpaceOver.toIntegral n S =
      toProjectiveSpace s hs :=
  projectiveSpaceOver.lift_toIntegral n f _

end Universe0

/-! ### The two statements the general case needs -/

/-- **Naturality of the morphism to projective space in the source scheme.** Precomposing with
`g : Y ⟶ X` gives the morphism of the pulled-back family of sections. -/
def HasPullbackNaturality : Prop :=
  ∀ {Y X : Scheme.{u}} {n : ℕ} (g : Y ⟶ X) (s : Fin (n + 1) → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤)
    (hgs : Ideal.span (Set.range fun i => g.appTop (s i)) = ⊤),
    g ≫ toProjectiveSpaceAtUniverse s hs =
      toProjectiveSpaceAtUniverse (fun i => g.appTop (s i)) hgs

/-- **Invariance of the morphism to projective space under scaling the family by a unit.** Not
proved; see the module docstring. -/
def HasUnitInvariance : Prop :=
  ∀ {X : Scheme.{u}} {n : ℕ} (u : Γ(X, ⊤)ˣ) (s : Fin (n + 1) → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤)
    (hus : Ideal.span (Set.range fun i => (u : Γ(X, ⊤)) * s i) = ⊤),
    toProjectiveSpaceAtUniverse (fun i => (u : Γ(X, ⊤)) * s i) hus =
      toProjectiveSpaceAtUniverse s hs

/-! ### The glueing step -/

/-- Restriction of a global section along an inclusion of opens, as a map of sections of the
structure sheaves of the open subschemes. -/
abbrev resOfLE {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (a : Γ(V.toScheme, ⊤)) :
    Γ(U.toScheme, ⊤) := (X.homOfLE h).appTop a

/-- **The glueing step of Stacks Tag 01NE.** Given a cover of `X` by opens `U i`, on each of which
a family `t i` of sections of `𝒪_X` spans the unit ideal, and given that on each overlap the two
families differ by a unit, the chart morphisms glue to a single morphism `X ⟶ ℙⁿ_ℤ`.

For an invertible `L` with generating global sections `s₀, …, sₙ` the hypotheses hold with
`U i = X_{sᵢ}` and `t i k` the ratio `s_k / sᵢ` produced by the trivialization of Tag 01CY; the
unit on the overlap is `t i j`, invertible there by the cocycle identity. See the module
docstring.

Conditional on `Stacks.SectionsToProjectiveSpace.HasPullbackNaturality` and
`Stacks.SectionsToProjectiveSpace.HasUnitInvariance`. -/
theorem exists_hom_of_cover (hA : HasPullbackNaturality.{u}) (hB : HasUnitInvariance.{u})
    {X : Scheme.{u}} {n : ℕ} (U : Fin (n + 1) → X.Opens) (hU : IsOpenCover U)
    (t : ∀ i, Fin (n + 1) → Γ((U i).toScheme, ⊤))
    (ht : ∀ i, Ideal.span (Set.range (t i)) = ⊤)
    (hagree : ∀ i j, ∃ u : Γ((U i ⊓ U j : X.Opens).toScheme, ⊤)ˣ, ∀ k,
      resOfLE (inf_le_left : U i ⊓ U j ≤ U i) (t i k) =
        (u : Γ((U i ⊓ U j : X.Opens).toScheme, ⊤)) *
          resOfLE (inf_le_right : U i ⊓ U j ≤ U j) (t j k)) :
    ∃ g : X ⟶ projectiveSpaceAtUniverse.{u} n,
      ∀ i, (U i).ι ≫ g = toProjectiveSpaceAtUniverse (t i) (ht i) := by
  have key : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫
      toProjectiveSpaceAtUniverse (t i) (ht i) =
        X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫
          toProjectiveSpaceAtUniverse (t j) (ht j) := by
    intro i j
    obtain ⟨u, hu⟩ := hagree i j
    rw [hA (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (t i) (ht i)
        (span_range_comp _ _ (ht i)),
      hA (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (t j) (ht j)
        (span_range_comp _ _ (ht j))]
    have hfun : (fun k => (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).appTop (t i k)) =
        fun k => (u : Γ((U i ⊓ U j : X.Opens).toScheme, ⊤)) *
          (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop (t j k) := funext hu
    have h2 := hB u (fun k => (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop (t j k))
      (span_range_comp _ _ (ht j))
      (by rw [span_range_unit_smul]; exact span_range_comp _ _ (ht j))
    exact (toProjectiveSpaceAtUniverse_congr hfun _ _).trans h2
  refine ⟨(X.openCoverOfIsOpenCover U hU).glueMorphisms
    (fun i => toProjectiveSpaceAtUniverse (t i) (ht i)) ?_, ?_⟩
  · intro i j
    change pullback.fst (U i).ι (U j).ι ≫ toProjectiveSpaceAtUniverse (t i) (ht i) =
      pullback.snd (U i).ι (U j).ι ≫ toProjectiveSpaceAtUniverse (t j) (ht j)
    rw [← cancel_epi (isPullback_opens_inf (U i) (U j)).isoPullback.hom, ← Category.assoc,
      ← Category.assoc, (isPullback_opens_inf (U i) (U j)).isoPullback_hom_fst,
      (isPullback_opens_inf (U i) (U j)).isoPullback_hom_snd]
    exact key i j
  · intro i
    exact (X.openCoverOfIsOpenCover U hU).ι_glueMorphisms _ _ i

end Stacks.SectionsToProjectiveSpace

end
