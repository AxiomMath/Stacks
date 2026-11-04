module

public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.Separated

/-!
# The graded direct image `⨁_{d ≥ 0} f_* L^{⊗ d}` of a relatively ample module

Let `f : X ⟶ S` be a morphism of schemes and `L` an invertible `𝒪_X`-module that is ample
relative to `f` in the sense of [Stacks, Tag 01VH]. Clause (5) of [Stacks, Tag 01VJ] singles
out the quasi-coherent graded `𝒪_S`-algebra

`𝒜 = f_*(⨁_{d ≥ 0} L^{⊗ d})`

together with the adjunction map `ψ : f^*𝒜 → ⨁_{d ≥ 0} L^{⊗ d}`, and asserts three things: that
`f` is quasi-separated, that `U(ψ) = X`, and that `r_{L, ψ} : X ⟶ Proj_S(𝒜)` is an open
immersion. This file proves the **first two**, and builds the homogeneous pieces of `𝒜`.

## Main definitions

* `Stacks.RelativeAmple.gradedDirectImage`: the homogeneous pieces of `𝒜`, namely
  `f_* L^{⊗ d}` in degree `d ≥ 0` and the zero module in negative degrees. Its sections over an
  open `V` of `S` are, by `rfl`, the sections of `L^{⊗ d}` over `f⁻¹(V)`.

## Main results

* `Stacks.RelativeAmple.IsRelativelyAmple.quasiSeparated`: **Tag 01VJ, clause (5), the
  quasi-separatedness assertion.**
* `Stacks.RelativeAmple.isQuasicoherent_gradedDirectImage` and
  `isZero_gradedDirectImage_of_neg`: the homogeneous pieces of `𝒜` are quasi-coherent
  `𝒪_S`-modules and vanish in negative degrees.
* `Stacks.RelativeAmple.sections_gradedDirectImage`: the sections of `𝒜_d` over `V` are the
  sections of `L^{⊗ d}` over `f⁻¹(V)`.
* `Stacks.RelativeAmple.exists_pos_section_mem_nonvanishingOpenOn`: through every point of
  `f⁻¹(V)`, for `V` an affine open of the base, there is a section of `𝒜_d` for some `d ≥ 1`
  whose nonvanishing open is affine and contains that point.
* `Stacks.RelativeAmple.iSup_nonvanishingOpenOn_eq_top`: **Tag 01VJ, clause (5), the assertion
  `U(ψ) = X`.**

## Why `U(ψ) = X` is the supremum below

`U(ψ)` is, by its definition in [Stacks, Tag 01NK] (formalized here as
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.coveringOpen`), the union of the
nonvanishing opens `X_{ψ(a)}` of the images under `ψ` of the homogeneous sections `a` of `𝒜` of
positive degree. For the `𝒜` of clause (5) the sections of `𝒜_d` over `V` *are* the sections of
`L^{⊗ d}` over `f⁻¹(V)` — the pushforward presheaf is given by `Γ(f_* M, V) = Γ(M, f⁻¹(V))`, and
this holds by `rfl`, which is `sections_gradedDirectImage` — and the degree-`d` component of the
adjunction map `ψ` carries such a section to itself under that identification. So the family of
sections whose nonvanishing opens are united to form `U(ψ)` is exactly the family appearing in
`iSup_nonvanishingOpenOn_eq_top`: triples of an affine open `V` of `S`, a degree `d ≥ 1`, and a
section of `L^{⊗ d}` over `f⁻¹(V)`. No global `ψ` is named, and none is needed: the statement
quantifies over the sections themselves.

Restricting to *affine* `V` only strengthens the statement, the affine opens being a basis.

## Implementation notes

**The pieces are indexed by `ℤ` and defined by a match on the constructors of `Int`.** Situation
[Stacks, Tag 01NN] asks for a family `ℤ → S.Modules` vanishing in negative degrees, while the
pushforwards `f_* L^{⊗ d}` that are wanted are indexed by `d ≥ 0`. Writing the piece as
`if 0 ≤ d then … else 0` would make every use of a nonnegative degree carry a transport along
`dif_pos`. Matching on `Int.ofNat` and `Int.negSucc` instead makes `𝒜_{(d : ℕ)}` reduce to
`f_* L^{⊗ d}` definitionally, and — because `Nat.cast` into `ℤ` is `Int.ofNat` and `Int.add`
reduces on that constructor — makes `𝒜_{(i : ℕ) + (j : ℕ)}` reduce to `f_* L^{⊗ (i + j)}` as
well, so the degree bookkeeping of a graded multiplication would need no transport either. The
same observation is recorded for the graded ring of sections in the implementation notes of
`StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing`.

Quasi-coherence of the pieces is [Stacks, Tag 01LC] — pushforward along a quasi-compact,
quasi-separated morphism preserves quasi-coherence — applied to the tensor powers of `L`, which
are quasi-coherent because they are invertible. Both hypotheses of that tag are available for a
relatively ample `L`: quasi-compactness is part of [Stacks, Tag 01VH] and quasi-separatedness is
`IsRelativelyAmple.quasiSeparated` below. This is the step the source attributes to Schemes,
Lemma 26.24.1.

## The graded algebra and the morphism `r_{L, ψ}`

The pieces here are written with `Stacks.Ample.tensorPowModule`. The graded algebra `𝒜` itself,
with its multiplication and unit, is assembled in
`StacksFrontier/AlgebraicGeometry/RelativeAmple/DirectImageAlgebra.lean` as
`Stacks.RelativeAmple.directImageAlgebra`, from the Laurent algebra of [Stacks, Tag 01CU] (pieces
`Stacks.AmpleProjectiveImmersion.tensorPowerModule`), and the adjunction map `ψ` there is
`Stacks.RelativeAmple.directImagePowerMap`. For that `𝒜` and that `ψ`,
`StacksFrontier/AlgebraicGeometry/RelativeAmple/ProjIso.lean` proves `U(ψ) = X`
(`Stacks.RelativeAmple.coveringOpen_directImagePowerMap`), builds the morphism
`r : X ⟶ Proj_S(𝒜)` (`Stacks.RelativeAmple.relativeAmpleProjHom`) and proves it is an isomorphism
when `f` is universally closed ([Stacks, Tag 0C6J]). The open-immersion assertion of clause (5),
clauses (4) and (6), and the equivalence of all six clauses are in
`StacksFrontier/AlgebraicGeometry/RelativeAmple/ProjCharacterization.lean`
(`Stacks.RelativeAmple.IsRelativelyAmple.isOpenImmersion_globalMorphism`,
`Stacks.RelativeAmple.isRelativelyAmple_tfae`).

## References

* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VI](https://stacks.math.columbia.edu/tag/01VI)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [EGA II, Proposition 4.6.3]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ZeroObject
open Stacks.Ample
open Stacks.SectionPowerOpen (nonvanishingOpenOn)

universe u

namespace Stacks.RelativeAmple

/-! ### Clause (5): quasi-separatedness -/

/-- **Stacks Tag 01VJ, clause (5), the quasi-separatedness assertion.** A morphism carrying a
relatively ample invertible module is quasi-separated. It is in fact separated, which is
[Stacks, Tag 01VI] and is
`AlgebraicGeometry.Scheme.Modules.IsRelativelyAmple.isSeparated`; a separated
morphism is quasi-separated. -/
@[stacks 01VJ "(5), the quasi-separatedness assertion: a morphism carrying a relatively ample \
invertible module is quasi-separated"]
theorem IsRelativelyAmple.quasiSeparated {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
    [IsInvertibleModule X L] (hL : IsRelativelyAmple f L) : QuasiSeparated f := by
  have := AlgebraicGeometry.Scheme.Modules.IsRelativelyAmple.isSeparated hL
  infer_instance

/-! ### The homogeneous pieces of `𝒜 = f_*(⨁_{d ≥ 0} L^{⊗ d})` -/

/-- **The homogeneous pieces of the graded `𝒪_S`-algebra `𝒜 = f_*(⨁_{d ≥ 0} L^{⊗ d})` of clause
(5) of [Stacks, Tag 01VJ]**: the direct image `f_* L^{⊗ d}` in degree `d ≥ 0`, and the zero
module in negative degrees, as Situation [Stacks, Tag 01NN] requires.

The match is on the constructors of `Int` rather than on `0 ≤ d`, so that a nonnegative degree
needs no transport; see the implementation notes of this file. -/
def gradedDirectImage {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] : ℤ → S.Modules
  | (d : ℕ) => (Scheme.Modules.pushforward f).obj (tensorPowModule X L (d : ℤ))
  | .negSucc _ => 0

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]

/-- In a nonnegative degree the piece is the direct image of the tensor power, by definition. -/
theorem gradedDirectImage_natCast (d : ℕ) :
    gradedDirectImage f L (d : ℤ)
      = (Scheme.Modules.pushforward f).obj (tensorPowModule X L (d : ℤ)) :=
  rfl

/-- **The sections of `𝒜_d` over an open `V` of the base are the sections of `L^{⊗ d}` over
`f⁻¹(V)`.** This holds by `rfl`: it is the defining formula for the sections of a pushforward.
It is this identification that makes the degree-`d` component of the adjunction map
`ψ : f^*𝒜 → ⨁_{d ≥ 0} L^{⊗ d}` the identity on sections over `V`. -/
theorem sections_gradedDirectImage (d : ℕ) (V : S.Opens) :
    Γ(gradedDirectImage f L (d : ℤ), V) = Γ(tensorPowModule X L (d : ℤ), f ⁻¹ᵁ V) :=
  rfl

/-- **The pieces of `𝒜` vanish in negative degrees**, as Situation [Stacks, Tag 01NN]
requires. -/
theorem isZero_gradedDirectImage_of_neg {d : ℤ} (hd : d < 0) :
    IsZero (gradedDirectImage f L d) := by
  cases d with
  | ofNat k => exact absurd hd (by simp)
  | negSucc k => exact isZero_zero _

/-- **The pieces of `𝒜` in nonnegative degree are quasi-coherent `𝒪_S`-modules.** This is
[Stacks, Tag 01LC], pushforward along a quasi-compact and quasi-separated morphism preserving
quasi-coherence, applied to the tensor power `L^{⊗ d}`, which is quasi-coherent because it is
invertible. This is the step the source attributes to Schemes, Lemma 26.24.1. -/
theorem isQuasicoherent_gradedDirectImage [QuasiCompact f] [QuasiSeparated f] (d : ℕ) :
    (gradedDirectImage f L (d : ℤ)).IsQuasicoherent := by
  have : (tensorPowModule X L (d : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L (d : ℤ)
  exact AlgebraicGeometry.pushforward_isQuasicoherent f (tensorPowModule X L (d : ℤ))

/-- **The pieces of `𝒜` in nonnegative degree are quasi-coherent**, for a relatively ample `L`:
both hypotheses of [Stacks, Tag 01LC] are then available, quasi-compactness from
[Stacks, Tag 01VH] and quasi-separatedness from
`Stacks.RelativeAmple.IsRelativelyAmple.quasiSeparated`. -/
@[stacks 01VJ "(5), the homogeneous pieces of the graded algebra A = f_*(⨁_{d ≥ 0} L^{⊗ d}) of \
the clause: their quasi-coherence in nonnegative degree (the step the source attributes to \
Schemes 26.24.1) and their vanishing in negative degree. The graded algebra A itself, with its \
multiplication, is Stacks.RelativeAmple.directImageAlgebra; see the module docstring"]
theorem isQuasicoherent_gradedDirectImage_of_isRelativelyAmple
    (hL : IsRelativelyAmple f L) (d : ℕ) :
    (gradedDirectImage f L (d : ℤ)).IsQuasicoherent := by
  have := hL.quasiCompact
  have := hL.quasiSeparated
  exact isQuasicoherent_gradedDirectImage f L d

/-! ### Clause (5): `U(ψ) = X` -/

/-- **Through every point over an affine open of the base there is a section of `𝒜_d` of
positive degree `d` that does not vanish there**, with affine nonvanishing open. This is
ampleness of the restriction of `L` to `f⁻¹(V)`, read through
`Stacks.RelativeAmpleLocalOnBase.isAmple_pullbackModule_iff`, which states ampleness on the open
subscheme `f⁻¹(V)` in terms of sections over the open `f⁻¹(V)` of the tensor powers of `L` on
`X` — and those are, by `sections_gradedDirectImage`, the sections of `𝒜_d` over `V`. -/
theorem exists_pos_section_mem_nonvanishingOpenOn (hL : IsRelativelyAmple f L) {V : S.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ f ⁻¹ᵁ V) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ s : Γ(gradedDirectImage f L (d : ℤ), V),
      IsAffineOpen (nonvanishingOpenOn (tensorPowModule X L (d : ℤ)) (f ⁻¹ᵁ V) s) ∧
        x ∈ nonvanishingOpenOn (tensorPowModule X L (d : ℤ)) (f ⁻¹ᵁ V) s :=
  ((Stacks.RelativeAmpleLocalOnBase.isAmple_pullbackModule_iff L (f ⁻¹ᵁ V)).mp
    (hL.isAmple_preimage f L V hV)).2 x hx

/-- **Stacks Tag 01VJ, clause (5), the assertion `U(ψ) = X`.** For `L` ample relative to `f`,
the nonvanishing opens of the sections of positive degree of `𝒜 = f_*(⨁_{d ≥ 0} L^{⊗ d})` cover
`X`.

The supremum is over triples of an affine open `V` of `S`, a degree `d ≥ 1`, and a section of
`𝒜_d` over `V`; `U(ψ)` is the union of exactly these nonvanishing opens, since the degree-`d`
component of the adjunction map `ψ` is the identity on sections over `V` under
`sections_gradedDirectImage`. See the section "Why `U(ψ) = X` is the supremum below" of the
module docstring. -/
@[stacks 01VJ "(5), the assertion U(psi) = X: for L ample relative to f, the nonvanishing opens \
of the positive-degree sections of A = f_*(⨁_{d ≥ 0} L^{⊗ d}) cover X"]
theorem iSup_nonvanishingOpenOn_eq_top (hL : IsRelativelyAmple f L) :
    (⨆ p : Σ' (V : S.Opens) (_ : IsAffineOpen V) (d : ℕ) (_ : 1 ≤ d),
        Γ(gradedDirectImage f L (d : ℤ), V),
      nonvanishingOpenOn (tensorPowModule X L (p.2.2.1 : ℤ)) (f ⁻¹ᵁ p.1) p.2.2.2.2) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ?_
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨d, hd, s, -, hs⟩ := exists_pos_section_mem_nonvanishingOpenOn f L hL hV hxV
  exact ⟨⟨V, hV, d, hd, s⟩, hs⟩

end Stacks.RelativeAmple

end
