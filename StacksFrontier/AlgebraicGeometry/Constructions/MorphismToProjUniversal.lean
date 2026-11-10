module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartCocycleMatch
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjSectionsUniqueness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms into `Proj` from a graded map of section rings

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)`, let `d > 0` and let `U_d ⊆ X` be the
open of Equation 27.12.0.1. Let `Y` be a scheme, `L` an invertible `𝒪_Y`-module and
`ψ : A^{(d)} → Γ_*(Y, L)` a graded ring map whose degree-`d` part generates `L`. [Stacks, Tag
01N8] produces a morphism `φ : Y ⟶ X` factoring through `U_d` together with an isomorphism
`α : φ⁎𝒪_{U_d}(d) ≅ L` identifying `ψ^d_φ` with `ψ`, and asserts that the pair `(φ, α)` is
**unique**. This file assembles the existence half (built in the sibling `ProjChart*` files) and
the uniqueness half (`ProjSectionsUniqueness.lean`) into that single statement.

## Main definitions

* `Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow`: the left unitor
  `L ^⊗ 1 ≅ L`, the first of the two transports listed below.
* `Stacks.AlgebraicGeometry.MorphismToProjUniversal.psiSection`: the global section `ψ(f)` of `L`
  attached to a homogeneous `f` of degree `d`, read in `Γ(L, ⊤)` through that unitor.
* `Stacks.AlgebraicGeometry.MorphismToProjUniversal.twistCast`: the transport
  `φ⁎𝒪_X(k) ≅ φ⁎𝒪_X(d)` along an equality `k = d` of natural numbers, the second transport.
* `Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible`: **the compatibility of a pair
  `(φ, α)` with `ψ`**, i.e. the assertion that `ψ^d_φ` agrees with `ψ` via `α`, written out in
  the two degreewise forms described below.

## Main results

* `Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair`: there is a unique pair
  `(φ, α)` compatible with `ψ`. The statement of [Stacks, Tag 01N8] itself, with the commuting
  square written on the tensor powers in every degree, is
  `Stacks.AlgebraicGeometry.MorphismToProjSquare.existsUnique_square`, which is derived from
  this one.
* `Stacks.AlgebraicGeometry.MorphismToProjUniversal.preimage_basicOpen_eq`: for a compatible
  pair, the preimage of `D₊(f)` under `φ` is the nonvanishing open `Y_{ψ(f)}`. This is the
  topological step the source performs before invoking sobriety; here it is a *consequence* of
  compatibility, not a hypothesis, which is why it does not appear in `IsCompatible`.
* `Stacks.AlgebraicGeometry.MorphismToProjUniversal.preimage_basicOpen_eq_nonvanishingOpen`:
  for an arbitrary morphism through `U_d`, that preimage is the nonvanishing open of the
  pulled-back degree-`d` section. Both inclusions: [Stacks, Tag 01MV] and [Stacks, Tag 0H78] are
  equivalences, and `ProjChartAlphaInstance` used only one direction of each.

## Implementation notes

**What the pair is.** `Stacks.AlgebraicGeometry.ProjSectionsUnique.Pair` bundles `φ` with `α`, so
"the pair is unique" is an equality in a single type rather than an equality together with a
transported one; `∃!` over that type is the whole lemma, existence and uniqueness at once.

**The compatibility is degreewise, in two shapes.** The source states compatibility as a
commuting square of graded ring maps out of `A^{(d)}`. A graded map *is* its family of
components, so the square is the family of degreewise identities
`α^{⊗ n}(ψ^d_φ(x)) = ψ(x)`, `x ∈ (A^{(d)})_n`. In degree `1` the tensor power is trivial and that
identity is written here as it stands — the first conjunct of `IsCompatible`. In degree `n` the
identity is written in the local form the source itself uses in its proof, which needs no tensor
power at all: over any open mapping into `D₊(f)`,

  `ψ(a)|_V = φ^♯(a/f^n) · ψ(f)^n|_V`,

the second conjunct of `IsCompatible`. Divided through by the nonvanishing `ψ(f)^n` it says
exactly that `φ^♯` on `A_{(f)}` is the ring map `a/f^n ↦ ψ(a)/ψ(f)^n` of the source, which is
how the source pins `φ` down and how it proves `φ` unique. This local form is what the triples of
Section 27.12 are classified by; the square on the tensor powers `α^{⊗ n}` in every degree, as the
source states it, is derived from it in
`StacksFrontier/AlgebraicGeometry/Constructions/MorphismToProjSquare.lean`.

**The tensor-power square.** The multiplicativity of `thetaNat` rests on associativity of the
twist multiplication maps at the level of sheaves. That associativity is proved and
hypothesis-free — `Stacks.AlgebraicGeometry.ThetaMul.twistMulIso_assoc`, whose proof is
`Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_assoc` — and with it the multiplicativity
square itself, in every bidegree of natural numbers: `Stacks.AlgebraicGeometry.ThetaMul.theta_mul`
and `Stacks.AlgebraicGeometry.ThetaMul.thetaNat_mul`. So nothing stands in the way of stating the
second conjunct as the square `α^{⊗ n}(ψ^d_φ(x)) = ψ(x)`; the local identity is kept because it
is what the source's own proof establishes and what the uniqueness argument consumes, and because
the square implies it, so the uniqueness assertion below is at least as strong either way.

**The two transports, each applied once.** Every statement on the existence side is indexed by
`L ^⊗ 1`, while `Pair` and the uniqueness side are indexed by `L`; the difference is the left
unitor, isolated in `unitorPow` and pushed onto nonvanishing opens by
`Stacks.Ample.nonvanishingLocus_congr` in `nonvanishingOpen_psiSection`. The deliberate deferral
is recorded in the implementation notes of `MorphismToProjRatios.lean`. Likewise
`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.pullbackDegreeSection` and
`Stacks.AlgebraicGeometry.MorphismsIntoProj.psiPullbackHom 𝒜 φ 1` are one and the same
construction read at the indices `d` and `1 * d`; `twistCast` is that transport and
`twistCast_hom_app_psiPullbackHom` identifies the two sections, once.

**The generation hypothesis is the only hypothesis.** `IsCompatible` and the statement below
mention no covering family: the family `W` over which the charts are glued is *constructed* in
the proof as `W f = Y_{ψ(f)}`, and the hypotheses `hWle`, `hcover`, `hglue` and `hmatch` of the
existence-side files are discharged there. The generation condition — that the `Y_{ψ(f)}`,
`f ∈ A_d`, cover `Y` — is the source's own hypothesis that `L` is generated by the image of
`ψ|_{A_d}`, in the geometric form Section 27.12 uses it.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Equation 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjChartCocycle
open Stacks.AlgebraicGeometry.ProjChartCocycleMatch
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ProjSectionsUnique (Pair pair_eq eq_of_smul_restrict_eq)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.MorphismToProjUniversal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The first transport: `L ^⊗ 1` and `L` -/

/-- **`L ^⊗ 1 ≅ L`**, the left unitor. The degree-`1` piece of `Γ_*(Y, L)` is `Γ(L ^⊗ 1, ⊤)`,
which is how every statement on the existence side of [Stacks, Tag 01N8] is indexed, while the
isomorphism `α` of the tag goes to `L` itself. This is the only difference, and it is isolated
here. -/
def unitorPow {Y : Scheme.{u}} (L : Y.Modules) : natTensorPow L 1 ≅ L := λ_ L

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L]

/-- **The global section `ψ(f)` of `L`**, for `f` homogeneous of degree `d`: the degree-`1` value
`ψ(f) ∈ Γ(L ^⊗ 1, ⊤)` read in `Γ(L, ⊤)` through the left unitor. -/
def psiSection (ψ : VeroneseSections 𝒜 d L) (f : 𝒜 d) : Γ(L, ⊤) :=
  (unitorPow L).hom.app ⊤ (ψ.pow f.2 1)

/-- **The nonvanishing open of `ψ(f)` does not depend on which of `L ^⊗ 1` and `L` it is read
in.** This is the first transport applied to the nonvanishing opens, by
`Stacks.Ample.nonvanishingLocus_congr`; it is what lets the generation hypothesis and clause (a)
be stated for `L` while the charts are built over `L ^⊗ 1`. -/
theorem nonvanishingOpen_psiSection (ψ : VeroneseSections 𝒜 d L) (f : 𝒜 d) :
    nonvanishingOpen Y L (psiSection 𝒜 ψ f)
      = nonvanishingOpen Y (natTensorPow L 1) (ψ.pow f.2 1) :=
  Opens.ext (Stacks.Ample.nonvanishingLocus_congr (unitorPow L) _)

/-! ### The second transport: the twist degrees `1 * d` and `d` -/

/-- **The transport `φ⁎𝒪_X(k) ≅ φ⁎𝒪_X(d)` along an equality `k = d` of natural numbers.** The
degree-`1` component of `ψ^d_φ` lands in the twist of degree `1 * d`, while the isomorphism `α`
of [Stacks, Tag 01N8] is indexed by `d`; the two naturals are equal but not syntactically so, and
this is the resulting transport. -/
def twistCast (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) {k : ℕ} (hk : k = d) :
    pullbackTwist 𝒜 φ (k : ℤ) ≅ pullbackTwist 𝒜 φ (d : ℤ) :=
  eqToIso (congrArg (fun j : ℕ => pullbackTwist 𝒜 φ (j : ℤ)) hk)

/-- The transport carries the pullback of the degree-`k` section of an element to the pullback of
its degree-`d` section. With `k = d` substituted both the transport and the two readings of the
element become the identity. -/
theorem twistCast_hom_app_degreeSection (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) {k : ℕ}
    (hk : k = d) (x : 𝒜 k) (hx : (x : A) ∈ 𝒜 d) :
    (twistCast 𝒜 φ hk).hom.app ⊤
        (pullbackSectionHom (toProj 𝒜 φ) (twistingSheaf 𝒜 (k : ℤ)) ⊤ ⊤ (by simp)
          (degreeSection 𝒜 k x))
      = pullbackDegreeSection 𝒜 φ ⟨(x : A), hx⟩ := by
  subst hk
  simp [twistCast, pullbackDegreeSection]

/-- **The degree-`1` component of `ψ^d_φ` is the pulled-back degree-`d` section**, after the
transport along `1 * d = d`. The two sides are
`Stacks.AlgebraicGeometry.MorphismsIntoProj.psiPullbackHom` at `n = 1` and
`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.pullbackDegreeSection`: the same construction at
the two spellings of one degree. -/
theorem twistCast_hom_app_psiPullbackHom (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (x : 𝒜 (1 * d))
    (hx : (x : A) ∈ 𝒜 d) :
    (twistCast 𝒜 φ (one_mul d)).hom.app ⊤ (psiPullbackHom 𝒜 φ 1 x)
      = pullbackDegreeSection 𝒜 φ ⟨(x : A), hx⟩ :=
  twistCast_hom_app_degreeSection 𝒜 φ (one_mul d) x hx

/-! ### The preimage of a standard open, for an arbitrary morphism through `U_d` -/

/-- **[Stacks, Tag 01MV] at `n = 1`, as an equivalence.** On the invertible locus `W_d`, the
global section of `𝒪_X(d)` attached to a homogeneous element of degree `d` is nonvanishing
exactly on the standard open of that element.

`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.mem_nonvanishingLocus_degreeSection` is the
implication that was needed there; both directions are needed here, and the degree is carried by
a separate argument `k` with the equation `k = 1 * d` for the same reason — the twist and the
section are indexed by a natural number and `1 * d` is not `d`. -/
@[ega "II 2.6.3" "(f)"]
theorem mem_nonvanishingLocus_degreeSection_iff {k : ℕ} (hk : k = 1 * d) (f : 𝒜 k)
    {x : ProjectiveSpectrum.top 𝒜}
    (hx : x ∈ Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible 𝒜 d) :
    x ∈ Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒜)
        (twistingSheaf 𝒜 (k : ℤ)) (degreeSection 𝒜 k f) ↔
      x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) := by
  subst hk
  exact Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    𝒜 d 1 f hx

/-- The pulled-back degree-`d` section of `f`, in the
`Stacks.NonvanishingPullback.pullbackGlobalSection` spelling. The two differ by the restriction
along `⊤ ⟶ φ ⁻¹ᵁ ⊤`, which is the identity because `φ ⁻¹ᵁ ⊤ = ⊤` by `rfl`. -/
theorem pullbackDegreeSection_eq_pullbackGlobalSection
    (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (f : 𝒜 d) :
    pullbackDegreeSection 𝒜 φ f
      = Stacks.NonvanishingPullback.pullbackGlobalSection (toProj 𝒜 φ)
          (twistingSheaf 𝒜 (d : ℤ)) (degreeSection 𝒜 d f) := by
  change ((Scheme.Modules.pullback (toProj 𝒜 φ)).obj (twistingSheaf 𝒜 (d : ℤ))).presheaf.map
      (eqToHom (show toProj 𝒜 φ ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens) = ⊤ from rfl)).op
      (Stacks.NonvanishingPullback.pullbackGlobalSection (toProj 𝒜 φ)
        (twistingSheaf 𝒜 (d : ℤ)) (degreeSection 𝒜 d f)) = _
  exact Functor.map_id_apply _ _ _

/-- **The preimage of `D₊(f)` under a morphism through `U_d` is the nonvanishing open of the
pulled-back degree-`d` section of `f`** — both inclusions, for an arbitrary morphism and with no
reference to any chart.

`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.le_nonvanishingOpen_pullbackDegreeSection` is
one inclusion. The other uses the same two inputs in the other direction, both of which are
equivalences: [Stacks, Tag 0H78] identifies the nonvanishing locus of a pulled-back section with
the preimage of the nonvanishing locus, and [Stacks, Tag 01MV] identifies the latter with `D₊(f)`
because the image of `φ` lies in `U_d ⊆ W_d`. -/
theorem preimage_basicOpen_eq_nonvanishingOpen
    (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (f : 𝒜 d) :
    toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)
      = nonvanishingOpen Y (pullbackTwist 𝒜 φ (d : ℤ)) (pullbackDegreeSection 𝒜 φ f) := by
  refine le_antisymm (le_nonvanishingOpen_pullbackDegreeSection 𝒜 φ f le_rfl) fun y hy => ?_
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen,
    pullbackDegreeSection_eq_pullbackGlobalSection] at hy
  refine (mem_nonvanishingLocus_degreeSection_iff 𝒜 (one_mul d).symm f
    (degreeOpen_le_whereInvertible 𝒜 d (mem_degreeOpen_toProj 𝒜 φ y))).mp ?_
  exact (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff (toProj 𝒜 φ)
    (twistingSheaf 𝒜 (d : ℤ)) (degreeSection 𝒜 d f) y).mp hy

/-! ### Restricting a chart to a smaller open -/

/-- **The chart over `W`, read into `Proj A`, restricts to the chart over a smaller open.** This
is `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.homOfLE_chart` in the
`chartToProj` spelling, which is the one
`Stacks.AlgebraicGeometry.ProjChartGluing.appLE_awayToSection` consumes. -/
theorem homOfLE_chartToProj (ψ : VeroneseSections 𝒜 d L) {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    {W W' : Y.Opens} (hW : W ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hf 1))
    (h : W' ≤ W) :
    Y.homOfLE h ≫ (ψ.homogeneousRatios hf hW).chartToProj hd
      = (ψ.homogeneousRatios hf (h.trans hW)).chartToProj hd := by
  rw [HomogeneousRatios.chartToProj, HomogeneousRatios.chartToProj, ← Category.assoc,
    HomogeneousRatios.homOfLE_toSpecAway _ hd h _ (ψ.lift_res hf hW hd h)]

/-! ### Compatibility of a pair with `ψ` -/

/-- **`ψ^d_φ` agrees with `ψ` via `α`**, for a pair `p = (φ, α)` as in [Stacks, Tag 01N8]. This
is the commuting square of the tag, written degreewise; see the module's implementation notes for
why degree `1` and the degrees `n > 0` are written in different, equivalent, shapes.

* In degree `1` the square is the identity `α(ψ^d_φ(x)) = ψ(x)` for `x` in the degree-`1` piece
  `A_{1 · d}` of `A^{(d)}`, with the degree-`1` tensor power of `α` trivial. The transport
  `twistCast` moves `ψ^d_φ(x)`, which is indexed by `1 * d`, to the index `d` of `α`, and the
  unitor `unitorPow` moves `ψ(x)`, which lives in `Γ(L ^⊗ 1, ⊤)`, to `Γ(L, ⊤)`.
* In degree `n` it is the source's own local identity `ψ(a)|_V = φ^♯(a/f^n) · ψ(f)^n|_V`, over
  any open `V` mapping into `D₊(f)`, for `f` homogeneous of degree `d` and `a` of degree `nd`.
  Since `ψ(f)^n` is nonvanishing on `V` this determines `φ^♯` on `A_{(f)}`, which is how the
  source defines `φ` and how it proves `φ` unique. -/
def IsCompatible (ψ : VeroneseSections 𝒜 d L) (p : Pair 𝒜 L d) : Prop :=
  (∀ x : 𝒜 (1 * d),
      p.2.hom.app ⊤ ((twistCast 𝒜 p.1 (one_mul d)).hom.app ⊤ (psiPullbackHom 𝒜 p.1 1 x))
        = (unitorPow L).hom.app ⊤ (ψ.toFun 1 x)) ∧
  (∀ (f : 𝒜 d) (V : Y.Opens)
      (hV : V ≤ toProj 𝒜 p.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
      (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) (a : 𝒜 (n * d)), (a : A) = x →
      resTop (natTensorPow L n) (ψ.toFun n a) V
        = (toProj 𝒜 p.1).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) V hV
            (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n x hx))
          • resTop (natTensorPow L n) (ψ.pow f.2 n) V)

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **A compatible `α` carries the pulled-back degree-`d` section of `f` to `ψ(f)`.** This is the
degree-`1` clause of compatibility with the two transports performed, and it is the shape
`Stacks.AlgebraicGeometry.ProjSectionsUnique.iso_eq_of_app_eq` consumes. -/
theorem app_top_pullbackDegreeSection {ψ : VeroneseSections 𝒜 d L} {p : Pair 𝒜 L d}
    (h : IsCompatible 𝒜 ψ p) (f : 𝒜 d) :
    p.2.hom.app ⊤ (pullbackDegreeSection 𝒜 p.1 f) = psiSection 𝒜 ψ f := by
  have hx : (f : A) ∈ 𝒜 (1 * d) := by simp
  have hcompat := h.1 ⟨(f : A), hx⟩
  rw [twistCast_hom_app_psiPullbackHom 𝒜 p.1 ⟨(f : A), hx⟩ f.2] at hcompat
  rw [hcompat, psiSection]
  exact congrArg _ (ψ.toFun_eq_pow f.2 1 ⟨(f : A), hx⟩ (pow_one _).symm)

/-- **Clause (a) of [Stacks, Tag 01N8]: the preimage of `D₊(f)` under a compatible `φ` is
`Y_{ψ(f)}`.** The source establishes this before comparing two pairs; here it is a consequence of
compatibility rather than an extra condition, so the statement of the tag below carries no
hypothesis about preimages.

Two steps, neither of which mentions a chart: the preimage is the nonvanishing open of the
pulled-back degree-`d` section
(`preimage_basicOpen_eq_nonvanishingOpen`), and `α` carries that section to
`ψ(f)`, so the two nonvanishing opens agree
(`Stacks.Ample.nonvanishingLocus_congr`). -/
theorem preimage_basicOpen_eq {ψ : VeroneseSections 𝒜 d L} {p : Pair 𝒜 L d}
    (h : IsCompatible 𝒜 ψ p) (f : 𝒜 d) :
    toProj 𝒜 p.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)
      = nonvanishingOpen Y L (psiSection 𝒜 ψ f) := by
  rw [preimage_basicOpen_eq_nonvanishingOpen 𝒜 p.1 f,
    ← app_top_pullbackDegreeSection 𝒜 h f]
  exact (Opens.ext (Stacks.Ample.nonvanishingLocus_congr p.2 _)).symm

/-- **Two compatible pairs induce the same ring map on the fractions `a/f^n`.** Both values of
`φ^♯` satisfy the local identity `ψ(a)|_{Y_{ψ(f)}} = φ^♯(a/f^n) · ψ(f)^n|_{Y_{ψ(f)}}` with the
same left-hand side, and `ψ(f)^n` is nonvanishing there, so they agree
(`Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_smul_restrict_eq`). This is the hypothesis
`happ` of `Stacks.AlgebraicGeometry.ProjSectionsUnique.pair_eq`. -/
theorem appLE_eq {ψ : VeroneseSections 𝒜 d L} {p q : Pair 𝒜 L d}
    (hp : IsCompatible 𝒜 ψ p) (hq : IsCompatible 𝒜 ψ q) (f : 𝒜 d) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    (toProj 𝒜 p.1).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
        (nonvanishingOpen Y L (psiSection 𝒜 ψ f)) (preimage_basicOpen_eq 𝒜 hp f).ge
        (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n x hx))
      = (toProj 𝒜 q.1).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
        (nonvanishingOpen Y L (psiSection 𝒜 ψ f)) (preimage_basicOpen_eq 𝒜 hq f).ge
        (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n x hx)) := by
  have hmem : x ∈ 𝒜 (n * d) := by simpa [smul_eq_mul] using hx
  refine eq_of_smul_restrict_eq (natTensorPow L n) (ψ.pow f.2 n)
    ((nonvanishingOpen_psiSection 𝒜 ψ f).le.trans (ψ.le_nonvanishingOpen_pow f.2 n))
    (hp.2 f _ (preimage_basicOpen_eq 𝒜 hp f).ge n x hx ⟨x, hmem⟩ rfl)
    (hq.2 f _ (preimage_basicOpen_eq 𝒜 hq f).ge n x hx ⟨x, hmem⟩ rfl)

/-! ### The tag -/

/-- **The classification behind Stacks Tag 01N8, Lemma 27.12.1.** Let `A` be a graded ring,
`X = Proj(A)`, let `d > 0` and let `U_d ⊆ X` be the open of Equation 27.12.0.1. Let `Y` be a
scheme, `L` an invertible `𝒪_Y`-module and `ψ : A^{(d)} → Γ_*(Y, L)` a graded ring map such that
`L` is generated by the global sections `ψ(f)`, `f ∈ A_d` — in the geometric form of Section 27.12,
that their nonvanishing opens cover `Y`. Then there is a morphism `φ : Y ⟶ X` factoring through
`U_d` together with an isomorphism `α : φ⁎𝒪_{U_d}(d) ≅ L` such that `ψ^d_φ` agrees with `ψ` via
`α`, and **the pair `(φ, α)` is unique**.

The pair is `Stacks.AlgebraicGeometry.ProjSectionsUnique.Pair`, the factorization through `U_d`
is built into its first component, and the compatibility is
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible`.

Existence: the family `W f = Y_{ψ(f)}` covers `Y` by the generation hypothesis, the charts of
`ψ` over it glue to `φ` (`Stacks.AlgebraicGeometry.ProjChartCocycle.glued`), the per-chart
trivializations glue to `α` (`Stacks.AlgebraicGeometry.ProjChartCocycleMatch.alphaGlued`), the
degree-`1` compatibility is the normalization of `α`, and the degree-`n` identity is clause (b)
on a chart (`…VeroneseSections.resTop_eq_lift_smul`) together with the identification of `φ^♯`
with the chart's ring map (`…ProjChartGluing.appLE_awayToSection`).

Uniqueness: `Stacks.AlgebraicGeometry.ProjSectionsUnique.pair_eq`, whose preimage hypotheses are
`preimage_basicOpen_eq`, whose `happ` is `appLE_eq` and whose normalization of `α` is
`app_top_pullbackDegreeSection`.

The tag's own statement, with the commuting square `α^{⊗ n}(φ^*(ψ^d(x))) = ψ(x)` on the tensor
powers in every degree `n`, is `Stacks.AlgebraicGeometry.MorphismToProjSquare.existsUnique_square`,
derived from this one. -/
theorem existsUnique_pair (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) :
    ∃! p : Pair 𝒜 L d, IsCompatible 𝒜 ψ p := by
  have hWle : ∀ g : 𝒜 d,
      nonvanishingOpen Y L (psiSection 𝒜 ψ g)
        ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1) :=
    fun g => (nonvanishingOpen_psiSection 𝒜 ψ g).le
  have hpair : IsCompatible 𝒜 ψ
      ⟨glued 𝒜 ψ hd hWle hgen, alphaGlued 𝒜 ψ hd hWle hgen ≪≫ unitorPow L⟩ := by
    refine ⟨fun x => ?_, fun f V hV n y hy a hay => ?_⟩
    · rw [twistCast_hom_app_psiPullbackHom 𝒜 _ x (by simpa using x.2), Iso.trans_hom,
        Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
        alphaGlued_hom_app_top 𝒜 ψ hd hWle hgen ⟨(x : A), by simpa using x.2⟩]
      exact congrArg _ (ψ.toFun_eq_pow (by simpa using x.2) 1 x (pow_one _).symm).symm
    · have hVle : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow f.2 1) :=
        hV.trans (preimage_basicOpen_glued 𝒜 ψ hd hWle hgen f).le
      have hVW : V ≤ nonvanishingOpen Y L (psiSection 𝒜 ψ f) :=
        hVle.trans (nonvanishingOpen_psiSection 𝒜 ψ f).ge
      have hPhi : V.ι ≫ toProj 𝒜 (glued 𝒜 ψ hd hWle hgen)
          = (ψ.homogeneousRatios f.2 hVle).chartToProj hd := by
        rw [← Y.homOfLE_ι hVW, Category.assoc,
          ι_comp_toProj 𝒜 ψ hd hWle (ι_glued 𝒜 ψ hd hWle hgen) f,
          homOfLE_chartToProj 𝒜 ψ f.2 hd (hWle f) hVW]
      rw [ProjChartGluing.appLE_awayToSection (ψ.homogeneousRatios f.2 hVle) hd hPhi hV]
      exact ψ.resTop_eq_lift_smul f.2 hVle hd n y hy a hay
  refine ⟨_, hpair, fun q hq => ?_⟩
  exact pair_eq 𝒜 hd q _ (preimage_basicOpen_eq 𝒜 hq) (preimage_basicOpen_eq 𝒜 hpair)
    (fun f n x hx => appLE_eq 𝒜 hq hpair f n x hx) hgen
    (m := fun ξ g => pullbackDegreeSection 𝒜 ξ g)
    (app_top_pullbackDegreeSection 𝒜 hq) (app_top_pullbackDegreeSection 𝒜 hpair)

end Stacks.AlgebraicGeometry.MorphismToProjUniversal

end
