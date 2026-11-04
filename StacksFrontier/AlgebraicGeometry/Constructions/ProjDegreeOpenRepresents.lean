module

public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjUniversal

/-!
# `U_d` represents the functor of triples, and its universal family

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)`, let `d ≥ 1` and let
`U_d = ⋃_{f ∈ 𝒜 d} D₊(f) ⊆ X` be the open of Equation 27.12.0.1. Section 27.12 attaches to a
scheme `Y` the set `F_d(Y)` of strict equivalence classes of triples `(d, L, ψ)` — an invertible
`𝒪_Y`-module `L` together with a graded ring map `ψ : A^{(d)} ⟶ Γ_*(Y, L)` whose degree-`d` part
generates `L` — and [Stacks, Tag 01N9] states that `U_d` represents `F_d`, with
`(d, 𝒪_{U_d}(d), ψ^d)` the universal family. Its proof is the one sentence *"this is a
reformulation of Lemma 27.12.1"*, i.e. of [Stacks, Tag 01N8].

This file carries out that reformulation and puts the universal family on `U_d`.

* **Representability.** Unwinding "`U_d` represents `F_d` with universal family
  `(d, 𝒪_{U_d}(d), ψ^d)`" gives: for every scheme `Y` and every triple `(L, ψ)` over `Y` there is
  **one and only one** morphism `φ : Y ⟶ U_d` whose pullback of the universal family is strictly
  equivalent to `(L, ψ)` — that is, for which *some* isomorphism
  `α : φ⁎𝒪_{U_d}(d) ≅ L` identifies `ψ^d_φ` with `ψ`. Surjectivity of
  `Mor(Y, U_d) → F_d(Y)` is the existence of `φ`, injectivity is its uniqueness. [Stacks, Tag
  01N8] gives the unique *pair* `(φ, α)`; the morphism alone is then unique because a pair is
  determined by its first component together with the compatibility.
* **The universal family.** `𝒪_{U_d}(d)` is an invertible `𝒪_{U_d}`-module and the degree-one
  values `ψ^d(f)`, `f ∈ 𝒜 d`, generate it: their nonvanishing opens cover `U_d`. So
  `(d, 𝒪_{U_d}(d), ψ^d)` is a family of the kind `F_d` classifies, which is what makes the
  statement above a statement about pulling the universal family back.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents.universalTwist` — **`𝒪_{U_d}(d)`**, the
  invertible module of the universal family, as the value at `φ = 𝟙` of the family `φ⁎𝒪_{U_d}(d)`
  whose pullbacks the representability statement compares against.
* `Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents.universalSection` — **`ψ^d(f)`**, the
  degree-one value of `ψ^d` on a homogeneous element of degree `d`, i.e. the global section of
  `𝒪_X(d)` attached to it, restricted to `U_d`.

## Main results

* `Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents.iSup_nonvanishingOpen_universalSection_eq_top`
  — **the universal family of [Stacks, Tag 01N9]**: `𝒪_{U_d}(d)` is invertible on `U_d` and its
  degree-one sections generate it. Invertibility is the instance
  `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.isInvertibleModule_pullbackTwist` at `φ = 𝟙`.
* `Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents.existsUnique_hom` — **`U_d` represents
  `F_d`**: a unique morphism `Y ⟶ U_d` for each triple over `Y`.

## Implementation notes

**Why the statement quantifies over triples and not over their classes.** `F_d(Y)` is the set of
strict equivalence classes, and representability says that `Mor(Y, U_d) → F_d(Y)` is bijective.
The statement `existsUnique_hom` quantifies over a *representative* `(L, ψ)` instead, which is
the stronger reading: it asserts a unique `φ` for each triple, hence in particular for each
class. No quotient is formed, and no choice of representative is made.

**What "the pullback of the universal family is strictly equivalent to `(L, ψ)`" is.** It is
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible`, the condition of [Stacks, Tag
01N8] that `α` identify `ψ^d_φ` with `ψ`; `ψ^d_φ` is by construction the pullback along `φ` of
`ψ^d`, so a compatible `α` is exactly a strict equivalence between `φ⁎(d, 𝒪_{U_d}(d), ψ^d)` and
`(d, L, ψ)`. `IsCompatible` writes that square degreewise, in degree one as it stands and in
higher degrees in the local form `ψ(a)|_V = φ^♯(a/f^n) · ψ(f)^n|_V` the source's own proof
establishes; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Constructions/MorphismToProjUniversal.lean` for why, and the
attribute below for the resulting caveat, which is inherited verbatim from [Stacks, Tag 01N8].

**Why the universal family is written at `φ = 𝟙`.** The triple whose pullbacks the
representability statement compares against is the family `(φ⁎𝒪_{U_d}(d), ψ^d_φ)`; at `φ = 𝟙`
that family *is* `(𝒪_{U_d}(d), ψ^d)`, because `ψ^d_φ` is defined as the pullback along
`φ ≫ U_d.ι` of the canonical graded map and `𝟙 ≫ U_d.ι = U_d.ι`. Writing the universal family
this way rather than through a second restriction functor keeps the two clauses below literally
about the objects the representability statement mentions, with `toProj_id` the only
bookkeeping.

**What is not here.** The graded ring map `ψ^d : A^{(d)} ⟶ Γ_*(U_d, 𝒪_{U_d}(d))` itself, as a
single map into the graded section ring of the *tensor powers* of `𝒪_{U_d}(d)`, is not available:
`Stacks.AlgebraicGeometry.ProjDegreeOpenSections.psi` is the same map with `⨁_n Γ(U_d, 𝒪(nd))` as
its target, and identifying the two needs the graded-*ring* upgrade of
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat`. **That upgrade is available**,
since it rests on associativity of the canonical twist multiplication maps at the level of
sheaves of modules: the sheaf-level associativity is
`Stacks.AlgebraicGeometry.ThetaMul.twistMulIso_assoc`, hypothesis-free for arbitrary integers, and
the multiplicativity of `thetaNat` in every bidegree of natural numbers is
`Stacks.AlgebraicGeometry.ThetaMul.thetaNat_mul`. The identification of the two targets is
therefore within reach, and the corresponding identification on the *abstract* tensor powers
— `(L ^⊗ d) ^⊗ n ≅ L ^⊗ (n d)` together with its multiplicativity — is
`Stacks.GradedSections.powPowIso` and `Stacks.GradedSections.ofPowPow_mul`, out of which
`Stacks.AlgebraicGeometry.ProjChartFromRatios.sectionRingVeronese` builds the first
`VeroneseSections` datum in this development. Assembling `ψ^d` itself is still not done here. The
clauses below therefore record the universal family through its degree-one data —
the invertibility of `𝒪_{U_d}(d)` and the generation by the sections `ψ^d(f)`, `f ∈ 𝒜 d` — which
is exactly the data the triple's generation condition is about, and the comparison with a general
triple is made by `IsCompatible` degreewise rather than through that single graded map.

## References

* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Equation 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u w

namespace Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### The universal family on `U_d` -/

section UniversalFamily

variable (d : ℕ)

/-- **`𝒪_{U_d}(d)`, the invertible module of the universal family of [Stacks, Tag 01N9].** It is
written as the value at the identity of `φ ↦ φ⁎𝒪_{U_d}(d)`, the family whose pullbacks the
representability statement compares a triple against. -/
abbrev universalTwist : (degreeOpen 𝒜 d).toScheme.Modules :=
  pullbackTwist 𝒜 (𝟙 (degreeOpen 𝒜 d).toScheme) (d : ℤ)

/-- **`ψ^d(f)`, the degree-one value of the universal family's graded map** on a homogeneous
element `f` of degree `d`: the global section of `𝒪_X(d)` attached to `f` by Equation 27.10.1.2,
restricted to `U_d`. -/
abbrev universalSection (f : 𝒜 d) : Γ(universalTwist 𝒜 d, ⊤) :=
  pullbackDegreeSection 𝒜 (𝟙 (degreeOpen 𝒜 d).toScheme) f

/-- The morphism into `Proj A` underlying the identity of `U_d` is the open immersion `U_d ⟶ X`.
This is the only bookkeeping the universal family needs. -/
theorem toProj_id : toProj 𝒜 (𝟙 (degreeOpen 𝒜 d).toScheme) = (degreeOpen 𝒜 d).ι :=
  Category.id_comp _

/-- **The universal family of [Stacks, Tag 01N9] is generated in degree one.** The nonvanishing
open of `ψ^d(f)` on `U_d` is the preimage of `D₊(f)` under the open immersion `U_d ⟶ X`
(`Stacks.AlgebraicGeometry.MorphismToProjUniversal.preimage_basicOpen_eq_nonvanishingOpen`, which
is [Stacks, Tag 01MV] together with [Stacks, Tag 0H78]), and those preimages cover `U_d` because
the `D₊(f)`, `f ∈ 𝒜 d`, are what `U_d` is the union of. So `𝒪_{U_d}(d)` is generated by the
global sections `ψ^d(f)`, in the geometric form Section 27.12 uses that condition. -/
@[stacks 01N9 "the universal family (d, 𝒪_{U_d}(d), ψ^d): the degree-one values ψ^d(f), f ∈ A_d, \
generate 𝒪_{U_d}(d), their nonvanishing opens covering U_d"]
theorem iSup_nonvanishingOpen_universalSection_eq_top :
    (⨆ f : 𝒜 d, nonvanishingOpen (degreeOpen 𝒜 d).toScheme (universalTwist 𝒜 d)
      (universalSection 𝒜 d f)) = ⊤ := by
  calc (⨆ f : 𝒜 d, nonvanishingOpen (degreeOpen 𝒜 d).toScheme (universalTwist 𝒜 d)
        (universalSection 𝒜 d f))
      = ⨆ f : 𝒜 d, toProj 𝒜 (𝟙 (degreeOpen 𝒜 d).toScheme) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) :=
        iSup_congr fun f => (preimage_basicOpen_eq_nonvanishingOpen 𝒜 _ f).symm
    _ = toProj 𝒜 (𝟙 (degreeOpen 𝒜 d).toScheme) ⁻¹ᵁ degreeOpen 𝒜 d := by
        rw [← Scheme.Hom.preimage_iSup]
        rfl
    _ = ⊤ := by rw [toProj_id]; exact Scheme.Opens.ι_preimage_self _

end UniversalFamily

/-! ### `U_d` represents `F_d` -/

section Represents

variable {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]

/-- **Stacks Tag 01N9, Lemma 27.12.2.** Let `A` be a graded ring, `X = Proj(A)`, let `d > 0` and
let `U_d ⊆ X` be the open of Equation 27.12.0.1. The open subscheme `U_d` **represents the
functor `F_d`**, the triple `(d, 𝒪_{U_d}(d), ψ^d)` being the universal family: for a scheme `Y`
and a triple `(d, L, ψ)` over `Y` — an invertible `𝒪_Y`-module `L` and a graded map
`ψ : A^{(d)} ⟶ Γ_*(Y, L)` whose degree-`d` part generates `L`, in the geometric form that the
nonvanishing opens of the sections `ψ(f)`, `f ∈ A_d`, cover `Y` — there is **one and only one**
morphism `φ : Y ⟶ U_d` for which the pullback `φ⁎(d, 𝒪_{U_d}(d), ψ^d)` of the universal family is
strictly equivalent to `(d, L, ψ)`, i.e. for which some isomorphism
`α : φ⁎𝒪_{U_d}(d) ≅ L` identifies `ψ^d_φ` with `ψ`.

That is the bijection `Mor(Y, U_d) ≅ F_d(Y)`: the existence of `φ` is its surjectivity and the
uniqueness of `φ` its injectivity, the map being `φ ↦ [φ⁎(d, 𝒪_{U_d}(d), ψ^d)]`.

The source's proof is *"this is a reformulation of Lemma 27.12.1"*, and so is this one:
[Stacks, Tag 01N8] (`Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair`) gives a
unique *pair* `(φ, α)`, and a pair is its first component together with the compatibility, so the
morphism is unique among those admitting a compatible `α`. -/
@[stacks 01N9 "U_d represents F_d, with (d, 𝒪_{U_d}(d), ψ^d) the universal family: a unique \
morphism Y ⟶ U_d for every triple over Y. The strict equivalence between the pullback of the \
universal family and the given triple is IsCompatible, whose degree-n clause for n ≥ 2 is the \
source's local identity ψ(a)|_V = φ♯(a/f^n)·ψ(f)^n|_V rather than the tensor-power square \
α^{⊗n}(ψ^d_φ(x)) = ψ(x); the square implies it, so the uniqueness assertion is at least as \
strong as the source's, and the caveat is inherited verbatim from Tag 01N8. Degree 1 is the \
square itself. The source quantifies over strict equivalence classes; this statement quantifies \
over representatives, which is stronger."]
theorem existsUnique_hom (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) :
    ∃! φ : Y ⟶ (degreeOpen 𝒜 d).toScheme,
      ∃ α : pullbackTwist 𝒜 φ (d : ℤ) ≅ L, IsCompatible 𝒜 ψ ⟨φ, α⟩ := by
  obtain ⟨p, hp, huniq⟩ := existsUnique_pair 𝒜 hd ψ hgen
  refine ⟨p.1, ⟨p.2, hp⟩, ?_⟩
  rintro φ ⟨α, hα⟩
  exact congrArg Sigma.fst (huniq ⟨φ, α⟩ hα)

end Represents

end Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents

end
