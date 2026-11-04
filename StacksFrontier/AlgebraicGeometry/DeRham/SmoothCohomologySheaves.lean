module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham cohomology sheaves of a smooth morphism

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and smooth morphism of schemes over a base
`S`, with `g : Y ⟶ S` the structure morphism of the target. [Stacks, Tag 0FMM] produces a
bounded spectral sequence with first page

`E_1^{p, q} = H^q(Ω^p_{Y/S} ⊗^{\mathbf L}_{𝒪_Y} Rf_*Ω^•_{X/Y})`

abutting to `R^{p + q}f_*Ω^•_{X/S}`. The remark [Stacks, Tag 0FMN] annotates that spectral
sequence. It names the cohomology sheaves

`ℋ^q_dR(X/Y) = H^q(Rf_*Ω^•_{X/Y})`

of the derived direct image of the relative de Rham complex of `X` over `Y`, and observes that
when these are flat `𝒪_Y`-modules the first page simplifies to
`Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`, the derived tensor product being replaced by the ordinary one.
This file defines both sheaves — `ℋ^q_dR(X/Y)` and the flat-case first page — and reduces the
identification of the two first pages to one general statement about derived tensor products on
`Y`, which is the step the source omits.

## Main definitions

* `Stacks.DeRhamSmooth.deRhamCohomologySheaf`: **`ℋ^q_dR(X/Y) = H^q(Rf_*Ω^•_{X/Y})`**, the `q`-th
  cohomology sheaf of the derived direct image of the relative de Rham complex of `X` over `Y`,
  a sheaf of `𝒪_Y`-modules.
* `Stacks.DeRhamSmooth.deRhamFirstPageFlat`: **`Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`**, the first page
  of Tag 0FMM as the remark writes it in the flat case, read as a sheaf of `g^{-1}𝒪_S`-modules
  by restriction of scalars along `g^{-1}𝒪_S ⟶ 𝒪_Y`, exactly as
  `Stacks.DeRhamSmooth.deRhamFirstPage` is.
* `Stacks.DeRhamSmooth.FlatDegenerateDerivedTensor`: the statement the source omits, as data —
  for every `𝒪_Y`-module `M` and every object `K` of `D(𝒪_Y)` all of whose cohomology sheaves
  are flat, an identification `H^t(M ⊗^{\mathbf L}_{𝒪_Y} K) ≅ M ⊗_{𝒪_Y} H^t(K)`.

## Main results

* `Stacks.DeRhamSmooth.deRhamFirstPageIsoFlat`: granted
  `FlatDegenerateDerivedTensor` and the flatness of the `ℋ^q_dR(X/Y)`, the first page of Tag
  0FMM is `Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`.
* `Stacks.DeRhamSmooth.exists_boundedDeRhamSpectralSequence_flat`: the spectral sequence of Tag
  0FMM with its first page written that way.

## Implementation notes

**What this file does and does not prove, and why.** Of the three assertions of Tag 0FMN, only
the first is formalized outright: the definition of `ℋ^q_dR(X/Y)`.

* The remark's claim that `ℋ^q_dR(X/Y)` is finite locally free when `f` is in addition proper
  and `S` is a scheme over `Q` is **not stated anywhere below, and not assumed anywhere below**.
  The source defers its proof to a reference it does not supply — the text reads "insert future
  reference here" — so there is nothing to formalize: a Lean statement of it would be a claim
  this development cannot discharge and the source does not either. It is recorded here only as
  a hole on the source's side.
* The simplification of the first page in the flat case is the step the source marks "tiny
  argument omitted", and the argument is not tiny in the library as it stands. On paper it is
  the collapse of the hyper-Tor spectral sequence
  `E_2^{s, t} = Tor_{-s}^{𝒪_Y}(M, H^t(K)) ⟹ H^{s + t}(M ⊗^{\mathbf L}_{𝒪_Y} K)`
  of Tag 0662: flatness of every `H^t(K)` kills the columns `s ≠ 0` and leaves
  `H^t(M ⊗^{\mathbf L}_{𝒪_Y} K) = M ⊗_{𝒪_Y} H^t(K)`. That spectral sequence exists in this
  library for modules over a commutative ring — it is
  `exists_derived_tensor_spectral_sequences` of
  `StacksFrontier/Algebra/Homology/SpectralSequence/DerivedTensor.lean`
  — and **not for sheaves of modules on a ringed space**, which is where the derived tensor
  product `Stacks.Cohomology.TorAmplitude.derTensor` of Tag 06YU lives and where this page
  is computed. Nothing weaker suffices: the Tor contributions that must vanish come from
  cohomology in arbitrarily high degrees, so no induction over the canonical truncations of `K`
  closes the gap, and flatness of the cohomology sheaves does not make a bounded-below complex
  of flat modules out of `K`. The step is therefore isolated as the single hypothesis
  `FlatDegenerateDerivedTensor`, stated for an arbitrary module and an arbitrary object of
  `D(𝒪_Y)` so that it is a general lemma about derived tensor products rather than a restatement
  of the conclusion it is used for, in the same way that Tag 0FMM takes its graded-piece
  identification `hgr` as a hypothesis.
* The remark's last assertion — that `d_1^{0, q}` is an integrable connection `∇`, the
  Gauss--Manin connection, and that `d_1^{•, q}` is the de Rham complex of `∇` — presupposes
  the flat-case identification, since the differentials in question are those of the spectral
  sequence read through it. It is not reached here.

Accordingly the `@[stacks 0FMN]` attributes below are suffixed: one names the cohomology sheaves
and one names the module `Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`. Neither is a bare tag, because the
remark is not covered.

**The spellings.** `deRhamFirstPageFlat` is the restriction of scalars along `g^{-1}𝒪_S ⟶ 𝒪_Y`
of an `𝒪_Y`-module, which is how `Stacks.DeRhamSmooth.deRhamFirstPage` reads its own first page;
the two are therefore objects of the same category and an isomorphism between them is a
statement about the spectral sequence of Tag 0FMM. The underived tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor` of Tag 06YM, the bifunctor the derived tensor product
of Tag 06YU is the derived functor of, so no second tensor product is introduced; flatness is
`AlgebraicGeometry.SheafOfModules.IsFlat`, part (3) of Tag 03ER. `ℋ^q_dR(X/Y)` is read with
`CategoryTheory.DerivedCategory.Plus.homologyFunctor`, because
`Stacks.DeRhamDirectImage.derivedDeRhamDirectImage` lands in `D⁺(𝒪_Y)`; along the inclusion
`D⁺(𝒪_Y) ⟶ D(𝒪_Y)` the cohomology functors agree, which is what lets the flatness hypothesis
below be handed to `FlatDegenerateDerivedTensor` unchanged.

`FlatDegenerateDerivedTensor` is `Type`-valued rather than `Prop`-valued: it carries the
isomorphisms themselves, so that the identification of the first pages is an isomorphism and not
the assertion that one exists.

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, whose priority
is raised for the file, matching `StacksFrontier/AlgebraicGeometry/DeRham/SmoothSpectralSequence.lean`
and `StacksFrontier/AlgebraicGeometry/DeRham/DerivedDirectImage.lean`: the locally small model
arrives with the imports as a competing instance of the same priority, and the objects used here
are baked at the standard one.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FLX](https://stacks.math.columbia.edu/tag/0FLX)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.FilteredComplex Stacks.DeRhamDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

section Degeneration

variable (Y : Scheme.{u})

/-- **The step Tag 0FMN omits, as data.** For every `𝒪_Y`-module `M` and every object `K` of
`D(𝒪_Y)` whose cohomology sheaves are all flat `𝒪_Y`-modules, an identification

`H^t(M ⊗^{\mathbf L}_{𝒪_Y} K) ≅ M ⊗_{𝒪_Y} H^t(K)`

for every `t`: the derived tensor product with `M` may be computed termwise on cohomology.

On paper this is the collapse of the hyper-Tor spectral sequence
`E_2^{s, t} = Tor_{-s}^{𝒪_Y}(M, H^t(K))` of Tag 0662, whose columns `s ≠ 0` vanish by the
flatness hypothesis. That spectral sequence is available in this library over a commutative ring
and not over a ringed space, so the statement is isolated here rather than proved; see the
implementation notes. It is stated for an arbitrary `M` and an arbitrary `K`, and so is a
general statement about the derived tensor product of Tag 06YU, not a restatement of the
first-page identification it is used for below. -/
abbrev FlatDegenerateDerivedTensor : Type (u + 1) :=
  ∀ (M : Y.Modules) (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace)),
    (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
        ((DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) i).obj K)) →
    ∀ t : ℤ,
      (DerivedCategory.homologyFunctor
            (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) t).obj
          (((Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).tensor.obj
              ((DerivedCategory.singleFunctor
                (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) 0).obj M)).obj K) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj M).obj
          ((DerivedCategory.homologyFunctor
            (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) t).obj K)

end Degeneration

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **`ℋ^q_dR(X/Y) = H^q(Rf_*Ω^•_{X/Y})`**, the `q`-th de Rham cohomology sheaf of `X` over `Y`:
the `q`-th cohomology sheaf of the derived direct image along `f` of the relative de Rham complex
of `X` over `Y`, a sheaf of `𝒪_Y`-modules.

The derived direct image is `Stacks.DeRhamDirectImage.derivedDeRhamDirectImage`, an object of
`D⁺(𝒪_Y)`, so the cohomology is read with the cohomology functors of `D⁺`; along the inclusion
of `D⁺(𝒪_Y)` into `D(𝒪_Y)` these agree with the cohomology functors of `D(𝒪_Y)`. By
[Stacks, Tag 0FLX] — `Stacks.DeRhamDirectImage.isQuasicoherent_homology_derivedDeRhamDirectImage`
— these sheaves are quasi-coherent whenever `f` is quasi-compact and quasi-separated. -/
@[stacks 0FMN "the cohomology sheaves ℋ^q_dR(X/Y) = H^q(Rf_*Ω^•_{X/Y})",
  sga "7 XXII 3.3" "more general"]
def deRhamCohomologySheaf (q : ℤ) : Y.Modules :=
  (DerivedCategory.Plus.homologyFunctor Y.Modules q).obj (derivedDeRhamDirectImage f)

/-- **`Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`**, the module the remark [Stacks, Tag 0FMN] writes the
first page of the spectral sequence of [Stacks, Tag 0FMM] as when the `ℋ^q_dR(X/Y)` are flat:
the ordinary — not derived — tensor product over `𝒪_Y` of the sheaf `Ω^p_{Y/S}` of relative
`p`-forms of `Y` over `S` with the `q`-th de Rham cohomology sheaf of `X` over `Y`, read as a
sheaf of `g^{-1}𝒪_S`-modules by restriction of scalars along `g^{-1}𝒪_S ⟶ 𝒪_Y`.

The restriction of scalars is the one `Stacks.DeRhamSmooth.deRhamFirstPage` uses, so this module
and `deRhamFirstPage f g p q` are objects of the same category; `deRhamFirstPageIsoFlat` is the
isomorphism between them, granted the hypotheses the source does not discharge. -/
@[stacks 0FMN "the module Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y) of the flat case"]
def deRhamFirstPageFlat (p q : ℤ) : Modules (inverseImageBase g) :=
  (pushforward (toInverseImageBase g)).obj
    (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
      (Scheme.Hom.relativeDifferentialForms g p)).obj (deRhamCohomologySheaf f q))

/-- **The first page of [Stacks, Tag 0FMM] in the flat case of [Stacks, Tag 0FMN].** If the de
Rham cohomology sheaves `ℋ^q_dR(X/Y)` are flat `𝒪_Y`-modules then

`H^q(Ω^p_{Y/S} ⊗^{\mathbf L}_{𝒪_Y} Rf_*Ω^•_{X/Y}) ≅ Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`,

the derived tensor product of the first page being replaced by the ordinary one.

The hypothesis `d` is the step the source marks "tiny argument omitted", stated once for an
arbitrary module and an arbitrary object of `D(𝒪_Y)`; it is not proved here, and the
implementation notes name what is missing. What is proved here is that the specific first page
of Tag 0FMM is the instance of it at `M = Ω^p_{Y/S}` and `K = Rf_*Ω^•_{X/Y}`: the flatness
hypothesis on `ℋ^q_dR(X/Y)`, which is read in `D⁺(𝒪_Y)`, is the flatness of the cohomology
sheaves of the image of `Rf_*Ω^•_{X/Y}` in `D(𝒪_Y)`, and the restriction of scalars along
`g^{-1}𝒪_S ⟶ 𝒪_Y` is applied to the resulting isomorphism of `𝒪_Y`-modules. -/
def deRhamFirstPageIsoFlat (d : FlatDegenerateDerivedTensor Y)
    (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (deRhamCohomologySheaf f q)) (p q : ℤ) :
    deRhamFirstPage f g p q ≅ deRhamFirstPageFlat f g p q :=
  (pushforward (toInverseImageBase g)).mapIso
    (d (Scheme.Hom.relativeDifferentialForms g p)
      (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f)) (fun i => hflat i) q)

/-- **The spectral sequence of [Stacks, Tag 0FMM] with the first page of [Stacks, Tag 0FMN].**
Under the hypotheses of Tag 0FMM — the filtration `K` of `Ω^•_{X/S}` by the forms pulled back
from `Y`, its exhaustion `hexh`, the eventual vanishing `hvanish` of the higher direct images of
its far steps, and the identification `hgr` of `R^{p + q}f_*gr^pK` with the first page — if in
addition the de Rham cohomology sheaves `ℋ^q_dR(X/Y)` are flat `𝒪_Y`-modules, the bounded
spectral sequence abutting to `R^{p + q}f_*Ω^•_{X/S}` has

`E_1^{p, q} = Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`.

This is `Stacks.DeRhamSmooth.exists_boundedDeRhamSpectralSequence` composed with
`deRhamFirstPageIsoFlat`, so it carries the latter's hypothesis `d`: the argument the source
omits is not supplied. The attribute is therefore withheld. -/
theorem exists_boundedDeRhamSpectralSequence_flat
    [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (K : CochainComplex.Filtered
      (SheafOfModules.{u} (structureSheafRing (inverseImageBase (f ≫ g)))))
    (hKX : K.X = deRhamCochainComplex (f ≫ g))
    (hexh : ∀ p : ℤ, p ≤ 0 → IsIso (K.filtration.ι.app (op p)))
    (hvanish : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (higherDirectImage (derivedRelativePushforward f g)
        (K.filtration.obj (op p)) n))
    (hgr : ∀ p q : ℤ, Nonempty (higherDirectImage (derivedRelativePushforward f g)
      ((FilteredObject.gr p).obj K) (p + q) ≅ deRhamFirstPage f g p q))
    (d : FlatDegenerateDerivedTensor Y)
    (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (deRhamCohomologySheaf f q)) :
    ∃ E : CohomologicalSpectralSequence
        (SheafOfModules.{u} (structureSheafRing (inverseImageBase g))) 1,
      _root_.IsBounded E ∧
      (∀ p q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ deRhamFirstPageFlat f g p q)) ∧
      SpectralSequence.AbutsTo E (fun n => deRhamHigherDirectImage f g n) := by
  obtain ⟨E, hbdd, hpage, habuts⟩ :=
    exists_boundedDeRhamSpectralSequence f g K hKX hexh hvanish hgr
  exact ⟨E, hbdd, fun p q => ⟨(hpage p q).some ≪≫ deRhamFirstPageIsoFlat f g d hflat p q⟩,
    habuts⟩

end Stacks.DeRhamSmooth

end
