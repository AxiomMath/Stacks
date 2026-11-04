module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteTypesComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiLocalTypesComparison
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteFinitePresentationAgreement
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteIff
import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentation across `𝓕 ↦ 𝓕^a`, in the sense of Modules on Sites, Definition 03DL (7)

Let `S` be a scheme and `𝓕` a quasi-coherent `𝒪_S`-module.  Descent, Lemma 05VG says that the
equivalences `QCoh(𝒪_S) ⟶ QCoh((Sch/S)_τ, 𝒪)` and `QCoh(𝒪_S) ⟶ QCoh(S_τ, 𝒪)`,
`𝓕 ↦ 𝓕^a`, of Descent, Proposition 03DX preserve and reflect the properties of modules of
Modules on Sites, Definitions 03DE, 03DL and 03ER.  For the property "of finite presentation",
Definition 03DL (7), this reads: `𝓕` is of finite presentation if and only if `𝓕^a` is of finite
presentation as an `𝒪`-module.

Definition 03DL (7) on a ringed site `(𝒞, 𝒪)`: a sheaf of `𝒪`-modules `𝓖` is of finite
presentation if for every object `U` of `𝒞` there is a covering `{Uᵢ ⟶ U}` such that each
restriction `𝓖|_{𝒞/Uᵢ}` has a finite global presentation.  This is
`SheafOfModules.IsFinitePresentationOnSite`, and it is the predicate used on both sides below:
on the left for `𝓕` on the site of opens of `S` with the structure sheaf `𝒪_S`, the ringed site
of the ringed space `(S, 𝒪_S)`, and on the right for `𝓕^a` on the site in question.

The sites and functors are those of Proposition 03DX:

* the big site `(Sch/S)_τ` for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, with
  `𝓕^a = (AlgebraicGeometry.BigFppfOver.baseAssociatedModule B S hS τ).obj 𝓕`;
* the small Zariski site `S_Zar`, with `AlgebraicGeometry.SmallZariski.associatedModule`;
* the small étale site `S_étale`, with `AlgebraicGeometry.SmallEtale.associatedModule`;
* the small site `S_τ` for `τ ∈ {smooth, syntomic, fppf}`, with
  `AlgebraicGeometry.SmallFlatSite.associatedModule`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isFinitePresentationOnSite_baseAssociatedModule_iff`: the big
  site `(Sch/S)_τ`, every `τ`.
* `AlgebraicGeometry.SmallZariski.isFinitePresentationOnSite_iff_associatedModule`: `S_Zar`.
* `AlgebraicGeometry.SmallEtale.isFinitePresentationOnSite_iff_associatedModule`: `S_étale`.
* `AlgebraicGeometry.SmallFlatSite.isFinitePresentationOnSite_iff_associatedModule`: `S_τ` for
  `τ ∈ {smooth, syntomic, fppf}`.
* `AlgebraicGeometry.Scheme.Modules.isFinitePresentationOnSite_iff_associatedModule`: all of the
  above in one statement.

## Implementation notes

Each statement is obtained from the corresponding statement for Mathlib's
`SheafOfModules.IsFinitePresentation`, which asks for a single family covering the final object
on whose members the module has a finite presentation by free modules; that is the
characterization of Modules on Sites, Lemma 03DN, rather than Definition 03DL (7) itself.  The
two conditions agree on every site,
`SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation`, and the theorems here are
those statements read on both sides through that agreement.

Quasi-coherence of `𝓕` is the hypothesis of the source, which states the lemma for the
equivalences on quasi-coherent modules.  The forward implications do not use it, and on the
small Zariski site neither implication does, so that statement is made for every `𝒪_S`-module.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG for "of finite presentation" (Modules on Sites, Definition 03DL (7)),
on the big site `(Sch/S)_τ`, for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  A
quasi-coherent `𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite
presentation as an `𝒪`-module on `(Sch/S)_τ`, where `𝓕 ↦ 𝓕^a` is the functor of Descent,
Proposition 03DX (1). -/
@[stacks 05VG "of finite presentation (03DL (7)), on (Sch/S)_τ for every τ ∈ {Zariski, étale, \
smooth, syntomic, fppf}, at the functor 𝓕 ↦ 𝓕ᵃ of 03DX"]
theorem isFinitePresentationOnSite_baseAssociatedModule_iff (τ : SiteKind) (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      ((baseAssociatedModule B S hS τ).obj 𝓕).IsFinitePresentationOnSite :=
  (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).trans
    ((isFinitePresentation_baseAssociatedModule_iff B S hS τ 𝓕).trans
      (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).symm)

end BigFppfOver

namespace SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG for "of finite presentation" (Modules on Sites, Definition 03DL (7)),
on the small Zariski site `S_Zar`.**  An `𝒪_S`-module `𝓕` is of finite presentation if and
only if `𝓕^a` is of finite presentation as an `𝒪`-module on `S_Zar`, where `𝓕 ↦ 𝓕^a` is the
functor of Descent, Proposition 03DX (2).  On this site no quasi-coherence is needed. -/
@[stacks 05VG "of finite presentation (03DL (7)), on S_Zar, at the functor 𝓕 ↦ 𝓕ᵃ of 03DX"]
theorem isFinitePresentationOnSite_iff_associatedModule (𝓕 : S.Modules) :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      ((associatedModule B S hS).obj 𝓕).IsFinitePresentationOnSite :=
  (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).trans
    ((isFinitePresentation_iff_associatedModule B S hS 𝓕).trans
      (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).symm)

end SmallZariski

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG for "of finite presentation" (Modules on Sites, Definition 03DL (7)),
on the small étale site `S_étale`.**  A quasi-coherent `𝒪_S`-module `𝓕` is of finite
presentation if and only if `𝓕^a` is of finite presentation as an `𝒪`-module on `S_étale`, where
`𝓕 ↦ 𝓕^a` is the functor of Descent, Proposition 03DX (2). -/
@[stacks 05VG "of finite presentation (03DL (7)), on S_étale, at the functor 𝓕 ↦ 𝓕ᵃ of 03DX"]
theorem isFinitePresentationOnSite_iff_associatedModule (𝓕 : S.Modules) [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      ((associatedModule B S hS).obj 𝓕).IsFinitePresentationOnSite :=
  (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).trans
    ((isFinitePresentation_associatedModule_iff B S hS 𝓕 h𝓕).trans
      (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).symm)

end SmallEtale

namespace SmallFlatSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-- **Descent, Lemma 05VG for "of finite presentation" (Modules on Sites, Definition 03DL (7)),
on the small site `S_τ`, for every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation as an
`𝒪`-module on `S_τ`, where `𝓕 ↦ 𝓕^a` is the pullback along `(S_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`. -/
@[stacks 05VG "of finite presentation (03DL (7)), on S_τ for every τ ∈ {smooth, syntomic, fppf}, \
at the functor 𝓕 ↦ 𝓕ᵃ"]
theorem isFinitePresentationOnSite_iff_associatedModule (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      ((associatedModule B S hS κ).obj 𝓕).IsFinitePresentationOnSite :=
  (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).trans
    ((isFinitePresentation_iff_associatedModule B S hS κ 𝓕).trans
      (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).symm)

end SmallFlatSite

namespace Scheme.Modules

variable {S : Scheme.{u}} (Bf : BigFppfSite.{u}) (hf : Bf.Contains S) (Be : BigEtaleSite.{u})
  (he : Be.Contains S) (Bz : BigZariskiSite.{u}) (hz : Bz.Contains S)

/-- **Descent, Lemma 05VG, for the property "of finite presentation" (Modules on Sites,
Definition 03DL (7)).**  For a quasi-coherent `𝒪_S`-module `𝓕`, `𝓕` is of finite presentation
if and only if `𝓕^a` is of finite presentation as an `𝒪`-module, at each of the functors
`𝓕 ↦ 𝓕^a` of Descent, Proposition 03DX: on the big site `(Sch/S)_τ` for every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, on `S_Zar`, on `S_étale`, and on the small site
`S_τ` for every `τ ∈ {smooth, syntomic, fppf}`.  Both sides are finite presentation in the sense
of Definition 03DL (7), `SheafOfModules.IsFinitePresentationOnSite`; on the left it is taken on
the site of opens of `S`. -/
@[stacks 05VG "of finite presentation (03DL (7)): 𝓕 has 𝒫 ⇔ 𝓕ᵃ has 𝒫 on (Sch/S)_τ for every τ, \
on S_Zar, on S_étale, and on S_τ for τ ∈ {smooth, syntomic, fppf}"]
theorem isFinitePresentationOnSite_iff_associatedModule (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    (∀ τ : SiteKind, SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
        ((BigFppfOver.baseAssociatedModule Bf S hf τ).obj 𝓕).IsFinitePresentationOnSite) ∧
      (SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
        ((SmallZariski.associatedModule Bz S hz).obj 𝓕).IsFinitePresentationOnSite) ∧
      (SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
        ((SmallEtale.associatedModule Be S he).obj 𝓕).IsFinitePresentationOnSite) ∧
      ∀ κ : FlatSiteKind, SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
        ((SmallFlatSite.associatedModule Bf S hf κ).obj 𝓕).IsFinitePresentationOnSite :=
  ⟨fun τ ↦ BigFppfOver.isFinitePresentationOnSite_baseAssociatedModule_iff Bf S hf τ 𝓕,
    SmallZariski.isFinitePresentationOnSite_iff_associatedModule Bz S hz 𝓕,
    SmallEtale.isFinitePresentationOnSite_iff_associatedModule Be S he 𝓕,
    fun κ ↦ SmallFlatSite.isFinitePresentationOnSite_iff_associatedModule Bf S hf κ 𝓕⟩

end Scheme.Modules

end AlgebraicGeometry

end
