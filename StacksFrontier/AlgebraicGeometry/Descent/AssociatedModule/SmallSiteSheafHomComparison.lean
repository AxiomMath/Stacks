module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleTensorBifunctor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteSheafHomComparisonMate
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteSheafHomComparisonUlift
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInternalHomFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 06VE (8) at `τ = étale`

Clause (8) of Descent, Lemma 06VE says that for `τ ∈ {Zariski, étale}` and quasi-coherent
`𝒪_S`-modules `𝓕`, `𝓖` with `𝓕` of finite presentation,

`(SheafHom_{𝒪_S}(𝓕, 𝓖))^a = SheafHom_𝒪(𝓕^a, 𝓖^a)` in `Mod(S_τ, 𝒪)`.

**This file proves the clause at `τ = étale`**; the Zariski half is
`AlgebraicGeometry.SmallZariski.associatedModuleInternalHomSheafIso` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallSiteSheafHomComparisonZariski.lean`.
Clause (9) of the same lemma, that the statement fails on a big site, is
`AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.exists_isQuasicoherent_not_iso_sheafHom`.

The source's proof is that `𝓕 ↦ 𝓕^a` is the pullback along the flat morphism of ringed sites
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Lemma 0GNA, and that pullback along a flat morphism
commutes with internal Hom out of a finitely presented module by Modules on Sites, Lemma 0GN2.
That route is not the one taken here: Tag 0GN2 is available in this development only for a
`AlgebraicGeometry.RingedSite.{u, u, u}` and with the continuity of internal Hom in its first
variable as a hypothesis, and the small étale site is a `AlgebraicGeometry.RingedSite.{u + 1, u,
u}`.  What replaces it is the two facts the flatness and the finite presentation are *used for*,
both of which this development has at the small étale site:

* **the right-hand side is quasi-coherent.**  This is clause (6) of Stacks 0GNB,
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf`, whose hypothesis is
  that `𝓕^a` be of finite presentation on the site in the sense of Stacks 03DL (7) — which the
  finite presentation of `𝓕` gives, by Stacks 03DO for that clause — and that `𝓖^a` be
  quasi-coherent.  It is where finite presentation enters, exactly as in the source.
* **the comparison `ε^* ε_* ⟶ 𝟙` is an isomorphism at a quasi-coherent module**, Stacks 03DX (2)
  at `τ = étale`, `AlgebraicGeometry.SmallEtale.isIso_counit`, and the unit `𝟙 ⟶ ε_* ε^*` is an
  isomorphism at a quasi-coherent `𝒪_S`-module, Stacks 0GN7,
  `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`.  This is where the exactness of `ε^*` —
  the flatness of `ε` — has already been spent.

Given those, the clause is formal.  The mate of the comparison of Stacks 03EL — clause (7) of
this same lemma, `AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso` — against the
two tensor--internal-Hom adjunctions of Stacks 03EO identifies

`ε_* SheafHom_𝒪(𝓕^a, 𝓖) ≅ SheafHom_{𝒪_S}(𝓕, ε_* 𝓖)`

(`AlgebraicGeometry.SmallEtale.restrictModuleInternalHomIso`, which has no hypothesis and holds
on any site).  At `𝓖 := 𝓖^a` the unit turns the right-hand side into
`SheafHom_{𝒪_S}(𝓕, 𝓖)`, so the Zariski restriction of `SheafHom_𝒪(𝓕^a, 𝓖^a)` is the source of
the left-hand side of the clause; and the counit, available because that internal Hom is
quasi-coherent, turns `SheafHom_𝒪(𝓕^a, 𝓖^a)` into the associated module of its own restriction.

## Main results

* `AlgebraicGeometry.SmallEtale.restrictModuleInternalHomIso`:
  `ε_* SheafHom_𝒪(𝓕^a, 𝓖) ≅ SheafHom_{𝒪_S}(𝓕, ε_* 𝓖)`, the mate of clause (7) at `τ = étale`.
* `AlgebraicGeometry.SmallEtale.isFinitePresentationOnSite_associatedModule`: **Stacks 03DO for
  the clause 03DL (7) at `ε`** — the associated module of a module of finite presentation is of
  finite presentation on the small étale site.
* `AlgebraicGeometry.SmallEtale.associatedModuleInternalHomSheafIso`: **Stacks 06VE (8) at
  `τ = étale`**.

## Implementation notes

The internal Hom of Stacks 03EM on the small étale site is
`AlgebraicGeometry.SmallEtale.internalHomSheaf`, which is
`AlgebraicGeometry.RingedSite.internalHomSheafSmall` of the small étale ringed site: the internal
Hom read in the universe of the sections rather than in the universe of the objects of the site,
identified with `AlgebraicGeometry.RingedSite.internalHomSheaf` by
`AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso`.  It is the spelling clause (6) of
Stacks 0GNB is stated at.  The internal Hom on `S` itself is
`Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules`, the sheaf Hom of two
`𝒪_S`-modules, which `AlgebraicGeometry.SmallZariski.sheafHomModules_eq` identifies with Tag
03EM's internal Hom on the site of opens of `S`.

**The finite-presentation hypothesis.**  It is `SheafOfModules.IsFinitePresentationOnSite` for
`𝓕` itself — Stacks 03DL (7) on the site of opens of `S`, which on a scheme says that every open
is covered by opens over which `𝓕` is the cokernel of a map of finite free modules, the
definition of a module of finite presentation.  Clause (6) of Stacks 0GNB consumes it for `𝓕^a`
instead, and `AlgebraicGeometry.SmallEtale.isFinitePresentationOnSite_associatedModule` carries
it across: that is Stacks 03DO for the clause 03DL (7),
`Stacks.Sheaves.FinitePresentation.pullbackModules_isFinitePresentationOnSite`, read at `ε`.

Quasi-coherence of `𝓕` is not assumed, the source's hypothesis notwithstanding: nothing in the
argument uses it.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 0GNA](https://stacks.math.columbia.edu/tag/0GNA)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The pushforward of an internal Hom out of a pullback.**  For an `𝒪_S`-module `𝓕` and an
`𝒪`-module `𝓖` on the small étale site of `S`,

`ε_* SheafHom_𝒪(𝓕^a, 𝓖) ≅ SheafHom_{𝒪_S}(𝓕, ε_* 𝓖)`.

This is the mate, `CategoryTheory.Adjunction.rightAdjointSquareIso`, of the comparison of
Stacks 03EL — clause (7) of Stacks 06VE at `τ = étale` — against the two tensor--internal-Hom
adjunctions of Stacks 03EO, the one on the site of opens of `S` and
`AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction` on the small étale
site.  No hypothesis is needed: it is the formal half of clause (8), and holds on any site. -/
@[sga "4 IV 13.4" "special case"]
def restrictModuleInternalHomIso (𝓕 : S.Modules) :
    internalHomSheafFunctor B S hS ((associatedModule B S hS).obj 𝓕) ⋙ restrictModule B S hS ≅
      restrictModule B S hS ⋙
        Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
          (Opens.grothendieckTopology ↥S) S.sheaf 𝓕 :=
  Adjunction.rightAdjointSquareIso (associatedModuleAdjunction B S hS)
    ((Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction S.sheaf 𝓕).ofNatIsoLeft
      (Functor.tensorRightOfBifunctorUncurryIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf) 𝓕).symm)
    ((RingedSite.sheafTensorRightInternalHomSmallAdjunction (smallEtaleRingedSite B S hS)
        ((associatedModule B S hS).obj 𝓕)).ofNatIsoLeft
      (Functor.tensorRightOfBifunctorUncurryIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS).O)
        ((associatedModule B S hS).obj 𝓕)).symm)
    (Functor.tensorRightOfBifunctorIso (associatedModule B S hS)
      (associatedModuleTensorBifunctorIso B S hS) 𝓕)

/-- **Stacks 03DO for the clause 03DL (7) at `ε`**: the associated module of an `𝒪_S`-module of
finite presentation is of finite presentation on the small étale site.

This is `Stacks.Sheaves.FinitePresentation.pullbackModules_isFinitePresentationOnSite`, the
statement for the pullback of modules along a morphism of ringed topoi, at the morphism
underlying `ε` — `AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso` identifies that
pullback with `𝓕 ↦ 𝓕^a`, and finite presentation on a site is invariant under isomorphism. -/
theorem isFinitePresentationOnSite_associatedModule (𝓕 : S.Modules)
    (h𝓕 : SheafOfModules.IsFinitePresentationOnSite 𝓕) :
    SheafOfModules.IsFinitePresentationOnSite ((associatedModule B S hS).obj 𝓕) :=
  SheafOfModules.IsFinitePresentationOnSite.of_iso
    ((pullbackModulesToZariskiIso B S hS).app 𝓕)
    (Stacks.Sheaves.FinitePresentation.pullbackModules_isFinitePresentationOnSite
      (toZariskiRingedToposModulesHom B S hS) 𝓕 h𝓕)

/-- **Stacks 06VE (8) at `τ = étale`.**  For `𝒪_S`-modules `𝓕`, `𝓖` on a scheme `S` with `𝓖`
quasi-coherent and `𝓕` of finite presentation — Stacks 03DL (7) on the site of opens of `S` —

`(SheafHom_{𝒪_S}(𝓕, 𝓖))^a ≅ SheafHom_𝒪(𝓕^a, 𝓖^a)` in `Mod(S_étale, 𝒪)`,

where `𝓕 ↦ 𝓕^a` is the functor of Definition 03DU (4) at `τ = étale` in its pullback description
of Remark 03FH, `AlgebraicGeometry.SmallEtale.associatedModule`, and the internal Hom on the
right is Tag 03EM's on the small étale site.

The proof is the one the module docstring describes: the mate of clause (7),
`AlgebraicGeometry.SmallEtale.restrictModuleInternalHomIso`, computes the Zariski restriction of
the right-hand side as `SheafHom_{𝒪_S}(𝓕, ε_* 𝓖^a)`; the unit of the associated-module
adjunction is an isomorphism at the quasi-coherent `𝓖`, Stacks 0GN7, so that restriction is
`SheafHom_{𝒪_S}(𝓕, 𝓖)`; and the counit is an isomorphism at the right-hand side because that
internal Hom is quasi-coherent, which is clause (6) of Stacks 0GNB and is where the finite
presentation of `𝓕` is spent, through Stacks 03DO for the clause 03DL (7),
`AlgebraicGeometry.SmallEtale.isFinitePresentationOnSite_associatedModule`.

Quasi-coherence of `𝓕` is not needed. -/
@[stacks 06VE "part (8), small site at τ = étale, for the pullback-defined functor 𝓕 ↦ 𝓕ᵃ of \
Remark 03FH and Tag 03EM's internal Hom on S_étale"]
def associatedModuleInternalHomSheafIso (𝓕 𝓖 : S.Modules)
    (h𝓖 : SheafOfModules.IsQuasicoherent 𝓖)
    (h𝓕 : SheafOfModules.IsFinitePresentationOnSite 𝓕) :
    (associatedModule B S hS).obj
        (Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules 𝓕 𝓖) ≅
      internalHomSheaf B S hS ((associatedModule B S hS).obj 𝓕)
        ((associatedModule B S hS).obj 𝓖) := by
  have h𝓖' : ((associatedModule B S hS).obj 𝓖).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS 𝓖 h𝓖
  have hIH : (internalHomSheaf B S hS ((associatedModule B S hS).obj 𝓕)
      ((associatedModule B S hS).obj 𝓖)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_internalHomSheaf B S hS ((associatedModule B S hS).obj 𝓕)
      ((associatedModule B S hS).obj 𝓖)
      (isFinitePresentationOnSite_associatedModule B S hS 𝓕 h𝓕) h𝓖'
  have hcounit : IsIso ((associatedModuleAdjunction B S hS).counit.app
      (internalHomSheaf B S hS ((associatedModule B S hS).obj 𝓕)
        ((associatedModule B S hS).obj 𝓖))) :=
    isIso_counit B S hS
      (internalHomSheaf B S hS ((associatedModule B S hS).obj 𝓕)
        ((associatedModule B S hS).obj 𝓖)) hIH
      (isQuasicoherent_restrictModule B S hS
        (internalHomSheaf B S hS ((associatedModule B S hS).obj 𝓕)
          ((associatedModule B S hS).obj 𝓖)) hIH)
  haveI : IsIso ((associatedModuleAdjunction B S hS).unit.app 𝓖) :=
    unitIsoOnQuasicoherent B S hS ⟨𝓖, h𝓖⟩
  refine ((associatedModule B S hS).mapIso
    ((restrictModuleInternalHomIso B S hS 𝓕).app ((associatedModule B S hS).obj 𝓖) ≪≫
      (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
        (Opens.grothendieckTopology ↥S) S.sheaf 𝓕).mapIso
        (asIso ((associatedModuleAdjunction B S hS).unit.app 𝓖)).symm)).symm ≪≫ ?_
  exact @asIso _ _ _ _ _ hcounit

end AlgebraicGeometry.SmallEtale

end
