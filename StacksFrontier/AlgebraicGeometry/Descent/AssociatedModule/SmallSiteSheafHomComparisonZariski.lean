module

public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteSheafHomComparisonMate
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteSheafHomComparisonUlift
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.SmallZariskiAssociatedModuleTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 06VE (8) at `τ = Zariski`

Clause (8) of Descent, Lemma 06VE says that for `τ ∈ {Zariski, étale}` and quasi-coherent
`𝒪_S`-modules `𝓕`, `𝓖` with `𝓕` of finite presentation,

`(SheafHom_{𝒪_S}(𝓕, 𝓖))^a = SheafHom_𝒪(𝓕^a, 𝓖^a)` in `Mod(S_τ, 𝒪)`.

**This file proves the clause at `τ = Zariski`**, for the functor `𝓕 ↦ 𝓕^a` of Definition
03DU (4) on the small Zariski site of schemes over `S`, and with no hypothesis on `𝓕` or `𝓖` at
all.  The étale half is `AlgebraicGeometry.SmallEtale.associatedModuleInternalHomSheafIso` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallSiteSheafHomComparison.lean`;
clause (9), that the statement fails on a big site, is
`AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.exists_isQuasicoherent_not_iso_sheafHom`.

The source disposes of `τ = Zariski` in one sentence — "the category of `𝒪`-modules on `S_Zar`
is the same as the category of `𝒪_S`-modules on the topological space `S`" — and that is what
the proof below uses, in the form in which this development has it: the comparison of Remark
03FH at `τ = Zariski` is an equivalence of the categories of modules, Stacks 03FG, which is
`AlgebraicGeometry.SmallZariski.isEquivalence_associatedModule`.  Concretely, two steps:

* the formal half, `CategoryTheory.Adjunction.rightAdjointSquareIso` applied to the
  associated-module adjunction, the tensor--internal-Hom adjunction of Stacks 03EO on `S` and
  the one on `S_Zar`, and the comparison of Stacks 03EL — clause (7) of this same lemma.  It
  gives `ε_* SheafHom_𝒪(𝓕^a, 𝓖^a) ≅ SheafHom_{𝒪_S}(𝓕, ε_* 𝓖^a)`, which is
  `AlgebraicGeometry.SmallZariski.restrictModuleInternalHomIso` below and holds on any site.
* the half that is special to `τ = Zariski`: the unit `𝓖 ⟶ ε_* 𝓖^a` and the counit
  `ε^* ε_* 𝓗 ⟶ 𝓗` of that adjunction are isomorphisms, because `𝓕 ↦ 𝓕^a` is an equivalence.
  At `τ = étale` neither is, and both have to be bought with quasi-coherence; that is the whole
  difference between the two halves of the clause.

## Main results

* `AlgebraicGeometry.SmallZariski.restrictModuleInternalHomIso`:
  `ε_* SheafHom_𝒪(𝓕^a, 𝓖) ≅ SheafHom_{𝒪_S}(𝓕, ε_* 𝓖)`, the mate of clause (7).
* `AlgebraicGeometry.SmallZariski.associatedModuleInternalHomSheafIso`: **Stacks 06VE (8) at
  `τ = Zariski`**.

## Implementation notes

The internal Hom of Stacks 03EM on the small Zariski site of schemes over `S` is
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`, the internal Hom read in the universe of
the sections rather than in the universe of the objects of the site; the site is essentially
small, and `AlgebraicGeometry.RingedSite.internalHomSheafSmallIso` says that this is the internal
Hom of `AlgebraicGeometry.RingedSite.internalHomSheaf` and not another construction.  The
internal Hom on `S` itself is `Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules`,
the sheaf Hom of two `𝒪_S`-modules, which `AlgebraicGeometry.SmallZariski.sheafHomModules_eq`
identifies with Tag 03EM's internal Hom on the site of opens of `S`.

The statement is made for **all** `𝒪_S`-modules.  The source states clause (8) for
quasi-coherent `𝓕`, `𝓖` with `𝓕` of finite presentation, and the quasi-coherent case is this
one restricted along `CategoryTheory.ObjectProperty.ι`; neither hypothesis is used, and the
source's own argument at `τ = Zariski` does not use them either.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying category of the small Zariski ringed site of `S` is `u`-essentially small. -/
instance smallZariskiRingedSite_essentiallySmall :
    EssentiallySmall.{u} (smallZariskiRingedSite B S hS).C := by
  change EssentiallySmall.{u} (SmallZariski B S hS)
  infer_instance

/-- Presheaves of abelian groups on the small Zariski ringed site of `S` admit sheafification. -/
instance smallZariskiRingedSite_hasSheafify :
    HasWeakSheafify (smallZariskiRingedSite B S hS).J AddCommGrpCat.{u} := by
  change HasWeakSheafify (topology B S hS) AddCommGrpCat.{u}
  infer_instance

/-- On the small Zariski ringed site of `S`, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
instance smallZariskiRingedSite_wEqualsLocallyBijective :
    (smallZariskiRingedSite B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  change (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

/-- **The pushforward of an internal Hom out of a pullback.**  For `𝒪_S`-modules `𝓕` and an
`𝒪`-module `𝓖` on the small Zariski site of schemes over `S`,

`ε_* SheafHom_𝒪(𝓕^a, 𝓖) ≅ SheafHom_{𝒪_S}(𝓕, ε_* 𝓖)`.

This is the mate, `CategoryTheory.Adjunction.rightAdjointSquareIso`, of the comparison of
Stacks 03EL — clause (7) of Stacks 06VE at `τ = Zariski` — against the two
tensor--internal-Hom adjunctions of Stacks 03EO, the one on the site of opens of `S` and
`AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction` on the small Zariski
site.  No hypothesis is needed: it is the formal half of clause (8), and holds on any site. -/
@[sga "4 IV 13.4" "special case"]
def restrictModuleInternalHomIso (𝓕 : S.Modules) :
    RingedSite.internalHomSheafSmallFunctor.{u} (smallZariskiRingedSite B S hS)
          ((associatedModule B S hS).obj 𝓕) ⋙ restrictModule B S hS ≅
      restrictModule B S hS ⋙
        Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
          (Opens.grothendieckTopology ↥S) S.sheaf 𝓕 :=
  Adjunction.rightAdjointSquareIso (associatedModuleAdjunction B S hS)
    ((Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction S.sheaf 𝓕).ofNatIsoLeft
      (Functor.tensorRightOfBifunctorUncurryIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf) 𝓕).symm)
    ((RingedSite.sheafTensorRightInternalHomSmallAdjunction (smallZariskiRingedSite B S hS)
        ((associatedModule B S hS).obj 𝓕)).ofNatIsoLeft
      (Functor.tensorRightOfBifunctorUncurryIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallZariskiRingedSite B S hS).O)
        ((associatedModule B S hS).obj 𝓕)).symm)
    (Functor.tensorRightOfBifunctorIso (associatedModule B S hS)
      (associatedModuleTensorIsoOfComparison B S hS) 𝓕)

/-- **Stacks 06VE (8) at `τ = Zariski`.**  For `𝒪_S`-modules `𝓕` and `𝓖` on a scheme `S`,

`(SheafHom_{𝒪_S}(𝓕, 𝓖))^a ≅ SheafHom_𝒪(𝓕^a, 𝓖^a)` in `Mod(S_Zar, 𝒪)`,

where `𝓕 ↦ 𝓕^a` is the functor of Definition 03DU (4) at `τ = Zariski` in its pullback
description of Remark 03FH, `AlgebraicGeometry.SmallZariski.associatedModule`, and the internal
Hom on the right is Tag 03EM's on the small Zariski site of schemes over `S`.

The proof is the source's: the mate of clause (7),
`AlgebraicGeometry.SmallZariski.restrictModuleInternalHomIso`, computes the restriction of the
right-hand side as `SheafHom_{𝒪_S}(𝓕, ε_* 𝓖^a)`; the unit of the associated-module adjunction
identifies `ε_* 𝓖^a` with `𝓖`, so that restriction is the left-hand side's source; and the
counit identifies the right-hand side with the associated module of its own restriction.  Both
unit and counit are isomorphisms because `𝓕 ↦ 𝓕^a` is an equivalence at `τ = Zariski`,
Stacks 03FG — which is the content of the source's one-sentence argument, and the only thing
clause (8) needs at this topology.

Neither quasi-coherence nor finite presentation of `𝓕` is assumed: they are what the clause
needs at `τ = étale`, where they buy the two isomorphisms that come for free here. -/
@[stacks 06VE "part (8), small site at τ = Zariski, for the pullback-defined functor 𝓕 ↦ 𝓕ᵃ of \
Remark 03FH and Tag 03EM's internal Hom on S_Zar, for all 𝒪_S-modules"]
def associatedModuleInternalHomSheafIso (𝓕 𝓖 : S.Modules) :
    (associatedModule B S hS).obj
        (Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules 𝓕 𝓖) ≅
      RingedSite.internalHomSheafSmall.{u} (smallZariskiRingedSite B S hS)
        ((associatedModule B S hS).obj 𝓕) ((associatedModule B S hS).obj 𝓖) := by
  haveI := isEquivalence_associatedModule B S hS
  refine ((associatedModule B S hS).mapIso
    ((restrictModuleInternalHomIso B S hS 𝓕).app ((associatedModule B S hS).obj 𝓖) ≪≫
      (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
        (Opens.grothendieckTopology ↥S) S.sheaf 𝓕).mapIso
        ((restrictAssociatedModuleIso B S hS).app 𝓖).symm)).symm ≪≫ ?_
  exact (asIso (associatedModuleAdjunction B S hS).counit).app
    (RingedSite.internalHomSheafSmall.{u} (smallZariskiRingedSite B S hS)
      ((associatedModule B S hS).obj 𝓕) ((associatedModule B S hS).obj 𝓖))

end AlgebraicGeometry.SmallZariski

end
