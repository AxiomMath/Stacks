module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.DerivedSectionsModel
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeSectionsModelCrossing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# [Stacks, Tag 089W] over an open of the target, read in the relative model

`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_hom_eq_lerayComparison`
(`AffineCohomologyComparison/DerivedSectionsModel.lean`) reads [Stacks, Tag 089W] in the model of
derived sections, at the **global** sections of the two schemes. The tail of conclusion (c) of
[Stacks, Tag 0EX3] meets 089W at a **restricted** morphism `f ∣_ V`, whose two schemes are the open
subschemes `f⁻¹V` of `X` and `V` of `Y`, while the `γ⁺` side of (c) speaks of derived sections over
the open `V` of `Y` and over `f⁻¹V` of `X` — the relative model.

This file carries 089W across that divide. Its two ends are transported along the two
crossings of the relative model with the open subscheme's global sections,
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPreimageSectionsIsoAffineOpenCohomology`
upstairs and
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedSectionsOverOpenHomologyIso` downstairs, and
the module its downstairs end lands in is matched by
`AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`, the identification
`(f ∣_ V)_*(F|_{f⁻¹V}) ≅ (f_* F)|_V`.

## Main definitions

* `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOverOpen` — **[Stacks, Tag 089W] at
  `f ∣_ V`, with both ends in the relative model**: `H^n(RΓ(f⁻¹V, F[0])) ≅ H^n(RΓ(V, (f_*F)[0]))`,
  both read over `Γ(Y, V)`.

## Main results

* `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOverOpen_hom` and
  `…_inv` — the four factors, read off the construction.
* `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOverOpen_hom_eq_lerayComparison`
  and `…_inv_eq_lerayComparison` — **the transported equation.** 089W over the open, with its
  089W factor replaced by the derived-sections reading of
  `cohomologyIsoPushforward_hom_eq_lerayComparison` and
  `cohomologyIsoPushforward_inv_eq_lerayComparison`. No hypothesis is added: the two inverses the
  inverse direction needs are handed in as left inverses of plain morphisms, exactly as the
  global-sections statement hands them in, and the only hypotheses anywhere are the affineness of
  `f ∣_ V` and the quasi-coherence of `F|_{f⁻¹V}` that [Stacks, Tag 089W] itself carries.

## Implementation notes

*What is transported and what is not.* The middle of the chain still speaks of the restricted
morphism: `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison (f ∣_ V) ⊤` on the open
subschemes, not `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison f V` on `X` and `Y`. Only
the two **ends** are carried into the relative model, which is what the two crossings of
`TopDegreeSectionsModelCrossing.lean` and `DerivedSectionsModelCrossing.lean` provide; the
compatibility of the Leray comparison itself with restriction to an open subscheme is a different
statement, and it is not proved here. See the ledger of `BaseChangeSectionsTail.lean`.

*Why the hypotheses are explicit arguments and the statements open with `haveI`.* In the situation
of [Stacks, Tag 0EX3] (c) neither the affineness of the restricted morphism nor the
quasi-coherence of the restricted module is an instance — they are produced by
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isAffineHom_resLE_of_isPullback` and
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor` — so they are taken in argument
position, as `…TopDegreeBaseChange.topDirectImageSectionsIsoAffineOpenCohomology` takes its four.
The two equations below name the acyclicity [Stacks, Tag 01XC] supplies, which needs both as
instances to elaborate, so their types open by introducing them; that is the shape
`BaseChangeSectionsTail.lean` already uses.

*The four-fold inverse at variables.* `CategoryTheory.Iso.trans_inv` reverses a two-fold
composite, so a four-fold one comes out left-associated. `four_trans_inv` performs the
reassociation at variables of an abstract category, where it is free, rather than at the concrete
isomorphisms — the discipline of this directory, and the one that keeps `simp only` away from a
goal mentioning `SheafOfModules.evaluation`.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 089W] carries its attribute where it is
proved, in `AffineCohomologyComparison/Basic.lean`; what is here is the dictionary between two
models of it, and conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open DerivedCategory
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit exists_quasiIso_isKInjective)
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedPreimageSections derivedPreimageSectionsUnit derivedSectionsOverOpen
    derivedSectionsOverOpenUnit lerayComparison sectionsOverOpen)

namespace Stacks.Cohomology.AffineComparison

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (F : X.Modules) (n : ℕ)

/-! ### A four-fold inverse, at variables -/

/-- **The inverse of a four-fold composite of isomorphisms**, reassociated. At variables of an
abstract category, where the reassociation is free. -/
private theorem four_trans_inv {C : Type*} [Category* C] {A B D E G : C} (a : A ≅ B) (b : B ≅ D)
    (c : D ≅ E) (d : E ≅ G) :
    (a ≪≫ b ≪≫ c ≪≫ d).inv = d.inv ≫ c.inv ≫ b.inv ≫ a.inv := by
  simp only [Iso.trans_inv, Category.assoc]

/-! ### [Stacks, Tag 089W] over an open, with both ends in the relative model -/

/-- **[Stacks, Tag 089W] over an open of the target, with both ends in the relative model.** Let
`f : X ⟶ S` be a morphism of schemes, `V ⊆ S` an open, `F` an `𝒪_X`-module and `n` a degree.
Suppose the restricted morphism `f ∣_ V` is affine and the restriction `F|_{f⁻¹V}` is
quasi-coherent — the two hypotheses [Stacks, Tag 089W] itself carries. Then

> `H^n(RΓ(f⁻¹V, F[0])) ≅ H^n(RΓ(V, (f_* F)[0]))`,

both sides read as `Γ(S, V)`-modules in the unbounded model of
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections` and
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen`.

It is 089W at `f ∣_ V` conjugated by the two crossings of that model with the global
sections of the open subschemes —
`…TopDegreeBaseChange.derivedPreimageSectionsIsoAffineOpenCohomology` upstairs and
`…TopDegreeBaseChange.derivedSectionsOverOpenHomologyIso` downstairs — the first through the
`ℕ`-versus-`ℤ` indexing of `…TopDegreeBaseChange.affineOpenCohomologyNatIso`, and with
`AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` matching the module 089W's
right-hand end lands in, `(f ∣_ V)_*(F|_{f⁻¹V})`, with `(f_* F)|_V`.

Nothing is assumed of `f`, of `V`, of `F` or of `n` beyond those two hypotheses: all three
conjugating isomorphisms are unconditional. -/
@[ega "III 1.3.3" "more general"]
def cohomologyIsoPushforwardOverOpen (haff : IsAffineHom (f ∣_ V))
    (hF : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent) :
    (homologyFunctor (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))
          (n : ℤ)).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj
          ((singleFunctor X.Modules 0).obj F)) ≅
      (homologyFunctor (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))
          (n : ℤ)).obj
        ((derivedSectionsOverOpen S.toRingedSpace V).obj
          ((singleFunctor S.Modules 0).obj ((Scheme.Modules.pushforward f).obj F))) :=
  haveI := haff
  haveI := hF
  derivedPreimageSectionsIsoAffineOpenCohomology f V F n ≪≫
    (affineOpenCohomologyNatIso f V F n).symm ≪≫
    (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapIso
        (cohomologyIsoPushforward (f ∣_ V)
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) n ≪≫
          ((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).rightDerived
              n).mapIso
            ((AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app F).symm) ≪≫
    (derivedSectionsOverOpenHomologyIso S V ((Scheme.Modules.pushforward f).obj F) n).symm

/-- **The four factors of `cohomologyIsoPushforwardOverOpen`, read off the construction.** The
upstairs crossing, the `ℕ`-versus-`ℤ` indexing inverted, 089W at `f ∣_ V` followed by the
restriction comparison, and the downstairs crossing inverted. -/
theorem cohomologyIsoPushforwardOverOpen_hom (haff : IsAffineHom (f ∣_ V))
    (hF : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent) :
    haveI := haff
    haveI := hF
    (cohomologyIsoPushforwardOverOpen f V F n haff hF).hom =
      (derivedPreimageSectionsIsoAffineOpenCohomology f V F n).hom ≫
        (affineOpenCohomologyNatIso f V F n).inv ≫
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
              ((cohomologyIsoPushforward (f ∣_ V)
                    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) n).hom ≫
                ((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).rightDerived
                    n).map
                  ((AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).inv.app F)) ≫
            (derivedSectionsOverOpenHomologyIso S V
              ((Scheme.Modules.pushforward f).obj F) n).inv :=
  rfl

/-- **The four factors of `cohomologyIsoPushforwardOverOpen`, inverted.** The downstairs crossing,
the restriction comparison and 089W at `f ∣_ V` inverted, the `ℕ`-versus-`ℤ` indexing, and the
upstairs crossing inverted. -/
theorem cohomologyIsoPushforwardOverOpen_inv (haff : IsAffineHom (f ∣_ V))
    (hF : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent) :
    haveI := haff
    haveI := hF
    (cohomologyIsoPushforwardOverOpen f V F n haff hF).inv =
      (derivedSectionsOverOpenHomologyIso S V ((Scheme.Modules.pushforward f).obj F) n).hom ≫
        (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
            (((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).rightDerived n).map
                ((AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).hom.app F) ≫
              (cohomologyIsoPushforward (f ∣_ V)
                ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) n).inv) ≫
          (affineOpenCohomologyNatIso f V F n).hom ≫
            (derivedPreimageSectionsIsoAffineOpenCohomology f V F n).inv :=
  four_trans_inv _ _ _ _

/-! ### The transported equation -/

/-- **[Stacks, Tag 089W] over an open, read in the derived-sections model.** The forward
direction of `cohomologyIsoPushforwardOverOpen` with its 089W factor replaced by
`cohomologyIsoPushforward_hom_eq_lerayComparison`: the upstairs crossing, the `ℕ`-versus-`ℤ`
indexing inverted, then — read over `Γ(S, V)` through
`AlgebraicGeometry.Scheme.Opens.topIso` — restriction of scalars pulled inside the right derived
functor, the crossing of the two models of `RΓ((f ∣_ V)⁻¹⊤, -)` inverted, the degree-`n`
cohomology of the Leray comparison of [Stacks, Tag 0D5W] for `f ∣_ V` over `⊤`, the degree-`n`
cohomology of `RΓ(⊤, -)` of the collapse of `R(f ∣_ V)_*`, the crossing of the two models of
`RΓ(V, -)` on the open subscheme, and the restriction comparison; and finally the downstairs
crossing inverted.

Nothing is assumed beyond the affineness of `f ∣_ V` and the quasi-coherence of `F|_{f⁻¹V}` that
[Stacks, Tag 089W] itself carries. -/
theorem cohomologyIsoPushforwardOverOpen_hom_eq_lerayComparison (haff : IsAffineHom (f ∣_ V))
    (hF : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent) :
    haveI := haff
    haveI := hF
    (cohomologyIsoPushforwardOverOpen f V F n haff hF).hom =
      (derivedPreimageSectionsIsoAffineOpenCohomology f V F n).hom ≫
        (affineOpenCohomologyNatIso f V F n).inv ≫
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
              (((restrictScalarsRightDerivedIso (f ∣_ V)
                      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) n).hom ≫
                  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                      (modulePushforward (f ∣_ V).toLRSHom.toShHom ⋙
                        sectionsOverOpen (V : Scheme).toSheafedSpace ⊤)
                      (derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤)
                      (derivedPreimageSectionsUnit (f ∣_ V).toLRSHom.toShHom ⊤)
                      (exists_quasiIso_isKInjective (f ⁻¹ᵁ V : Scheme).toSheafedSpace) n).inv.app
                    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) ≫
                    (homologyFunctor (ModuleCat.{u} ((structureSheafRing
                            (V : Scheme).toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).map
                        ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
                          ((singleFunctor (SheafOfModules.{u} (structureSheafRing
                              (f ⁻¹ᵁ V : Scheme).toSheafedSpace)) 0).obj
                            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))) ≫
                      (homologyFunctor (ModuleCat.{u} ((structureSheafRing
                              (V : Scheme).toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).map
                          ((derivedSectionsOverOpen (V : Scheme).toSheafedSpace ⊤).map
                            ((modulePushforward (f ∣_ V).toLRSHom.toShHom).singleCollapse
                              (derivedPushforward (f ∣_ V).toLRSHom.toShHom)
                              (derivedPushforwardUnit (f ∣_ V).toLRSHom.toShHom)
                              (exists_quasiIso_isKInjective (f ⁻¹ᵁ V : Scheme).toSheafedSpace)
                              ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)
                              (rightAcyclic_pushforward_of_isAffineHom (f ∣_ V)
                                ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)))) ≫
                        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                            (sectionsOverOpen (V : Scheme).toSheafedSpace ⊤)
                            (derivedSectionsOverOpen (V : Scheme).toSheafedSpace ⊤)
                            (derivedSectionsOverOpenUnit (V : Scheme).toSheafedSpace ⊤)
                            (exists_quasiIso_isKInjective (V : Scheme).toSheafedSpace)
                            n).hom.app
                          ((Scheme.Modules.pushforward (f ∣_ V)).obj
                            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))) ≫
                ((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).rightDerived
                    n).map
                  ((AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).inv.app F)) ≫
            (derivedSectionsOverOpenHomologyIso S V
              ((Scheme.Modules.pushforward f).obj F) n).inv := by
  have := haff
  have := hF
  exact congrArg (fun z =>
      (derivedPreimageSectionsIsoAffineOpenCohomology f V F n).hom ≫
        (affineOpenCohomologyNatIso f V F n).inv ≫
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
              (z ≫ ((Stacks.Cohomology.AffineBase.moduleGlobalSections
                    (V : Scheme)).rightDerived n).map
                ((AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).inv.app F)) ≫
            (derivedSectionsOverOpenHomologyIso S V
              ((Scheme.Modules.pushforward f).obj F) n).inv)
    (cohomologyIsoPushforward_hom_eq_lerayComparison (f ∣_ V)
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) n)

/-- **[Stacks, Tag 089W] over an open, read in the derived-sections model, inverted** — the
direction the tail of conclusion (c) of [Stacks, Tag 0EX3] carries. The downstairs crossing, then
— read over `Γ(S, V)` — the restriction comparison, the crossing of the two models of `RΓ(V, -)`
on the open subscheme inverted, the degree-`n` cohomology of `RΓ(⊤, c)` for a comparison `c` of
the two models of `R(f ∣_ V)_*` retracting the collapse, a left inverse of the degree-`n`
cohomology of the Leray comparison, the crossing of the two models of `RΓ((f ∣_ V)⁻¹⊤, -)`, and
restriction of scalars pulled out of the right derived functor; and finally the `ℕ`-versus-`ℤ`
indexing and the upstairs crossing inverted.

The two inverses are handed in as left inverses of **plain** morphisms, `hc` and `hl`, exactly as
`cohomologyIsoPushforward_inv_eq_lerayComparison` hands them in, so that the two statements
compose; neither costs a hypothesis, both being invertible unconditionally. So nothing is assumed
beyond the affineness of `f ∣_ V` and the quasi-coherence of `F|_{f⁻¹V}`. -/
theorem cohomologyIsoPushforwardOverOpen_inv_eq_lerayComparison (haff : IsAffineHom (f ∣_ V))
    (hF : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent)
    {c : (singleFunctor (SheafOfModules.{u} (structureSheafRing
            (V : Scheme).toSheafedSpace)) 0).obj
          ((modulePushforward (f ∣_ V).toLRSHom.toShHom).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ⟶
      (derivedPushforward (f ∣_ V).toLRSHom.toShHom).obj
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing
          (f ⁻¹ᵁ V : Scheme).toSheafedSpace)) 0).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))}
    (hc : haveI := haff
      haveI := hF
      c ≫ (modulePushforward (f ∣_ V).toLRSHom.toShHom).singleCollapse
          (derivedPushforward (f ∣_ V).toLRSHom.toShHom)
          (derivedPushforwardUnit (f ∣_ V).toLRSHom.toShHom)
          (exists_quasiIso_isKInjective (f ⁻¹ᵁ V : Scheme).toSheafedSpace)
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)
          (rightAcyclic_pushforward_of_isAffineHom (f ∣_ V)
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) = 𝟙 _)
    {lInv : (homologyFunctor (ModuleCat.{u} ((structureSheafRing
            (V : Scheme).toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).obj
          ((derivedSectionsOverOpen (V : Scheme).toSheafedSpace ⊤).obj
            ((derivedPushforward (f ∣_ V).toLRSHom.toShHom).obj
              ((singleFunctor (SheafOfModules.{u} (structureSheafRing
                (f ⁻¹ᵁ V : Scheme).toSheafedSpace)) 0).obj
                ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)))) ⟶
      (homologyFunctor (ModuleCat.{u} ((structureSheafRing
          (V : Scheme).toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).obj
        ((derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing
            (f ⁻¹ᵁ V : Scheme).toSheafedSpace)) 0).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)))}
    (hl : lInv ≫ (homologyFunctor (ModuleCat.{u} ((structureSheafRing
            (V : Scheme).toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).map
          ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing
              (f ⁻¹ᵁ V : Scheme).toSheafedSpace)) 0).obj
              ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))) = 𝟙 _) :
    haveI := haff
    haveI := hF
    (cohomologyIsoPushforwardOverOpen f V F n haff hF).inv =
      (derivedSectionsOverOpenHomologyIso S V ((Scheme.Modules.pushforward f).obj F) n).hom ≫
        (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
            (((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).rightDerived n).map
                ((AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).hom.app F) ≫
              (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                    (sectionsOverOpen (V : Scheme).toSheafedSpace ⊤)
                    (derivedSectionsOverOpen (V : Scheme).toSheafedSpace ⊤)
                    (derivedSectionsOverOpenUnit (V : Scheme).toSheafedSpace ⊤)
                    (exists_quasiIso_isKInjective (V : Scheme).toSheafedSpace) n).inv.app
                  ((Scheme.Modules.pushforward (f ∣_ V)).obj
                    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≫
                (homologyFunctor (ModuleCat.{u} ((structureSheafRing
                        (V : Scheme).toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).map
                    ((derivedSectionsOverOpen (V : Scheme).toSheafedSpace ⊤).map c) ≫
                  lInv ≫
                    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                          (modulePushforward (f ∣_ V).toLRSHom.toShHom ⋙
                            sectionsOverOpen (V : Scheme).toSheafedSpace ⊤)
                          (derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤)
                          (derivedPreimageSectionsUnit (f ∣_ V).toLRSHom.toShHom ⊤)
                          (exists_quasiIso_isKInjective
                            (f ⁻¹ᵁ V : Scheme).toSheafedSpace) n).hom.app
                        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) ≫
                      (restrictScalarsRightDerivedIso (f ∣_ V)
                        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) n).inv) ≫
          (affineOpenCohomologyNatIso f V F n).hom ≫
            (derivedPreimageSectionsIsoAffineOpenCohomology f V F n).inv := by
  have := haff
  have := hF
  refine (cohomologyIsoPushforwardOverOpen_inv f V F n haff hF).trans
    (congrArg (fun z =>
      (derivedSectionsOverOpenHomologyIso S V ((Scheme.Modules.pushforward f).obj F) n).hom ≫
        (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
            (((Stacks.Cohomology.AffineBase.moduleGlobalSections
                    (V : Scheme)).rightDerived n).map
                ((AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).hom.app F) ≫
              z) ≫
          (affineOpenCohomologyNatIso f V F n).hom ≫
            (derivedPreimageSectionsIsoAffineOpenCohomology f V F n).inv)
      (cohomologyIsoPushforward_inv_eq_lerayComparison (f ∣_ V)
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) n hc hl))

end Stacks.Cohomology.AffineComparison

end
