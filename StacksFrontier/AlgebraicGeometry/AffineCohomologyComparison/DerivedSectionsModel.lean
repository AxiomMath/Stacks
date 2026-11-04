module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.UnboundedModel
public import StacksFrontier.CategoryTheory.CompositeCancellation
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayViaPlus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# [Stacks, Tag 089W] read in the model of derived sections

`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_hom_eq` reads
[Stacks, Tag 089W] at an *arbitrary* pair of unbounded right derived functors of `f_*` and
of `Γ(S, -)` together with an arbitrary comparison `θ` of the iterated ones, because the
unbounded functors used here are stated at
`SheafOfModules (structureSheafRing _)` while 089W is stated at
`AlgebraicGeometry.Scheme.Modules`, and the two carry different `Preadditive` instances. A user
of it crosses between the two once, in argument position, when it supplies `RF`, `RG`, `RFG` and
`θ`; this file supplies them.

The data supplied is the one the tail of conclusion (c) of [Stacks, Tag 0EX3] speaks in:

* `RF` is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f`;
* `RG` is `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen S ⊤`, global sections
  being `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen` at `⊤`;
* `RFG` is `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f ⊤`, which is
  sections over `f⁻¹⊤ = ⊤` read over `Γ(S, 𝒪_S)`;
* `θ` is the **Leray comparison** of [Stacks, Tag 0D5W],
  `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison f ⊤`.

The coherence `hθ` that 089W's reading asks for is then
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app_refl` **on the nose** — that
lemma has exactly this shape — so nothing is proved here beyond the
crossing itself.

## Main results

* `cohomologyIsoPushforward_hom_eq_lerayComparison`: **[Stacks, Tag 089W] along an affine
  morphism of schemes, read in the model of derived sections.** For `f : X ⟶ S` affine and `F`
  quasi-coherent, the comparison `H^n(X, F) ≅ H^n(S, f_* F)` is

  > restriction of scalars pulled inside the right derived functor, the crossing of the two
  > models of `RΓ(f⁻¹⊤, -)` inverted, `H^n` of the Leray comparison of [Stacks, Tag 0D5W] for
  > `f` over `⊤` at `F[0]`, `H^n(RΓ(⊤, -))` of the collapse of `Rf_*` at `F`, and the crossing
  > of the two models of `RΓ(S, -)`.

* `cohomologyIsoPushforward_inv_eq_lerayComparison`: the same **inverted**, which is the
  direction the tail of [Stacks, Tag 0EX3] (c) carries. The two inverses it needs are handed in
  as left inverses of plain morphisms — a comparison `c` of the two models of `Rf_*` at `F[0]`
  retracting the collapse, and a left inverse `lInv` of the degree-`n` cohomology of the Leray
  comparison — so the statement adds no hypothesis: both are invertible unconditionally, by
  `CategoryTheory.Functor.singleCollapseIso` and
  `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`.

## Why this is the match the tail of [Stacks, Tag 0EX3] (c) needs

The `ψ` side of the pure-tensor agreement of (c) carries
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.cohomologyPullbackIsoPushforward` — which is
`cohomologyIsoPushforward` at the pullback along the affine `h' ∣`, by definition — **inverted**,
while the `γ⁺` side's tail, as `Stacks.Cohomology.DerivedBaseChange`
`.homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite` reads it, begins with the
derived sections of a comparison `c` of the two models of `Rh'_*` followed by a relative Leray
comparison inverted. `cohomologyIsoPushforward_inv_eq_lerayComparison` is those same two
factors: the collapse of `Rf_*` at an `f_*`-acyclic `F` is exactly such a `c` inverted, by
`CategoryTheory.Functor.singleCollapse`, and the Leray comparison is the same transformation of
[Stacks, Tag 0D5W].

**Scope.** This is 089W at *global* sections of the two schemes, i.e. at `⊤`; the tail meets it
at the **restricted** morphism `h'.resLE (f'⁻¹V) (f''⁻¹W)`, which needs two further passages: from
the open subscheme's global sections to the relative statement over the open `f'⁻¹V` of `X'` —
the direction of `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedSectionsOverOpenHomologyIso`
and `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsCohomologyIso` — and the
restriction from `h'⁻¹(f'⁻¹V)` down to the smaller `f''⁻¹W`. The second is
`Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_restrictSource`, and the **two
ends** of the first are `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOverOpen`,
which carries the two equations below through the crossings of the relative model; its
**middle** is the compatibility of the Leray comparison with restriction to an open subscheme.

## Implementation notes

*The two spellings of the modules on a scheme, and why every factor below is written at the
`SheafOfModules` one.* `X.Modules` and `SheafOfModules (structureSheafRing X.toRingedSpace)` are
equal types with different `Category` and `Abelian` instance terms, and
`AlgebraicGeometry.Scheme.Modules` is a **semireducible** `def`: it unfolds for ordinary
unification but not at the transparency instance synthesis runs at. Three facts decide the
shape of what follows.

* Writing `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` or
  `CategoryTheory.Functor.singleCollapse` at a degreewise functor out of `X.Modules` — which is
  what 089W's own statement names — **does not elaborate**: both ask for
  `HasDerivedCategory` of that source, and the right derived functor handed to them is stated at
  `SheafOfModules _`, so the instance has to be the one *that* functor carries.
  `HasDerivedCategory.standard` as a local instance gives `standard X.Modules` instead and the
  application then fails to typecheck, reported as `failed to synthesize instance of type class
  HasDerivedCategory X.Modules`. Priority does not help, and neither does a local instance keyed
  on `Z.Modules` whose *value* is the `SheafOfModules`-spelled one. At the
  `SheafOfModules` spelling every factor is consistent and the statement elaborates in seconds.
* `DerivedCategory.Qh.IsLocalization (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))`
  is not synthesisable either, so the three `IsRightDerivedFunctor` instances 089W asks for at
  the `X.Modules` spelling cannot be *stated* there — a `local instance` or a `haveI` written out
  at that spelling does not elaborate.
* Those instance arguments are **not** postponed into addressable tactic goals: supplying them is
  forced to happen inside the application.

So the application is written with `@` and the three instances are passed as `inferInstanceAs` at
the `SheafOfModules` spelling, where they are found; the expected types are the ones Lean
computes from 089W's own signature, and the two agree by unfolding `Scheme.Modules`, which
ordinary unification does. `AlgebraicGeometry.Scheme.Modules.pushforward f` appears in the
statement only inside the right-hand end `(f_* F)`, where it is in argument position — that is
the one crossing, the discipline
`…TopDegreeBaseChange.singleCompDerivedCompHomologyIsoRightDerived_hom_app_eq` also follows.

*`HasDerivedCategory.standard` is a local instance at high priority, and that is not cosmetic.*
`cohomologyIsoPushforward_hom_eq` was elaborated with it in force, so its `DerivedCategory
X.Modules` is the standard model; the locally small instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `SheafOfModules.hasDerivedCategory`
are global, and where they are in scope they
otherwise win — and then `derivedPushforward` is at morphism universe `u` while 089W's `RF` is
expected at `u + 1`, and the application fails with a universe mismatch.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 089W] carries its attribute where it is
proved; what is here is the dictionary between two models of it, and conclusion (c) of
[Stacks, Tag 0EX3] is not proved here.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.AffineComparison

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] (F : X.Modules)
  [F.IsQuasicoherent] (n : ℕ)

/-- **[Stacks, Tag 089W] along an affine morphism of schemes, read in the model of derived
sections.** For an affine morphism `f : X ⟶ S` of schemes, a quasi-coherent `𝒪_X`-module `F` and
a degree `n`, the comparison `H^n(X, F) ≅ H^n(S, f_* F)` of [Stacks, Tag 089W] is

> restriction of scalars pulled inside the right derived functor, the crossing of the two models
> of `RΓ(f⁻¹⊤, -)` inverted, the degree-`n` cohomology of the Leray comparison of
> [Stacks, Tag 0D5W] for `f` over `⊤` at `F[0]`, the degree-`n` cohomology of `RΓ(⊤, -)` of the
> collapse of `Rf_*` at `F`, and the crossing of the two models of `RΓ(S, -)`.

This is `cohomologyIsoPushforward_hom_eq` at the derived data the tail of conclusion (c) of
[Stacks, Tag 0EX3] speaks in — the derived direct image, derived sections over `⊤`, derived
sections over `f⁻¹⊤`, and the Leray comparison between them — whose coherence is
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app_refl`. Nothing is proved: the
content is that those four pieces of data satisfy 089W's hypotheses, and no hypothesis is added
beyond affineness of `f` and quasi-coherence of `F`, which 089W itself carries. -/
@[ega "III 1.3.3"]
theorem cohomologyIsoPushforward_hom_eq_lerayComparison :
    (cohomologyIsoPushforward f F n).hom =
      (restrictScalarsRightDerivedIso f F n).hom ≫
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (modulePushforward f.toLRSHom.toShHom ⋙ sectionsOverOpen S.toSheafedSpace ⊤)
            (derivedPreimageSections f.toLRSHom.toShHom ⊤)
            (derivedPreimageSectionsUnit f.toLRSHom.toShHom ⊤)
            (exists_quasiIso_isKInjective X.toSheafedSpace) n).inv.app F ≫
          (DerivedCategory.homologyFunctor
                (ModuleCat.{u} ((structureSheafRing S.toSheafedSpace).obj.obj (op ⊤)))
                (n : ℤ)).map
              ((lerayComparison f.toLRSHom.toShHom ⊤).app
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj F)) ≫
            (DerivedCategory.homologyFunctor
                  (ModuleCat.{u} ((structureSheafRing S.toSheafedSpace).obj.obj (op ⊤)))
                  (n : ℤ)).map
                ((derivedSectionsOverOpen S.toSheafedSpace ⊤).map
                  ((modulePushforward f.toLRSHom.toShHom).singleCollapse
                    (derivedPushforward f.toLRSHom.toShHom)
                    (derivedPushforwardUnit f.toLRSHom.toShHom)
                    (exists_quasiIso_isKInjective X.toSheafedSpace) F
                    (rightAcyclic_pushforward_of_isAffineHom f F))) ≫
              (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                  (sectionsOverOpen S.toSheafedSpace ⊤)
                  (derivedSectionsOverOpen S.toSheafedSpace ⊤)
                  (derivedSectionsOverOpenUnit S.toSheafedSpace ⊤)
                  (exists_quasiIso_isKInjective S.toSheafedSpace) n).hom.app
                ((Scheme.Modules.pushforward f).obj F) :=
  @cohomologyIsoPushforward_hom_eq X S f ‹_› F ‹_›
    (derivedPushforward f.toLRSHom.toShHom) (derivedPushforwardUnit f.toLRSHom.toShHom)
    (inferInstanceAs ((derivedPushforward f.toLRSHom.toShHom).IsRightDerivedFunctor
      (derivedPushforwardUnit f.toLRSHom.toShHom)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))
        (ComplexShape.up ℤ))))
    (derivedSectionsOverOpen S.toSheafedSpace ⊤) (derivedSectionsOverOpenUnit S.toSheafedSpace ⊤)
    (inferInstanceAs ((derivedSectionsOverOpen S.toSheafedSpace ⊤).IsRightDerivedFunctor
      (derivedSectionsOverOpenUnit S.toSheafedSpace ⊤)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.toSheafedSpace))
        (ComplexShape.up ℤ))))
    (derivedPreimageSections f.toLRSHom.toShHom ⊤)
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom ⊤)
    (inferInstanceAs ((derivedPreimageSections f.toLRSHom.toShHom ⊤).IsRightDerivedFunctor
      (derivedPreimageSectionsUnit f.toLRSHom.toShHom ⊤)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))
        (ComplexShape.up ℤ))))
    (lerayComparison f.toLRSHom.toShHom ⊤)
    (exists_quasiIso_isKInjective X.toSheafedSpace)
    (exists_quasiIso_isKInjective S.toSheafedSpace)
    (lerayComparison_fac_app_refl f.toLRSHom.toShHom ⊤) n

/-! ### Cancellations, at variables -/

/-- **An isomorphism read off a right inverse.** At variables of an abstract category, where the
cancellation is free. -/
private theorem inv_eq_of_comp_hom_id {C : Type*} [Category* C] {P Q : C} (e : P ≅ Q)
    {g : Q ⟶ P} (hg : g ≫ e.hom = 𝟙 Q) : e.inv = g :=
  (Category.id_comp e.inv).symm.trans
    (by rw [← hg, Category.assoc, e.hom_inv_id, Category.comp_id])

/-- **A five-fold composite cancelled against its reverse.** Three of the five factors are
cancelled by an isomorphism's own identity and two by a hypothesis. Stated at variables of an
abstract category, so that at the application the unifier never meets a composite spanning the
two spellings of the modules on a scheme. -/
private theorem reverse_comp_id {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ P₅ : C}
    (a : P₀ ≅ P₁) (b : P₂ ≅ P₁) {c₁ : P₂ ⟶ P₃} {c₂ : P₃ ⟶ P₂} (hc : c₂ ≫ c₁ = 𝟙 P₃)
    {d₁ : P₃ ⟶ P₄} {d₂ : P₄ ⟶ P₃} (hd : d₂ ≫ d₁ = 𝟙 P₄) (e : P₄ ≅ P₅) :
    (e.inv ≫ d₂ ≫ c₂ ≫ b.hom ≫ a.inv) ≫ a.hom ≫ b.inv ≫ c₁ ≫ d₁ ≫ e.hom = 𝟙 P₅ := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc c₂, hc, Category.id_comp, ← Category.assoc d₂, hd, Category.id_comp,
    e.inv_hom_id]

/-! ### The match the tail of [Stacks, Tag 0EX3] (c) consumes -/

/-- **[Stacks, Tag 089W] in the model of derived sections, inverted.** The direction the tail of
conclusion (c) of [Stacks, Tag 0EX3] carries: for an affine `f : X ⟶ S`, a quasi-coherent `F` and
a degree `n`, the comparison `H^n(S, f_* F) ≅ H^n(X, F)` of [Stacks, Tag 089W] inverted is

> the crossing of the two models of `RΓ(S, -)` inverted, the degree-`n` cohomology of
> `RΓ(⊤, c)` for a comparison `c : (f_* F)[0] ⟶ Rf_*(F[0])` of the two models of `Rf_*`
> retracting the collapse, a left inverse of the degree-`n` cohomology of the Leray comparison of
> [Stacks, Tag 0D5W], the crossing of the two models of `RΓ(f⁻¹⊤, -)`, and restriction of
> scalars pulled out of the right derived functor.

The two inverses are taken as left inverses of **plain** morphisms, `hc` and `hl`, exactly as
`Stacks.Cohomology.DerivedBaseChange`
`.homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite` takes the Leray one, so that
the two statements compose. Neither costs a hypothesis: the collapse is invertible by
`CategoryTheory.Functor.singleCollapseIso` and the Leray comparison by
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`, both unconditionally. So nothing
is assumed of `f` beyond the affineness [Stacks, Tag 089W] itself assumes, and nothing of `F`
beyond quasi-coherence. -/
@[ega "III 1.3.3"]
theorem cohomologyIsoPushforward_inv_eq_lerayComparison
    {c : (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing S.toSheafedSpace)) 0).obj
          ((modulePushforward f.toLRSHom.toShHom).obj F) ⟶
      (derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj F)}
    (hc : c ≫ (modulePushforward f.toLRSHom.toShHom).singleCollapse
        (derivedPushforward f.toLRSHom.toShHom)
        (derivedPushforwardUnit f.toLRSHom.toShHom)
        (exists_quasiIso_isKInjective X.toSheafedSpace) F
        (rightAcyclic_pushforward_of_isAffineHom f F) = 𝟙 _)
    {lInv : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S.toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).obj
        ((derivedSectionsOverOpen S.toSheafedSpace ⊤).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj F))) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S.toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).obj
        ((derivedPreimageSections f.toLRSHom.toShHom ⊤).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj F))}
    (hl : lInv ≫ (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S.toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).map
        ((lerayComparison f.toLRSHom.toShHom ⊤).app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj F)) = 𝟙 _) :
    (cohomologyIsoPushforward f F n).inv =
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (sectionsOverOpen S.toSheafedSpace ⊤)
            (derivedSectionsOverOpen S.toSheafedSpace ⊤)
            (derivedSectionsOverOpenUnit S.toSheafedSpace ⊤)
            (exists_quasiIso_isKInjective S.toSheafedSpace) n).inv.app
          ((Scheme.Modules.pushforward f).obj F) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing S.toSheafedSpace).obj.obj (op ⊤)))
              (n : ℤ)).map ((derivedSectionsOverOpen S.toSheafedSpace ⊤).map c) ≫
          lInv ≫
            (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                (modulePushforward f.toLRSHom.toShHom ⋙ sectionsOverOpen S.toSheafedSpace ⊤)
                (derivedPreimageSections f.toLRSHom.toShHom ⊤)
                (derivedPreimageSectionsUnit f.toLRSHom.toShHom ⊤)
                (exists_quasiIso_isKInjective X.toSheafedSpace) n).hom.app F ≫
              (restrictScalarsRightDerivedIso f F n).inv := by
  refine inv_eq_of_comp_hom_id _ ?_
  rw [cohomologyIsoPushforward_hom_eq_lerayComparison f F n]
  exact reverse_comp_id (restrictScalarsRightDerivedIso f F n)
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (modulePushforward f.toLRSHom.toShHom ⋙ sectionsOverOpen S.toSheafedSpace ⊤)
      (derivedPreimageSections f.toLRSHom.toShHom ⊤)
      (derivedPreimageSectionsUnit f.toLRSHom.toShHom ⊤)
      (exists_quasiIso_isKInjective X.toSheafedSpace) n).app F)
    hl
    (map_comp_cancel (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing S.toSheafedSpace).obj.obj (op ⊤))) (n : ℤ))
      (map_comp_cancel (derivedSectionsOverOpen S.toSheafedSpace ⊤) hc))
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (sectionsOverOpen S.toSheafedSpace ⊤) (derivedSectionsOverOpen S.toSheafedSpace ⊤)
      (derivedSectionsOverOpenUnit S.toSheafedSpace ⊤)
      (exists_quasiIso_isKInjective S.toSheafedSpace) n).app
        ((Scheme.Modules.pushforward f).obj F))

end Stacks.Cohomology.AffineComparison

end
