module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.PreimageSectionsCollapseMirrorScalars
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeCrossingSections

/-!
# Factor (1) of [Stacks, Tag 089W] matched without brick (i), by the collapse mirror

The `ψ` side of conclusion (c) of [Stacks, Tag 0EX3] carries [Stacks, Tag 089W] inverted in the
reading `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison`, at
`g := h'.resLE (f'⁻¹V) (f''⁻¹W)`, with restriction of scalars along `(f' ∣_ V)^♯` applied to the
whole block. Printed from that statement, its **first** factor is the crossing of the two models
of `RᵈΓ(f'⁻¹V, ⊤, -)` on the open subscheme `(f'⁻¹V : Scheme)`, **inverted**, at the module
`g_* N` — which is not a restriction from the ambient `X'`, so neither existing form of brick (i)
reaches it.

Brick (i) is not needed. The exact functor that this factor's own surroundings supply is the
restriction of scalars along `(f' ∣_ V)^♯`, and it sits on the **outside**, which is the collapse
mirror's shape and not brick (i)'s. So the mirror already proved for factor (4) —
`Stacks.EdgeCompat.singleCompDerivedPreimageSectionsComp_hom_app_comp`
`_restrictScalarsRightDerivedIso_inv` (`PreimageSectionsCollapseMirrorScalars.lean`) — applies to
factor (1) verbatim, at the morphism `f' ∣_ V` out of the open subscheme and the open `⊤` of its
target, and moves the crossing off the absolute sections functor with **nothing assumed**: the
mirror's pointwise homology-preservation hypothesis is `fun _ => inferInstance`, restriction of
scalars being exact.

What the move reaches is the crossing of the two models of `Rⁿ(q_* ⋙ Γ(B, ⊤, -))`, which is the
spelling `…TopDegreeBaseChange.sectionsOverOpenHomologyComparison_comp_map`
`_homologyFunctorDerivedPushforwardIso_hom_eq` (`TopDegreeCrossingSections.lean`) reads the `γ⁺`
side's prefix at. Composing the two eliminates that crossing and leaves factor (1) standing
against the `γ⁺` side's own factors, which is the second result below.

## Where the quasi-coherence is spent, and where it is not

[Stacks, Tag 01XK]'s two halves behave differently here, and the whole point of this route is
which half each factor needs.

* The half the mirror produces —
  `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` at the pair
  `(Γ(q⁻¹⊤, -), res_{q^♯})`, which is
  `Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso` by the dictionary
  `Stacks.EdgeCompat.rightDerivedCompNatIsoTop_inv_app_eq_restrictScalarsRightDerivedIso` — has
  its hypothesis **free**, restriction of scalars being exact. It is factor (5) of
  [Stacks, Tag 089W].
* The half the `γ⁺` prefix needs — the same comparison at the pair `(q_*, Γ(B, ⊤, -))` — is
  Grothendieck's, and its pointwise hypothesis `hpl` is the degeneration of the Leray spectral
  sequence. It is **carried as an explicit hypothesis** in both of the statements this file
  composes, so nothing is assumed here either; a consumer supplies it at the coefficient it
  crosses 01XK at.

So the second result below is factor (1) matched at **whatever** coefficient the consumer can
discharge `hpl` at. In conclusion (c) of [Stacks, Tag 0EX3] that coefficient is `g_* N`, whose
quasi-coherence is `inferInstance` and over whose affine `V` the degeneration is
`Stacks.Cohomology.AffineBase.preservesLeftHomology_pushforward_injectiveResolution`; the
coefficient at which the degeneration is **not** available — the source of the `ψ` side's
transport, which `(h')_*` does not keep quasi-coherent without a hypothesis on `h` — is never
visited, because no naturality of 01XK along that transport is asked for.

## Main results

* `…TopDegreeBaseChange.restrictScalars_singleCompDerivedSectionsTop_inv_app_eq` — **the mirror
  solved for factor (1).** For a morphism of schemes `q : Sq ⟶ B`, a module `M` on `Sq` and a
  degree `n`, restriction of scalars along `q^♯` applied to the crossing of the two models of
  `RⁿΓ(Sq, ⊤, -)` **inverted** at `M` is `restrictScalarsRightDerivedIso`, the crossing of the two
  models of `Rⁿ(q_* ⋙ Γ(B, ⊤, -))` inverted, the degree-`n` cohomology of
  `Stacks.EdgeCompat.preimageSectionsModelComparison q ⊤`, and the edge morphism of the
  restriction of scalars. Nothing is assumed of `q`, of `M` or of `n`.
* `…TopDegreeBaseChange.prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` — **factor (1)
  matched against the `γ⁺` side's prefix.** The edge morphism of `RΓ(B, ⊤, -)` at `Rq_*((E Z)[0])`
  followed by `Γ(B, ⊤, -)` of the crossing of the two models of `Rq_*` is the Leray left inverse,
  then the two mirror factors, then factor (1) **forward**, then factor (5), then Grothendieck's
  comparison inverted and `Γ(B, ⊤, -)` of the comparison of the two indexings.

## Implementation notes

*Why the mirror is solved for its last factor inverted, and what that costs.* The crossing
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` and
`Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso` are isomorphisms by
construction, so the transposition takes `.inv` of each and of nothing else. In particular
**neither `Stacks.EdgeCompat.preimageSectionsModelComparison` nor the edge morphism of the
restriction of scalars is inverted**, and the two invertibility results for them —
`Stacks.EdgeCompat.isIso_preimageSectionsModelComparison` and
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isIso_derivedHomologyComparison_mapDerivedCategory` — are not used. That is what makes the first
result unconditional.

*The two units at the composite's spelling are one term.*
`Stacks.EdgeCompat.derivedPreimageSectionsUnitComp`, which the `γ⁺` prefix is written at, is an
`abbrev` for `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsUnit`, which the
mirror is written at, so the two readings of the crossing of the two models of
`Rⁿ(q_* ⋙ Γ(B, ⊤, -))` are the same term and no crossing is owed between them.

*The index functor is left general.* Both inputs are stated for an arbitrary
`E : Dc ⥤ Mod(𝒪_{Sq})`, because Grothendieck's comparison is; the consumer in conclusion (c)
instantiates it at the inclusion of the quasi-coherent modules, where its `hpl` is available, and
an `(𝟭 _).obj` in that slot causes unfolding problems. Nothing here needs `E` to be either.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 089W] and [Stacks, Tag 01XK] carry theirs
where they are proved, and conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.EdgeCompat
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison)

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Cancellations, at variables -/

/-- **A functor applied to an isomorphism's inverse, read off a factorisation of the forward
direction.** From `a.hom ≫ e.inv = m ≫ G.map κ.hom` with `a` and `e` isomorphisms and `m` a plain
morphism, `G.map κ.inv` is `e.hom`, `a.inv` and `m`. Nothing is assumed of `m`, so no inverse of
any of its factors is taken; stated at variables of abstract categories, where every
reassociation is free. -/
private theorem map_inv_eq_of_comp_inv_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {Q₁ Q₂ : C} (κ : Q₁ ≅ Q₂) {P Q : D} (a : P ≅ Q) (e : G.obj Q₂ ≅ Q)
    {m : P ⟶ G.obj Q₁} (h : a.hom ≫ e.inv = m ≫ G.map κ.hom) :
    G.map κ.inv = e.hom ≫ a.inv ≫ m := by
  rw [← cancel_mono (G.map κ.hom), Category.assoc, Category.assoc, ← h]
  simp

/-- **An isomorphism's inverse moved out of a three-fold factorisation.** From
`a ≫ e.inv = m₁ ≫ m₂ ≫ m₃` one gets `a = m₁ ≫ m₂ ≫ m₃ ≫ e.hom`, right-associated. At variables
of an abstract category. -/
private theorem eq_comp_hom_of_comp_inv_eq {C : Type*} [Category* C] {P T Q R₁ R₂ : C} (e : T ≅ Q)
    {a : P ⟶ Q} {m₁ : P ⟶ R₁} {m₂ : R₁ ⟶ R₂} {m₃ : R₂ ⟶ T}
    (h : a ≫ e.inv = m₁ ≫ m₂ ≫ m₃) : a = m₁ ≫ m₂ ≫ m₃ ≫ e.hom := by
  simp [← reassoc_of% h]

/-- **A middle factor of a known factorisation replaced by a four-fold one.** From
`lhs = l ≫ (c ≫ r) ≫ s` and `c = m₁ ≫ m₂ ≫ m₃ ≫ m₄` one gets the right-associated
`lhs = l ≫ m₁ ≫ m₂ ≫ m₃ ≫ m₄ ≫ r ≫ s`. At variables of an abstract category, where the
reassociation is free. -/
private theorem trans_subst_middle {C : Type*} [Category* C]
    {A P₀ Q₁ Q₂ Q₃ P₁ P₂ T : C} {lhs : A ⟶ T} {l : A ⟶ P₀} {c : P₀ ⟶ P₁} {r : P₁ ⟶ P₂}
    {s : P₂ ⟶ T} (h : lhs = l ≫ (c ≫ r) ≫ s)
    {m₁ : P₀ ⟶ Q₁} {m₂ : Q₁ ⟶ Q₂} {m₃ : Q₂ ⟶ Q₃} {m₄ : Q₃ ⟶ P₁}
    (hc : c = m₁ ≫ m₂ ≫ m₃ ≫ m₄) :
    lhs = l ≫ m₁ ≫ m₂ ≫ m₃ ≫ m₄ ≫ r ≫ s := by
  rw [h, hc]
  simp only [Category.assoc]

/-! ### The mirror solved for factor (1) -/

variable {Sq B : Scheme.{u}} (q : Sq ⟶ B) (n : ℕ)

/-- **Factor (1) of [Stacks, Tag 089W], moved off the absolute sections functor by the collapse
mirror.** For a morphism of schemes `q : Sq ⟶ B`, a sheaf of modules `M` on `Sq` and a degree `n`,

> restriction of scalars along `q^♯` applied to the crossing of the two models of
> `RⁿΓ(Sq, ⊤, -)` **inverted** at `M` is
> `Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso q M n`, then the crossing of
> the two models of `Rⁿ(q_* ⋙ Γ(B, ⊤, -))` inverted at `M`, then the degree-`n` cohomology of
> `Stacks.EdgeCompat.preimageSectionsModelComparison q ⊤` at `M[0]`, then the edge morphism of
> restriction of scalars along `q^♯` at `RΓ(q⁻¹⊤, M[0])`.

The left-hand side is the first factor of
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison`, read under
the restriction of scalars that the `ψ` side of conclusion (c) of [Stacks, Tag 0EX3] applies to
the whole of [Stacks, Tag 089W] inverted; `M` is **arbitrary**, in particular not assumed to be a
restriction from an ambient scheme, which is the hypothesis both existing forms of brick (i) need
and neither gets at this factor.

This is `Stacks.EdgeCompat.singleCompDerivedPreimageSectionsComp_hom_app_comp`
`_restrictScalarsRightDerivedIso_inv` transposed at its two isomorphism factors. **Nothing is
assumed** of `q`, of `M` or of `n` — no affineness, no acyclicity, no boundedness and no
quasi-coherence — and in particular neither `preimageSectionsModelComparison` nor the edge
morphism of the restriction of scalars is inverted. -/
theorem restrictScalars_singleCompDerivedSectionsTop_inv_app_eq
    (M : SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace)) :
    (preimageRestrictScalars q.toLRSHom.toShHom ⊤).map
        ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (sectionsOverOpen Sq.toSheafedSpace ((opensMap q.toLRSHom.toShHom).obj ⊤))
          (derivedSectionsOverOpen Sq.toSheafedSpace ((opensMap q.toLRSHom.toShHom).obj ⊤))
          (derivedSectionsOverOpenUnit Sq.toSheafedSpace
            ((opensMap q.toLRSHom.toShHom).obj ⊤))
          (exists_quasiIso_isKInjective Sq.toSheafedSpace) n).inv.app M) =
      (Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso q M n).hom ≫
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
              (modulePushforward q.toLRSHom.toShHom ⋙ sectionsOverOpen B.toSheafedSpace ⊤)
              (derivedPreimageSections q.toLRSHom.toShHom ⊤)
              (derivedPreimageSectionsUnit q.toLRSHom.toShHom ⊤)
              (exists_quasiIso_isKInjective Sq.toSheafedSpace) n).inv.app M ≫
          (DerivedCategory.homologyFunctor
                (ModuleCat.{u} ((structureSheafRing B.toSheafedSpace).obj.obj (op ⊤)))
                (n : ℤ)).map
              ((preimageSectionsModelComparison q.toLRSHom.toShHom ⊤).app
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace)) 0).obj M)) ≫
            (derivedHomologyComparison (preimageRestrictScalars q.toLRSHom.toShHom ⊤)
                  (preimageRestrictScalars q.toLRSHom.toShHom ⊤).mapDerivedCategory
                  (preimageRestrictScalars q.toLRSHom.toShHom
                    ⊤).mapDerivedCategoryFactorsh.inv
                  (exists_quasiIso_isKInjective_preimageSectionsRing
                    q.toLRSHom.toShHom ⊤) (n : ℤ)).app
              ((derivedSectionsOverOpen Sq.toSheafedSpace
                  ((opensMap q.toLRSHom.toShHom).obj ⊤)).obj
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace)) 0).obj M)) :=
  map_inv_eq_of_comp_inv_eq (preimageRestrictScalars q.toLRSHom.toShHom ⊤)
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (sectionsOverOpen Sq.toSheafedSpace ((opensMap q.toLRSHom.toShHom).obj ⊤))
      (derivedSectionsOverOpen Sq.toSheafedSpace ((opensMap q.toLRSHom.toShHom).obj ⊤))
      (derivedSectionsOverOpenUnit Sq.toSheafedSpace ((opensMap q.toLRSHom.toShHom).obj ⊤))
      (exists_quasiIso_isKInjective Sq.toSheafedSpace) n).app M)
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (modulePushforward q.toLRSHom.toShHom ⋙ sectionsOverOpen B.toSheafedSpace ⊤)
      (derivedPreimageSections q.toLRSHom.toShHom ⊤)
      (derivedPreimageSectionsUnit q.toLRSHom.toShHom ⊤)
      (exists_quasiIso_isKInjective Sq.toSheafedSpace) n).app M)
    (Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso q M n)
    (singleCompDerivedPreimageSectionsComp_hom_app_comp_restrictScalarsRightDerivedIso_inv
      q n (E := Functor.id _) M)

/-! ### Factor (1) against the `γ⁺` side's prefix -/

variable {Dc : Type*} [Category* Dc]
  (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace))

/-- **Factor (1) of [Stacks, Tag 089W] matched against the `γ⁺` side's prefix, with no brick (i)
and no [Stacks, Tag 01XK] at a coefficient other than the one the consumer supplies `hpl` at.**
For a morphism of schemes `q : Sq ⟶ B`, a functor `E : Dc ⥤ Mod(𝒪_{Sq})`, an object `Z` and a
degree `n`, the composite

> the edge morphism of `RΓ(B, ⊤, -)` at `Rq_*((E Z)[0])`, then `Γ(B, ⊤, -)` of the crossing of
> the two models of `Rq_*`

— which is the prefix the tail of conclusion (c) of [Stacks, Tag 0EX3] meets on the `γ⁺` side, by
`sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq` — is

> the Leray left inverse, the degree-`n` cohomology of
> `Stacks.EdgeCompat.preimageSectionsModelComparison q ⊤`, the edge morphism of restriction of
> scalars along `q^♯`, **factor (1) of [Stacks, Tag 089W]** — restriction of scalars applied to
> the crossing of the two models of `RⁿΓ(Sq, ⊤, -)` at `E Z` — then **factor (5)**,
> `Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso`, then Grothendieck's
> comparison at the pair `(q_*, Γ(B, ⊤, -))` inverted and `Γ(B, ⊤, -)` of the comparison of the
> two indexings.

So factor (1) stands against the `γ⁺` side's own factors with **the crossing of the two models of
`Rⁿ(q_* ⋙ Γ(B, ⊤, -))` eliminated between them**, and the module `E Z` is arbitrary: it is not
assumed to be a restriction from an ambient scheme, which is what both existing forms of brick (i)
need at this factor and neither gets.

The two hypotheses are the ones its two inputs carry and nothing more. `hpl` is Grothendieck's
pointwise homology-preservation hypothesis at the pair `(q_*, Γ(B, ⊤, -))` — the degeneration of
the Leray spectral sequence, which over an affine `B` is [Stacks, Tag 01XB] and needs the
coefficient quasi-coherent; and `hl` is a left inverse of the degree-`n` cohomology of the Leray
comparison of [Stacks, Tag 0D5W], which
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison` supplies **unconditionally**. The
other half of [Stacks, Tag 01XK] — the comparison at the pair `(Γ(q⁻¹⊤, -), res_{q^♯})`, which is
factor (5) — carries its hypothesis for free, restriction of scalars being exact, so it does not
appear. Nothing is assumed of `q`, of `E`, of `Z` or of `n`. -/
theorem prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv
    (hpl : ∀ Z : Dc, (sectionsOverOpen B.toSheafedSpace ⊤).PreservesLeftHomologyOf
      ((((modulePushforward q.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (Z : Dc)
    [(sectionsOverOpen B.toSheafedSpace ⊤).PreservesLeftHomologyOf
      ((((modulePushforward q.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution (E.obj Z)).cocomplex).sc n)]
    {lInv : (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing B.toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).obj
        ((derivedSectionsOverOpen B.toSheafedSpace ⊤).obj
          ((derivedPushforward q.toLRSHom.toShHom).obj
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace)) 0).obj
              (E.obj Z)))) ⟶
      (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing B.toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).obj
        ((derivedPreimageSections q.toLRSHom.toShHom ⊤).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace)) 0).obj
            (E.obj Z)))}
    (hl : lInv ≫ (homologyFunctor
            (ModuleCat.{u} ((structureSheafRing B.toSheafedSpace).obj.obj (op ⊤))) (n : ℤ)).map
          ((lerayComparison q.toLRSHom.toShHom ⊤).app
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace)) 0).obj
              (E.obj Z))) = 𝟙 _) :
    (derivedHomologyComparison (sectionsOverOpen B.toSheafedSpace ⊤)
            (derivedSectionsOverOpen B.toSheafedSpace ⊤)
            (derivedSectionsOverOpenUnit B.toSheafedSpace ⊤)
            (exists_quasiIso_isKInjective B.toSheafedSpace) (n : ℤ)).app
          ((derivedPushforward q.toLRSHom.toShHom).obj
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace)) 0).obj
              (E.obj Z))) ≫
        (sectionsOverOpen B.toSheafedSpace ⊤).map
          (homologyFunctorDerivedPushforwardIso q (E.obj Z) (n : ℤ)).hom =
      lInv ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing B.toSheafedSpace).obj.obj (op ⊤)))
              (n : ℤ)).map
            ((preimageSectionsModelComparison q.toLRSHom.toShHom ⊤).app
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace)) 0).obj (E.obj Z))) ≫
          (derivedHomologyComparison (preimageRestrictScalars q.toLRSHom.toShHom ⊤)
                (preimageRestrictScalars q.toLRSHom.toShHom ⊤).mapDerivedCategory
                (preimageRestrictScalars q.toLRSHom.toShHom
                  ⊤).mapDerivedCategoryFactorsh.inv
                (exists_quasiIso_isKInjective_preimageSectionsRing
                  q.toLRSHom.toShHom ⊤) (n : ℤ)).app
              ((derivedSectionsOverOpen Sq.toSheafedSpace
                  ((opensMap q.toLRSHom.toShHom).obj ⊤)).obj
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing Sq.toSheafedSpace)) 0).obj
                    (E.obj Z))) ≫
            (preimageRestrictScalars q.toLRSHom.toShHom ⊤).map
                ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                  (sectionsOverOpen Sq.toSheafedSpace ((opensMap q.toLRSHom.toShHom).obj ⊤))
                  (derivedSectionsOverOpen Sq.toSheafedSpace
                    ((opensMap q.toLRSHom.toShHom).obj ⊤))
                  (derivedSectionsOverOpenUnit Sq.toSheafedSpace
                    ((opensMap q.toLRSHom.toShHom).obj ⊤))
                  (exists_quasiIso_isKInjective Sq.toSheafedSpace) n).hom.app (E.obj Z)) ≫
              (Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso q
                  (E.obj Z) n).hom ≫
                (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso E
                    (modulePushforward q.toLRSHom.toShHom)
                    (sectionsOverOpen B.toSheafedSpace ⊤) n hpl).inv.app Z ≫
                  (sectionsOverOpen B.toSheafedSpace ⊤).map
                    ((Stacks.DerivedIndexing.rightDerivedIso
                      (modulePushforward q.toLRSHom.toShHom) n).hom.app (E.obj Z)) :=
  trans_subst_middle
    (sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq
      q ⊤ n E hpl Z hl)
    (eq_comp_hom_of_comp_inv_eq
      (Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso q (E.obj Z) n)
      (singleCompDerivedPreimageSectionsComp_hom_app_comp_restrictScalarsRightDerivedIso_inv
        q n E Z))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
