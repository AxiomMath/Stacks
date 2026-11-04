module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymExtPowFunctorial
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictSheafification
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Vanishing07LMAffineReduction

/-!
# The transport of the coefficients of [Stacks, Tag 07LM] from two module-level inputs

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].
`Crystalline.GlobalCrystallineSituation.SmallSite.Transport07LMForms` of
`SmallSite/Vanishing07LMAffineReduction.lean` is the last step of the proof of
[Stacks, Tag 07LM] to land: the restriction to `Cris(V/S|_W)` of the sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is the corresponding sheaf of the restricted situation, for a sheaf of
`𝒪_{V/S|_W}`-modules again satisfying conditions (1) and (2) of [Stacks, Tag 07JN].

This file reduces it to **two statements about presheaves of modules**, with every passage between
presheaves and sheaves and every compatibility of the tensor product and the exterior power
discharged:

1. `Ω_{V/S|_W} ≅ Ω_{X/S}|` — the crystalline differentials of the restricted situation are the
   restriction of those of `S` along `smallExtend`;
2. a sheaf of `𝒪_{X/S}`-modules satisfying conditions (1) and (2) of [Stacks, Tag 07JN]
   restricts, as a *sheaf* of `𝒪_{V/S|_W}`-modules, to one that again satisfies them.

Neither is proved here, and both are now theorems elsewhere: (1) is
`...SmallSite.smallExtendCrysDifferentialsIso` of
`SmallSite/RestrictCrystallineDifferentials.lean` and (2) is
`...SmallSite.exists_smallExtendRestriction_of_vanishingHypotheses` of
`SmallSite/RestrictQuasiCoherent.lean`.  `...SmallSite.transport07LMForms` of
`SmallSite/Vanishing07LMProof.lean` feeds them to the theorem below and so proves
`Transport07LMForms` outright.

## Why nothing else is needed

Restriction along `smallExtend` is precomposition on presheaves, the structure sheaves of the two
sites agreeing on the nose (`...SmallSite.structurePresheaf_restrict`), so it carries the tensor
product to the tensor product and `Ω^i_{X/S}` to the `i`-th exterior power of the restriction of
`Ω_{X/S}`, both on the nose
(`...SmallSite.smallExtendModuleRestriction_obj_tensorObj` and
`...SmallSite.smallExtendModuleRestriction_obj_crysDifferentialForms`).  With (1) the degree-`i`
coefficient presheaf of the restricted situation is therefore the restriction of the degree-`i`
coefficient presheaf of `S`, up to the isomorphism `PresheafOfModules.extPowMap` produces from
(1).  Sheafification then commutes with the restriction, [Stacks, Tag 00XR] in the form
`...SmallSite.smallExtendAbelianRestrictionCompPresheafToSheafIso`, which turns that into the
isomorphism of abelian sheaves `Transport07LMForms` asks for.

## What is and is not proved

The two inputs are hypotheses of the theorem below and are proved elsewhere: both are theorems,
`...SmallSite.smallExtendCrysDifferentialsIso` and
`...SmallSite.exists_smallExtendRestriction_of_vanishingHypotheses`, and
`...SmallSite.transport07LMForms` of `SmallSite/Vanishing07LMProof.lean` combines them with the
reduction below into a proof of `Transport07LMForms`, hence — through
`...SmallSite.vanishing07LM_of_transport07LMForms` — of the vanishing clause of
[Stacks, Tag 07LM] at the generality of [Stacks, Tag 07LN].

**No `@[stacks]` attribute is placed**: nothing here is an assertion of the chapter.  The clauses
of [Stacks, Tag 07LM] and [Stacks, Tag 07LN] that this reduction serves are registered where they
are proved, in `SmallSite/Vanishing07LMProof.lean`.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `smallExtendModuleRestrictionTensorIso` — the degree-`i` coefficient presheaf of the restricted
  situation is the restriction of the one of `S`, given input (1).
* `smallExtendAbelianRestrictionTensorSheafIso` — the same on abelian sheaves, given the
  module-level isomorphism.
* `transport07LMForms_of_crysDifferentialsIso` — **`Transport07LMForms` from the two inputs**.

## References

* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-- **The exterior power of an isomorphism of presheaves of modules.**  Both directions are
`PresheafOfModules.extPowMap` and they compose to the identity by `extPowMap_comp` and
`extPowMap_id`. -/
def extPowIso (i : ℕ)
    {M N : PresheafOfModules.{u} (structurePresheaf (restrict S W V hVW) ⋙
      forget₂ CommRingCat RingCat)} (e : M ≅ N) :
    PresheafOfModules.extPow i M ≅ PresheafOfModules.extPow i N where
  hom := PresheafOfModules.extPowMap i e.hom
  inv := PresheafOfModules.extPowMap i e.inv
  hom_inv_id := by
    rw [← PresheafOfModules.extPowMap_comp, e.hom_inv_id, PresheafOfModules.extPowMap_id]
  inv_hom_id := by
    rw [← PresheafOfModules.extPowMap_comp, e.inv_hom_id, PresheafOfModules.extPowMap_id]

/-- **The degree-`i` coefficient presheaf of the restricted situation is the restriction of the
one of `S`**, given that the crystalline differentials restrict.  Restriction carries the tensor
product to the tensor product and `Ω^i_{X/S}` to the `i`-th exterior power of the restriction of
`Ω_{X/S}`, both on the nose, and the hypothesis replaces that exterior power by `Ω^i_{V/S|_W}`. -/
def smallExtendModuleRestrictionTensorIso
    (eΩ : (smallExtendModuleRestriction S W V hVW).obj (crysDifferentials S) ≅
      crysDifferentials (restrict S W V hVW))
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) (i : ℕ) :
    (smallExtendModuleRestriction S W V hVW).obj (tensorDifferentialForms M i) ≅
      tensorDifferentialForms ((smallExtendModuleRestriction S W V hVW).obj M) i :=
  eqToIso (smallExtendModuleRestriction_obj_tensorObj S W V hVW _ _) ≪≫
    whiskerLeftIso _
      (eqToIso (smallExtendModuleRestriction_obj_crysDifferentialForms S W V hVW i) ≪≫
        extPowIso S W V hVW i eΩ)

/-- **The restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` as an abelian sheaf on `Cris(V/S|_W)**, given
the module-level comparison.  Both sheaves are sheafifications of the underlying abelian
presheaves of the two tensor products, and restriction of abelian sheaves commutes with
sheafification by `smallExtendAbelianRestrictionCompPresheafToSheafIso`. -/
def smallExtendAbelianRestrictionTensorSheafIso
    (F : SheafOfModules.{u} (structureSheaf S))
    (F' : SheafOfModules.{u} (structureSheaf (restrict S W V hVW))) (i : ℕ)
    (e : (smallExtendModuleRestriction S W V hVW).obj
        (tensorDifferentialForms
          (F.val : PresheafOfModules.{u}
            (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) ≅
      tensorDifferentialForms
        (F'.val : PresheafOfModules.{u}
          (structurePresheaf (restrict S W V hVW) ⋙ forget₂ CommRingCat RingCat)) i) :
    (smallExtendAbelianRestriction S W V hVW).obj (tensorDifferentialFormsSheaf F i) ≅
      tensorDifferentialFormsSheaf F' i :=
  ((smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW).app
      ((PresheafOfModules.toPresheaf _).obj
          (tensorDifferentialForms
            (F.val : PresheafOfModules.{u}
              (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u})).symm ≪≫
    (presheafToSheaf (smallTopology (restrict S W V hVW)) AddCommGrpCat.{u + 1}).mapIso
      (Functor.isoWhiskerRight ((PresheafOfModules.toPresheaf _).mapIso e)
        AddCommGrpCat.uliftFunctor.{u + 1, u})

section Transport

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] in
/-- **The transport of the coefficients of [Stacks, Tag 07LM] from two module-level inputs.**

The first input is that the crystalline differentials of a restricted situation are the
restriction of those of `S` along `smallExtend`; the second is that a sheaf of `𝒪_{X/S}`-modules
satisfying conditions (1) and (2) of [Stacks, Tag 07JN] restricts to a sheaf of
`𝒪_{V/S|_W}`-modules satisfying them, whose underlying presheaf is the restriction of the given
one.  Everything else — the tensor product, the exterior power, and the passage from presheaves to
sheaves — is discharged by `smallExtendModuleRestrictionTensorIso` and
`smallExtendAbelianRestrictionTensorSheafIso`.

With `vanishing07LM_of_transport07LMForms` this is the whole of the vanishing clause of
[Stacks, Tag 07LM] from those two statements, and both are now theorems:
`smallExtendCrysDifferentialsIso` and `exists_smallExtendRestriction_of_vanishingHypotheses`.
`...SmallSite.transport07LMForms` of `SmallSite/Vanishing07LMProof.lean` is this theorem applied
to them.  **No tag attribute is placed here**: this is the reduction, and the clauses it yields
are registered at that application. -/
theorem transport07LMForms_of_crysDifferentialsIso
    (eΩ : ∀ (W : S.S.scheme.Opens) (V : S.X.Opens) (hVW : V ≤ sourceToBase S ⁻¹ᵁ W),
      (smallExtendModuleRestriction S W V hVW).obj (crysDifferentials S) ≅
        crysDifferentials (restrict S W V hVW))
    (hres : ∀ (W : S.S.scheme.Opens) (V : S.X.Opens) (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)
      (F : SheafOfModules.{u} (structureSheaf S)), IsLocallyQuasiCoherent F →
        CohomologyRestriction.IsSurjectiveComparison F.val →
          ∃ F' : SheafOfModules.{u} (structureSheaf (restrict S W V hVW)),
            IsLocallyQuasiCoherent F' ∧
              CohomologyRestriction.IsSurjectiveComparison F'.val ∧
              Nonempty ((smallExtendModuleRestriction S W V hVW).obj
                  (F.val : PresheafOfModules.{u}
                    (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) ≅
                (F'.val : PresheafOfModules.{u}
                  (structurePresheaf (restrict S W V hVW) ⋙ forget₂ CommRingCat RingCat)))) :
    Transport07LMForms S := by
  intro W V hVW _ _ F hqc hsurj i
  obtain ⟨F', hqc', hsurj', ⟨eF⟩⟩ := hres W V hVW F hqc hsurj
  refine ⟨F', hqc', hsurj', ⟨smallExtendAbelianRestrictionTensorSheafIso S W V hVW F F' i ?_⟩⟩
  exact smallExtendModuleRestrictionTensorIso S W V hVW (eΩ W V hVW) _ i ≪≫
    whiskerRightIso eF _

end Transport

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
