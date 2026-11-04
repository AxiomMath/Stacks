module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AmpleFibreTwistLocalBase
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalBaseIdeal
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# The reduction of Tag 0D2M to a local base, over an arbitrary base

[Stacks, Tag 0D2M] is about a proper morphism `f : X ⟶ Y` with `Y` Noetherian, an invertible
`𝒪_X`-module `ℒ`, a coherent `𝒪_X`-module `ℱ` and a point `y ∈ Y` at which `ℒ_y` is ample on the
fibre `X_y`; it produces a `d₀` such that for `d ≥ d₀` the stalk `R ᵖ f_*(ℱ ⊗ ℒ ^⊗ d)_y` vanishes
for `p > 0` and `f_*(ℱ ⊗ ℒ ^⊗ d)_y ⟶ H ⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)` is surjective.

The source's proof opens by base changing along the flat morphism `Spec 𝒪_{Y,y} ⟶ Y`, which
replaces `Y` by the spectrum of a Noetherian local ring and `y` by its closed point;
`StacksFrontier/AlgebraicGeometry/FormalFunctions/AmpleFibreTwistLocalBase.lean` proves both
clauses in that situation. This file carries out the part of that opening paragraph which does
*not* need flat base change: it identifies the fibre `X_y` with the closed subscheme of

  `X' = X ×_Y Spec 𝒪_{Y,y}`

cut out by `𝔪_y · 𝒪_{X'}`, moves the ampleness hypothesis across that identification, and so
states both clauses of [Stacks, Tag 0D2M] for `X'` over `Spec 𝒪_{Y,y}` **under the source's own
hypothesis on `ℒ`**, namely ampleness of `ℒ_y` on the fibre `X_y` of `f` itself.

What is left over is exactly flat base change: an identification of `H ᵖ(X', ℱ' ⊗ ℒ' ^⊗ d)` with
the stalk `R ᵖ f_*(ℱ ⊗ ℒ ^⊗ d)_y`. See "What is not proved" below.

## Main definitions

* `Stacks.FormalFunctions.fiberIsoInfinitesimalBaseIdealSubscheme` — **the fibre as an
  ideal-power subscheme of the base change**: `X_y ≅ V(𝔪_y 𝒪_{X'})`.

## Main results

* `Stacks.FormalFunctions.fiberIsoInfinitesimalBaseIdealSubscheme_hom_comp` — the identification
  is compatible with the two morphisms to `X`, so a module pulled back to the fibre is the same
  as one pulled back to the subscheme.
* `Stacks.FormalFunctions.isAmple_pullbackModule_subschemeι_of_isAmple_fiber` — **the ampleness
  hypothesis of [Stacks, Tag 0D2M] in the form the local-base theorem consumes**: if `ℒ_y` is
  ample on `X_y` then the pullback of `ℒ` to `V(𝔪_y 𝒪_{X'})` is ample there.
* `Stacks.FormalFunctions.exists_subsingleton_and_surjective_twistModule_stalkBaseChange` —
  **both clauses of [Stacks, Tag 0D2M] on the base change `X' = X ×_Y Spec 𝒪_{Y,y}`, with `Y`
  only locally Noetherian and with ampleness asked of `ℒ_y` on `X_y`.**

## Implementation notes

The fibre identification is a composite of two existing isomorphisms and not a new construction:
`Stacks.FormalFunctions.fiberIsoInfinitesimalNeighbourhoodOne` identifies `X_y` with the first
infinitesimal neighbourhood `X_1` of the fibre, and
`Stacks.FormalFunctions.infinitesimalNeighbourhoodIsoSubscheme` identifies `X_n` with the
subscheme of `(𝔪_y 𝒪_{X'}) ^ n`; at `n = 1` the two compose, and `pow_one` contracts the
exponent. Both compatibilities are read off the compatibilities those two isomorphisms already
carry, so nothing is chased through either construction.

Ampleness is moved by `Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso` along the inverse of
that identification and then transported along an isomorphism of modules by
`Stacks.RelativeVeryAmple.isAmple_congr`; the module isomorphism is the composition law
`Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso` twice, with
`Stacks.RelativeAmpleBaseChange.pullbackModuleCongr` crossing the equality of the two composites
`X_y ⟶ X`.

The local-base theorem is applied with `@` and its `IsLocalRing` and `IsNoetherianRing`
instances supplied by name. Elaborated by application, the instance
`IsLocalRing ↥(𝒪_{Y,y})` is not found, for the reason recorded at
`StacksFrontier/AlgebraicGeometry/FormalFunctions/StalkFormalFunctionsFrom02O8.lean`, which
instantiates the affine side of the theorem on formal functions at the same ring in the same
way.

## What is not proved

**No `@[stacks 0D2M]` attribute is attached here, and none may be.** The tag's conclusions are
about the stalks `R ᵖ f_*(ℱ(d))_y` and `f_*(ℱ(d))_y` on `Y`, and what is proved below is about
`H ᵖ(X', ℱ'(d))` on the base change. The two are identified by [Stacks, Tag 02KH] part (1) along
the flat morphism `Spec 𝒪_{Y,y} ⟶ Y`. That passage is carried out in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/AmpleFibreTwistStalkVanishing.lean` for the
vanishing clause and in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/AmpleFibreTwistStalkSurjective.lean` for the
surjectivity clause; the tag's own site is the latter's
`Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_and_surjective_fiberTwist`.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FormalFunctions

open Stacks.Ample
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.Cohomology.FormalFunctions Stacks.AlgebraicGeometry.HyperplaneTwistSequence

variable {X Y : Scheme.{u}}

/-! ### The fibre as an ideal-power subscheme of the base change -/

/-- The projection `X_1 ⟶ X` of the first infinitesimal neighbourhood, read on `X_y`: the
comparison `X_y ⟶ X_1` is a lift of `f.fiberι y`, so composing it with the projection returns
that morphism. -/
public theorem fiberToInfinitesimalNeighbourhoodOne_comp_ι (f : X ⟶ Y) (y : Y) :
    fiberToInfinitesimalNeighbourhoodOne f y ≫ infinitesimalι f y 1 = f.fiberι y := by
  rw [fiberToInfinitesimalNeighbourhoodOne]
  exact Limits.pullback.lift_fst _ _ _

/-- **The fibre `X_y` is the closed subscheme of `X' = X ×_Y Spec 𝒪_{Y,y}` cut out by the first
power of `𝔪_y · 𝒪_{X'}`.** The composite of
`Stacks.FormalFunctions.fiberIsoInfinitesimalNeighbourhoodOne`, which identifies `X_y` with the
first infinitesimal neighbourhood of the fibre, with
`Stacks.FormalFunctions.infinitesimalNeighbourhoodIsoSubscheme` at `n = 1`. -/
public def fiberIsoInfinitesimalBaseIdealSubschemePow (f : X ⟶ Y) (y : Y) :
    f.fiber y ≅ (infinitesimalBaseIdealSheaf f y ^ 1).subscheme :=
  fiberIsoInfinitesimalNeighbourhoodOne f y ≪≫
    (infinitesimalNeighbourhoodIsoSubscheme f y 1).symm

/-- The identification of `Stacks.FormalFunctions.fiberIsoInfinitesimalBaseIdealSubschemePow` is
compatible with the two morphisms to `X`: the inclusion of the subscheme into `X'` followed by
the projection `X' ⟶ X` is `f.fiberι y`. -/
public theorem fiberIsoInfinitesimalBaseIdealSubschemePow_hom_comp (f : X ⟶ Y) (y : Y) :
    (fiberIsoInfinitesimalBaseIdealSubschemePow f y).hom ≫
        ((infinitesimalBaseIdealSheaf f y ^ 1).subschemeι ≫ stalkBaseChangeι f y) =
      f.fiberι y := by
  have h1 : (infinitesimalBaseIdealSheaf f y ^ 1).subschemeι ≫ stalkBaseChangeι f y =
      (infinitesimalNeighbourhoodIsoSubscheme f y 1).hom ≫ infinitesimalι f y 1 := by
    rw [← infinitesimalNeighbourhoodIsoSubscheme_hom_comp_ιBaseChange f y 1, Category.assoc,
      infinitesimalιBaseChange_comp_ι]
  rw [fiberIsoInfinitesimalBaseIdealSubschemePow, Iso.trans_hom, Iso.symm_hom, h1,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact fiberToInfinitesimalNeighbourhoodOne_comp_ι f y

/-- **The fibre `X_y` is the closed subscheme of `X' = X ×_Y Spec 𝒪_{Y,y}` cut out by
`𝔪_y · 𝒪_{X'}`.** This is
`Stacks.FormalFunctions.fiberIsoInfinitesimalBaseIdealSubschemePow` with the exponent `1`
contracted, which is the spelling the local-base form of [Stacks, Tag 0D2M] uses. -/
public def fiberIsoInfinitesimalBaseIdealSubscheme (f : X ⟶ Y) (y : Y) :
    f.fiber y ≅ (infinitesimalBaseIdealSheaf f y).subscheme :=
  fiberIsoInfinitesimalBaseIdealSubschemePow f y ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (pow_one (infinitesimalBaseIdealSheaf f y)))

/-- `Stacks.FormalFunctions.fiberIsoInfinitesimalBaseIdealSubschemePow_hom_comp` with the
exponent `1` contracted. -/
public theorem fiberIsoInfinitesimalBaseIdealSubscheme_hom_comp (f : X ⟶ Y) (y : Y) :
    (fiberIsoInfinitesimalBaseIdealSubscheme f y).hom ≫
        ((infinitesimalBaseIdealSheaf f y).subschemeι ≫ stalkBaseChangeι f y) =
      f.fiberι y := by
  have h2 : eqToHom (congrArg Scheme.IdealSheafData.subscheme
          (pow_one (infinitesimalBaseIdealSheaf f y))) ≫
        ((infinitesimalBaseIdealSheaf f y).subschemeι ≫ stalkBaseChangeι f y) =
      (infinitesimalBaseIdealSheaf f y ^ 1).subschemeι ≫ stalkBaseChangeι f y := by
    rw [← Category.assoc, Stacks.PuncturedSpectrumPicard.subscheme_eqToHom_comp_subschemeι _ _
      (pow_one (infinitesimalBaseIdealSheaf f y))]
  rw [fiberIsoInfinitesimalBaseIdealSubscheme, Iso.trans_hom, eqToIso.hom, Category.assoc, h2]
  exact fiberIsoInfinitesimalBaseIdealSubschemePow_hom_comp f y

/-- The two morphisms `X_y ⟶ X` agree: the inverse of the fibre identification followed by
`f.fiberι y` is the inclusion of the subscheme into `X'` followed by `X' ⟶ X`. -/
public theorem inv_fiberIsoInfinitesimalBaseIdealSubscheme_comp_fiberι (f : X ⟶ Y) (y : Y) :
    (fiberIsoInfinitesimalBaseIdealSubscheme f y).inv ≫ f.fiberι y =
      (infinitesimalBaseIdealSheaf f y).subschemeι ≫ stalkBaseChangeι f y := by
  rw [← fiberIsoInfinitesimalBaseIdealSubscheme_hom_comp f y, Iso.inv_hom_id_assoc]

/-! ### The ampleness hypothesis of Tag 0D2M on the base change -/

/-- **The ampleness hypothesis of [Stacks, Tag 0D2M], read on the base change.** If `ℒ_y` is
ample on the fibre `X_y`, then the pullback of `ℒ` to the closed subscheme of
`X' = X ×_Y Spec 𝒪_{Y,y}` cut out by `𝔪_y · 𝒪_{X'}` is ample there.

Ampleness is carried along the inverse of
`Stacks.FormalFunctions.fiberIsoInfinitesimalBaseIdealSubscheme` by
`Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso`, and the resulting module is identified
with the pullback to the subscheme of the pullback to `X'` by the composition law for module
pullbacks and
`Stacks.FormalFunctions.inv_fiberIsoInfinitesimalBaseIdealSubscheme_comp_fiberι`. -/
public theorem isAmple_pullbackModule_subschemeι_of_isAmple_fiber (f : X ⟶ Y) (y : Y)
    (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    IsAmple (infinitesimalBaseIdealSheaf f y).subscheme
      (pullbackModule (infinitesimalBaseIdealSheaf f y).subschemeι
        (pullbackModule (stalkBaseChangeι f y) L)) := by
  have h1 := Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso
    (fiberIsoInfinitesimalBaseIdealSubscheme f y).inv (pullbackModule (f.fiberι y) L) hL
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mp h1
  exact (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso
        (fiberIsoInfinitesimalBaseIdealSubscheme f y).inv (f.fiberι y) L).symm ≪≫
      Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
        (inv_fiberIsoInfinitesimalBaseIdealSubscheme_comp_fiberι f y) L ≪≫
    Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso
      (infinitesimalBaseIdealSheaf f y).subschemeι (stalkBaseChangeι f y) L

/-! ### Both clauses of Tag 0D2M on the base change -/

/-- **Both clauses of [Stacks, Tag 0D2M] on the base change `X' = X ×_Y Spec 𝒪_{Y,y}`, under the
source's own hypotheses.**

Let `f : X ⟶ Y` be proper with `Y` locally Noetherian, let `ℒ` be an invertible `𝒪_X`-module and
`ℱ` a coherent `𝒪_X`-module, and let `y ∈ Y` be a point at which `ℒ_y` is ample on the fibre
`X_y`. Write `X' = X ×_Y Spec 𝒪_{Y,y}` with structure morphism `g : X' ⟶ Spec 𝒪_{Y,y}` and
projection `q : X' ⟶ X`, and `ℱ' = q ^* ℱ`, `ℒ' = q ^* ℒ`. Then there is a `d₀` such that for
every `d ≥ d₀`

1. `H ᵖ(X', ℱ' ⊗ ℒ' ^⊗ d) = 0` for every `p > 0`, and
2. `H ⁰(X', ℱ' ⊗ ℒ' ^⊗ d) ⟶ H ⁰(X', (ℱ' ⊗ ℒ' ^⊗ d) / 𝔪_y (ℱ' ⊗ ℒ' ^⊗ d))` is surjective.

This is `Stacks.Cohomology.FormalFunctions.exists_subsingleton_and_surjective_twistModule` — the
local-base form of the tag — applied at the Noetherian local ring `𝒪_{Y,y}`, with its ampleness
hypothesis discharged from the tag's own by
`Stacks.FormalFunctions.isAmple_pullbackModule_subschemeι_of_isAmple_fiber`. The base change is
proper because properness is stable under base change, `X'` is locally Noetherian because `g` is
locally of finite type over a Noetherian affine, and `ℱ'` is coherent by [Stacks, Tag 0EBF].

**This is not [Stacks, Tag 0D2M].** The tag's conclusions are about the stalks of
`R ᵖ f_*(ℱ ⊗ ℒ ^⊗ d)` and `f_*(ℱ ⊗ ℒ ^⊗ d)` at `y`; passing from the two displays above to them
is [Stacks, Tag 02KH] part (1) along `Spec 𝒪_{Y,y} ⟶ Y`, which in positive degrees is open in
this library. -/
public theorem exists_subsingleton_and_surjective_twistModule_stalkBaseChange (f : X ⟶ Y)
    [IsProper f] [AlgebraicGeometry.IsLocallyNoetherian Y] (y : Y) (F L : X.Modules)
    [IsInvertibleModule X L] [F.IsCoherent]
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      (∀ p : ℕ, 0 < p → Subsingleton (cohomologyOverBase (Y.presheaf.stalk y)
          (stalkBaseChangeStructure f y) p
          (twistModule (stalkBaseChange f y) (pullbackModule (stalkBaseChangeι f y) L)
            (pullbackModule (stalkBaseChangeι f y) F) d))) ∧
        Function.Surjective (adicCohomologyProj (Y.presheaf.stalk y)
          (stalkBaseChangeStructure f y) (stalkMaximalIdeal y)
          (twistModule (stalkBaseChange f y) (pullbackModule (stalkBaseChangeι f y) L)
            (pullbackModule (stalkBaseChangeι f y) F) d) 0 1) := by
  have hloc : IsLocalRing ↥(Y.presheaf.stalk y) := inferInstance
  have hnoe : IsNoetherianRing ↥(Y.presheaf.stalk y) := inferInstance
  let _ : AlgebraicGeometry.IsLocallyNoetherian (stalkBaseChange f y) :=
    LocallyOfFiniteType.isLocallyNoetherian (stalkBaseChangeStructure f y)
  let _ : (pullbackModule (stalkBaseChangeι f y) F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback (stalkBaseChangeι f y) F
  exact @exists_subsingleton_and_surjective_twistModule ↥(Y.presheaf.stalk y) _ hloc hnoe _
    (stalkBaseChangeStructure f y) _ (pullbackModule (stalkBaseChangeι f y) F)
    (pullbackModule (stalkBaseChangeι f y) L) _ _
    (isAmple_pullbackModule_subschemeι_of_isAmple_fiber f y L hL)

end Stacks.FormalFunctions

end
