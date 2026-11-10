module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalNeighbourhood
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme

/-!
# The infinitesimal neighbourhoods of a fibre as the ideal-power subschemes of a base change

Let `f : X ⟶ Y` be a morphism of schemes and let `y` be a point of `Y`. The `n`-th
infinitesimal neighbourhood of the fibre `X_y`,

  `X_n = X ×_Y Spec (𝒪_{Y,y}/𝔪_y ^ n)`,

is constructed in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/InfinitesimalNeighbourhood.lean` as a fibre
product over `Y`. Because the structure morphism `c_n : Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Y` is by
definition the composite of the closed immersion `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec 𝒪_{Y,y}` with
`Spec 𝒪_{Y,y} ⟶ Y`, that fibre product factors through the base change

  `X' = X ×_Y Spec 𝒪_{Y,y}`,

and `X_n` is then the closed subscheme of `X'` cut out by the `n`-th power of the ideal sheaf
`𝔪_y · 𝒪_{X'}`. This file proves exactly that, together with the two compatibilities that make
the identification usable: it carries the inclusion `X_n ⟶ X'` to the inclusion of the
subscheme, and it carries the transition morphisms `X_n ⟶ X_m` of the infinitesimal system to
the inclusions of subschemes coming from `𝔪_y ^ m 𝒪_{X'} ⊆ 𝔪_y ^ n 𝒪_{X'}`.

That is what connects the two halves of the theorem on formal functions as this library has
them. The tower `n ↦ Γ(X_n, 𝒪_{X_n})` is the right-hand side of [Stacks, Tag 02OD] at `p = 0`
for the structure sheaf (`Stacks.FormalFunctions.infinitesimalFunctions`), while the
[Stacks, Tag 02OB] and [Stacks, Tag 02OC] machinery of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/IdealPowerQuotientCohomologyBound.lean` and
`StacksFrontier/AlgebraicGeometry/FormalFunctions/AdicCompletionLimitComparison.lean`
is stated over an affine base `Spec A` for the tower
`n ↦ H⁰(X', 𝒪_{X'}/𝓘 ^ n)` with `𝓘 = I · 𝒪_{X'}`. Here `A = 𝒪_{Y,y}` and `I = 𝔪_y`, and the
identification below is what lets the second tower be read as the first.

## Main definitions

* `Stacks.FormalFunctions.stalkBaseChange` — the scheme `X' = X ×_Y Spec 𝒪_{Y,y}`, with its two
  projections `Stacks.FormalFunctions.stalkBaseChangeι` (to `X`) and
  `Stacks.FormalFunctions.stalkBaseChangeStructure` (to `Spec 𝒪_{Y,y}`).
* `Stacks.FormalFunctions.infinitesimalBaseIdealSheaf` — the quasi-coherent ideal sheaf
  `𝔪_y · 𝒪_{X'}` on `X'`.
* `Stacks.FormalFunctions.infinitesimalιBaseChange` — the canonical morphism `X_n ⟶ X'`.
* `Stacks.FormalFunctions.infinitesimalNeighbourhoodIsoSubscheme` — **the identification**
  `(𝔪_y 𝒪_{X'}) ^ n`-subscheme `≅ X_n`.

## Main results

* `Stacks.FormalFunctions.infinitesimalιBaseChange_comp_ι` — the projection `i_n : X_n ⟶ X`
  factors through `X'`.
* `Stacks.FormalFunctions.infinitesimalιBaseChange_comp_structure` — the defining square of
  `X_n` over `X'`: `X_n ⟶ X' ⟶ Spec 𝒪_{Y,y}` equals `X_n ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶
  Spec 𝒪_{Y,y}`.
* `Stacks.FormalFunctions.infinitesimalTransition_comp_ιBaseChange` — the transition morphisms
  of the infinitesimal system commute with the morphisms to `X'`.
* `Stacks.FormalFunctions.infinitesimalNeighbourhoodIsoSubscheme_hom_comp_ιBaseChange` — the
  identification carries the subscheme inclusion into `X'` to `X_n ⟶ X'`.
* `Stacks.FormalFunctions.infinitesimalNeighbourhoodIsoSubscheme_hom_comp_transition` — the
  identification is compatible with the transition morphisms of the two systems.
* `Stacks.FormalFunctions.isClosedImmersion_infinitesimalιBaseChange` — `X_n ⟶ X'` is a closed
  immersion, so it is a monomorphism; this is what pins the two compatibilities down.

## Implementation notes

`AlgebraicGeometry.Scheme.IdealSheafData.inclusion` goes the other way round from the order on
ideal sheaves: for `h : I ≤ J` it is a morphism `J.subscheme ⟶ I.subscheme`. Since
`𝓘 ^ m ≤ 𝓘 ^ n` for `n ≤ m` (`AlgebraicGeometry.Scheme.IdealSheafData.pow_le_pow_of_le`), the
inclusion of subschemes attached to `n ≤ m` runs `X_n ⟶ X_m`, in the same direction as
`Stacks.FormalFunctions.infinitesimalTransition`.

`Stacks.FormalFunctions.basePullbackIso` is
`Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback` with its target spelled with
`Stacks.FormalFunctions.toStalkQuotient` rather than with the quotient map it abbreviates. The
two spellings are definitionally equal, but the composite `≪≫` with the pasting isomorphism is
not type-correct at `implicit` transparency without the restatement, and then rewriting with
`Iso.trans_hom` fails.

Both compatibilities are proved by cancelling a monomorphism rather than by chasing the
construction of the pasting isomorphism: `X_n ⟶ X'` and `(𝓘 ^ n).subschemeι` are closed
immersions, hence monomorphisms, and a morphism into `X_n` is determined by its composite with
either.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FormalFunctions

open Stacks.Cohomology.FormalFunctions (baseIdealSheaf baseIdealSheaf_pow)

variable {X Y : Scheme.{u}}

/-! ### The base change to the spectrum of the local ring -/

/-- **The base change `X' = X ×_Y Spec 𝒪_{Y,y}`.** Every infinitesimal neighbourhood of the
fibre of `f` over `y` is a closed subscheme of this one scheme. -/
public abbrev stalkBaseChange (f : X ⟶ Y) (y : Y) : Scheme.{u} :=
  pullback f (Y.fromSpecStalk y)

/-- The projection `X' ⟶ X`. -/
public abbrev stalkBaseChangeι (f : X ⟶ Y) (y : Y) : stalkBaseChange f y ⟶ X :=
  pullback.fst f (Y.fromSpecStalk y)

/-- The structure morphism `X' ⟶ Spec 𝒪_{Y,y}`, a base change of `f`. -/
public abbrev stalkBaseChangeStructure (f : X ⟶ Y) (y : Y) :
    stalkBaseChange f y ⟶ Spec (Y.presheaf.stalk y) :=
  pullback.snd f (Y.fromSpecStalk y)

/-- **The ideal sheaf `𝔪_y · 𝒪_{X'}` on the base change.** Its `n`-th power cuts out the `n`-th
infinitesimal neighbourhood of the fibre. -/
public abbrev infinitesimalBaseIdealSheaf (f : X ⟶ Y) (y : Y) :
    (stalkBaseChange f y).IdealSheafData :=
  baseIdealSheaf (Y.presheaf.stalk y) (stalkMaximalIdeal y) (stalkBaseChangeStructure f y)

/-! ### The infinitesimal neighbourhoods over the base change -/

/-- **`X_n` is the base change of `X'` along `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec 𝒪_{Y,y}`**, by the
pasting of the two cartesian squares over `Spec 𝒪_{Y,y}` and over `Y`. -/
public def infinitesimalNeighbourhoodIsoPullback (f : X ⟶ Y) (y : Y) (n : ℕ) :
    pullback (stalkBaseChangeStructure f y) (Spec.map (toStalkQuotient y n)) ≅
      infinitesimalNeighbourhood f y n :=
  pullbackLeftPullbackSndIso f (Y.fromSpecStalk y) (Spec.map (toStalkQuotient y n))

/-- **The canonical morphism `X_n ⟶ X'`.** -/
public def infinitesimalιBaseChange (f : X ⟶ Y) (y : Y) (n : ℕ) :
    infinitesimalNeighbourhood f y n ⟶ stalkBaseChange f y :=
  (infinitesimalNeighbourhoodIsoPullback f y n).inv ≫
    pullback.fst (stalkBaseChangeStructure f y) (Spec.map (toStalkQuotient y n))

/-- The projection `i_n : X_n ⟶ X` factors through the base change `X'`. -/
@[reassoc (attr := simp)]
public theorem infinitesimalιBaseChange_comp_ι (f : X ⟶ Y) (y : Y) (n : ℕ) :
    infinitesimalιBaseChange f y n ≫ stalkBaseChangeι f y = infinitesimalι f y n := by
  have h : (infinitesimalNeighbourhoodIsoPullback f y n).hom ≫ infinitesimalι f y n =
      pullback.fst (stalkBaseChangeStructure f y) (Spec.map (toStalkQuotient y n)) ≫
        stalkBaseChangeι f y :=
    pullbackLeftPullbackSndIso_hom_fst f (Y.fromSpecStalk y) (Spec.map (toStalkQuotient y n))
  rw [infinitesimalιBaseChange, Category.assoc, ← h, Iso.inv_hom_id_assoc]

/-- The defining square of `X_n` over `X'`: the two routes `X_n ⟶ Spec 𝒪_{Y,y}` agree. -/
@[reassoc]
public theorem infinitesimalιBaseChange_comp_structure (f : X ⟶ Y) (y : Y) (n : ℕ) :
    infinitesimalιBaseChange f y n ≫ stalkBaseChangeStructure f y =
      infinitesimalStructure f y n ≫ Spec.map (toStalkQuotient y n) := by
  have h : (infinitesimalNeighbourhoodIsoPullback f y n).hom ≫ infinitesimalStructure f y n =
      pullback.snd (stalkBaseChangeStructure f y) (Spec.map (toStalkQuotient y n)) :=
    pullbackLeftPullbackSndIso_hom_snd f (Y.fromSpecStalk y) (Spec.map (toStalkQuotient y n))
  rw [infinitesimalιBaseChange, Category.assoc, pullback.condition, ← Category.assoc,
    ← h, Iso.inv_hom_id_assoc]

/-- `X_n ⟶ X'` is a closed immersion, being a base change of the closed immersion
`Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec 𝒪_{Y,y}`. -/
public instance isClosedImmersion_infinitesimalιBaseChange (f : X ⟶ Y) (y : Y) (n : ℕ) :
    IsClosedImmersion (infinitesimalιBaseChange f y n) := by
  rw [infinitesimalιBaseChange]
  infer_instance

/-- The transition morphisms of the infinitesimal system are morphisms over `X'`. -/
@[reassoc (attr := simp)]
public theorem infinitesimalTransition_comp_ιBaseChange (f : X ⟶ Y) (y : Y) {n m : ℕ}
    (h : n ≤ m) :
    infinitesimalTransition f y h ≫ infinitesimalιBaseChange f y m =
      infinitesimalιBaseChange f y n := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, infinitesimalιBaseChange_comp_ι, infinitesimalTransition_ι,
      infinitesimalιBaseChange_comp_ι]
  · rw [Category.assoc, infinitesimalιBaseChange_comp_structure,
      ← Category.assoc, infinitesimalTransition_structure, Category.assoc,
      infinitesimalιBaseChange_comp_structure, baseTransition, ← Spec.map_comp,
      toStalkQuotient_comp_stalkQuotientFactor]

/-! ### The identification with the ideal-power subschemes -/

/-- `Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback` with its target written in
the shape the infinitesimal system uses, so that the two isomorphisms compose without a
transport. -/
public def basePullbackIso (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (baseIdealSheaf (Y.presheaf.stalk y) (stalkMaximalIdeal y ^ n)
        (stalkBaseChangeStructure f y)).subscheme ≅
      pullback (stalkBaseChangeStructure f y) (Spec.map (toStalkQuotient y n)) :=
  Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback (Y.presheaf.stalk y)
    (stalkMaximalIdeal y ^ n) (stalkBaseChangeStructure f y)

/-- `Stacks.FormalFunctions.basePullbackIso` is compatible with the two closed immersions
into the base change. -/
public theorem basePullbackIso_hom_fst (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (basePullbackIso f y n).hom ≫
        pullback.fst (stalkBaseChangeStructure f y) (Spec.map (toStalkQuotient y n)) =
      (baseIdealSheaf (Y.presheaf.stalk y) (stalkMaximalIdeal y ^ n)
        (stalkBaseChangeStructure f y)).subschemeι :=
  Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback_hom_fst (Y.presheaf.stalk y)
    (stalkMaximalIdeal y ^ n) (stalkBaseChangeStructure f y)

/-- **The `n`-th infinitesimal neighbourhood of the fibre is the closed subscheme of
`X' = X ×_Y Spec 𝒪_{Y,y}` cut out by `(𝔪_y 𝒪_{X'}) ^ n`.** -/
public def infinitesimalNeighbourhoodIsoSubscheme (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (infinitesimalBaseIdealSheaf f y ^ n).subscheme ≅ infinitesimalNeighbourhood f y n :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (baseIdealSheaf_pow (Y.presheaf.stalk y) (stalkMaximalIdeal y)
        (stalkBaseChangeStructure f y) n).symm) ≪≫
    basePullbackIso f y n ≪≫ infinitesimalNeighbourhoodIsoPullback f y n

/-- **The identification carries the inclusion of the subscheme to `X_n ⟶ X'`.** -/
@[reassoc (attr := simp)]
public theorem infinitesimalNeighbourhoodIsoSubscheme_hom_comp_ιBaseChange (f : X ⟶ Y) (y : Y)
    (n : ℕ) :
    (infinitesimalNeighbourhoodIsoSubscheme f y n).hom ≫ infinitesimalιBaseChange f y n =
      (infinitesimalBaseIdealSheaf f y ^ n).subschemeι := by
  rw [infinitesimalNeighbourhoodIsoSubscheme, infinitesimalιBaseChange, Iso.trans_hom,
    Iso.trans_hom, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    basePullbackIso_hom_fst, eqToIso.hom,
    Stacks.PuncturedSpectrumPicard.subscheme_eqToHom_comp_subschemeι]
  exact (baseIdealSheaf_pow (Y.presheaf.stalk y) (stalkMaximalIdeal y)
    (stalkBaseChangeStructure f y) n).symm

/-- **The identification is compatible with the transitions**: the inclusion of the subscheme
of `(𝔪_y 𝒪_{X'}) ^ m` into that of `(𝔪_y 𝒪_{X'}) ^ n` corresponds to `X_n ⟶ X_m`. -/
public theorem infinitesimalNeighbourhoodIsoSubscheme_hom_comp_transition (f : X ⟶ Y) (y : Y)
    {n m : ℕ} (h : n ≤ m) :
    (infinitesimalNeighbourhoodIsoSubscheme f y n).hom ≫ infinitesimalTransition f y h =
      Scheme.IdealSheafData.inclusion
          (Scheme.IdealSheafData.pow_le_pow_of_le (infinitesimalBaseIdealSheaf f y) h) ≫
        (infinitesimalNeighbourhoodIsoSubscheme f y m).hom := by
  rw [← cancel_mono (infinitesimalιBaseChange f y m), Category.assoc, Category.assoc,
    infinitesimalTransition_comp_ιBaseChange,
    infinitesimalNeighbourhoodIsoSubscheme_hom_comp_ιBaseChange,
    infinitesimalNeighbourhoodIsoSubscheme_hom_comp_ιBaseChange,
    Scheme.IdealSheafData.inclusion_subschemeι]

end Stacks.FormalFunctions

end
