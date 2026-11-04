module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupModuleCohomology
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.Deformation.RingedSpaceThickening.FlatCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# `p^*((A/Iⁿ)~) ≅ 𝒪_{Yₙ}`, and the cohomology of a free thickened module on the blowup

Let `A` be a commutative ring, `I ⊆ A` an ideal and `p : X → Spec(A)` the blowup of `Spec(A)` in
`I`, with `Yₙ` the `n`-th thickening of its exceptional divisor. This file identifies the
pullback along `p` of the quasi-coherent module attached to `A ⧸ Iⁿ` with the structure sheaf of
`Yₙ`,

`p^*((A/Iⁿ)~) ≅ 𝒪_{Yₙ}`,

carries that identification through the twist and through cohomology, and concludes with

`Hⁱ(X, 𝒪_X(q) ⊗ p^*(((A/Iⁿ)^{⊕r})~)) ≃ₗ[A] (Fin r → Hⁱ(X, 𝒪_{Yₙ}(q)))`,

which is the field `freeIso` of `Stacks.LocalCohomology.UniformityIII.ModuleSituation` for a
`ModuleSituation` built on `Stacks.LocalCohomology.UniformityIII.blowupSituationOf`.

## What this completes

`BitUniformityIII/BlowupModuleCohomology.lean` reduced `freeIso` to two inputs and proved the
second, `blowupHmodTwistedPullbackPiEquiv`, that cohomology commutes with finite direct sums.
Of the first, the geometric identification `p^*(A/Iⁿ) ≅ 𝒪_{Yₙ}`, it read off the ideal-sheaf half
(`thickeningIdeal_eq_comap`: `Yₙ = p⁻¹(V(Iⁿ))` scheme-theoretically) and proved the
module-level half (`pullbackPowStructureSheafIso`: `p^*(𝒪_{V(Iⁿ)}) ≅ 𝒪_{Yₙ}`), leaving the
affine step of recognising `𝒪_{V(Iⁿ)}` — the structure sheaf of the subscheme of the ideal sheaf
`powIdealSheaf I n`, pushed forward to `Spec(A)` — as `(A/Iⁿ)~`. That step is taken here, and it
is the composition of two results proved separately:

* `Stacks.LocalCohomology.subschemeIsoSpecQuotient` with its compatibility
  `Stacks.LocalCohomology.subschemeIsoSpecQuotient_hom_comp_subschemeι`, which identify the
  closed subscheme cut out by an ideal sheaf on `Spec A` with `Spec (A ⧸ J)` *as a scheme over
  `Spec A`*; and
* `Stacks.LocalCohomology.tildeQuotientIsoPushforward`, which is `(A/J)~ ≅ π_* 𝒪` for
  `π : Spec (A ⧸ J) ⟶ Spec A`.

The glue between them is `pushforwardUnitIsoOfCompEq` below: the direct image of the structure
sheaf is unchanged by an isomorphism of the source over the base. Its one nonformal ingredient —
that pushforward along an isomorphism of schemes carries the structure sheaf to the structure
sheaf — is `AlgebraicGeometry.Scheme.Modules.pushforwardUnitIso` and is not reproved.

## Why the twist needs the symmetry of the tensor product

The two halves of the development write the twist on opposite sides. `𝒪_{Yₙ}(q)` is
`Stacks.LocalCohomology.UniformityIII.thickeningTwist`, which is `𝒪_{Yₙ} ⊗ 𝒪_X(q)`; the twisted
pullback `Stacks.Blowup.twistedGeometricFactor` is `𝒪_X(q) ⊗ p^*(-)~`, the twist on the left,
because it is an instance of the Eilenberg–Watts geometric factor `F ⊗ (f')^*(-)~`. Passing
between them is `AlgebraicGeometry.RingedSpaceThickening.tensorSheafCommIso`, the symmetry of
the sheafified tensor product of [Stacks, Tag 01CA] on a ringed space; the monoidal structure
`Stacks.SheafOfModules.OnSpace.monoidal` used throughout `BitUniformityIII` has that sheafified
tensor product as its tensor product by definition, so the symmetry applies to it with no
transport, and no `CategoryTheory.BraidedCategory` instance — of which there is none at this
spelling of the category — is needed.

## Main results

* `Stacks.LocalCohomology.pushforwardUnitIsoOfCompEq`: `f_* 𝒪_Y ≅ g_* 𝒪_Z` for an isomorphism
  `e : Y ≅ Z` with `e ≫ g = f`.
* `Stacks.LocalCohomology.tildeQuotientIsoSubschemePushforward`: **`(A/J)~ ≅ (Z(W))_* 𝒪`** for an
  ideal sheaf `W` on `Spec A` whose ideal of global sections is `J`.
* `Stacks.LocalCohomology.UniformityIII.pullbackTildeQuotientIsoThickeningSheaf`:
  **`p^*((A/Iⁿ)~) ≅ 𝒪_{Yₙ}`.**
* `Stacks.LocalCohomology.UniformityIII.twistedPullbackQuotientIsoThickeningTwist`:
  **`𝒪_X(q) ⊗ p^*((A/Iⁿ)~) ≅ 𝒪_{Yₙ}(q)`.**
* `Stacks.LocalCohomology.UniformityIII.blowupFreeIso` and
  `Stacks.LocalCohomology.UniformityIII.blowupFreeIsoSituationOf`: **the field `freeIso` of
  `Stacks.LocalCohomology.UniformityIII.ModuleSituation`, for the blowup.**

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology

/-- **The direct image of the structure sheaf is unchanged by an isomorphism of the source over
the base**: for `e : Y ≅ Z` and morphisms `g : Z ⟶ X`, `f : Y ⟶ X` with `e ≫ g = f`, the
`𝒪_X`-modules `f_* 𝒪_Y` and `g_* 𝒪_Z` agree.

Pushforward along `e` carries `𝒪_Y` to `𝒪_Z` by
`AlgebraicGeometry.Scheme.Modules.pushforwardUnitIso`, and the two pushforwards compose to the
pushforward along `e ≫ g` by `AlgebraicGeometry.Scheme.Modules.pushforwardComp`, which is `f` by
hypothesis. -/
def pushforwardUnitIsoOfCompEq {X Y Z : Scheme.{u}} (e : Y ≅ Z) {g : Z ⟶ X} {f : Y ⟶ X}
    (h : e.hom ≫ g = f) :
    (Scheme.Modules.pushforward f).obj (Scheme.unitModule Y) ≅
      (Scheme.Modules.pushforward g).obj (Scheme.unitModule Z) :=
  ((Scheme.Modules.pushforwardCongr h).app (Scheme.unitModule Y)).symm ≪≫
    ((Scheme.Modules.pushforwardComp e.hom g).app (Scheme.unitModule Y)).symm ≪≫
      (Scheme.Modules.pushforward g).mapIso (Scheme.Modules.pushforwardUnitIso e.hom)

/-- **`(A/J)~ ≅ (Z(W))_* 𝒪`.** For an ideal sheaf `W` on `Spec A` whose ideal of global sections
is the image of `J ⊆ A` under `A ≃ Γ(Spec A, ⊤)`, the quasi-coherent module attached to `A ⧸ J`
is the direct image of the structure sheaf of the closed subscheme cut out by `W`.

Both sides are the direct image of a structure sheaf along a closed immersion into `Spec A`, for
the two closed immersions `Spec (A ⧸ J) ⟶ Spec A` and `Z(W) ⟶ Spec A`; `subschemeIsoSpecQuotient`
identifies their sources and `subschemeIsoSpecQuotient_hom_comp_subschemeι` says the
identification is over `Spec A`, which is what `pushforwardUnitIsoOfCompEq` asks for. -/
def tildeQuotientIsoSubschemePushforward (A : Type u) [CommRing A]
    (W : (Spec (CommRingCat.of A)).IdealSheafData) (J : Ideal A)
    (hW : W.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ =
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm :
        A →+* Γ(Spec (CommRingCat.of A), ⊤)) J) :
    tilde (ModuleCat.of A (A ⧸ J)) ≅
      (Scheme.Modules.pushforward W.subschemeι).obj (Scheme.unitModule W.subscheme) :=
  tildeQuotientIsoPushforward (CommRingCat.of A) J ≪≫
    pushforwardUnitIsoOfCompEq (subschemeIsoSpecQuotient A W J hW)
      (subschemeIsoSpecQuotient_hom_comp_subschemeι A W J hW)

namespace UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The ideal of global sections of the ideal sheaf of `V(Iⁿ) ⊆ Spec A` is the image of `Iⁿ`
under `A ≃ Γ(Spec A, ⊤)`: the restriction map of `Scheme.IdealSheafData.ofIdealTop` to `⊤` is the
identity, so taking the image twice is taking it once. -/
theorem ideal_powIdealSheaf_top (n : ℕ) :
    (powIdealSheaf I n).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ =
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm :
        A →+* Γ(Spec (CommRingCat.of A), ⊤)) (I ^ n) := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  congr 1

/-- **`p^*((A/Iⁿ)~) ≅ 𝒪_{Yₙ}`**: the inverse image along the blowdown of the quasi-coherent
module attached to `A ⧸ Iⁿ` is the structure sheaf of the `n`-th thickening of the exceptional
divisor.

This is the first input to the field `freeIso` of
`Stacks.LocalCohomology.UniformityIII.ModuleSituation`, and the geometric half of it is
`pullbackPowStructureSheafIso`, `p^*(𝒪_{V(Iⁿ)}) ≅ 𝒪_{Yₙ}`. What is composed with that here is
the affine identification `(A/Iⁿ)~ ≅ 𝒪_{V(Iⁿ)}`, which carries no geometry and no blowup. -/
def pullbackTildeQuotientIsoThickeningSheaf (n : ℕ) :
    (Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).obj
        (tilde (ModuleCat.of A (A ⧸ I ^ n))) ≅ thickeningSheaf I n :=
  (Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).mapIso
      (tildeQuotientIsoSubschemePushforward A (powIdealSheaf I n) (I ^ n)
        (ideal_powIdealSheaf_top I n)) ≪≫
    pullbackPowStructureSheafIso I n

/-- `Stacks.Blowup.twistedGeometricFactor` read as what it is, the twist of the pullback:
`𝒪_X(q) ⊗ p^*Ñ`. The two sides are the same object — the functor is the composition of
sheafification, pullback and tensoring — but the composite is opaque to `rw`, and the factored
form is the one the isomorphisms below are built on. -/
def twistedPullbackObjIso (q : ℤ) (N : ModuleCat.{u} A) :
    (Stacks.Blowup.twistedGeometricFactor I q).obj N ≅
      Stacks.Blowup.blowUpTwist I q ⊗
        (Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).obj (tilde N) :=
  Iso.refl _

/-- **`𝒪_X(q) ⊗ p^*((A/Iⁿ)~) ≅ 𝒪_{Yₙ}(q)`**: the twisted pullback of `A ⧸ Iⁿ` is the `q`-th
twist of the structure sheaf of the `n`-th thickening.

The twist changes sides on the way: the twisted pullback has it on the left and
`Stacks.LocalCohomology.UniformityIII.thickeningTwist` on the right, so the symmetry of the
sheafified tensor product is applied once, and then
`pullbackTildeQuotientIsoThickeningSheaf` is whiskered against `𝒪_X(q)`. -/
def twistedPullbackQuotientIsoThickeningTwist (n q : ℕ) :
    (Stacks.Blowup.twistedGeometricFactor I (q : ℤ)).obj (ModuleCat.of A (A ⧸ I ^ n)) ≅
      thickeningTwist I n q :=
  twistedPullbackObjIso I (q : ℤ) (ModuleCat.of A (A ⧸ I ^ n)) ≪≫
    AlgebraicGeometry.RingedSpaceThickening.tensorSheafCommIso _ _ _ ≪≫
      whiskerRightIso (pullbackTildeQuotientIsoThickeningSheaf I n) (blowupTwist I q)

/-- **`Hⁱ(X, 𝒪_X(q) ⊗ p^*((A/Iⁿ)~)) ≃ₗ[A] Hⁱ(X, 𝒪_{Yₙ}(q))`**: the cohomology of the twisted
pullback of `A ⧸ Iⁿ` is the cohomology of the twist of `𝒪_{Yₙ}`, which is the field `Hdiv` of
the Situation of [Stacks, Tag 0GA6] for the blowup. -/
def blowupHmodTwistedPullbackQuotientEquiv (n i q : ℕ) :
    blowupHmodTwistedPullback I (ModuleCat.of A (A ⧸ I ^ n)) i (q : ℤ) ≃ₗ[A]
      blowupHmod I i (thickeningTwist I n q) :=
  (((blowupΓmod I).rightDerived i).mapIso
    (twistedPullbackQuotientIsoThickeningTwist I n q)).toLinearEquiv

/-- **`Hⁱ(X, 𝒪_X(q) ⊗ p^*(((A/Iⁿ)^{⊕r})~)) ≃ₗ[A] (Fin r → Hⁱ(X, 𝒪_{Yₙ}(q)))`**, the field
`freeIso` of `Stacks.LocalCohomology.UniformityIII.ModuleSituation` for the blowup.

Its two inputs are `blowupHmodTwistedPullbackPiEquiv`, that the cohomology of the twisted
pullback commutes with the finite direct sum, and `blowupHmodTwistedPullbackQuotientEquiv`,
applied in each of the `r` coordinates. -/
def blowupFreeIso (n r i q : ℕ) :
    blowupHmodTwistedPullback I (ModuleCat.of A (Fin r → (A ⧸ I ^ n))) i (q : ℤ) ≃ₗ[A]
      (Fin r → blowupHmod I i (thickeningTwist I n q)) :=
  (blowupHmodTwistedPullbackPiEquiv I (ModuleCat.of A (A ⧸ I ^ n)) r i (q : ℤ)).trans
    (LinearEquiv.piCongrRight fun _ => blowupHmodTwistedPullbackQuotientEquiv I n i q)

/-- `blowupFreeIso` stated against the field `Hdiv` of the witness `blowupSituationOf`, which is
the spelling the field `freeIso` of `Stacks.LocalCohomology.UniformityIII.ModuleSituation` asks
for: there the module is `A ⧸ Iⁿ`, `r` is the rank of the chosen presentation, and the target is
a function type `Fin r → Hdiv n i q`. -/
def blowupFreeIsoSituationOf [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀)
    (n r i q : ℕ) :
    blowupHmodTwistedPullback I (ModuleCat.of A (Fin r → (A ⧸ I ^ n))) i (q : ℤ) ≃ₗ[A]
      (Fin r → (blowupSituationOf I q₀ h).Hdiv n i q) :=
  blowupFreeIso I n r i q

end UniformityIII

end Stacks.LocalCohomology

end
