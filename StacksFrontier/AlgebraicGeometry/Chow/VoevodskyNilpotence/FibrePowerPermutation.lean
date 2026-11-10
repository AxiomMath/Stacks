module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPowerNormPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric group acting on the `n`-fold fibre power of a scheme

Stacks 0FH9 works on `Xⁿ = X ×_k ⋯ ×_k X` and on the symmetric power `Sⁿ(X)`, and pulls an
invertible module back along `π : Xⁿ ⟶ Sⁿ(X)`. This file constructs the action of `Sₙ` on `Xⁿ`
and uses it to discharge one of the two hypotheses of
`Stacks.SheafOfModules.pullbackPicardClass_eq_factorial_nsmul_sum`.

## What `Sⁿ(X)` is, and what it is not

**`Sⁿ(X)` is not `Xⁿ/Sₙ`.** Stacks 0FH9 does not define `Sⁿ(X)` as a quotient of `Xⁿ`; it defines it
as the Hilbert scheme `Hilb^n_{X/k}`, citing Stacks 0B94 and 0B9C, and that is also what the
repository has — `Stacks.Hilbert` builds `Hilb^d_{X/S}` and the point-addition morphism of Stacks
0B9G without ever presenting it as a quotient. The correct account is in the module documentation of
`StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormGroupProduct` and of
`StacksFrontier.AlgebraicGeometry.Picard.SymmetricPowerNormPullback`, which also record why a
quotient presentation is not merely unbuilt but unavailable: the hypotheses of the two quotient
theorems of Stacks 02Z2 and 07S7 fail for the permutation action as soon as `n ≥ 2` and `X` has a
rational point, which Stacks 0FH9 assumes.

Nothing below depends on the identity of `Sⁿ(X)`: the statements of this file are about `Xⁿ`, the
permutation action, and the pullback formula in the Picard group.

## What `Xⁿ` is here, and why nothing has to be built

`Xⁿ` is the `n`-fold product of `Y = (X ⟶ S)` in the category `Over S`, which is the `n`-fold
fibre product over `S`. It needs no construction: `Scheme` has finite limits, hence finite wide
pullbacks (`CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`), hence `Over S` has
finite limits (`CategoryTheory.Over.hasFiniteLimits`) and therefore finite products, so
`∏ᶜ (fun _ : Fin n => Y)` is found by instance search alone for every `Y : Over S` and every `n`.
Accordingly no object is named here; the statements below are about that product.

## What the action is for

Two things.

*The Picard computation.* `Stacks.SheafOfModules.pullbackPicardClass_eq_factorial_nsmul_sum`
computes `π^*(Norm_π ℒ₁)` in `Pic(Xⁿ)` from two hypotheses: `horbit`, that the group permutes
the family `ℒᵢ = prᵢ^*ℒ`, and `hnorm`, the hint Stacks 0FH9 supplies in place of the calculation
it omits. `horbit` was assumed there only because the fibre power and its action were not
available; `Stacks.SheafOfModules.pullbackPicardClass_fibrePowerPerm` below proves it, and
`Stacks.SheafOfModules.pullbackPicardClass_fibrePower_eq_factorial_nsmul_sum` is the resulting
formula on the actual fibre power, carrying only the source's hint.

*The quotient.* `AlgebraicGeometry.Space.actionQuotient` (Stacks 02Z2) takes an action in the
shape of a group homomorphism `G →* Aut U` for `U : Over S`, and
`Stacks.Groupoids.FiniteFlatQuotient` (Stacks 07S6) is the quotient *scheme* of a groupoid
scheme. `Stacks.Scheme.fibrePowerPermAut` is that homomorphism for `G = Sₙ` and `U = Yⁿ`, so it
is the datum from which *a quotient of `Xⁿ` by `Sₙ`* would be formed.

It is **not** the datum from which `Sⁿ(X)` is to be formed, for two reasons: `Sⁿ(X)` is not
that quotient (see above), and neither quotient theorem applies
to this action anyway — both of their hypotheses fail for `n ≥ 2` over a scheme with a rational
point. So this homomorphism has the shape those theorems consume and no route through them.

## Why the group is the opposite group

`CategoryTheory.Aut` multiplies by `f * g = g ≪≫ f`, while permuting the factors composes in the
other order: `fibrePowerPerm σ ≫ fibrePowerPerm τ = fibrePowerPerm (σ * τ)`. So the assignment
`σ ↦ fibrePowerPerm σ` is a homomorphism out of `(Equiv.Perm (Fin n))ᵐᵒᵖ`, not out of
`Equiv.Perm (Fin n)`. This is the same convention the repository's other scheme-level actions
use — `Stacks.Descent.specGaloisAction` and
`AlgebraicGeometry.galoisActionOnBaseChange` are both stated at `ᵐᵒᵖ` — and it costs nothing
here, since `(Equiv.Perm (Fin n))ᵐᵒᵖ` is again a finite group and every statement below either
quantifies over all of it or is indifferent to the order.

## Main definitions

* `Stacks.Scheme.fibrePowerPerm` — the morphism `Yⁿ ⟶ Yⁿ` permuting the factors by `σ`.
* `Stacks.Scheme.fibrePowerPermIso` — the same morphism as an isomorphism.
* `Stacks.Scheme.fibrePowerPermAut` — the action of `Sₙ` on `Yⁿ`, as a group homomorphism
  `(Equiv.Perm (Fin n))ᵐᵒᵖ →* Aut Yⁿ`.

## Main results

* `Stacks.Scheme.fibrePowerPerm_comp_π` — `σ ≫ prᵢ = pr_{σ(i)}`. This is the only property of
  the action that the Picard computation uses.
* `Stacks.SheafOfModules.pullbackPicardClass_fibrePowerPerm` — the orbit identity
  `σ^*ℒ_{i} = ℒ_{σ(i)}` in `Pic(Yⁿ)` for a family `ℒᵢ` whose class is `prᵢ^*[ℒ]`.
* `Stacks.SheafOfModules.pullbackPicardClass_fibrePower_eq_factorial_nsmul_sum` — the formula
  `π^*𝒩 = (ℒ₁ ⊗ ⋯ ⊗ ℒₙ)^{⊗(n-1)!}` of Stacks 0FH9, on the fibre power and its permutation
  action, with `horbit` discharged.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Nat RingedSpaceModuleAdjunction

universe u

namespace Stacks.Scheme

variable {S : Scheme.{u}} (Y : Over S) (n : ℕ)

/-! ### Permuting the factors -/

/-- **Permuting the factors of the `n`-fold fibre power.** The morphism `Yⁿ ⟶ Yⁿ` over `S` whose
`i`-th component is the `σ(i)`-th projection. -/
def fibrePowerPerm (σ : Equiv.Perm (Fin n)) :
    (∏ᶜ fun _ : Fin n => Y) ⟶ (∏ᶜ fun _ : Fin n => Y) :=
  Pi.lift fun i ↦ Pi.π (fun _ : Fin n => Y) (σ i)

/-- **The defining property of the permutation morphism**: it carries the `i`-th projection to
the `σ(i)`-th one. Every statement below about the action is a consequence of this one. -/
@[simp]
theorem fibrePowerPerm_comp_π (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    fibrePowerPerm Y n σ ≫ Pi.π (fun _ : Fin n => Y) i =
      Pi.π (fun _ : Fin n => Y) (σ i) :=
  Pi.lift_comp_π _ _

/-- The identity permutation acts as the identity. -/
@[simp]
theorem fibrePowerPerm_one : fibrePowerPerm Y n 1 = 𝟙 _ :=
  Pi.hom_ext _ _ fun i ↦ by simp

/-- **Composing permutation morphisms multiplies the permutations**, in that order: applying `σ`
and then `τ` is applying `σ ∘ τ`, because the morphism reads the factors backwards. -/
@[simp]
theorem fibrePowerPerm_comp (σ τ : Equiv.Perm (Fin n)) :
    fibrePowerPerm Y n σ ≫ fibrePowerPerm Y n τ = fibrePowerPerm Y n (σ * τ) :=
  Pi.hom_ext _ _ fun i ↦ by simp

/-- **Permuting the factors is an isomorphism of `S`-schemes**, with the inverse permutation as
its inverse. -/
@[simps]
def fibrePowerPermIso (σ : Equiv.Perm (Fin n)) :
    (∏ᶜ fun _ : Fin n => Y) ≅ (∏ᶜ fun _ : Fin n => Y) where
  hom := fibrePowerPerm Y n σ
  inv := fibrePowerPerm Y n σ⁻¹
  hom_inv_id := by rw [fibrePowerPerm_comp, mul_inv_cancel, fibrePowerPerm_one]
  inv_hom_id := by rw [fibrePowerPerm_comp, inv_mul_cancel, fibrePowerPerm_one]

/-- **The symmetric group acts on the `n`-fold fibre power by permuting the factors.** The action
is given in the shape `AlgebraicGeometry.Space.actionQuotient` (Stacks 02Z2) consumes, a group
homomorphism into the automorphisms of an object of `Over S`; it is stated at the opposite group
for the reason recorded in the module documentation. -/
@[sga "3 VIIA 6.3" "partial"]
def fibrePowerPermAut : (Equiv.Perm (Fin n))ᵐᵒᵖ →* Aut (∏ᶜ fun _ : Fin n => Y) where
  toFun σ := .of (fibrePowerPermIso Y n σ.unop)
  map_one' := Aut.ext (Iso.ext (fibrePowerPerm_one Y n))
  map_mul' σ τ := Aut.ext (Iso.ext (fibrePowerPerm_comp Y n τ.unop σ.unop).symm)

/-- **The permutation action on the fibre power is faithful** as soon as `Y` has two distinct
sections over `S`: if `σ i ≠ τ i`, the point whose `σ(i)`-th coordinate is `s` and whose other
coordinates are `t` is sent to different points by `pr_i ∘ σ` and `pr_i ∘ τ`. -/
theorem fibrePowerPerm_left_injective {s t : Over.mk (𝟙 S) ⟶ Y} (hst : s ≠ t) :
    Function.Injective fun σ : Equiv.Perm (Fin n) ↦ (fibrePowerPerm Y n σ).left := by
  intro σ τ h
  have h' : fibrePowerPerm Y n σ = fibrePowerPerm Y n τ := Over.OverMorphism.ext h
  refine Equiv.ext fun i ↦ Classical.byContradiction fun hi ↦ ?_
  let p : Over.mk (𝟙 S) ⟶ (∏ᶜ fun _ : Fin n => Y) :=
    Pi.lift fun j ↦ if j = σ i then s else t
  have hs : p ≫ fibrePowerPerm Y n σ ≫ Pi.π (fun _ : Fin n => Y) i = s := by
    rw [fibrePowerPerm_comp_π, Pi.lift_comp_π, ite_eq_left rfl]
  have ht : p ≫ fibrePowerPerm Y n τ ≫ Pi.π (fun _ : Fin n => Y) i = t := by
    rw [fibrePowerPerm_comp_π, Pi.lift_comp_π, ite_eq_right (Ne.symm hi)]
  exact hst (hs.symm.trans (h' ▸ ht))

end Stacks.Scheme

namespace Stacks.SheafOfModules

open Stacks.Scheme

/-! ### The orbit of a pulled-back invertible module -/

/-- **The permutation action permutes the family `ℒᵢ = prᵢ^*ℒ`**, in `Pic(Yⁿ)`:

  `(σ)^*ℒ_{i₀} = ℒ_{σ(i₀)}`.

The hypothesis `hpull` says that `ℒᵢ` is `prᵢ^*ℒ`, read in the Picard group — which is how the
family of Stacks 0FH9 is given — and the conclusion is the `horbit` hypothesis of
`Stacks.SheafOfModules.pullbackPicardClass_eq_factorial_nsmul_sum` for the fibre power and its
permutation morphisms.

The proof is the composition rule `Stacks.SheafOfModules.pullbackPicardClass_comp` applied to
`Stacks.Scheme.fibrePowerPerm_comp_π`: pulling back along `σ` and then along `prᵢ₀` is pulling
back along `pr_{σ(i₀)}`. -/
theorem pullbackPicardClass_fibrePowerPerm {S : Scheme.{u}} (Y : Over S) {n : ℕ}
    (M : SheafOfModules.{u} (structureSheafRing Y.left.toRingedSpace))
    (hM : IsInvertible Y.left.presheaf Y.left.ringCatIsSheaf M)
    (L : Fin n → SheafOfModules.{u}
      (structureSheafRing (∏ᶜ fun _ : Fin n => Y).left.toRingedSpace))
    (hL : ∀ i, IsInvertible (∏ᶜ fun _ : Fin n => Y).left.presheaf
      (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i))
    (hpull : ∀ i, pullbackPicardClass (Pi.π (fun _ : Fin n => Y) i).left M hM =
      picardClass (∏ᶜ fun _ : Fin n => Y).left.presheaf
        (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i) (hL i))
    (σ : Equiv.Perm (Fin n)) (i₀ : Fin n) :
    pullbackPicardClass (fibrePowerPerm Y n σ).left (L i₀) (hL i₀) =
      picardClass (∏ᶜ fun _ : Fin n => Y).left.presheaf
        (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L (σ i₀)) (hL (σ i₀)) := by
  -- The pullback of `M` along a projection is invertible, by Stacks 0B8L.
  have hpb : ∀ i : Fin n, IsInvertible (∏ᶜ fun _ : Fin n => Y).left.presheaf
      (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf
      ((modulePullback ((Pi.π (fun _ : Fin n => Y) i).left).toLRSHom.toShHom).obj M) :=
    fun i ↦ Stacks.RingedSpace.modulePullback_isInvertible _ M
  -- `L i` is isomorphic to that pullback, since the two have the same Picard class.
  have hiso : ∀ i : Fin n, Nonempty
      (L i ≅ (modulePullback ((Pi.π (fun _ : Fin n => Y) i).left).toLRSHom.toShHom).obj M) :=
    fun i ↦ (picardClass_eq_iff _ _ _ _ (hL i) (hpb i)).1 (hpull i).symm
  obtain ⟨e⟩ := hiso i₀
  rw [pullbackPicardClass_congr _ _ _ (hL i₀) (hpb i₀) e,
    ← pullbackPicardClass_comp (fibrePowerPerm Y n σ).left
      (Pi.π (fun _ : Fin n => Y) i₀).left M hM (hpb i₀),
    ← Over.comp_left, fibrePowerPerm_comp_π,
    pullbackPicardClass_eq_picardClass _ M hM (hpb (σ i₀))]
  exact (picardClass_eq_iff _ _ _ _ (hpb (σ i₀)) (hL (σ i₀))).2
    ⟨(hiso (σ i₀)).some.symm⟩

/-- **The pullback of the norm, on the fibre power itself.** This is
`Stacks.SheafOfModules.pullbackPicardClass_eq_factorial_nsmul_sum` with `P = Yⁿ`, the
permutation morphisms of `Stacks.Scheme.fibrePowerPerm` for the action, and `horbit` discharged
by `Stacks.SheafOfModules.pullbackPicardClass_fibrePowerPerm`. For `Y = (X ⟶ Spec k)`,
`Q = Sⁿ(X)` and `𝒩 = Norm_π(ℒ₁)` it is the formula

  `π^*𝒩 = (ℒ₁ ⊗ ⋯ ⊗ ℒₙ)^{⊗(n-1)!}`

of Stacks 0FH9, written additively.

One hypothesis remains, and it is the one Stacks 0FH9 omits the calculation for: `hnorm`, that
`π^*(Norm_π ℒ_{i₀})` is the sum over `Sₙ` of the pullbacks of `ℒ_{i₀}`. Discharging it needs
`𝒪_{Sⁿ(X)}` to be the `Sₙ`-invariants of `π_*𝒪_{Xⁿ}`, i.e. the presentation of `Sⁿ(X)` as the
quotient of `Xⁿ` by the action `Stacks.Scheme.fibrePowerPermAut` builds. -/
theorem pullbackPicardClass_fibrePower_eq_factorial_nsmul_sum {S : Scheme.{u}} (Y : Over S)
    {n : ℕ} {Q : Scheme.{u}} (π : (∏ᶜ fun _ : Fin n => Y).left ⟶ Q) (i₀ : Fin n)
    (M : SheafOfModules.{u} (structureSheafRing Y.left.toRingedSpace))
    (hM : IsInvertible Y.left.presheaf Y.left.ringCatIsSheaf M)
    (L : Fin n → SheafOfModules.{u}
      (structureSheafRing (∏ᶜ fun _ : Fin n => Y).left.toRingedSpace))
    (hL : ∀ i, IsInvertible (∏ᶜ fun _ : Fin n => Y).left.presheaf
      (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i))
    (hpull : ∀ i, pullbackPicardClass (Pi.π (fun _ : Fin n => Y) i).left M hM =
      picardClass (∏ᶜ fun _ : Fin n => Y).left.presheaf
        (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i) (hL i))
    (N : SheafOfModules.{u} (structureSheafRing Q.toRingedSpace))
    (hN : IsInvertible Q.presheaf Q.ringCatIsSheaf N)
    (hnorm : pullbackPicardClass π N hN =
      ∑ σ : Equiv.Perm (Fin n),
        pullbackPicardClass (fibrePowerPerm Y n σ).left (L i₀) (hL i₀)) :
    pullbackPicardClass π N hN =
      (n - 1)! • ∑ i, picardClass (∏ᶜ fun _ : Fin n => Y).left.presheaf
        (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i) (hL i) :=
  pullbackPicardClass_eq_factorial_nsmul_sum π i₀ L hL N hN
    (fun σ ↦ (fibrePowerPerm Y n σ).left)
    (fun σ ↦ pullbackPicardClass_fibrePowerPerm Y M hM L hL hpull σ i₀) hnorm

end Stacks.SheafOfModules

end
