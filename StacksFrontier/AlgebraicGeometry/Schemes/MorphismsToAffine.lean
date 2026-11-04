module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms into an affine scheme are ring maps on global sections

Let `X` be a locally ringed space and let `Y` be an affine scheme. **Stacks 01I1** says that the
map

    Mor(X, Y) ⟶ Hom(Γ(Y, 𝒪_Y), Γ(X, 𝒪_X)),    f ↦ f^♯ on global sections

is bijective. The source attributes the fact to J. Tate, after [EGA, II, Err 1, Prop. 1.8.1].

**Stacks 01HY** reads off the same ring map one point at a time: for `x : X`, the inverse image
`p` of the maximal ideal `m_x` of `𝒪_{X,x}` under `Γ(Y, 𝒪_Y) --f^♯--> Γ(X, 𝒪_X) ⟶ 𝒪_{X,x}` is a
prime of `Γ(Y, 𝒪_Y)`, hence a point `y` of the affine scheme `Y`, and `f x = y`. Neither tag
implies the other: 01I1 says which ring maps arise, 01HY says where a point goes.

## Main definitions

* `AlgebraicGeometry.specGlobalSections`: the counit of the `Γ`-`Spec` adjunction at a ring, read
  as the canonical ring map from `R` to the global sections of `Spec R`.
* `AlgebraicGeometry.homEquivΓSpec`: the hom-equivalence of the `Γ`-`Spec` adjunction for locally
  ringed spaces, with the opposite-category bookkeeping discharged.

## Main results

* `AlgebraicGeometry.bijective_Γ_map_op_of_isAffine`: **Stacks 01I1**.
* `AlgebraicGeometry.bijective_Γ_map_op_spec`: the same for the target `Spec R`, which is the case
  the source reduces to in its first line.
* `AlgebraicGeometry.isoSpec_hom_base_apply_of_isAffine`: **Stacks 01HY**.
* `AlgebraicGeometry.base_eq_isoSpec_inv_base_of_isAffine`: Stacks 01HY written as `f x = y`.
* `AlgebraicGeometry.toΓSpecFun_base_apply`: Stacks 01HY with the target an arbitrary locally
  ringed space, which is the generality in which it is true and in which it is proved.

## Implementation notes

Mathlib proves this, as `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction`, the adjunction
`Γ ⊣ Spec` between `CommRingCatᵒᵖ` and `AlgebraicGeometry.LocallyRingedSpace`. What is stated here
is the source's own phrasing — that one particular map, taking global sections, is bijective —
routed to that adjunction rather than reproved. The two steps the routing needs are that the
adjunction's hom-equivalence is composition with the counit
(`CategoryTheory.Adjunction.homEquiv_counit`), and that the counit is an isomorphism, which holds
because it is `AlgebraicGeometry.Scheme.ΓSpecIso` — `AlgebraicGeometry.specGlobalSections` is
definitionally its inverse, which is what `AlgebraicGeometry.isIso_specGlobalSections` records.

The source's generality is kept on both sides. `X` is a locally ringed space, not a scheme: the
source states it that way, and the adjunction holds there. `Y` is an arbitrary affine scheme, not
`Spec R` on the nose; the passage from the one to the other is transport along
`AlgebraicGeometry.Scheme.isoSpec`, which is what separates
`AlgebraicGeometry.bijective_Γ_map_op_of_isAffine` from
`AlgebraicGeometry.bijective_Γ_map_op_spec`.

The scheme-source restriction of this statement is already proved, untagged, several times over
in this development — `Stacks.Smooth.homEquivOfIsAffine`,
`Stacks.RelativeSpec.affineHomEquiv`, `Stacks.EtaleCohomology.schemeHomEquivAppTop` and
`Stacks.EtaleCohomology.existsUnique_schemeHom_appTop_eq` are the same equivalence written out
independently, with two further `Spec R`-target spellings and two `private` copies. Each is the
restriction of the statement here to a scheme source, so none of them states Stacks 01I1 as the
source has it, and the tag sits here rather than being moved onto one of them.

Stacks 01HY is already proved in Mathlib, but only as a step inside the proof that
`AlgebraicGeometry.identityToΓSpec` is natural; there is no declaration to cite. What that step
proves is `AlgebraicGeometry.toΓSpecFun_base_apply`, so that is stated here and the affine case
is transported onto it. Mathlib's proof runs under `backward.isDefEq.respectTransparency false`,
which is not available in this library: the four ring maps of the commuting square are composable
only up to unfolding, so rewriting in the geometric statement fails its motive check. The fix is
`AlgebraicGeometry.comap_closedPoint_eq_comap_comap`, which takes the four maps as explicit
arguments; in that context every composite is syntactically well typed and the rewrites go
through unchanged. The geometric statement then needs no rewriting at all, only the commuting
square `AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ` and the locality of the stalk map.

## References

* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks Project, Tag 01HY](https://stacks.math.columbia.edu/tag/01HY)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe u

noncomputable section

/-! ### The counit of the `Γ`-`Spec` adjunction -/

/-- **The canonical ring map from `R` to the global sections of `Spec R`.** This is the counit of
the `Γ`-`Spec` adjunction for locally ringed spaces at `R`, read in `CommRingCat` rather than in
its opposite. It is definitionally the inverse of `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
def specGlobalSections (R : CommRingCat.{u}) :
    R ⟶ LocallyRingedSpace.Γ.obj (op (Spec.toLocallyRingedSpace.obj (op R))) :=
  (ΓSpec.locallyRingedSpaceAdjunction.counit.app (op R)).unop

/-- `AlgebraicGeometry.specGlobalSections` is an isomorphism: it is the inverse of
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
instance isIso_specGlobalSections (R : CommRingCat.{u}) : IsIso (specGlobalSections R) := by
  change IsIso (Scheme.ΓSpecIso R).inv
  infer_instance

/-- **Morphisms from a locally ringed space to `Spec R` are the ring maps out of `R`.** This is
the hom-equivalence of `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` with the
opposite-category bookkeeping discharged. -/
@[ega "I 1.7.3" "more general"]
def homEquivΓSpec (X : LocallyRingedSpace.{u}) (R : CommRingCat.{u}) :
    (X ⟶ Spec.toLocallyRingedSpace.obj (op R)) ≃ (R ⟶ LocallyRingedSpace.Γ.obj (op X)) :=
  (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op R)).symm.trans (opEquiv _ _)

/-- `AlgebraicGeometry.homEquivΓSpec` is taking global sections, after the canonical map from `R`
to the global sections of `Spec R`. -/
theorem homEquivΓSpec_apply (X : LocallyRingedSpace.{u}) (R : CommRingCat.{u})
    (f : X ⟶ Spec.toLocallyRingedSpace.obj (op R)) :
    homEquivΓSpec X R f = specGlobalSections R ≫ LocallyRingedSpace.Γ.map f.op := by
  change ((ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op R)).symm f).unop = _
  rw [Adjunction.homEquiv_counit]
  rfl

/-! ### Stacks 01I1 -/

/-- **Stacks 01I1 for the target `Spec R`.** For a locally ringed space `X` and a ring `R`, taking
global sections is a bijection from the morphisms `X ⟶ Spec R` of locally ringed spaces onto the
ring maps `Γ(Spec R, 𝒪) ⟶ Γ(X, 𝒪_X)`. -/
@[ega "I 1.8.1", sga "3 I 4.3.3" "more general"]
theorem bijective_Γ_map_op_spec (X : LocallyRingedSpace.{u}) (R : CommRingCat.{u}) :
    Function.Bijective (fun f : X ⟶ Spec.toLocallyRingedSpace.obj (op R) =>
      LocallyRingedSpace.Γ.map f.op) := by
  refine (((isIso_iff_coyoneda_map_bijective _).1 (isIso_specGlobalSections R) _).of_comp_iff'
    _).1 ?_
  rw [show _ ∘ _ = ⇑(homEquivΓSpec X R) from funext fun f => (homEquivΓSpec_apply X R f).symm]
  exact (homEquivΓSpec X R).bijective

/-- Let `X` be a locally ringed space and let `Y` be an affine scheme. The map

    Mor(X, Y) ⟶ Hom(Γ(Y, 𝒪_Y), Γ(X, 𝒪_X))

sending a morphism to the ring map it induces on global sections is bijective.

The target is read as a locally ringed space, which is where the morphisms of the source live. -/
@[stacks 01I1, ega "I 1.7.3" "more general"]
theorem bijective_Γ_map_op_of_isAffine (X : LocallyRingedSpace.{u}) (Y : Scheme.{u}) [IsAffine Y] :
    Function.Bijective (fun f : X ⟶ Y.toLocallyRingedSpace =>
      LocallyRingedSpace.Γ.map f.op) := by
  let u : Y.toLocallyRingedSpace ≅ Spec.toLocallyRingedSpace.obj (op Γ(Y, ⊤)) :=
    Scheme.forgetToLocallyRingedSpace.mapIso Y.isoSpec
  have h1 := bijective_Γ_map_op_spec X Γ(Y, ⊤)
  have he : Function.Bijective (fun f : X ⟶ Y.toLocallyRingedSpace => f ≫ u.hom) := by
    refine ⟨fun a b hab => ?_, fun g => ⟨g ≫ u.inv, ?_⟩⟩
    · simpa using congrArg (fun k => k ≫ u.inv) hab
    · simp
  have hpre := (isIso_iff_coyoneda_map_bijective (LocallyRingedSpace.Γ.map u.hom.op)).1
    inferInstance (LocallyRingedSpace.Γ.obj (op X))
  refine (hpre.of_comp_iff' _).1 ?_
  have hEq : ((fun h : LocallyRingedSpace.Γ.obj (op Y.toLocallyRingedSpace) ⟶
        LocallyRingedSpace.Γ.obj (op X) => LocallyRingedSpace.Γ.map u.hom.op ≫ h) ∘
      (fun f : X ⟶ Y.toLocallyRingedSpace => LocallyRingedSpace.Γ.map f.op)) =
      ((fun g : X ⟶ Spec.toLocallyRingedSpace.obj (op Γ(Y, ⊤)) =>
        LocallyRingedSpace.Γ.map g.op) ∘ (fun f => f ≫ u.hom)) := by
    funext f
    exact (LocallyRingedSpace.Γ.map_comp u.hom.op f.op).symm
  rw [hEq]
  exact h1.comp he

/-! ### Stacks 01HY -/

/-- **A commuting square of ring maps whose right-hand vertical arrow is local transports the
closed point.** If `a ≫ b = g ≫ c` and `b` is a local ring map between local rings, then the
inverse image of the maximal ideal of `A` along `a` — which is the inverse image along `b ∘ a` of
the maximal ideal, `b` being local — is its inverse image along `g` then `c`. -/
theorem comap_closedPoint_eq_comap_comap {R S A B : CommRingCat.{u}}
    (a : R ⟶ B) (b : B ⟶ A) (g : R ⟶ S) (c : S ⟶ A)
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom b.hom] (h : a ≫ b = g ≫ c) :
    PrimeSpectrum.comap a.hom (IsLocalRing.closedPoint B) =
      PrimeSpectrum.comap g.hom (PrimeSpectrum.comap c.hom (IsLocalRing.closedPoint A)) := by
  rw [← IsLocalRing.comap_closedPoint b.hom, ← PrimeSpectrum.comap_comp_apply,
    ← PrimeSpectrum.comap_comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, h]

/-- **Stacks 01HY in locally ringed spaces.** For a morphism `f : X ⟶ Y` of locally ringed
spaces, the canonical map `Y → Spec Γ(Y, 𝒪_Y)` sends `f x` to the inverse image of the maximal
ideal `m_x` of `𝒪_{X,x}` along `Γ(Y, 𝒪_Y) --f^♯--> Γ(X, 𝒪_X) → 𝒪_{X,x}`.

Both sides are read through `AlgebraicGeometry.LocallyRingedSpace.toΓSpecFun`, which is by
definition that inverse image: the prime of `Γ(X, 𝒪_X)` associated to `x` is the preimage of the
maximal ideal of the stalk. So the statement says that the prime of `Γ(Y, 𝒪_Y)` attached to the
point `f x` is the preimage along `f^♯` of the prime attached to `x`, which is Stacks 01HY with
the target left as an arbitrary locally ringed space rather than specialized to an affine
scheme. -/
theorem toΓSpecFun_base_apply {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    Y.toΓSpecFun (f.base x) =
      PrimeSpectrum.comap (LocallyRingedSpace.Γ.map f.op).hom (X.toΓSpecFun x) :=
  comap_closedPoint_eq_comap_comap (Y.presheaf.Γgerm (f.base x)) (f.stalkMap x)
    (LocallyRingedSpace.Γ.map f.op) (X.presheaf.Γgerm x)
    (LocallyRingedSpace.stalkMap_germ f ⊤ x trivial)

/-- Let `X` be a locally ringed space, let `Y` be an affine scheme and let
`f : X ⟶ Y` be a morphism of locally ringed spaces. Given `x : X`, consider the ring maps

    Γ(Y, 𝒪_Y) --f^♯--> Γ(X, 𝒪_X) ⟶ 𝒪_{X,x}

and let `p ⊆ Γ(Y, 𝒪_Y)` be the inverse image of the maximal ideal `m_x`. Let `y ∈ Y` be the
corresponding point. Then `f x = y`.

The point `y` of the affine scheme `Y` corresponding to a prime of `Γ(Y, 𝒪_Y)` is named by
transporting along `AlgebraicGeometry.Scheme.isoSpec`, the identification of `Y` with
`Spec Γ(Y, 𝒪_Y)`: the statement here is that `Y.isoSpec.hom` sends `f x` to `p`, and
`AlgebraicGeometry.base_eq_isoSpec_inv_base_of_isAffine` is the same thing written as `f x = y`.
The prime `p` is spelled as the inverse image along `f^♯` of the inverse image along
`Γ(X, 𝒪_X) ⟶ 𝒪_{X,x}` of the maximal ideal, which is the inverse image along the composite. -/
@[stacks 01HY]
theorem isoSpec_hom_base_apply_of_isAffine (X : LocallyRingedSpace.{u}) (Y : Scheme.{u})
    [IsAffine Y] (f : X ⟶ Y.toLocallyRingedSpace) (x : X) :
    Y.isoSpec.hom.base (f.base x) =
      PrimeSpectrum.comap (LocallyRingedSpace.Γ.map f.op).hom
        (PrimeSpectrum.comap (X.presheaf.Γgerm x).hom
          (IsLocalRing.closedPoint (X.presheaf.stalk x))) :=
  toΓSpecFun_base_apply f x

/-- **Stacks 01HY as the source states it:** `f x = y`, where `y` is the point of the affine
scheme `Y` corresponding to the inverse image in `Γ(Y, 𝒪_Y)` of the maximal ideal `m_x`.

This is `AlgebraicGeometry.isoSpec_hom_base_apply_of_isAffine` with the identification
`Y ≅ Spec Γ(Y, 𝒪_Y)` applied in the other direction, so that the conclusion is an equality of
points of `Y` rather than of `Spec Γ(Y, 𝒪_Y)`. -/
theorem base_eq_isoSpec_inv_base_of_isAffine (X : LocallyRingedSpace.{u}) (Y : Scheme.{u})
    [IsAffine Y] (f : X ⟶ Y.toLocallyRingedSpace) (x : X) :
    f.base x = Y.isoSpec.inv.base
      (PrimeSpectrum.comap (LocallyRingedSpace.Γ.map f.op).hom
        (PrimeSpectrum.comap (X.presheaf.Γgerm x).hom
          (IsLocalRing.closedPoint (X.presheaf.stalk x)))) := by
  refine Eq.trans ?_
    (congrArg (fun y => Y.isoSpec.inv.base y) (isoSpec_hom_base_apply_of_isAffine X Y f x))
  simp

end

end AlgebraicGeometry

end
