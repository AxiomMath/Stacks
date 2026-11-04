module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PushforwardUnitBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical comparison `f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}`, and its invertibility for affine `g`

Let

```
      g'
  X' ---→ X
  |       |
f'|       |f
  v   g   v
  S' ---→ S
```

be a commutative square of schemes.  There is a canonical morphism of `𝒪_X`-modules

`f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}`,

namely the left-adjoint transpose, under `f^* ⊣ f_*`, of the direct image along `g` of the
structure morphism `(f')^♯ : 𝒪_{S'} ⟶ f'_*𝒪_{X'}`, read through the identification
`g_*f'_* ≅ f_*g'_*` of the two composite direct images around the square.  **This module proves
that the comparison is invertible as soon as the square is Cartesian and `g` is affine** — no
Noetherian, quasi-compactness or flatness hypothesis anywhere — and packages it as an
isomorphism.

## Main definitions

* `AlgebraicGeometry.pushforwardUnitSquareHom` — the morphism
  `g_*𝒪_{S'} ⟶ f_*g'_*𝒪_{X'}` of `𝒪_S`-modules whose transpose the comparison is.
* `AlgebraicGeometry.pullbackPushforwardUnitHom` — **the canonical comparison**
  `f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}`, attached to a commutative square.
* `AlgebraicGeometry.pullbackPushforwardUnitHomRingedSpace` and
  `AlgebraicGeometry.pullbackPushforwardUnitHomRingedSpaceIso` — the same comparison, ascribed
  at the `SheafOfModules (structureSheafRing _)` spelling of the categories.

## Main results

* `AlgebraicGeometry.homEquiv_baseChangeNatTrans_unitObj` — **the base-change morphism of
  [Stacks, Tag 02KG] at the structure sheaf of `S'`, followed by `g'_*(f'^*𝒪_{S'} ≅ 𝒪_{X'})`, is
  the canonical comparison.**  Stated as the equality of its transpose with
  `pushforwardUnitSquareHom`; no hypothesis on the square.
* `AlgebraicGeometry.pullbackPushforwardUnitHom_eq_baseChangeNatTrans` — the same, read as a
  description of the comparison itself.
* `AlgebraicGeometry.pullbackPushforwardUnitHom_eq_iso_hom` — for a Cartesian square with `g`
  affine, the canonical comparison is the forward map of the isomorphism
  `AlgebraicGeometry.pullbackPushforwardUnitIso`.
* `AlgebraicGeometry.isIso_pullbackPushforwardUnitHom` and
  `AlgebraicGeometry.isIso_pullbackPushforwardUnitHomRingedSpace` — **the theorem**: for a
  Cartesian square whose lower horizontal arrow `g` is affine, the canonical comparison is
  invertible.

## Implementation notes

The canonical comparison is the base-change morphism
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` of [Stacks, Tag 02KG] at
`𝒪_{S'}`, followed by `g'_*(f'^*𝒪_{S'} ≅ 𝒪_{X'})`; the invertibility of the base-change morphism
for an affine horizontal arrow is
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`.

The square is written in the orientation of [Stacks, Tag 08IB] (`w : g' ≫ f = f' ≫ g`), while
`baseChangeNatTrans` is applied to the transposed square `f' ≫ g = g' ≫ f`; by proof
irrelevance `hsq.flip.w` and `hsq.w.symm` are interchangeable.

The ringed-space versions are type ascriptions: `AlgebraicGeometry.Scheme.Modules.pullback h`
and `RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom` are the same functor by
`rfl`, as are the two spellings of the structure sheaf as a module over itself, but this
equality is not visible at the transparency of instance search, so `IsIso` is stated at both
spellings.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffineBaseChange
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-! ### The canonical comparison -/

/-- For a commutative square `g' ≫ f = f' ≫ g` of schemes, the morphism of `𝒪_S`-modules
`g_*𝒪_{S'} ⟶ f_*g'_*𝒪_{X'}`: the direct image along `g` of the structure morphism
`(f')^♯ : 𝒪_{S'} ⟶ f'_*𝒪_{X'}`, followed by the identification `g_*f'_* ≅ f_*g'_*` of the two
composite direct images around the square. -/
def pushforwardUnitSquareHom (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pushforward g).obj (unitObj S') ⟶
      (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward g').obj (unitObj X')) :=
  (Scheme.Modules.pushforward g).map (structureUnitHom f') ≫
    (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w.symm).hom.app (unitObj X')

/-- **The canonical comparison `f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}`** attached to a commutative square
`g' ≫ f = f' ≫ g` of schemes: the left-adjoint transpose, under `f^* ⊣ f_*`, of
`AlgebraicGeometry.pushforwardUnitSquareHom`. -/
def pullbackPushforwardUnitHom (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward g).obj (unitObj S')) ⟶
      (Scheme.Modules.pushforward g').obj (unitObj X') :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (pushforwardUnitSquareHom w)

/-- The canonical comparison read through the hom-set bijection of `f^* ⊣ f_*`: its transpose is
`AlgebraicGeometry.pushforwardUnitSquareHom`. -/
theorem homEquiv_pullbackPushforwardUnitHom (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (pullbackPushforwardUnitHom w) =
      pushforwardUnitSquareHom w :=
  Equiv.apply_symm_apply _ _

/-! ### The comparison is the base-change morphism of [Stacks, Tag 02KG] -/

/-- **The base-change morphism of [Stacks, Tag 02KG] at the structure sheaf of `S'`, followed by
the direct image along `g'` of `f'^*𝒪_{S'} ≅ 𝒪_{X'}`, is the canonical comparison.**  Stated
through the hom-set bijection of `f^* ⊣ f_*`: the transpose of that composite is
`AlgebraicGeometry.pushforwardUnitSquareHom`.  No hypothesis on the square. -/
theorem homEquiv_baseChangeNatTrans_unitObj (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w.symm).app
            (unitObj S') ≫
          (Scheme.Modules.pushforward g').map (pullbackUnitIso f').hom) =
      pushforwardUnitSquareHom w := by
  have hnat : (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w.symm).hom.app
          ((Scheme.Modules.pullback f').obj (unitObj S')) ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pushforward g').map (pullbackUnitIso f').hom) =
      (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pushforward f').map (pullbackUnitIso f').hom) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w.symm).hom.app
          (unitObj X') :=
    ((Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w.symm).hom.naturality
      (pullbackUnitIso f').hom).symm
  rw [Adjunction.homEquiv_naturality_right, homEquiv_baseChangeNatTrans, Category.assoc, hnat]
  exact map_unit_comp_map_map_pullbackUnitIso w.symm

/-- The canonical comparison is the base-change morphism of [Stacks, Tag 02KG] at the structure
sheaf of `S'`, followed by the direct image along `g'` of `f'^*𝒪_{S'} ≅ 𝒪_{X'}`. -/
theorem pullbackPushforwardUnitHom_eq_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) :
    pullbackPushforwardUnitHom w =
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w.symm).app (unitObj S') ≫
        (Scheme.Modules.pushforward g').map (pullbackUnitIso f').hom :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm_apply_eq.2
    (homEquiv_baseChangeNatTrans_unitObj w).symm

/-- The canonical comparison of a Cartesian square with `g` affine is the isomorphism
`AlgebraicGeometry.pullbackPushforwardUnitIso`. -/
theorem pullbackPushforwardUnitHom_eq_iso_hom (hsq : IsPullback g' f' f g) [IsAffineHom g] :
    pullbackPushforwardUnitHom hsq.w = (pullbackPushforwardUnitIso hsq).hom :=
  (pullbackPushforwardUnitHom_eq_baseChangeNatTrans hsq.w).trans
    (pullbackPushforwardUnitIso_hom hsq).symm

/-! ### Invertibility for an affine `g` -/

/-- **Ordinary affine base change of the structure sheaf.**  For a Cartesian square of schemes

```
      g'
  X' ---→ X
  |       |
f'|       |f
  v   g   v
  S' ---→ S
```

whose lower horizontal arrow `g` is affine, the canonical comparison
`f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}` is invertible. -/
theorem isIso_pullbackPushforwardUnitHom (hsq : IsPullback g' f' f g) [IsAffineHom g] :
    IsIso (pullbackPushforwardUnitHom hsq.w) := by
  rw [pullbackPushforwardUnitHom_eq_iso_hom hsq]
  infer_instance

/-! ### The same at the ringed-space spelling -/

/-- The canonical comparison `f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}` of
`AlgebraicGeometry.pullbackPushforwardUnitHom`, ascribed at the
`SheafOfModules (structureSheafRing _)` spelling of the categories of modules and the
`RingedSpaceModuleAdjunction` spelling of the two functors, which agree with the scheme-level
spellings by `rfl`. -/
def pullbackPushforwardUnitHomRingedSpace (w : g' ≫ f = f' ≫ g) :
    (modulePullback f.toLRSHom.toShHom).obj
        ((modulePushforward g.toLRSHom.toShHom).obj
          (SheafOfModules.unit (_root_.structureSheafRing S'.toRingedSpace))) ⟶
      (modulePushforward g'.toLRSHom.toShHom).obj
        (SheafOfModules.unit (_root_.structureSheafRing X'.toRingedSpace)) :=
  pullbackPushforwardUnitHom w

/-- **Ordinary affine base change of the structure sheaf, at the ringed-space spelling.**  For a
Cartesian square of schemes whose lower horizontal arrow `g` is affine, the canonical comparison
`f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}` is invertible. -/
theorem isIso_pullbackPushforwardUnitHomRingedSpace (hsq : IsPullback g' f' f g)
    [IsAffineHom g] : IsIso (pullbackPushforwardUnitHomRingedSpace hsq.w) :=
  isIso_pullbackPushforwardUnitHom hsq

/-- **Ordinary affine base change of the structure sheaf at the ringed-space spelling, packaged
as an isomorphism**: for a Cartesian square with `g` affine, `f^*(g_*𝒪_{S'}) ≅ g'_*𝒪_{X'}`. -/
def pullbackPushforwardUnitHomRingedSpaceIso (hsq : IsPullback g' f' f g) [IsAffineHom g] :
    (modulePullback f.toLRSHom.toShHom).obj
        ((modulePushforward g.toLRSHom.toShHom).obj
          (SheafOfModules.unit (_root_.structureSheafRing S'.toRingedSpace))) ≅
      (modulePushforward g'.toLRSHom.toShHom).obj
        (SheafOfModules.unit (_root_.structureSheafRing X'.toRingedSpace)) :=
  haveI := isIso_pullbackPushforwardUnitHomRingedSpace hsq
  asIso (pullbackPushforwardUnitHomRingedSpace hsq.w)

/-- The forward map of `AlgebraicGeometry.pullbackPushforwardUnitHomRingedSpaceIso` is the
canonical comparison `AlgebraicGeometry.pullbackPushforwardUnitHomRingedSpace`. -/
@[simp]
theorem pullbackPushforwardUnitHomRingedSpaceIso_hom (hsq : IsPullback g' f' f g)
    [IsAffineHom g] :
    (pullbackPushforwardUnitHomRingedSpaceIso hsq).hom =
      pullbackPushforwardUnitHomRingedSpace hsq.w :=
  rfl

end AlgebraicGeometry

end
