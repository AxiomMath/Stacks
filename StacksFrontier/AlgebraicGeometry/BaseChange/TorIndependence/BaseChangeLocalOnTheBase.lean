module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityOnAnOpenCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting

/-!
# Invertibility of the derived base-change map is local on the base

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of ringed spaces or of schemes and let

`Lg^*(Rf_*K) ⟶ Rf'_*(L(g')^*K)`

be the derived base-change map of Stacks 08HY.  The proof of Stacks 08IB opens with *"to check
this is an isomorphism we may work locally on `S'`; hence we may assume `g : S' \to S` is a
morphism of affine schemes"*, and the same move is the first of the three the proof of
Stacks 0DJ9 makes.  This module carries that move in full, unconditionally: no
quasi-compactness, quasi-separatedness, quasi-coherence or Tor-independence hypothesis appears
anywhere below, and the square is not even required to be Cartesian except where the restricted
squares are to be produced.

**The mechanism.**  Localizing the base replaces the square by the rectangle obtained by pasting
it, horizontally, with the Cartesian square over the inclusion of an open of `S'`.  Pasting of
base-change maps is Stacks 0ATM,
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_comp_horizontal`, and in the pasted
composite three of the four factors are invertible for free: two are components of the
composition isomorphisms of Stacks 0D5S, and the third is the base-change map of a Cartesian
square whose horizontal arrows are open immersions,
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions`.  So the
rectangle's base-change map is invertible exactly when the restriction of the square's own
base-change map to that open is — and invertibility in `D(𝒪_{S'})` is local on an open cover,
`Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map`.  Shrinking the base `S` is the
same pasting read with the two squares exchanged.

## Main results

All in the namespace `Stacks.Cohomology.DerivedBaseChange`.

* `isIso_derivedPullback_map_derivedBaseChangeMap_iff`: **localizing `S'`.**  For a Cartesian
  square with open-immersion horizontal arrows pasted on the left, the derived pullback of the
  base-change map along the open immersion of the base is invertible exactly when the
  base-change map of the pasted rectangle is.
* `isIso_derivedBaseChangeMap_hcomp_iff`: **shrinking `S`.**  For a Cartesian square with
  open-immersion horizontal arrows pasted on the *right*, the base-change map of the left-hand
  square at the restricted complex is invertible exactly when the base-change map of the pasted
  rectangle is.
* `isIso_derivedBaseChangeMap_congr`: the base-change map's invertibility only depends on the
  two horizontal arrows up to equality — the transport that lets the two pastings above be
  composed, since the rectangle's legs are produced in two different spellings.
* `isIso_derivedBaseChangeMap_of_isIso_on_open_cover`: **the localization, for ringed spaces.**
  If the base-change maps of the rectangles over the members of an open cover of `S'` are
  invertible, so is the base-change map of the square.
* `isIso_derivedBaseChangeMap_of_isIso_on_open_cover_scheme`: the same for a square of schemes,
  with the cover a family of opens of `S'` and the Cartesian squares over them taken in schemes.
* `isIso_derivedBaseChangeMap_of_affineBaseCase`: **the first move of Stacks 08IB in full.**  For
  a Cartesian square of schemes, the derived base-change map is invertible at `K` as soon as, for
  every affine open `V ⊆ S` and every affine open `V' ⊆ g^{-1}(V)`, the base-change map of the
  restricted square `g|_{V'} : V' \to V` is invertible at the restriction of `K` to `f^{-1}(V)`.
  So the general case of the tag reduces to its case of a morphism of affine schemes.

## Implementation notes

*What this does not prove.*  Nothing here says that any base-change map is invertible under the
hypotheses of Stacks 08IB; the affine case is the hypothesis `haff` of
`isIso_derivedBaseChangeMap_of_affineBaseCase` and is not supplied.  Settling it needs the
identification of the chart comparison of Stacks 0DJ8 (2) — available on charts as
`AlgebraicGeometry.BaseChangeChart.isIso_comparison` — with the affine form of the base-change
map, which the library does not carry.  No tag is registered below for that reason: each
statement is a reduction, and a reduction is not the tag.  What the module does remove is the
source's reduction of Stacks 0DJ9 to an affine base ("we may work locally on `S'`"), in the form
the base-change *map* needs it: that reduction for the general composition
`Lg^*Rf_*K ⟶ Rf'_*K'` of a morphism `φ : L(g')^*K ⟶ K'` is not implied, the restriction of `φ`
to an open of `S'` being a datum this module never forms.

*Why the hypotheses of the two pasting lemmas sit where they do.*  In both, the Cartesian square
and the two open immersions belong to the *other* square, the one supplying the invertible
factor; the square whose base-change map is in question carries nothing but commutativity.  That
is what makes the conclusion usable in both directions: `.mp` localizes, `.mpr` globalizes.

*Why `hk` is a hypothesis of the ringed-space statement and not of the scheme one.*  Openness of
the top arrow of each Cartesian square over a cover member is a consequence of the square — an
open immersion is stable under base change — but that stability is packaged for schemes
(`CategoryTheory.MorphismProperty.of_isPullback`) and not for the Cartesian squares of
sheafed spaces, which are produced one at a time.  The scheme-level statement therefore
discharges it, and the ringed-space statement asks for it; it is satisfied by every Cartesian
square with an open-immersion base, in particular by the chosen fibre products
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_fst_of_right`.

*Why the affine reduction needs a transport of the rectangle.*  The rectangle over an affine open
`V' ⊆ S'` arises twice: once as the paste of the square over `V' \to S'` with the original square,
where its legs read `(f'^{-1}V')_ι ≫ g'` and `V'_ι ≫ g`, and once as the paste of the square over
`V' \to V` with the square over `V \to S`, where they read `g'|_{V'} ≫ (f^{-1}V)_ι` and
`g|_{V'} ≫ V_ι`.  The two spellings are equal by `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` but
not definitionally, and the base-change map depends on its two horizontal arrows, so the
identification is paid by `isIso_derivedBaseChangeMap_congr` — a substitution of two morphism
variables, which costs nothing, rather than an `eqToHom` inside the derived category.

*The restricted square is Cartesian.*  `AlgebraicGeometry.Scheme.Hom.isPullback_resLE` of Mathlib
gives it, at `U_Y = f'^{-1}(V')`, whose hypothesis `U_Y = g'^{-1}(f^{-1}V) ⊓ f'^{-1}(V')` is the
inclusion `preimage_le_preimage_of_comm` proved below.  So `haff` may assume Cartesianness, which
it must: the affine case of Stacks 08IB is false for a square that merely commutes.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-! ### The two horizontal pastings, read for invertibility -/

section Pasting

variable {X'' X' X Y'' Y' Y : RingedSpace.{u, u}} (g' : X'' ⟶ X') (g : X' ⟶ X)
  (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)

/-- **Localizing the base.**  Paste onto a commutative square

```
X' --g--> X
|f'       |f
Y' --h--> Y
```

the Cartesian square over an open immersion `h' : Y'' ⟶ Y'` of the base,

```
X'' --g'--> X'
|f''        |f'
Y'' --h'--> Y'
```

Then the derived pullback along `h'` of the base-change map of the first square is invertible
exactly when the base-change map of the pasted rectangle is.

Of the four factors into which Stacks 0ATM resolves the rectangle's base-change map, the two
composition isomorphisms of Stacks 0D5S are invertible as components of isomorphisms and the
base-change map of the Cartesian square is invertible by
`isIso_derivedBaseChangeMap_of_isOpenImmersions`; so the remaining factor, the derived pullback
of the first square's base-change map, is invertible exactly when the composite is.

No hypothesis is placed on the first square beyond commutativity, and none on `K`. -/
theorem isIso_derivedPullback_map_derivedBaseChangeMap_iff
    [SheafedSpace.IsOpenImmersion g'] [SheafedSpace.IsOpenImmersion h']
    (sq₁ : g ≫ f = f' ≫ h) (sq₂ : IsPullback g' f'' f' h')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso ((derivedPullback h').map (derivedBaseChangeMap g f' f h sq₁ K)) ↔
      IsIso (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
        (hcomp_square g' g f'' f' f h' h sq₁ sq₂.w) K) := by
  have := isIso_derivedBaseChangeMap_of_isOpenImmersions g' f'' f' h' sq₂
    ((derivedPullback g).obj K)
  rw [← derivedBaseChangeMap_comp_horizontal g' g f'' f' f h' h sq₁ sq₂.w K, isIso_comp_left_iff,
    isIso_comp_right_iff]

/-- **Shrinking the base.**  Paste onto a commutative square

```
X'' --g'--> X'
|f''        |f'
Y'' --h'--> Y'
```

the Cartesian square over an open immersion `h : Y' ⟶ Y` of the base,

```
X' --g--> X
|f'       |f
Y' --h--> Y
```

Then the base-change map of the first square, at the restriction `Lg^*K` of the complex, is
invertible exactly when the base-change map of the pasted rectangle is at `K`.

This is `isIso_derivedPullback_map_derivedBaseChangeMap_iff` with the roles of the two squares
exchanged: the same four-factor resolution of Stacks 0ATM, with the invertible factors now the
two composition isomorphisms and the derived pullback of the Cartesian square's base-change
map. -/
theorem isIso_derivedBaseChangeMap_hcomp_iff
    [SheafedSpace.IsOpenImmersion g] [SheafedSpace.IsOpenImmersion h]
    (sq₁ : IsPullback g f' f h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (derivedBaseChangeMap g' f'' f' h' sq₂ ((derivedPullback g).obj K)) ↔
      IsIso (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
        (hcomp_square g' g f'' f' f h' h sq₁.w sq₂) K) := by
  have := isIso_derivedBaseChangeMap_of_isOpenImmersions g f' f h sq₁ K
  rw [← derivedBaseChangeMap_comp_horizontal g' g f'' f' f h' h sq₁.w sq₂ K, isIso_comp_left_iff,
    isIso_comp_left_iff, isIso_comp_right_iff]

end Pasting

/-- Invertibility of the derived base-change map depends on the square's two horizontal arrows
only up to equality: equal arrows give the same map, the commutativity proofs being proofs of a
proposition.  This is the transport that composes the two pastings above, the rectangle over an
open of `S'` being produced with its legs spelled one way by the first and the other way by the
second. -/
theorem isIso_derivedBaseChangeMap_congr {X' X Y' Y : RingedSpace.{u, u}} {g₁ g₂ : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {h₁ h₂ : Y' ⟶ Y} (hg : g₁ = g₂) (hh : h₁ = h₂)
    (sq₁ : g₁ ≫ f = f' ≫ h₁) (sq₂ : g₂ ≫ f = f' ≫ h₂)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (derivedBaseChangeMap g₁ f' f h₁ sq₁ K) ↔
      IsIso (derivedBaseChangeMap g₂ f' f h₂ sq₂ K) := by
  subst hg hh
  exact Iff.rfl

/-! ### Locality on the base -/

section Cover

variable {X' X Y' Y : RingedSpace.{u, u}} (g : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (h : Y' ⟶ Y)

/-- **Invertibility of the derived base-change map is local on the base.**  Let `U` be a family
of opens of `Y'` with `⨆ t, U t = ⊤`, and for each `t` let

```
W t --k t--> X'
|p t          |f'
U t --ι-----> Y'
```

be a Cartesian square with `k t` an open immersion.  If the base-change map of the rectangle
pasted from that square and the given square is invertible at `K` for every `t`, then the
base-change map of the given square is invertible at `K`.

Invertibility in `D(𝒪_{Y'})` is local on the cover
(`Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map`), restriction to a member is
derived pullback along its inclusion
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`), and that derived
pullback of the base-change map is invertible by
`isIso_derivedPullback_map_derivedBaseChangeMap_iff`.

There is no hypothesis on `f`, on `h`, on the square beyond commutativity, or on `K`. -/
theorem isIso_derivedBaseChangeMap_of_isIso_on_open_cover (sq₁ : g ≫ f = f' ≫ h)
    {ι : Type*} (U : ι → TopologicalSpace.Opens Y') (hU : iSup U = ⊤)
    (W : ι → RingedSpace.{u, u}) (k : ∀ t, W t ⟶ X')
    (p : ∀ t, W t ⟶ Y'.restrict (U t).isOpenEmbedding)
    (hk : ∀ t, SheafedSpace.IsOpenImmersion (k t))
    (sqs : ∀ t, IsPullback (k t) (p t) f' (Y'.ofRestrict (U t).isOpenEmbedding))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hloc : ∀ t, IsIso (derivedBaseChangeMap (k t ≫ g) (p t) f
      (Y'.ofRestrict (U t).isOpenEmbedding ≫ h)
      (hcomp_square (k t) g (p t) f' f (Y'.ofRestrict (U t).isOpenEmbedding) h sq₁
        (sqs t).w) K)) :
    IsIso (derivedBaseChangeMap g f' f h sq₁ K) := by
  refine isIso_of_isIso_jStar_mapDerivedCategory_map (structureSheafRing Y') U hU _ fun t => ?_
  refine (NatIso.isIso_map_iff
    (DerivedOpenImmersion.derivedPullbackOpenRestrictionIso Y' (U t)) _).mp ?_
  have := hk t
  exact (isIso_derivedPullback_map_derivedBaseChangeMap_iff (k t) g (p t) f' f
    (Y'.ofRestrict (U t).isOpenEmbedding) h sq₁ (sqs t) K).2 (hloc t)

end Cover

/-! ### Locality on the base, for a square of schemes -/

section Schemes

variable {X' X S' S : Scheme.{u}}

/-- **Invertibility of the derived base-change map of a square of schemes is local on the base.**
Let `V` be a family of opens of `S'` with `⨆ t, V t = ⊤` and for each `t` let

```
W t --k t--> X'
|p t          |f'
V t --ι-----> S'
```

be a Cartesian square of schemes.  If the base-change map of the rectangle pasted from it and the
given square is invertible at `K` for every `t`, then the base-change map of the given square is
invertible at `K`.

This is `isIso_derivedBaseChangeMap_of_isIso_on_open_cover` read through the underlying ringed
spaces.  The openness of `k t` is a consequence of the square, `k t` being a base change of the
open immersion `(V t).ι`, and the square stays Cartesian in ringed spaces by
`isPullback_toShHom_of_isOpenImmersion`.  The underlying ringed space of the open subscheme
`(V t).toScheme` is the restriction of that of `S'`, and `(V t).ι` is its canonical map, so no
transport between the two presentations of an open subspace is needed. -/
theorem isIso_derivedBaseChangeMap_of_isIso_on_open_cover_scheme (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g) {ι : Type*} (V : ι → S'.Opens)
    (hV : iSup V = ⊤) (W : ι → Scheme.{u}) (k : ∀ t, W t ⟶ X')
    (p : ∀ t, W t ⟶ (V t).toScheme) (sqs : ∀ t, IsPullback (k t) (p t) f' (V t).ι)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hloc : ∀ t, IsIso (derivedBaseChangeMap
      ((k t).toLRSHom.toShHom ≫ g'.toLRSHom.toShHom) (p t).toLRSHom.toShHom f.toLRSHom.toShHom
      ((V t).ι.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
      (hcomp_square (k t).toLRSHom.toShHom g'.toLRSHom.toShHom (p t).toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom (V t).ι.toLRSHom.toShHom g.toLRSHom.toShHom
        (AlgebraicGeometry.comp_toShHom_of_comm w)
        (AlgebraicGeometry.comp_toShHom_of_comm (sqs t).w)) K)) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (AlgebraicGeometry.comp_toShHom_of_comm w) K) := by
  refine isIso_derivedBaseChangeMap_of_isIso_on_open_cover g'.toLRSHom.toShHom
    f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (AlgebraicGeometry.comp_toShHom_of_comm w) V hV
    (fun t => (W t).toRingedSpace) (fun t => (k t).toLRSHom.toShHom)
    (fun t => (p t).toLRSHom.toShHom) (fun t => ?_) (fun t => ?_) K hloc
  · have : AlgebraicGeometry.IsOpenImmersion (k t) :=
      MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsOpenImmersion) (sqs t).flip
        inferInstance
    infer_instance
  · exact isPullback_toShHom_of_isOpenImmersion (k t) (p t) f' (V t).ι (sqs t)

/-- The preimage of an open `V' ⊆ S'` under `f'` lands in the preimage under `g'` of the preimage
of `V` under `f`, as soon as `V'` lands in the preimage of `V` under `g`.  This is the
commutativity of the square read on points. -/
theorem preimage_le_preimage_of_comm (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (w : g' ≫ f = f' ≫ g) {V : S.Opens} {V' : S'.Opens} (hle : V' ≤ g ⁻¹ᵁ V) :
    f' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
  intro x hx
  have hb : f.base (g'.base x) = g.base (f'.base x) := by
    simpa using congrArg (fun k : X' ⟶ S => k.base x) w
  change f.base (g'.base x) ∈ V
  rw [hb]
  exact hle hx

/-- **The square restricts.**  For `V ⊆ S` and `V' ⊆ g^{-1}(V)` opens, the restrictions

```
f'^{-1}(V') --g'|--> f^{-1}(V)
   |f'|_{V'}            |f|_V
   V'       --g|-->      V
```

form a commutative square.  The open immersion `V_ι` is a monomorphism, so it suffices to check
the identity after composing with it, where it is the commutativity of the original square. -/
theorem resLE_morphismRestrict_comm (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (w : g' ≫ f = f' ≫ g) {V : S.Opens} {V' : S'.Opens} (hle : V' ≤ g ⁻¹ᵁ V) :
    g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') (preimage_le_preimage_of_comm g' f' f g w hle) ≫ f ∣_ V =
      f' ∣_ V' ≫ g.resLE V V' hle := by
  rw [← cancel_mono V.ι]
  simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι,
    morphismRestrict_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc]
  rw [w]

/-- **The restricted square is Cartesian.**  For a Cartesian square of schemes, opens `V ⊆ S` and
`V' ⊆ g^{-1}(V)`, the square of restrictions is Cartesian.

This is Mathlib's `AlgebraicGeometry.Scheme.Hom.isPullback_resLE` at `U_Y = f'^{-1}(V')`, whose
hypothesis `U_Y = g'^{-1}(f^{-1}V) ⊓ f'^{-1}(V')` is `preimage_le_preimage_of_comm`; the two
vertical legs are then converted from the `resLE` spelling to the `∣_` one by
`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`. -/
theorem isPullback_resLE_morphismRestrict {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) {V : S.Opens} {V' : S'.Opens} (hle : V' ≤ g ⁻¹ᵁ V) :
    IsPullback (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V')
        (preimage_le_preimage_of_comm g' f' f g sq.w hle))
      (f' ∣_ V') (f ∣_ V) (g.resLE V V' hle) := by
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    Scheme.Hom.isPullback_resLE sq hle (le_refl (f ⁻¹ᵁ V)) (UY := f' ⁻¹ᵁ V')
      (inf_eq_right.mpr (preimage_le_preimage_of_comm g' f' f g sq.w hle)).symm

/-- **The first move of the proof of Stacks 08IB, in full.**  Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a Cartesian square of schemes and let `K` be an object of `D(𝒪_X)`.  Suppose that for every
affine open `V ⊆ S` and every affine open `V' ⊆ g^{-1}(V)` the derived base-change map of the
restricted square

```
f'^{-1}(V') --g'|--> f^{-1}(V)
   |f'|_{V'}            |f|_V
   V'       --g|-->      V
```

is invertible at the restriction of `K` to `f^{-1}(V)`.  Then the derived base-change map of the
original square is invertible at `K`.

This is the source's *"to check this is an isomorphism we may work locally on `S'`; hence we may
assume `g : S' \to S` is a morphism of affine schemes"*, and it is the first of the three moves
of the proof of Stacks 0DJ9.  Every point of `S'` lies in an affine open `V'` contained in the
preimage of an affine open `V ∋ g(x)`, which is where affineness is used and the only place it
is; the cover so obtained is fed to
`isIso_derivedBaseChangeMap_of_isIso_on_open_cover_scheme`, and each of its rectangles is
resolved by `isIso_derivedBaseChangeMap_hcomp_iff` against the Cartesian square over `V ⊆ S`,
whose two horizontal arrows are open immersions.

`haff` is asked for only at Cartesian restricted squares, `isPullback_resLE_morphismRestrict`
supplying the Cartesianness: the affine case of the tag is false for a square that merely
commutes, so a hypothesis stated without it could not be discharged.

There is no quasi-compactness, quasi-separatedness, quasi-coherence or Tor-independence
hypothesis: those enter only in `haff`, which this module does not prove. -/
theorem isIso_derivedBaseChangeMap_of_affineBaseCase (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S)
    (g : S' ⟶ S) (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (haff : ∀ (V : S.Opens) (V' : S'.Opens), IsAffineOpen V → IsAffineOpen V' →
      ∀ hle : V' ≤ g ⁻¹ᵁ V,
      IsPullback (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V')
          (preimage_le_preimage_of_comm g' f' f g sq.w hle))
        (f' ∣_ V') (f ∣_ V) (g.resLE V V' hle) →
      IsIso (derivedBaseChangeMap
        (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V')
          (preimage_le_preimage_of_comm g' f' f g sq.w hle)).toLRSHom.toShHom
        (f' ∣_ V').toLRSHom.toShHom (f ∣_ V).toLRSHom.toShHom
        (g.resLE V V' hle).toLRSHom.toShHom
        (AlgebraicGeometry.comp_toShHom_of_comm
          (resLE_morphismRestrict_comm g' f' f g sq.w hle))
        ((derivedPullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj K))) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (AlgebraicGeometry.comp_toShHom_of_comm sq.w) K) := by
  have hex : ∀ x : S', ∃ (V : S.Opens) (V' : S'.Opens), IsAffineOpen V ∧ IsAffineOpen V' ∧
      V' ≤ g ⁻¹ᵁ V ∧ x ∈ V' := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := S) (x := g.base x)
        (U := ⊤) (TopologicalSpace.Opens.mem_top _)
    obtain ⟨V', hV', hxV', hsub⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := S') (x := x)
        (U := g ⁻¹ᵁ V) hxV
    exact ⟨V, V', hV, hV', hsub, hxV'⟩
  choose Vb Vp hVb hVp hlep hmemp using hex
  refine isIso_derivedBaseChangeMap_of_isIso_on_open_cover_scheme g' f' f g sq.w Vp
    (eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmemp y⟩)
    (fun x => (f' ⁻¹ᵁ Vp x).toScheme) (fun x => (f' ⁻¹ᵁ Vp x).ι) (fun x => f' ∣_ Vp x)
    (fun x => (AlgebraicGeometry.isPullback_morphismRestrict f' (Vp x)).flip) K (fun x => ?_)
  have hsq₁ := isPullback_toShHom_of_isOpenImmersion ((f ⁻¹ᵁ Vb x).ι) (f ∣_ Vb x) f ((Vb x).ι)
    (AlgebraicGeometry.isPullback_morphismRestrict f (Vb x)).flip
  exact (isIso_derivedBaseChangeMap_congr
    (AlgebraicGeometry.comp_toShHom_of_comm (Scheme.Hom.resLE_comp_ι g'
      (preimage_le_preimage_of_comm g' f' f g sq.w (hlep x))))
    (AlgebraicGeometry.comp_toShHom_of_comm (Scheme.Hom.resLE_comp_ι g (hlep x))) _ _ K).mp
    ((isIso_derivedBaseChangeMap_hcomp_iff
      (g'.resLE (f ⁻¹ᵁ Vb x) (f' ⁻¹ᵁ Vp x)
        (preimage_le_preimage_of_comm g' f' f g sq.w (hlep x))).toLRSHom.toShHom
      (f ⁻¹ᵁ Vb x).ι.toLRSHom.toShHom (f' ∣_ Vp x).toLRSHom.toShHom
      (f ∣_ Vb x).toLRSHom.toShHom f.toLRSHom.toShHom
      (g.resLE (Vb x) (Vp x) (hlep x)).toLRSHom.toShHom (Vb x).ι.toLRSHom.toShHom
      hsq₁ (AlgebraicGeometry.comp_toShHom_of_comm
        (resLE_morphismRestrict_comm g' f' f g sq.w (hlep x))) K).mp
      (haff (Vb x) (Vp x) (hVb x) (hVp x) (hlep x)
        (isPullback_resLE_morphismRestrict sq (hlep x))))

end Schemes

end

end Stacks.Cohomology.DerivedBaseChange

end
