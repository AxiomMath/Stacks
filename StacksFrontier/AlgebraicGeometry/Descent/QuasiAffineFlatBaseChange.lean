module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfae

/-!
# The affine hull of a quasi-affine scheme over an affine base, and flat base change

Let `S` be an affine scheme and let `f : X ⟶ S` be a quasi-affine morphism. Then `X` is a
quasi-affine scheme, the relative spectrum of `f_*𝒪_X` is the affine scheme `Spec Γ(X, ⊤)`, and
the canonical morphism `X ⟶ Spec Γ(X, ⊤)` is a quasi-compact open immersion over `S`. This file
records that description, and proves that the whole picture is stable under flat base change:
for an affine scheme `T` and a flat morphism `T ⟶ S`, the affine hull of `X ×_S T` is
`Spec Γ(X, ⊤) ×_S T`, and `X ×_S T ⟶ Spec Γ(X ×_S T, ⊤)` is the base change of
`X ⟶ Spec Γ(X, ⊤)`.

The second statement is the input which the proof of Stacks 0247 — effective descent for
quasi-affine morphisms along an fppf covering — takes from Stacks 02KH, flat base change for the
higher direct images, at `i = 0`. Over an affine base the sections of the pushforward are the
global sections, so no derived functor is involved, and the comparison map is Mathlib's
`AlgebraicGeometry.pushoutSection`, which
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` proves to be an
isomorphism for a quasi-compact quasi-separated source. A quasi-affine scheme is quasi-compact
and separated, so that hypothesis is met.

Stacks 0247 reduces by Stacks 02W3 to one faithfully flat morphism `Spec(A) ⟶ Spec(R)` of affine
schemes and a descent datum `(V, φ)` on a quasi-affine `V ⟶ Spec(A)`. The statements of this
file are then applied with `Spec(A)` as the affine base, `Spec(A) ×_{Spec(R)} Spec(A)` as the
affine scheme over it, and each of the two projections as the flat morphism — both are base
changes of `Spec(A) ⟶ Spec(R)`. The two base changes of `V` along those projections are the two
sides of `φ`, so the flat base change of the affine hull, applied twice, turns `φ` into a gluing
isomorphism of the affine scheme `Spec Γ(V, ⊤)`, under which the quasi-compact open immersion
`V ⟶ Spec Γ(V, ⊤)` is a morphism of descent data.

## Main definitions

* `AlgebraicGeometry.specΓToBase` is the structure morphism `Spec Γ(X, ⊤) ⟶ S` of the affine
  hull of `X` over an affine base `S`, through which a morphism `f : X ⟶ S` factors.

## Main results

* `AlgebraicGeometry.isPushout_appTop_of_flat`: **Stacks 02KH at `i = 0` over an affine base.**
  In a Cartesian square whose base and whose right-hand column are affine, with the right-hand
  column flat, and whose left-hand column has quasi-compact quasi-separated source, the induced
  square of global sections is a pushout of rings. Concretely
  `Γ(X ×_S T, ⊤) = Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(T, ⊤)`.
* `AlgebraicGeometry.isPullback_specMap_appTop_of_flat`: the same statement read through `Spec` —
  the affine hull of the base change is the base change of the affine hull.
* `AlgebraicGeometry.isPullback_toSpecΓ_of_flat`: the canonical morphism to the affine hull is
  stable under such a base change — the square formed by `X ×_S T ⟶ X` and the two canonical
  morphisms `· ⟶ Spec Γ(·, ⊤)` is Cartesian. Besides identifying the affine hull of the base
  change, this says that the base change of `X` sits inside that affine hull as the preimage of
  `X`, so that every property of `X ⟶ Spec Γ(X, ⊤)` stable under base change is inherited.
* `AlgebraicGeometry.isQuasiAffineHom_iff_toSpecΓ`: **Stacks 01SM, part (4), over an affine
  base.** A morphism to an affine scheme is quasi-affine exactly when the canonical morphism
  from its source to the spectrum of its global sections is a quasi-compact open immersion.
* `AlgebraicGeometry.toSpecΓ_specΓToBase`: that quasi-compact open immersion is a morphism over
  the base, and `AlgebraicGeometry.isAffineHom_specΓToBase` records that the remaining factor is
  affine. Together they are the factorization of a quasi-affine morphism over an affine base
  into a quasi-compact open immersion followed by an affine morphism.
* `AlgebraicGeometry.isOpenImmersion_toSpecΓ_of_flat`: for the base change of a quasi-affine
  morphism along a flat morphism of affine schemes, the canonical morphism to the affine hull is
  again a quasi-compact open immersion.
* `AlgebraicGeometry.isPullback_fst_pullback_comp` and
  `AlgebraicGeometry.isPullback_snd_pullback_comp`: the two sides `V ×_S X` and `X ×_S V` of a
  descent datum are the base changes of `V ⟶ X` along the two projections of `X ×_S X`.
* `AlgebraicGeometry.isPullback_toSpecΓ_pullback_fst` and
  `AlgebraicGeometry.isPullback_toSpecΓ_pullback_snd`: the flat base change of the affine hull
  read at those two projections. These are the two identifications under which the gluing
  isomorphism of a descent datum of quasi-affine schemes becomes a gluing isomorphism of the
  affine scheme `Spec Γ(V, ⊤)`.

## Implementation notes

`AlgebraicGeometry.isPushout_appTop_of_flat` is Mathlib's comparison map read at
`U_S = U_T = U_X = ⊤`. Mathlib states it for the sections over arbitrary opens, with the open of
the fibre product given as `pr₁ ⁻¹ U_X ⊓ pr₂ ⁻¹ U_T`; at `⊤` that open is `⊤`, and the four
`appLE ⊤ ⊤` are the four `appTop` by `Stacks.AffineAlgebraEquivalence.appLE_top_top`.

`AlgebraicGeometry.isPullback_toSpecΓ_of_flat` is deduced from it by one application of
`CategoryTheory.IsPullback.of_right`: the square to be proved Cartesian, pasted on the right
with the Cartesian square of affine hulls, is the given Cartesian square, because the canonical
morphism to the affine hull is a morphism over the base. The right-hand square is the image
under `Spec` of the pushout of global sections, with its two affine corners transported along
`AlgebraicGeometry.Scheme.isoSpec`.

Nothing here needs the base change to be *faithfully* flat: surjectivity of `T ⟶ S` enters the
proof of Stacks 0247 only after this step, when the descended open is cut out.

## References

* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### Stacks 01SM, part (4), over an affine base -/

/-- The structure morphism over an affine base `S` of the affine hull `Spec Γ(X, ⊤)` of the
source of a morphism `f : X ⟶ S`. Over an affine base this is the structure morphism of the
relative spectrum of `f_*𝒪_X`, and `AlgebraicGeometry.toSpecΓ_specΓToBase` is the factorization
of `f` through it. -/
noncomputable def specΓToBase [IsAffine S] (f : X ⟶ S) : Spec Γ(X, ⊤) ⟶ S :=
  Spec.map f.appTop ≫ S.isoSpec.inv

/-- The structure morphism of the affine hull over an affine base is an affine morphism, both
its source and its target being affine. -/
instance isAffineHom_specΓToBase [IsAffine S] (f : X ⟶ S) : IsAffineHom (specΓToBase f) :=
  inferInstance

/-- A morphism to an affine scheme is recovered from its map on global sections. -/
private theorem toSpecΓ_comp_map_appTop_comp_isoSpec_inv [IsAffine S] (f : X ⟶ S) :
    X.toSpecΓ ≫ Spec.map f.appTop ≫ S.isoSpec.inv = f := by
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- A morphism to an affine scheme factors through the affine hull of its source. -/
@[reassoc (attr := simp)]
theorem toSpecΓ_specΓToBase [IsAffine S] (f : X ⟶ S) : X.toSpecΓ ≫ specΓToBase f = f :=
  toSpecΓ_comp_map_appTop_comp_isoSpec_inv f

/-- **Stacks Project, Tag 01SM, part (4), over an affine base.** A morphism to an affine scheme
is quasi-affine if and only if the canonical morphism from its source to the spectrum of its
global sections — the relative spectrum of the pushforward of the structure sheaf — is a
quasi-compact open immersion. -/
@[stacks 01SM "(4) over an affine base", ega "II 5.1.6" "(a)<=>(b), affine base", ega "II 5.1.8"]
theorem isQuasiAffineHom_iff_toSpecΓ [IsAffine S] (f : X ⟶ S) :
    IsQuasiAffineHom f ↔ IsOpenImmersion X.toSpecΓ ∧ QuasiCompact X.toSpecΓ := by
  rw [isQuasiAffineHom_iff_isQuasiAffine f]
  refine ⟨fun hX ↦ have := hX; ⟨inferInstance, inferInstance⟩, fun ⟨hi, hc⟩ ↦ ?_⟩
  have := hc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace X.toSpecΓ
  have : IsImmersion X.toSpecΓ := have := hi; inferInstance
  constructor

/-! ### Flat base change -/

/-- **Stacks Project, Tag 02KH at `i = 0`, over an affine base.** Let
```
  Y ---p--→ X
  |         |
  q         π
  ↓         ↓
  T ---g--→ S
```
be a Cartesian square of schemes with `S` and `T` affine, `g` flat, and `X` quasi-compact and
quasi-separated. Then the induced square of global sections is a pushout of rings, that is,
`Γ(Y, ⊤) = Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(T, ⊤)`.

This is flat base change for the pushforward of the structure sheaf in degree zero: over an
affine base the sections of `π_*𝒪_X` are the global sections of `X`, and the comparison map is
Mathlib's `AlgebraicGeometry.pushoutSection` read at the total opens. -/
@[ega "III 1.4.15" "q=0, F=O_X, affine base",
  sga "3 XV 4.7" "special case",
  sga "7 VII 1.3.8" "special case"]
theorem isPushout_appTop_of_flat {Y T : Scheme.{u}} {π : X ⟶ S} {g : T ⟶ S} {p : Y ⟶ X}
    {q : Y ⟶ T} (H : IsPullback p q π g) [IsAffine S] [IsAffine T] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsPushout π.appTop g.appTop p.appTop q.appTop := by
  have h₁ : (⊤ : T.Opens) ≤ g ⁻¹ᵁ (⊤ : S.Opens) := le_top
  have h₂ : (⊤ : X.Opens) ≤ π ⁻¹ᵁ (⊤ : S.Opens) := le_top
  have h₃ : (⊤ : Y.Opens) = p ⁻¹ᵁ (⊤ : X.Opens) ⊓ q ⁻¹ᵁ (⊤ : T.Opens) := by simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H h₁ h₂ h₃
    (isAffineOpen_top S) (isAffineOpen_top T) isCompact_univ isQuasiSeparated_univ
  have h := (isIso_pushoutSection_iff H h₁ h₂ h₃).1 hiso
  rwa [Stacks.AffineAlgebraEquivalence.appLE_top_top,
    Stacks.AffineAlgebraEquivalence.appLE_top_top,
    Stacks.AffineAlgebraEquivalence.appLE_top_top,
    Stacks.AffineAlgebraEquivalence.appLE_top_top] at h

/-- The affine hulls of a Cartesian square as in `AlgebraicGeometry.isPushout_appTop_of_flat`
again form a Cartesian square: `Spec Γ(X ×_S T, ⊤) = Spec Γ(X, ⊤) ×_S T`, compatibly with the
structure morphisms over `S` and over `T`. -/
theorem isPullback_specMap_appTop_of_flat {Y T : Scheme.{u}} {π : X ⟶ S} {g : T ⟶ S} {p : Y ⟶ X}
    {q : Y ⟶ T} (H : IsPullback p q π g) [IsAffine S] [IsAffine T] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsPullback (Spec.map p.appTop) (Spec.map q.appTop ≫ T.isoSpec.inv) (specΓToBase π) g := by
  have HS : IsPullback (Spec.map p.appTop) (Spec.map q.appTop) (Spec.map π.appTop)
      (Spec.map g.appTop) := ((isPushout_appTop_of_flat H).op.map Scheme.Spec).flip
  refine HS.of_iso (Iso.refl _) (Iso.refl _) T.isoSpec.symm S.isoSpec.symm
    (by simp) (by simp) (by simp [specΓToBase]) ?_
  rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom,
    ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- **The affine hull of a quasi-compact quasi-separated scheme over an affine base commutes
with flat base change, compatibly with the canonical morphism into it.** In the Cartesian square
of `AlgebraicGeometry.isPushout_appTop_of_flat`, the square
```
  Y ------→ Spec Γ(Y, ⊤)
  |              |
  p              |
  ↓              ↓
  X ------→ Spec Γ(X, ⊤)
```
formed by the two canonical morphisms is Cartesian. In particular `Y` is the preimage of `X`
under `Spec Γ(Y, ⊤) ⟶ Spec Γ(X, ⊤)`, so every property of `X ⟶ Spec Γ(X, ⊤)` stable under base
change — being an open immersion, being quasi-compact — is inherited by `Y ⟶ Spec Γ(Y, ⊤)`.

This is the step of the proof of Stacks 0247 which transports a descent datum on a quasi-affine
`X` over the base to a descent datum on the affine scheme `Spec Γ(X, ⊤)`, with the quasi-compact
open immersion `X ⟶ Spec Γ(X, ⊤)` a morphism of descent data. -/
theorem isPullback_toSpecΓ_of_flat {Y T : Scheme.{u}} {π : X ⟶ S} {g : T ⟶ S} {p : Y ⟶ X}
    {q : Y ⟶ T} (H : IsPullback p q π g) [IsAffine S] [IsAffine T] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsPullback Y.toSpecΓ p (Spec.map p.appTop) X.toSpecΓ := by
  refine IsPullback.of_right ?_ (Scheme.toSpecΓ_naturality p).symm
    (isPullback_specMap_appTop_of_flat H).flip
  rw [toSpecΓ_comp_map_appTop_comp_isoSpec_inv, toSpecΓ_specΓToBase]
  exact H.flip

/-- `isPullback_toSpecΓ_of_flat` for the base change of a quasi-affine morphism `π`. -/
private theorem isPullback_toSpecΓ_of_flat_of_isQuasiAffineHom {Y T : Scheme.{u}} {π : X ⟶ S}
    {g : T ⟶ S} {p : Y ⟶ X} {q : Y ⟶ T} (H : IsPullback p q π g) [IsAffine S] [IsAffine T]
    [Flat g] [IsQuasiAffineHom π] : IsPullback Y.toSpecΓ p (Spec.map p.appTop) X.toSpecΓ :=
  have : X.IsQuasiAffine := (isQuasiAffineHom_iff_isQuasiAffine π).1 inferInstance
  isPullback_toSpecΓ_of_flat H

/-- For the base change of a quasi-affine morphism along a flat morphism of affine schemes, the
canonical morphism to the affine hull is again a quasi-compact open immersion. With
`AlgebraicGeometry.isPullback_toSpecΓ_of_flat` this says that the factorization of Stacks 01SM
part (4) is stable under such a base change. -/
theorem isOpenImmersion_toSpecΓ_of_flat {Y T : Scheme.{u}} {π : X ⟶ S} {g : T ⟶ S} {p : Y ⟶ X}
    {q : Y ⟶ T} (H : IsPullback p q π g) [IsAffine S] [IsAffine T] [Flat g]
    [IsQuasiAffineHom π] :
    IsOpenImmersion Y.toSpecΓ ∧ QuasiCompact Y.toSpecΓ := by
  have hY : IsQuasiAffineHom q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback H inferInstance
  have : Y.IsQuasiAffine := (isQuasiAffineHom_iff_isQuasiAffine q).1 hY
  exact ⟨inferInstance, inferInstance⟩

/-! ### The two base changes carrying a descent datum

A descent datum for `V/X/S` relative to `f : X ⟶ S` is an isomorphism
`V ×_S X ≅ X ×_S V` over `X ×_S X` — in the shape of
`AlgebraicGeometry.DescentDatum.transitionPullbackIso`, an isomorphism
`pullback (π ≫ f) f ≅ pullback f (π ≫ f)` for `π : V ⟶ X` the structure morphism. The two sides
are the base changes of `π` along the two projections of `X ×_S X`, both of which are base
changes of `f` and so flat as soon as `f` is. The two statements below read the flat base change
of the affine hull at those two projections, which is what turns such an isomorphism into an
isomorphism of the two base changes of `Spec Γ(V, ⊤)`. -/

/-- `V ×_S X` is the base change of `V ⟶ X` along the first projection of `X ×_S X`. -/
theorem isPullback_fst_pullback_comp {V : Scheme.{u}} (f : X ⟶ S) (π : V ⟶ X) :
    IsPullback (pullback.fst (π ≫ f) f)
      (pullback.lift (pullback.fst (π ≫ f) f ≫ π) (pullback.snd (π ≫ f) f)
        (by rw [Category.assoc, pullback.condition])) π (pullback.fst f f) := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f f)
  rw [pullback.lift_snd]
  exact IsPullback.of_hasPullback (π ≫ f) f

/-- `X ×_S V` is the base change of `V ⟶ X` along the second projection of `X ×_S X`. -/
theorem isPullback_snd_pullback_comp {V : Scheme.{u}} (f : X ⟶ S) (π : V ⟶ X) :
    IsPullback (pullback.snd f (π ≫ f))
      (pullback.lift (pullback.fst f (π ≫ f)) (pullback.snd f (π ≫ f) ≫ π)
        (by rw [Category.assoc, ← pullback.condition])) π (pullback.snd f f) := by
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback f f).flip
  rw [pullback.lift_fst]
  exact (IsPullback.of_hasPullback f (π ≫ f)).flip

variable {V : Scheme.{u}} (f : X ⟶ S) (π : V ⟶ X)

/-- The affine hull of `V ×_S X` is the first base change of the affine hull of `V`, and
`V ×_S X` sits inside it as the preimage of `V`. -/
theorem isPullback_toSpecΓ_pullback_fst [IsAffine S] [IsAffine X] [Flat f]
    [IsQuasiAffineHom π] :
    IsPullback (pullback (π ≫ f) f).toSpecΓ (pullback.fst (π ≫ f) f)
      (Spec.map (pullback.fst (π ≫ f) f).appTop) V.toSpecΓ :=
  isPullback_toSpecΓ_of_flat_of_isQuasiAffineHom (isPullback_fst_pullback_comp f π)

/-- The affine hull of `X ×_S V` is the second base change of the affine hull of `V`, and
`X ×_S V` sits inside it as the preimage of `V`. -/
theorem isPullback_toSpecΓ_pullback_snd [IsAffine S] [IsAffine X] [Flat f]
    [IsQuasiAffineHom π] :
    IsPullback (pullback f (π ≫ f)).toSpecΓ (pullback.snd f (π ≫ f))
      (Spec.map (pullback.snd f (π ≫ f)).appTop) V.toSpecΓ :=
  isPullback_toSpecΓ_of_flat_of_isQuasiAffineHom (isPullback_snd_pullback_comp f π)

end AlgebraicGeometry

end
