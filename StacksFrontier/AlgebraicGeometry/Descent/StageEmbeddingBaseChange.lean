module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.FlatBaseChangeOnIntersection

/-!
# The canonical map of a quasi-compact open to the spectrum of its functions under flat base change

Let
```
  Z ---k---→ T
  |          |
  p          g
  ↓          ↓
  Y ---πY--→ S
```
be a Cartesian square of schemes with `S` and `T` affine, `g` flat and `Y` quasi-separated, and let
`U` be a quasi-compact open of `Y`. [Stacks, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
read over the single open `U` — `AlgebraicGeometry.isPushout_appLE_of_flat` — says that
`Γ(Z, p⁻¹U)` is `Γ(Y, U) ⊗_{Γ(S, ⊤)} Γ(T, ⊤)`. This file upgrades that statement about rings to a
statement about the *canonical maps* `τ_U : U ⟶ Spec Γ(Y, U)` of
`AlgebraicGeometry.Scheme.Opens.toSpecΓ`: the square
```
  p⁻¹U ---τ_{p⁻¹U}---→ Spec Γ(Z, p⁻¹U)
   |                        |
  p|                 Spec of the restriction map
   ↓                        ↓
   U -----τ_U---------→ Spec Γ(Y, U)
```
is Cartesian, with no hypothesis on `U` beyond quasi-compactness. Consequently, when `Y` is
ind-quasi-affine — so that `τ_U` is an open immersion by Stacks 0API — the image of an open under
`τ_{p⁻¹U}` is the preimage of its image under `τ_U`.

That last statement is the *stage-level* case of the comparison which step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) reads off its commutative diagram,
and which the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.DescentInvariantsProjections` record as the one missing
input of step 5: there one needs it not for a single quasi-compact open but for an *intersection*
`E` of a nonempty family of them, with `τ` replaced by the embedding `j` of Stacks 0API. See the
implementation notes below for exactly what passing from here to there still needs.

## Main results

* `AlgebraicGeometry.isPullback_toSpecΓ_appLE_of_flat` : **the canonical map of a quasi-compact
  open to the spectrum of its functions is stable under flat affine base change.**
* `AlgebraicGeometry.isOpenImmersion_toSpecΓ_preimage_of_flat` : over an ind-quasi-affine `Y`, the
  canonical map of the preimage open is again an open immersion — without any assumption that `Z`
  be ind-quasi-affine.
* `AlgebraicGeometry.preimage_specMap_appLE_image_toSpecΓ` : **images are preimages.** The image
  under `τ_{p⁻¹U}` of the preimage of an open subset `W` of `Y` is the preimage of the image
  `τ_U(W ∩ U)`. It is written on subsets of the ambient schemes, which is the shape in which
  Stacks 0API states its own assertion about the images of opens.

## Implementation notes

*Why the Cartesian square needs no quasi-affineness.* It is a cancellation. The outer rectangle
```
  p⁻¹U ⟶ Spec Γ(Z, p⁻¹U) ⟶ Spec Γ(T, ⊤)
   |                          |
   ↓                          ↓
   U   ⟶ Spec Γ(Y, U)    ⟶ Spec Γ(S, ⊤)
```
is the Cartesian square `p⁻¹U = U ×_Y Z = U ×_S T` pasted with the square comparing `T` and `S` to
their own spectra, which is Cartesian because both of its horizontal maps are isomorphisms; the
right-hand square is Tag 0APJ over `U`, read through `Spec`. `CategoryTheory.IsPullback.of_right`
then gives the left-hand square. The two rewrites that identify the outer rectangle use only
`AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top` and
`AlgebraicGeometry.Scheme.toSpecΓ_naturality`.

*Why the open immersion on top is free.* `AlgebraicGeometry.IsOpenImmersion` is stable under base
change, and in the Cartesian square above `τ_{p⁻¹U}` is the base change of `τ_U`. So nothing need
be known about `Z`, which in the application is the fibre product `V ×_S X`.

*How the intersection is reached.* Writing `E = ⋂ᵢ Uᵢ` and `j` for the embedding of Stacks 0API,
the statement step 5 consumes is
```
(Spec.map (Scheme.sectionsRingOnSubsetMap p E (p⁻¹E) _)).base ⁻¹' j(W) = j'(p⁻¹W),
```
and it is proved as
`AlgebraicGeometry.preimage_specMap_sectionsRingOnSubsetMap_subsetΓSpecImage`. It uses the results
here together with the conjunct of
`AlgebraicGeometry.exists_iInter_iso_iInter_in_specΓ` identifying each map
`pᵢ : Spec Γ(E, 𝒪_Y|_E) ⟶ Spec Γ(Y, Uᵢ)` with
`Spec.map (Scheme.openToSubset Y (U i) E _)`: with that, the comparison of the stage opens across
the base change is `Spec.map`-functoriality plus
`AlgebraicGeometry.preimage_specMap_appLE_image_toSpecΓ` at `W = Uᵢ`. Ind-quasi-affineness of the
fibre product, which that comparison needs on the other side of the square, is free: a morphism
of affine schemes is affine, so `p` is, and the source of an affine morphism into an
ind-quasi-affine scheme is ind-quasi-affine.

*No tag is placed.* Tag 0APJ is carried by
`AlgebraicGeometry.isPushout_sectionsRingOnSubset_of_flat` and Tag 0API by
`AlgebraicGeometry.exists_iInter_iso_iInter_in_specΓ`; these are steps in the proof of Tag 0APK,
which is stated for an arbitrary fpqc covering family.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {S T Y Z : Scheme.{u}} [IsAffine S] [IsAffine T]
    {πY : Y ⟶ S} {g : T ⟶ S} {p : Z ⟶ Y} {k : Z ⟶ T}

/-- The canonical map of an open of `X`, followed by `Spec` of the restriction of the global
sections map of `f : X ⟶ A` to the open, is the canonical map of `A` after `U.ι ≫ f`. -/
private theorem toSpecΓ_comp_specMap_appTop_comp_presheaf_map {X A : Scheme.{u}} [IsAffine A]
    (f : X ⟶ A) (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (Scheme.Hom.appTop f ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) =
      (U.ι ≫ f) ≫ A.toSpecΓ := by
  rw [Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
    Category.assoc, Category.assoc, ← Scheme.toSpecΓ_naturality]

/-- **The canonical map of a quasi-compact open to the spectrum of its functions is stable under
flat affine base change.**  In a Cartesian square of schemes
```
  Z ---k---→ T
  |          |
  p          g
  ↓          ↓
  Y ---πY--→ S
```
with `S` and `T` affine, `g` flat and `Y` quasi-separated, and for a quasi-compact open `U` of
`Y`, the square
```
  p⁻¹U ---→ Spec Γ(Z, p⁻¹U)
   |            |
   ↓            ↓
   U   ---→ Spec Γ(Y, U)
```
is Cartesian, the vertical maps being the restriction of `p` and the spectrum of the restriction
map on functions.

No quasi-affineness is needed: the ring square is
[Stacks, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ) over one open, and the geometric
square is cancelled out of it. -/
theorem isPullback_toSpecΓ_appLE_of_flat (H : IsPullback p k πY g) [Flat g]
    [QuasiSeparatedSpace Y] (U : Y.Opens) (hU : IsCompact (U : Set Y)) :
    IsPullback (p ⁻¹ᵁ U).toSpecΓ (p ∣_ U)
      (Spec.map (p.appLE U (p ⁻¹ᵁ U) le_rfl)) U.toSpecΓ := by
  have hcomm : (p ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (p.appLE U (p ⁻¹ᵁ U) le_rfl) =
      (p ∣_ U) ≫ U.toSpecΓ := by
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE, Scheme.Hom.resLE_eq_morphismRestrict]
  have tSpec := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_appLE_of_flat H U hU)).flip
  have sB : IsPullback T.toSpecΓ g (Spec.map (Scheme.Hom.appTop g)) S.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality g).symm⟩
  have sA : IsPullback ((p ⁻¹ᵁ U).ι ≫ k) (p ∣_ U) g (U.ι ≫ πY) :=
    ((isPullback_morphismRestrict p U).paste_vert H).flip
  have s := sA.paste_horiz sB
  rw [← toSpecΓ_comp_specMap_appTop_comp_presheaf_map k (p ⁻¹ᵁ U),
    ← toSpecΓ_comp_specMap_appTop_comp_presheaf_map πY U] at s
  exact IsPullback.of_right s hcomm tSpec

/-- Over an ind-quasi-affine scheme, the canonical map of the preimage of a quasi-compact open to
the spectrum of its functions is an open immersion.

This is the base change of the open immersion of
`AlgebraicGeometry.isOpenImmersion_toSpecΓ_of_isIndQuasiAffine` along the Cartesian square of
`AlgebraicGeometry.isPullback_toSpecΓ_appLE_of_flat`, so nothing is assumed about `Z`; in
particular `Z` need not be ind-quasi-affine, which in the proof of Stacks 0APK it is not known to
be. -/
theorem isOpenImmersion_toSpecΓ_preimage_of_flat (H : IsPullback p k πY g) [Flat g]
    [QuasiSeparatedSpace Y] [IsIndQuasiAffine Y] (U : Y.Opens) (hU : IsCompact (U : Set Y)) :
    IsOpenImmersion (p ⁻¹ᵁ U).toSpecΓ :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_toSpecΓ_appLE_of_flat H U hU).flip
    (isOpenImmersion_toSpecΓ_of_isIndQuasiAffine Y U hU)

/-- **The image of an open under the canonical map of a preimage open is the preimage of its
image.**  In the situation of `AlgebraicGeometry.isPullback_toSpecΓ_appLE_of_flat`, with `Y` in
addition ind-quasi-affine: for a subset `W` of `Y` which is open, the preimage in
`Spec Γ(Z, p⁻¹U)` of the image of `W ∩ U` under the canonical map of `U` is the image of
`p⁻¹W ∩ p⁻¹U` under the canonical map of `p⁻¹U`.

This is the stage-level case of the comparison that step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) reads off its commutative diagram.
It is `AlgebraicGeometry.IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback` applied
to the Cartesian square of `AlgebraicGeometry.isPullback_toSpecΓ_appLE_of_flat`, with the open
immersion on the top edge supplied by
`AlgebraicGeometry.isOpenImmersion_toSpecΓ_preimage_of_flat`.

The images and preimages are written as subsets of the ambient schemes rather than as open
subschemes, because that is the shape in which
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API) states its own assertion about
images of opens: `AlgebraicGeometry.exists_iInter_iso_iInter_in_specΓ` phrases it with the subset
`{x : U | (x : Y) ∈ W}`, so the two compose with no transport. No containment of `W` in `U` is
required, since both sides intersect `W` with the relevant open. -/
theorem preimage_specMap_appLE_image_toSpecΓ (H : IsPullback p k πY g) [Flat g]
    [QuasiSeparatedSpace Y] [IsIndQuasiAffine Y] (U : Y.Opens) (hU : IsCompact (U : Set Y))
    (W : Set Y) (hW : IsOpen W) :
    (Spec.map (p.appLE U (p ⁻¹ᵁ U) le_rfl)).base ⁻¹'
        (U.toSpecΓ.base '' {x : U | (x : Y) ∈ W}) =
      (p ⁻¹ᵁ U).toSpecΓ.base '' {z : ↥(p ⁻¹ᵁ U) | (z : Z) ∈ ⇑p ⁻¹' W} := by
  have h1 : IsOpenImmersion U.toSpecΓ := isOpenImmersion_toSpecΓ_of_isIndQuasiAffine Y U hU
  have h2 : IsOpenImmersion (p ⁻¹ᵁ U).toSpecΓ :=
    isOpenImmersion_toSpecΓ_preimage_of_flat H U hU
  have key := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_toSpecΓ_appLE_of_flat H U hU).flip (U.ι ⁻¹ᵁ (⟨W, hW⟩ : Y.Opens))
  have hcoe := TopologicalSpace.Opens.ext_iff.mp key
  simp only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_image] at hcoe
  refine hcoe.symm.trans (congrArg (fun A => (p ⁻¹ᵁ U).toSpecΓ.base '' A) ?_)
  ext z
  have hz : U.ι.base ((p ∣_ U).base z) = p.base ((p ⁻¹ᵁ U).ι.base z) :=
    congrArg (fun m : (p ⁻¹ᵁ U).toScheme ⟶ Y => m.base z) (morphismRestrict_ι p U)
  change U.ι.base ((p ∣_ U).base z) ∈ W ↔ _
  rw [hz]
  exact Iff.rfl

end AlgebraicGeometry

end

end
