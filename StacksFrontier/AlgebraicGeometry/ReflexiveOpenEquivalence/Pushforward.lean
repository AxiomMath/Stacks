module

public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.AffineExtension
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.RestrictStalk
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.RingTheory.Depth.RingEquiv

/-!
# Tag 0EBJ: restriction and direct image are inverse on coherent reflexive modules

Let `X` be an integral locally Noetherian scheme and `j : U → X` an open subscheme whose
complement consists of points at which the structure sheaf has depth at least two.  Then `j^*`
and `j_*` are inverse equivalences between the coherent reflexive `𝒪_X`-modules and the coherent
reflexive `𝒪_U`-modules.  That is
[Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ), and this file proves it.

What remained was the direct-image step: that `j_*𝒢` is coherent and reflexive for `𝒢` coherent
and reflexive on `U`.  The source proves it by *reducing to `X` affine*, and that reduction is
carried out here:

* coherence and reflexivity are local on nonempty affine opens
  (`isCoherent_and_isReflexive_of_forall_isAffineOpen_restrict`);
* the restriction of `j_*𝒢` to an open `V` of `X` is the direct image of `𝒢|_{j⁻¹V}` along
  `j ∣_ V` (`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`);
* on an affine `V` that direct image is coherent and reflexive, because every coherent module on
  an open of an affine locally Noetherian scheme extends
  (`exists_isCoherent_extension_of_isAffine`, part (1) of Tag 0G41) and the extension may be
  taken reflexive.

The depth hypothesis transports from `X` to `V` because the local rings at a point of `V` are
the same ring up to isomorphism and depth is a ring-isomorphism invariant
(`Module.depth_self_eq_of_ringEquiv`).

## Main results

* `isCoherent_and_isReflexive_pushforward_of_isOpenImmersion`: the direct-image step for an
  arbitrary open immersion into an affine integral locally Noetherian scheme.
* `two_le_depth_stalk_restrict`: the depth hypothesis on an open subscheme.
* `isCoherent_and_isReflexive_pushforward`: **the direct-image step of Tag 0EBJ, unconditional**.
* `reflexiveCoherentEquivalence`: **Stacks, Tag 0EBJ**, carrying the tag.

## Implementation notes

The reduction produces `j ∣_ V`, which is an open immersion but is not the inclusion of an open
subscheme, so the affine statement is first transported along `Scheme.Hom.isoOpensRange` —
`pushforwardIsoRestrictInverse` turns the direct image along the isomorphism into a restriction,
after which `Scheme.Modules.pushforwardComp` and `Scheme.Modules.pushforwardCongr` identify the
composite with the direct image along `j ∣_ V` itself.

Integrality is used only on `X` and on the *nonempty affine opens* of `X`, never on `U` or on
`j⁻¹V`; that is why the restriction statements of
`StacksFrontier/AlgebraicGeometry/ReflexiveOpenEquivalence/RestrictStalk.lean` are proved
through stalks rather than from clause (2) of Tag 0EBF, which assumes an integral source.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- Coherence and reflexivity pull back along an isomorphism of modules. -/
private theorem isCoherent_and_isReflexive_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (hC : G.IsCoherent) (hR : IsReflexive G) : F.IsCoherent ∧ IsReflexive F :=
  ⟨Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := X.ringCatSheaf) e,
    isReflexive_of_iso e.symm hR⟩

/-- **The direct-image step of Stacks, Tag 0EBJ, for an arbitrary open immersion into an affine
scheme.**  Same as `isCoherent_and_isReflexive_pushforward_of_isAffine`, for an open immersion
rather than the inclusion of an open subscheme. -/
public theorem isCoherent_and_isReflexive_pushforward_of_isOpenImmersion {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] [IsAffine X] (f : Y ⟶ X)
    [IsOpenImmersion f]
    (hdepth : ∀ x : X, x ∉ (f.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (G : Y.Modules) (hGcoh : G.IsCoherent) (hGrefl : IsReflexive G) :
    ((Scheme.Modules.pushforward f).obj G).IsCoherent ∧
      IsReflexive ((Scheme.Modules.pushforward f).obj G) := by
  have hYN : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion f
  let e := f.isoOpensRange
  let H := G.restrict e.inv
  obtain ⟨hC, hR⟩ := isCoherent_and_isReflexive_pushforward_of_isAffine X f.opensRange hdepth
    H (isCoherent_restrict_of_isOpenImmersion e.inv G hGcoh)
    (isReflexive_restrict_of_isOpenImmersion e.inv G hGcoh hGrefl)
  let i : (Scheme.Modules.pushforward f.opensRange.ι).obj H ≅
      (Scheme.Modules.pushforward f).obj G :=
    (Scheme.Modules.pushforward f.opensRange.ι).mapIso (pushforwardIsoRestrictInverse e G).symm ≪≫
      (Scheme.Modules.pushforwardComp e.hom f.opensRange.ι).app G ≪≫
      (Scheme.Modules.pushforwardCongr f.isoOpensRange_hom_ι).app G
  exact isCoherent_and_isReflexive_of_iso i.symm hC hR

/-- **The depth hypothesis of Tag 0EBJ on an open subscheme.**  The local rings of an open
subscheme are the local rings of the ambient scheme, and the depth of a local ring along its
maximal ideal is a ring-isomorphism invariant. -/
public theorem two_le_depth_stalk_restrict {X : Scheme.{u}} (V : X.Opens) (v : V.toScheme)
    (h : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk v.1)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk v.1)) (X.presheaf.stalk v.1)) :
    (2 : ℕ∞) ≤ Module.depth (V.toScheme.presheaf.stalk v)
      (IsLocalRing.maximalIdeal (V.toScheme.presheaf.stalk v))
      (V.toScheme.presheaf.stalk v) := by
  rwa [Module.depth_self_eq_of_ringEquiv (V.stalkIso v).commRingCatIsoToRingEquiv]

/-- **The direct-image step of Stacks, Tag 0EBJ, unconditionally.**  On an integral locally
Noetherian scheme, the direct image of a coherent reflexive module on an open subscheme whose
complement has structure-sheaf depth at least two is coherent and reflexive.

This is the source's reduction to the affine case, carried out: both conclusions are local on
nonempty affine opens, the restriction of the direct image to an open of the target is the
direct image of a restriction, and on an affine open the statement is
`isCoherent_and_isReflexive_pushforward_of_isOpenImmersion`. -/
public theorem isCoherent_and_isReflexive_pushforward (X : Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (G : U.toScheme.Modules) (hGcoh : G.IsCoherent) (hGrefl : IsReflexive G) :
    ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
      IsReflexive ((Scheme.Modules.pushforward U.ι).obj G) := by
  have hUN : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  refine isCoherent_and_isReflexive_of_forall_isAffineOpen_restrict _ fun V hVa hVne => ?_
  have hVaff : IsAffine V.toScheme := hVa
  have := hVne
  have hVint : AlgebraicGeometry.IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have hVN : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have hd : ∀ v : V.toScheme, v ∉ ((U.ι ∣_ V).opensRange : Set V.toScheme) →
      (2 : ℕ∞) ≤ Module.depth (V.toScheme.presheaf.stalk v)
        (IsLocalRing.maximalIdeal (V.toScheme.presheaf.stalk v))
        (V.toScheme.presheaf.stalk v) := fun v hv =>
    two_le_depth_stalk_restrict V v (hdepth v.1 fun hvU =>
      hv ⟨⟨⟨v.1, hvU⟩, v.2⟩, Subtype.ext (morphismRestrict_base_coe U.ι V _)⟩)
  obtain ⟨hC, hR⟩ := isCoherent_and_isReflexive_pushforward_of_isOpenImmersion (U.ι ∣_ V) hd
    (G.restrict (U.ι ⁻¹ᵁ V).ι) (isCoherent_restrict_of_isOpenImmersion _ G hGcoh)
    (isReflexive_restrict_of_isOpenImmersion _ G hGcoh hGrefl)
  let i : ((Scheme.Modules.pushforward U.ι).obj G).restrict V.ι ≅
      (Scheme.Modules.pushforward (U.ι ∣_ V)).obj (G.restrict (U.ι ⁻¹ᵁ V).ι) :=
    (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso U.ι V).app G
  exact isCoherent_and_isReflexive_of_iso i hC hR

/-- **Stacks Project, Tag 0EBJ.** Restriction to an open subscheme whose complement
has structure-sheaf depth at least two is an equivalence on coherent reflexive modules;
its inverse is direct image. Both identifications are natural.

This is `reflexiveCoherentEquivalenceOfPushforward` with its one hypothesis discharged by
`isCoherent_and_isReflexive_pushforward`. -/
@[stacks 0EBJ]
public noncomputable def reflexiveCoherentEquivalence (X : Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    Σ e : ReflexiveCoherentModules X ≌ ReflexiveCoherentModules U.toScheme,
      (e.functor ⋙ ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pullback U.ι) ×
      (e.inverse ⋙ ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pushforward U.ι) :=
  reflexiveCoherentEquivalenceOfPushforward X U hdepth
    (isCoherent_and_isReflexive_pushforward X U hdepth)

end Stacks.AlgebraicGeometry.ReflexiveModules

end
