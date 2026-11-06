module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.MonoIntoLocallyArtinian
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyQuasiFiniteOverFieldRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.MonoToZeroDimensionalLocalSpectra
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty

/-!
# Monomorphisms into algebraic spaces locally quasi-finite over a field

Let `k` be a field and `f : X ⟶ Y` a monomorphism of algebraic spaces over `k`. If `Y` is locally
quasi-finite over `k`, so is `X`. This is Stacks 06S1.

## Main results

* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono_of_isLocallyQuasiFinite`:
  **Stacks 06S1**.

## Implementation notes

An algebraic space over `k` is an algebraic space over a scheme `S` together with an isomorphism
`S ≅ Spec k`, and its structure morphism is the unique morphism to the presheaf represented by the
base. A monomorphism of algebraic spaces is a monomorphism of presheaves.

The proof follows the source's. The space `Y` is a scheme by the scheme clause of Stacks 06LZ,
and its underlying scheme is locally Artinian, being locally quasi-finite over `Spec k`. The point
space of `Y` is discrete (Stacks 0ACA), the monomorphism `f` is injective and continuous on
points (Stacks 06RV and 03BX), so the point space of `X` is discrete too; `X` is quasi-separated,
since `Y` is a discrete scheme and a monomorphism is quasi-separated, and so reasonable by Stacks
03JX, and a reasonable algebraic space with discrete point space is a scheme. This is the argument
of Stacks 06RZ, run here on the discreteness of `|Y|` rather than on a decomposition of `Y` into
spectra of zero-dimensional local rings, so that Stacks 06S0 is not needed.

The morphism of schemes underlying `f` is then a monomorphism into a locally Artinian scheme,
hence locally of finite type: over a point of the target it is, on an affine open of the source,
an epimorphism of rings out of an Artinian local ring, which is surjective by Nakayama's lemma
(this is the source's computation with `A_i → B_i`). A monomorphism which is locally of finite
type is locally quasi-finite (Stacks 0463), and the composite with the structure morphism of `Y`
is locally quasi-finite (Stacks 03XK).

## References

* [Stacks Project, Tag 06S1](https://stacks.math.columbia.edu/tag/06S1)
* [Stacks Project, Tag 06RZ](https://stacks.math.columbia.edu/tag/06RZ)
* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Stacks 06S1.** Let `k` be a field and `f : X ⟶ Y` a monomorphism of algebraic spaces over
`k`. If `Y` is locally quasi-finite over `k`, so is `X`. -/
@[stacks 06S1]
theorem isLocallyQuasiFinite_of_mono_of_isLocallyQuasiFinite {k : Type u} [Field k]
    (e : S ≅ Spec (.of k)) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) [Mono f]
    (hYk : IsLocallyQuasiFinite B S hS ((isTerminal_yoneda_obj_base B S hS).from Y)) :
    IsLocallyQuasiFinite B S hS ((isTerminal_yoneda_obj_base B S hS).from X) := by
  have hZ := BigFppfSite.contains_terminal B
  let T := BigFppfOver.toScheme B S hS
  let K : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let eK : T.obj K ≅ Spec (.of k) := e
  have hK : Subsingleton (T.obj K) :=
    ⟨fun a b ↦ eK.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  -- `Y` is a scheme whose underlying scheme is locally Artinian
  have : Y.IsRepresentable := isRepresentable_of_isLocallyQuasiFinite_to_field B S hS eK hY _ hYk
  let gY : Y.reprX ⟶ K := yoneda.preimage (Y.reprW.hom ≫ (isTerminal_yoneda_obj_base B S hS).from Y)
  have : LocallyQuasiFinite (T.map gY) :=
    (prop_toScheme_map_of_holdsOnEveryEtaleChart B S hS hYk Y.reprW.hom
      (presheaf_etale_of_iso B S hS Y.reprW) (t := gY) (yoneda.map_preimage _)).2
  have : IsLocallyArtinian (T.obj Y.reprX) := .of_locallyQuasiFinite (T.map gY ≫ eK.hom)
  -- `X` is a scheme: its point space is discrete and it is reasonable
  have := discreteTopology_points_of_isLocallyQuasiFinite B S hS hY hK _ hYk
  have hdiscX : DiscreteTopology (points B S hS X) :=
    DiscreteTopology.of_continuous_injective (continuous_pointsMap B S hS f)
      (pointsMap_injective_of_mono B S hS f)
  have hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS Y hZ
        ⟨Y.reprX, inferInstance, ⟨Y.representableBy⟩⟩)
      (isQuasiSeparated_of_mono B S hS f inferInstance)
  have : X.IsRepresentable :=
    isRepresentable_of_discreteTopology_points_of_isReasonableSpace B S hS hX
      (isReasonableSpace_of_isVeryReasonableSpace B S hS X hX
        (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ X hX
          (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS X hZ hX
            hXqs)))
      hdiscX
  -- the morphism of schemes underlying `f` is a monomorphism into a locally Artinian scheme
  let p : X.reprX ⟶ Y.reprX := yoneda.preimage (X.reprW.hom ≫ f ≫ Y.reprW.inv)
  have : Mono p := (Functor.mono_map_iff_mono yoneda p).1 (by
    rw [show yoneda.map p = X.reprW.hom ≫ f ≫ Y.reprW.inv from yoneda.map_preimage _]
    exact mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ X.reprW.isIso_hom)
      (mono_comp' ‹Mono f› (@IsIso.mono_of_iso _ _ _ _ _ Y.reprW.isIso_inv)))
  have hft : IsLocallyOfFiniteType B S hS f :=
    (holdsOnEveryEtaleChart_iff_representable B S hS _
      isEtaleLocalOnSourceAndTarget_locallyOfFiniteType f).2
      (locallyOfFiniteType_of_mono_of_isLocallyArtinian (T.map p))
  rw [(isTerminal_yoneda_obj_base B S hS).hom_ext ((isTerminal_yoneda_obj_base B S hS).from X)
    (f ≫ (isTerminal_yoneda_obj_base B S hS).from Y)]
  exact isLocallyQuasiFinite_comp B S hS hX hY (isAlgebraicSpace_yoneda B S hS K) f _
    (isLocallyQuasiFinite_of_mono B S hS hX hY f inferInstance hft) hYk

end AlgebraicGeometry.Space
