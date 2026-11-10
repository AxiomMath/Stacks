module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MonoLocallyQuasiFiniteOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeQuasiDM

/-!
# Residual gerbes of quasi-DM algebraic stacks, with Stacks 06S1 supplied

`StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeQuasiDM` proves that a quasi-DM algebraic
stack
has a residual gerbe at every point (**Stacks 06UI**) from two universally quantified inputs: the
implication (1) ⟹ (2) of **Stacks 06MF** and **Stacks 06S1** in the form
`AlgebraicGeometry.Stack.MonoLocallyQuasiFiniteOverField`. This file proves the second input, so
that the statement left takes the quasi-DM presentation of Stacks 06MF alone.

Stacks 06S1 is in the library as
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono_of_isLocallyQuasiFinite`, for algebraic
spaces over a base scheme `S` which is itself the spectrum of a field. The residual-gerbe argument
applies it over a field object `Spec k` of the big fppf site of an arbitrary `S`, to algebraic
spaces over `S` with a morphism to `Spec k`. The proof is the same, run with the field object in
place of the final object; it is
`AlgebraicGeometry.Space.isLocallyQuasiFinite_comp_of_mono_to_field`.

## Main results

* `AlgebraicGeometry.Space.isLocallyQuasiFinite_comp_of_mono_to_field`: **Stacks 06S1** over a
  field object of the site.
* `AlgebraicGeometry.Stack.monoLocallyQuasiFiniteOverField`: the input
  `AlgebraicGeometry.Stack.MonoLocallyQuasiFiniteOverField`, proved.
* `Stack.exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM_of_hasQuasiDMPresentation`: the residual
  gerbe of a quasi-DM algebraic stack exists at every point, given the implication (1) ⟹ (2) of
  Stacks 06MF. It is not registered against Stacks 06UI.

## References

* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06S1](https://stacks.math.columbia.edu/tag/06S1)
* [Stacks Project, Tag 06UI](https://stacks.math.columbia.edu/tag/06UI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Stacks 06S1 over a field object of the site.** Let `K` be an object of the big fppf site of
`S` whose underlying scheme is the spectrum of a field, let `f : X ⟶ Y` be a monomorphism of
algebraic spaces over `S` and let `q : Y ⟶ K` be locally quasi-finite. Then `f ≫ q` is locally
quasi-finite.

This is the proof of `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono_of_isLocallyQuasiFinite`
with `K` in place of the final object: `Y` is a locally Artinian scheme, `X` is a scheme because
its space of points is discrete and it is reasonable, `f` is locally of finite type as a
monomorphism into a locally Artinian scheme, hence locally quasi-finite (**Stacks 0463**), and the
composite is locally quasi-finite (**Stacks 03XK**). -/
theorem isLocallyQuasiFinite_comp_of_mono_to_field {k : Type u} [Field k]
    {K : BigFppfOver B S hS} (eK : (BigFppfOver.toScheme B S hS).obj K ≅ Spec (.of k))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) [Mono f]
    (q : Y ⟶ yoneda.obj K) (hq : IsLocallyQuasiFinite B S hS q) :
    IsLocallyQuasiFinite B S hS (f ≫ q) := by
  have hZ := BigFppfSite.contains_terminal B
  let T := BigFppfOver.toScheme B S hS
  have hK : Subsingleton (T.obj K) :=
    ⟨fun _ _ ↦ eK.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  -- `Y` is a scheme whose underlying scheme is locally Artinian
  have : Y.IsRepresentable := isRepresentable_of_isLocallyQuasiFinite_to_field B S hS eK hY q hq
  let gY : Y.reprX ⟶ K := yoneda.preimage (Y.reprW.hom ≫ q)
  have : LocallyQuasiFinite (T.map gY) :=
    (prop_toScheme_map_of_holdsOnEveryEtaleChart B S hS hq Y.reprW.hom
      (presheaf_etale_of_iso B S hS Y.reprW) (t := gY) (yoneda.map_preimage _)).2
  have : IsLocallyArtinian (T.obj Y.reprX) := .of_locallyQuasiFinite (T.map gY ≫ eK.hom)
  -- `X` is a scheme: its point space is discrete and it is reasonable
  have := discreteTopology_points_of_isLocallyQuasiFinite B S hS hY hK q hq
  have hdiscX : DiscreteTopology (points B S hS X) :=
    DiscreteTopology.of_continuous_injective (continuous_pointsMap B S hS f)
      (pointsMap_injective_of_mono B S hS f)
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS Y hZ
      ⟨Y.reprX, inferInstance, ⟨Y.representableBy⟩⟩
  have hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX hYqs
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
    have : Mono X.reprW.hom := IsIso.mono_of_iso _
    have : Mono Y.reprW.inv := IsIso.mono_of_iso _
    exact mono_comp _ (f ≫ Y.reprW.inv))
  have hft : IsLocallyOfFiniteType B S hS f :=
    (holdsOnEveryEtaleChart_iff_representable B S hS _
      isEtaleLocalOnSourceAndTarget_locallyOfFiniteType f).2
      (locallyOfFiniteType_of_mono_of_isLocallyArtinian (T.map p))
  exact isLocallyQuasiFinite_comp B S hS hX hY (isAlgebraicSpace_yoneda B S hS K) f q
    (isLocallyQuasiFinite_of_mono B S hS hX hY f inferInstance hft) hq

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The input `AlgebraicGeometry.Stack.MonoLocallyQuasiFiniteOverField`, proved.** It is
**Stacks 06S1** over the field object of a `AlgebraicGeometry.Stack.FieldSpectrum`,
`AlgebraicGeometry.Space.isLocallyQuasiFinite_comp_of_mono_to_field`. -/
theorem monoLocallyQuasiFiniteOverField : MonoLocallyQuasiFiniteOverField B S hS :=
  fun F _ _ hX hY m _ q hq =>
    Space.isLocallyQuasiFinite_comp_of_mono_to_field B S hS F.isSpec hX hY m q hq

/-- **The residual gerbe of a quasi-DM algebraic stack exists, given the quasi-DM presentation.**
Let `𝒳` be a quasi-DM algebraic stack over `S` and `x ∈ |𝒳|`. Given the implication (1) ⟹ (2) of
**Stacks 06MF** — every quasi-DM algebraic stack over `S` admits a surjective, flat, locally
finitely presented, locally quasi-finite 1-morphism from a scheme of the site — some strictly full
subcategory of `𝒳` is the residual gerbe of `𝒳` at `x` (**Stacks 06MU**), in the sense of the
specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT**.

This is `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM_of` with its
Stacks 06S1 input supplied by `AlgebraicGeometry.Stack.monoLocallyQuasiFiniteOverField`. The
argument `hpresentation` is stated in the shape of the theorem that proves it,
`hasQuasiDMPresentation_of_isAbsolutelyQuasiDM`. -/
theorem exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM_of_hasQuasiDMPresentation
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hpresentation : ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS),
      AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳 → HasQuasiDMPresentation.{u, w} B S hS 𝒳)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ P : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x P :=
  exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM_of B S hS hZ hpresentation
    (monoLocallyQuasiFiniteOverField B S hS) 𝒳 h𝒳 x

end AlgebraicGeometry.Stack

end
