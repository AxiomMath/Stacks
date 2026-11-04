module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# The defining ideal sheaf of a closed subspace is the ideal sheaf of its base changed immersion

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `Z ⊆ X` be a closed
subspace and let `A` be an étale scheme chart of `X`.  Two ideal sheaves are attached to `Z` over
the scheme `chartScheme A`, and this file identifies them *as sheaves of modules*:

* the base change `j : Z ×_X A ⟶ chartScheme A` of the inclusion of `Z` is a closed immersion of
  schemes, so it has the ideal sheaf `Stacks.ClosedImmersion.idealSheaf j` of
  [Stacks, Tag 01C2] — a sheaf of `𝒪`-modules on the Zariski site of `chartScheme A`, defined as
  the categorical kernel of `𝒪 ⟶ j_*𝒪`;
* the defining ideal sheaf `𝓘_Z ⊆ 𝒪_X` of [Stacks, Tag 03MB] lives on the small étale site of
  `X`, and `AlgebraicGeometry.Space.openChartIdeal` reads its sections over the étale chart cut
  out by a Zariski open `V` of `chartScheme A` as an ideal of `Γ(chartScheme A, V)`.

What the tree already had is the comparison of the two as `AlgebraicGeometry.Scheme.IdealSheafData`
on the chart scheme: `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart` says that
`j.ker` is `AlgebraicGeometry.Space.idealSheafDataOfChart` of `𝓘_Z`.  An `IdealSheafData` is a
family of ideals indexed by the *affine* opens, not a sheaf of modules, so nothing followed from
it about `Stacks.ClosedImmersion.idealSheaf`, which is the form in which the scheme-level conormal
sheaf of [Stacks, Tag 01R3] is built.  That step is what this file supplies.

## Main definitions

* `AlgebraicGeometry.Space.chartIdealSheafIso`: **the identification, as sheaves of modules.**
  `Stacks.ClosedImmersion.idealSheaf j` is isomorphic to the ideal sheaf of the closed subscheme
  of `chartScheme A` cut out by `AlgebraicGeometry.Space.idealSheafDataOfChart` of `𝓘_Z`.
* `AlgebraicGeometry.Space.chartIdealSheafSectionsIso`: the same identification read on sections.
  Over an affine open `V` of the chart scheme, the sections of
  `Stacks.ClosedImmersion.idealSheaf j` are the ideal `AlgebraicGeometry.Space.openChartIdeal` of
  sections of `𝓘_Z` over the étale chart cut out by `V`, as modules over `Γ(chartScheme A, V)`.
* `AlgebraicGeometry.Space.representedIdealSheafIso` and
  `AlgebraicGeometry.Space.representedIdealSheafSectionsIso`: the two at the identity chart of a
  representable algebraic space, which is the case the comparison with the scheme-level conormal
  sheaf needs: there `A` is `AlgebraicGeometry.Space.selfChart`, the chart scheme is the
  representing scheme, and `j` is the closed immersion of schemes corresponding to `Z`.
* `Stacks.Conormal.idealSheafIsoImageι`: the scheme-level step which makes the module-level
  statement possible — the ideal sheaf of a closed immersion is the ideal sheaf of the inclusion
  of its scheme-theoretic image, the comparison morphism to the image being an isomorphism.

## Main results

* `AlgebraicGeometry.Space.ker_appTop_chartBaseChangeHom`: on global functions the kernel of the
  base changed closed immersion is `AlgebraicGeometry.Space.definingIdealAt`, the sections of
  `𝓘_Z` over the chart.  This needs no affineness hypothesis on the chart, unlike
  `AlgebraicGeometry.Space.ker_chartBaseChangeHom`, which compares the whole ideal sheaves.
* `AlgebraicGeometry.Space.ker_app_chartBaseChangeHom`: over an affine open of the chart scheme
  the kernel of the base changed closed immersion on functions is
  `AlgebraicGeometry.Space.openChartIdeal`.
* `AlgebraicGeometry.Space.mem_openChartIdeal_iff`: the same read as a membership criterion — a
  regular function on an affine open of the chart lies in the sections of `𝓘_Z` exactly when the
  base changed closed immersion kills it.
* `AlgebraicGeometry.Space.ker_app_representedClosedImmersion` and
  `AlgebraicGeometry.Space.ker_appTop_representedClosedImmersion`: the two kernel computations at
  the identity chart of a representable algebraic space.

## Implementation notes

The affine-open statement is the `IdealSheafData` comparison read through Mathlib's
`AlgebraicGeometry.Scheme.Hom.ker_apply`, which computes the ideal of `j.ker` over an affine open
as the kernel of `j` on functions there.  That lemma asks for `AlgebraicGeometry.QuasiCompact j`,
which a closed immersion satisfies, the instance being found from
`AlgebraicGeometry.Space.isClosedImmersion_chartBaseChangeHom` through `IsAffineHom`.

The global-sections statement is not an instance of the affine-open one: `⊤` need not be an affine
open of the chart scheme.  It is instead `AlgebraicGeometry.Space.definingIdealAt_eq_ker`, whose
right-hand side is the kernel of `AlgebraicGeometry.Scheme.Γ` of the base change, rewritten by
`AlgebraicGeometry.Scheme.Γ_map_op` into the kernel on global sections.  Applied at the chart cut
out by a Zariski open `V` of the chart scheme it computes the sections of `𝓘_Z` over that chart
with no affineness; what an arbitrary `V` lacks, and an affine one has, is the comparison of the
base change of `Z` along `V ⟶ A ⟶ X` with the restriction of `j` over `V`, which is why the
sections isomorphism below is stated over the affine opens.

The passage from the ideal of sections to the sheaf of modules is
`Stacks.Conormal.idealSheafSectionsIso`, which computes the sections of
`Stacks.ClosedImmersion.idealSheaf` over an arbitrary open as the kernel of the map on functions;
no quasi-coherence and no affineness enter there.

The module-level statement does not go through sections at all, and so is not limited to the
affine opens.  Two closed immersions with the same `AlgebraicGeometry.Scheme.Hom.ker` factor
through one another by an isomorphism of sources, because a closed immersion is an isomorphism
onto its scheme-theoretic image; and the ideal sheaf is insensitive to an isomorphism of the
source, by `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource`.  So the
equality of `AlgebraicGeometry.Scheme.IdealSheafData` upgrades to an isomorphism of
modules with nothing further to prove.

## What is not proved here

This is *not* an isomorphism between `Stacks.ClosedImmersion.idealSheaf j` and the module `𝓘_Z`
itself.  The right-hand side of `AlgebraicGeometry.Space.chartIdealSheafIso` is the ideal sheaf
of the *Zariski* sheaf of ideals that `𝓘_Z` induces on the chart scheme, whereas `𝓘_Z` lives on
the small étale site of `X`; crossing between the two is the comparison of [Stacks, Tag 03DU] (4)
at `τ = étale`, `AlgebraicGeometry.SmallEtale.associatedModule`, transported to a represented
algebraic space as `AlgebraicGeometry.Space.representedAssociatedModule`.  Identifying `𝓘_Z` with
the associated module of the ideal sheaf above would need the two read over *every* object of the
small étale site of the chart, and nothing here does that: the chartwise ideal sheaf is pinned
only over the affine opens of the chart scheme, which is the granularity at which an
`AlgebraicGeometry.Scheme.IdealSheafData` determines a quasi-coherent sheaf of ideals.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Conormal

/-- **The ideal sheaf of a closed immersion is the ideal sheaf of its scheme-theoretic image.**
For a closed immersion of schemes `j : W ⟶ T` the morphism `j.toImage : W ⟶ j.image` to the
closed subscheme cut out by `j.ker` is an isomorphism, so transporting the ideal sheaf along it
identifies the ideal sheaf of `j` with the ideal sheaf of
`AlgebraicGeometry.Scheme.Hom.imageι`, the inclusion of that closed subscheme.

This is the isomorphism which turns an equality of `AlgebraicGeometry.Scheme.IdealSheafData` —
a family of ideals indexed by the affine opens — into an isomorphism of the corresponding
sheaves of modules. -/
noncomputable def idealSheafIsoImageι {W T : AlgebraicGeometry.Scheme.{u}} (j : W ⟶ T)
    [_root_.AlgebraicGeometry.IsClosedImmersion j] :
    Stacks.ClosedImmersion.idealSheaf j.toLRSHom.toShHom ≅
      Stacks.ClosedImmersion.idealSheaf j.imageι.toLRSHom.toShHom :=
  Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSourceOfCompEq
    (asIso j.toImage) j.imageι j j.toImage_imageι

end Stacks.Conormal

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The kernel of the base changed closed immersion on functions -/

/-- **On global functions the base changed closed immersion of a closed subspace kills exactly
the defining ideal at the chart.**  For a closed subspace `Z ⊆ X` and an étale scheme chart `A`
of `X`, the kernel of pullback of global regular functions along the closed immersion of schemes
`Z ×_X A ⟶ chartScheme A` is `AlgebraicGeometry.Space.definingIdealAt`, the ideal of sections of
the defining ideal sheaf `𝓘_Z` over `A`.

No affineness is assumed.  The companion
`AlgebraicGeometry.Space.ker_chartBaseChangeHom` compares the whole ideal sheaves and does need
the chart scheme to be affine, an ideal sheaf on an affine scheme being determined by its ideal
of global sections. -/
theorem ker_appTop_chartBaseChangeHom (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS X.1) :
    RingHom.ker (chartBaseChangeHom B S hS X Z A).appTop.hom =
      definingIdealAt B S hS X Z (op A) := by
  have h := definingIdealAt_eq_ker B S hS X Z A
  rw [Scheme.Γ_map_op] at h
  exact h.symm

/-- **Over an affine open of an étale chart the base changed closed immersion kills exactly the
sections of the defining ideal sheaf.**  For a closed subspace `Z ⊆ X`, an étale scheme chart `A`
of `X` and an affine open `V` of the chart scheme, the kernel of the closed immersion
`Z ×_X A ⟶ chartScheme A` on the functions over `V` is
`AlgebraicGeometry.Space.openChartIdeal`, the ideal of sections of `𝓘_Z` over the étale chart cut
out by `V`.

This is `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart` read over `V` through
Mathlib's `AlgebraicGeometry.Scheme.Hom.ker_apply`. -/
theorem ker_app_chartBaseChangeHom (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).affineOpens) :
    RingHom.ker ((chartBaseChangeHom B S hS X Z A).app V.1).hom =
      openChartIdeal B S hS X (definingIdealSheaf B S hS X Z) A V.1 :=
  (Scheme.Hom.ker_apply (chartBaseChangeHom B S hS X Z A) V).symm.trans
    (congrArg (fun J : (chartScheme A).IdealSheafData => J.ideal V)
      (ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z A))

/-- **The sections of the defining ideal sheaf over an affine open of a chart, as a membership
criterion.**  A regular function on an affine open `V` of an étale chart `A` of `X` lies in the
ideal of sections of `𝓘_Z` over the chart cut out by `V` exactly when pullback along the closed
immersion `Z ×_X A ⟶ chartScheme A` kills it. -/
theorem mem_openChartIdeal_iff (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).affineOpens) (y : Γ(chartScheme A, V.1)) :
    y ∈ openChartIdeal B S hS X (definingIdealSheaf B S hS X Z) A V.1 ↔
      ((chartBaseChangeHom B S hS X Z A).app V.1).hom y = 0 := by
  rw [← ker_app_chartBaseChangeHom B S hS X Z A V]
  exact RingHom.mem_ker

/-! ### The identification of the two ideal sheaves on sections -/

/-- **The ideal sheaf of the base changed closed immersion is the defining ideal sheaf, read on
sections over an affine open.**  Over an affine open `V` of the scheme of an étale chart `A` of
`X`, the sections of the ideal sheaf `Stacks.ClosedImmersion.idealSheaf` of the closed immersion
of schemes `Z ×_X A ⟶ chartScheme A` are the ideal `AlgebraicGeometry.Space.openChartIdeal` of
sections of the defining ideal sheaf `𝓘_Z` over the étale chart cut out by `V`, as modules over
`Γ(chartScheme A, V)`.

`Stacks.Conormal.idealSheafSectionsIso` computes the left-hand side as the kernel of the map on
functions, and `AlgebraicGeometry.Space.ker_app_chartBaseChangeHom` identifies that kernel. -/
noncomputable def chartIdealSheafSectionsIso (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).affineOpens) :
    (Stacks.ClosedImmersion.idealSheaf
        (chartBaseChangeHom B S hS X Z A).toLRSHom.toShHom).val.obj (op V.1) ≅
      ModuleCat.of Γ(chartScheme A, V.1)
        (openChartIdeal B S hS X (definingIdealSheaf B S hS X Z) A V.1) :=
  Stacks.Conormal.idealSheafSectionsIso (chartBaseChangeHom B S hS X Z A) V.1 ≪≫
    eqToIso (by rw [ker_app_chartBaseChangeHom B S hS X Z A V])

/-- **The ideal sheaf of the base changed closed immersion of a closed subspace is the ideal
sheaf of the closed subscheme that the defining ideal sheaf cuts out on the chart**, as sheaves
of `𝒪`-modules on the Zariski site of the chart scheme.

The closed immersion of schemes `Z ×_X A ⟶ chartScheme A` and the closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` of the closed subscheme cut out by
`AlgebraicGeometry.Space.idealSheafDataOfChart` of `𝓘_Z` have the same kernel ideal sheaf, by
`AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`, so the first factors through the
second by an isomorphism of sources and the two ideal sheaves agree.

Unlike `AlgebraicGeometry.Space.chartIdealSheafSectionsIso` this is an isomorphism of modules
and not only of the sections over one affine open; what it compares the ideal sheaf of the
immersion with is the Zariski sheaf of ideals that `𝓘_Z` induces on the chart, which carries the
same data as `𝓘_Z` over the affine opens of the chart. -/
noncomputable def chartIdealSheafIso (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS X.1) :
    Stacks.ClosedImmersion.idealSheaf (chartBaseChangeHom B S hS X Z A).toLRSHom.toShHom ≅
      Stacks.ClosedImmersion.idealSheaf
        (idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
            (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z)
            A).subschemeι.toLRSHom.toShHom :=
  Stacks.Conormal.idealSheafIsoImageι (chartBaseChangeHom B S hS X Z A) ≪≫
    eqToIso (congrArg (fun I : (chartScheme A).IdealSheafData =>
        Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom)
      (ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z A))

/-! ### The representable case -/

variable (U : BigFppfOver B S hS)

/-- **On global functions the closed immersion of schemes of a closed subspace of a representable
algebraic space kills exactly the defining ideal.**  This is
`AlgebraicGeometry.Space.ker_appTop_chartBaseChangeHom` at the identity chart
`AlgebraicGeometry.Space.selfChart`, whose scheme is the representing scheme. -/
theorem ker_appTop_representedClosedImmersion
    (Z : ClosedSubspaces B S hS (schemeSpace U).obj) :
    RingHom.ker
        (chartBaseChangeHom B S hS (schemeSpace U) Z (selfChart B S hS U)).appTop.hom =
      definingIdealAt B S hS (schemeSpace U) Z (op (selfChart B S hS U)) :=
  ker_appTop_chartBaseChangeHom B S hS (schemeSpace U) Z (selfChart B S hS U)

/-- **Over an affine open of the representing scheme, the closed immersion of schemes of a closed
subspace of a representable algebraic space kills exactly the sections of the defining ideal
sheaf.**  This is `AlgebraicGeometry.Space.ker_app_chartBaseChangeHom` at the identity chart. -/
theorem ker_app_representedClosedImmersion
    (Z : ClosedSubspaces B S hS (schemeSpace U).obj)
    (V : (chartScheme (selfChart B S hS U)).affineOpens) :
    RingHom.ker
        ((chartBaseChangeHom B S hS (schemeSpace U) Z (selfChart B S hS U)).app V.1).hom =
      openChartIdeal B S hS (schemeSpace U)
        (definingIdealSheaf B S hS (schemeSpace U) Z) (selfChart B S hS U) V.1 :=
  ker_app_chartBaseChangeHom B S hS (schemeSpace U) Z (selfChart B S hS U) V

/-- **The ideal sheaf of the closed immersion of schemes corresponding to a closed subspace of a
representable algebraic space is the defining ideal sheaf, read on sections over an affine
open.**  This is `AlgebraicGeometry.Space.chartIdealSheafSectionsIso` at the identity chart
`AlgebraicGeometry.Space.selfChart` of `yoneda.obj U`, whose scheme is the scheme underlying `U`:
the closed subspace `Z` of the representable algebraic space is cut out of that scheme by a
closed immersion, and the sections of its ideal sheaf over an affine open are the sections of
`𝓘_Z` over the corresponding étale chart. -/
noncomputable def representedIdealSheafSectionsIso
    (Z : ClosedSubspaces B S hS (schemeSpace U).obj)
    (V : (chartScheme (selfChart B S hS U)).affineOpens) :
    (Stacks.ClosedImmersion.idealSheaf (chartBaseChangeHom B S hS (schemeSpace U) Z
        (selfChart B S hS U)).toLRSHom.toShHom).val.obj (op V.1) ≅
      ModuleCat.of Γ(chartScheme (selfChart B S hS U), V.1)
        (openChartIdeal B S hS (schemeSpace U)
          (definingIdealSheaf B S hS (schemeSpace U) Z) (selfChart B S hS U) V.1) :=
  chartIdealSheafSectionsIso B S hS (schemeSpace U) Z (selfChart B S hS U) V

/-- **The ideal sheaf of the closed immersion of schemes corresponding to a closed subspace of a
representable algebraic space is the ideal sheaf of the closed subscheme that the defining ideal
sheaf cuts out on the representing scheme.**  This is
`AlgebraicGeometry.Space.chartIdealSheafIso` at the identity chart
`AlgebraicGeometry.Space.selfChart`, and it is the identification of
`Stacks.ClosedImmersion.idealSheaf` with `AlgebraicGeometry.Space.definingIdealSheaf` in the
representable case, as sheaves of modules on the Zariski site of the representing scheme. -/
noncomputable def representedIdealSheafIso
    (Z : ClosedSubspaces B S hS (schemeSpace U).obj) :
    Stacks.ClosedImmersion.idealSheaf (chartBaseChangeHom B S hS (schemeSpace U) Z
        (selfChart B S hS U)).toLRSHom.toShHom ≅
      Stacks.ClosedImmersion.idealSheaf
        (idealSheafDataOfChart B S hS (schemeSpace U)
            (definingIdealSheaf B S hS (schemeSpace U) Z)
            (definingIdealSheaf_isCartesianOnAffineCharts B S hS (schemeSpace U) Z)
            (selfChart B S hS U)).subschemeι.toLRSHom.toShHom :=
  chartIdealSheafIso B S hS (schemeSpace U) Z (selfChart B S hS U)

end AlgebraicGeometry.Space

end
