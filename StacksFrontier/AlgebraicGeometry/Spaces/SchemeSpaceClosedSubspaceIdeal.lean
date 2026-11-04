module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Closed subspaces of a represented algebraic space are closed subschemes of the scheme

Let `S` be a scheme contained in a big fppf site `B` and let `V` be an object of the big fppf
category over `S`.  This file compares the two sides of the dictionary at a *represented*
algebraic space `h_V = yoneda.obj V`:

* a closed subspace `Z ⊆ h_V` in the sense of Stacks 02YU (2), an element of
  `AlgebraicGeometry.Space.ClosedSubspaces B S hS (yoneda.obj V)`, and
* a sheaf of ideals `I ⊆ 𝒪_V` on the *scheme* underlying `V`, an
  `AlgebraicGeometry.Scheme.IdealSheafData`.

`AlgebraicGeometry.Space.schemeSpaceIdeal` is the forward map, and
`AlgebraicGeometry.Space.schemeSpaceIdealOrderIso` is the resulting inclusion-reversing order
isomorphism.  Before this the dictionary ran one way only: Tag 02YU in the form
`AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map` turned a closed immersion of the site
into a closed subspace, and `AlgebraicGeometry.Space.isRepresentable_of_isClosedSubspace` said
that the subspace is representable, but nothing identified the two *lattices*, nor the ideal
sheaf on the small étale site of `h_V` with the Zariski ideal sheaf of `V`.

## The anchoring, handled once

For a represented closed subspace the underlying presheaf is
`CategoryTheory.Subfunctor.range (yoneda.map j)` for a closed immersion `j : R ⟶ V` of the site,
and **not** `yoneda.obj R`.  The two are isomorphic but not syntactically equal, and the
mismatch is expensive: the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceUnramifiedPairSplitting.lean` record that
re-anchoring a closed subspace under an inverse image of modules makes the kernel unfold the
inverse image to its construction by sheafification and not terminate.

Everything below is therefore phrased on the range, and the mismatch is paid for exactly once,
in `AlgebraicGeometry.Space.exists_closedImmersion_range_eq`: every closed subspace of `h_V`
*is* the range of the yoneda image of a closed immersion of the site, and the witness is the
canonical base change `Z ×_{h_V} h_V ⟶ V` that the relative representability of the inclusion
already supplies.  No appeal to representability of `Z` itself, and so no transport along an
isomorphism of presheaves, is needed; the two statements the library had are not used in either
direction below.

## Main definitions

* `AlgebraicGeometry.Space.schemeSpaceIdeal`: the sheaf of ideals of `𝒪_V` cut out by a closed
  subspace of `h_V`, namely the kernel of pullback of regular functions along the canonical base
  change of the inclusion along the identity chart.
* `AlgebraicGeometry.Space.schemeSpaceIdealOrderIso`: the inclusion-reversing order isomorphism
  between the closed subspaces of `h_V` and the sheaves of ideals of `𝒪_V`.

## Main results

* `AlgebraicGeometry.Space.exists_closedImmersion_range_eq`: the anchoring statement above.
* `AlgebraicGeometry.Space.schemeSpaceIdeal_eq_ker_of_range_eq`: **the comparison.**  If a closed
  subspace of `h_V` is the range of the yoneda image of a closed immersion `j : R ⟶ V` of the
  site, then the sheaf of ideals it cuts out is the kernel of `j`.  This is the form the
  consumers want, because it is the form in which a closed subspace of a represented space is
  given to them.
* `AlgebraicGeometry.Space.comap_schemeSpaceIdeal_eq_idealSheafDataOfChart`: **the ideal sheaf on
  the small étale site of `h_V` is pulled back from the single Zariski ideal sheaf of `V`.**  At
  every étale chart `A` of `h_V`, the sheaf of ideals that the defining ideal sheaf
  `𝓘_Z ⊆ 𝒪_{h_V}` of Stacks 03MB induces on the chart scheme is the inverse image along the
  chart of `AlgebraicGeometry.Space.schemeSpaceIdeal`.  So `𝓘_Z` carries no information beyond
  the Zariski ideal sheaf of `V`, which is what makes the order isomorphism below possible.
* `AlgebraicGeometry.Space.schemeSpaceIdeal_antitone`,
  `AlgebraicGeometry.Space.le_of_schemeSpaceIdeal_le` and
  `AlgebraicGeometry.Space.schemeSpaceIdeal_injective`: the two directions of the
  inclusion-reversal and injectivity.
* `AlgebraicGeometry.Space.exists_schemeSpaceIdeal_eq`: surjectivity — every sheaf of ideals of
  `𝒪_V` is cut out by a closed subspace of `h_V`.  The closed subscheme it defines is the source
  of a monomorphism into `V`, hence lies in the site by
  `AlgebraicGeometry.exists_mono_bigFppfOver`, the size cutoff being closed under powersets; no
  cardinal hypothesis is needed and none is assumed.
* `AlgebraicGeometry.Space.schemeSpaceIdeal_eq_comap_of_preimage_eq`: the correspondence is
  compatible with base change along a morphism of the site, in the form that takes the inverse
  image as an equation on the underlying subfunctor and so applies to every spelling of it.
* `AlgebraicGeometry.Space.idealSheafDataOfChart_mono`: the sheaf of ideals a sheaf of ideals of
  `𝒪_X` induces on an étale chart is monotone in it.

## What this file does not do, and why it carries no `@[stacks]` attribute

Stacks 03MB is the inclusion-reversing bijection between the closed subspaces of an algebraic
space `X` and the **quasi-coherent sheaves of ideals of `𝒪_X` on the small étale site of `X`**.
The right-hand side here is different: it is the sheaves of ideals of the *scheme* `V`.  For a
represented algebraic space the two right-hand sides do correspond, but identifying them is
Descent, Proposition 03DX (2) — that a quasi-coherent module on the small étale site is
cartesian on affine charts — which this tree does not have; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealQuasicoherent.lean`, where the residue
of 03MB is isolated as the hypothesis `hsurj`.  So nothing below is an instance of 03MB, and no
declaration here claims it.  What is proved is the scheme-side correspondence, which needs
neither quasi-coherence on the site nor 03DX (2):
`AlgebraicGeometry.Space.comap_schemeSpaceIdeal_eq_idealSheafDataOfChart` goes through
`AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`, whose only input is the
*unconditional* `AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts`.

Neither is the module-level comparison
`(definingIdealSheaf …).toSheafOfModules ≅ (representedAssociatedModule …).obj (…)` proved here.
That statement needs the associated-module functor of Stacks 03DU (4) to be computed on the
sections of a sheaf of ideals, which is
`AlgebraicGeometry.SmallEtale.associatedModuleObjIsoSections` composed with the identification of
`ε^*(𝒪_V ⟶ j_*𝒪_R)` with `𝒪_{h_V} ⟶ i_*𝒪_{h_R}`; the first is available (an ideal sheaf is
quasi-coherent, `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_isQuasicoherent`) and the
second is not.  What is proved here is that comparison read on *ideal sheaves of the chart
schemes* instead of on modules, which is the reading the consumers of the comparison use and the
one that avoids the direct image altogether.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU), closed subspaces.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the correspondence on
  the small étale site, which this file does *not* prove.
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B), the ideal sheaf of a
  closed subspace.
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX), the comparison of
  quasi-coherence on the two sites, which is what separates this file from 03MB.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart ideal sheaf is monotone in the sheaf of ideals -/

/-- **The ideal of sections over a Zariski open of an étale chart is monotone in the sheaf of
ideals.**  Both sides are the image under the same ring map of the sections over the étale chart
cut out by the open. -/
theorem openChartIdeal_mono (X : AlgebraicSpaces B S hS)
    (N₁ N₂ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) (h : N₁ ≤ N₂)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    openChartIdeal B S hS X N₁ A W ≤ openChartIdeal B S hS X N₂ A W :=
  Ideal.map_mono (h (op (openChart B S hS X.1 A W)))

/-- **The sheaf of ideals that a sheaf of ideals of `𝒪_X` induces on an étale chart is monotone
in it.**  Over an affine open of the chart the induced ideal is
`AlgebraicGeometry.Space.openChartIdeal`, which is monotone. -/
theorem idealSheafDataOfChart_mono (X : AlgebraicSpaces B S hS)
    (N₁ N₂ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN₁ : IsCartesianOnAffineCharts N₁.toSheafOfModules)
    (hN₂ : IsCartesianOnAffineCharts N₂.toSheafOfModules) (h : N₁ ≤ N₂)
    (A : SmallEtale B S hS X.1) :
    idealSheafDataOfChart B S hS X N₁ hN₁ A ≤ idealSheafDataOfChart B S hS X N₂ hN₂ A :=
  Scheme.IdealSheafData.le_def.2 fun W => openChartIdeal_mono B S hS X N₁ N₂ h A W.1

/-! ### The sheaf of ideals of a closed subspace of a represented algebraic space -/

variable (V : BigFppfOver B S hS)

/-- **The sheaf of ideals of `𝒪_V` cut out by a closed subspace of the algebraic space
represented by `V`.**  The inclusion of a closed subspace is relatively representable, so its
base change along the identity chart of `h_V` is a closed immersion of schemes; this is the
kernel of pullback of regular functions along it. -/
noncomputable def schemeSpaceIdeal (Z : ClosedSubspaces B S hS (yoneda.obj V)) :
    ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData :=
  chartKer B S hS (schemeSpace V) Z (𝟙 (yoneda.obj V))

/-- The sheaf of ideals of a closed subspace of `h_V` is the kernel of the canonical base change
of its inclusion along the identity chart. -/
theorem schemeSpaceIdeal_eq_ker (Z : ClosedSubspaces B S hS (yoneda.obj V)) :
    schemeSpaceIdeal B S hS V Z =
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (𝟙 (yoneda.obj V)))).ker :=
  rfl

/-- **The canonical base change of a closed subspace of `h_V` along the identity chart sweeps out
the subspace itself.**  The range of the yoneda image of a base change is the inverse image of
the subspace, and along the identity the inverse image is the subspace. -/
theorem range_yoneda_map_rep_snd_id (Z : ClosedSubspaces B S hS (yoneda.obj V)) :
    Subfunctor.range (yoneda.map (Z.2.2.rep.snd (𝟙 (yoneda.obj V)))) = Z.1 :=
  (preimage_eq_range_rep_snd B S hS (schemeSpace V) Z V (𝟙 (yoneda.obj V))).symm.trans
    (Subfunctor.preimage_id Z.1)

/-- **Every closed subspace of a represented algebraic space is the range of the yoneda image of
a closed immersion of the site.**  This is the anchoring statement of this file: a consumer which
has a closed subspace `Z ⊆ h_V` in hand may replace it by a closed immersion `j : R ⟶ V` of the
site together with the equation `range (yoneda.map j) = Z.1`, and the sheaf of ideals that `Z`
cuts out is then the kernel of `j`.

The witness is the canonical base change of the inclusion along the identity chart, which the
relative representability contained in `AlgebraicGeometry.Space.IsClosedSubspace` already
supplies; so the statement needs neither representability of the presheaf `Z.1.toFunctor` nor any
transport along an isomorphism of presheaves. -/
theorem exists_closedImmersion_range_eq (Z : ClosedSubspaces B S hS (yoneda.obj V)) :
    ∃ (R : BigFppfOver B S hS) (j : R ⟶ V),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
        Subfunctor.range (yoneda.map j) = Z.1 ∧
        ((BigFppfOver.toScheme B S hS).map j).ker = schemeSpaceIdeal B S hS V Z :=
  ⟨Z.2.2.rep.pullback (𝟙 (yoneda.obj V)), Z.2.2.rep.snd (𝟙 (yoneda.obj V)),
    Z.2.2.property_snd _, range_yoneda_map_rep_snd_id B S hS V Z, rfl⟩

/-- **The comparison.**  If a closed subspace of the algebraic space represented by `V` is the
range of the yoneda image of a closed immersion `j : R ⟶ V` of the site, then the sheaf of ideals
of `𝒪_V` it cuts out is the kernel of pullback of regular functions along `j`.

Together with `AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map`, which turns such a `j`
into a closed subspace, and `AlgebraicGeometry.Space.exists_closedImmersion_range_eq`, which
produces such a `j` from an arbitrary closed subspace, this is the whole dictionary between the
closed subspaces of `h_V` and the closed subschemes of `V`. -/
theorem schemeSpaceIdeal_eq_ker_of_range_eq (Z : ClosedSubspaces B S hS (yoneda.obj V))
    {R : BigFppfOver B S hS} (j : R ⟶ V)
    [_root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hj : Subfunctor.range (yoneda.map j) = Z.1) :
    schemeSpaceIdeal B S hS V Z = ((BigFppfOver.toScheme B S hS).map j).ker :=
  ker_rep_snd_eq_ker_of_range_eq B S hS (schemeSpace V) Z V R (𝟙 (yoneda.obj V)) j
    ((Subfunctor.preimage_id Z.1).trans hj.symm)

/-- **The sheaf of ideals of a closed subspace of `h_V` is the sheaf of ideals that its defining
ideal sheaf induces on the identity chart.**  The identity chart
`AlgebraicGeometry.Space.selfChart` of `h_V` has the scheme underlying `V` as its chart scheme,
and its structure morphism is the identity, so the two sides are the two readings of the same
ideal sheaf. -/
theorem schemeSpaceIdeal_eq_idealSheafDataOfChart (Z : ClosedSubspaces B S hS (yoneda.obj V)) :
    schemeSpaceIdeal B S hS V Z =
      idealSheafDataOfChart B S hS (schemeSpace V) (definingIdealSheaf B S hS (schemeSpace V) Z)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS (schemeSpace V) Z)
        (selfChart B S hS V) :=
  ker_rep_snd_eq_idealSheafDataOfChart B S hS (schemeSpace V) Z (selfChart B S hS V)

/-- The inverse image along a chart of the sheaf of ideals of `𝒪_V` cut out by a closed subspace is
the kernel of the canonical base change along that chart. -/
private theorem comap_schemeSpaceIdeal_eq_ker_rep_snd (Z : ClosedSubspaces B S hS (yoneda.obj V))
    (A : SmallEtale B S hS (yoneda.obj V)) :
    (schemeSpaceIdeal B S hS V Z).comap
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage A.1.hom)) =
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker :=
  comap_chartKer B S hS (schemeSpace V) Z (𝟙 (yoneda.obj V)) (yoneda.preimage A.1.hom) A.1.hom
    ((Category.comp_id _).trans (yoneda.map_preimage A.1.hom))

/-- **The ideal sheaf of a closed subspace of `h_V` on the small étale site is pulled back from
the single Zariski ideal sheaf of `V`.**  At every étale chart `A` of `h_V`, the sheaf of ideals
that the defining ideal sheaf `𝓘_Z ⊆ 𝒪_{h_V}` of Stacks 083B induces on the chart scheme is the
inverse image along the chart of `AlgebraicGeometry.Space.schemeSpaceIdeal`.

This is the comparison of the ideal sheaf on the small étale site with the Zariski ideal sheaf,
read on the ideal sheaves of the chart schemes: `𝓘_Z` is determined chartwise by one sheaf of
ideals on `V`.  The morphism of charts is written as the yoneda preimage of the structure
morphism of `A`, which is the only morphism of the site whose yoneda image is that structure
morphism. -/
theorem comap_schemeSpaceIdeal_eq_idealSheafDataOfChart
    (Z : ClosedSubspaces B S hS (yoneda.obj V)) (A : SmallEtale B S hS (yoneda.obj V)) :
    (schemeSpaceIdeal B S hS V Z).comap
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage A.1.hom)) =
      idealSheafDataOfChart B S hS (schemeSpace V) (definingIdealSheaf B S hS (schemeSpace V) Z)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS (schemeSpace V) Z) A :=
  (comap_schemeSpaceIdeal_eq_ker_rep_snd B S hS V Z A).trans
    (ker_rep_snd_eq_idealSheafDataOfChart B S hS (schemeSpace V) Z A)

/-- The sheaf of ideals of a closed subspace of `h_V` at an étale chart, in the orientation in
which `AlgebraicGeometry.Space.le_of_forall_ker_le` asks for it: the kernel of the canonical base
change along the chart is the inverse image along the chart of the sheaf of ideals of `𝒪_V`. -/
theorem ker_rep_snd_eq_comap_schemeSpaceIdeal (Z : ClosedSubspaces B S hS (yoneda.obj V))
    (A : SmallEtale B S hS (yoneda.obj V)) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker =
      (schemeSpaceIdeal B S hS V Z).comap
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage A.1.hom)) :=
  (comap_schemeSpaceIdeal_eq_ker_rep_snd B S hS V Z A).symm

/-- **The correspondence is compatible with base change.**  If a closed subspace `Z' ⊆ h_{V'}`
has as its underlying presheaf the inverse image of a closed subspace `Z ⊆ h_V` along a morphism
`g : V' ⟶ V` of the site, then the sheaf of ideals it cuts out on `V'` is the inverse image along
`g` of the one `Z` cuts out on `V`.

The inverse image is taken as a hypothesis on the underlying *subfunctor* rather than as a
spelling of the subspace, so that the statement applies to any of the spellings of the inverse
image that the library carries -- `AlgebraicGeometry.Space.preimageSubspace`,
`AlgebraicGeometry.Space.preimageClosedSubspace`, or the anonymous constructor -- a closed
subspace being determined by its subfunctor. -/
theorem schemeSpaceIdeal_eq_comap_of_preimage_eq {V' : BigFppfOver B S hS} (g : V' ⟶ V)
    (Z : ClosedSubspaces B S hS (yoneda.obj V)) (Z' : ClosedSubspaces B S hS (yoneda.obj V'))
    (hZ' : Z'.1 = Z.1.preimage (yoneda.map g)) :
    schemeSpaceIdeal B S hS V' Z' =
      (schemeSpaceIdeal B S hS V Z).comap ((BigFppfOver.toScheme B S hS).map g) := by
  have he : Z' = preimageClosedSubspace (schemeSpaceMap g) Z := Subtype.ext hZ'
  rw [he]
  exact chartKer_preimage B S hS (schemeSpaceMap g) Z (selfChart B S hS V') (𝟙 (yoneda.obj V)) g
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-! ### The correspondence reverses inclusions and is bijective -/

/-- **The correspondence reverses inclusions.**  A smaller closed subspace of `h_V` cuts out a
larger sheaf of ideals of `𝒪_V`. -/
theorem schemeSpaceIdeal_antitone (Z W : ClosedSubspaces B S hS (yoneda.obj V))
    (hZW : Z.1 ≤ W.1) : schemeSpaceIdeal B S hS V W ≤ schemeSpaceIdeal B S hS V Z := by
  rw [schemeSpaceIdeal_eq_idealSheafDataOfChart, schemeSpaceIdeal_eq_idealSheafDataOfChart]
  exact idealSheafDataOfChart_mono B S hS (schemeSpace V) _ _ _ _
    (definingIdealSheaf_antitone B S hS (schemeSpace V) Z W hZW) (selfChart B S hS V)

/-- **The correspondence reverses inclusions in the other direction.**  An inclusion of the
sheaves of ideals comes from the reverse inclusion of closed subspaces.

The chartwise criterion `AlgebraicGeometry.Space.le_of_forall_ker_le` applies at every étale
chart because the chart kernels are inverse images of the two sheaves of ideals on `V`, by
`AlgebraicGeometry.Space.ker_rep_snd_eq_comap_schemeSpaceIdeal`, and inverse image of sheaves of
ideals is monotone. -/
theorem le_of_schemeSpaceIdeal_le (Z W : ClosedSubspaces B S hS (yoneda.obj V))
    (h : schemeSpaceIdeal B S hS V W ≤ schemeSpaceIdeal B S hS V Z) : Z.1 ≤ W.1 := by
  refine le_of_forall_ker_le B S hS (schemeSpace V) Z W fun A => ?_
  exact (ker_rep_snd_eq_comap_schemeSpaceIdeal B S hS V W A).trans_le
    ((Scheme.IdealSheafData.comap_mono _ h).trans
      (ker_rep_snd_eq_comap_schemeSpaceIdeal B S hS V Z A).ge)

/-- **Distinct closed subspaces of `h_V` cut out distinct sheaves of ideals of `𝒪_V`.** -/
theorem schemeSpaceIdeal_injective :
    Function.Injective (schemeSpaceIdeal B S hS V) := fun Z W hZW =>
  Subtype.ext (le_antisymm
    (le_of_schemeSpaceIdeal_le B S hS V Z W hZW.ge)
    (le_of_schemeSpaceIdeal_le B S hS V W Z hZW.le))

/-- **Every sheaf of ideals of `𝒪_V` is cut out by a closed subspace of `h_V`.**

The closed subscheme `V(I) ⊆ V` is the source of a monomorphism into an object of the site, so it
is itself an object of the site by `AlgebraicGeometry.exists_mono_bigFppfOver` — the size cutoff
of a big fppf site is a strong prelimit, hence closed under the powerset bound a monomorphism
costs, and no cardinal hypothesis is needed.  Its range is a closed subspace by
`AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map`, and the sheaf of ideals it cuts out
is the kernel of the closed immersion presenting it, which is `I`. -/
theorem exists_schemeSpaceIdeal_eq (I : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData) :
    ∃ Z : ClosedSubspaces B S hS (yoneda.obj V), schemeSpaceIdeal B S hS V Z = I := by
  obtain ⟨R, j, ε, hε⟩ := exists_mono_bigFppfOver V I.subschemeι inferInstance
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j) := by
    rw [← hε]
    infer_instance
  have hker : ((BigFppfOver.toScheme B S hS).map j).ker = I := by
    rw [← hε, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
  exact ⟨⟨Subfunctor.range (yoneda.map j), isClosedSubspace_range_yoneda_map B S hS j hci⟩,
    (schemeSpaceIdeal_eq_ker_of_range_eq B S hS V _ j rfl).trans hker⟩

/-- **The closed subspaces of a represented algebraic space are the sheaves of ideals of the
representing scheme**, inclusion-reversingly: sending a closed subspace `Z ⊆ h_V` to the kernel
of the canonical base change of its inclusion is an order isomorphism onto the order dual of the
sheaves of ideals of `𝒪_V`.

Both halves of the bijection are unconditional:
`AlgebraicGeometry.Space.schemeSpaceIdeal_injective` recovers the subspace from the sheaf of
ideals, and `AlgebraicGeometry.Space.exists_schemeSpaceIdeal_eq` realizes every sheaf of ideals.
The formula pinning the isomorphism down to the canonical rule is
`AlgebraicGeometry.Space.schemeSpaceIdeal_eq_ker_of_range_eq`.

This is *not* Stacks 03MB: the right-hand side there is the quasi-coherent sheaves of ideals on
the small étale site of `h_V`, and identifying it with the right-hand side here is Descent,
Proposition 03DX (2).  See the section "What this file does not do" of this file. -/
noncomputable def schemeSpaceIdealOrderIso :
    ClosedSubspaces B S hS (yoneda.obj V) ≃o
      (((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)ᵒᵈ where
  toFun Z := OrderDual.toDual (schemeSpaceIdeal B S hS V Z)
  invFun I := (exists_schemeSpaceIdeal_eq B S hS V (OrderDual.ofDual I)).choose
  left_inv Z := schemeSpaceIdeal_injective B S hS V
    (exists_schemeSpaceIdeal_eq B S hS V (schemeSpaceIdeal B S hS V Z)).choose_spec
  right_inv I := congrArg OrderDual.toDual
    (exists_schemeSpaceIdeal_eq B S hS V (OrderDual.ofDual I)).choose_spec
  map_rel_iff' {Z W} :=
    ⟨fun hle => Subtype.coe_le_coe.1 (le_of_schemeSpaceIdeal_le B S hS V Z W hle),
      fun hle => schemeSpaceIdeal_antitone B S hS V Z W (Subtype.coe_le_coe.2 hle)⟩

/-- The order isomorphism sends a closed subspace to the sheaf of ideals it cuts out. -/
theorem schemeSpaceIdealOrderIso_apply (Z : ClosedSubspaces B S hS (yoneda.obj V)) :
    schemeSpaceIdealOrderIso B S hS V Z = OrderDual.toDual (schemeSpaceIdeal B S hS V Z) :=
  rfl

end AlgebraicGeometry.Space

end
