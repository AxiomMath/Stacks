module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Descent
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleChartComparison
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleLocal.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Glueing a sheaf of modules from the affine opens of a scheme

The affine opens of a scheme `X` form a basis of its topology, and they are ordered by inclusion.
This file assembles a sheaf of modules on `X` out of a sheaf of modules on each affine open
together with a comparison isomorphism for each *inclusion* of affine opens, subject to the
cocycle condition for a chain of two inclusions. No comparison over the intersection of two
affine opens is asked for — that intersection need not be affine — because the affine opens are a
*locally directed* covering family: the intersection of two of them is covered by the affine opens
contained in both. That is what `Stacks.SheafOfModules.ModulesDirectedGlueData` consumes.

This is the shape in which the determinant of a two-term perfect complex is glued: over an affine
open the determinant is the one of More on Algebra, Section 0FJI, and the comparison between two
affine opens is the base change along the restriction of functions, which is defined only for an
inclusion.

## Main definitions

* `AlgebraicGeometry.AffineOpensGlue.chart`: the open immersion `V ⟶ X` of an affine open, read as
  the chart morphism of the covering family indexed by `X.affineOpens`.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison`: **the glueing datum**: a sheaf of modules on
  each affine open, a comparison isomorphism of the pushforwards for each inclusion of affine
  opens, and the cocycle condition for a chain of two inclusions.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.toGlueData`,
  `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glued` and
  `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartIso`: the locally directed glueing datum
  it defines, the glued sheaf of modules on `X`, and the identification of its restriction to a
  chart with the member of the family there.

## Main results

* `AlgebraicGeometry.AffineOpensGlue.opensRange_mono` and
  `AlgebraicGeometry.AffineOpensGlue.locallyDirected`: the two structural fields of
  `Stacks.SheafOfModules.ModulesDirectedGlueData` for the family of affine opens.
* `AlgebraicGeometry.AffineOpensGlue.localApp_restrictLocal_le`: **the sections map of a morphism
  of restrictions over an open `O ≤ V ≤ W` is the sections map of its restriction to `V`.** This
  is what lets the comparisons attached to `V ≤ V'` and to `V' ≤ W` be composed over an open
  contained in `V`, and so it is what reduces the cocycle condition to one equation of morphisms.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.isInvertibleModule_glued`: **a module glued
  from invertible modules on the affine opens is invertible.**

## Implementation notes

The covering family is indexed by `AlgebraicGeometry.Scheme.affineOpens`, which is a type in the
universe of the scheme, and the chart of `V` is the inclusion `V.ι` of the open subscheme rather
than `AlgebraicGeometry.IsAffineOpen.fromSpec`. The two have the same range, but `V.ι` composes
strictly with `AlgebraicGeometry.Scheme.homOfLE`, which is what the comparison isomorphisms along
an inclusion are stated against, and `AlgebraicGeometry.restrictLocal` is stated for inclusions of
opens of the base.

The comparison is asked for between the *pushforwards* of the two members to `X`, restricted to
the smaller chart, rather than between a member and the restriction of the other member. These
agree, through the counit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, but the
pushforward form is the one whose sections over an open of `X` are
`Stacks.SheafOfModules.openSections`, so `AlgebraicGeometry.localAppEquiv` applies to it with no
transport.

Invertibility of the glued module is local on `X` by
`Stacks.Modules.isInvertible_of_isInvertible_restrict_isOpenCover`, and
`Stacks.SheafOfModules.ModulesDirectedGlueData.chartIso` identifies the restriction of the glued
module to a chart with the member of the family there.

## References

* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.AffineOpensGlue

variable {X : Scheme.{u}}

/-! ### The affine opens as a locally directed covering family -/

/-- The chart morphism of an affine open of `X`: the inclusion of the open subscheme. -/
abbrev chart (X : Scheme.{u}) (V : X.affineOpens) : ((V.1 : X.Opens) : Scheme.{u}) ⟶ X :=
  (V.1 : X.Opens).ι

/-- The range of the chart of an affine open is that affine open. -/
theorem opensRange_chart (X : Scheme.{u}) (V : X.affineOpens) :
    (chart X V).opensRange = (V.1 : X.Opens) :=
  Scheme.Opens.opensRange_ι _

/-- **The ranges of the charts are monotone in the inclusion of affine opens.** This is the
`opensRange_mono` field of `Stacks.SheafOfModules.ModulesDirectedGlueData` for the family of
affine opens. -/
theorem opensRange_mono {V W : X.affineOpens} (h : V ≤ W) :
    (chart X V).opensRange ≤ (chart X W).opensRange := by
  rw [opensRange_chart, opensRange_chart]
  exact h

/-- An open contained in the range of a chart is contained in the affine open itself. -/
theorem le_of_le_opensRange_chart {V : X.affineOpens} {O : X.Opens}
    (hO : O ≤ (chart X V).opensRange) : O ≤ (V.1 : X.Opens) := by
  rwa [opensRange_chart] at hO

/-- **The affine opens are a locally directed covering family.** The intersection of two affine
opens is covered by the affine opens contained in both, because the affine opens form a basis of
the topology. This is the `locallyDirected` field of
`Stacks.SheafOfModules.ModulesDirectedGlueData` for the family of affine opens. -/
theorem locallyDirected (V W : X.affineOpens) :
    (chart X V).opensRange ⊓ (chart X W).opensRange ≤
      ⨆ k : {k : X.affineOpens // k ≤ V ∧ k ≤ W}, (chart X k.1).opensRange := by
  rw [opensRange_chart, opensRange_chart]
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((V.1 : X.Opens) ⊓ (W.1 : X.Opens) : X.Opens) from hx)
      ((V.1 : X.Opens) ⊓ (W.1 : X.Opens)).2
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, fun y hy => (hUle hy).1,
    fun y hy => (hUle hy).2⟩, ?_⟩
  simpa [opensRange_chart] using hxU

/-- The affine opens of a scheme cover it. -/
theorem isOpenCover_affineOpens (X : Scheme.{u}) :
    IsOpenCover (fun V : X.affineOpens => (V.1 : X.Opens)) := by
  unfold IsOpenCover
  simpa using AlgebraicGeometry.iSup_affineOpens_eq_top X

/-! ### Restricting a morphism of restrictions to a smaller open -/

/-- The image under the inclusion `V ⟶ W` of the preimage in `V` of an open `O ≤ V` is the
preimage of `O` in `W`. -/
theorem homOfLE_image_preimage {O V W : X.Opens} (hVW : V ≤ W) (hOV : O ≤ V) :
    X.homOfLE hVW ''ᵁ (V.ι ⁻¹ᵁ O) = W.ι ⁻¹ᵁ O := by
  have h1 : V.ι ⁻¹ᵁ O = X.homOfLE hVW ⁻¹ᵁ (W.ι ⁻¹ᵁ O) := by
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
  rw [h1, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.opensRange_homOfLE]
  refine le_antisymm inf_le_right ?_
  intro x hx
  exact ⟨hOV hx, hx⟩

/-- **The sections map over an open `O ≤ V` of a morphism of the restrictions to `W` is the
sections map of its restriction to `V`.** `AlgebraicGeometry.localApp_restrictLocal` is the case
`O = V`; this is the form in which two comparisons attached to `V ≤ V'` and `V' ≤ W` can be
composed over an open contained in `V`. -/
theorem localApp_restrictLocal_le {A B : X.Modules} {O V W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (hVW : V ≤ W) (hOV : O ≤ V) :
    localApp φ O (hOV.trans hVW) = localApp (restrictLocal φ hVW) O hOV := by
  have himg : W.ι ''ᵁ (X.homOfLE hVW ''ᵁ (V.ι ⁻¹ᵁ O)) = V.ι ''ᵁ (V.ι ⁻¹ᵁ O) := by
    rw [← Scheme.Hom.comp_image]
    simp only [Scheme.homOfLE_ι]
  rw [localApp, localApp,
    restrictLocal_app φ hVW (V.ι ⁻¹ᵁ O) (eqToHom himg).op (eqToHom himg.symm).op]
  have hU : W.ι ⁻¹ᵁ O = X.homOfLE hVW ''ᵁ (V.ι ⁻¹ᵁ O) := (homOfLE_image_preimage hVW hOV).symm
  exact (conj_app_eq₃ φ (homOfLE (le_of_eq hU)) _ _ _ _ _ _).symm

/-- `AlgebraicGeometry.AffineOpensGlue.localApp_restrictLocal_le`, read on an individual
section. -/
theorem localAppFun_restrictLocal_le {A B : X.Modules} {O V W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (hVW : V ≤ W) (hOV : O ≤ V) (s : ToType (A.val.obj (op O))) :
    localAppFun φ O (hOV.trans hVW) s = localAppFun (restrictLocal φ hVW) O hOV s :=
  congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _))
    (localApp_restrictLocal_le φ hVW hOV)) s

/-! ### The glueing datum -/

/-- **A glueing datum of sheaves of modules on the affine opens of a scheme.** A sheaf of modules
on each affine open, a comparison isomorphism of the pushforwards for each inclusion of affine
opens — restricted to the smaller one, where both are defined — and the cocycle condition for a
chain of two inclusions.

The intersection of two affine opens carries no comparison; it does not have to, because the
affine opens are a locally directed covering family by
`AlgebraicGeometry.AffineOpensGlue.locallyDirected`. -/
structure ChartComparison (X : Scheme.{u}) where
  /-- The sheaf of modules on an affine open. -/
  mod : ∀ V : X.affineOpens, ((V.1 : X.Opens) : Scheme.{u}).Modules
  /-- The comparison attached to an inclusion of affine opens. -/
  comp : ∀ {V W : X.affineOpens} (_h : V ≤ W),
    Scheme.Modules.restrict ((Scheme.Modules.pushforward (chart X V)).obj (mod V))
        (V.1 : X.Opens).ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward (chart X W)).obj (mod W))
        (V.1 : X.Opens).ι
  /-- The comparisons compose along a chain of two inclusions. -/
  comp_trans : ∀ {V V' W : X.affineOpens} (h : V ≤ V') (h' : V' ≤ W),
    (comp h).hom ≫ restrictLocal (comp h').hom (show (V.1 : X.Opens) ≤ (V'.1 : X.Opens) from h) =
      (comp (h.trans h')).hom

namespace ChartComparison

variable (D : ChartComparison X)

/-- **The locally directed glueing datum of a chart comparison.** The transition over an open
contained in the smaller chart is the sections map of the comparison; it commutes with restriction
of sections by `AlgebraicGeometry.localAppFun_naturality`, and it is functorial in the inclusion
by the cocycle condition read through
`AlgebraicGeometry.AffineOpensGlue.localAppFun_restrictLocal_le`. -/
def toGlueData : ModulesDirectedGlueData X (chart X) where
  mod := D.mod
  opensRange_mono := opensRange_mono
  locallyDirected := locallyDirected
  trans {V W} h {O} hO := localAppEquiv (D.comp h) O (le_of_le_opensRange_chart hO)
  trans_map {V W} h {O O'} hO hO' t := by
    have hOV : O ≤ (V.1 : X.Opens) := le_of_le_opensRange_chart hO
    exact (localAppFun_naturality (D.comp h).hom hOV (hO'.trans hOV) (homOfLE hO') t).symm
  trans_trans {V V' W} h h' {O} hO t := by
    have hOV : O ≤ (V.1 : X.Opens) := le_of_le_opensRange_chart hO
    change localAppFun (D.comp h').hom O (hOV.trans h) (localAppFun (D.comp h).hom O hOV t)
        = localAppFun (D.comp (h.trans h')).hom O hOV t
    rw [localAppFun_restrictLocal_le (D.comp h').hom
        (show (V.1 : X.Opens) ≤ (V'.1 : X.Opens) from h) hOV,
      ← localAppFun_comp, D.comp_trans]

/-- **The sheaf of modules on `X` glued from a chart comparison.** -/
abbrev glued : X.Modules := D.toGlueData.glued

/-- The glued sheaf of modules restricts along the chart of an affine open to the member of the
family there. -/
def chartIso (V : X.affineOpens) : D.glued.restrict (chart X V) ≅ D.mod V :=
  D.toGlueData.chartIso V

/-- **A sheaf of modules glued from invertible modules on the affine opens is invertible.**
Invertibility is local on `X`, and the restriction of the glued module to the chart of an affine
open is the module it was glued from. -/
theorem isInvertibleModule_glued
    (hinv : ∀ V : X.affineOpens,
      Stacks.Ample.IsInvertibleModule ((V.1 : X.Opens) : Scheme.{u}) (D.mod V)) :
    Stacks.Ample.IsInvertibleModule X D.glued := by
  refine Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.Modules.isInvertible_of_isInvertible_restrict_isOpenCover D.glued _
      (isOpenCover_affineOpens X) ?_)
  intro V
  have : Stacks.SheafOfModules.IsInvertible (((V.1 : X.Opens) : Scheme.{u})).presheaf
      (((V.1 : X.Opens) : Scheme.{u})).ringCatSheaf.2 (D.mod V) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ (hinv V)
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ (D.chartIso V).symm

end ChartComparison

end AlgebraicGeometry.AffineOpensGlue

end
