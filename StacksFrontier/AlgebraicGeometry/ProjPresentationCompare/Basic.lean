module

public import StacksFrontier.AlgebraicGeometry.ProjBundleProjectiveSpace.Descent
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProj.DataIso

/-!
# Comparing the two glueings of a relative homogeneous spectrum

This repository glues `Proj_S(𝒜)` twice, from two different records of the same local data.

* `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProj` glues the charts of a
  `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` as the colimit of the chart functor on
  the small affine Zariski site of `S`.
* `Stacks.RelativeProj.Data.relativeProj` glues the charts of a `Stacks.RelativeProj.Data` over
  the locally directed cover of `S` by *all* of its affine opens.

`StacksFrontier.AlgebraicGeometry.RelativeProj.DataIso` compares two `Data`s; this file compares a
`GradedAlgebra` with a `Data`. The input is the same in both cases: a graded ring isomorphism
over every affine open of the base, compatible with restriction and with the degree-zero
identifications. The output is an isomorphism of the glued schemes **over the base**, which is
what identifies the two constructions as relative homogeneous spectra rather than merely as
schemes.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjPresentation.projIso`: the induced isomorphism of charts.
* `Stacks.AlgebraicGeometry.ProjPresentation.chartFamily`: the charts of the `Data` read as a
  `Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily` for the `GradedAlgebra`.

## Main results

* `Stacks.AlgebraicGeometry.ProjPresentation.exists_iso_relativeProj`: **the two glueings are
  isomorphic over the base.**

## Implementation notes

The comparison goes through
`Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily`, the uniqueness half of Tag 01NQ for
the colimit glueing: a scheme over `S` carrying cartesian charts over the affine opens,
compatible with the transitions, is the colimit. The `Data`'s glued scheme carries exactly those
charts, transported along the chart isomorphism, so no new glueing argument is needed.

Only the *arrows of the site* — the basic open inclusions — need the transition compatibility.
The hypothesis `hres` is nevertheless stated for an arbitrary inclusion of affine opens, which
is no restriction: a `Data` has restriction maps along every inclusion and a `GradedAlgebra`
has them too, so that is the shape both sides come in.

`AlgebraicGeometry.Proj.map` is contravariant, so the chart isomorphism in the forward direction
— from the `GradedAlgebra`'s chart to the `Data`'s chart — is `Proj.map` of the *inverse* graded
ring homomorphism. Its hypothesis `ℬ₊ ≤ 𝒜₊.map f` is automatic for an isomorphism, by
`Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id`.

An object of `AlgebraicGeometry.Scheme.AffineZariskiSite` and a member of
`AlgebraicGeometry.Scheme.affineOpens` are the same pair of an open and a proof of its
affineness, but the two types are different definitions, so the conversion is written out as an
anonymous constructor at each occurrence.

The hypotheses are section variables, so each declaration takes exactly the ones it uses, in
the order of the `variable` block; the `omit` lines record which of them a declaration does
without.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)

## Not done here

No project tag is attached: the existence of the relative homogeneous spectrum is Tag 01NQ and
is tagged where it is built, and the comparison of two constructions of it is not a labelled
assertion of the source.

Nothing here identifies the graded rings of two particular presentations; this file only glues
such an identification once it is given.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousIdeal Graded
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue
open Stacks.AlgebraicGeometry.RelativeProjDescent

namespace Stacks.AlgebraicGeometry.ProjPresentation

universe u

/-- **The inverse of a graded ring homomorphism**, from a two-sided inverse of its underlying
function that respects the gradings. Mathlib has no bundled graded ring isomorphism, so the
inverse is built by hand; its ring-homomorphism laws are *transported* from those of `f` rather
than re-derived, which matters when the two gradings grade one carrier by two different ring
structures: deriving them again would make the elaborator compare the two structures once per
law. -/
public def gradedRingHomInverse {A B σ τ : Type u} [Semiring A] [Semiring B]
    [SetLike σ A] [SetLike τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} (f : 𝒜 →+*ᵍ ℬ) (g : B → A)
    (hgf : ∀ x : A, g (f x) = x) (hfg : ∀ y : B, f (g y) = y)
    (hmem : ∀ (i : ℕ) (y : B), y ∈ ℬ i → g y ∈ 𝒜 i) : ℬ →+*ᵍ 𝒜 where
  toFun := g
  map_one' := by
    calc g 1 = g (f 1) := by rw [map_one f]
      _ = 1 := hgf 1
  map_mul' x y := by
    have h : f (g x * g y) = x * y := by rw [map_mul f, hfg, hfg]
    calc g (x * y) = g (f (g x * g y)) := by rw [h]
      _ = g x * g y := hgf _
  map_zero' := by
    calc g 0 = g (f 0) := by rw [map_zero f]
      _ = 0 := hgf 0
  map_add' x y := by
    have h : f (g x + g y) = x + y := by rw [map_add f, hfg, hfg]
    calc g (x + y) = g (f (g x + g y)) := by rw [h]
      _ = g x + g y := hgf _
  map_mem := fun {i x} h => hmem i x h

/-- If `f ∘ g` is the identity graded ring homomorphism then `f (g x) = x`. -/
private theorem apply_apply_of_comp_eq_id {A B σ τ : Type u} [Semiring A] [Semiring B]
    [SetLike σ A] [SetLike τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {f : ℬ →+*ᵍ 𝒜} {g : 𝒜 →+*ᵍ ℬ}
    (h : f.comp g = GradedRingHom.id 𝒜) (x : A) : f (g x) = x := by
  have h' := GradedRingHom.congr_fun h x
  rwa [GradedRingHom.comp_apply, GradedRingHom.id_apply] at h'

section Compare

variable {S : Scheme.{u}}

/-- An object of the small affine Zariski site is an affine open of the base. Named, rather than
written as the projection `U.2`, because `AlgebraicGeometry.Scheme.AffineZariskiSite` is a `def`
and so `U.2` is type-correct only at default transparency: left inside a hypothesis's type it
makes every later `rw` report the goal as ill-typed at `instances` transparency. -/
public theorem isAffineOpen_toOpens (U : S.AffineZariskiSite) : IsAffineOpen U.toOpens := U.2

/-- An object of the small affine Zariski site, read as an affine open. Reducible, so that the
open underlying it is the usual `AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens` spelling and
the two indexings of the hypotheses below have the same types on the nose. -/
public abbrev siteAffineOpen (U : S.AffineZariskiSite) : S.affineOpens :=
  ⟨U.toOpens, isAffineOpen_toOpens U⟩

/-- `siteAffineOpen` is monotone: an inclusion of objects of the small affine Zariski site is an
inclusion of the corresponding affine opens. -/
public theorem siteAffineOpen_le {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens) :
    siteAffineOpen U ≤ siteAffineOpen V := h

variable
  {B τ : S.affineOpens → Type u} [∀ U, CommRing (B U)] [∀ U, SetLike (τ U) (B U)]
  [∀ U, AddSubgroupClass (τ U) (B U)] {ℬ : ∀ U, ℕ → τ U} [∀ U, GradedRing (ℬ U)]
  (d : Stacks.RelativeProj.Data ℬ)
  (𝒞 : Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra S)
  (hm : ∀ U : S.AffineZariskiSite, 𝒞.grading U →+*ᵍ ℬ (siteAffineOpen U))
  (hn : ∀ U : S.AffineZariskiSite, ℬ (siteAffineOpen U) →+*ᵍ 𝒞.grading U)
  (hnm : ∀ U : S.AffineZariskiSite, (hn U).comp (hm U) = GradedRingHom.id (𝒞.grading U))
  (hmn : ∀ U : S.AffineZariskiSite,
    (hm U).comp (hn U) = GradedRingHom.id (ℬ (siteAffineOpen U)))
  (hres : ∀ (U V : S.AffineZariskiSite) (h : U.toOpens ≤ V.toOpens),
    (hm U).comp (𝒞.res h) =
      (d.restrict (siteAffineOpen_le h)).comp (hm V))
  (hbase : ∀ U : S.AffineZariskiSite,
    𝒞.strZero U ≫ CommRingCat.ofHom (hm U).gradedZeroRingHom = d.base (siteAffineOpen U))

include d hm hn hnm hmn hres hbase

omit d hmn hres hbase in
/-- The irrelevant ideal of the `GradedAlgebra`'s chart is covered by the image of the `Data`'s;
this is automatic for an isomorphism. -/
public theorem irrelevant_le_hn (U : S.AffineZariskiSite) :
    irrelevant (𝒞.grading U) ≤ (irrelevant (ℬ (siteAffineOpen U))).map (hn U) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (hnm U)

omit d hnm hres hbase in
/-- The irrelevant ideal of the `Data`'s chart is covered by the image of the
`GradedAlgebra`'s. -/
public theorem irrelevant_le_hm (U : S.AffineZariskiSite) :
    irrelevant (ℬ (siteAffineOpen U)) ≤ (irrelevant (𝒞.grading U)).map (hm U) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (hmn U)

omit d hres hbase in
/-- **The induced isomorphism of charts** over an affine open of the base. -/
public def projIso (U : S.AffineZariskiSite) :
    𝒞.projOver U ≅ AlgebraicGeometry.Proj (ℬ (siteAffineOpen U)) where
  hom := Proj.map (hn U) (irrelevant_le_hn 𝒞 hm hn hnm U)
  inv := Proj.map (hm U) (irrelevant_le_hm 𝒞 hm hn hmn U)
  hom_inv_id := by
    refine Eq.trans (Proj.map_comp (hm U) (hn U)
      (irrelevant_le_hm 𝒞 hm hn hmn U)
      (irrelevant_le_hn 𝒞 hm hn hnm U)).symm ?_
    exact (Proj.map_congr (hnm U) _ (by simp)).trans Proj.map_id
  inv_hom_id := by
    refine Eq.trans (Proj.map_comp (hn U) (hm U)
      (irrelevant_le_hn 𝒞 hm hn hnm U)
      (irrelevant_le_hm 𝒞 hm hn hmn U)).symm ?_
    exact (Proj.map_congr (hmn U) _ (by simp)).trans Proj.map_id

omit d hres hbase in
/-- The forward map of `projIso` is the map of `Proj`s induced by `hn U`. -/
public theorem projIso_hom (U : S.AffineZariskiSite) :
    (projIso 𝒞 hm hn hnm hmn U).hom =
      Proj.map (hn U) (irrelevant_le_hn 𝒞 hm hn hnm U) := rfl

omit d hmn hres hbase in
/-- The degree-zero parts of the two homomorphisms are inverse ring isomorphisms. -/
public theorem gradedZeroRingHom_comp (U : S.AffineZariskiSite) :
    ((hn U).gradedZeroRingHom).comp ((hm U).gradedZeroRingHom) =
      RingHom.id (𝒞.grading U 0) := by
  exact RingHom.ext fun x => Subtype.ext (apply_apply_of_comp_eq_id (hnm U) (x : 𝒞.ring U))

omit hmn hres in
/-- The degree-zero identifications are compatible with the inverse homomorphism. -/
public theorem base_comp_hn (U : S.AffineZariskiSite) :
    d.base (siteAffineOpen U) ≫ CommRingCat.ofHom (hn U).gradedZeroRingHom = 𝒞.strZero U := by
  rw [← hbase U, Category.assoc, ← CommRingCat.ofHom_comp,
    gradedZeroRingHom_comp 𝒞 hm hn hnm U, CommRingCat.ofHom_id,
    Category.comp_id]

omit hbase in
/-- The inverse homomorphism also commutes with the restriction maps. This is the form the
naturality of the chart isomorphism needs, `AlgebraicGeometry.Proj.map` being
contravariant. -/
public theorem res_comp_hn (U V : S.AffineZariskiSite) (h : U.toOpens ≤ V.toOpens) :
    (𝒞.res h).comp (hn V) =
      (hn U).comp (d.restrict (siteAffineOpen_le h)) := by
  refine GradedRingHom.ext fun y => ?_
  have hnat : hm U (𝒞.res h (hn V y)) =
      d.restrict (siteAffineOpen_le h) y := by
    have h1 := GradedRingHom.congr_fun (hres U V h) (hn V y)
    rw [GradedRingHom.comp_apply, GradedRingHom.comp_apply] at h1
    rw [h1, apply_apply_of_comp_eq_id (hmn V) y]
  rw [GradedRingHom.comp_apply, GradedRingHom.comp_apply,
    ← apply_apply_of_comp_eq_id (hnm U) (𝒞.res h (hn V y)), hnat]

omit hres in
/-- The chart isomorphism is a morphism over the affine open of the base. -/
public theorem projIso_hom_chartToOpen (U : S.AffineZariskiSite) :
    (projIso 𝒞 hm hn hnm hmn U).hom ≫
        Stacks.RelativeProj.chartToOpen ℬ (siteAffineOpen U) (d.base (siteAffineOpen U)) =
      𝒞.toOpen U := by
  rw [projIso_hom, Stacks.RelativeProj.chartToOpen, Proj.map_toSpecZero_assoc,
    ← Spec.map_comp_assoc, base_comp_hn d 𝒞 hm hn hnm hbase U]
  rfl

omit hbase in
/-- The chart isomorphism is natural in the affine open of the base. -/
public theorem transition_projIso_hom (U V : S.AffineZariskiSite) (h : U.toOpens ≤ V.toOpens)
    (hi : irrelevant (𝒞.grading U) ≤ (irrelevant (𝒞.grading V)).map (𝒞.res h)) :
    Proj.map (𝒞.res h) hi ≫ (projIso 𝒞 hm hn hnm hmn V).hom =
      (projIso 𝒞 hm hn hnm hmn U).hom ≫
        d.map (siteAffineOpen_le h) := by
  rw [projIso_hom, projIso_hom]
  refine Eq.trans (Proj.map_comp (hn V) (𝒞.res h)
    (irrelevant_le_hn 𝒞 hm hn hnm V) hi).symm ?_
  refine Eq.trans ?_ (Proj.map_comp
    (d.restrict (siteAffineOpen_le h)) (hn U)
    (d.irrelevant_le (siteAffineOpen_le h))
    (irrelevant_le_hn 𝒞 hm hn hnm U))
  exact Proj.map_congr (res_comp_hn d 𝒞 hm hn hnm hmn hres U V h) _ _

/-- **The charts of the `Data`'s glued scheme, read as a chart family for the
`GradedAlgebra`.** -/
public def chartFamily : ChartFamily 𝒞 d.relativeProj d.toBase where
  chart U := (projIso 𝒞 hm hn hnm hmn U).hom ≫ d.chartι (siteAffineOpen U)
  isPullback U := by
    refine (d.isPullback_chartι (siteAffineOpen U)).of_iso'
      (projIso 𝒞 hm hn hnm hmn U) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_
      (by simp) (by simp) (by simp)
    simp only [Iso.refl_hom, Category.comp_id]
    exact projIso_hom_chartToOpen d 𝒞 hm hn hnm hmn hbase U
  transition {U V} φ := by
    have hle : U.toOpens ≤ V.toOpens := Scheme.AffineZariskiSite.toOpens_mono φ.le
    have hw : d.map (siteAffineOpen_le hle) ≫
        d.chartι (siteAffineOpen V) = d.chartι (siteAffineOpen U) :=
      colimit.w d.gluingData.functor (homOfLE (siteAffineOpen_le hle))
    change 𝒞.transition hle (mapDomain_res_eq_top_of_le 𝒞 φ.le _) ≫
        ((projIso 𝒞 hm hn hnm hmn V).hom ≫ d.chartι (siteAffineOpen V)) =
      (projIso 𝒞 hm hn hnm hmn U).hom ≫ d.chartι (siteAffineOpen U)
    rw [𝒞.transition_eq_map hle _ (irrelevant_le_map_res_of_le 𝒞 φ.le hle), ← Category.assoc,
      transition_projIso_hom d 𝒞 hm hn hnm hmn hres U V hle
        (irrelevant_le_map_res_of_le 𝒞 φ.le hle),
      Category.assoc, hw]

/-- **The two glueings of the relative homogeneous spectrum agree over the base.** The colimit
glueing of a `GradedAlgebra` and the cover glueing of a `Data` whose graded rings of sections
are isomorphic to the `GradedAlgebra`'s, compatibly with restriction and with the degree-zero
identifications, produce isomorphic schemes over the base. -/
public theorem exists_iso_relativeProj :
    ∃ e : relativeProj 𝒞 ≅ d.relativeProj, e.hom ≫ d.toBase = relativeProjToBase 𝒞 :=
  ⟨(chartFamily d 𝒞 hm hn hnm hmn hres hbase).iso,
    (chartFamily d 𝒞 hm hn hnm hmn hres hbase).iso_hom_comp⟩

end Compare

section Inverse

variable {S : Scheme.{u}}
  {B τ : S.affineOpens → Type u} [∀ U, CommRing (B U)] [∀ U, SetLike (τ U) (B U)]
  [∀ U, AddSubgroupClass (τ U) (B U)] {ℬ : ∀ U, ℕ → τ U} [∀ U, GradedRing (ℬ U)]

/-- **The two glueings agree over the base, from one graded ring homomorphism and an inverse of
its underlying function.** This is
`Stacks.AlgebraicGeometry.ProjPresentation.exists_iso_relativeProj` with the inverse graded ring
homomorphism and the two round-trip identities supplied by
`Stacks.AlgebraicGeometry.ProjPresentation.gradedRingHomInverse`, so that a caller writes the
comparison of the two graded rings of sections once rather than twice. -/
public theorem exists_iso_relativeProj_of_inverse (d : Stacks.RelativeProj.Data ℬ)
    (𝒞 : Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra S)
    (hm : ∀ U : S.AffineZariskiSite, 𝒞.grading U →+*ᵍ ℬ (siteAffineOpen U))
    (g : ∀ U : S.AffineZariskiSite, B (siteAffineOpen U) → 𝒞.ring U)
    (hgf : ∀ (U : S.AffineZariskiSite) (x : 𝒞.ring U), g U (hm U x) = x)
    (hfg : ∀ (U : S.AffineZariskiSite) (y : B (siteAffineOpen U)), hm U (g U y) = y)
    (hmem : ∀ (U : S.AffineZariskiSite) (i : ℕ) (y : B (siteAffineOpen U)),
      y ∈ ℬ (siteAffineOpen U) i → g U y ∈ 𝒞.grading U i)
    (hres : ∀ (U V : S.AffineZariskiSite) (h : U.toOpens ≤ V.toOpens),
      (hm U).comp (𝒞.res h) = (d.restrict (siteAffineOpen_le h)).comp (hm V))
    (hbase : ∀ U : S.AffineZariskiSite,
      𝒞.strZero U ≫ CommRingCat.ofHom (hm U).gradedZeroRingHom = d.base (siteAffineOpen U)) :
    ∃ e : relativeProj 𝒞 ≅ d.relativeProj, e.hom ≫ d.toBase = relativeProjToBase 𝒞 :=
  exists_iso_relativeProj d 𝒞 hm
    (fun U => gradedRingHomInverse (hm U) (g U) (hgf U) (hfg U) (hmem U))
    (fun U => GradedRingHom.ext fun x => hgf U x)
    (fun U => GradedRingHom.ext fun y => hfg U y) hres hbase

end Inverse

end Stacks.AlgebraicGeometry.ProjPresentation

end
