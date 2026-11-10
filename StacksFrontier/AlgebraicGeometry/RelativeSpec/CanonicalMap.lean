module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability

/-!
# The canonical morphism to the relative spectrum of a pushforward algebra

Let `f : T ⟶ S` be a morphism of schemes whose pushed-forward structure algebra
`f_* 𝒪_T` is quasi-coherent. The relative spectrum `Spec_S(f_* 𝒪_T)` then receives a canonical
morphism from `T`, namely the one that the representing property of
`Stacks.RelativeSpec.gluedSpectrum` ([Stacks, Tag 01LV]) attaches to the *identity* map of
`f_* 𝒪_T`. This file constructs that morphism, identifies it on each affine open of `S` with the
canonical map of the inverse image to the spectrum of its sections, and proves the cartesian
square that identifies the canonical morphism as an open immersion over a prescribed open.

The main theorem `isPullback_canonicalMap` is the shape consumed downstream: if `f` factors
through an open immersion `j : U ⟶ S` and the inverse image under `f` of every affine open of
`S` inside the image of `j` is affine, then

```
  T  --canonicalMap f-->  Spec_S(f_* 𝒪_T)
  |                             |
  g                             toBase
  v                             v
  U  --------- j --------->      S
```

is cartesian. No quasi-compactness or quasi-separatedness of `f` is assumed anywhere: the
quasi-coherence of `f_* 𝒪_T` is taken as a hypothesis instead of being derived from
[Stacks, Tag 01LC], and nothing else about `f` is used.

## Main definitions

* `Stacks.RelativeSpec.situationOfPushforward` — the relative-spectrum situation `(S, f_* 𝒪_T)`.
* `Stacks.RelativeSpec.canonicalMap` — the canonical morphism `T ⟶ Spec_S(f_* 𝒪_T)`.

## Main results

* `Stacks.RelativeSpec.canonicalMap_comp_toBase` — the canonical morphism lies over `S`.
* `Stacks.RelativeSpec.canonicalMap_homEquiv` — it is the morphism classifying the identity.
* `Stacks.RelativeSpec.canonicalMap_on_affineOpen` — on an affine open `W` of `S`, the canonical
  morphism restricted to `f ⁻¹ W` is the canonical map `f ⁻¹ W ⟶ Spec Γ(T, f ⁻¹ W)` followed by
  the gluing chart of the relative spectrum.
* `Stacks.RelativeSpec.isOpenImmersion_chart`, `Stacks.RelativeSpec.chart_opensRange` — each
  gluing chart is an open immersion, with image the inverse image of its affine open.
* `Stacks.RelativeSpec.isIso_morphismRestrict_canonicalMap` — over an affine open whose inverse
  image is affine, the canonical morphism restricts to an isomorphism.
* `Stacks.RelativeSpec.isPullback_canonicalMap` — the cartesian square displayed above.

## Implementation notes

**No `@[stacks]` attribute is placed here.** The content of `canonicalMap` and
`canonicalMap_on_affineOpen` is [Stacks, Tag 01LY], but that tag's own statement assumes `f`
quasi-compact and quasi-separated and asserts the quasi-coherence of `f_* 𝒪_T` as part of its
covering set; what is proved here takes that quasi-coherence as a hypothesis, so it is one
member of the tag's covering set short of the tag.

`canonicalMap_on_affineOpen` is proved by the universal property rather than by computing with
the gluing: the lift `l` of `(f ⁻¹ W).ι ≫ canonicalMap f` through the cartesian chart square and
the canonical map `(f ⁻¹ W).toSpecΓ` are two morphisms to an affine scheme, so it is enough to
compare them on global sections, which is what `AlgebraicGeometry.ext_to_Spec` does. The two
section maps agree because both compute the second component of the relative-spectrum pair
attached to `(f ⁻¹ W).ι ≫ canonicalMap f`; the auxiliary function `pairApp` extracts that
component from a pair in a way that only depends on the pair, so one `congrArg` transports the
equality of pairs to the equality of maps.

Every step of that argument that would naturally be a `rw` is written in **term mode**
(`Eq.trans`, `congrArg`, `Category.assoc`). The reason is specific and worth recording: a goal
mentioning `(situationOfPushforward f).base` beside `S`, or a chart of a relative spectrum, is
not type-correct at `implicit` transparency, because `TopCat.Sheaf` is a semireducible
definition for `CategoryTheory.Sheaf`; so `rw` fails its motive type-check on goals that
elaboration crosses without difficulty. Term mode runs conversion at default transparency and
crosses it. This is the same mechanism that `Stacks.RelativeSpec.gluedSpectrum` had to work
around, and it is why this file carries no `set_option`.

## References

* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 01LY](https://stacks.math.columbia.edu/tag/01LY)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec

/-! ### The situation and the canonical morphism -/

/-- **The relative-spectrum situation attached to a pushforward algebra.** For a morphism
`f : T ⟶ S` whose pushed-forward structure algebra is quasi-coherent, this is the base `S`
together with the algebra `f_* 𝒪_T`. -/
public def situationOfPushforward {T S : Scheme.{u}} (f : T ⟶ S)
    [(pushforwardAlgebra f).IsQuasicoherent] : RelativeSpecSituation.{u} :=
  ⟨S, pushforwardAlgebra f⟩

/-- **The canonical morphism `T ⟶ Spec_S(f_* 𝒪_T)`.** It is the morphism that the representing
property of the relative spectrum attaches to the identity map of `f_* 𝒪_T`. -/
public def canonicalMap {T S : Scheme.{u}} (f : T ⟶ S)
    [(pushforwardAlgebra f).IsQuasicoherent] :
    T ⟶ (gluedSpectrum (situationOfPushforward f)).scheme :=
  (relativeSpecRepresentableBy (situationOfPushforward f)).homEquiv.symm
    ⟨f, Under.homMk (𝟙 _) (by rfl)⟩

/-- **The canonical morphism is a morphism over `S`.** -/
public theorem canonicalMap_comp_toBase {T S : Scheme.{u}} (f : T ⟶ S)
    [(pushforwardAlgebra f).IsQuasicoherent] :
    canonicalMap f ≫ (gluedSpectrum (situationOfPushforward f)).toBase = f :=
  (relativeSpecRepresentableBy_homEquiv_fst (situationOfPushforward f)
      (canonicalMap f)).symm.trans
    (congrArg Sigma.fst
      ((relativeSpecRepresentableBy (situationOfPushforward f)).homEquiv.apply_symm_apply
        ⟨f, Under.homMk (𝟙 _) rfl⟩))

/-- **The canonical morphism classifies the identity of `f_* 𝒪_T`.** -/
public theorem canonicalMap_homEquiv {T S : Scheme.{u}} (f : T ⟶ S)
    [(pushforwardAlgebra f).IsQuasicoherent] :
    (relativeSpecRepresentableBy (situationOfPushforward f)).homEquiv
        (canonicalMap f) = ⟨f, Under.homMk (𝟙 _) (by rfl)⟩ :=
  Equiv.apply_symm_apply _ _

/-! ### The canonical morphism on an affine open of the base -/

/-- **On an affine open of the base, the canonical morphism is the canonical map to the spectrum
of the sections of the inverse image, followed by the gluing chart.** This is the local
description of the canonical morphism; every geometric property of it proved below is read off
from this equation. -/
public theorem canonicalMap_on_affineOpen {T S : Scheme.{u}} (f : T ⟶ S)
    [(pushforwardAlgebra f).IsQuasicoherent] (U : S.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ canonicalMap f =
      (f ⁻¹ᵁ U.1).toSpecΓ ≫
        (gluedSpectrum (situationOfPushforward f)).chart U := by
  classical
  let s := situationOfPushforward f
  let R := gluedSpectrum s
  let V := f ⁻¹ᵁ U.1
  let g : V.toScheme ⟶ R.scheme := V.ι ≫ canonicalMap f
  let k : V.toScheme ⟶ U.1.toScheme := f.resLE U.1 V le_rfl
  have hgbase : g ≫ R.toBase = k ≫ U.1.ι :=
    (Category.assoc _ _ _).trans
      (((congrArg (fun m => V.ι ≫ m) (canonicalMap_comp_toBase f)).trans
        (Scheme.Hom.resLE_comp_ι f (e := le_rfl)).symm))
  let l := (R.chart_isPullback U).lift g k hgbase
  have hl : l ≫ R.chart U = g := (R.chart_isPullback U).lift_fst g k hgbase
  have hpre : g ⁻¹ᵁ (R.toBase ⁻¹ᵁ U.1) = ⊤ :=
    (Scheme.Hom.comp_preimage g R.toBase U.1).symm.trans
      ((congrArg (fun m => m ⁻¹ᵁ U.1) hgbase).trans
        (by rw [Scheme.Hom.comp_preimage, U.1.ι_preimage_self]; simp))
  have hcan :
      (relativeSpecRepresentableBy s).homEquiv (canonicalMap f) =
        ⟨f, Under.homMk (𝟙 _) rfl⟩ :=
    canonicalMap_homEquiv f
  have hpair :
      (relativeSpecRepresentableBy s).homEquiv g =
        RelativeSpecPair.pullback V.ι ⟨f, Under.homMk (𝟙 _) rfl⟩ := by
    rw [Functor.RepresentableBy.homEquiv_comp, hcan]
    rfl
  have hId :
      (universalAlgebraMap s).right.app (.op U.1) ≫
          g.appLE (R.toBase ⁻¹ᵁ U.1) ⊤ (by simp [hpre]) =
        (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv ≫ V.toSpecΓ.appTop := by
    have hPP := (relativeSpecRepresentableBy_homEquiv s g).symm.trans hpair
    let pulledG : RelativeSpecPair s V.toScheme :=
      RelativeSpecPair.pullback g
        ⟨R.toBase, universalAlgebraMap s⟩
    let pulledV : RelativeSpecPair s V.toScheme :=
      RelativeSpecPair.pullback V.ι ⟨f, Under.homMk (𝟙 _) rfl⟩
    change pulledG = pulledV at hPP
    have hfullG : pulledG.1 ⁻¹ᵁ U.1 = ⊤ := hpre
    have hfullV : pulledV.1 ⁻¹ᵁ U.1 = ⊤ := V.ι_preimage_self
    let fullG : {p : RelativeSpecPair s V.toScheme // p.1 ⁻¹ᵁ U.1 = ⊤} := ⟨pulledG, hfullG⟩
    let fullV : {p : RelativeSpecPair s V.toScheme // p.1 ⁻¹ᵁ U.1 = ⊤} := ⟨pulledV, hfullV⟩
    let pairApp : {p : RelativeSpecPair s V.toScheme // p.1 ⁻¹ᵁ U.1 = ⊤} →
        ((Under.mk s.algebra.hom.hom).right.obj (.op U.1) ⟶
          V.toScheme.presheaf.obj (.op ⊤)) :=
      fun p => p.1.2.right.app (.op U.1) ≫ V.toScheme.presheaf.map (homOfLE p.2.ge).op
    calc
      (universalAlgebraMap s).right.app (.op U.1) ≫
          g.appLE (R.toBase ⁻¹ᵁ U.1) ⊤ (by simp [hpre]) = pairApp fullG := by
        simp only [pairApp, fullG, pulledG,
          Stacks.RelativeSpec.RelativeSpecPair.pullback_eq,
          Under.Hom.right, Under.comp_right, Scheme.Hom.appLE]
        rfl
      _ = pairApp fullV := congrArg pairApp (Subtype.ext hPP)
      _ = (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv ≫ V.toSpecΓ.appTop := by
        simp only [pairApp, fullV, pulledV,
          Stacks.RelativeSpec.RelativeSpecPair.pullback_eq,
          Under.Hom.right, Under.comp_right]
        rw [Scheme.Opens.toSpecΓ_appTop]
        change _ = (Scheme.ΓSpecIso (Γ(T, V))).inv ≫
          (Scheme.ΓSpecIso (Γ(T, V))).hom ≫ V.topIso.inv
        simp only [Iso.inv_hom_id_assoc]
        simp only [NatTrans.comp_app]
        simp only [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.topIso_inv]
        exact (T.presheaf.map_comp _ _).symm
  have hlapp :
      (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv ≫ l.appTop =
        (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv ≫ V.toSpecΓ.appTop := by
    have hchartpre : (R.chart U) ⁻¹ᵁ (R.toBase ⁻¹ᵁ U.1) = ⊤ :=
      R.chart_preimage U
    have hcompPre : (l ≫ R.chart U) ⁻¹ᵁ (R.toBase ⁻¹ᵁ U.1) = ⊤ := hl ▸ hpre
    have hLpre : l ⁻¹ᵁ ((R.chart U) ⁻¹ᵁ (R.toBase ⁻¹ᵁ U.1)) = ⊤ := by
      simpa only [Scheme.Hom.comp_preimage] using hcompPre
    have hcomp0 := Scheme.Hom.comp_appLE l (R.chart U) (R.toBase ⁻¹ᵁ U.1) ⊤ hcompPre.ge
    have hcomp1 :
        g.appLE (R.toBase ⁻¹ᵁ U.1) ⊤ (by simp [hpre]) =
          (R.chart U).app (R.toBase ⁻¹ᵁ U.1) ≫
            l.appLE ((R.chart U) ⁻¹ᵁ (R.toBase ⁻¹ᵁ U.1)) ⊤ hLpre.ge := by
      simpa only [hl] using hcomp0
    have hOpen :
        (R.chart U).appLE (R.toBase ⁻¹ᵁ U.1) ⊤ hchartpre.ge ≫ l.appTop =
          (R.chart U).app (R.toBase ⁻¹ᵁ U.1) ≫
            l.appLE ((R.chart U) ⁻¹ᵁ (R.toBase ⁻¹ᵁ U.1)) ⊤ hLpre.ge := by
      simp only [Scheme.Hom.appLE, Category.assoc]
      exact congrArg _ (l.naturality (homOfLE hchartpre.ge).op)
    calc
      (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv ≫ l.appTop
          = (universalAlgebraMap s).right.app (.op U.1) ≫
            g.appLE (R.toBase ⁻¹ᵁ U.1) ⊤ (by simp [hpre]) := by
        rw [← universalAlgebraMap_app_chartAppLE s U, Category.assoc]
        exact congrArg _ (hOpen.trans hcomp1.symm)
      _ = (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv ≫ V.toSpecΓ.appTop := hId
  exact hl.symm.trans (congrArg (fun m => m ≫ R.chart U) (AlgebraicGeometry.ext_to_Spec hlapp))

/-! ### The gluing charts as open immersions -/

/-- **A gluing chart of a relative spectrum is an open immersion**, being the base change of the
inclusion of its affine open along the structure morphism. -/
public instance isOpenImmersion_chart (s : RelativeSpecSituation.{u})
    (W : s.base.affineOpens) : IsOpenImmersion ((gluedSpectrum s).chart W) :=
  (gluedSpectrum s).chart_isOpenImmersion W

/-- **The image of a gluing chart is the inverse image of its affine open.** -/
public theorem chart_opensRange (s : RelativeSpecSituation.{u}) (W : s.base.affineOpens) :
    ((gluedSpectrum s).chart W).opensRange = (gluedSpectrum s).toBase ⁻¹ᵁ W.1 := by
  rw [← Scheme.Hom.image_top_eq_opensRange]
  simpa using IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    ((gluedSpectrum s).chart_isPullback W).flip ⊤

/-! ### The cartesian square -/

/-- **Over an affine open of the base whose inverse image is affine, the canonical morphism
restricts to an isomorphism.** The restriction is the canonical map of the inverse image to the
spectrum of its sections — an isomorphism because that inverse image is affine — followed by the
identification of the chart with the inverse image of the affine open. -/
public theorem isIso_morphismRestrict_canonicalMap {T S : Scheme.{u}} (f : T ⟶ S)
    [(pushforwardAlgebra f).IsQuasicoherent] (W : S.affineOpens)
    (hW : IsAffineOpen (f ⁻¹ᵁ W.1)) :
    IsIso (canonicalMap f ∣_ ((gluedSpectrum (situationOfPushforward f)).toBase ⁻¹ᵁ W.1)) := by
  set s := situationOfPushforward f with hs
  set R := gluedSpectrum s with hR
  have : IsOpenImmersion (R.chart W) := isOpenImmersion_chart s W
  set O : R.scheme.Opens := R.toBase ⁻¹ᵁ W.1 with hO
  have hpre : canonicalMap f ⁻¹ᵁ O =  f ⁻¹ᵁ W.1 :=
    (Scheme.Hom.comp_preimage (canonicalMap f) R.toBase W.1).symm.trans
      (congrArg (fun m => m ⁻¹ᵁ W.1) (canonicalMap_comp_toBase f))
  have hrange : Set.range (R.chart W) = Set.range O.ι := by
    have h1 : (R.chart W).opensRange = R.toBase ⁻¹ᵁ W.1 := chart_opensRange s W
    have h2 : O.ι.opensRange = O := O.opensRange_ι
    exact congrArg (fun (V : R.scheme.Opens) => (V : Set R.scheme)) (h1.trans h2.symm)
  set χ := IsOpenImmersion.isoOfRangeEq (R.chart W) O.ι hrange with hχ
  have hχfac : χ.hom ≫ O.ι = R.chart W :=
    IsOpenImmersion.isoOfRangeEq_hom_fac (R.chart W) O.ι hrange
  have hiso : IsIso ((f ⁻¹ᵁ W.1).toSpecΓ) := by
    have : IsAffine (f ⁻¹ᵁ W.1).toScheme := hW
    rw [Scheme.Opens.toSpecΓ]
    infer_instance
  have hfac : (canonicalMap f ∣_ O) =
      (T.isoOfEq hpre).hom ≫ (f ⁻¹ᵁ W.1).toSpecΓ ≫ χ.hom := by
    rw [← cancel_mono O.ι]
    calc (canonicalMap f ∣_ O) ≫ O.ι = (canonicalMap f ⁻¹ᵁ O).ι ≫ canonicalMap f :=
          morphismRestrict_ι _ _
      _ = ((T.isoOfEq hpre).hom ≫ (f ⁻¹ᵁ W.1).ι) ≫ canonicalMap f :=
          congrArg (fun m => m ≫ canonicalMap f) (T.isoOfEq_hom_ι hpre).symm
      _ = (T.isoOfEq hpre).hom ≫ ((f ⁻¹ᵁ W.1).ι ≫ canonicalMap f) := Category.assoc _ _ _
      _ = (T.isoOfEq hpre).hom ≫ ((f ⁻¹ᵁ W.1).toSpecΓ ≫ R.chart W) :=
          congrArg _ (canonicalMap_on_affineOpen f W)
      _ = ((T.isoOfEq hpre).hom ≫ (f ⁻¹ᵁ W.1).toSpecΓ ≫ χ.hom) ≫ O.ι :=
          ((Category.assoc _ _ _).trans
            (congrArg (fun m => (T.isoOfEq hpre).hom ≫ m)
              ((Category.assoc _ _ _).trans
                (congrArg (fun m => (f ⁻¹ᵁ W.1).toSpecΓ ≫ m) hχfac)))).symm
  rw [hfac]
  exact IsIso.comp_isIso' (T.isoOfEq hpre).isIso_hom
    (IsIso.comp_isIso' hiso χ.isIso_hom)

/-- **The canonical morphism identifies the source with the part of the relative spectrum lying
over a prescribed open.** If `f` factors as `g ≫ j` through an open immersion `j` and the inverse
image under `f` of every affine open of the base contained in the image of `j` is affine, then
the square formed by `g`, the canonical morphism, `j` and the structure morphism of the relative
spectrum is cartesian.

The hypothesis is checked one affine open at a time, which is what makes the theorem usable: it
never asks for anything about `f` over an affine open that meets the complement of the image of
`j`. -/
public theorem isPullback_canonicalMap {T S U : Scheme.{u}} (f : T ⟶ S)
    [(pushforwardAlgebra f).IsQuasicoherent]
    (j : U ⟶ S) [IsOpenImmersion j] (g : T ⟶ U) (hfg : g ≫ j = f)
    (haff : ∀ W : S.affineOpens, W.1 ≤ j.opensRange → IsAffineOpen (f ⁻¹ᵁ W.1)) :
    IsPullback g (canonicalMap f) j
      (gluedSpectrum (situationOfPushforward f)).toBase := by
  have hcb := canonicalMap_comp_toBase f
  -- the points of the image lie over the image of `j`
  have hpt : ∀ t : T, (gluedSpectrum (situationOfPushforward f)).toBase
      (canonicalMap f t) = j (g t) := by
    intro t
    have h1 : (gluedSpectrum (situationOfPushforward f)).toBase (canonicalMap f t) = f t :=
      congrArg (fun m : T ⟶ S => m.base t) hcb
    have h2 : f t = j (g t) := (congrArg (fun m : T ⟶ S => m.base t) hfg).symm
    exact h1.trans h2
  have hmem : ∀ t : T, (gluedSpectrum (situationOfPushforward f)).toBase
      (canonicalMap f t) ∈ j.opensRange := fun t => ⟨g t, (hpt t).symm⟩
  set ι₀ := {W : S.affineOpens // W.1 ≤ j.opensRange} with hι₀
  set Op : ι₀ → (gluedSpectrum (situationOfPushforward f)).scheme.Opens :=
    fun W => (gluedSpectrum (situationOfPushforward f)).toBase ⁻¹ᵁ W.1.1 with hOp
  have hkey : ∀ W : ι₀, IsIso (canonicalMap f ∣_ Op W) :=
    fun W => isIso_morphismRestrict_canonicalMap f W.1 (haff W.1 W.2)
  -- every point of the image lies in one of the chosen opens
  have hcover : ∀ y : (gluedSpectrum (situationOfPushforward f)).scheme.carrier,
      (gluedSpectrum (situationOfPushforward f)).toBase y ∈ j.opensRange →
      ∃ W : ι₀, y ∈ Op W := by
    intro y hy
    obtain ⟨W, hWaff, hWmem, hWsub⟩ := exists_isAffineOpen_mem_and_subset hy
    exact ⟨⟨⟨W, hWaff⟩, hWsub⟩, hWmem⟩
  have hsub : Set.range (canonicalMap f).base ⊆ ((⨆ W : ι₀, Op W : _) : Set _) := by
    rintro y ⟨t, rfl⟩
    obtain ⟨W, hW⟩ := hcover _ (hmem t)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨W, hW⟩
  have hoi : IsOpenImmersion (canonicalMap f) := by
    refine IsZariskiLocalAtTarget.of_range_subset_iSup Op hsub fun W => ?_
    have := hkey W
    infer_instance
  -- the range of the canonical map is exactly the inverse image of the image of `j`
  have hrange : ((gluedSpectrum (situationOfPushforward f)).toBase ⁻¹ᵁ j.opensRange : Set _)
      = Set.range (canonicalMap f).base := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨W, hW⟩ := hcover y hy
      have hmiso := hkey W
      have hsurj : Function.Surjective (canonicalMap f ∣_ Op W).base :=
        (inferInstance : Surjective (canonicalMap f ∣_ Op W)).surj
      obtain ⟨x, hx⟩ := hsurj ⟨y, hW⟩
      refine ⟨(canonicalMap f ⁻¹ᵁ Op W).ι x, ?_⟩
      have hι := morphismRestrict_ι (canonicalMap f) (Op W)
      have h3 : (Op W).ι ((canonicalMap f ∣_ Op W) x)
          = canonicalMap f ((canonicalMap f ⁻¹ᵁ Op W).ι x) :=
        congrArg (fun m : (canonicalMap f ⁻¹ᵁ Op W).toScheme ⟶
          (gluedSpectrum (situationOfPushforward f)).scheme => m.base x) hι
      rw [← h3, hx]
      rfl
    · rintro y ⟨t, rfl⟩
      exact hmem t
  -- assemble
  refine IsOpenImmersion.isPullback g (canonicalMap f) j
    (gluedSpectrum (situationOfPushforward f)).toBase ?_ ?_
  · exact hcb.trans hfg.symm
  · exact TopologicalSpace.Opens.ext hrange

end Stacks.RelativeSpec

end
