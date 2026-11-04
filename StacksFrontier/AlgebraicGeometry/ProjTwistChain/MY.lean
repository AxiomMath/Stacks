module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.ProjShared.MapDomain
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The morphism on projective spectra induced by a graded ring homomorphism

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings. It does not in general
induce a morphism `Proj ℬ ⟶ Proj 𝒜`: a homogeneous prime of `ℬ` containing the image of the
irrelevant ideal `𝒜₊` has no image. Mathlib's `AlgebraicGeometry.Proj.map` therefore assumes
`ℬ₊ ≤ 𝒜₊.map ψ`, which forces the morphism to be everywhere defined.

This file removes that hypothesis: it constructs the morphism on its exact domain of
definition
`U(ψ) = ⋃_{d > 0} ⋃_{f ∈ 𝒜 d} D₊(ψ f) ⊆ Proj ℬ`,
which is `Stacks.AlgebraicGeometry.ProjShared.mapDomain`, and proves the two properties that
characterize it locally.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistChain.mapAwayHom`: on the standard open `D₊(ψ f)` of a
  homogeneous `f` of positive degree, the morphism to `Proj 𝒜` induced by the map
  `A_{(f)} → B_{(ψ f)}` of degree-zero localizations.
* `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`: the morphism `U(ψ) ⟶ Proj 𝒜` obtained by
  gluing these.
* `Stacks.AlgebraicGeometry.ProjTwistChain.mapAwayHomRes`: for a composable pair `φ, ψ`, the
  factorization of the local morphism of `ψ` through `D₊(φ f)`.

## Main results

* `mapHom_preimage_basicOpen`: the inverse image of `D₊(f)` under `mapHom` is
  `U(ψ).ι ⁻¹ᵁ D₊(ψ f)`; this is Tag 01MY part (2) for the underlying scheme morphism.
* `homOfLE_mapHom`: on `D₊(ψ f)` the morphism is `mapAwayHom`, i.e. it is induced by
  `HomogeneousLocalization.Away.map ψ f`. This is the local form of Tag 01MY part (2).
* `mapDomain_hom_ext`: two morphisms out of `U(ψ)` agreeing on every `D₊(ψ f)` are equal.
* `mapDomain_comp`: the domain of the composite is the image under `U(ψ).ι` of the inverse
  image of `U(φ)`; this is Tag 01MZ's statement about domains.
* `mapAwayHom_comp`: the local morphism of a composite is the composite of the local
  morphisms.

## Implementation notes

The domain `U(ψ)` is covered by the opens `D₊(ψ f)` of the *ambient* `Proj ℬ`, not by opens of
`U(ψ)`; the gluing therefore uses `AlgebraicGeometry.Scheme.Opens.iSupOpenCover` together with
`AlgebraicGeometry.isPullback_opens_inf_le`, whose pullback square is literally the square of
`Scheme.homOfLE`s. The compatibility condition on an overlap
`D₊(ψ f) ⊓ D₊(ψ g) = D₊(ψ (f g))` reduces to the commuting square of degree-zero
localizations `awayMap_comp_map`.

Two transparency gotchas were hit and are worth recording.

* The degree of a homogeneous element is an implicit argument of
  `AlgebraicGeometry.Proj.awayι` and of `basicOpenIsoSpec`, but it occurs only inside proofs.
  Proof irrelevance makes `mapAwayHom_congr` hold by `rfl`, yet `rw` cannot unify two
  different degrees, so `homOfLE_mapAwayHom` takes the degree `k` of the product as a free
  variable and the relevant Mathlib lemmas are applied through explicitly typed `have`s.
* `AlgebraicGeometry.Scheme.Opens.iSupOpenCover` is a plain `def`, so `(𝒰.f i)` is not
  type-correct at `implicit` transparency against a goal mentioning `Scheme.homOfLE`; every
  `rw` touching the cover is preceded by `dsimp only [Scheme.Opens.iSupOpenCover]`. For the
  same reason `GradedRingHom.comp` is made `implicit_reducible` locally, so that
  `(ψ.comp φ) f` and `ψ (φ f)` are interchangeable in rewrite motives.

Two stacks attributes are carried here: 01MY's "part (2), inverse images of standard opens"
on `mapHom_preimage_basicOpen`, and 01MZ's "the domain of the composite" on
`mapDomain_comp`. Each is its own covering set, and the two assertions are separate.
What is *not* here is anything quantified over the bundled `ProjMapData`. The twist
comparison itself is `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, and 01MZ's "the maps
on all twists of the composite" is `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp`
in `StacksFrontier/AlgebraicGeometry/ProjTwistCompTwistMap/Comp.lean`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open Stacks.AlgebraicGeometry.ProjShared

namespace Stacks.AlgebraicGeometry.ProjTwistChain

attribute [local implicit_reducible] GradedRingHom.comp

universe u w w' w''

section

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- For `f` homogeneous of positive degree, the standard open `D₊(ψ f)` of `Proj ℬ` lies in the
domain of definition `U(ψ)`. -/
public theorem basicOpen_le_mapDomain (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) : Proj.basicOpen ℬ (ψ f) ≤ mapDomain 𝒜 ℬ ψ :=
  le_iSup_of_le d (le_iSup_of_le hd
    (le_iSup (fun g : 𝒜 d => Proj.basicOpen ℬ (ψ (g : A))) ⟨f, hf⟩))

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- A graded ring homomorphism carries the degree-`d` part into the degree-`d` part. The
`DFunLike` coercion is used here, as in `AlgebraicGeometry.Proj.basicOpen`. -/
public theorem mem_of_mem (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) : ψ f ∈ ℬ d :=
  ψ.map_mem hf

/-- On the standard open `D₊(ψ f)` of a homogeneous `f` of positive degree, the morphism to
`Proj 𝒜` induced by the map `A_{(f)} → B_{(ψ f)}` of degree-zero localizations. -/
public def mapAwayHom (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    (Proj.basicOpen ℬ (ψ f)).toScheme ⟶ AlgebraicGeometry.Proj 𝒜 :=
  Proj.basicOpenToSpec ℬ (ψ f) ≫
    Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫ Proj.awayι 𝒜 f hf hd

/-- The morphism `mapAwayHom` does not depend on the degree in which `f` is homogeneous. -/
public theorem mapAwayHom_congr (ψ : 𝒜 →+*ᵍ ℬ) {d d' : ℕ} (hd : 0 < d) (hd' : 0 < d')
    {f : A} (hf : f ∈ 𝒜 d) (hf' : f ∈ 𝒜 d') :
    mapAwayHom 𝒜 ℬ ψ hd hf = mapAwayHom 𝒜 ℬ ψ hd' hf' := rfl

/-- The graded ring map commutes with the transition maps between degree-zero localizations:
for `x = f * g` the square `A_{(f)} → A_{(x)} → B_{(ψ x)}`, `A_{(f)} → B_{(ψ f)} → B_{(ψ x)}`
commutes. -/
public theorem awayMap_comp_map (ψ : 𝒜 →+*ᵍ ℬ) {d e : ℕ} {f g x : A}
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (hfg : x = f * g) :
    (awayMap ℬ (mem_of_mem 𝒜 ℬ ψ hg) (show ψ x = ψ f * ψ g by rw [hfg, map_mul])).comp
        (Away.map ψ f) =
      (Away.map ψ x).comp (awayMap 𝒜 hg hfg) := by
  subst hfg
  ext y
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf y
  simp [Away.map_mk, awayMap_mk]

/-- Restricting the local morphism attached to `f` to the standard open of a multiple
`x = f * g` of `f` gives the local morphism attached to `x`. -/
public theorem homOfLE_mapAwayHom (ψ : 𝒜 →+*ᵍ ℬ) {d e k : ℕ} (hd : 0 < d) (hk : 0 < k)
    {f g x : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (hx : x ∈ 𝒜 k) (hfg : x = f * g)
    {W : (AlgebraicGeometry.Proj ℬ).Opens}
    (hWx : W ≤ Proj.basicOpen ℬ (ψ x)) (hWf : W ≤ Proj.basicOpen ℬ (ψ f)) :
    (AlgebraicGeometry.Proj ℬ).homOfLE hWf ≫ mapAwayHom 𝒜 ℬ ψ hd hf =
      (AlgebraicGeometry.Proj ℬ).homOfLE hWx ≫ mapAwayHom 𝒜 ℬ ψ hk hx := by
  have hψ : ψ x = ψ f * ψ g := by rw [hfg, map_mul]
  have hbo : Proj.basicOpen ℬ (ψ x) ≤ Proj.basicOpen ℬ (ψ f) :=
    Proj.basicOpen_mono ℬ (ψ f) (ψ x) ⟨ψ g, hψ⟩
  have hawayι : Proj.awayι 𝒜 x hx hk =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 hg hfg)) ≫ Proj.awayι 𝒜 f hf hd :=
    (Proj.SpecMap_awayMap_awayι 𝒜 hf hd hg hfg).symm
  have key : (AlgebraicGeometry.Proj ℬ).homOfLE hbo ≫ mapAwayHom 𝒜 ℬ ψ hd hf =
      mapAwayHom 𝒜 ℬ ψ hk hx := by
    rw [mapAwayHom, mapAwayHom,
      ← Proj.basicOpenToSpec_SpecMap_awayMap_assoc ℬ (mem_of_mem 𝒜 ℬ ψ hg) hψ, hawayι,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, awayMap_comp_map 𝒜 ℬ ψ hf hg hfg]
  rw [← key, ← Category.assoc, Scheme.homOfLE_homOfLE]


/-- The index type of the standard affine cover of the domain of definition: homogeneous
elements of `A` of positive degree. -/
public abbrev MapIndex := Σ' (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The domain of definition written as a single supremum of standard opens. -/
public theorem mapDomain_eq_iSup (ψ : 𝒜 →+*ᵍ ℬ) :
    mapDomain 𝒜 ℬ ψ = ⨆ i : MapIndex 𝒜, Proj.basicOpen ℬ (ψ i.2.1) :=
  le_antisymm
    (iSup_le fun d => iSup_le fun hd => iSup_le fun f =>
      le_iSup (fun i : MapIndex 𝒜 => Proj.basicOpen ℬ (ψ i.2.1)) ⟨d, f, hd, f.2⟩)
    (iSup_le fun i => basicOpen_le_mapDomain 𝒜 ℬ ψ i.2.2.1 i.2.2.2)

/-- The local morphisms attached to two homogeneous elements agree on the overlap of their
standard opens. -/
@[ega "II 2.8.1" "partial"]
public theorem mapAwayHom_compat (ψ : 𝒜 →+*ᵍ ℬ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) :
    (AlgebraicGeometry.Proj ℬ).homOfLE
        (inf_le_left : Proj.basicOpen ℬ (ψ f) ⊓ Proj.basicOpen ℬ (ψ g) ≤ _) ≫
        mapAwayHom 𝒜 ℬ ψ hd hf =
      (AlgebraicGeometry.Proj ℬ).homOfLE
        (inf_le_right : Proj.basicOpen ℬ (ψ f) ⊓ Proj.basicOpen ℬ (ψ g) ≤ _) ≫
        mapAwayHom 𝒜 ℬ ψ he hg := by
  have hWx : Proj.basicOpen ℬ (ψ f) ⊓ Proj.basicOpen ℬ (ψ g) ≤
      Proj.basicOpen ℬ (ψ (f * g)) := by rw [map_mul, Proj.basicOpen_mul]
  rw [homOfLE_mapAwayHom 𝒜 ℬ ψ hd (Nat.lt_of_lt_of_le hd (Nat.le_add_right d e)) hf hg
      (SetLike.mul_mem_graded hf hg) rfl hWx inf_le_left,
    homOfLE_mapAwayHom 𝒜 ℬ ψ he (Nat.lt_of_lt_of_le hd (Nat.le_add_right d e)) hg hf
      (SetLike.mul_mem_graded hf hg) (mul_comm f g) hWx inf_le_right]

/-- The morphism `U(ψ) ⟶ Proj 𝒜` induced by a graded ring homomorphism `ψ : 𝒜 →+*ᵍ ℬ` on its
domain of definition `U(ψ) = ⋃ D₊(ψ f)`. -/
@[ega "II 2.8.2"]
public def mapHom (ψ : 𝒜 →+*ᵍ ℬ) :
    (mapDomain 𝒜 ℬ ψ).toScheme ⟶ AlgebraicGeometry.Proj 𝒜 :=
  ((AlgebraicGeometry.Proj ℬ).isoOfEq (mapDomain_eq_iSup 𝒜 ℬ ψ)).hom ≫
    (Scheme.Opens.iSupOpenCover
        (fun i : MapIndex 𝒜 => Proj.basicOpen ℬ (ψ i.2.1))).glueMorphisms
      (fun i => mapAwayHom 𝒜 ℬ ψ i.2.2.1 i.2.2.2) (fun i j => by
        dsimp only [Scheme.Opens.iSupOpenCover]
        rw [← cancel_epi (AlgebraicGeometry.isPullback_opens_inf_le
            (le_iSup (fun i : MapIndex 𝒜 => Proj.basicOpen ℬ (ψ i.2.1)) i)
            (le_iSup (fun i : MapIndex 𝒜 => Proj.basicOpen ℬ (ψ i.2.1)) j)).isoPullback.hom,
          ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_fst,
          ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_snd]
        exact mapAwayHom_compat 𝒜 ℬ ψ i.2.2.1 j.2.2.1 i.2.2.2 j.2.2.2)


/-- On the standard open `D₊(ψ f)` the induced morphism is the morphism of affine schemes
attached to the map `A_{(f)} → B_{(ψ f)}` of degree-zero localizations. -/
@[reassoc]
public theorem homOfLE_mapHom (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf) ≫
        mapHom 𝒜 ℬ ψ = mapAwayHom 𝒜 ℬ ψ hd hf := by
  rw [mapHom, ← Category.assoc, Scheme.isoOfEq_hom, Scheme.homOfLE_homOfLE]
  exact (Scheme.Opens.iSupOpenCover
    (fun i : MapIndex 𝒜 => Proj.basicOpen ℬ (ψ i.2.1))).ι_glueMorphisms _ _ ⟨d, f, hd, hf⟩


/-- The image of the localization element `g^d / f^e` under the graded ring map. -/
public theorem map_isLocalizationElem (ψ : 𝒜 →+*ᵍ ℬ) {d e : ℕ} {f g : A}
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) :
    Away.map ψ f (Away.isLocalizationElem hf hg) =
      Away.isLocalizationElem (mem_of_mem 𝒜 ℬ ψ hf) (mem_of_mem 𝒜 ℬ ψ hg) := by
  simp [Away.isLocalizationElem, Away.map_mk]

/-- The inverse image of a standard open under the local morphism attached to `g`. -/
@[ega "II 2.8.1" "(2.8.1.1)"]
public theorem mapAwayHom_preimage_basicOpen (ψ : 𝒜 →+*ᵍ ℬ) {e : ℕ} (he : 0 < e) {g : A}
    (hg : g ∈ 𝒜 e) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    mapAwayHom 𝒜 ℬ ψ he hg ⁻¹ᵁ Proj.basicOpen 𝒜 f =
      (Proj.basicOpen ℬ (ψ g)).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f) := by
  have hι : (Proj.basicOpen ℬ (ψ g)).ι =
      (Proj.basicOpenIsoSpec ℬ (ψ g) (mem_of_mem 𝒜 ℬ ψ hg) he).hom ≫
        Proj.awayι ℬ (ψ g) (mem_of_mem 𝒜 ℬ ψ hg) he := by
    rw [Proj.awayι, Iso.hom_inv_id_assoc]
  rw [hι, mapAwayHom, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen ℬ (mem_of_mem 𝒜 ℬ ψ hg) he (mem_of_mem 𝒜 ℬ ψ hf) hd,
    Proj.basicOpenIsoSpec_hom, Proj.awayι_preimage_basicOpen 𝒜 hg he hf hd,
    AlgebraicGeometry.SpecMap_preimage_basicOpen]
  congr 2
  simp [map_isLocalizationElem 𝒜 ℬ ψ hg hf]

/-- **Stacks 01MY (2)**: the inverse image of a standard open of `Proj 𝒜` under the induced
morphism is the standard open of the image element. -/
@[stacks 01MY "part (2), inverse images of standard opens", ega "II 2.8.1"]
public theorem mapHom_preimage_basicOpen (ψ : 𝒜 →+*ᵍ ℬ) (f : A) (d : ℕ) (hf : f ∈ 𝒜 d)
    (hd : 0 < d) :
    mapHom 𝒜 ℬ ψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f =
      (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f) := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  obtain ⟨e, g, he, hg, hgx⟩ := (mem_mapDomain_iff 𝒜 ℬ ψ x.1).mp x.2
  have hxg : x.1 ∈ AlgebraicGeometry.Proj.basicOpen ℬ (ψ g) := by simpa using hgx
  have hyx : (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ he hg)
      ⟨x.1, hxg⟩ = x := Subtype.ext (by simp)
  have hmem : ∀ U : (mapDomain 𝒜 ℬ ψ).toScheme.Opens,
      ((⟨x.1, hxg⟩ : ↥(AlgebraicGeometry.Proj.basicOpen ℬ (ψ g))) ∈
        (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ he hg) ⁻¹ᵁ U) ↔
      x ∈ U := fun U => by
    show ((AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ he hg)
      ⟨x.1, hxg⟩ ∈ U) ↔ x ∈ U
    rw [hyx]
  have h1 : (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ he hg) ⁻¹ᵁ
        (mapHom 𝒜 ℬ ψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f) =
      (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ he hg) ⁻¹ᵁ
        ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f)) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      homOfLE_mapHom 𝒜 ℬ ψ he hg, Scheme.homOfLE_ι,
      mapAwayHom_preimage_basicOpen 𝒜 ℬ ψ he hg hd hf]
  exact ((hmem _).symm.trans (by rw [h1])).trans (hmem _)


omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- Two morphisms out of the domain of definition agree as soon as they agree on each standard
open `D₊(ψ f)` of the cover. -/
public theorem mapDomain_hom_ext (ψ : 𝒜 →+*ᵍ ℬ) {Y : Scheme.{u}}
    (p q : (mapDomain 𝒜 ℬ ψ).toScheme ⟶ Y)
    (H : ∀ (d : ℕ) (hd : 0 < d) (f : A) (hf : f ∈ 𝒜 d),
      (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf) ≫ p =
        (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf) ≫ q) :
    p = q := by
  rw [← cancel_epi ((AlgebraicGeometry.Proj ℬ).isoOfEq (mapDomain_eq_iSup 𝒜 ℬ ψ)).inv]
  refine (Scheme.Opens.iSupOpenCover
    (fun i : MapIndex 𝒜 => Proj.basicOpen ℬ (ψ i.2.1))).hom_ext _ _ fun i => ?_
  dsimp only [Scheme.Opens.iSupOpenCover]
  rw [← Category.assoc, ← Category.assoc, Scheme.isoOfEq_inv, Scheme.homOfLE_homOfLE]
  exact H i.1 i.2.2.1 i.2.1 i.2.2.2

end

section comp

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The inverse image of the domain of the inner morphism under the outer morphism is the
domain of the composite. -/
public theorem mapHom_preimage_mapDomain (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) :
    mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ =
      (mapDomain ℬ 𝒞 ψ).ι ⁻¹ᵁ mapDomain 𝒜 𝒞 (ψ.comp φ) := by
  rw [mapDomain_eq_iSup 𝒜 ℬ φ, mapDomain_eq_iSup 𝒜 𝒞 (ψ.comp φ),
    Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_iSup]
  refine iSup_congr fun i => ?_
  exact mapHom_preimage_basicOpen ℬ 𝒞 ψ (φ i.2.1) i.1
    (mem_of_mem 𝒜 ℬ φ i.2.2.2) i.2.2.1

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **Stacks 01MZ**: the domain of the morphism induced by a composite is the inverse image,
under the morphism induced by the outer homomorphism, of the domain of the inner one. -/
public theorem mapDomain_comp (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) :
    mapDomain 𝒜 𝒞 (ψ.comp φ) =
      (mapDomain ℬ 𝒞 ψ).ι ''ᵁ (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ) := by
  rw [mapHom_preimage_mapDomain, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  exact (inf_eq_right.mpr (mapDomain_comp_le 𝒜 ℬ 𝒞 φ ψ)).symm


/-- The factorization through `D₊(φ f)` of the local morphism attached to the outer
homomorphism: it is `mapAwayHom ℬ 𝒞 ψ` with the final open immersion removed. -/
public def mapAwayHomRes (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) :
    (Proj.basicOpen 𝒞 ((ψ.comp φ) f)).toScheme ⟶ (Proj.basicOpen ℬ (φ f)).toScheme :=
  Proj.basicOpenToSpec 𝒞 ((ψ.comp φ) f) ≫
    Spec.map (CommRingCat.ofHom (Away.map ψ (φ f))) ≫
      (Proj.basicOpenIsoSpec ℬ (φ f) (mem_of_mem 𝒜 ℬ φ hf) hd).inv

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `mapAwayHomRes` really is a factorization of the local morphism of the outer
homomorphism through the standard open `D₊(φ f)`. -/
public theorem mapAwayHomRes_ι (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) :
    mapAwayHomRes 𝒜 ℬ 𝒞 φ ψ hd hf ≫ (Proj.basicOpen ℬ (φ f)).ι =
      mapAwayHom ℬ 𝒞 ψ hd (mem_of_mem 𝒜 ℬ φ hf) := by
  rw [mapAwayHomRes, mapAwayHom, Proj.awayι]
  simp only [Category.assoc]
  rfl

/-- The local morphism of a composite is the composite of the local morphisms. -/
public theorem mapAwayHom_comp (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) :
    mapAwayHom 𝒜 𝒞 (ψ.comp φ) hd hf =
      mapAwayHomRes 𝒜 ℬ 𝒞 φ ψ hd hf ≫ mapAwayHom 𝒜 ℬ φ hd hf := by
  have hring : CommRingCat.ofHom (Away.map (ψ.comp φ) f) =
      CommRingCat.ofHom (Away.map φ f) ≫ CommRingCat.ofHom (Away.map ψ (φ f)) :=
    CommRingCat.hom_ext (RingHom.ext fun x => (Away.map_map φ ψ f x).symm)
  rw [mapAwayHom, mapAwayHom, mapAwayHomRes, hring,
    ← Proj.basicOpenIsoSpec_hom ℬ (φ f) (mem_of_mem 𝒜 ℬ φ hf) hd]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun m => Proj.basicOpenToSpec 𝒞 ((ψ.comp φ) f) ≫ m ≫
      Proj.awayι 𝒜 f hf hd)
    (Spec.map_comp (CommRingCat.ofHom (Away.map φ f))
      (CommRingCat.ofHom (Away.map ψ (φ f))))

end comp

end Stacks.AlgebraicGeometry.ProjTwistChain

end
