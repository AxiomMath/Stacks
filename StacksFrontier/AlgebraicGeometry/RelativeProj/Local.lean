module

public import StacksFrontier.AlgebraicGeometry.ProjMapData.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local charts of the relative homogeneous spectrum

Tag 01NQ builds `Proj_S(𝒜) ⟶ S` by glueing the schemes `Proj Γ(U, 𝒜)` over the affine opens `U`
of `S`. This file constructs those charts together with their structure morphisms to `U` and to
`S`, and the transition morphism between the charts of a nested pair of affine opens, and proves
that the transitions commute with the structure morphisms.

The general statements about an arbitrary graded ring homomorphism are stated for an arbitrary
`ψ : 𝒜 →+*ᵍ ℬ` that happens to be everywhere defined, which is the only hypothesis they need.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProj.zeroHom`: the degree-zero part `𝒜 0 →+* ℬ 0` of a graded
  ring homomorphism.
* `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop`: the morphism `Proj ℬ ⟶ Proj 𝒜` induced by
  an everywhere-defined graded ring homomorphism.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.projOver`: the chart `Proj Γ(U, 𝒜)`.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.strZero`: the structure morphism of the
  base, corestricted to degree zero.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.toOpen` and
  `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.toBase`: the structure morphism of the
  chart over `U`, to `U` and to `S`.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.transition`: the transition morphism
  between the charts of a nested pair of affine opens.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.resMap`: the transition morphism for a
  basic open inclusion, which needs no hypothesis.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProj.mapHom_toSpecZero` and
  `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_toSpecZero`: the morphism induced by `ψ` is
  compatible with the structure morphisms `Proj ⟶ Spec` of the degree-zero parts. This is the
  commuting square underlying Tags 01N2 and 01NO.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.transition_toBase`: the transition
  morphisms commute with the structure morphisms to `S`.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.transition_toOpen`: hence the square over
  the inclusion of affine opens commutes. This is the *commutativity* half of the cartesian
  square of Tag 01NO.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.transition_id` and
  `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.ι_transition`: the transition over the
  identity inclusion is the identity, and the local description of a transition on a standard
  open.

## Implementation notes

`toBase`, not `toOpen`, is the morphism the proofs go through: it ends at `S`, so the triangle
`transition ≫ toBase V = toBase U` has no `Scheme.homOfLE` in it and reduces, through
`AlgebraicGeometry.IsAffineOpen.map_fromSpec`, to a single identity of ring maps. The square
`transition ≫ toOpen V = toOpen U ≫ S.homOfLE h` is then obtained by cancelling the
monomorphism `V.toOpens.ι`, rather than proved again.

Two transparency notes.

* `AlgebraicGeometry.Proj.toSpecZero` targets `Spec (.of <| 𝒜 0)`, so the degree-zero structure
  morphism has to be corestricted to `𝒜.grading U 0` rather than left as a map into
  `𝒜.ring U`. The corestriction is `GradedRing.projZeroRingHom'`, which projects an arbitrary
  element to its degree-zero component; on an element that already lies in degree zero this is
  the identity, which is the content of `projZeroRingHom'_coe_of_mem` and is what every
  compatibility proof below reduces to.
* The degree of a homogeneous element is an implicit argument of `Proj.awayι` occurring only
  inside proofs, so `ι_transition` takes the degree as a free variable rather than inferring it,
  exactly as `Stacks.AlgebraicGeometry.ProjTwistChain.homOfLE_mapAwayHom` does.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)

Transitivity of the transition morphisms (Tag 01NP) is not here but in
`StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison`, where it is read off a comparison
with Mathlib's `AlgebraicGeometry.Proj.map`.

## Not done here

The charts are *not* glued. Glueing them needs the squares of `transition_toOpen` to be
cartesian, i.e. Tag 01NO proper, which is Tag 01N2 for a localization at a degree-zero element
and is not proved: see the report accompanying this file. Concretely, what is missing is that
`AlgebraicGeometry.HomogeneousLocalization.Away ℬ (ψ f)` is the localization of
`AlgebraicGeometry.HomogeneousLocalization.Away 𝒜 f` away from the image of the degree-zero
element `g`, from which `mapHomOfTop` would be an open immersion with image the preimage of
`D(g)` and the squares would be cartesian. The comparison maps `θ` on the twists `𝒪(n)` are
likewise not constructed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.RelativeProj

universe u w w'

section GradeZero

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Projecting to the degree-zero component is the identity on an element that already lies in
degree zero. -/
public theorem projZeroRingHom'_coe_of_mem {a : A} (ha : a ∈ 𝒜 0) :
    (GradedRing.projZeroRingHom' 𝒜 a : A) = a := by
  rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply]
  exact DirectSum.decompose_of_mem_same 𝒜 ha

end GradeZero

section Zero

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- The degree-zero part of a graded ring homomorphism. -/
public def zeroHom (ψ : 𝒜 →+*ᵍ ℬ) : 𝒜 0 →+* ℬ 0 :=
  (GradedRing.projZeroRingHom' ℬ).comp (ψ.toRingHom.comp (algebraMap (𝒜 0) A))

/-- The degree-zero part of `ψ` agrees with `ψ` on elements of degree zero. -/
@[simp]
public theorem coe_zeroHom_apply (ψ : 𝒜 →+*ᵍ ℬ) (a : 𝒜 0) : (zeroHom 𝒜 ℬ ψ a : B) = ψ a :=
  projZeroRingHom'_coe_of_mem ℬ (ψ.map_mem a.2)

/-- The degree-zero part of `ψ` is compatible with the maps of the degree-zero parts into the
degree-zero localizations. -/
public theorem awayMap_comp_fromZeroRingHom (ψ : 𝒜 →+*ᵍ ℬ) (f : A) :
    (Away.map ψ f).comp (fromZeroRingHom 𝒜 (Submonoid.powers f)) =
      (fromZeroRingHom ℬ (Submonoid.powers (ψ f))).comp (zeroHom 𝒜 ℬ ψ) := by
  ext a
  change (Away.map ψ f (HomogeneousLocalization.mk ⟨0, a, 1, Submonoid.one_mem _⟩)).val =
    (HomogeneousLocalization.mk
      (⟨0, zeroHom 𝒜 ℬ ψ a, 1, Submonoid.one_mem _⟩ :
        HomogeneousLocalization.NumDenSameDeg ℬ (Submonoid.powers (ψ f)))).val
  rw [Away.map, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk]
  congr 1
  · exact (coe_zeroHom_apply 𝒜 ℬ ψ a).symm
  · exact Subtype.ext (map_one ψ)

/-- The local morphism attached to a positive-degree homogeneous `f` is compatible with the
structure morphisms to the spectra of the degree-zero parts. -/
public theorem mapAwayHom_toSpecZero (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) :
    mapAwayHom 𝒜 ℬ ψ hd hf ≫ Proj.toSpecZero 𝒜 =
      (Proj.basicOpen ℬ (ψ f)).ι ≫ Proj.toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom (zeroHom 𝒜 ℬ ψ)) := by
  rw [mapAwayHom, ← ProjTwistChain.basicOpenToSpec_comp_awayι ℬ hd (mem_of_mem 𝒜 ℬ ψ hf)]
  simp only [Category.assoc, Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, awayMap_comp_fromZeroRingHom]

/-- **The commuting square of Tags 01N2 and 01NO.** The morphism induced by a graded ring
homomorphism is compatible with the structure morphisms of the two projective spectra to the
spectra of their degree-zero parts. -/
@[ega "II 2.8.5" "Case A' = S'_0"]
public theorem mapHom_toSpecZero (ψ : 𝒜 →+*ᵍ ℬ) :
    mapHom 𝒜 ℬ ψ ≫ Proj.toSpecZero 𝒜 =
      (mapDomain 𝒜 ℬ ψ).ι ≫ Proj.toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom (zeroHom 𝒜 ℬ ψ)) := by
  refine mapDomain_hom_ext 𝒜 ℬ ψ _ _ fun d hd f hf => ?_
  rw [← Category.assoc, homOfLE_mapHom 𝒜 ℬ ψ hd hf, ← Category.assoc, Scheme.homOfLE_ι,
    mapAwayHom_toSpecZero 𝒜 ℬ ψ hd hf]

/-- The morphism `Proj ℬ ⟶ Proj 𝒜` induced by a graded ring homomorphism that is defined
everywhere. -/
public def mapHomOfTop (ψ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤) :
    AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜 :=
  (Scheme.topIso _).inv ≫ ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom ≫ mapHom 𝒜 ℬ ψ

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The isomorphism `Proj ℬ ≅ U(ψ)` used to define `mapHomOfTop` is a section of the inclusion of
the domain of definition. -/
public theorem topIso_inv_isoOfEq_hom_ι (ψ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤) :
    (Scheme.topIso _).inv ≫ ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom ≫
      (mapDomain 𝒜 ℬ ψ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ) := by
  rw [Scheme.isoOfEq_hom_ι]
  simp

/-- On the standard open `D₊(ψ f)`, the everywhere-defined morphism `mapHomOfTop` restricts to
the local morphism `mapAwayHom` attached to `f`. -/
@[reassoc]
public theorem ι_mapHomOfTop (ψ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤) {d : ℕ} (hd : 0 < d)
    {f : A} (hf : f ∈ 𝒜 d) :
    (Proj.basicOpen ℬ (ψ f)).ι ≫ mapHomOfTop 𝒜 ℬ ψ hdom = mapAwayHom 𝒜 ℬ ψ hd hf := by
  have h1 : (Proj.basicOpen ℬ (ψ f)).ι ≫ (Scheme.topIso _).inv ≫
      ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom =
      (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf) := by
    rw [← cancel_mono (Scheme.Opens.ι _), Scheme.homOfLE_ι, Category.assoc, Category.assoc,
      topIso_inv_isoOfEq_hom_ι 𝒜 ℬ ψ hdom, Category.comp_id]
  rw [mapHomOfTop, reassoc_of% h1, homOfLE_mapHom 𝒜 ℬ ψ hd hf]

/-- **The commuting square of Tag 01NO**, for an everywhere-defined graded ring homomorphism. -/
@[reassoc]
public theorem mapHomOfTop_toSpecZero (ψ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤) :
    mapHomOfTop 𝒜 ℬ ψ hdom ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (zeroHom 𝒜 ℬ ψ)) := by
  rw [mapHomOfTop, Category.assoc, Category.assoc, mapHom_toSpecZero 𝒜 ℬ ψ,
    ← Category.assoc _ _ (Proj.toSpecZero ℬ ≫ _), ← Category.assoc, ← Category.assoc,
    topIso_inv_isoOfEq_hom_ι 𝒜 ℬ ψ hdom, Category.id_comp]

end Zero

section Id

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The local morphism attached to the identity graded ring homomorphism is the inclusion of the
standard open. -/
public theorem mapAwayHom_id {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    mapAwayHom 𝒜 𝒜 (GradedRingHom.id 𝒜) hd hf = (Proj.basicOpen 𝒜 f).ι := by
  rw [mapAwayHom]
  simp only [Away.map_id]
  change Proj.basicOpenToSpec 𝒜 f ≫ Spec.map (CommRingCat.ofHom (RingHom.id (Away 𝒜 f))) ≫
    Proj.awayι 𝒜 f hf hd = (Proj.basicOpen 𝒜 f).ι
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  exact ProjTwistChain.basicOpenToSpec_comp_awayι 𝒜 hd hf

/-- The degree-zero part of the identity is the identity. -/
@[simp]
public theorem zeroHom_id : zeroHom 𝒜 𝒜 (GradedRingHom.id 𝒜) = RingHom.id (𝒜 0) := by
  ext a
  exact coe_zeroHom_apply 𝒜 𝒜 (GradedRingHom.id 𝒜) a

end Id

namespace GradedAlgebra

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S)

/-- The chart of the relative homogeneous spectrum over an affine open `U` of the base: the
absolute `Proj` of the graded ring of sections of `𝒜` over `U`.

An `abbrev`, so that every lemma about `AlgebraicGeometry.Proj` applies to it without a
transparency barrier. -/
@[ega "II 3.1.1" "partial"]
public abbrev projOver (U : S.AffineZariskiSite) : Scheme.{u} :=
  AlgebraicGeometry.Proj (𝒜.grading U)

/-- The structure morphism of the base, corestricted to the degree-zero part. -/
public def strZero (U : S.AffineZariskiSite) :
    Γ(S, U.toOpens) ⟶ CommRingCat.of (𝒜.grading U 0) :=
  CommRingCat.ofHom ((GradedRing.projZeroRingHom' (𝒜.grading U)).comp (𝒜.str U).hom)

/-- The degree-zero corestriction of the structure morphism agrees with the structure morphism. -/
@[simp]
public theorem coe_strZero_apply (U : S.AffineZariskiSite) (r : Γ(S, U.toOpens)) :
    (𝒜.strZero U r : 𝒜.ring U) = 𝒜.str U r :=
  projZeroRingHom'_coe_of_mem (𝒜.grading U) (𝒜.str_mem U r)

/-- The structure morphism of the chart over `U`, to the affine open `U` itself. -/
public def toOpen (U : S.AffineZariskiSite) : 𝒜.projOver U ⟶ U.toOpens.toScheme :=
  Proj.toSpecZero (𝒜.grading U) ≫ Spec.map (𝒜.strZero U) ≫ U.2.isoSpec.inv

/-- The structure morphism of the chart over `U`, to the base scheme `S`. -/
public def toBase (U : S.AffineZariskiSite) : 𝒜.projOver U ⟶ S :=
  Proj.toSpecZero (𝒜.grading U) ≫ Spec.map (𝒜.strZero U) ≫ U.2.fromSpec

/-- The structure morphism of the chart over `U` to `U`, followed by the inclusion of `U` into
`S`, is the structure morphism of the chart to `S`. -/
@[reassoc (attr := simp)]
public theorem toOpen_ι (U : S.AffineZariskiSite) :
    𝒜.toOpen U ≫ U.toOpens.ι = 𝒜.toBase U := by
  rw [toOpen, toBase]
  simp only [Category.assoc, IsAffineOpen.isoSpec_inv_ι]

/-- The transition morphism between the charts of a nested pair of affine opens, given that the
restriction map induces an everywhere-defined morphism of projective spectra. -/
public def transition {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
    (hdom : mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h) = ⊤) :
    𝒜.projOver U ⟶ 𝒜.projOver V :=
  mapHomOfTop (𝒜.grading V) (𝒜.grading U) (𝒜.res h) hdom

/-- The transition morphism along a *basic* open inclusion of affine opens. Quasi-coherence makes
this unconditional; see `GradedAlgebra.mapDomain_res_eq_top`. Basic open inclusions are exactly
the morphisms of `AlgebraicGeometry.Scheme.AffineZariskiSite`. -/
@[ega "II 3.1.1" "special case"]
public def resMap (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    𝒜.projOver (U.basicOpen f) ⟶ 𝒜.projOver U :=
  𝒜.transition (U := U.basicOpen f) (V := U) (S.basicOpen_le f) (𝒜.mapDomain_res_eq_top U f)

/-- The transition morphism over the identity inclusion is the identity. -/
public theorem transition_id (U : S.AffineZariskiSite)
    (hdom : mapDomain (𝒜.grading U) (𝒜.grading U) (𝒜.res (le_refl U.toOpens)) = ⊤) :
    𝒜.transition (le_refl U.toOpens) hdom = 𝟙 (𝒜.projOver U) := by
  have hmap : mapHom (𝒜.grading U) (𝒜.grading U) (𝒜.res (le_refl U.toOpens)) =
      (mapDomain (𝒜.grading U) (𝒜.grading U) (𝒜.res (le_refl U.toOpens))).ι := by
    refine mapDomain_hom_ext _ _ _ _ _ fun d hd f hf => ?_
    rw [homOfLE_mapHom _ _ _ hd hf, Scheme.homOfLE_ι, 𝒜.res_id U]
    exact mapAwayHom_id (𝒜.grading U) hd hf
  rw [transition, mapHomOfTop, hmap, topIso_inv_isoOfEq_hom_ι _ _ _ hdom]

/-- The local description of a transition morphism: on the standard open `D₊(ψ f)` it is the
morphism of affine schemes induced by the map of degree-zero localizations. -/
public theorem ι_transition {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
    (hdom : mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h) = ⊤) {d : ℕ} (hd : 0 < d)
    {f : 𝒜.ring V} (hf : f ∈ 𝒜.grading V d) :
    (Proj.basicOpen (𝒜.grading U) (𝒜.res h f)).ι ≫ 𝒜.transition h hdom =
      mapAwayHom (𝒜.grading V) (𝒜.grading U) (𝒜.res h) hd hf :=
  ι_mapHomOfTop (𝒜.grading V) (𝒜.grading U) (𝒜.res h) hdom hd hf

/-- Restriction of sections is compatible with the degree-zero structure morphisms. -/
public theorem presheaf_map_comp_strZero {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens) :
    S.presheaf.map (homOfLE h).op ≫ 𝒜.strZero U =
      𝒜.strZero V ≫ CommRingCat.ofHom
        (zeroHom (𝒜.grading V) (𝒜.grading U) (𝒜.res h)) := by
  ext r
  calc ((𝒜.strZero U ((S.presheaf.map (homOfLE h).op) r) : 𝒜.grading U 0) : 𝒜.ring U)
      = 𝒜.str U ((S.presheaf.map (homOfLE h).op) r) := 𝒜.coe_strZero_apply U _
    _ = 𝒜.res h (𝒜.str V r) := (𝒜.res_str h r).symm
    _ = ((zeroHom (𝒜.grading V) (𝒜.grading U) (𝒜.res h) (𝒜.strZero V r) :
          𝒜.grading U 0) : 𝒜.ring U) := by
        rw [coe_zeroHom_apply, 𝒜.coe_strZero_apply V r]

/-- **The structure morphisms are compatible with the transitions.** This is the commuting
triangle over the base that the relative glueing of Tag 01NQ asks for. -/
@[reassoc (attr := simp)]
public theorem transition_toBase {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
    (hdom : mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h) = ⊤) :
    𝒜.transition h hdom ≫ 𝒜.toBase V = 𝒜.toBase U := by
  rw [transition, toBase, toBase, mapHomOfTop_toSpecZero_assoc]
  simp only [← Spec.map_comp_assoc]
  rw [← presheaf_map_comp_strZero 𝒜 h, Spec.map_comp_assoc,
    V.2.map_fromSpec U.2 (homOfLE h).op]

/-- **The square of Tag 01NO commutes.** -/
public theorem transition_toOpen {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
    (hdom : mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h) = ⊤) :
    𝒜.transition h hdom ≫ 𝒜.toOpen V = 𝒜.toOpen U ≫ S.homOfLE h := by
  rw [← cancel_mono V.toOpens.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
    toOpen_ι, toOpen_ι, transition_toBase]

/-- The transition along a basic open inclusion is compatible with the structure morphisms. -/
@[reassoc (attr := simp)]
public theorem resMap_toBase (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    𝒜.resMap U f ≫ 𝒜.toBase U = 𝒜.toBase (U.basicOpen f) :=
  𝒜.transition_toBase (U := U.basicOpen f) (V := U) (S.basicOpen_le f) _

end GradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProj

end
