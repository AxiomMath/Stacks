module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjLocalizedRingMap
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of the structure sheaf between standard opens of Proj

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring and let `f`, `g` be homogeneous elements of positive
degree with `D₊(g) ⊆ D₊(f)`. Sections of the structure sheaf of `Proj 𝒜` over a standard open
`D₊(f)` are canonically the degree-zero localization `A₍f₎`, by Mathlib's
`AlgebraicGeometry.Proj.basicOpenIsoAway`. Under those identifications the restriction map of
the structure sheaf is the canonical map `ProjectiveSpectrum.degreeZeroRingMap : A₍f₎ → A₍g₎` of
degree-zero localizations.

## Main results

* `ProjectiveSpectrum.basicOpenIsoAway_restrict`: the restriction square commutes.
* `ProjectiveSpectrum.SpecMap_degreeZeroRingMap_awayι`: the corresponding square of schemes
  commutes, that is, the affine chart `Spec A₍g₎ → Proj 𝒜` of `D₊(g)` factors through the
  affine chart of `D₊(f)` along the map of degree-zero localizations.
* `ProjectiveSpectrum.opensRange_awayι_le`: consequently the chart of `D₊(g)` has the smaller
  open range.

## Implementation notes

Both sides of the square are compared pointwise. A section of the structure sheaf over `D₊(f)`
is a function on `D₊(f)` into the degree-zero localizations at the points, and both
identifications send a degree-zero fraction to the family of its images under
`HomogeneousLocalization.mapId`. After passing to the underlying ordinary localizations with
`HomogeneousLocalization.val`, the equality is the uniqueness part of the universal property of
`A_f`: both composites are ring maps out of `A_f` agreeing on the image of `A`.

The square of schemes is deduced from the square of rings exactly as Mathlib deduces
`AlgebraicGeometry.Proj.SpecMap_awayMap_awayι` from
`AlgebraicGeometry.Proj.awayMap_awayToSection`: transporting the ring square through
`Spec` identifies the two composites `Proj 𝒜 |_ D₊(g) ⟶ Spec A₍f₎`, and the affine charts
are the inverses of the canonical isomorphisms `Proj 𝒜 |_ D₊(f) ≅ Spec A₍f₎` composed with
the open immersions of `D₊(f)` into `Proj 𝒜`. The middle column of the source's diagram, the
`ℤ`-graded primes of `A_g`, is the space already identified with `D₊(g)` by
`AlgebraicGeometry.Proj.basicOpenIsoSpec`.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace ProjectiveSpectrum

variable {S σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒰 : ℕ → σ) [GradedRing 𝒰]

/-- The value of `HomogeneousLocalization.mapId` is the corresponding map of ordinary
localizations. -/
private theorem val_mapId {P Q : Submonoid S} (h : P ≤ Q)
    (a : HomogeneousLocalization 𝒰 P) :
    (HomogeneousLocalization.mapId 𝒰 h a).val =
      IsLocalization.map (M := P) (T := Q) _ (RingHom.id S) h a.val := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective a
  show (HomogeneousLocalization.map (GradedRingHom.id 𝒰)
      (show P ≤ Q.comap (GradedRingHom.id 𝒰) from h)
      (HomogeneousLocalization.mk c)).val = _
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk, GradedRingHom.id_apply]
  have hh : P ≤ Q.comap (RingHom.id S) := fun _ hx => h hx
  show Localization.mk _ _ =
    IsLocalization.map (Localization Q) (RingHom.id S) hh (Localization.mk _ _)
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk' (M := P)
    (S := Localization P) (T := Q) (Q := Localization Q) (hy := hh)]
  simp only [RingHom.id_apply]

/-- On standard opens of `Proj`, restriction of the structure sheaf agrees with the canonical
map of degree-zero homogeneous localizations. -/
public theorem basicOpenIsoAway_restrict (f g : S) (d e : ℕ)
    (hf : f ∈ 𝒰 d) (hd : 0 < d) (hg : g ∈ 𝒰 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒰 g ≤ ProjectiveSpectrum.basicOpen 𝒰 f) :
    CommRingCat.ofHom
        (ProjectiveSpectrum.degreeZeroRingMap 𝒰 f g
          ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom ≫
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒰 g hg he).hom =
    (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒰 f hf hd).hom ≫
      (AlgebraicGeometry.Proj 𝒰).presheaf.map (homOfLE hfg).op := by
  apply CommRingCat.hom_ext
  ext a
  apply AlgebraicGeometry.Proj.ext
  funext x
  simp only [AlgebraicGeometry.Proj.basicOpenIsoAway_hom, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply]
  apply HomogeneousLocalization.val_injective
  let y : ProjectiveSpectrum.basicOpen 𝒰 g := x
  change
    HomogeneousLocalization.val
        (((ProjectiveSpectrum.Proj.awayToSection 𝒰 g).hom
          ((ProjectiveSpectrum.degreeZeroRingMap 𝒰 f g
            ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom a)).val y) =
      HomogeneousLocalization.val
        (((ProjectiveSpectrum.Proj.awayToSection 𝒰 f).hom a).val
          ⟨y.1, hfg y.2⟩)
  dsimp [AlgebraicGeometry.Proj.awayToSection, ProjectiveSpectrum.Proj.awayToSection]
  change
    (HomogeneousLocalization.mapId 𝒰 (Submonoid.powers_le.mpr y.2)
      ((ProjectiveSpectrum.degreeZeroRingMap 𝒰 f g
        ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg) a)).val =
    (HomogeneousLocalization.mapId 𝒰
      (Submonoid.powers_le.mpr (hfg y.2)) a).val
  rw [val_mapId, val_mapId, ProjectiveSpectrum.val_degreeZeroRingMap]
  have hmap :
      (IsLocalization.map (M := Submonoid.powers g)
        (T := y.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl) (RingHom.id S)
        (Submonoid.powers_le.mpr y.2)).comp
          (ProjectiveSpectrum.localizedRingMap 𝒰 f g
            ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom =
        IsLocalization.map (M := Submonoid.powers f)
          (T := y.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl) (RingHom.id S)
          (Submonoid.powers_le.mpr (hfg y.2)) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers f)
    ext z
    simp [RingHom.comp_apply]
  simpa [RingHom.comp_apply] using congrArg (fun φ => φ (HomogeneousLocalization.val a)) hmap

/-- The inclusion `D₊(g) ⊆ D₊(f)`, read between the open subsets of the scheme `Proj 𝒜`. -/
private lemma projBasicOpen_le (f g : S)
    (hfg : ProjectiveSpectrum.basicOpen 𝒰 g ≤ ProjectiveSpectrum.basicOpen 𝒰 f) :
    AlgebraicGeometry.Proj.basicOpen 𝒰 g ≤ AlgebraicGeometry.Proj.basicOpen 𝒰 f := hfg

/-- Restriction of the structure sheaf, written through the canonical map
`A₍f₎ ⟶ Γ(Proj 𝒜, D₊(f))` of Mathlib instead of through the isomorphism it induces. -/
private theorem awayToSection_restrict (f g : S) (d e : ℕ)
    (hf : f ∈ 𝒰 d) (hd : 0 < d) (hg : g ∈ 𝒰 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒰 g ≤ ProjectiveSpectrum.basicOpen 𝒰 f) :
    CommRingCat.ofHom
        (ProjectiveSpectrum.degreeZeroRingMap 𝒰 f g
          ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom ≫
      AlgebraicGeometry.Proj.awayToSection 𝒰 g =
    AlgebraicGeometry.Proj.awayToSection 𝒰 f ≫
      (AlgebraicGeometry.Proj 𝒰).presheaf.map
        (homOfLE (projBasicOpen_le 𝒰 f g hfg)).op :=
  basicOpenIsoAway_restrict 𝒰 f g d e hf hd hg he hfg

/-- The canonical map `Proj 𝒜 |_ D₊(g) ⟶ Spec A₍g₎`, followed by the map of degree-zero
localizations, is the inclusion of `D₊(g)` into `D₊(f)` followed by the canonical map
`Proj 𝒜 |_ D₊(f) ⟶ Spec A₍f₎`. -/
@[reassoc]
private theorem basicOpenToSpec_SpecMap_degreeZeroRingMap (f g : S) (d e : ℕ)
    (hf : f ∈ 𝒰 d) (hd : 0 < d) (hg : g ∈ 𝒰 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒰 g ≤ ProjectiveSpectrum.basicOpen 𝒰 f) :
    AlgebraicGeometry.Proj.basicOpenToSpec 𝒰 g ≫
        Spec.map (CommRingCat.ofHom
          (ProjectiveSpectrum.degreeZeroRingMap 𝒰 f g
            ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom) =
      (AlgebraicGeometry.Proj 𝒰).homOfLE (projBasicOpen_le 𝒰 f g hfg) ≫
        AlgebraicGeometry.Proj.basicOpenToSpec 𝒰 f := by
  rw [AlgebraicGeometry.Proj.basicOpenToSpec, Category.assoc, ← Spec.map_comp,
    awayToSection_restrict 𝒰 f g d e hf hd hg he hfg, Spec.map_comp,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  rfl

/-- **Stacks Project, Tag 01M4.** For `D₊(g) ⊆ D₊(f)` the diagram of spaces of part (1)(f) is
commutative: the affine chart `Spec A₍g₎ ⟶ Proj 𝒜` of `D₊(g)` is the map of degree-zero
localizations `A₍f₎ → A₍g₎` followed by the affine chart of `D₊(f)`. The horizontal arrows of
the source's diagram are the isomorphisms `AlgebraicGeometry.Proj.basicOpenIsoSpec` and the
vertical arrows are open immersions. -/
@[ega "II 2.3.5" "more general"]
public theorem SpecMap_degreeZeroRingMap_awayι (f g : S) (d e : ℕ)
    (hf : f ∈ 𝒰 d) (hd : 0 < d) (hg : g ∈ 𝒰 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒰 g ≤ ProjectiveSpectrum.basicOpen 𝒰 f) :
    Spec.map (CommRingCat.ofHom
          (ProjectiveSpectrum.degreeZeroRingMap 𝒰 f g
            ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom) ≫
        AlgebraicGeometry.Proj.awayι 𝒰 f hf hd =
      AlgebraicGeometry.Proj.awayι 𝒰 g hg he := by
  rw [AlgebraicGeometry.Proj.awayι, AlgebraicGeometry.Proj.awayι, Iso.eq_inv_comp,
    AlgebraicGeometry.Proj.basicOpenIsoSpec_hom,
    basicOpenToSpec_SpecMap_degreeZeroRingMap_assoc 𝒰 f g d e hf hd hg he hfg,
    ← AlgebraicGeometry.Proj.basicOpenIsoSpec_hom 𝒰 f hf hd, Iso.hom_inv_id_assoc,
    Scheme.homOfLE_ι]

/-- **Stacks Project, Tag 01M4.** The vertical arrows of the diagram of part (1)(f) are open
immersions with nested ranges: the affine chart of `D₊(g)` has image inside the image of the
affine chart of `D₊(f)`. -/
public theorem opensRange_awayι_le (f g : S) (d e : ℕ)
    (hf : f ∈ 𝒰 d) (hd : 0 < d) (hg : g ∈ 𝒰 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒰 g ≤ ProjectiveSpectrum.basicOpen 𝒰 f) :
    (AlgebraicGeometry.Proj.awayι 𝒰 g hg he).opensRange ≤
      (AlgebraicGeometry.Proj.awayι 𝒰 f hf hd).opensRange := by
  rwa [AlgebraicGeometry.Proj.opensRange_awayι, AlgebraicGeometry.Proj.opensRange_awayι]

end ProjectiveSpectrum
