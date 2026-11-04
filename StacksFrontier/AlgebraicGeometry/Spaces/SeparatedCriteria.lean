module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Separatedness of a representable morphism of algebraic spaces, sections and graphs

Separatedness of a morphism of algebraic spaces over a scheme `S` is a property of its
relative diagonal.  For a *representable* morphism there is a second, more elementary
description: every represented base change of it is a separated morphism of schemes.  The same
holds for quasi-separatedness, and a representable morphism is always locally separated.  This
is Stacks 03KY.

The relative-diagonal description also governs the behaviour of a section `s` of a morphism
`p : P ⟶ V`: such a section is always representable, locally of finite type, locally
quasi-finite, separated and a monomorphism, and it is an immersion, a closed immersion or
quasi-compact as soon as `p` is locally separated, separated or quasi-separated.  This is
Stacks 03KP.  The graph of a morphism `f : X ⟶ Y` over `Z` is a section of the first
projection of `X ×[Z] Y`, so all four parts of Stacks 03KO follow: the graph is always
representable, locally of finite type, locally quasi-finite, separated and a monomorphism, and
it is an immersion, a closed immersion or quasi-compact as soon as `Y ⟶ Z` is locally
separated, separated or quasi-separated.

## Main definitions

* `AlgebraicGeometry.Space.arrowIsoMapDescSection` presents a section of `p : P ⟶ V` as the
  comparison `V ×[P] P ⟶ V ×[V] P` of two fibre products.
* `AlgebraicGeometry.Space.graph` is the graph `X ⟶ X ×[Z] Y` of a morphism `f : X ⟶ Y` of
  algebraic spaces over `S`, relative to a further morphism `g : Y ⟶ Z`.

## Main results

* `AlgebraicGeometry.Space.isSeparated_arrow_mk_iso_iff` and
  `AlgebraicGeometry.Space.isLocallySeparated_arrow_mk_iso_iff`: separatedness and local
  separatedness of a morphism of algebraic spaces over `S` are invariant under an isomorphism
  in the arrow category.
* `AlgebraicGeometry.Space.isSeparated_iff_presheaf`: a representable morphism of algebraic
  spaces over `S` is separated exactly when the relatively representable form of
  `AlgebraicGeometry.IsSeparated` holds for it, that is, when every represented base change
  of it is a separated morphism of schemes.
* `AlgebraicGeometry.Space.isQuasiSeparated_iff_presheaf`: the same for quasi-separatedness,
  with `AlgebraicGeometry.QuasiSeparated` in place of `AlgebraicGeometry.IsSeparated`.
* `AlgebraicGeometry.Space.isLocallySeparated_yoneda_map` and
  `AlgebraicGeometry.Space.isLocallySeparated_of_relativelyRepresentable`: a represented
  morphism of algebraic spaces over `S` is locally separated, and so is any representable one.
* `AlgebraicGeometry.Space.isQuasiSeparated_arrow_mk_iso_iff`: quasi-separatedness of a
  morphism of algebraic spaces over `S` is invariant under an isomorphism in the arrow
  category.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_section`,
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_section`,
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_section`,
  `AlgebraicGeometry.Space.isSeparated_of_section` and
  `AlgebraicGeometry.Space.mono_of_section`: a section of a morphism of algebraic spaces over
  `S` is representable, locally of finite type, locally quasi-finite, separated and a
  monomorphism, with no hypothesis on the morphism.
* `AlgebraicGeometry.Space.isImmersion_of_isLocallySeparated_of_section`,
  `AlgebraicGeometry.Space.isClosedImmersion_of_isSeparated_of_section` and
  `AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiSeparated_of_section`: a section of a
  locally separated, separated or quasi-separated morphism is an immersion, a closed immersion
  or quasi-compact.
* `AlgebraicGeometry.Space.relativelyRepresentable_graph`,
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_graph`,
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_graph`,
  `AlgebraicGeometry.Space.isSeparated_graph` and `AlgebraicGeometry.Space.mono_graph`: part
  (1) of Stacks 03KO, the graph of `f : X ⟶ Y` over `Z` is representable, locally of finite
  type, locally quasi-finite, separated and a monomorphism, with no hypothesis on `Y ⟶ Z`.
* `AlgebraicGeometry.Space.isImmersion_graph_of_isLocallySeparated`,
  `AlgebraicGeometry.Space.isClosedImmersion_graph_of_isSeparated` and
  `AlgebraicGeometry.Space.isQuasiCompact_graph_of_isQuasiSeparated`: parts (2), (3) and (4)
  of Stacks 03KO, the graph of `f : X ⟶ Y` over `Z` is an immersion, a closed immersion or
  quasi-compact when `Y ⟶ Z` is locally separated, separated or quasi-separated.

## Implementation notes

Separatedness of a morphism with algebraic source can be tested on all represented base
changes, which is `AlgebraicGeometry.Space.isSeparated_iff_forall_pullback`, the equivalence
of conditions (1) and (2) of Stacks 03KM.  For a representable morphism each such base change
is isomorphic, as an object of the arrow category, to the Yoneda image of a morphism of the
site, and separatedness of a Yoneda image is separatedness of the underlying morphism of
schemes by `AlgebraicGeometry.Space.isSeparated_yoneda_map_iff`.  So the two conditions agree
termwise and the equivalence is the conjunction of the two transports.

The algebraic-space hypothesis on the target is not used; it is retained, with an underscore,
so that the statement is the one of Stacks 03KY.  The quasi-separated half runs the same way,
over `AlgebraicGeometry.Space.isQuasiSeparated_iff_forall_pullback` and
`AlgebraicGeometry.Space.isQuasiSeparated_yoneda_map_iff`; there the algebraicity of neither
source nor target is needed, because quasi-separatedness is quasi-compactness of the relative
diagonal in the sense of Stacks 03HE and that is already a condition on base changes.

Local separatedness of a representable morphism needs no hypothesis beyond representability:
the relative diagonal of a morphism of schemes is an immersion, which is Stacks 01KJ and is
`AlgebraicGeometry.IsImmersion.instIsImmersionPullbackDiagonal` in Mathlib, so each represented
base change is locally separated and Stacks 03KM assembles them.  Transporting
quasi-separatedness along an isomorphism of arrows cannot reuse
`CategoryTheory.MorphismProperty.arrow_mk_iso_iff` for the relative diagonal of a
`CategoryTheory.MorphismProperty` out of the box, because Stacks 03HE quantifies over morphisms
from quasi-compact algebraic spaces rather than over represented base changes; what is used
instead is that quasi-compactness in that sense is stable under base change, which is
`AlgebraicGeometry.Space.IsQuasiCompact.of_isPullback`.

A section `s` of `p : P ⟶ V` is the comparison `V ×[P] P ⟶ V ×[V] P` of two fibre products,
read through the isomorphism `V ×[P] P ≅ V` coming from the identity leg and the isomorphism
`V ×[V] P ≅ P` coming from `s ≫ p = 𝟙 V`; that identification of arrows is
`AlgebraicGeometry.Space.arrowIsoMapDescSection`.  Each assertion of Stacks 03KP is therefore
the corresponding assertion of Stacks 03KN for that comparison, transported along the
isomorphism of arrows — along the cartesian square it provides, in the case of quasi-compactness,
which is not phrased as a `CategoryTheory.MorphismProperty`.  Two of the assertions are proved
differently: a section is a split monomorphism, so being a monomorphism needs no transport, and
being locally of finite type and locally quasi-finite are étale-chart conditions, obtained from
the represented-base-change form by the half of Stacks 03MJ proved in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartBridge.lean`.

Representability, local finite type and local quasi-finiteness come from the diagonal of `P`
and so need `P` to be an algebraic space; the five remaining assertions need no algebraicity at
all, and the source's hypothesis that `P` and `V` are algebraic spaces is dropped wherever it is
unused.  The graph of `f` over `Z` is a section of the first projection of `X ×[Z] Y`, which is
a base change of `g` up to the symmetry of a fibre product, so separatedness of `g` is exactly
what the section statement needs.  That is how Stacks 03KO is deduced here; the source instead
deduces it from Stacks 03KN applied to `X = X ×_Y Y → X ×_T Y`, which is the same comparison of
fibre products.  For parts (2) and (3) the separation hypothesis is transported along an
isomorphism of arrows; part (4) is the one assertion of Stacks 03KP whose conclusion is not a
`CategoryTheory.MorphismProperty`, so there the *graph* is moved across the symmetry instead
and quasi-compactness is read back along the resulting isomorphism.  The three assertions of
part (1) that go through the diagonal of the total space need `X ×[Z] Y` to be an algebraic
space, which is `AlgebraicGeometry.isAlgebraicSpace_pullback` applied to the three algebraic
spaces of the source's hypotheses.

## References

* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
* [Stacks Project, Tag 03KO](https://stacks.math.columbia.edu/tag/03KO)
* [Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Separatedness of a morphism of algebraic spaces over `S` is invariant under an
isomorphism in the arrow category.** Separatedness is the relative diagonal form of a
relatively representable morphism property, and such a property is stable under base change,
hence respects isomorphisms. -/
theorem isSeparated_arrow_mk_iso_iff {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ G} {p' : F' ⟶ G'} (e : Arrow.mk p ≅ Arrow.mk p') :
    IsSeparated B S hS p ↔ IsSeparated B S hS p' :=
  MorphismProperty.arrow_mk_iso_iff
    (MorphismProperty.diagonal (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))) e

/-- **Local separatedness of a morphism of algebraic spaces over `S` is invariant under an
isomorphism in the arrow category.** Local separatedness is the relative diagonal form of a
relatively representable morphism property, and such a property is stable under base change,
hence respects isomorphisms. -/
theorem isLocallySeparated_arrow_mk_iso_iff {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ G} {p' : F' ⟶ G'} (e : Arrow.mk p ≅ Arrow.mk p') :
    IsLocallySeparated B S hS p ↔ IsLocallySeparated B S hS p' :=
  MorphismProperty.arrow_mk_iso_iff
    (MorphismProperty.diagonal (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))) e

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A represented base change of a representable `f` is the Yoneda image of a morphism of the
site. -/
private noncomputable def arrowIsoYonedaMapSnd {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {T : BigFppfOver B S hS} (g : yoneda.obj T ⟶ Y) :
    Arrow.mk (yoneda.map (hf.snd g)) ≅ Arrow.mk (pullback.snd f g) :=
  Arrow.isoMk (hf.isPullback g).isoPullback (Iso.refl _) (by simp)

/-- **Stacks 03KY, part (2), the separated case.** A representable morphism of algebraic
spaces over `S` is separated exactly when all of its represented base changes are separated
morphisms of schemes.

Both sides are conditions on the represented base changes of `f`: the left-hand side because
separatedness of a morphism with algebraic source can be tested on them, by Stacks 03KM, and
the right-hand side by definition.  Termwise the two agree because a represented base change
of `f` is the Yoneda image of a morphism of the site and separatedness of a Yoneda image is
separatedness of the underlying morphism of schemes. -/
theorem isSeparated_iff_presheaf (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (_hY : IsAlgebraicSpace B S hS Y) (hf : yoneda.relativelyRepresentable f) :
    IsSeparated B S hS f ↔
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f := by
  let _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  rw [isSeparated_iff_forall_pullback B S hS hX f]
  refine ⟨fun h ↦ MorphismProperty.relative_of_snd hf fun T g ↦ ?_, fun h T g ↦ ?_⟩
  · exact (isSeparated_yoneda_map_iff B S hS _).1
      ((isSeparated_arrow_mk_iso_iff B S hS (arrowIsoYonedaMapSnd B S hS hf g)).2 (h T g))
  · exact (isSeparated_arrow_mk_iso_iff B S hS (arrowIsoYonedaMapSnd B S hS h.rep g)).1
      ((isSeparated_yoneda_map_iff B S hS _).2 (h.property_snd g))

/-- **A represented morphism of algebraic spaces over `S` is locally separated.** Yoneda
preserves fibre products, so it carries the relative diagonal of a morphism `m` of the site to
the relative diagonal of `yoneda.map m`, up to the comparison isomorphism; the represented
reading of the immersion property of that diagonal is then the immersion property of the
diagonal of the underlying morphism of schemes, and the diagonal of a morphism of schemes is
always an immersion. -/
@[ega "IV 16.3.1" "special case"]
theorem isLocallySeparated_yoneda_map {a b : BigFppfOver B S hS} (m : a ⟶ b) :
    IsLocallySeparated B S hS (yoneda.map m) := by
  have hyoneda : IsLocallySeparated B S hS (yoneda.map m) ↔
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (pullback.diagonal m)) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf _
      (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) m m).hom,
      Stacks.SeparationLocal.map_pullback_diagonal]
  have _ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hscheme : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.diagonal m)) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) _
      (PreservesPullback.iso (BigFppfOver.toScheme B S hS) m m).hom,
      Stacks.SeparationLocal.map_pullback_diagonal]
    infer_instance
  exact hyoneda.2 ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
    (pullback.diagonal m)).2 hscheme)

/-- **Stacks 03KY, part (1).** A representable morphism of algebraic spaces over `S` is
locally separated.

Local separatedness of a morphism with algebraic source can be tested on its represented base
changes, by Stacks 03KM, and for a representable morphism each of those is the Yoneda image of
a morphism of the site, hence locally separated by
`AlgebraicGeometry.Space.isLocallySeparated_yoneda_map`. -/
theorem isLocallySeparated_of_relativelyRepresentable (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (hf : yoneda.relativelyRepresentable f) : IsLocallySeparated B S hS f := by
  rw [isLocallySeparated_iff_forall_pullback B S hS hX f]
  exact fun T g ↦ (isLocallySeparated_arrow_mk_iso_iff B S hS (arrowIsoYonedaMapSnd B S hS hf g)).1
    (isLocallySeparated_yoneda_map B S hS (hf.snd g))

/-- **Quasi-separatedness of a morphism of algebraic spaces over `S` is invariant under an
isomorphism in the arrow category.** Quasi-separatedness is the relative diagonal form of
quasi-compactness of morphisms of presheaves in the sense of Stacks 03HE; that property is
stable under base change, hence so is its relative diagonal form, and a property stable under
base change respects isomorphisms. -/
theorem isQuasiSeparated_arrow_mk_iso_iff {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ G} {p' : F' ⟶ G'} (e : Arrow.mk p ≅ Arrow.mk p') :
    IsQuasiSeparated B S hS p ↔ IsQuasiSeparated B S hS p' :=
  have : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (q : F ⟶ G) => IsQuasiCompact B S hS q) :=
    ⟨fun sq hg => IsQuasiCompact.of_isPullback B S hS sq hg⟩
  have : MorphismProperty.RespectsIso
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (q : F ⟶ G) => IsQuasiCompact B S hS q) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.diagonal
        (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (q : F ⟶ G) =>
          IsQuasiCompact B S hS q)) :=
    MorphismProperty.IsStableUnderBaseChange.diagonal
  have : MorphismProperty.RespectsIso
      (MorphismProperty.diagonal
        (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (q : F ⟶ G) =>
          IsQuasiCompact B S hS q)) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  MorphismProperty.arrow_mk_iso_iff
    (MorphismProperty.diagonal
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (q : F ⟶ G) => IsQuasiCompact B S hS q)) e

/-- **Stacks 03KY, part (2), the quasi-separated case.** A representable morphism of algebraic
spaces over `S` is quasi-separated exactly when all of its represented base changes are
quasi-separated morphisms of schemes.

Both sides are conditions on the represented base changes of `f`: the left-hand side because
quasi-separatedness of a morphism can be tested on them, by Stacks 03KM, and the right-hand
side by definition.  Termwise the two agree because a represented base change of `f` is the
Yoneda image of a morphism of the site and quasi-separatedness of a Yoneda image is
quasi-separatedness of the underlying morphism of schemes. -/
theorem isQuasiSeparated_iff_presheaf (f : X ⟶ Y) (_hX : IsAlgebraicSpace B S hS X)
    (_hY : IsAlgebraicSpace B S hS Y) (hf : yoneda.relativelyRepresentable f) :
    IsQuasiSeparated B S hS f ↔
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.QuasiSeparated.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f := by
  let _ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.QuasiSeparated.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.QuasiSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  rw [isQuasiSeparated_iff_forall_pullback B S hS f]
  refine ⟨fun h ↦ MorphismProperty.relative_of_snd hf fun T g ↦ ?_, fun h T g ↦ ?_⟩
  · exact (isQuasiSeparated_yoneda_map_iff B S hS _).1
      ((isQuasiSeparated_arrow_mk_iso_iff B S hS (arrowIsoYonedaMapSnd B S hS hf g)).2 (h T g))
  · exact (isQuasiSeparated_arrow_mk_iso_iff B S hS (arrowIsoYonedaMapSnd B S hS h.rep g)).1
      ((isQuasiSeparated_yoneda_map_iff B S hS _).2 (h.property_snd g))

/-! ### Sections and graphs -/

section Graph

variable {P V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A section `s` of `p : P ⟶ V` is the comparison `V ×[P] P ⟶ V ×[V] P` of two fibre products:
the identity leg identifies `V ×[P] P` with `V`, and `s ≫ p = 𝟙 V` identifies `V ×[V] P` with
`P`. -/
noncomputable def arrowIsoMapDescSection (p : P ⟶ V) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    Arrow.mk (pullback.mapDesc s (𝟙 P) p) ≅ Arrow.mk s :=
  haveI : IsIso (pullback.fst s (𝟙 P)) := inferInstance
  haveI : IsIso (s ≫ p) := hs ▸ inferInstance
  haveI : IsIso (pullback.snd (s ≫ p) ((𝟙 P) ≫ p)) := inferInstance
  Arrow.isoMk (asIso (pullback.fst s (𝟙 P))) (asIso (pullback.snd (s ≫ p) ((𝟙 P) ≫ p)))
    (by
      change pullback.fst s (𝟙 P) ≫ s = _
      rw [pullback.condition]
      dsimp [pullback.mapDesc, pullback.map]
      rw [pullback.lift_snd])

/-- **Stacks 03KP, part (1).** A section of a morphism of algebraic spaces over `S` is a
monomorphism, being a split monomorphism. -/
@[stacks 03KP "part (1): monomorphism"]
theorem mono_of_section (p : P ⟶ V) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) : Mono s :=
  have : IsSplitMono s := IsSplitMono.mk' ⟨p, hs⟩
  inferInstance

/-- **Stacks 03KP, part (1).** A section of a morphism of algebraic spaces over `S` is
separated. -/
@[stacks 03KP "part (1): separated"]
theorem isSeparated_of_section (p : P ⟶ V) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    IsSeparated B S hS s :=
  (isSeparated_arrow_mk_iso_iff B S hS (arrowIsoMapDescSection B S hS p s hs)).1
    (isSeparated_mapDesc B S hS s (𝟙 P) p)

/-- Every represented base change of a section of a morphism of algebraic spaces over `S` with
algebraic total space is a morphism of schemes which is locally of finite type. -/
theorem locallyOfFiniteType_presheaf_section (p : P ⟶ V)
    (hP : IsAlgebraicSpace B S hS P) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) s :=
  (MorphismProperty.arrow_mk_iso_iff _ (arrowIsoMapDescSection B S hS p s hs)).1
    (locallyOfFiniteType_presheaf_mapDesc B S hS s (𝟙 P) p hP)

/-- Every represented base change of a section of a morphism of algebraic spaces over `S` with
algebraic total space is a morphism of schemes which is locally of finite type and locally
quasi-finite. -/
theorem locallyQuasiFinite_presheaf_section (p : P ⟶ V)
    (hP : IsAlgebraicSpace B S hS P) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@_root_.AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS))) s :=
  (MorphismProperty.arrow_mk_iso_iff _ (arrowIsoMapDescSection B S hS p s hs)).1
    (locallyQuasiFinite_presheaf_mapDesc B S hS s (𝟙 P) p hP)

/-- **Stacks 03KP, part (1).** A section of a morphism of algebraic spaces over `S` with
algebraic total space is representable. -/
@[stacks 03KP "part (1): representable"]
theorem relativelyRepresentable_of_section (p : P ⟶ V)
    (hP : IsAlgebraicSpace B S hS P) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    yoneda.relativelyRepresentable s :=
  (locallyOfFiniteType_presheaf_section B S hS p hP s hs).rep

/-- **Stacks 03KP, part (1).** A section of a morphism of algebraic spaces over `S` with
algebraic total space is locally of finite type in the sense of Stacks 03XF. -/
@[stacks 03KP "part (1): locally of finite type"]
theorem isLocallyOfFiniteType_of_section (p : P ⟶ V)
    (hP : IsAlgebraicSpace B S hS P) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    IsLocallyOfFiniteType B S hS s :=
  presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType B S hS _
    (locallyOfFiniteType_presheaf_section B S hS p hP s hs)

/-- **Stacks 03KP, part (1).** A section of a morphism of algebraic spaces over `S` with
algebraic total space is locally quasi-finite in the sense of Stacks 03XJ. -/
@[stacks 03KP "part (1): locally quasi-finite"]
theorem isLocallyQuasiFinite_of_section (p : P ⟶ V)
    (hP : IsAlgebraicSpace B S hS P) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    IsLocallyQuasiFinite B S hS s :=
  presheafImpliesHoldsOnEveryEtaleChart_locallyQuasiFinite B S hS _
    (locallyQuasiFinite_presheaf_section B S hS p hP s hs)

/-- **Stacks 03KP, part (2).** A section of a locally separated morphism of algebraic spaces
over `S` is an immersion. -/
@[stacks 03KP "part (2)"]
theorem isImmersion_of_isLocallySeparated_of_section (p : P ⟶ V)
    (hp : IsLocallySeparated B S hS p) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    IsImmersion B S hS s :=
  (MorphismProperty.arrow_mk_iso_iff _ (arrowIsoMapDescSection B S hS p s hs)).1
    (isImmersion_mapDesc B S hS s (𝟙 P) p hp)

/-- **Stacks 03KP, part (3).** A section of a separated morphism of algebraic spaces over `S`
is a closed immersion. -/
@[stacks 03KP "part (3)", sga "3 VIB 5.6.3" "more general"]
theorem isClosedImmersion_of_isSeparated_of_section (p : P ⟶ V)
    (hp : IsSeparated B S hS p) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    IsClosedImmersion B S hS s :=
  (MorphismProperty.arrow_mk_iso_iff _ (arrowIsoMapDescSection B S hS p s hs)).1
    (isClosedImmersion_mapDesc B S hS s (𝟙 P) p hp)

/-- **Stacks 03KP, part (4).** A section of a quasi-separated morphism of algebraic spaces over
`S` is quasi-compact. -/
@[stacks 03KP "part (4)"]
theorem isQuasiCompact_of_isQuasiSeparated_of_section (p : P ⟶ V)
    (hp : IsQuasiSeparated B S hS p) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    IsQuasiCompact B S hS s :=
  isQuasiCompact_of_isPullback B S hS
    (IsPullback.of_horiz_isIso ⟨Arrow.w (arrowIsoMapDescSection B S hS p s hs).inv⟩)
    (isQuasiCompact_mapDesc B S hS s (𝟙 P) p hp)

/-- The graph of `f : X ⟶ Y` relative to `g : Y ⟶ Z`, as a morphism `X ⟶ X ×[Z] Y`.  Its
components are the identity of `X` and `f`. -/
noncomputable def graph (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ pullback (f ≫ g) g :=
  pullback.lift (𝟙 X) f (by simp)

/-- The first component of the graph of `f` over `g` is the identity, so the graph is a section
of the first projection of `X ×[Z] Y`. -/
@[simp]
theorem graph_comp_fst (f : X ⟶ Y) (g : Y ⟶ Z) :
    graph B S hS f g ≫ pullback.fst (f ≫ g) g = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The second component of the graph of `f` over `g` is `f`, so `f` factors as its graph
followed by the second projection of `X ×[Z] Y`. -/
@[simp]
theorem graph_comp_snd (f : X ⟶ Y) (g : Y ⟶ Z) :
    graph B S hS f g ≫ pullback.snd (f ≫ g) g = f :=
  pullback.lift_snd _ _ _

/-- **Stacks 03KO, part (1).** The graph `X ⟶ X ×[Z] Y` of `f : X ⟶ Y` over `g : Y ⟶ Z` is a
monomorphism, with no hypothesis on `g`: it is a section of the first projection. -/
theorem mono_graph (f : X ⟶ Y) (g : Y ⟶ Z) : Mono (graph B S hS f g) :=
  mono_of_section B S hS (pullback.fst (f ≫ g) g) _ (graph_comp_fst B S hS f g)

/-- **Stacks 03KO, part (1).** The graph `X ⟶ X ×[Z] Y` of `f : X ⟶ Y` over `g : Y ⟶ Z` is
separated, with no hypothesis on `g`: it is a section of the first projection. -/
theorem isSeparated_graph (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsSeparated B S hS (graph B S hS f g) :=
  isSeparated_of_section B S hS (pullback.fst (f ≫ g) g) _ (graph_comp_fst B S hS f g)

/-- The total space `X ×[Z] Y` of the graph of `f : X ⟶ Y` over `g : Y ⟶ Z` is an algebraic
space, being a fibre product of algebraic spaces over an algebraic space. -/
theorem isAlgebraicSpace_pullback_graph (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) :
    IsAlgebraicSpace B S hS (pullback (f ≫ g) g) :=
  isAlgebraicSpace_pullback B S hS (f ≫ g) g hX hY hZ

/-- **Stacks 03KO, part (1).** The graph `X ⟶ X ×[Z] Y` of `f : X ⟶ Y` over `g : Y ⟶ Z` is
representable, with no hypothesis on `g`. -/
theorem relativelyRepresentable_graph (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) :
    yoneda.relativelyRepresentable (graph B S hS f g) :=
  relativelyRepresentable_of_section B S hS (pullback.fst (f ≫ g) g)
    (isAlgebraicSpace_pullback_graph B S hS f g hX hY hZ) _ (graph_comp_fst B S hS f g)

/-- **Stacks 03KO, part (1).** The graph `X ⟶ X ×[Z] Y` of `f : X ⟶ Y` over `g : Y ⟶ Z` is
locally of finite type in the sense of Stacks 03XF, with no hypothesis on `g`. -/
theorem isLocallyOfFiniteType_graph (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) :
    IsLocallyOfFiniteType B S hS (graph B S hS f g) :=
  isLocallyOfFiniteType_of_section B S hS (pullback.fst (f ≫ g) g)
    (isAlgebraicSpace_pullback_graph B S hS f g hX hY hZ) _ (graph_comp_fst B S hS f g)

/-- **Stacks 03KO, part (1).** The graph `X ⟶ X ×[Z] Y` of `f : X ⟶ Y` over `g : Y ⟶ Z` is
locally quasi-finite in the sense of Stacks 03XJ, with no hypothesis on `g`. -/
theorem isLocallyQuasiFinite_graph (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) :
    IsLocallyQuasiFinite B S hS (graph B S hS f g) :=
  isLocallyQuasiFinite_of_section B S hS (pullback.fst (f ≫ g) g)
    (isAlgebraicSpace_pullback_graph B S hS f g hX hY hZ) _ (graph_comp_fst B S hS f g)

/-- The first projection of `X ×[Z] Y` is isomorphic, as an arrow, to the second projection of
`Y ×[Z] X` by the symmetry of the fibre product. -/
private noncomputable def arrowIsoFstSnd (f : X ⟶ Y) (g : Y ⟶ Z) :
    Arrow.mk (pullback.fst (f ≫ g) g) ≅ Arrow.mk (pullback.snd g (f ≫ g)) :=
  Arrow.isoMk (pullbackSymmetry (f ≫ g) g) (Iso.refl X) (by simp)

/-- **The graph over a separated morphism is a closed immersion.** For `f : X ⟶ Y` and a
separated `g : Y ⟶ Z`, the graph `X ⟶ X ×[Z] Y` of `f` is a closed immersion. -/
@[ega "I 5.3.11" "separated case", ega "I 5.4.3"]
theorem isClosedImmersion_graph_of_isSeparated (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : IsSeparated B S hS g) :
    IsClosedImmersion B S hS (graph B S hS f g) := by
  have hrev : IsSeparated B S hS (pullback.snd g (f ≫ g)) :=
    isSeparated_pullbackSnd B S hS (f ≫ g) hg
  exact isClosedImmersion_of_isSeparated_of_section B S hS _
    ((isSeparated_arrow_mk_iso_iff B S hS (arrowIsoFstSnd B S hS f g)).2 hrev) _
    (graph_comp_fst B S hS f g)

/-- **The graph over a locally separated morphism is an immersion.** For `f : X ⟶ Y` and a
locally separated `g : Y ⟶ Z`, the graph `X ⟶ X ×[Z] Y` of `f` is an immersion. -/
theorem isImmersion_graph_of_isLocallySeparated (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : IsLocallySeparated B S hS g) :
    IsImmersion B S hS (graph B S hS f g) := by
  have hrev : IsLocallySeparated B S hS (pullback.snd g (f ≫ g)) :=
    isLocallySeparated_pullbackSnd B S hS (f ≫ g) hg
  exact isImmersion_of_isLocallySeparated_of_section B S hS _
    ((isLocallySeparated_arrow_mk_iso_iff B S hS (arrowIsoFstSnd B S hS f g)).2 hrev) _
    (graph_comp_fst B S hS f g)

/-- **Stacks 03KO, part (4).** For `f : X ⟶ Y` and a quasi-separated `g : Y ⟶ Z`, the graph
`X ⟶ X ×[Z] Y` of `f` is quasi-compact.

Composing the graph with the symmetry `X ×[Z] Y ≅ Y ×[Z] X` turns it into a section of
`pullback.snd g (f ≫ g)`, which is quasi-separated as a base change of `g`; quasi-compactness
of the graph itself is then read back across that isomorphism. -/
theorem isQuasiCompact_graph_of_isQuasiSeparated (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : IsQuasiSeparated B S hS g) :
    IsQuasiCompact B S hS (graph B S hS f g) := by
  have hrev : IsQuasiSeparated B S hS (pullback.snd g (f ≫ g)) :=
    isQuasiSeparated_pullbackSnd B S hS (f ≫ g) hg
  have hsec : (graph B S hS f g ≫ (pullbackSymmetry (f ≫ g) g).hom) ≫
      pullback.snd g (f ≫ g) = 𝟙 X := by simp
  exact isQuasiCompact_of_isPullback B S hS (IsPullback.of_horiz_isIso ⟨Category.id_comp _⟩)
    (isQuasiCompact_of_isQuasiSeparated_of_section B S hS (pullback.snd g (f ≫ g)) hrev _ hsec)

end Graph

end AlgebraicGeometry.Space

end
