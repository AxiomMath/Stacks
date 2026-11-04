module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalFull
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingPropertyTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.BeauvilleLaszlo

/-!
# Flatness and finite presentation from the glueing components (Stacks 0F9R)

Let `(g : R → R', f)` be a Beauville--Laszlo glueing pair, and write `X = Spec R`,
`U = Spec R_f`, `U' = Spec R'_{gf}` and `X' = Spec R'`. Stacks 0F9R says that a morphism of
affine schemes over `X` is flat and locally of finite presentation exactly when the three
components of its image under the glueing functor of Stacks 0F9N are, provided the target is
glueable for the pair; that statement is
`BeauvilleLaszlo.flat_and_locallyOfFinitePresentation_iff_baseChange`.

This module proves one direction of that statement for morphisms of affine algebraic spaces
over `X`: if the three base changes of a morphism `p` are flat and locally of finite
presentation, then so is `p`.

## Main results

* `BeauvilleLaszlo.Space.isFlat_and_isLocallyOfFinitePresentation_of_glueingComponents`: a
  morphism of affine algebraic spaces over `X` with glueable target is flat and locally of finite
  presentation as soon as its base changes to `U`, `U'` and `X'` are.

## Implementation notes

Flatness and local finite presentation are chart conditions (Stacks 03MJ), not relatively
representable conditions, so the hypotheses are chart conditions and the transport is
`AlgebraicGeometry.prop_overPullback_map_of_holdsOnEveryEtaleChart`, applied once per leg and
per property.

The affine-scheme statement asks for short exactness of the Beauville--Laszlo module sequence of
the ring of the target. This follows from the space-level glueability hypothesis by
`BeauvilleLaszlo.Space.isGlueableFor_of_isGlueableGlobalSections` and
`BeauvilleLaszlo.isGlueableFor_iff_beauvilleLaszloModuleSequence_shortExact`.

`AlgebraicGeometry.Space.IsGlueableGlobalSections` has its two rings in *different* universes,
`R : Type u` and `R' : Type v`, while the affine-scheme statement of Stacks 0F9R has all of `R`,
`R'` and the two algebras in `Type u`. Under the local instance `g.toAlgebra`, `algebraMap R R'`
is `g` by definition, so the glueability statement and the affine-scheme statement speak of the
same ring map.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9R](https://stacks.math.columbia.edu/tag/0F9R)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-- **Stacks 0F9R for flat morphisms locally of finite presentation, for algebraic spaces, one
direction.** Let `(g : R → R', f)` be a glueing pair. A morphism `p : L → V` of algebraic spaces
over `X = Spec R` with `L` and `V` affine and `V` glueable for `(g, f)` is flat and locally of
finite presentation as soon as its three base changes to `U = Spec R_f`, `U' = Spec R'_{gf}` and
`X' = Spec R'` — the three components of its image under the glueing functor of Stacks 0F9N —
are. -/
theorem isFlat_and_isLocallyOfFinitePresentation_of_glueingComponents
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    {L V : AlgebraicSpaces B (Spec (.of R)) hX} (p : L ⟶ V)
    (hLa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX L.1)
    (hVa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX V.1)
    (hVg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX V)
    (hpU : AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away f))) hU
        ((baseChange B (Spec (.of (Localization.Away f))) (Spec (.of R)) hU hX
          (canJU f B hU hX)).map p).hom ∧
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B
        (Spec (.of (Localization.Away f))) hU
        ((baseChange B (Spec (.of (Localization.Away f))) (Spec (.of R)) hU hX
          (canJU f B hU hX)).map p).hom)
    (hpU' : AlgebraicGeometry.Space.IsFlat B (Spec (.of (Localization.Away (g f)))) hU'
        ((baseChange B (Spec (.of (Localization.Away (g f)))) (Spec (.of R)) hU' hX
          (canGU g f B hU' hU ≫ canJU f B hU hX)).map p).hom ∧
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B
        (Spec (.of (Localization.Away (g f)))) hU'
        ((baseChange B (Spec (.of (Localization.Away (g f)))) (Spec (.of R)) hU' hX
          (canGU g f B hU' hU ≫ canJU f B hU hX)).map p).hom)
    (hpX' : AlgebraicGeometry.Space.IsFlat B (Spec (.of R')) hX'
        ((baseChange B (Spec (.of R')) (Spec (.of R)) hX' hX (canJX' g B hX' hX)).map p).hom ∧
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B (Spec (.of R')) hX'
        ((baseChange B (Spec (.of R')) (Spec (.of R)) hX' hX (canJX' g B hX' hX)).map p).hom) :
    AlgebraicGeometry.Space.IsFlat B (Spec (.of R)) hX p.hom ∧
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B (Spec (.of R)) hX p.hom := by
  let : Algebra R R' := g.toAlgebra
  obtain ⟨TL, hTL, ⟨eL0⟩⟩ := hLa
  obtain ⟨A, hA, φA, ⟨eL1⟩⟩ := BigFppfOver.exists_specOver B hX TL hTL
  obtain ⟨TV, hTV, ⟨eV0⟩⟩ := hVa
  obtain ⟨C, hC, φC, ⟨eV1⟩⟩ := BigFppfOver.exists_specOver B hX TV hTV
  let : Algebra R A := φA.hom.toAlgebra
  let : Algebra R C := φC.hom.toAlgebra
  obtain ⟨eL, eV, ψ, hψ⟩ :
      ∃ (eL : L.1 ≅ yoneda.obj (BigFppfOver.specOver B hX hA φA))
        (eV : V.1 ≅ yoneda.obj (BigFppfOver.specOver B hX hC φC))
        (ψ : BigFppfOver.specOver B hX hA φA ⟶ BigFppfOver.specOver B hX hC φC),
        yoneda.map ψ = eL.inv ≫ p.hom ≫ eV.hom :=
    ⟨eL0 ≪≫ yoneda.mapIso eL1, eV0 ≪≫ yoneda.mapIso eV1,
      yoneda.preimage ((eL0 ≪≫ yoneda.mapIso eL1).inv ≫ p.hom ≫
        (eV0 ≪≫ yoneda.mapIso eV1).hom), yoneda.map_preimage _⟩
  have hCgs : AlgebraicGeometry.Space.IsGlueableGlobalSections g f B hX
      (BigFppfOver.specOver B hX hC φC) :=
    hVg (BigFppfOver.specOver B hX hC φC) eV.inv
      (BigFppfOver.isAffine_toScheme_obj_specOver B hX hC φC)
      (AlgebraicGeometry.Space.isEtale_of_isIso B (Spec (.of R)) hX eV.inv)
  have hCg : (_root_.BeauvilleLaszlo.beauvilleLaszloModuleSequence (S := R')
      (C : Type u) f).ShortExact :=
    (_root_.BeauvilleLaszlo.isGlueableFor_iff_beauvilleLaszloModuleSequence_shortExact _ f).1
      (isGlueableFor_of_isGlueableGlobalSections g f B hX (C : Type u) hC hCgs)
  let h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (A : Type u)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (C : Type u)))) :=
    Over.homMk ((BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ)
      (BigFppfOver.specOverHomMap_comp B hX hA hC φA φC ψ)
  have hh : h.left = (BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ := rfl
  have hmid : B.inclusion.map (canGU g f B hU' hU ≫ canJU f B hU hX) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (algebraMap R R' f)))) := by
    rw [Functor.map_comp]
    change Spec.map (CommRingCat.ofHom (Localization.awayMap g f)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) = _
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  have hflat : MorphismProperty.RespectsIso (@Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hfp : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hmain : Flat ((BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ) := by
    rw [← hh]
    refine (_root_.BeauvilleLaszlo.flat_and_locallyOfFinitePresentation_iff_baseChange f hglue
      hCg h).mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact prop_overPullback_map_of_holdsOnEveryEtaleChart (@Flat.{u}) B (Spec (.of R)) _ hX hU
        (canJU f B hU hX) _ rfl ψ h hh p.hom eL eV hψ hpU.1
    · exact prop_overPullback_map_of_holdsOnEveryEtaleChart (@LocallyOfFinitePresentation.{u}) B
        (Spec (.of R)) _ hX hU (canJU f B hU hX) _ rfl ψ h hh p.hom eL eV hψ hpU.2
    · exact prop_overPullback_map_of_holdsOnEveryEtaleChart (@Flat.{u}) B (Spec (.of R)) _ hX hU'
        (canGU g f B hU' hU ≫ canJU f B hU hX) _ hmid ψ h hh p.hom eL eV hψ hpU'.1
    · exact prop_overPullback_map_of_holdsOnEveryEtaleChart (@LocallyOfFinitePresentation.{u}) B
        (Spec (.of R)) _ hX hU' (canGU g f B hU' hU ≫ canJU f B hU hX) _ hmid ψ h hh p.hom
        eL eV hψ hpU'.2
    · exact prop_overPullback_map_of_holdsOnEveryEtaleChart (@Flat.{u}) B (Spec (.of R)) _ hX hX'
        (canJX' g B hX' hX) _ rfl ψ h hh p.hom eL eV hψ hpX'.1
    · exact prop_overPullback_map_of_holdsOnEveryEtaleChart (@LocallyOfFinitePresentation.{u}) B
        (Spec (.of R)) _ hX hX' (canJX' g B hX' hX) _ rfl ψ h hh p.hom eL eV hψ hpX'.2
  exact ⟨holdsOnEveryEtaleChart_of_prop_toScheme_map (@Flat.{u})
      Flat.isEtaleLocalOnSourceAndTarget B (Spec (.of R)) hX ψ p.hom eL eV hψ hmain.1,
    holdsOnEveryEtaleChart_of_prop_toScheme_map (@LocallyOfFinitePresentation.{u})
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget B (Spec (.of R)) hX ψ p.hom
      eL eV hψ hmain.2⟩

end BeauvilleLaszlo.Space

end
