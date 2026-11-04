module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FppfLocalTarget

/-!
# Morphisms with locally Noetherian fibres

A morphism of schemes has locally Noetherian fibres when every one of its fibres is a locally
Noetherian scheme. This condition may be tested after an fppf covering of either the source or
the target.

## Main definitions

* `AlgebraicGeometry.locallyNoetherianFibers` is the property of a morphism of schemes that all
  of its fibres are locally Noetherian.
* `AlgebraicGeometry.compPullbackIso` identifies a base change of a composition with an iterated
  base change; for the fibre of a composition it gives the base change of the fibre of the second
  factor.

## Main results

* `AlgebraicGeometry.locallyNoetherianFibers_respectsIso`: the property is invariant under
  isomorphism of arrows.
* `AlgebraicGeometry.locallyNoetherianFibers_isLocalAtSource_fppf`: the property is local on the
  source for the fppf topology.
* `AlgebraicGeometry.locallyNoetherianFibers_isLocalAtTarget_fppf`: the property is local on the
  target for the fppf topology.

## Implementation notes

Fibres are Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber`, the pullback of the morphism along the
canonical morphism from the spectrum of the residue field of the chosen point, and the Noetherian
condition is Mathlib's `AlgebraicGeometry.IsLocallyNoetherian`. Locality is expressed by Mathlib's
`CategoryTheory.MorphismProperty.IsLocalAtSource` and
`CategoryTheory.MorphismProperty.IsLocalAtTarget`, whose two fields give ascent along a member of
a covering family and descent from a covering family.

Locality on the target rests on the comparison
`AlgebraicGeometry.isLocallyNoetherian_fiber_pullback_iff` of a fibre with the corresponding
fibre of a base change along a morphism locally of finite presentation: the induced extension of
residue fields is then finitely generated.

Locality on the source is a statement about one fibre at a time: an fppf covering of the source
induces an fppf covering of each fibre, so the content is that being a locally Noetherian scheme
is itself an fppf local condition.

## References

* [Stacks Project, Tag 0392](https://stacks.math.columbia.edu/tag/0392)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The property of Tag 0392.** All fibres of a morphism of schemes are locally Noetherian. -/
public abbrev locallyNoetherianFibers : MorphismProperty Scheme.{u} :=
  fun _ Y f => ∀ y : Y, IsLocallyNoetherian (f.fiber y)

/-- Having locally Noetherian fibres is invariant under isomorphism of arrows. -/
public theorem locallyNoetherianFibers_respectsIso :
    MorphismProperty.RespectsIso (locallyNoetherianFibers : MorphismProperty Scheme.{u}) := by
  refine MorphismProperty.RespectsIso.of_respects_arrow_iso locallyNoetherianFibers ?_
  intro a b e h y
  have _ : IsLocallyNoetherian (a.hom.fiber (e.symm.hom.right.base y)) :=
    h (e.symm.hom.right.base y)
  exact isLocallyNoetherian_of_isOpenImmersion (fiberIsoOfArrowIso b.hom a.hom e.symm y).hom

/-- Base changing `f` along `φ` and then restricting to `g` is the same as base changing the
composition `g ≫ f` along `φ`. Taking `φ` to be the canonical morphism from the spectrum of a
residue field, this says that the fibre of `g ≫ f` is the base change along `g` of the fibre
of `f`. -/
public noncomputable def compPullbackIso {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (φ : W ⟶ Y)
    (g : Z ⟶ X) : pullback (pullback.fst f φ) g ≅ pullback (g ≫ f) φ :=
  pullbackSymmetry (pullback.fst f φ) g ≪≫ pullbackRightPullbackFstIso f φ g

/-- The comparison `AlgebraicGeometry.compPullbackIso` is compatible with the projections
to `W`. -/
public theorem compPullbackIso_hom_snd {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (φ : W ⟶ Y)
    (g : Z ⟶ X) :
    (compPullbackIso f φ g).hom ≫ pullback.snd (g ≫ f) φ =
      pullback.fst (pullback.fst f φ) g ≫ pullback.snd f φ := by
  rw [compPullbackIso, Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    ← Category.assoc, pullbackSymmetry_hom_comp_snd]

/-- Having locally Noetherian fibres can be tested on an fppf covering family of the source,
one fibre at a time. -/
private theorem locallyNoetherianFibers_iff_zeroHypercover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Scheme.fppfPrecoverage.ZeroHypercover X) :
    locallyNoetherianFibers f ↔ ∀ i, locallyNoetherianFibers (𝒰.f i ≫ f) := by
  constructor
  · intro hf i y
    exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso
      (compPullbackIso f (Y.fromSpecResidueField y) (𝒰.f i))
      (ObjectProperty.IsLocal.component (𝒰.pullback₁ (f.fiberι y)).mem₀ _ ⟨i⟩ (hf y))
  · intro hf y
    exact (ObjectProperty.iff_of_zeroHypercover
      (P := fun Z : Scheme.{u} => IsLocallyNoetherian Z)
      (𝒰.pullback₁ (f.fiberι y))).mpr fun i => ObjectProperty.IsClosedUnderIsomorphisms.of_iso
        (compPullbackIso f (Y.fromSpecResidueField y) (𝒰.f i)).symm (hf i y)

/-- **Stacks Project, Tag 0392.** Having locally Noetherian fibres is local on the source for the
fppf topology. -/
@[stacks 0392 "fppf local on the source"]
public instance locallyNoetherianFibers_isLocalAtSource_fppf :
    (locallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtSource
      Scheme.fppfPrecoverage := by
  have _ : MorphismProperty.RespectsIso
      (locallyNoetherianFibers : MorphismProperty Scheme.{u}) :=
    locallyNoetherianFibers_respectsIso
  exact MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover
    locallyNoetherianFibers_iff_zeroHypercover

/-- **Stacks Project, Tag 0392.** Having locally Noetherian fibres is local on the target for the
fppf topology. -/
@[stacks 0392 "fppf local on the target"]
public instance locallyNoetherianFibers_isLocalAtTarget_fppf :
    (locallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtTarget
      Scheme.fppfPrecoverage := by
  have _ : MorphismProperty.RespectsIso
      (locallyNoetherianFibers : MorphismProperty Scheme.{u}) :=
    locallyNoetherianFibers_respectsIso
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff ?_
  intro X Y f R hR
  obtain ⟨hcover, hprops⟩ : R ∈ Scheme.jointlySurjectivePrecoverage Y ∧
      R ∈ MorphismProperty.precoverage
        (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Y := hR
  constructor
  · intro hf U g _ hRg y
    have : LocallyOfFinitePresentation g := (hprops hRg).2
    exact isLocallyNoetherian_fiber_pullback f g hf y
  · intro hlocal y
    obtain ⟨Z, g, hg, ⟨z, hz⟩⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
        (F := Scheme.forget)).mp hcover y
    have : LocallyOfFinitePresentation g := (hprops hg).2
    obtain rfl : g.base z = y := hz
    rw [isLocallyNoetherian_fiber_pullback_iff f g z]
    exact hlocal g hg z

end AlgebraicGeometry
