module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Fibres
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FppfLocalTarget

/-!
# Gorenstein morphisms are fppf local on the target and syntomic local on the source

For a morphism of schemes, the property of having locally Noetherian fibres and being Gorenstein
may be checked after an fppf covering of the target, and also after a syntomic covering of the
source.

## Main definitions

* `AlgebraicGeometry.gorensteinWithLocallyNoetherianFibers` is the morphism property combining
  locally Noetherian fibres with Gorensteinness.

## Main results

* `AlgebraicGeometry.isGorenstein_iff_of_iso`: Gorensteinness of a scheme is invariant under
  isomorphism.
* `AlgebraicGeometry.gorensteinWithLocallyNoetherianFibers_iff`: the property is flatness
  together with Gorensteinness of every fibre.
* `AlgebraicGeometry.gorensteinWithLocallyNoetherianFibers_isLocalAtTarget_fppf`: the property is
  local on the target for the fppf precoverage.
* `AlgebraicGeometry.gorensteinWithLocallyNoetherianFibers_isLocalAtSource_syntomic`: the property
  is local on the source for the syntomic precoverage.

## Implementation notes

The locally Noetherian condition on the fibres is packaged existentially, because Gorensteinness
of a morphism takes a proof of it as an explicit argument. The existential is harmless: a
Gorenstein scheme is by definition locally Noetherian, so the property is equivalent to flatness
together with Gorensteinness of every fibre, which is
`AlgebraicGeometry.gorensteinWithLocallyNoetherianFibers_iff`.

Locality is `CategoryTheory.MorphismProperty.IsLocalAtTarget`, which bundles isomorphism
invariance, stability under pullback along a member of a covering family, and descent from a
covering family. The pullback and descent halves are parts (1) and (2) of the base-change
statement Tag 0C07; isomorphism invariance comes from the fibre comparison
`AlgebraicGeometry.fiberIsoOfArrowIso`, together with the transport of Gorensteinness of a scheme
along an open immersion.

Source locality is `CategoryTheory.MorphismProperty.IsLocalAtSource`, whose two halves are the two
directions of the composition statement Tag 0C11: a syntomic morphism is Gorenstein by Tag 0C15,
so the composite with a member of a covering family is Gorenstein; and conversely a syntomic
morphism is flat, so Gorensteinness of the composite gives Gorensteinness of the second factor at
every point in the image. The condition on the fibres is handled by base changing the covering
family of the source along the embedding of a fibre, which produces a syntomic — hence fppf —
covering family of that fibre, and then descending local Noetherianity along it with
`AlgebraicGeometry.isLocallyNoetherian_isLocal_fppf`.

Flatness is the first half of the property in the source's decomposition, and is already known to
be fppf local on the target (Tag 02L2, `Stacks.Descent.flat_isLocalAtTarget_fpqc`) and fpqc local
on the source (Tag 036K, `AlgebraicGeometry.flat_isLocalAtSource_fpqc`); both are used through the
comparison of the syntomic, fppf and fpqc precoverages rather than re-proved.

The fibre comparisons `AlgebraicGeometry.isLocallyNoetherian_fiber_pullback_iff`,
`AlgebraicGeometry.fiberIsoOfArrowIso` and `AlgebraicGeometry.fiberCompIso` are shared with the
Cohen–Macaulay form of this lemma, Tag 045V, and are imported from it rather than duplicated.

Unlike the source's own argument, nothing here routes through Tag 0C01 (Gorensteinness of a
*scheme* is syntomic local), which this library does not prove; the fibre-by-fibre statements of
Tags 0C07 and 0C11 are used in its place, so neither result below is conditional.

## References

* [Stacks Project, Tag 0C0A](https://stacks.math.columbia.edu/tag/0C0A)
* [Stacks Project, Tag 0C07](https://stacks.math.columbia.edu/tag/0C07)
* [Stacks Project, Tag 0C11](https://stacks.math.columbia.edu/tag/0C11)
* [Stacks Project, Tag 0C15](https://stacks.math.columbia.edu/tag/0C15)
* [Stacks Project, Tag 02L2](https://stacks.math.columbia.edu/tag/02L2)
* [Stacks Project, Tag 036K](https://stacks.math.columbia.edu/tag/036K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Gorensteinness of a scheme is invariant under isomorphism: an isomorphism and its inverse are
both open immersions, and Gorensteinness passes to the source of an open immersion. -/
public theorem isGorenstein_iff_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    IsGorenstein X ↔ IsGorenstein Y :=
  ⟨fun _ => isGorenstein_of_isOpenImmersion e.inv, fun _ => isGorenstein_of_isOpenImmersion e.hom⟩

/-- **The property of Tag 0C0A.** A morphism of schemes has locally Noetherian fibres and is
Gorenstein. -/
public abbrev gorensteinWithLocallyNoetherianFibers : MorphismProperty Scheme.{u} :=
  fun _ _ f => ∃ hf : ∀ y, IsLocallyNoetherian (f.fiber y), Scheme.Hom.IsGorenstein f hf

/-- A morphism has locally Noetherian fibres and is Gorenstein exactly when it is flat with
Gorenstein fibres. The locally Noetherian condition is automatic, a Gorenstein scheme being
locally Noetherian. -/
public theorem gorensteinWithLocallyNoetherianFibers_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    gorensteinWithLocallyNoetherianFibers f ↔
      Flat f ∧ ∀ y : Y, IsGorenstein (f.fiber y) := by
  refine ⟨fun ⟨hf, hG⟩ =>
    (Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f hf).mp hG, ?_⟩
  rintro ⟨hflat, hfib⟩
  exact ⟨fun y => (hfib y).toIsLocallyNoetherian,
    (Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f _).mpr ⟨hflat, hfib⟩⟩

/-- Having locally Noetherian fibres and being Gorenstein is invariant under isomorphism of
arrows. -/
public instance gorensteinWithLocallyNoetherianFibers_respectsIso :
    MorphismProperty.RespectsIso
      (gorensteinWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}) := by
  refine MorphismProperty.RespectsIso.of_respects_arrow_iso
    gorensteinWithLocallyNoetherianFibers ?_
  intro a b e h
  rw [gorensteinWithLocallyNoetherianFibers_iff] at h ⊢
  have _ : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    (Stacks.Descent.flat_isLocalAtTarget_fpqc.{u}).toRespects
  refine ⟨(MorphismProperty.arrow_iso_iff (@Flat : MorphismProperty Scheme.{u}) e).mp h.1,
    fun y' => ?_⟩
  exact (isGorenstein_iff_of_iso (fiberIsoOfArrowIso b.hom a.hom e.symm y')).mpr (h.2 _)

/-- **Stacks Project, Tag 0C0A.** Having locally Noetherian fibres and being Gorenstein is local
on the target for the fppf topology. -/
@[stacks 0C0A "local in the fppf topology on the target"]
public instance gorensteinWithLocallyNoetherianFibers_isLocalAtTarget_fppf :
    (gorensteinWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtTarget
      Scheme.fppfPrecoverage := by
  have _ : MorphismProperty.RespectsIso
      (gorensteinWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}) :=
    gorensteinWithLocallyNoetherianFibers_respectsIso
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff ?_
  intro X Y f R hR
  have hdec : R ∈ Scheme.jointlySurjectivePrecoverage Y ∧
      R ∈ MorphismProperty.precoverage
        (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Y := hR
  obtain ⟨hcover, hprops⟩ := hdec
  constructor
  · rintro ⟨hf, hG⟩ U g hgPull hRg
    have _ : Flat g := (hprops hRg).1
    have _ : LocallyOfFinitePresentation g := (hprops hRg).2
    have _ : LocallyOfFiniteType g := inferInstance
    refine ⟨fun y' => isLocallyNoetherian_fiber_pullback f g hf y', fun x' => ?_⟩
    exact Scheme.Hom.isGorensteinAt_pullback f g hf x' (hG ((pullback.fst f g).base x'))
  · intro hlocal
    have hflat : Flat f := by
      refine (MorphismProperty.IsLocalAtTarget.of_le
        (P := (@Flat : MorphismProperty Scheme.{u}))
        Scheme.fppfPrecoverage_le_fpqcPrecoverage).of_forall_pullbackSnd hR ?_
      intro U g _ hRg
      obtain ⟨hf', hG'⟩ := hlocal g hRg
      exact ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber
        (pullback.snd f g) hf').mp hG').1
    have hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y) := by
      intro y
      obtain ⟨Z, g, hg, ⟨z, hz⟩⟩ :=
        (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
          (F := Scheme.forget)).mp hcover y
      have _ : LocallyOfFinitePresentation g := (hprops hg).2
      have _ : LocallyOfFiniteType g := inferInstance
      have _ : HasPullback f g := inferInstance
      obtain ⟨hf', -⟩ := hlocal g hg
      have hgz : g.base z = y := hz
      rw [← hgz, isLocallyNoetherian_fiber_pullback_iff f g z]
      exact hf' z
    refine ⟨hf, fun x => ?_⟩
    obtain ⟨Z, g, hg, ⟨z, hz⟩⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
        (F := Scheme.forget)).mp hcover (f.base x)
    have _ : LocallyOfFinitePresentation g := (hprops hg).2
    have _ : LocallyOfFiniteType g := inferInstance
    have _ : HasPullback f g := inferInstance
    obtain ⟨x', hx', -⟩ :=
      Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback f g) x z hz.symm
    obtain ⟨hf', hG'⟩ := hlocal g hg
    have hfl : IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x') :=
      (Flat.iff_flat_stalkMap f).mp hflat ((pullback.fst f g).base x')
    simpa [hx'] using
      Scheme.Hom.isGorensteinAt_of_pullback_of_flat f g hf x' hfl (hG' x')

/-- **Stacks Project, Tag 0C0A.** Having locally Noetherian fibres and being Gorenstein is local
on the source for the syntomic topology. -/
@[stacks 0C0A "local in the syntomic topology on the source"]
public instance gorensteinWithLocallyNoetherianFibers_isLocalAtSource_syntomic :
    (gorensteinWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtSource
      (Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u})) := by
  have _ : MorphismProperty.RespectsIso
      (gorensteinWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}) :=
    gorensteinWithLocallyNoetherianFibers_respectsIso
  have _ : MorphismProperty.IsLocalAtSource (@Flat : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtSource.of_le Scheme.syntomicPrecoverage_le_fpqcPrecoverage
  refine MorphismProperty.IsLocalAtSource.mk_of_iff ?_
  intro X Y f R hR
  have hdec : R ∈ Scheme.jointlySurjectivePrecoverage X ∧
      R ∈ MorphismProperty.precoverage (@Syntomic : MorphismProperty Scheme.{u}) X := hR
  obtain ⟨hcover, hprops⟩ := hdec
  constructor
  · rintro ⟨hf, hG⟩ U g hg
    have hsyn : Syntomic g := hprops hg
    have _ : LocallyOfFinitePresentation g := locallyOfFinitePresentation hsyn
    have hgfib : ∀ x : X, IsLocallyNoetherian (g.fiber x) := fun x =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation g x
    have hgffib := isLocallyNoetherian_fiber_comp_of_syntomic hsyn f hf
    exact ⟨hgffib, Scheme.Hom.isGorenstein_comp g f hgfib hf hgffib
      (isGorenstein_of_syntomic g hsyn) hG⟩
  · intro hlocal
    have hflat : Flat f := by
      refine MorphismProperty.IsLocalAtSource.of_forall_comp hR ?_
      intro U g hg
      obtain ⟨hgf, hGgf⟩ := hlocal hg
      exact ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber (g ≫ f) hgf).mp hGgf).1
    have hffib : ∀ y : Y, IsLocallyNoetherian (f.fiber y) := by
      intro y
      have _ : (Scheme.precoverage
          (@Syntomic : MorphismProperty Scheme.{u})).IsStableUnderBaseChange :=
        precoverage_isStableUnderBaseChange (@Syntomic : MorphismProperty Scheme.{u})
      have hcov : R.pullbackArrows (f.fiberι y) ∈
          Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u}) (f.fiber y) :=
        Precoverage.pullbackArrows_mem _ hR
      refine isLocallyNoetherian_isLocal_fppf.of_presieve
        (Scheme.syntomicPrecoverage_le_fppfPrecoverage _ hcov) ?_
      rintro Z p ⟨W, g, hg⟩
      have _ : IsLocallyNoetherian ((g ≫ f).fiber y) := (hlocal hg).1 y
      have _ : IsOpenImmersion (fiberCompIso g f y).inv := inferInstance
      exact isLocallyNoetherian_of_isOpenImmersion (fiberCompIso g f y).inv
    refine ⟨hffib, fun x => ?_⟩
    obtain ⟨U, g, hg, ⟨u, hu⟩⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
        (F := Scheme.forget)).mp hcover x
    have hsyn : Syntomic g := hprops hg
    have _ : LocallyOfFinitePresentation g := locallyOfFinitePresentation hsyn
    have _ : Flat g := flat hsyn
    have hgfib : ∀ x : X, IsLocallyNoetherian (g.fiber x) := fun x =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation g x
    obtain ⟨hgf, hGgf⟩ := hlocal hg
    have hux : g u = x := hu
    have key := Scheme.Hom.isGorensteinAt_right_of_comp g f hgfib hffib hgf u (hGgf u)
      (Flat.stalkMap g u)
    rwa [hux] at key

end AlgebraicGeometry
