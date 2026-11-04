module

public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.TopologyComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Fibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularNoetherian
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohen–Macaulay morphisms are fppf local on the target and syntomic local on the source

For a morphism of schemes, the property of having locally Noetherian fibres and being
Cohen–Macaulay may be checked after an fppf covering of the target, and also after a syntomic
covering of the source.

## Main definitions

* `AlgebraicGeometry.cohenMacaulayWithLocallyNoetherianFibers` is the morphism property
  combining locally Noetherian fibres with Cohen–Macaulayness.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_iff_of_iso`: Cohen–Macaulayness of a scheme is invariant
  under isomorphism.
* `AlgebraicGeometry.isLocallyNoetherian_fiber_pullback_iff`: along a morphism locally of finite
  type, a fibre is locally Noetherian exactly when the corresponding fibre of the base change
  is.
* `AlgebraicGeometry.cohenMacaulayWithLocallyNoetherianFibers_iff`: the property is flatness
  together with Cohen–Macaulayness of every fibre.
* `AlgebraicGeometry.cohenMacaulayWithLocallyNoetherianFibers_isLocalAtTarget_fppf`: the
  property is local on the target for the fppf precoverage.
* `AlgebraicGeometry.fiberCompIso`: the fibre of a composite over a point of the outer target is
  the base change of the first morphism along the embedding of the fibre of the second.
* `AlgebraicGeometry.cohenMacaulayWithLocallyNoetherianFibers_isLocalAtSource_syntomic`: the
  property is local on the source for the syntomic precoverage.

## Implementation notes

The locally Noetherian condition on the fibres is packaged existentially, because
Cohen–Macaulayness of a morphism takes a proof of it as an explicit argument. The existential is
harmless: Cohen–Macaulayness of a scheme already implies that it is locally Noetherian, so the
property is equivalent to flatness together with Cohen–Macaulayness of every fibre.

Locality is `CategoryTheory.MorphismProperty.IsLocalAtTarget`, which bundles the isomorphism
invariance, stability under pullback along a member of a covering family, and descent from a
covering family. The pullback and descent halves are the base-change statements of Tag 045T;
isomorphism invariance comes from the fibre comparison
`AlgebraicGeometry.fiberIsoOfArrowIso` below.

Source locality is `CategoryTheory.MorphismProperty.IsLocalAtSource`, whose two halves are the
two directions of the composition statement of Tag 0C0W: a syntomic morphism is Cohen–Macaulay,
so the composite with a member of a covering family is Cohen–Macaulay; and conversely a syntomic
morphism is flat, so Cohen–Macaulayness of the composite gives Cohen–Macaulayness of the second
factor at every point in the image. The condition on the fibres is handled by base changing the
covering family of the source along the embedding of a fibre, which produces a syntomic — hence
fppf — covering family of that fibre, and then descending local Noetherianity along it with
`AlgebraicGeometry.isLocallyNoetherian_isLocal_fppf`.

## References

* [Stacks Project, Tag 045V](https://stacks.math.columbia.edu/tag/045V)
* [Stacks Project, Tag 0C0W](https://stacks.math.columbia.edu/tag/0C0W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A Cohen–Macaulay scheme is locally Noetherian.

Kept `private`: the public, tagged form of this statement is
`AlgebraicGeometry.IsCohenMacaulay.isLocallyNoetherian` in
`StacksFrontier.AlgebraicGeometry.Chow.Setup.CohenMacaulayBase`, which carries
`@[stacks 0F91 "local Noetherianity"]`. That module sits in a different part of the import graph,
so this file cannot route through it, and two public declarations of one fully-qualified name
collide the moment the umbrella imports both. `private` mangles this copy per-module, which keeps
the in-file dot-notation use below working and leaves the tagged declaration sole owner of the
name. -/
private theorem IsCohenMacaulay.isLocallyNoetherian {X : Scheme.{u}} (hX : IsCohenMacaulay X) :
    IsLocallyNoetherian X :=
  (((isCohenMacaulay_tfae_stalk X).out 1 2 rfl rfl).mp hX).1

/-- Cohen–Macaulayness of a scheme is invariant under isomorphism. -/
public theorem isCohenMacaulay_iff_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    IsCohenMacaulay X ↔ IsCohenMacaulay Y := by
  have key : ∀ {A B : Scheme.{u}}, (A ≅ B) → IsCohenMacaulay A → IsCohenMacaulay B := by
    intro A B e hA
    obtain ⟨hNA, hstA⟩ := ((isCohenMacaulay_tfae_stalk A).out 1 2 rfl rfl).mp hA
    have _ : IsLocallyNoetherian A := hNA
    have _ : IsLocallyNoetherian B := isLocallyNoetherian_of_isOpenImmersion e.inv
    refine ((isCohenMacaulay_tfae_stalk B).out 2 1 rfl rfl).mp ⟨inferInstance, fun b => ?_⟩
    have hab : e.hom.base (e.inv.base b) = b := by simp
    obtain ⟨_, hCM⟩ := hstA (e.inv.base b)
    have _ : IsIso (e.hom.stalkMap (e.inv.base b)) :=
      ((isIso_iff_isIso_stalkMap e.hom).mp inferInstance).2 _
    refine ⟨inferInstance, ?_⟩
    rw [← hab]
    exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
      (asIso (e.hom.stalkMap (e.inv.base b))).commRingCatIsoToRingEquiv).mpr hCM
  exact ⟨key e, key e.symm⟩

/-- Along a morphism locally of finite type, a fibre of `f` is locally Noetherian exactly when
the corresponding fibre of the base change of `f` is locally Noetherian. -/
public theorem isLocallyNoetherian_fiber_pullback_iff {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g] (y' : Y') :
    IsLocallyNoetherian (f.fiber (g.base y')) ↔
      IsLocallyNoetherian ((pullback.snd f g).fiber y') := by
  let _ : Algebra (Y.residueField (g.base y')) (Y'.residueField y') :=
    (g.residueFieldMap y').hom.toAlgebra
  have _ : Algebra.EssFiniteType (Y.residueField (g.base y')) (Y'.residueField y') :=
    residueField_essFiniteType_of_locallyOfFiniteType g y'
  have he : CommRingCat.ofHom (g.residueFieldMap y').hom = g.residueFieldMap y' := by ext; rfl
  have hbc := isLocallyNoetherian_baseChange_iff (Y.residueField (g.base y'))
    (Y'.residueField y') (f.fiber (g.base y')) (f.fiberToSpecResidueField (g.base y'))
  rw [RingHom.algebraMap_toAlgebra, he] at hbc
  exact hbc.trans ⟨fun _ => isLocallyNoetherian_of_isOpenImmersion (fiberPullbackIso f g y').hom,
    fun _ => isLocallyNoetherian_of_isOpenImmersion (fiberPullbackIso f g y').inv⟩

/-- **The property of Tag 045V.** A morphism of schemes has locally Noetherian fibres and is
Cohen–Macaulay. -/
public abbrev cohenMacaulayWithLocallyNoetherianFibers : MorphismProperty Scheme.{u} :=
  fun _ _ f => ∃ hf : ∀ y, IsLocallyNoetherian (f.fiber y), Scheme.Hom.IsCohenMacaulay f hf

/-- A morphism has locally Noetherian fibres and is Cohen–Macaulay exactly when it is flat with
Cohen–Macaulay fibres. The locally Noetherian condition is automatic, being implied by
Cohen–Macaulayness of the fibres. -/
public theorem cohenMacaulayWithLocallyNoetherianFibers_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cohenMacaulayWithLocallyNoetherianFibers f ↔
      Flat f ∧ ∀ y : Y, IsCohenMacaulay (f.fiber y) := by
  refine ⟨fun ⟨hf, hcm⟩ => (isCohenMacaulay_iff_flat_and_fibers f hf).mp hcm, ?_⟩
  rintro ⟨hflat, hfib⟩
  exact ⟨fun y => (hfib y).isLocallyNoetherian,
    (isCohenMacaulay_iff_flat_and_fibers f _).mpr ⟨hflat, hfib⟩⟩

/-- The fibres of two isomorphic arrows of schemes are isomorphic. -/
public noncomputable def fiberIsoOfArrowIso {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (e : Arrow.mk f ≅ Arrow.mk g) (y : Y) :
    f.fiber y ≅ g.fiber (e.hom.right.base y) := by
  have _ : IsIso e.hom.left := by dsimp; infer_instance
  have _ : IsIso e.hom.right := by dsimp; infer_instance
  have h₁ : f ≫ e.hom.right = e.hom.left ≫ g := e.hom.w.symm
  have h₂ : Y.fromSpecResidueField y ≫ e.hom.right =
      Spec.map (e.hom.right.residueFieldMap y) ≫
        Y'.fromSpecResidueField (e.hom.right.base y) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField e.hom.right y).symm
  have _ : IsIso (Spec.map (e.hom.right.residueFieldMap y)) := inferInstance
  exact @asIso Scheme.{u} Scheme.instCategory _ _
    (pullback.map f (Y.fromSpecResidueField y) g
      (Y'.fromSpecResidueField (e.hom.right.base y)) e.hom.left
      (Spec.map (e.hom.right.residueFieldMap y)) e.hom.right h₁ h₂)
    (pullback.map_isIso f (Y.fromSpecResidueField y) g
      (Y'.fromSpecResidueField (e.hom.right.base y)) e.hom.left
      (Spec.map (e.hom.right.residueFieldMap y)) e.hom.right h₁ h₂)

/-- Having locally Noetherian fibres and being Cohen–Macaulay is invariant under isomorphism of
arrows. -/
public instance cohenMacaulayWithLocallyNoetherianFibers_respectsIso :
    MorphismProperty.RespectsIso
      (cohenMacaulayWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}) := by
  refine MorphismProperty.RespectsIso.of_respects_arrow_iso
    cohenMacaulayWithLocallyNoetherianFibers ?_
  intro a b e h
  rw [cohenMacaulayWithLocallyNoetherianFibers_iff] at h ⊢
  have _ : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    (Stacks.Descent.flat_isLocalAtTarget_fpqc.{u}).toRespects
  refine ⟨(MorphismProperty.arrow_iso_iff (@Flat : MorphismProperty Scheme.{u}) e).mp h.1,
    fun y' => ?_⟩
  exact (isCohenMacaulay_iff_of_iso (fiberIsoOfArrowIso b.hom a.hom e.symm y')).mpr (h.2 _)

/-- **Stacks Project, Tag 045V.** Having locally Noetherian fibres and being Cohen–Macaulay is
local on the target for the fppf topology. -/
@[stacks 045V "fppf local on the target"]
public instance cohenMacaulayWithLocallyNoetherianFibers_isLocalAtTarget_fppf :
    (cohenMacaulayWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtTarget
      Scheme.fppfPrecoverage := by
  have _ : MorphismProperty.RespectsIso
      (cohenMacaulayWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}) :=
    cohenMacaulayWithLocallyNoetherianFibers_respectsIso
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff ?_
  intro X Y f R hR
  have hdec : R ∈ Scheme.jointlySurjectivePrecoverage Y ∧
      R ∈ MorphismProperty.precoverage
        (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Y := hR
  obtain ⟨hcover, hprops⟩ := hdec
  constructor
  · rintro ⟨hf, hcm⟩ U g hgPull hRg
    have _ : Flat g := (hprops hRg).1
    have _ : LocallyOfFinitePresentation g := (hprops hRg).2
    refine ⟨fun y' => isLocallyNoetherian_fiber_pullback f g hf y', fun x' => ?_⟩
    exact isCohenMacaulayAt_pullback f g hf x' (hcm ((pullback.fst f g).base x'))
  · intro hlocal
    have hflat : Flat f := by
      refine (MorphismProperty.IsLocalAtTarget.of_le
        (P := (@Flat : MorphismProperty Scheme.{u}))
        Scheme.fppfPrecoverage_le_fpqcPrecoverage).of_forall_pullbackSnd hR ?_
      intro U g _ hRg
      obtain ⟨hf', hcm'⟩ := hlocal g hRg
      exact ((isCohenMacaulay_iff_flat_and_fibers (pullback.snd f g) hf').mp hcm').1
    have hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y) := by
      intro y
      obtain ⟨Z, g, hg, ⟨z, hz⟩⟩ :=
        (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
          (F := Scheme.forget)).mp hcover y
      have _ : LocallyOfFinitePresentation g := (hprops hg).2
      obtain ⟨hf', -⟩ := hlocal g hg
      obtain rfl : g.base z = y := hz
      exact (isLocallyNoetherian_fiber_pullback_iff f g z).mpr (hf' z)
    refine ⟨hf, fun x => ?_⟩
    obtain ⟨Z, g, hg, ⟨z, hz⟩⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
        (F := Scheme.forget)).mp hcover (f.base x)
    have _ : LocallyOfFinitePresentation g := (hprops hg).2
    obtain ⟨x', hx', -⟩ :=
      Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback f g) x z hz.symm
    obtain ⟨hf', hcm'⟩ := hlocal g hg
    simpa [hx'] using isCohenMacaulayAt_of_pullback_of_flat f g hf x'
      ((Flat.iff_flat_stalkMap f).mp hflat _) (hcm' x')

/-- The fibre of a composite `g ≫ f` over a point `y` of the outer target is the base change of
`g` along the embedding of the fibre of `f` over `y`. -/
public noncomputable def fiberCompIso {U X Y : Scheme.{u}} (g : U ⟶ X) (f : X ⟶ Y) (y : Y) :
    (g ≫ f).fiber y ≅ pullback g (f.fiberι y) :=
  (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) g).symm

/-- The fibres of a composite with a syntomic morphism are locally Noetherian as soon as the
fibres of the second factor are: the fibre of the composite is the base change of the syntomic
morphism along the embedding of a fibre of the second factor, hence locally of finite type over a
locally Noetherian scheme. -/
public theorem isLocallyNoetherian_fiber_comp_of_syntomic {U X Y : Scheme.{u}} {g : U ⟶ X}
    (hg : Syntomic g) (f : X ⟶ Y) (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (y : Y) :
    IsLocallyNoetherian ((g ≫ f).fiber y) := by
  have _ : LocallyOfFinitePresentation g := locallyOfFinitePresentation hg
  have _ : LocallyOfFiniteType g := inferInstance
  have _ : IsLocallyNoetherian (f.fiber y) := hf y
  have _ : IsLocallyNoetherian (pullback g (f.fiberι y)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g (f.fiberι y))
  have _ : IsOpenImmersion (fiberCompIso g f y).hom := inferInstance
  exact isLocallyNoetherian_of_isOpenImmersion (fiberCompIso g f y).hom

/-- **Stacks Project, Tag 045V.** Having locally Noetherian fibres and being Cohen–Macaulay is
local on the source for the syntomic topology. -/
@[stacks 045V "syntomic local on the source"]
public instance cohenMacaulayWithLocallyNoetherianFibers_isLocalAtSource_syntomic :
    (cohenMacaulayWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtSource
      (Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u})) := by
  have _ : MorphismProperty.RespectsIso
      (cohenMacaulayWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}) :=
    cohenMacaulayWithLocallyNoetherianFibers_respectsIso
  have _ : MorphismProperty.IsLocalAtSource (@Flat : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtSource.of_le Scheme.syntomicPrecoverage_le_fpqcPrecoverage
  refine MorphismProperty.IsLocalAtSource.mk_of_iff ?_
  intro X Y f R hR
  have hdec : R ∈ Scheme.jointlySurjectivePrecoverage X ∧
      R ∈ MorphismProperty.precoverage (@Syntomic : MorphismProperty Scheme.{u}) X := hR
  obtain ⟨hcover, hprops⟩ := hdec
  constructor
  · rintro ⟨hf, hcm⟩ U g hg
    have hsyn : Syntomic g := hprops hg
    have _ : LocallyOfFinitePresentation g := locallyOfFinitePresentation hsyn
    have hgfib : ∀ x : X, IsLocallyNoetherian (g.fiber x) := fun x =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation g x
    have hgffib := isLocallyNoetherian_fiber_comp_of_syntomic hsyn f hf
    exact ⟨hgffib, isCohenMacaulay_comp g f hgfib hf hgffib
      (isCohenMacaulay_of_syntomic hsyn hgfib) hcm⟩
  · intro hlocal
    have hflat : Flat f := by
      refine MorphismProperty.IsLocalAtSource.of_forall_comp hR ?_
      intro U g hg
      obtain ⟨hgf, hcmgf⟩ := hlocal hg
      exact ((isCohenMacaulay_iff_flat_and_fibers (g ≫ f) hgf).mp hcmgf).1
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
    obtain ⟨hgf, hcmgf⟩ := hlocal hg
    obtain rfl : g u = x := hu
    exact isCohenMacaulayAt_right_of_comp_of_flat g f hffib hgf hcmgf (flat (hprops hg)) u

end AlgebraicGeometry
