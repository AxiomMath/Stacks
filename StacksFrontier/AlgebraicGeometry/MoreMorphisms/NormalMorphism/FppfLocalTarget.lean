module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.NormalMorphism
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.BaseFieldExtension
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.Normal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.LocallyNoetherianFibres
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.Normal

/-!
# Normal morphisms with locally Noetherian fibres are fppf local on the target

For a morphism of schemes, the property of having locally Noetherian fibres and being normal may
be tested after an fppf covering of the target.

## Main definitions

* `AlgebraicGeometry.normalMorphisms` is normality of a morphism of schemes, as a property of
  morphisms.
* `AlgebraicGeometry.normalWithLocallyNoetherianFibers` is the morphism property combining
  locally Noetherian fibres with normality.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers`: a morphism is
  normal exactly when it is flat and all of its fibres are geometrically normal.
* `AlgebraicGeometry.isGeometricallyNormal_fiber_pullback_iff`: a fibre of a morphism is
  geometrically normal exactly when the corresponding fibre of any base change is.
* `AlgebraicGeometry.normalMorphisms_isStableUnderBaseChange`: normality is stable under
  arbitrary base change.
* `AlgebraicGeometry.normalWithLocallyNoetherianFibers_isLocalAtTarget_fppf`: the property is
  local on the target for the fppf topology.

## References

* [Stacks Project, Tag 0393](https://stacks.math.columbia.edu/tag/0393)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- Geometric normality over a field is invariant under an isomorphism over that field. -/
public theorem isGeometricallyNormal_iff_of_isoOver {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Z ⟶ Spec (.of k)) (e : X ≅ Z) (he : e.hom ≫ g = f) :
    IsGeometricallyNormal f ↔ IsGeometricallyNormal g := by
  have h₁ : f ≫ 𝟙 (Spec (.of k)) = e.hom ≫ g := by simpa using he.symm
  have hiso : ∀ (K : Type u) [Field K] [Algebra k K],
      pullback f (Spec.map (ofHom (algebraMap k K))) ≅
        pullback g (Spec.map (ofHom (algebraMap k K))) := by
    intro K _ _
    have h₂ : Spec.map (ofHom (algebraMap k K)) ≫ 𝟙 (Spec (.of k)) =
        𝟙 (Spec (.of K)) ≫ Spec.map (ofHom (algebraMap k K)) := by simp
    have hmap : IsIso (pullback.map f (Spec.map (ofHom (algebraMap k K))) g
        (Spec.map (ofHom (algebraMap k K))) e.hom (𝟙 _) (𝟙 _) h₁ h₂) :=
      pullback.map_isIso f (Spec.map (ofHom (algebraMap k K))) g
        (Spec.map (ofHom (algebraMap k K))) e.hom (𝟙 _) (𝟙 _) h₁ h₂
    exact @asIso _ _ _ _ (pullback.map f (Spec.map (ofHom (algebraMap k K))) g
      (Spec.map (ofHom (algebraMap k K))) e.hom (𝟙 _) (𝟙 _) h₁ h₂) hmap
  have hX := (geometricallyNormal_tfae k X f).out 1 2
  have hZ := (geometricallyNormal_tfae k Z g).out 1 2
  rw [hX, hZ]
  refine ⟨fun h K _ _ ↦ ?_, fun h K _ _ ↦ ?_⟩
  · have _ : IsNormal (pullback f (Spec.map (ofHom (algebraMap k K)))) := h K
    exact isNormal_of_flat_surjective (hiso K).hom
  · have _ : IsNormal (pullback g (Spec.map (ofHom (algebraMap k K)))) := h K
    exact isNormal_of_flat_surjective (hiso K).inv

/-- A fibre of a morphism of schemes is geometrically normal exactly when the corresponding fibre
of any base change of it is geometrically normal. -/
public theorem isGeometricallyNormal_fiber_pullback_iff {X Y U : Scheme.{u}} (f : X ⟶ Y)
    (g : U ⟶ Y) (u : U) :
    IsGeometricallyNormal (f.fiberToSpecResidueField (g u)) ↔
      IsGeometricallyNormal ((pullback.snd f g).fiberToSpecResidueField u) := by
  let _ : Algebra (Y.residueField (g u)) (U.residueField u) :=
    (g.residueFieldMap u).hom.toAlgebra
  have he : ofHom (g.residueFieldMap u).hom = g.residueFieldMap u := by ext; rfl
  have hbc := isGeometricallyNormal_iff_baseChange (Y.residueField (g u)) (U.residueField u)
    (f.fiber (g u)) (f.fiberToSpecResidueField (g u))
  rw [RingHom.algebraMap_toAlgebra, he] at hbc
  exact hbc.trans (isGeometricallyNormal_iff_of_isoOver _ _ (fiberPullbackIso f g u).symm
    (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f g) u).isoPullback_inv_snd)

/-- A morphism of schemes is normal exactly when it is flat and all of its fibres are
geometrically normal. -/
public theorem Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    f.IsNormal ↔ Flat f ∧ ∀ y : Y, IsGeometricallyNormal (f.fiberToSpecResidueField y) := by
  constructor
  · intro hf
    refine ⟨(Flat.iff_flat_stalkMap f).2 fun x ↦ (hf x).1, fun y z ↦ ?_⟩
    let x := f.fiberι y z
    have hx : x = f.fiberι y z := rfl
    clear_value x
    have hxy : f x = y := by
      rw [hx]
      show (f.fiberι y ≫ f) z = y
      rw [f.fiber_fac]
      simp
    cases hxy
    have hz : f.asFiber x = z := by
      refine (f.fiberι (f x)).isEmbedding.injective ?_
      rw [Scheme.Hom.fiberι_asFiber]
      exact hx
    simpa [hz] using (hf x).2
  · rintro ⟨hflat, hgeom⟩ x
    exact ⟨(Flat.iff_flat_stalkMap f).mp hflat x, hgeom (f x) (f.asFiber x)⟩

/-- Normality of a morphism of schemes, as a property of morphisms. -/
public abbrev normalMorphisms : MorphismProperty Scheme.{u} := fun _ _ f => f.IsNormal

/-- Normality of a morphism of schemes is invariant under an isomorphism of its source. -/
private theorem isNormal_of_sourceIso {X X' Y : Scheme.{u}} (i : X ≅ X') (f : X ⟶ Y)
    (f' : X' ⟶ Y) (hi : f = i.hom ≫ f') (hf : f.IsNormal) : f'.IsNormal := by
  have _ : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    (Stacks.Descent.flat_isLocalAtTarget_fpqc.{u}).toRespects
  obtain ⟨hflat, hgeom⟩ := (Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers f).mp hf
  have e : Arrow.mk f ≅ Arrow.mk f' := Arrow.isoMk i (Iso.refl Y) hi.symm
  refine (Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers f').mpr
    ⟨(MorphismProperty.arrow_iso_iff (@Flat : MorphismProperty Scheme.{u}) e).mp hflat,
      fun y ↦ ?_⟩
  have hw : f ≫ 𝟙 Y = i.hom ≫ f' := by simpa using hi
  have hw' : Y.fromSpecResidueField y ≫ 𝟙 Y =
      𝟙 (Spec (Y.residueField y)) ≫ Y.fromSpecResidueField y := by simp
  have hm : IsIso (pullback.map f (Y.fromSpecResidueField y) f'
      (Y.fromSpecResidueField y) i.hom (𝟙 _) (𝟙 _) hw hw') :=
    pullback.map_isIso f (Y.fromSpecResidueField y) f'
      (Y.fromSpecResidueField y) i.hom (𝟙 _) (𝟙 _) hw hw'
  refine (isGeometricallyNormal_iff_of_isoOver _ _
    (@asIso _ _ _ _ (pullback.map f (Y.fromSpecResidueField y) f'
      (Y.fromSpecResidueField y) i.hom (𝟙 _) (𝟙 _) hw hw') hm) ?_).mp (hgeom y)
  show pullback.map f (Y.fromSpecResidueField y) f' (Y.fromSpecResidueField y)
      i.hom (𝟙 _) (𝟙 _) hw hw' ≫ pullback.snd f' (Y.fromSpecResidueField y) =
    pullback.snd f (Y.fromSpecResidueField y)
  rw [pullback.lift_snd, Category.comp_id]

/-- Normality of a morphism of schemes is stable under arbitrary base change. -/
public instance normalMorphisms_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (normalMorphisms : MorphismProperty Scheme.{u}) where
  of_isPullback {X Y Y' S f g f' g'} H hg := by
    have hpull : (pullback.snd g f).IsNormal := by
      obtain ⟨hflat, hgeom⟩ :=
        (Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers g).mp hg
      have _ : Flat g := hflat
      have _ : Flat (pullback.snd g f) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (IsPullback.of_hasPullback g f) hflat
      exact (Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers
        (pullback.snd g f)).mpr ⟨inferInstance, fun u ↦
          (isGeometricallyNormal_fiber_pullback_iff g f u).mp (hgeom (f u))⟩
    exact isNormal_of_sourceIso H.isoPullback.symm (pullback.snd g f) g'
      ((Iso.eq_inv_comp H.isoPullback).mpr H.isoPullback_hom_snd) hpull

/-- The property of a morphism of schemes of having locally Noetherian fibres and being normal. -/
public abbrev normalWithLocallyNoetherianFibers : MorphismProperty Scheme.{u} :=
  locallyNoetherianFibers ⊓ normalMorphisms

/-- Normality of a morphism of schemes is local on the target for the fppf topology. -/
public instance normalMorphisms_isLocalAtTarget_fppf :
    (normalMorphisms : MorphismProperty Scheme.{u}).IsLocalAtTarget
      Scheme.fppfPrecoverage := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff ?_
  intro X Y f R hR
  have hdec : R ∈ Scheme.jointlySurjectivePrecoverage Y ∧
      R ∈ MorphismProperty.precoverage
        (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Y := hR
  obtain ⟨hcover, -⟩ := hdec
  constructor
  · intro hf U g hgPull hRg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g) hf
  · intro hlocal
    have hflat : Flat f := by
      refine (MorphismProperty.IsLocalAtTarget.of_le
        (P := (@Flat : MorphismProperty Scheme.{u}))
        Scheme.fppfPrecoverage_le_fpqcPrecoverage).of_forall_pullbackSnd hR ?_
      intro U g _ hRg
      exact ((Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers
        (pullback.snd f g)).mp (hlocal g hRg)).1
    refine (Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers f).mpr
      ⟨hflat, fun y ↦ ?_⟩
    obtain ⟨Z, g, hg, ⟨z, rfl⟩⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
        (F := Scheme.forget)).mp hcover y
    exact (isGeometricallyNormal_fiber_pullback_iff f g z).mpr
      (((Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers
        (pullback.snd f g)).mp (hlocal g hg)).2 z)

/-- Having locally Noetherian fibres and being normal is local on
the target for the fppf topology. -/
@[stacks 0393 "fppf local on the target"]
public instance normalWithLocallyNoetherianFibers_isLocalAtTarget_fppf :
    (normalWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtTarget
      Scheme.fppfPrecoverage :=
  inferInstance

end AlgebraicGeometry
