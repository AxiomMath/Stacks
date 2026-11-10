module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.RegularMorphism
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.LocallyNoetherianFibres
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular morphisms with locally Noetherian fibres are fppf local on the target

For a morphism of schemes, the property of having locally Noetherian fibres and being regular may
be tested after an fppf covering of the target.

## Main definitions

* `AlgebraicGeometry.regularMorphisms` is regularity of a morphism of schemes, as a property of
  morphisms.
* `AlgebraicGeometry.regularWithLocallyNoetherianFibers` is the morphism property combining
  locally Noetherian fibres with regularity.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers`: a morphism is
  regular exactly when it is flat and all of its fibres are geometrically regular.
* `AlgebraicGeometry.isGeometricallyRegular_iff_of_isoOver`: geometric regularity over a field is
  invariant under an isomorphism over that field.
* `AlgebraicGeometry.isGeometricallyRegular_fiber_iff_of_isPullback`: a fibre with locally
  Noetherian source is geometrically regular exactly when the corresponding fibre of a base
  change along a morphism locally of finite type is.
* `AlgebraicGeometry.regularWithLocallyNoetherianFibers_isLocalAtTarget_fppf`: the property is
  local on the target for the fppf topology.

## Implementation notes

Regularity of a morphism is defined pointwise, as flatness at a point together with geometric
regularity of the fibre at the corresponding point. The first result below repackages this as a
condition on the morphism and on each whole fibre, which is the form in which the source states
it; it holds with no Noetherian hypothesis, since both sides quantify over the same points.

The fibre of a base change is the base change of a fibre along the induced extension of residue
fields, which is finitely generated when the covering morphism is locally of finite presentation.
Geometric regularity is therefore transported by Tag 038W, whose hypotheses are exactly a
finitely generated extension and a locally Noetherian source — both available here, the latter
because having locally Noetherian fibres is part of the property. Flatness is fppf local on the
target by Tag 02L2 and locally Noetherian fibres by Tag 0392.

## References

* [Stacks Project, Tag 07RA](https://stacks.math.columbia.edu/tag/07RA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 07R8**, the equivalence of conditions (1) and (2). A morphism of
schemes is regular exactly when it is flat and all of its fibres are geometrically regular. -/
@[ega "IV 17.5.2" "Restating clause", ega "IV 6.8.4" "more general"]
public theorem Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    f.IsRegular ↔ Flat f ∧ ∀ y : Y, IsGeometricallyRegular (f.fiberToSpecResidueField y) := by
  constructor
  · intro hf
    refine ⟨(Flat.iff_flat_stalkMap f).2 fun x => (hf x).1, fun y z => ?_⟩
    let x := f.fiberι y z
    have hx : x = f.fiberι y z := rfl
    clear_value x
    have hxy : f x = y := by
      rw [hx]
      change (f.fiberι y ≫ f) z = y
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

/-- Geometric regularity over a field passes along an isomorphism over that field. -/
private theorem isGeometricallyRegular_of_isoOver {k : Type u} [Field k] {X Z : Scheme.{u}}
    (i : X ≅ Z) (f : X ⟶ Spec (.of k)) (f' : Z ⟶ Spec (.of k)) (hi : f = i.hom ≫ f')
    (hf : IsGeometricallyRegular f') : IsGeometricallyRegular f := by
  have h₁ : f ≫ 𝟙 (Spec (.of k)) = i.hom ≫ f' := by simpa using hi
  intro x K _ _ _ _ x'' hx''
  let φ : Spec (.of K) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k K))
  have h₂ : φ ≫ 𝟙 (Spec (.of k)) = 𝟙 (Spec (.of K)) ≫ φ := by simp
  let q : pullback f φ ⟶ pullback f' φ := pullback.map f φ f' φ i.hom (𝟙 _) (𝟙 _) h₁ h₂
  have _ : IsIso q := pullback.map_isIso f φ f' φ i.hom (𝟙 _) (𝟙 _) h₁ h₂
  have hcomp : q ≫ pullback.fst f' φ = pullback.fst f φ ≫ i.hom := by
    change pullback.lift (pullback.fst f φ ≫ i.hom) (pullback.snd f φ ≫ 𝟙 _) _ ≫
      pullback.fst f' φ = _
    rw [pullback.lift_fst]
  have hx' : pullback.fst f' φ (q x'') = i.hom x := by
    rw [← hx'', ← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
  have _ : IsRegularLocalRing ((pullback f' φ).presheaf.stalk (q x'')) :=
    hf (i.hom x) K (q x'') hx'
  exact IsRegularLocalRing.of_ringEquiv (asIso (q.stalkMap x'')).commRingCatIsoToRingEquiv

/-- Geometric regularity over a field is invariant under an isomorphism over that field. -/
public theorem isGeometricallyRegular_iff_of_isoOver {k : Type u} [Field k] {X Z : Scheme.{u}}
    (i : X ≅ Z) (f : X ⟶ Spec (.of k)) (f' : Z ⟶ Spec (.of k)) (hi : f = i.hom ≫ f') :
    IsGeometricallyRegular f ↔ IsGeometricallyRegular f' :=
  ⟨isGeometricallyRegular_of_isoOver i.symm f' f (by simp [hi]),
    isGeometricallyRegular_of_isoOver i f f' hi⟩

/-- For a cartesian square whose right-hand morphism is locally of finite type, a fibre of the
left-hand morphism is geometrically regular exactly when the corresponding fibre above is. -/
public theorem isGeometricallyRegular_fiber_iff_of_isPullback {X Y U V : Scheme.{u}}
    {f : X ⟶ Y} {g : U ⟶ Y} {fst : V ⟶ X} {snd : V ⟶ U} (h : IsPullback fst snd f g)
    [LocallyOfFiniteType g] (x : U) (hnoeth : IsLocallyNoetherian (f.fiber (g x))) :
    IsGeometricallyRegular (snd.fiberToSpecResidueField x) ↔
      IsGeometricallyRegular (f.fiberToSpecResidueField (g x)) := by
  let _ : Algebra (Y.residueField (g x)) (U.residueField x) :=
    (g.residueFieldMap x).hom.toAlgebra
  have _ : Algebra.EssFiniteType (Y.residueField (g x)) (U.residueField x) := by
    change ((IsLocalRing.ResidueField.map (g.stalkMap x).hom)).EssFiniteType
    exact RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap g x)
  have _ : IsLocallyNoetherian (f.fiber (g x)) := hnoeth
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback h x
  refine (isGeometricallyRegular_iff_of_isoOver hpb.isoPullback _ _
    hpb.isoPullback_hom_snd.symm).trans ?_
  exact (geometricallyRegular_baseChange_iff (Y.residueField (g x)) (U.residueField x)
    (f.fiber (g x)) (f.fiberToSpecResidueField (g x))).symm

/-- Regularity of a morphism of schemes, as a property of morphisms. -/
public abbrev regularMorphisms : MorphismProperty Scheme.{u} := fun _ _ f => f.IsRegular

/-- **The property of Tag 07RA.** A morphism of schemes has locally Noetherian fibres and is
regular. -/
public abbrev regularWithLocallyNoetherianFibers : MorphismProperty Scheme.{u} :=
  locallyNoetherianFibers ⊓ regularMorphisms

/-- Having locally Noetherian fibres and being regular is invariant under isomorphism of
arrows. -/
public instance regularWithLocallyNoetherianFibers_respectsIso :
    (regularWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}).RespectsIso := by
  have _ : MorphismProperty.RespectsIso
      (locallyNoetherianFibers : MorphismProperty Scheme.{u}) :=
    locallyNoetherianFibers_respectsIso
  refine MorphismProperty.RespectsIso.of_respects_arrow_iso _ ?_
  intro a b e hf
  have hnoeth : ∀ y : b.right, IsLocallyNoetherian (b.hom.fiber y) :=
    (MorphismProperty.arrow_iso_iff
      (locallyNoetherianFibers : MorphismProperty Scheme.{u}) e).mp hf.1
  obtain ⟨hflat, hgeom⟩ :=
    (Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers a.hom).mp hf.2
  have _ : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    (Stacks.Descent.flat_isLocalAtTarget_fpqc.{u}).toRespects
  refine ⟨hnoeth, (Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers b.hom).mpr
    ⟨(MorphismProperty.arrow_iso_iff (@Flat : MorphismProperty Scheme.{u}) e).mp hflat,
      fun y => ?_⟩⟩
  have hpb : IsPullback e.inv.left b.hom a.hom e.inv.right :=
    IsPullback.of_horiz_isIso ⟨e.inv.w⟩
  exact (isGeometricallyRegular_fiber_iff_of_isPullback hpb y
    (hf.1 (e.inv.right.base y))).mpr (hgeom (e.inv.right.base y))

/-- **Stacks Project, Tag 07RA.** Having locally Noetherian fibres and being regular is local on
the target for the fppf topology. -/
@[stacks 07RA "fppf local on the target"]
public instance regularWithLocallyNoetherianFibers_isLocalAtTarget_fppf :
    (regularWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtTarget
      Scheme.fppfPrecoverage := by
  have hnoethLocal := locallyNoetherianFibers_isLocalAtTarget_fppf.{u}
  have hflatLocal : MorphismProperty.IsLocalAtTarget
      (@Flat : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff ?_
  intro X Y f R hR
  have hdec : R ∈ Scheme.jointlySurjectivePrecoverage Y ∧
      R ∈ MorphismProperty.precoverage
        (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Y := hR
  obtain ⟨hcover, hprops⟩ := hdec
  constructor
  · rintro ⟨hnoeth, hreg⟩ U g hgPull hRg
    have _ : LocallyOfFinitePresentation g := (hprops hRg).2
    obtain ⟨hflat, hgeom⟩ :=
      (Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers f).mp hreg
    refine ⟨hnoethLocal.pullbackSnd hR hRg hnoeth,
      (Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers
        (pullback.snd f g)).mpr ⟨hflatLocal.pullbackSnd hR hRg hflat, fun x => ?_⟩⟩
    exact (isGeometricallyRegular_fiber_iff_of_isPullback (IsPullback.of_hasPullback f g) x
      (hnoeth (g x))).mpr (hgeom (g x))
  · intro hlocal
    have hnoeth : ∀ y : Y, IsLocallyNoetherian (f.fiber y) :=
      hnoethLocal.of_forall_pullbackSnd hR fun hRg => (hlocal _ hRg).1
    have hflat : Flat f := hflatLocal.of_forall_pullbackSnd hR fun hRg =>
      ((Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers
        (pullback.snd f _)).mp (hlocal _ hRg).2).1
    refine ⟨hnoeth, (Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers f).mpr
      ⟨hflat, fun y => ?_⟩⟩
    obtain ⟨Z, g, hg, ⟨z, rfl⟩⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
        (F := Scheme.forget)).mp hcover y
    have _ : LocallyOfFinitePresentation g := (hprops hg).2
    exact (isGeometricallyRegular_fiber_iff_of_isPullback (IsPullback.of_hasPullback f g) z
      (hnoeth (g z))).mp
      (((Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers
        (pullback.snd f g)).mp (hlocal g hg).2).2 z)

end AlgebraicGeometry
