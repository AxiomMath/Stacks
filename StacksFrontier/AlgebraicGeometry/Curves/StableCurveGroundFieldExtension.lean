module

public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenFibreAmple
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic

/-!
# Stability of a nodal curve does not depend on the ground field

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` whose
singularities are at worst nodal, and let `K/k` be a field extension. Then `X` has genus at least
two and neither a rational tail nor a rational bridge exactly when its base change `X_K` has.

On such curves the condition is the ampleness of the dualizing sheaf (Stacks 0E76 (2)(b) ⟺ (c),
`AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField`),
`X_K` is again such a curve (Stacks 0BY9, and the base change of nodes, Stacks 0C56), and
`ω_{X_K} ≅ (g')^* ω_X` (Stacks 0E32). Ampleness ascends along the affine projection `X_K ⟶ X`, and
descends along it because `Spec K ⟶ Spec k` is an affine flat covering (the descent of ampleness
of Stacks 0D2P).

This is the form in which the stability of the fibres of a family of curves is transported along
an étale chart of the base in the proof of Stacks 0E8A: the residue fields of a chart are finite
separable extensions of those of the base.

## Main results

* `AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_iff_of_isPullback_algebraMap`:
  the invariance along `Spec K ⟶ Spec k` for a field extension `K/k`.
* `AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_iff_of_isPullback`: the same along
  an arbitrary morphism of spectra of fields.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.AmpleLocallyClosed (pullbackModule)

/-- **Stability of a nodal curve is invariant under extension of the ground field.** Let
`f : X ⟶ Spec k` be proper with `X` of dimension one, `H⁰(X, 𝒪_X) = k` and at-worst-nodal
singularities, let `K/k` be a field extension and `X'` the base change of `X` to `K`, presented by
a cartesian square. Then `X` has genus at least two and neither a rational tail nor a rational
bridge if and only if `X'` has. -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_iff_of_isPullback_algebraMap
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Spec (.of K)} {f : X ⟶ Spec (.of k)}
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) [IsProper f]
    (hdim : topologicalKrullDim X = 1) (hglob : Function.Bijective f.appTop)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    HasGenusTwoNoRationalTailNoRationalBridge k f ↔
      HasGenusTwoNoRationalTailNoRationalBridge K f' := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective f.appTop).2 hglob
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := inferInstance
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f'.appTop) :=
    isIso_globalSections_baseChange k K g' f' f h
  have : IsIso f'.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of K)).inv _
  have hglob' : Function.Bijective f'.appTop :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hdim' : topologicalKrullDim X' = 1 :=
    (topologicalKrullDim_baseChange k K g' f' f h).trans hdim
  -- the base change is again nodal: on the chosen pullback, then along `X' ≅ X ×_k K`
  have hnodal' : let : X'.Over (Spec (.of K)) := ⟨f'⟩
      Stacks.Curves.HasAtWorstNodalSingularities K X' := by
    have hPb : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) := IsPullback.of_hasPullback _ _
    have : IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      MorphismProperty.of_isPullback (P := @IsProper) hPb inferInstance
    exact Stacks.Curves.hasAtWorstNodalSingularities_of_isIso
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) f'
      ((topologicalKrullDim_baseChange k K _ _ f hPb).trans hdim) h.isoPullback.hom (𝟙 _)
      (by rw [Spec.map_id, Category.comp_id, IsPullback.isoPullback_hom_snd])
      (Stacks.Curves.hasAtWorstNodalSingularities_baseChange k K X
        (equidimensional_of_isIso_globalSections_of_dimension_one k f hdim) hdim hnodal)
  rw [hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField k f hdim hglob
      hnodal,
    hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField K f' hdim'
      hglob' hnodal']
  let : X'.Over (Spec (.of K)) := ⟨f'⟩
  have : IsProper (X' ↘ Spec (.of K)) := inferInstanceAs (IsProper f')
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k f
  have : ConnectedSpace X' := connectedSpace_of_isIso_globalSections K f'
  have hω : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  have hω' : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f') :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K X' hdim' hnodal'
  -- `ω_{X'} ≅ (g')^* ω_X`, Stacks 0E32
  let e := Stacks.Duality.dualizingSheafOverFieldBaseChangeIso f g' f' h
  have : IsAffineHom g' := MorphismProperty.of_isPullback h.flip inferInstance
  have := Stacks.Modules.isInvertible_pullback g' (Stacks.Duality.dualizingSheafOverField f)
  constructor
  · rintro ⟨_, hamp⟩
    have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    exact ⟨hω', Scheme.Modules.isAmple_of_iso e
      (Scheme.Modules.isAmple_pullback_of_isAffineHom g' _ hamp)⟩
  · rintro ⟨_, hamp'⟩
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
      Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
    have h3 : Stacks.Ample.IsAmple X (Stacks.Duality.dualizingSheafOverField f) :=
      Stacks.Descent.isAmple_of_forall_isAmple_pullbackModule_of_affineFlatCover (m := 1) f
        (Stacks.Duality.dualizingSheafOverField f) (T := fun _ => Spec (.of K))
        (t := fun _ => Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (fun _ => ⟨0, IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩)
        (Y' := fun _ => X') (pr := fun _ => g') (q' := fun _ => f') (fun _ => h)
        (fun _ => (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).2
          (Scheme.Modules.isAmple_of_iso e.symm hamp'))
    exact ⟨hω, (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).1 h3⟩

/-- **Stability of a nodal curve is invariant under extension of the ground field**, along an
arbitrary morphism `ι : Spec L ⟶ Spec K` of spectra of fields (which is `Spec` of a field
extension `K → L`). -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_iff_of_isPullback
    {K L : Type u} [Field K] [Field L] {X X' : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Spec (.of L)} {f : X ⟶ Spec (.of K)} {ι : Spec (.of L) ⟶ Spec (.of K)}
    (h : IsPullback g' f' f ι) [IsProper f]
    (hdim : topologicalKrullDim X = 1) (hglob : Function.Bijective f.appTop)
    (hnodal : letI : X.Over (Spec (.of K)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities K X) :
    HasGenusTwoNoRationalTailNoRationalBridge K f ↔
      HasGenusTwoNoRationalTailNoRationalBridge L f' := by
  let : Algebra K L := (Spec.preimage ι).hom.toAlgebra
  have hι : Spec.map (CommRingCat.ofHom (algebraMap K L)) = ι := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage ι).hom) = ι
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have h' : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    rwa [hι]
  exact hasGenusTwoNoRationalTailNoRationalBridge_iff_of_isPullback_algebraMap K L h' hdim hglob
    hnodal

end AlgebraicGeometry

end
