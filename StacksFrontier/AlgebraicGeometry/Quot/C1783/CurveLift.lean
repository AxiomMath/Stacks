module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningLimit.Converse
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PicardRestrictionPullback
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Thickenings.IdealSheafCohomologyTransfer
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ProperFibreDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationProjective
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison

/-!
# Lifting a relatively ample invertible module on a curve along a first-order thickening

Let `i : X ⟶ X'` be a first-order thickening and `f' : X' ⟶ T'` a proper morphism to an affine
scheme all of whose fibres have dimension at most one. Every invertible `𝒪_X`-module `L` which is
ample relative to `i ≫ f'` is the restriction `i^* L'` of an invertible `𝒪_{X'}`-module `L'`,
and every such `L'` is ample relative to `f'`. This is the core of the proof of
[Stacks, Tag 0DPJ].

The proof has three steps.

* *Vanishing of the obstruction.* The ideal sheaf `𝓘` of `i` is a quasi-coherent
  `𝒪_{X'}`-module, and a proper morphism onto an affine scheme with fibres of dimension at most
  one has no quasi-coherent cohomology above degree one ([Stacks, Tag 0E7D]), so `H²(X', 𝓘) = 0`.
* *Lifting.* By the exact sequence `Pic(X') → Pic(X) → H²(X, 𝓘)` of [Stacks, Tag 0C6R], read
  through the identification of the restriction map with pullback of invertible modules, every
  invertible module on `X` is the pullback of one on `X'`.
* *Ampleness.* Over an affine open `V` of `T'`, the restriction of `i` to the preimages of `V` is
  again a closed immersion which is a homeomorphism, and an invertible module is ample as soon as
  its restriction along such a morphism is ([Stacks, Tag 09MW]).

## Main results

All in the namespace `AlgebraicGeometry.C1783`.

* `forall_eq_zero_cohomology_two_idealAddSheafOnSub`:
  `H²(X, 𝓘) = 0` for a first-order thickening of a scheme proper over an affine scheme with
  fibres of dimension at most one.
* `exists_isInvertibleModule_pullback_iso`:
  invertible modules lift along a first-order thickening whose ideal has vanishing `H²`.
* `isRelativelyAmple_of_pullback_iso`:
  relative ampleness descends to the thickening.
* `exists_lift_isRelativelyAmple_of_isFirstOrderThickening`:
  the lifting statement.

## Implementation notes

The vanishing of `H²` does not use the relative ampleness of `L`: it is the vanishing of
quasi-coherent cohomology above the fibre dimension, which holds over an arbitrary affine base.
Neither flatness nor finite presentation of `f'` is used.

## References

* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.Cohomology.AffineBase (isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup)

universe u

namespace AlgebraicGeometry.C1783

attribute [local implicit_reducible] TopCat.Sheaf

attribute [local instance] Stacks.Thickenings.hasExtAbelianSheaf

/-- **The obstruction group vanishes.** Let `i : X ⟶ X'` be a first-order thickening and
`f' : X' ⟶ T'` a proper morphism onto an affine scheme with fibres of dimension at most one.
Then the second cohomology of the ideal sheaf of `i`, restricted to `X`, vanishes: the ideal sheaf
is a quasi-coherent `𝒪_{X'}`-module, and quasi-coherent cohomology vanishes above the fibre
dimension ([Stacks, Tag 0E7D]). -/
private theorem forall_eq_zero_cohomology_two_idealAddSheafOnSub {X X' T' : Scheme.{u}} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsFirstOrderThickening i) (f' : X' ⟶ T') [IsAffine T']
    [IsProper f'] (hdim : ∀ t : T', topologicalKrullDim (f'.fiber t) ≤ 1)
    (x : Sheaf.H.{u} (Stacks.Thickenings.idealAddSheafOnSub i) 2) : x = 0 := by
  have : IsClosedImmersion i := hi.1
  have := Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf i
  have hdim' : ∀ t : T', topologicalKrullDim (f'.fiber t) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    simpa using hdim
  have h2 := (isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup X'
      (Stacks.Thickenings.idealModuleSheaf i) 2).mp
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_cohomology_of_affine_base (d := 1) f'
      hdim' _ ((2 : ℕ) : ℤ) (by norm_num))
  exact Stacks.Thickenings.forall_eq_zero_cohomology_idealAddSheafOnSub_of_iso i hi (Iso.refl _)
    (Stacks.Cohomology.ModuleComparison.eq_zero_sheafH_of_isZero_schemeHgroupTop X' 2 _ h2) x

/-- **Invertible modules lift along a first-order thickening with vanishing obstruction group.**
If `i : X ⟶ X'` is a first-order thickening whose ideal sheaf has vanishing second cohomology,
every invertible `𝒪_X`-module is the pullback of an invertible `𝒪_{X'}`-module
([Stacks, Tag 0C6R]). -/
private theorem exists_isInvertibleModule_pullback_iso {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsFirstOrderThickening i)
    (h2 : ∀ x : Sheaf.H.{u} (Stacks.Thickenings.idealAddSheafOnSub i) 2, x = 0)
    (L : X.Modules) [hL : Stacks.Ample.IsInvertibleModule X L] :
    ∃ (L' : X'.Modules) (_ : Stacks.Ample.IsInvertibleModule X' L'),
      Nonempty ((Scheme.Modules.pullback i).obj L' ≅ L) := by
  obtain ⟨c, hc⟩ :=
    Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_of_forall_eq_zero i hi h2
      (Stacks.SheafOfModules.picardClass X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L hL)
  exact ⟨(Stacks.Picard.picardRepresentative X'.toRingedSpace c).obj,
    (Stacks.Picard.picardRepresentative X'.toRingedSpace c).property,
    (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 hc⟩

/-- Pulling back along `g` and then `h`, for `g ≫ h = k`, is pulling back along `k`. -/
private noncomputable def pullbackCompEqIso {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C) (k : A ⟶ C)
    (e : g ≫ h = k) (M : C.Modules) :
    (modulePullback g.toLRSHom.toShHom).obj ((modulePullback h.toLRSHom.toShHom).obj M) ≅
      (modulePullback k.toLRSHom.toShHom).obj M :=
  (Scheme.Modules.pullbackComp g h).app M ≪≫
    eqToIso (congrArg (fun q : A ⟶ C => (Scheme.Modules.pullback q).obj M) e)

/-- **Relative ampleness descends along a thickening.** Let `i : X ⟶ X'` be a closed immersion
which is surjective, let `f' : X' ⟶ S` be quasi-compact, and let `L'` be an invertible
`𝒪_{X'}`-module whose pullback `i^* L'` is isomorphic to an invertible `𝒪_X`-module `L` ample
relative to `i ≫ f'`. Then `L'` is ample relative to `f'`. Over an affine open `V` of `S` the
restriction of `i` to the preimages of `V` is a surjective closed immersion, and ampleness ascends
along it ([Stacks, Tag 09MW]). -/
private theorem isRelativelyAmple_of_pullback_iso {X X' S : Scheme.{u}} (i : X ⟶ X')
    [IsClosedImmersion i] [Surjective i] (f' : X' ⟶ S) [QuasiCompact f'] (L' : X'.Modules)
    [Stacks.Ample.IsInvertibleModule X' L'] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (e : (Scheme.Modules.pullback i).obj L' ≅ L)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple (i ≫ f') L) :
    Stacks.RelativeAmple.IsRelativelyAmple f' L' := by
  refine ⟨inferInstance, fun V hV => ?_⟩
  set W := f' ⁻¹ᵁ V
  have hhomeo : IsHomeomorph (i ∣_ W).base := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    exact ⟨(i ∣_ W).isClosedEmbedding.isEmbedding,
      (IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹Surjective i› W).surj⟩
  refine Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback_of_isHomeomorph (i ∣_ W)
    _ hhomeo ?_
  have h := hL.2 V hV
  change Stacks.Ample.IsAmple (i ⁻¹ᵁ W).toScheme
    ((modulePullback (i ⁻¹ᵁ W).ι.toLRSHom.toShHom).obj L) at h
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mpr h
  exact pullbackCompEqIso (i ∣_ W) W.ι ((i ⁻¹ᵁ W).ι ≫ i) (morphismRestrict_ι i W) L' ≪≫
    (pullbackCompEqIso (i ⁻¹ᵁ W).ι i _ rfl L').symm ≪≫
    (modulePullback (i ⁻¹ᵁ W).ι.toLRSHom.toShHom).mapIso e

/-- **Lifting a relatively ample invertible module on a curve along a first-order thickening**,
the core of [Stacks, Tag 0DPJ]. Let `i : X ⟶ X'` be a first-order thickening and let
`f' : X' ⟶ T'` be a proper morphism onto an affine scheme all of whose fibres have dimension at
most one. Then every invertible `𝒪_X`-module `L` ample relative to `i ≫ f'` is, up to
isomorphism, the pullback `i^* L'` of an invertible `𝒪_{X'}`-module `L'` ample relative to
`f'`. -/
theorem exists_lift_isRelativelyAmple_of_isFirstOrderThickening {X X' T' : Scheme.{u}}
    (i : X ⟶ X') (hi : Stacks.Thickenings.IsFirstOrderThickening i) (f' : X' ⟶ T')
    [IsAffine T'] [IsProper f'] (hdim : ∀ t : T', topologicalKrullDim (f'.fiber t) ≤ 1)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple (i ≫ f') L) :
    ∃ (L' : X'.Modules) (_ : Stacks.Ample.IsInvertibleModule X' L'),
      Nonempty ((Scheme.Modules.pullback i).obj L' ≅ L) ∧
        Stacks.RelativeAmple.IsRelativelyAmple f' L' := by
  have : IsClosedImmersion i := hi.1
  have : Surjective i := ⟨hi.isThickening.2⟩
  obtain ⟨L', hL', ⟨e⟩⟩ := exists_isInvertibleModule_pullback_iso i hi
    (forall_eq_zero_cohomology_two_idealAddSheafOnSub i hi f' hdim) L
  exact ⟨L', hL', ⟨e⟩, isRelativelyAmple_of_pullback_iso i f' L' L e hL⟩

end AlgebraicGeometry.C1783

end
