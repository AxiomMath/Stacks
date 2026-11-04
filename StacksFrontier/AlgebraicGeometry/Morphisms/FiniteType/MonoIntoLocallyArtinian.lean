module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.Algebra.Category.Ring.Epi.NilpotentMaximalIdeal
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Monomorphism

/-!
# Monomorphisms into locally Artinian schemes

A monomorphism of schemes whose target is locally Artinian is locally of finite type. The target
is discrete, so the question is local on it around a single point, where it is affine with a
local Artinian ring of global sections; on an affine open of the source the morphism is a
monomorphism of affine schemes, so it is an epimorphism of rings on global sections, and an
epimorphism out of a local ring with nilpotent maximal ideal is surjective.

This is the scheme-theoretic step of the proof of Stacks 06S1: a monomorphism into a scheme
locally quasi-finite over a field is locally of finite type.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_of_mono_of_subsingleton`: a monomorphism into a scheme
  with at most one point which is locally Artinian is locally of finite type.
* `AlgebraicGeometry.locallyOfFiniteType_of_mono_of_isLocallyArtinian`: a monomorphism into a
  locally Artinian scheme is locally of finite type.

## References

* [Stacks Project, Tag 06S1](https://stacks.math.columbia.edu/tag/06S1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A monomorphism into a one-point locally Artinian scheme is locally of finite type.** The
target is affine with a local Artinian ring of global sections, and on each affine open of the
source the map on global sections is an epimorphism out of that ring, hence surjective. -/
theorem locallyOfFiniteType_of_mono_of_subsingleton {V T : Scheme.{u}} (q : V ⟶ T) [Mono q]
    [Subsingleton T] [IsLocallyArtinian T] : LocallyOfFiniteType q := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType.{u})
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) V.affineCover]
  intro i
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  set φ := (V.affineCover.f i ≫ q).appTop
  refine RingHom.FiniteType.of_surjective _ ?_
  rcases subsingleton_or_nontrivial Γ(T, ⊤) with hR | hR
  · have : Subsingleton Γ(V.affineCover.X i, ⊤) :=
      subsingleton_of_zero_eq_one (by simpa using congrArg φ.hom (Subsingleton.elim 0 1))
    exact fun s ↦ ⟨0, Subsingleton.elim _ _⟩
  -- `Γ(T, ⊤)` has a unique prime ideal, so it is a local Artinian ring
  have : Subsingleton (PrimeSpectrum Γ(T, ⊤)) :=
    T.isoSpec.hom.homeomorph.symm.injective.subsingleton
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum Γ(T, ⊤)) := inferInstance
  have hp : ∃! I : Ideal Γ(T, ⊤), I.IsPrime := ⟨p.asIdeal, p.2, fun I hI ↦
    congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (⟨I, hI⟩ : PrimeSpectrum Γ(T, ⊤)) p)⟩
  have : IsLocalRing Γ(T, ⊤) :=
    (((Ring.krullDimLE_zero_and_isLocalRing_tfae Γ(T, ⊤)).out 2 1 rfl rfl).1 hp).2
  have hm : IsNilpotent (IsLocalRing.maximalIdeal Γ(T, ⊤)) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  -- the map on global sections is an epimorphism
  have := epi_appTop_of_mono (V.affineCover.f i ≫ q)
  algebraize [φ.hom]
  have : Algebra.IsEpi Γ(T, ⊤) Γ(V.affineCover.X i, ⊤) := CommRingCat.epi_iff_epi.mp this
  exact Algebra.IsEpi.surjective_algebraMap_of_isNilpotent_maximalIdeal hm

/-- **A monomorphism into a locally Artinian scheme is locally of finite type.** The target is
discrete, so it is covered by its one-point open subschemes, and over each of them the
restriction is a monomorphism into a one-point locally Artinian scheme. -/
theorem locallyOfFiniteType_of_mono_of_isLocallyArtinian {V W : Scheme.{u}} (p : V ⟶ W)
    [Mono p] [IsLocallyArtinian W] : LocallyOfFiniteType p := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType.{u})
  let U (w : W) : W.Opens := ⟨{w}, isOpen_discrete _⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U
    (eq_top_iff.2 fun w _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨w, rfl⟩) fun w ↦ ?_
  have : Subsingleton (U w) := Set.subsingleton_singleton.coe_sort
  have : Mono (p ∣_ U w) := by
    have : Mono (p ∣_ U w ≫ (U w).ι) := by rw [morphismRestrict_ι]; infer_instance
    exact mono_of_mono _ (U w).ι
  exact locallyOfFiniteType_of_mono_of_subsingleton _

end AlgebraicGeometry
