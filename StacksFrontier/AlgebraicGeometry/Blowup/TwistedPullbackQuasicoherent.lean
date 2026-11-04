module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackTerms
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QuasiCoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.DirectSums
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound

/-!
# The twisted derived pullback on a blowup has quasi-coherent cohomology

Let `A` be a commutative ring, `I ⊆ A` an ideal and `p : X = Proj(⨁_{n ≥ 0} Iⁿ) ⟶ Spec A` the
blowup of `Spec A` in `I`, with its twists `𝒪_X(q)`. For an `A`-module `M` the object

`Lp^*(M̃) ⊗^𝐋_{𝒪_X} 𝒪_X(q)`

of the derived category of `𝒪_X`-modules has quasi-coherent cohomology sheaves, so it is an
object of `AlgebraicGeometry.QuasicoherentDerivedCategory (blowUpSpec I)`. That is the form in
which the hypercohomology spectral sequence of [Stacks, Tag 0G9Q] asks for its input, while
[Stacks, Tag 0G9Z] produces the object as a bare object of the derived category.

No new mathematics is involved. `Lp^*(M̃)` has quasi-coherent cohomology by [Stacks, Tag 08DW]
part (1), the twist is quasi-coherent, and a derived tensor product of two such objects again has
quasi-coherent cohomology by [Stacks, Tag 08DX] part (1); both are already proved in this
development, for an arbitrary model of the derived categories in the first case and at the
standard model in the second, which is the model the blowup object lives at.

## Main results

* `Stacks.Blowup.isQuasicoherent_homology_twistedDerivedPullback`: the cohomology sheaves of
  `Lp^*(M̃) ⊗^𝐋 𝒪_X(q)` are quasi-coherent.
* `Stacks.Blowup.twistedDerivedPullbackQcoh`: **the same object as an object of
  `D_QCoh(𝒪_X)`**, with the same underlying object of the derived category.

## Implementation notes

Four spellings of the sheaf of rings of the blowup are in play, as
`StacksFrontier/AlgebraicGeometry/Blowup/TwistedPullbackTerms.lean` already records: they agree by
`rfl` but instance search crosses none of them. Every crossing below is therefore made by a term
— `Stacks.Blowup.isQuasicoherent_blowUpTwist` and the two closure instances at the top of this
file are passed explicitly rather than found.

`Stacks.Blowup.isQuasicoherent_homology_Q_single` is stated for an arbitrary scheme, because
nothing in it is about the blowup: it is the statement that a quasi-coherent module placed in
degree zero has quasi-coherent cohomology.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 0G9Q](https://stacks.math.columbia.edu/tag/0G9Q)
* [Stacks Project, Tag 0G9Z](https://stacks.math.columbia.edu/tag/0G9Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedPullbackOfATilde
open AlgebraicGeometry

universe u

-- The blowup object of [Stacks, Tag 0G9Z] and the quasi-coherent derived category of
-- `StacksFrontier/AlgebraicGeometry/Perfect/QuasiCoherentDerived/DirectSums.lean` are both built
-- with the standard model of the derived category, so that model is given priority here.
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- Quasi-coherent modules on an affine scheme are closed under kernels, read at the
ringed-space spelling of the sheaf of rings. The two spellings are equal by `rfl`
(`AlgebraicGeometry.schemeRingCatSheaf_eq_ringSheaf`), but instance search does not cross
between them, so the crossing is made here once by a term. -/
instance isClosedUnderKernels_isQuasicoherent_specRingedSpace : (SheafOfModules.isQuasicoherent
    (structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace)).IsClosedUnderKernels :=
  inferInstanceAs ((SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of A)).ringCatSheaf).IsClosedUnderKernels)

/-- Quasi-coherent modules on an affine scheme are closed under cokernels, read at the
ringed-space spelling of the sheaf of rings; the companion of
`Stacks.Blowup.isClosedUnderKernels_isQuasicoherent_specRingedSpace`. -/
instance isClosedUnderCokernels_isQuasicoherent_specRingedSpace : (SheafOfModules.isQuasicoherent
    (structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace)).IsClosedUnderCokernels :=
  inferInstanceAs ((SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of A)).ringCatSheaf).IsClosedUnderCokernels)

/-- **`M̃[0]` has quasi-coherent cohomology.** The degreewise sheafification of a complex of
`R`-modules has quasi-coherent terms, and quasi-coherent modules on an affine scheme are closed
under kernels and cokernels, so every cohomology sheaf of its class in the derived category is
quasi-coherent. -/
theorem isQuasicoherent_homology_Q_tildeComplex_single
    (M : ModuleCat.{u} (CommRingCat.of A)) (j : ℤ) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace)) j).obj
      (DerivedCategory.Q.obj (tildeComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M)))
      ).IsQuasicoherent :=
  Stacks.DerivedQCoh.isDQCoh_Q_obj
    (R := structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace)
    (tildeComplex ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M))
    (fun k => inferInstanceAs
      (((tilde.functor (CommRingCat.of A)).obj
        (((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M).X k)
          ).IsQuasicoherent)) j

/-- **A quasi-coherent module placed in degree zero has quasi-coherent cohomology.** The
cohomology sheaves are the module itself in degree zero and zero elsewhere, the latter by the
two bounds the single-object complex carries. -/
theorem isQuasicoherent_homology_Q_single (X : Scheme.{u})
    (N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hN : N.IsQuasicoherent) (j : ℤ) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj N))
      ).IsQuasicoherent := by
  have hGE : ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj N).IsGE 0 := inferInstance
  have hLE : ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj N).IsLE 0 := inferInstance
  refine (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).app N)) ?_
  by_cases hj : j = 0
  · subst hj
    exact (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).app N).symm hN
  · refine (SheafOfModules.isQuasicoherent
      (structureSheafRing X.toRingedSpace)).prop_of_iso (IsZero.isoZero ?_).symm
      (AlgebraicGeometry.isQuasicoherent_zero X)
    rcases lt_or_gt_of_ne hj with hj' | hj'
    · exact ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj N).isZero_of_isGE 0 j hj'
    · exact ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj N).isZero_of_isLE 0 j hj'

/-- **`Lp^*M̃` has quasi-coherent cohomology.** This is [Stacks, Tag 08DW] part (1) — the
derived pullback of an object with quasi-coherent cohomology again has quasi-coherent cohomology
— applied to the structure morphism `p : X ⟶ Spec A` of the blowup and to `M̃[0]`. -/
theorem isQuasicoherent_homology_derivedPullbackTildeSingle
    (M : ModuleCat.{u} (CommRingCat.of A)) (j : ℤ) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (blowUpSpec I).toRingedSpace)) j).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M))))
      ).IsQuasicoherent :=
  Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel (toSpec I) _
    (isQuasicoherent_homology_Q_tildeComplex_single M) j

/-- **`Lp^*M̃ ⊗^𝐋 𝒪_X(q)` has quasi-coherent cohomology.** [Stacks, Tag 08DX] part (1) — a
derived tensor product of two objects with quasi-coherent cohomology has quasi-coherent
cohomology — applied to `Lp^*M̃`, whose cohomology is quasi-coherent by [Stacks, Tag 08DW] part
(1), and to the twist `𝒪_X(q)` placed in degree zero, which is quasi-coherent because every
twisting sheaf of the blowup is. -/
theorem isQuasicoherent_homology_twistedDerivedPullback
    (M : ModuleCat.{u} (CommRingCat.of A)) (q j : ℤ) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (blowUpSpec I).toRingedSpace)) j).obj
      (((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
              ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M))))).obj
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q))))
      ).IsQuasicoherent :=
  AlgebraicGeometry.TorFormula.isQuasicoherent_homology_derivedTensor (blowUpSpec I) _ _
    (isQuasicoherent_homology_derivedPullbackTildeSingle I M)
    (isQuasicoherent_homology_Q_single (blowUpSpec I) (blowUpTwist I q)
      (isQuasicoherent_blowUpTwist I q)) j

/-- **`Lp^*M̃ ⊗^𝐋 𝒪_X(q)` as an object of `D_QCoh(𝒪_X)` on the blowup.** This is the form in
which [Stacks, Tag 0G9Q] — `AlgebraicGeometry.hypercohomologySpectralSequence_abutsTo` and
`AlgebraicGeometry.hypercohomologySpectralSequence_isBounded` — asks for its input, and the
underlying object of the derived category is the one [Stacks, Tag 0G9Z]
(`Stacks.Blowup.nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow`) is
stated for, on the nose rather than up to an isomorphism.

Nothing is constructed here: the object already exists, and what the subcategory asks for in
addition is the quasi-coherence of its cohomology sheaves, which is
`Stacks.Blowup.isQuasicoherent_homology_twistedDerivedPullback`. -/
def twistedDerivedPullbackQcoh (M : ModuleCat.{u} (CommRingCat.of A)) (q : ℤ) :
    AlgebraicGeometry.QuasicoherentDerivedCategory (blowUpSpec I) :=
  ⟨((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
            ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M))))).obj
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q))),
    fun j => isQuasicoherent_homology_twistedDerivedPullback I M q j⟩

end Stacks.Blowup

end
