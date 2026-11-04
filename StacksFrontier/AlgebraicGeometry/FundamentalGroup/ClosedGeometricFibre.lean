module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.BaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence

/-!
# The closed geometric fibre of a proper scheme over a local ring

Let `A` be a local ring, let `ψ : A → κ` be a local homomorphism to a field — so `Spec κ ⟶ Spec A`
is a point over the closed point, and a *geometric* point when `κ` is algebraically closed — and
let `f : X ⟶ Spec A` be proper. Every point of `X` then specializes into the closed geometric
fibre `X ×_{Spec A} Spec κ`, because it specializes into the fibre over the closed point and the
two fibres have the same image in `X`.

That is the first of the two hypotheses of
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_essSurjOver`, so granted the second —
essential surjectivity of base change over every finite étale cover — base change to the closed
geometric fibre is an equivalence on finite étale covers, and then
`AlgebraicGeometry.etaleFundamentalGroupContinuousMulEquivOfIsEquivalence` (Stacks 0BQA) makes
the closed geometric fibre carry the same étale fundamental group as `X`.

## Main results

* `AlgebraicGeometry.exists_specializes_mem_range_pullback_fst_of_isLocalHom` — every point of a
  proper scheme over a local ring specializes into the closed geometric fibre.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_closedGeometricFibre` — base change to
  the closed geometric fibre is an equivalence on finite étale covers, granted essential
  surjectivity.
* `AlgebraicGeometry.etaleFundamentalGroupContinuousMulEquivClosedGeometricFibre` — the
  identification of fundamental groups that results.

## Implementation notes

**No `@[stacks]` attribute appears in this file, deliberately.** The results below are Stacks
0A48 (base change to the closed fibre of a proper scheme over a henselian local ring is an
equivalence on finite étale covers) *granted* the essential-surjectivity input that
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence` leaves open — that
file reduces Stacks 0GS2 to exactly this input and likewise carries no attribute. Taking the
fibre over a *geometric* point rather than over the residue field means the hypothesis also
absorbs the content of Stacks 0A49 and 0BTW, the two lemmas by which the Stacks construction of a
specialization map passes from the closed fibre over `κ(A)` to the closed fibre over an
algebraically closed extension of it. Attaching 0A48, 0A49 or 0BTW here would therefore record
as formalized three statements of which this file proves none outright.

Henselianity of `A` is not a hypothesis: it is not needed for the specialization statement, which
only uses that the maximal ideal is contained in the Jacobson radical of the zero ideal. It is
needed for the essential-surjectivity hypothesis to be *true*, which is why the statements take
that hypothesis rather than deriving it.

## References

* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsLocalRing A] {κ : Type u} [Field κ] (ψ : A →+* κ)
  [IsLocalHom ψ] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- Every point of a proper scheme over a local ring `A` specializes into the fibre over a point
`Spec κ ⟶ Spec A` of the closed point: the fibre over the residue field receives every point as
a specialization, and both fibres have the same image, namely the preimage of the closed point.
-/
theorem exists_specializes_mem_range_pullback_fst_of_isLocalHom [IsProper f] (z : X) :
    ∃ z' ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom ψ))).base, z ⤳ z' := by
  obtain ⟨z', hz'mem, hz'⟩ := exists_specializes_mem_range_pullback_fst_of_isProper A
    (I := maximalIdeal A) (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge f z
  refine ⟨z', ?_, hz'⟩
  have hr : Set.range (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal A)))).base
      = PrimeSpectrum.zeroLocus (maximalIdeal A : Set A) := by
    show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal A))) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  rw [Scheme.Pullback.range_fst, Set.mem_preimage, hr] at hz'mem
  -- the image of `z'` contains the maximal ideal, hence is the closed point
  have hle : maximalIdeal A ≤ (f.base z').asIdeal := fun a ha ↦
    (PrimeSpectrum.mem_zeroLocus _ _).mp hz'mem ha
  have hfz : f.base z' = closedPoint A :=
    PrimeSpectrum.ext (le_antisymm (le_maximalIdeal (f.base z').2.ne_top) hle)
  rw [Scheme.Pullback.range_fst, Set.mem_preimage, hfz]
  exact ⟨closedPoint κ, comap_closedPoint ψ⟩

/-- Granted essential surjectivity of base change over every finite étale cover, base change to
the closed geometric fibre of a proper scheme over a local ring is an equivalence on finite étale
covers. -/
theorem isEquivalence_finiteEtaleBaseChange_closedGeometricFibre [IsProper f]
    (hes : ∀ P : FiniteEtaleOver X,
      finiteEtaleBaseChangeEssSurjOver
        (pullback.fst f (Spec.map (CommRingCat.ofHom ψ))) P) :
    (finiteEtaleBaseChange (pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_essSurjOver _
    (fun z ↦ exists_specializes_mem_range_pullback_fst_of_isLocalHom ψ f z) hes

/-- Granted the same hypothesis, the closed geometric fibre of a proper scheme over a local ring
has the same étale fundamental group as the whole scheme, as a topological group. This is the
identification that the construction of a specialization map inverts. -/
def etaleFundamentalGroupContinuousMulEquivClosedGeometricFibre [IsProper f]
    [ConnectedSpace ↥X] [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom ψ)))]
    (y : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom ψ))))
    (hes : ∀ P : FiniteEtaleOver X,
      finiteEtaleBaseChangeEssSurjOver
        (pullback.fst f (Spec.map (CommRingCat.ofHom ψ))) P) :
    EtaleFundamentalGroup (pullback f (Spec.map (CommRingCat.ofHom ψ))) y ≃ₜ*
      EtaleFundamentalGroup X
        (y.map (pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))) :=
  have := isEquivalence_finiteEtaleBaseChange_closedGeometricFibre ψ f hes
  etaleFundamentalGroupContinuousMulEquivOfIsEquivalence _ y

end AlgebraicGeometry

end
