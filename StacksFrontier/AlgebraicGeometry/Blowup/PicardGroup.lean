module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurvePicard
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsionExponent
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PuncturedSpectrumRegular
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace

/-!
# The Picard group of the blowup of a regular local surface

Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let `X ⟶ Spec A` be the blowup of
`Spec A` in `𝔪` and let `E` be the exceptional divisor. Then `Pic(X)` is infinite cyclic on the
class of `𝒪_X(E)`. This file proves the two steps of the source's argument that the library
supports and assembles the conclusion from them.

The *infinite order* of `[𝒪_X(E)]` is proved here in general: if `D` is an exceptional curve of
the first kind on a scheme `X` over a field `k` — an effective Cartier divisor together with an
isomorphism `e : 𝐏¹_k ≅ D` carrying the normal sheaf of `D` to `𝒪(-1)` — then `n • [𝒪_X(D)] = 0`
forces `n = 0`. Pulling the class of `𝒪_X(D)` back along `D ⟶ X` gives the class of the normal
sheaf, pulling that back along `e` gives the class of `𝒪(-1)` on `𝐏¹_k`, and `m ↦ [𝒪(m)]` is
injective on `𝐏¹_k` ([Stacks, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)).

The *triviality of `Pic(X ∖ E)`* is proved here for the blowup of any regular local ring in its
maximal ideal: a blowup is an isomorphism away from its centre
([Stacks, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)), the centre is the closed point,
and the Picard group of the punctured spectrum of a regular local ring vanishes
([Stacks, Tag 0F2H](https://stacks.math.columbia.edu/tag/0F2H)).

## Main results

* `Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.eq_zero_of_zsmul_picardClass_eq_zero`:
  **the class of `𝒪_X(D)` has infinite order** for `D` an exceptional curve of the first kind.
* `AlgebraicGeometry.subsingleton_picardGroup_compl_exceptionalIdeal`: **the Picard group of the
  complement of the exceptional divisor is trivial.**
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.picardGroupEquivInt` and
  `AlgebraicGeometry.picardGroupEquivInt_blowUp_maximalIdeal`: the identification
  `ℤ ≃+ Pic(X)` carrying `1` to `[𝒪_X(E)]`, granted generation.

## No unrestricted `@[stacks 0C5G]`

The identification `Pic(X) = ℤ · [𝒪_X(E)]` is **not** proved outright, and every declaration
carrying the tag names its hypothesis in the attribute. Two inputs of the source's proof are
absent from the library.

* **That `E` is an exceptional curve of the first kind over `κ`.** This is the half of
  [Stacks, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ) that identifies `E` with `𝐏¹_κ`
  and `𝒪_X(E)|_E` with `𝒪(-1)`; of that tag the library has only the closed immersion
  `X ⟶ 𝐏¹_{Spec A}` (`Stacks.Blowup.exists_isClosedImmersion_blowUpSpec_maximalIdeal`), and
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` is a definition with no
  consumer establishing it for a blowup. It is therefore carried as a hypothesis, from which the
  infinite order of `[𝒪_X(E)]` *is* derived here.
* **Generation.** The source produces, for an invertible `ℒ`, a trivialization over `X ∖ E`, reads
  it as a regular meromorphic section with `div_ℒ(s) = nE`, and concludes `ℒ ≅ 𝒪_X(nE)` from
  [Stacks, Tag 0BE8](https://stacks.math.columbia.edu/tag/0BE8). The first and last steps are
  available (`Stacks.PicardUFD.subsingleton_picardGroup_puncturedSpectrum` and
  `AlgebraicGeometry.picardToWeilDivisorClassGroup_injective`); the middle one is not. The
  identification of the Weil divisor class of `𝒪_X(D)` with the class of `D` is available —
  `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_eq_of_forall_ord` of
  `StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/CanonicalSectionOrder.lean` — but
  reading a trivialization of `ℒ` over `X ∖ E` as a regular meromorphic section of `ℒ` on `X` is
  not, and there is no restriction homomorphism `Cl(X) ⟶ Cl(X ∖ E)` in the library either, so the
  divisor-class route is equally blocked. Generation is therefore carried as a hypothesis.

## Implementation notes

**Which Picard group.** `Stacks.Picard.ofScheme`, which is `Stacks.SheafOfModules.PicardGroup`
of the structure sheaf and so the group Tag 0BXJ is stated over, equipped here with a pullback
homomorphism (`Stacks.Picard.schemePullbackClassHom`) and with the Picard class of an effective
Cartier divisor (`Stacks.Divisors.picardClass`). No bridge between two Picard groups is needed:
there is one group, and the vanishing of `n • [L]` in it is triviality of `L^{⊗ n}`.

**The centre.** The blowup centre is written out as
`Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (𝔪))`, the
spelling the library already uses for this blowup, rather than abbreviated.

## References

* [Stacks Project, Tag 0C5G](https://stacks.math.columbia.edu/tag/0C5G)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0F2H](https://stacks.math.columbia.edu/tag/0F2H)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.RingedSpace (structureIsSheaf pullbackFunctor modulePullback_isInvertible_of)

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  [Stacks.Divisors.IsEffectiveCartierDivisor D] (e : projectiveLineProj k ≅ D.subscheme)

/-- The Picard class of `𝒪_X(D)`, pulled back to `𝐏¹_k`, is the class of `𝒪(-1)`. -/
private theorem schemePullbackClass_picardClass (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Stacks.Picard.schemePullbackClass e.hom
        (Stacks.Picard.schemePullbackClass D.subschemeι (Stacks.Divisors.picardClass D)) =
      Stacks.SheafOfModules.picardClass (projectiveLineProj k).presheaf
        (structureIsSheaf (projectiveLineProj k).toRingedSpace)
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1))
        (AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_twistingSheaf_projectiveLine k (-1)) :=
  (congrArg (Stacks.Picard.schemePullbackClass e.hom)
      (Stacks.Picard.pullbackClass_classOf D.subschemeι.toLRSHom.toShHom _
        (Stacks.Divisors.isInvertible_invertibleSheaf_picard D))).trans
    ((Stacks.Picard.pullbackClass_classOf e.hom.toLRSHom.toShHom _
        (AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_pullback_invertibleSheaf D)).trans
      ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
        ⟨AlgebraicGeometry.Scheme.IdealSheafData.pullbackInvertibleSheafIsoTwist D k e hE⟩))

/-- **Stacks Project, Tag 0C5G, the infinite-order half.** Let `D` be an exceptional curve of
the first kind on a scheme `X` over a field `k`. Then the class of `𝒪_X(D)` has infinite order
in `Pic(X)`: no nonzero multiple of it vanishes.

Pulling the class back along the closed immersion `D ⟶ X` gives the class of the normal sheaf of
`D`, and pulling that back along `e` gives the class of `𝒪(-1)` on `𝐏¹_k`, which has infinite
order because `m ↦ [𝒪(m)]` is injective there (Tag 0BXJ). -/
@[stacks 0C5G "the infinite-order half, for an exceptional curve of the first kind: that the \
exceptional divisor of the blowup is one is the unproved half of Tag 0AGQ"]
theorem IsExceptionalCurveOfFirstKind.eq_zero_of_zsmul_picardClass_eq_zero
    (hE : D.IsExceptionalCurveOfFirstKind k e) (n : ℤ)
    (hn : n • Stacks.Divisors.picardClass D = 0) : n = 0 := by
  have pull : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (x : Stacks.Picard.ofScheme Z),
      n • x = 0 → n • Stacks.Picard.schemePullbackClass f x = 0 := fun f x h => by
    have := congrArg (Stacks.Picard.schemePullbackClassHom f) h
    rwa [map_zsmul, map_zero] at this
  have h2 := pull e.hom _ (pull D.subschemeι _ hn)
  rw [schemePullbackClass_picardClass D k e hE] at h2
  have h3 : n • Stacks.PicardUFD.twistPicardHom k 1 (-1) = 0 := h2
  simpa using (injective_iff_map_eq_zero _).1
    (Stacks.PicardUFD.twistPicardHom_injective k 1 Nat.one_pos) (n • -1)
    (by rw [map_zsmul]; exact h3)

/-- **Stacks Project, Tag 0C5G, granted generation.** Let `D` be an exceptional curve of the
first kind on a scheme `X` over a field `k`, and suppose every Picard class of `X` is an
integral multiple of the class of `𝒪_X(D)`. Then `n ↦ n • [𝒪_X(D)]` is an isomorphism
`ℤ ≃+ Pic(X)`: it is surjective by hypothesis and injective because `[𝒪_X(D)]` has infinite
order. -/
@[stacks 0C5G "granted generation, which is hypothesized: the source's generation step needs \
the Weil divisor of the canonical section of O_X(D) to be identified with D, which the library \
lacks; and that the exceptional divisor of the blowup is an exceptional curve of the first kind \
is the unproved half of Tag 0AGQ"]
def IsExceptionalCurveOfFirstKind.picardGroupEquivInt
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hgen : Function.Surjective fun n : ℤ => n • Stacks.Divisors.picardClass D) :
    ℤ ≃+ Stacks.Picard.ofScheme X :=
  AddEquiv.ofBijective (zmultiplesHom _ (Stacks.Divisors.picardClass D))
    ⟨(injective_iff_map_eq_zero _).2 fun n hn =>
      hE.eq_zero_of_zsmul_picardClass_eq_zero D k e n hn, hgen⟩

/-- The isomorphism `ℤ ≃+ Pic(X)` carries `1` to the class of `𝒪_X(D)`, so `Pic(X)` is
infinite cyclic *on that class*. -/
@[stacks 0C5G "granted generation, which is hypothesized: the generator clause"]
theorem IsExceptionalCurveOfFirstKind.picardGroupEquivInt_one
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hgen : Function.Surjective fun n : ℤ => n • Stacks.Divisors.picardClass D) :
    hE.picardGroupEquivInt D k hgen 1 = Stacks.Divisors.picardClass D := by
  change (zmultiplesHom (Stacks.Picard.ofScheme X) (Stacks.Divisors.picardClass D)) 1 = _
  rw [zmultiplesHom_apply, one_zsmul]

end Scheme.IdealSheafData

/-! ### The blowup of a regular local ring in its maximal ideal -/

/-- The support of the blowup centre is the closed point: a prime of `A` contains the maximal
ideal exactly when it is the maximal ideal. -/
theorem support_ofIdealTop_map_maximalIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))).support =
      ⟨{IsLocalRing.closedPoint A}, IsLocalRing.isClosed_singleton_closedPoint A⟩ := by
  ext x
  simp only [Scheme.IdealSheafData.coe_support_ofIdealTop]
  rw [Spec_zeroLocus]
  let f : A ≃+* ↥Γ(Spec (.of A), ⊤) :=
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  have hpre : f ⁻¹' (Ideal.map f (IsLocalRing.maximalIdeal A) : Set ↥Γ(Spec (.of A), ⊤)) =
      (IsLocalRing.maximalIdeal A : Set A) := by
    ext a
    change f a ∈ Ideal.map f (IsLocalRing.maximalIdeal A) ↔ a ∈ IsLocalRing.maximalIdeal A
    rw [Ideal.mem_map_iff_of_surjective f f.surjective]
    constructor
    · rintro ⟨b, hb, hba⟩
      exact f.injective hba ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  change (x : PrimeSpectrum A) ∈ PrimeSpectrum.zeroLocus
      (f ⁻¹' (Ideal.map f (IsLocalRing.maximalIdeal A) : Set ↥Γ(Spec (.of A), ⊤))) ↔
    (x : PrimeSpectrum A) ∈ ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))
  rw [hpre]
  change IsLocalRing.maximalIdeal A ≤ x.asIdeal ↔ x = IsLocalRing.closedPoint A
  constructor
  · intro hx
    apply PrimeSpectrum.ext_iff.mpr
    simpa [IsLocalRing.closedPoint] using
      ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le x.2.ne_top hx).symm
  · rintro rfl
    exact le_rfl

/-- The complement of the blowup centre is the punctured spectrum. -/
theorem support_compl_ofIdealTop_map_maximalIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
            (IsLocalRing.maximalIdeal A))).support.compl =
      Stacks.Divisors.puncturedSpectrum A := by
  rw [support_ofIdealTop_map_maximalIdeal]
  rfl

/-- The complement of the exceptional divisor is the preimage of the complement of the centre:
the exceptional ideal is the inverse image of the centre. -/
theorem support_compl_exceptionalIdeal {X : Scheme.{u}} (I : X.IdealSheafData) :
    (exceptionalIdeal I).support.compl = blowUpToBase I ⁻¹ᵁ I.support.compl := by
  rw [exceptionalIdeal, Scheme.IdealSheafData.support_comap]
  rfl

/-- **Stacks Project, Tag 0C5G, the third step of the source's proof.** Let `A` be a regular
local ring and let `X ⟶ Spec A` be the blowup of `Spec A` in its maximal ideal, with exceptional
divisor `E`. Then `Pic(X ∖ E)` is trivial.

The blowup is an isomorphism over the complement of its centre (Tag 02OS), that complement is
the punctured spectrum of `A`, and a regular local ring is a unique factorization domain, so the
Picard group of its punctured spectrum vanishes (Tag 0F2H). No hypothesis on the dimension of
`A` is used. -/
@[stacks 0C5G "the third step of the source's proof: triviality of the Picard group of the \
complement of the exceptional divisor"]
theorem subsingleton_picardGroup_compl_exceptionalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] :
    Subsingleton (Scheme.Opens.toScheme (exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
        (IsLocalRing.maximalIdeal A)))).support.compl).picardGroup := by
  rw [support_compl_exceptionalIdeal]
  refine Stacks.PicardGroup.subsingleton_of_iso (asIso (blowUpToBase
    (Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
      (IsLocalRing.maximalIdeal A))) ∣_ _)).symm ?_
  rw [support_compl_ofIdealTop_map_maximalIdeal]
  exact Stacks.PicardUFD.subsingleton_picardGroup_puncturedSpectrum A

/-- **Stacks Project, Tag 0C5G, granted the two missing inputs.** Let `(A, 𝔪, κ)` be a regular
local ring of dimension two and let `X ⟶ Spec A` be the blowup of `Spec A` in `𝔪`, with
exceptional divisor `E`. Granted that `E` is an exceptional curve of the first kind over `κ` and
that every Picard class of `X` is an integral multiple of `[𝒪_X(E)]`, the map `n ↦ n • [𝒪_X(E)]`
is an isomorphism `ℤ ≃+ Pic(X)`; so `Pic(X) = ℤ`, generated by `𝒪_X(E)`. -/
@[stacks 0C5G "granted the two inputs the library lacks, both hypothesized: that the \
exceptional divisor is an exceptional curve of the first kind over the residue field (the \
unproved half of Tag 0AGQ), and generation of the Picard group by its class"]
def picardGroupEquivInt_blowUp_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (_hdim : ringKrullDim A = 2)
    {e : projectiveLineProj (IsLocalRing.ResidueField A) ≅
      (exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
          (IsLocalRing.maximalIdeal A)))).subscheme}
    (hE : (exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
          (IsLocalRing.maximalIdeal A)))).IsExceptionalCurveOfFirstKind
      (IsLocalRing.ResidueField A) e)
    (hgen : Function.Surjective fun n : ℤ => n • Stacks.Divisors.picardClass
      (exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))) :
    ℤ ≃+ Stacks.Picard.ofScheme (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))) :=
  hE.picardGroupEquivInt _ _ hgen

end AlgebraicGeometry

end
