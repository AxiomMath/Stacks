module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleComposition
public import StacksFrontier.AlgebraicGeometry.Blowup.SuccessiveCentre
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessTransport

/-!
# Two successive flattening blowups make one

The induction of [Stacks, Tag 0815] blows the base up twice: once to make the module finite
locally free near the generic points of the fibres ([Stacks, Tag 0811]), and once more on the
result, by the inductive hypothesis. The conclusion of 0815 asks for a *single* `U`-admissible
blowup, so the two have to be amalgamated. This file does that.

What makes it possible is [Stacks, Tag 080B]: for a centre `I` on `S` and a centre `J` on the
blowup of `S` in `I`, there is a centre `K` on `S` — the product `I · J₀` of `I` with an ideal
sheaf `J₀` whose inverse image on the blowup is `E ^ d · J` — such that the two-step blowup is
the blowup in `K` over `S`, and `Supp K = Supp I ∪ b(Supp J)`. The existence of the pair
`(d, J₀)` is [Stacks, Tag 0803] (Divisors, Lemma 31.32.5); it is carried here as
`Stacks.Blowup.SecondCentreFactorization`, and is discharged by
`AlgebraicGeometry.secondCentreFactorization`. The composition theorem
`Stacks.Blowup.IsAdmissibleBlowup.comp` no longer carries it: it discharges the factorization
itself, through `Stacks.Blowup.exists_factorization_blowUp`.

## Main results

* `AlgebraicGeometry.isFlatOver_strictTransformSheaf_of_iterated`: if the strict transform of the
  strict transform is flat over the two-step blowup, then the strict transform in a composite
  centre with the right support is flat over its blowup. Unconditional.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_successive`:
  two successive flattening centres amalgamate into one `U`-admissible flattening centre,
  granted `Stacks.Blowup.SecondCentreFactorization`.

## Implementation notes

`AlgebraicGeometry.isFlatOver_strictTransformSheaf_transport_comp` is the companion statement
whose hypothesis is flatness of the *first* strict transform; it derives flatness of the second
for free, because a module flat over the base has strict transform equal to its pullback. Here
the hypothesis is on the second strict transform instead, which is the direction the induction
needs, and the two share their last step: [Stacks, Tag 080I] identifies the iterated strict
transform with the strict transform in the composite centre, over the isomorphism of two-step
and one-step blowups.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### The transport along the composite centre -/

/-- **The iterated strict transform is the strict transform in the composite centre.** Let `I` be
a centre on `S`, `J` a centre on the blowup of `S` in `I`, and `K` a centre on `S` whose support
is `Supp I ∪ b(Supp J)` and whose blowup is the two-step blowup over `S`. If the strict transform
along `J` of the strict transform along `I` of `F` is flat over the two-step blowup, then the
strict transform of `F` along `K` is flat over the blowup of `S` in `K`.

This is [Stacks, Tag 080I] part (1) read through
`AlgebraicGeometry.isFlatOver_iff_of_schemeIsos`: the identification of the two modules is an
isomorphism of modules over an isomorphism of schemes over an isomorphism of bases, and flatness
over the base is invariant under all three. -/
theorem isFlatOver_strictTransformSheaf_of_iterated (f : X ⟶ S) (I K : S.IdealSheafData)
    (J : (blowUp I).IdealSheafData)
    (hK : K.supportSet = I.supportSet ∪ (blowUpToBase I).base '' J.supportSet)
    (e : Over.mk (blowUpToBase J ≫ blowUpToBase I) ≅ Over.mk (blowUpToBase K))
    (F : X.Modules) [F.IsQuasicoherent]
    (hflat : IsFlatOver
        (pullback.snd (pullback.snd f (blowUpToBase I)) (blowUpToBase J)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf (pullback.snd f (blowUpToBase I)) (blowUpToBase J)
        (exceptionalIdeal J)
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F))) :
    IsFlatOver (pullback.snd f (blowUpToBase K)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase K) (exceptionalIdeal K) F) := by
  set f₁ : Stacks.StrictTransform.baseChange f (blowUpToBase I) ⟶ blowUp I :=
    pullback.snd f (blowUpToBase I) with hf₁
  set QI := Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F with hQI
  have : QI.IsQuasicoherent := inferInstance
  have : (Stacks.StrictTransform.sheaf f₁ (blowUpToBase J)
      (exceptionalIdeal J) QI).IsQuasicoherent := inferInstance
  have : (Stacks.StrictTransform.sheaf f (blowUpToBase K)
      (exceptionalIdeal K) F).IsQuasicoherent := inferInstance
  obtain ⟨g, hg, hq, eQ, -⟩ :=
    Stacks.StrictTransform.strictTransformSheaf_comp_blowUp f I K J hK e F
  exact (isFlatOver_iff_of_schemeIsos (pullback.snd f₁ (blowUpToBase J))
    (pullback.snd f (blowUpToBase K)) g ((Over.forget S).mapIso e) hq.symm
    (Stacks.StrictTransform.sheaf f₁ (blowUpToBase J) (exceptionalIdeal J) QI)
    (Stacks.StrictTransform.sheaf f (blowUpToBase K) (exceptionalIdeal K) F) eQ.symm).mp hflat

/-! ### Amalgamating two successive flattening centres -/

/-- **Two successive flattening centres amalgamate into one.** Let `I` be a finitely presented
centre on `S` supported away from `U`, let `J` be a finitely presented centre on the blowup of
`S` in `I` supported away from the inverse image of `U`, and suppose the strict transform along
`J` of the strict transform along `I` of `F` is flat over the two-step blowup. Then there is a
single finitely presented centre `K` on `S`, supported away from `U` and so exhibiting a
`U`-admissible blowup, along which the strict transform of `F` is flat.

The centre is the one produced by `Stacks.Blowup.exists_centre_of_successive`: the product
`I · J₀` of [Stacks, Tag 080B], for `(d, J₀)` the pair supplied by
`Stacks.Blowup.SecondCentreFactorization`. -/
theorem exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_successive
    (h0803 : Stacks.Blowup.SecondCentreFactorization.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens) (I : S.IdealSheafData)
    (hI : FinitePresentation I.subschemeι) (hUI : Disjoint (U : Set S) (I.support : Set S))
    (J : (blowUp I).IdealSheafData) (hJ : FinitePresentation J.subschemeι)
    (hUJ : Disjoint ((blowUpToBase I ⁻¹ᵁ U : (blowUp I).Opens) : Set (blowUp I))
      (J.support : Set (blowUp I)))
    (hflat : IsFlatOver
        (pullback.snd (pullback.snd f (blowUpToBase I)) (blowUpToBase J)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf (pullback.snd f (blowUpToBase I)) (blowUpToBase J)
        (exceptionalIdeal J)
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F))) :
    ∃ K : S.IdealSheafData, FinitePresentation K.subschemeι ∧
      Disjoint (U : Set S) (K.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase K) ∧
      IsFlatOver (pullback.snd f (blowUpToBase K)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase K) (exceptionalIdeal K) F) := by
  obtain ⟨K, hfp, hUK, hsupp, ⟨e⟩⟩ :=
    Stacks.Blowup.exists_centre_of_successive h0803 U I hI hUI J hJ hUJ
  exact ⟨K, hfp, hUK,
    (Stacks.Blowup.isAdmissibleBlowup_iff U (blowUpToBase K)).mpr
      ⟨K, hfp, hUK, Iso.refl _, Category.id_comp _⟩,
    isFlatOver_strictTransformSheaf_of_iterated f I K J hsupp e F hflat⟩

end AlgebraicGeometry

end
