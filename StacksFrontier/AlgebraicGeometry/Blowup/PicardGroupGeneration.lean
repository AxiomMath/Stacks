module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.PicardGroup
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality

/-!
# `Pic(X) = ℤ` for the blowup of a regular local surface, with nothing assumed

Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let `X ⟶ Spec A` be the blowing up of
`Spec A` in `𝔪` and let `E` be the exceptional divisor. This file proves the generation half of
[Stacks, Tag 0C5G] — every Picard class of `X` is an integral multiple of `[𝒪_X(E)]` — reads the
infinite-order half,
`Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.eq_zero_of_zsmul_picardClass_eq_zero`, which
is stated for an exceptional curve of the first kind, on `E` itself, and combines the two to get
`ℤ ≃+ Pic(X)` carrying `1` to `[𝒪_X(E)]`, with no hypothesis beyond regularity and dimension two.

## The argument

`AlgebraicGeometry.surjective_zsmul_picardClass_of_subsingleton_picardGroup_compl` reduces
generation to four facts about the blowup `X = Proj (⨁ₙ 𝔪ⁿ)` and its exceptional divisor `E`:
`X` is integral, locally Noetherian and normal, `E` is an effective Cartier divisor with integral
closed subscheme, and `Pic(X ∖ E)` is trivial. The last three of the first group and the Picard
group of the complement are available for the blowup of the *ideal sheaf* of the closed point of
`Spec A` — [Stacks, Tag 0AGR] for regularity and hence normality, properness over a Noetherian
base for Noetherianness, and
`AlgebraicGeometry.subsingleton_picardGroup_compl_exceptionalIdeal` (from [Stacks, Tag 0F2H])
for the complement — and the two presentations of the blowup are identified over `Spec A` by
`Stacks.Blowup.nonempty_over_iso_blowUpToBase`, under which the two exceptional ideal sheaves
correspond, both being inverse images of the centre. That `E` has integral closed subscheme is
part (1) of [Stacks, Tag 0AGQ]: `E` is the projective line over `κ`.

## Main results

* `AlgebraicGeometry.exists_iso_blowUpSpec_comap_exceptionalIdeal`: the two presentations of the
  blowup of a local ring in its maximal ideal, with their exceptional ideal sheaves.
* `AlgebraicGeometry.surjective_zsmul_picardClass_exceptionalIdealData`: **the generation half of
  Tag 0C5G**, with nothing assumed.
* `AlgebraicGeometry.eq_zero_of_zsmul_picardClass_exceptionalIdealData_eq_zero`: **the
  infinite-order half of Tag 0C5G for the blowup itself**, with nothing assumed.
* `AlgebraicGeometry.picardGroupEquivInt_blowUpSpec_maximalIdeal` and
  `AlgebraicGeometry.picardGroupEquivInt_blowUpSpec_maximalIdeal_one`: **Tag 0C5G**, `Pic(X)` is
  infinite cyclic on the class of `𝒪_X(E)`, with nothing assumed.

## References

* [Stacks Project, Tag 0C5G](https://stacks.math.columbia.edu/tag/0C5G)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0F2H](https://stacks.math.columbia.edu/tag/0F2H)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The two presentations of the blowup of a local ring in its maximal ideal -/

/-- The image of an ideal along a ring isomorphism is its inverse image along the inverse, stated
for the coercions of the isomorphism to ring homomorphisms. -/
private theorem ideal_map_eq_comap_symm {R S : Type*} [CommRing R] [CommRing S]
    (g : R ≃+* S) (I : Ideal R) :
    Ideal.map (g : R →+* S) I = Ideal.comap (g.symm : S →+* R) I :=
  le_antisymm (Ideal.map_le_iff_le_comap.mpr fun _ ha => by simpa using ha)
    fun x hx => by
      simpa using Ideal.mem_map_of_mem (g : R →+* S) (show g.symm x ∈ I from by simpa using hx)

/-- The image of an ideal of `A` along the inverse of `AlgebraicGeometry.Scheme.ΓSpecIso` is its
inverse image along `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem ideal_map_ΓSpecIso_inv_eq_comap_hom (A : Type u) [CommRing A] (I : Ideal A) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I =
      Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom I := by
  set g : A ≃+* ↥Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv with hg
  have h1 : (g : A →+* ↥Γ(Spec (CommRingCat.of A), ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by ext a; rfl
  have h2 : (g.symm : ↥Γ(Spec (CommRingCat.of A), ⊤) →+* A) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom := by ext a; rfl
  rw [← h1, ← h2]
  exact ideal_map_eq_comap_symm g I

/-- The complement of the support of an inverse-image ideal sheaf is the inverse image of the
complement of the support. -/
theorem compl_support_comap {X Y : Scheme.{u}} (J : Y.IdealSheafData) (f : X ⟶ Y) :
    Closeds.compl (J.comap f).support = f ⁻¹ᵁ Closeds.compl J.support := by
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- **The two presentations of the blowup of a local ring in its maximal ideal are identified,
and their exceptional ideal sheaves correspond.** The identification over `Spec A` is
`Stacks.Blowup.nonempty_over_iso_blowUpToBase`, and the exceptional ideal sheaves correspond
because both are inverse images of the centre along the structure morphism to `Spec A`. -/
theorem exists_iso_blowUpSpec_comap_exceptionalIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    ∃ ψ : Stacks.Blowup.blowUpSpec (maximalIdeal A) ≅
        blowUp (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A))),
      (exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop
            (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
              (maximalIdeal A)))).comap ψ.hom =
        Stacks.Blowup.exceptionalIdealData (maximalIdeal A) := by
  obtain ⟨φ⟩ := Stacks.Blowup.nonempty_over_iso_blowUpToBase A (maximalIdeal A)
  have hw : φ.hom.left ≫ blowUpToBase (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A))) =
      Stacks.Blowup.toSpec (maximalIdeal A) := Over.w φ.hom
  refine ⟨(Over.forget _).mapIso φ, ?_⟩
  show (exceptionalIdeal _).comap φ.hom.left = _
  rw [show exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop (Ideal.map
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A))) =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.map
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A))).comap
          (blowUpToBase _) from rfl,
    ← Scheme.IdealSheafData.comap_comp, hw]
  show (Scheme.IdealSheafData.ofIdealTop (Ideal.map
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A))).comap
        (Stacks.Blowup.toSpec (maximalIdeal A)) =
    (Scheme.IdealSheafData.ofIdealTop (Ideal.comap
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (maximalIdeal A))).comap
        (Stacks.Blowup.toSpec (maximalIdeal A))
  rw [ideal_map_ΓSpecIso_inv_eq_comap_hom]

/-! ### Generation of the Picard group of the blowup -/

/-- **Stacks Project, Tag 0C5G, the generation half, with nothing assumed.** Let `(A, 𝔪, κ)` be a
regular local ring of dimension two, let `X ⟶ Spec A` be the blowing up of `Spec A` in `𝔪` and
let `E` be its exceptional divisor. Then every Picard class of `X` is an integral multiple of the
class of `𝒪_X(E)`.

`AlgebraicGeometry.surjective_zsmul_picardClass_of_subsingleton_picardGroup_compl` is applied to
`E`. Its hypotheses are: `X` integral, locally Noetherian and normal, which transport along the
identification of the affine blowup with the blowup of the ideal sheaf of the closed point, where
they are [Stacks, Tag 0AGR] and properness over a Noetherian base; the closed subscheme of `E` is
integral, being the projective line over `κ` by part (1) of [Stacks, Tag 0AGQ]; and `Pic(X ∖ E)`
is trivial, which is
`AlgebraicGeometry.subsingleton_picardGroup_compl_exceptionalIdeal` transported along the same
identification, under which the two exceptional ideal sheaves correspond. -/
@[stacks 0C5G "the generation half, with nothing assumed: every Picard class of the blowup of a \
regular local ring of dimension two in its maximal ideal is an integral multiple of the class of \
O_X(E)"]
theorem surjective_zsmul_picardClass_exceptionalIdealData (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    Function.Surjective fun n : ℤ => n • Stacks.Divisors.picardClass
      (Stacks.Blowup.exceptionalIdealData (maximalIdeal A)) := by
  let B := Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A))
  obtain ⟨ψ, hψ⟩ := exists_iso_blowUpSpec_comap_exceptionalIdeal A
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsNoetherian (blowUp B) := Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  have : IsNormal (blowUp B) := isNormal_blowUp_maximalIdeal_of_isRegularLocalRing A hdim
  have : IsReduced (blowUp B) := isReduced_of_isNormal _
  have : IrreducibleSpace (blowUp B) := irreducibleSpace_blowUp_maximalIdeal A hdim
  have : IsIntegral (blowUp B) :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).2 ⟨inferInstance, inferInstance⟩
  have : IsIntegral (Stacks.Blowup.blowUpSpec (maximalIdeal A)) := IsIntegral.of_isIso ψ.inv
  have : IsLocallyNoetherian (Stacks.Blowup.blowUpSpec (maximalIdeal A)) :=
    isLocallyNoetherian_of_isOpenImmersion ψ.hom
  have : IsNormal (Stacks.Blowup.blowUpSpec (maximalIdeal A)) :=
    isNormal_of_isOpenImmersion ψ.hom
  obtain ⟨e, -⟩ := Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdealData A hdim
  have : IsIntegral (Stacks.Blowup.exceptionalIdealData (maximalIdeal A)).subscheme :=
    isIntegral_subscheme_of_iso_projectiveLineProj _ (ResidueField A) e
  refine surjective_zsmul_picardClass_of_subsingleton_picardGroup_compl _ ?_
  rw [show Closeds.compl (Stacks.Blowup.exceptionalIdealData (maximalIdeal A)).support =
      ψ.hom ⁻¹ᵁ Closeds.compl (exceptionalIdeal B).support from by
    rw [← hψ]; exact compl_support_comap _ _]
  exact Stacks.PicardGroup.subsingleton_of_iso
    (asIso (ψ.hom ∣_ Closeds.compl (exceptionalIdeal B).support)).symm
    (subsingleton_picardGroup_compl_exceptionalIdeal A)

/-! ### The infinite order of the class of `𝒪_X(E)` -/

/-- **Stacks Project, Tag 0C5G, the infinite-order half for the blowup itself.** Let `(A, 𝔪, κ)`
be a regular local ring of dimension two, let `X ⟶ Spec A` be the blowing up of `Spec A` in `𝔪`
and let `E` be its exceptional divisor. Then no nonzero multiple of the class of `𝒪_X(E)`
vanishes in `Pic(X)`.

`Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.eq_zero_of_zsmul_picardClass_eq_zero` proves
this for an exceptional curve of the first kind, and `E` is one: parts (1) and (3) of
[Stacks, Tag 0AGQ], read as the predicate by
`Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdealData`. -/
@[stacks 0C5G "the infinite-order half for the blowup of a regular local ring of dimension two \
in its maximal ideal, with nothing assumed: no nonzero multiple of the class of O_X(E) vanishes \
in Pic(X)"]
theorem eq_zero_of_zsmul_picardClass_exceptionalIdealData_eq_zero (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) (n : ℤ)
    (hn : n • Stacks.Divisors.picardClass
      (Stacks.Blowup.exceptionalIdealData (maximalIdeal A)) = 0) :
    n = 0 :=
  (Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdealData A
      hdim).choose_spec.eq_zero_of_zsmul_picardClass_eq_zero _ _ _ n hn

/-! ### `Pic(X) = ℤ` -/

/-- **Stacks Project, Tag 0C5G.** Let `(A, 𝔪, κ)` be a regular local ring of dimension two and
let `X ⟶ Spec A` be the blowing up of `Spec A` in `𝔪`, with exceptional divisor `E`. Then
`n ↦ n • [𝒪_X(E)]` is an isomorphism `ℤ ≃+ Pic(X)`: so `Pic(X)` is infinite cyclic, generated by
`𝒪_X(E)`.

The map is injective because `[𝒪_X(E)]` has infinite order, which is
`Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.eq_zero_of_zsmul_picardClass_eq_zero` applied
to `E` through parts (1) and (3) of [Stacks, Tag 0AGQ], and surjective by
`AlgebraicGeometry.surjective_zsmul_picardClass_exceptionalIdealData`. Nothing is assumed beyond
regularity and dimension two. -/
@[stacks 0C5G "the identification Z ≃+ Pic(X) for the blowup of a regular local ring of \
dimension two in its maximal ideal, with nothing assumed: both halves, generation and infinite \
order, are proved for the exceptional divisor of this blowup"]
def picardGroupEquivInt_blowUpSpec_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) :
    ℤ ≃+ Stacks.Picard.ofScheme (Stacks.Blowup.blowUpSpec (maximalIdeal A)) :=
  (Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdealData A
      hdim).choose_spec.picardGroupEquivInt _ _
    (surjective_zsmul_picardClass_exceptionalIdealData A hdim)

/-- The isomorphism `ℤ ≃+ Pic(X)` of the blowup carries `1` to the class of `𝒪_X(E)`, so
`Pic(X)` is infinite cyclic on that class. -/
@[stacks 0C5G "the generator clause for the blowup of a regular local ring of dimension two in \
its maximal ideal, with nothing assumed: the isomorphism carries 1 to the class of O_X(E)"]
theorem picardGroupEquivInt_blowUpSpec_maximalIdeal_one (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    picardGroupEquivInt_blowUpSpec_maximalIdeal A hdim 1 =
      Stacks.Divisors.picardClass
        (Stacks.Blowup.exceptionalIdealData (maximalIdeal A)) :=
  (Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdealData A
      hdim).choose_spec.picardGroupEquivInt_one _ _
    (surjective_zsmul_picardClass_exceptionalIdealData A hdim)

end AlgebraicGeometry

end
