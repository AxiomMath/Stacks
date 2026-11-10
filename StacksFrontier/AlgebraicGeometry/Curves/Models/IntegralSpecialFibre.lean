module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal
public import StacksFrontier.AlgebraicGeometry.Blowup.PicardGroup
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.GlobalFunctionsConstant
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseFibreAux

/-!
# Models with an integral special fibre contain no exceptional curve

Let `R` be a discrete valuation ring with residue field `k`, and let `X ⟶ Spec R` be flat and
universally closed. If the special fibre `X_k` is integral of dimension at most one, then `X`
contains no exceptional curve of the first kind.

## Main results

* `AlgebraicGeometry.comp_eq_Spec_residue_of_projectiveLine`: a closed subscheme of `X` that is a
  projective line over some field lies over the closed point of `Spec R`.
* `AlgebraicGeometry.eq_specialFibre_of_projectiveLine`: such a closed subscheme is the special
  fibre, when the special fibre is integral of dimension at most one.
* `AlgebraicGeometry.not_hasExceptionalCurveOfFirstKind_of_isIntegral_specialFibre`: the main
  statement.

## Implementation notes

The argument has three steps. A projective line `E ≅ 𝐏¹_κ` has no functions beyond `κ`, so
`E ⟶ Spec R` has one point as image; that image is closed, `X` being universally closed over
`R`, so it is the closed point and `E` lies in the special fibre. Inside the special fibre, an
irreducible closed subset of dimension one fills an irreducible space of dimension at most one,
and a surjective closed immersion into a reduced scheme is an isomorphism, so `E = X_k`. Finally
`𝒪_X(X_k) ≅ 𝒪_X`, because `X_k` is cut out by a uniformizer ([Stacks, Tag 0C5Z]), while the class
of an exceptional curve of the first kind has infinite order in the Picard group
([Stacks, Tag 0C5G]).

## References

* [Stacks Project, Tag 0C2V](https://stacks.math.columbia.edu/tag/0C2V)
* [Stacks Project, Section 0C2I](https://stacks.math.columbia.edu/tag/0C2I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The structure morphism of the residue field of a local ring, as a morphism of spectra. -/
noncomputable abbrev residueSpecMap (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))

/-- **A projective line in a scheme universally closed over a local ring lies over the closed
point.** If `e : 𝐏¹_κ ≅ E` presents a closed subscheme `E ⊆ X` as a projective line over a field
`κ`, then `E ⟶ X ⟶ Spec R` factors through the closed point `Spec k ⟶ Spec R`: the functions on
`𝐏¹_κ` are constant, so the image of `E` is one point, and it is closed. -/
theorem comp_eq_Spec_residue_of_projectiveLine {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (D : X.IdealSheafData) (κ : Type u) [Field κ]
    (e : projectiveSpaceOverRing 1 (.of κ) ≅ D.subscheme) :
    ∃ h : D.subscheme ⟶ Spec (.of (IsLocalRing.ResidueField R)),
      D.subschemeι ≫ f = h ≫ residueSpecMap R := by
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_Spec_map_of_projectiveSpaceOverRing κ 1
    (e.hom ≫ D.subschemeι ≫ f)
  -- every point of `𝐏¹_κ` maps to the prime `ker ψ`
  have hpt : ∀ x : projectiveSpaceOverRing 1 (.of κ),
      (e.hom ≫ D.subschemeι ≫ f) x = ⟨RingHom.ker ψ.hom, RingHom.ker_isPrime _⟩ := by
    intro x
    rw [hψ, Scheme.Hom.comp_apply]
    set y := (projectiveSpaceOverRing 1 (.of κ) ↘ Spec (.of κ)) x
    apply PrimeSpectrum.ext
    change Ideal.comap ψ.hom y.asIdeal = _
    rw [@Ideal.eq_bot_of_prime _ _ _ y.isPrime]
    rfl
  -- the image is closed, hence the prime `ker ψ` is the maximal ideal
  obtain ⟨x₀⟩ : Nonempty (projectiveSpaceOverRing 1 (.of κ)) :=
    (isIntegral_projectiveSpace_one κ).nonempty
  have hrange : Set.range (e.hom ≫ D.subschemeι ≫ f) =
      {⟨RingHom.ker ψ.hom, RingHom.ker_isPrime _⟩} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨x₀, hpt x₀⟩, fun _ ⟨x, hx⟩ => hx ▸ hpt x⟩
  have hclosed : IsClosed (Set.range (e.hom ≫ D.subschemeι ≫ f)) :=
    (e.hom ≫ D.subschemeι ≫ f).isClosedMap.isClosed_range
  rw [hrange] at hclosed
  have hker : RingHom.ker ψ.hom = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hclosed)
  let ψ' : IsLocalRing.ResidueField R →+* κ :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) ψ.hom fun a ha => by rwa [← hker] at ha
  have hψψ' : ψ = CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)) ≫
      CommRingCat.ofHom ψ' := by
    ext r
    rfl
  refine ⟨e.inv ≫ (projectiveSpaceOverRing 1 (.of κ) ↘ Spec (.of κ)) ≫
    Spec.map (CommRingCat.ofHom ψ'), ?_⟩
  rw [← cancel_epi e.hom, hψ, hψψ', Spec.map_comp]
  simp only [IsLocalRing.ResidueField.algebraMap_eq, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- **Over a local ring, a projective line contains the special fibre as an ideal sheaf.** The
ideal sheaf of the special fibre, that is the kernel of `X_k ⟶ X`, is contained in the ideal sheaf
of any closed subscheme of `X` that is a projective line over some field. -/
theorem ker_specialFibre_le_of_projectiveLine {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (D : X.IdealSheafData) (κ : Type u) [Field κ]
    (e : projectiveSpaceOverRing 1 (.of κ) ≅ D.subscheme) :
    (pullback.fst f (residueSpecMap R)).ker ≤ D := by
  obtain ⟨h, hh⟩ := comp_eq_Spec_residue_of_projectiveLine f D κ e
  calc (pullback.fst f (residueSpecMap R)).ker
      ≤ (pullback.lift D.subschemeι h hh ≫ pullback.fst f (residueSpecMap R)).ker :=
        Scheme.Hom.le_ker_comp _ _
    _ = D := by rw [pullback.lift_fst, Scheme.IdealSheafData.ker_subschemeι]

/-- The support of an ideal sheaf has the dimension of any scheme isomorphic to the closed
subscheme it cuts out. -/
private theorem Scheme.IdealSheafData.topologicalKrullDim_support_eq_of_iso {X Y : Scheme.{u}}
    (D : X.IdealSheafData) (e : Y ≅ D.subscheme) :
    topologicalKrullDim (D.support : Set X) = topologicalKrullDim Y :=
  (IsHomeomorph.topologicalKrullDim_eq _
    ((Scheme.homeoOfIso e).trans
      (D.subschemeι.isClosedEmbedding.toIsEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr D.range_subschemeι))).isHomeomorph).symm

/-- The support of an ideal sheaf cutting out an irreducible subscheme is irreducible. -/
private theorem Scheme.IdealSheafData.isIrreducible_support {X : Scheme.{u}}
    (D : X.IdealSheafData) [IrreducibleSpace D.subscheme] : IsIrreducible (D.support : Set X) := by
  rw [← D.range_subschemeι, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ D.subschemeι.continuous.continuousOn

/-- Two nested ideal sheaves with the same support agree, when the larger subscheme is
reduced. -/
private theorem Scheme.IdealSheafData.eq_of_le_of_support_eq {X : Scheme.{u}}
    {I D : X.IdealSheafData} (hle : I ≤ D) (hsupp : (D.support : Set X) = I.support)
    [IsReduced I.subscheme] : D = I := by
  let ι := Scheme.IdealSheafData.inclusion hle
  have hι : ι ≫ I.subschemeι = D.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι hle
  have : IsClosedImmersion (ι ≫ I.subschemeι) := hι ▸ inferInstance
  have : IsClosedImmersion ι := IsClosedImmersion.of_comp ι I.subschemeι
  have : Surjective ι := by
    refine ⟨fun y => ?_⟩
    obtain ⟨z, hz⟩ : I.subschemeι y ∈ Set.range D.subschemeι := by
      rw [D.range_subschemeι, hsupp, ← I.range_subschemeι]
      exact ⟨y, rfl⟩
    refine ⟨z, I.subschemeι.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hι, hz]
  have : IsIso ι := isIso_of_isClosedImmersion_of_surjective ι
  calc D = D.subschemeι.ker := (Scheme.IdealSheafData.ker_subschemeι D).symm
    _ = (ι ≫ I.subschemeι).ker := by rw [hι]
    _ = I.subschemeι.ker := Scheme.Hom.ker_comp_of_isIso ι I.subschemeι
    _ = I := Scheme.IdealSheafData.ker_subschemeι I

/-- **A projective line in a model with an integral special fibre of dimension at most one is
the special fibre.** The projective line lies in the special fibre, is irreducible of dimension
one, and so fills it; a surjective closed immersion into a reduced scheme is an isomorphism. -/
theorem eq_specialFibre_of_projectiveLine {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    [IsIntegral (pullback f (residueSpecMap R))]
    (hdim : topologicalKrullDim (pullback f (residueSpecMap R) : Scheme.{u}) ≤ 1)
    (D : X.IdealSheafData) (κ : Type u) [Field κ]
    (e : projectiveSpaceOverRing 1 (.of κ) ≅ D.subscheme) :
    D = (pullback.fst f (residueSpecMap R)).ker := by
  set j := pullback.fst f (residueSpecMap R)
  set I := j.ker
  have hle : I ≤ D := ker_specialFibre_le_of_projectiveLine f D κ e
  -- the special fibre and its ideal-sheaf subscheme
  have : IsClosedImmersion (residueSpecMap R) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let eI : pullback f (residueSpecMap R) ≅ I.subscheme := asIso j.toImage
  have : IsIntegral I.subscheme := IsIntegral.of_isIso eI.hom
  have : IsIntegral (projectiveSpaceOverRing 1 (.of κ)) := isIntegral_projectiveSpace_one κ
  have : IsIntegral D.subscheme := IsIntegral.of_isIso e.hom
  -- dimensions of the two supports
  have hdimI : topologicalKrullDim (I.support : Set X) ≤ 1 := by
    rwa [I.topologicalKrullDim_support_eq_of_iso eI]
  have hdimD : topologicalKrullDim (D.support : Set X) = 1 := by
    rw [D.topologicalKrullDim_support_eq_of_iso e]
    exact topologicalKrullDim_projectiveSpace_one κ
  have hsupp : (D.support : Set X) = I.support := by
    refine le_antisymm (Scheme.IdealSheafData.support_antitone hle) ?_
    by_contra hlt
    let W : IrreducibleCloseds X := ⟨D.support, D.isIrreducible_support, D.support.isClosed⟩
    let C : IrreducibleCloseds X := ⟨I.support, I.isIrreducible_support, I.support.isClosed⟩
    have hWC : W < C := lt_of_le_of_ne
      (show (W : Set X) ⊆ C from Scheme.IdealSheafData.support_antitone hle)
      fun h => hlt (congrArg (fun Z : IrreducibleCloseds X => (Z : Set X)) h).ge
    exact ((hdimD.symm.trans_lt (topologicalKrullDim_lt_of_lt_irreducibleCloseds W C hWC
      (hdimD.trans_ne (by decide)))).trans_le hdimI).false
  exact Scheme.IdealSheafData.eq_of_le_of_support_eq hle hsupp

/-- **A flat universally closed scheme over a discrete valuation ring whose special fibre is
integral of dimension at most one contains no exceptional curve of the first kind.** An
exceptional curve would be the special fibre, whose invertible sheaf is trivial because the
special fibre is cut out by a uniformizer; but the class of an exceptional curve of the first
kind has infinite order in the Picard group. -/
theorem not_hasExceptionalCurveOfFirstKind_of_isIntegral_specialFibre {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [Flat f] [UniversallyClosed f]
    [IsIntegral (pullback f (residueSpecMap R))]
    (hdim : topologicalKrullDim (pullback f (residueSpecMap R) : Scheme.{u}) ≤ 1) :
    ¬ X.HasExceptionalCurveOfFirstKind := by
  rintro ⟨κ, _, D, e, hE⟩
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  have hD : D = (pullback.fst f (residueSpecMap R)).ker :=
    eq_specialFibre_of_projectiveLine f hdim D κ
      ((Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison κ 1).iso ≪≫ e)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.fst f (residueSpecMap R)).ker :=
    Stacks.Models.isEffectiveCartierDivisor_specialFiber (AlgEquiv.refl) f
  have h0 : Stacks.Divisors.picardClass (pullback.fst f (residueSpecMap R)).ker = 0 :=
    (Stacks.SheafOfModules.picardClass_eq_zero_iff _ _ _ _).2
      ⟨Stacks.Models.invertibleSheafIsoUnit_specialFiber (AlgEquiv.refl) f hπ⟩
  exact one_ne_zero (hE.eq_zero_of_zsmul_picardClass_eq_zero D κ e 1
    (by rw [one_smul, Stacks.Divisors.picardClass_congr hD, h0]))

end AlgebraicGeometry

end
