module

public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroSupported
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectLocalOnSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback

/-!
# Approximation descends along an elementary distinguished square

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S`, let `T ⊆ |X| \ |U|` and let `(T, E, m)` be a triple as in Stacks 08HI.  Stacks 08HL says
that if approximation holds for `(j^{-1}T, E|_V, m)` and the sheaves `Hⁱ(E)` for `i ≥ m` are
supported on `T`, then approximation holds for `(T, E, m)`.

## Main results

* `AlgebraicGeometry.Space.approximationHolds_of_isElementaryDistinguishedSquare`:
  **Stacks 08HL**.

## Implementation notes

*The proof.*  Let `α : P ⟶ E|_V` approximate the restricted triple.  The source takes `Rj_*P`,
perfect by Stacks 08HK, and identifies it with `j_!P` by Stacks 08GG part (2) clause (c).  Here
`j_!P` itself is the approximating object, which removes the derived direct image from the
argument altogether; its perfectness is the source's proof of Stacks 08HK run on `j_!P` instead
of `Rj_*P`:

* perfectness is local on `X_étale` along the covering `{U, V}`,
  `AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsDerivedRestrict`;
* `(j_!P)|_U = 0`, and a zero object is perfect:
  `AlgebraicGeometry.Space.isZero_edsDerivedRestrictOpen_shriek_of_cohomologySupportedOn`;
* `(j_!P)|_V ≅ P` by Stacks 08GG part (2) clause (a),
  `AlgebraicGeometry.Space.isIso_edsEtaleDerivedAdjunction_unit_app_of_cohomologySupportedOn`.

`j_!P` is supported on `T` by Equation 08GU,
`AlgebraicGeometry.Space.cohomologySupportedOn_etaleModuleLowerShriek_mapDerivedCategory`.  The
map to `E` is the source's composite `j_!P ⟶ j_!(E|_V) ⟶ E` of `j_!α` and the counit; `j_!` is
exact, so `j_!α` is an isomorphism on `Hⁱ` for `i > m` and surjective on `Hᵐ`, and the counit is
an isomorphism on `Hⁱ` for every `i ≥ m` by hypothesis (2), through
`AlgebraicGeometry.Space.isIso_homologyFunctor_map_edsEtaleDerivedAdjunction_counit_app`.

*The objects.*  `j_!` is the extension by zero the library constructs,
`AlgebraicGeometry.Space.etaleModuleLowerShriek`, and its adjunction with restriction on derived
categories is `AlgebraicGeometry.Space.edsEtaleDerivedAdjunction`.  The restricted triple is
formed with `E|_V` the étale pullback `AlgebraicGeometry.Space.quasicoherentDerivedEtalePullback`,
which lands in `D_QCoh(𝒪_V)` by Stacks 08F4 for étale morphisms; its underlying object of
`D(𝒪_V)` is `(edsDerivedRestrictEtale hsq).obj E`.  `T` is an arbitrary subset of `|X| \ |U|`
rather than a closed one, which is the convention of `AlgebraicGeometry.Space.ApproximationHolds`;
closedness is not used, so this only strengthens the statement.

## References

* [Stacks Project, Tag 08HL](https://stacks.math.columbia.edu/tag/08HL)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08HK](https://stacks.math.columbia.edu/tag/08HK)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Stacks 08HL.**  Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of
algebraic spaces over a scheme `S`, let `T ⊆ |X| \ |U|` and let `(T, E, m)` be a triple as in
Stacks 08HI.  If

1. approximation holds for `(j^{-1}T, E|_V, m)`, and
2. the sheaves `Hⁱ(E)` for `i ≥ m` are supported on `T`,

then approximation holds for `(T, E, m)`. -/
@[stacks 08HL]
theorem approximationHolds_of_isElementaryDistinguishedSquare
    (T : Set (points B S hS W.1)) (hTU : T ⊆ edsComplementPoints B S hS Uo)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2) (m : ℤ)
    (happrox : ApproximationHolds B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T)
      ((quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj E) m)
    (hsupp : ∀ i : ℤ, m ≤ i →
      supportOfSheaf B S hS W.1
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).obj E.obj)) ⊆ T) :
    ApproximationHolds B S hS W.1 W.2 T E m := by
  obtain ⟨P, hPperf, hPsupp, α, hαiso, hαepi⟩ := happrox
  set shriek := etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  have hPsupp' : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2 (edsEtalePreimageComplementPoints B S hS hsq) P :=
    CohomologySupportedOn.mono B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 hPsupp
      (Set.preimage_mono hTU)
  -- `j_!P` is perfect: it vanishes on `U` and restricts to `P` on `V`.
  have hQperf : (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect
      (shriek.mapDerivedCategory.obj P) := by
    refine isPerfect_of_isPerfect_edsDerivedRestrict B S hS hsq _ (RingedSite.isPerfect_of_isZero _
      (isZero_edsDerivedRestrictOpen_shriek_of_cohomologySupportedOn B S hS hsq P hPsupp')) ?_
    have := isIso_edsEtaleDerivedAdjunction_unit_app_of_cohomologySupportedOn B S hS hsq P
      hPsupp'
    exact RingedSite.IsPerfect.of_iso _ hPperf
      (asIso ((edsEtaleDerivedAdjunction B S hS hsq).unit.app P))
  refine ⟨shriek.mapDerivedCategory.obj P, hQperf,
    CohomologySupportedOn.mono B S hS W.1 W.2
      (cohomologySupportedOn_etaleModuleLowerShriek_mapDerivedCategory B S hS
        (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) T P hPsupp) le_rfl,
    shriek.mapDerivedCategory.map α ≫ (edsEtaleDerivedAdjunction B S hS hsq).counit.app E.obj,
    fun i hi => ?_, ?_⟩
  · have h₁ := shriek.isIso_homologyFunctor_map_mapDerivedCategory_map α i (hαiso i hi)
    have h₂ := isIso_homologyFunctor_map_edsEtaleDerivedAdjunction_counit_app B S hS hsq E.obj i
      ((hsupp i hi.le).trans hTU)
    exact (congrArg IsIso ((DerivedCategory.homologyFunctor _ i).map_comp _ _)).mpr
      (@IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂)
  · have h₁ := shriek.epi_homologyFunctor_map_mapDerivedCategory_map α m hαepi
    have h₂ := isIso_homologyFunctor_map_edsEtaleDerivedAdjunction_counit_app B S hS hsq E.obj m
      ((hsupp m le_rfl).trans hTU)
    exact (congrArg Epi ((DerivedCategory.homologyFunctor _ m).map_comp _ _)).mpr
      (@epi_comp _ _ _ _ _ _ h₁ _ (@IsIso.epi_of_iso _ _ _ _ _ h₂))

end AlgebraicGeometry.Space
