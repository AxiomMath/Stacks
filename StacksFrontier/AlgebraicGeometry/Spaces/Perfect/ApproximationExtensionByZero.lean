module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplementClauses
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekSupport
import StacksCore.Tactic.StacksAttribute

/-!
# Approximation across an elementary distinguished square

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S` and set `T₀ = |X| \ |U|`.

* **Stacks 08HK.**  If `E` is a perfect object of `D(𝒪_V)` supported on `j^{-1}T₀`, then `Rj_*E`
  is perfect.
* **Stacks 08HL.**  If `T ⊆ T₀`, `(T, E, m)` is a triple as in Stacks 08HI, approximation holds
  for `(j^{-1}T, E|_V, m)` and `Hⁱ(E)` is supported on `T` for `i ≥ m`, then approximation holds
  for `(T, E, m)`.

## The proofs

*Stacks 08HK.*  Perfectness is local along the square
(`AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsRestrict`).  The extension by zero `j_!E` of
a perfect `E` supported on `j^{-1}T₀` is supported on `T₀`, so it restricts to zero on `U`; and
its restriction to `V` is `E` by clause (2)(a) of Stacks 08GG.  So `j_!E` is perfect, and
`Rj_*E ≅ j_!E` by clause (2)(c) of Stacks 08GG.

*Stacks 08HL.*  For an approximation `α : P ⟶ E|_V` of the restricted triple, the approximation of
`(T, E, m)` is `j_!P ⟶ j_!(E|_V) ⟶ E`, the image of `α` under `j_!` followed by the counit.  This
is the source's `Rj_*P = j_!P ⟶ j_!(E|_V) ⟶ E`, the first identification being Stacks 08GG part
(2) clause (c).  `j_!P` is perfect as in Stacks 08HK and supported on `T` by Equation 08GU.  Since
`j_!` is exact it commutes with cohomology sheaves, so `j_!α` is an isomorphism on `Hⁱ` for
`i > m` and a surjection on `Hᵐ`.  The counit is an isomorphism on `Hⁱ` for `i ≥ m`
(`AlgebraicGeometry.Space.isIso_homology_counit_of_supportedFrom`): it is natural, the truncation
`E ⟶ τ_{≥m}E` is an isomorphism on `Hⁱ` for `i ≥ m`, `τ_{≥m}E` is supported on `T₀` by the
support hypothesis, and on objects supported on `T₀` the counit is an isomorphism by clause
(1)(b) of Stacks 08GG.

## Implementation notes

`T` is an arbitrary subset of `|X| \ |U|`, as in `AlgebraicGeometry.Space.ApproximationHolds`;
closedness of `T` is part of the source's notion of a triple and is used nowhere in this lemma.
The restricted triple is `(j^{-1}T, E|_V, m)` with `E|_V` the image of `E` under
`AlgebraicGeometry.Space.quasicoherentDerivedEtalePullback`, Stacks 08F4 for an étale morphism.

## References

* [Stacks Project, Tag 08HK](https://stacks.math.columbia.edu/tag/08HK)
* [Stacks Project, Tag 08HL](https://stacks.math.columbia.edu/tag/08HL)
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
  smallEtaleRingedSite_hasSheafify smallEtaleRingedSite_wEqualsLocallyBijective

section Square

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The extension by zero of a perfect object supported on `j^{-1}T₀` is perfect.**  It
restricts to zero on the open subspace, being supported on `T₀`, and to the given object on the
étale space, by clause (2)(a) of Stacks 08GG; perfectness is local along the square. -/
theorem isPerfect_lowerShriek_of_cohomologySupportedOn
    (P : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hP : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).IsPerfect P)
    (hPs : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) P) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj P) := by
  have hunit := isIso_unit_mapDerivedCategory_lowerShriek_of_cohomologySupportedOn B S hS hsq P hPs
  refine isPerfect_of_isPerfect_edsRestrict B S hS hsq _
    (RingedSite.isPerfect_of_isZero _
      (isZero_edsOpen_and_edsInter_of_cohomologySupportedOn B S hS hsq _
        (cohomologySupportedOn_lowerShriek_of_cohomologySupportedOn B S hS hsq P hPs)).1) ?_
  exact RingedSite.IsPerfect.of_iso _ hP (asIso ((etaleModuleLowerShriekAdjunction B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.unit.app P))

/-- **Stacks 08HK.**  Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic
spaces over a scheme `S` and set `T = |X| \ |U|`.  If `E` is a perfect object of `D(𝒪_V)`
supported on `j^{-1}T`, then `Rj_*E` is a perfect object of `D(𝒪_X)`.

`Rj_*` is any right adjoint of derived restriction, which pins it; a total right derived functor
of the direct image is one, by
`AlgebraicGeometry.Space.etaleModulePullbackDerivedPushforwardAdjunction`. -/
@[stacks 08HK "Rj_*E is a perfect object of D(O_X) for E perfect on V and supported on j^{-1}T,
T = |X| \\ |U|, for an elementary distinguished square and nothing else bound; Rj_* is any right
adjoint of derived restriction, which pins it"]
theorem isPerfect_derivedPushforward_of_isPerfect_of_cohomologySupportedOn
    {RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjPush : edsDerivedRestrictEtale B S hS hsq ⊣ RpushD)
    (E : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hE : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).IsPerfect E)
    (hEs : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) E) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect (RpushD.obj E) := by
  have h := isIso_supportedShriekToPushforward_of_supported B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory adjPush E hEs
  exact RingedSite.IsPerfect.of_iso _ (isPerfect_lowerShriek_of_cohomologySupportedOn B S hS hsq E
    hE hEs) (asIso (supportedShriekToPushforward B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory adjPush E
      (isIso_unit_derivedShriek_of_cohomologySupportedOn B S hS hsq _ E hEs)))

/-- The truncation `E ⟶ τ_{≥m}E` of an object of a derived category, with its two properties: it
is an isomorphism on `Hⁱ` for `i ≥ m`, and `τ_{≥m}E` has no cohomology below `m`. -/
theorem exists_truncGE {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (E : DerivedCategory C) (m : ℤ) :
    ∃ (τ : DerivedCategory C) (π : E ⟶ τ),
      (∀ i : ℤ, m ≤ i → IsIso ((DerivedCategory.homologyFunctor C i).map π)) ∧
        ∀ i : ℤ, i < m → IsZero ((DerivedCategory.homologyFunctor C i).obj τ) := by
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  refine ⟨DerivedCategory.Q.obj (K.truncGE m), e.inv ≫ DerivedCategory.Q.map (K.πTruncGE m),
    fun i hi => ?_, fun i hi => ?_⟩
  · have h1 : IsIso ((DerivedCategory.homologyFunctor C i).map
        (DerivedCategory.Q.map (K.πTruncGE m))) := by
      rw [← Functor.comp_map, NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C i)]
      exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 (K.quasiIsoAt_πTruncGE m i hi)
    rw [Functor.map_comp]
    infer_instance
  · exact ((DerivedCategory.homologyFunctorFactors C i).app (K.truncGE m)).isZero_iff.2
      (CochainComplex.isZero_of_isGE (K.truncGE m) m i hi)

/-- **The counit of extension by zero is an isomorphism on cohomology from the degree on which the
support condition holds.**  If `Hⁱ(E)` is supported on `T₀ = |X| \ |U|` for every `i ≥ m`, then
the counit `j_!(E|_V) ⟶ E` is an isomorphism on `Hⁱ` for every `i ≥ m`. -/
theorem isIso_homology_counit_of_supportedFrom (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (m : ℤ)
    (hsupp : ∀ i : ℤ, m ≤ i →
      supportOfSheaf B S hS W.1
        ((SheafOfModules.toSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).obj E)) ⊆
        edsComplementPoints B S hS Uo)
    (i : ℤ) (hi : m ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).map
      ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.counit.app E)) := by
  let adj := (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  let sh := etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
  let r := etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  let H := fun k : ℤ => DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) k
  obtain ⟨τ, π, hπ, hτ⟩ := exists_truncGE E m
  have hτs : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) τ := by
    intro k
    rcases lt_or_ge k m with hk | hk
    · have h0 := (supportOfSheaf_eq_empty_iff_isZero B S hS W _).2 (hτ k hk)
      exact fun x hx => absurd (h0.le hx) (Set.notMem_empty x)
    · have := hπ k hk
      exact fun x hx => hsupp k hk
        ((supportOfSheaf_eq_of_iso B S hS W (asIso ((H k).map π))).ge hx)
  have hcτ : IsIso (adj.mapDerivedCategory.counit.app τ) :=
    isIso_counit_derivedRestrict_of_cohomologySupportedOn B S hS hsq adj.mapDerivedCategory τ hτs
  have hπi := hπ i hi
  have h1 : IsIso ((DerivedCategory.homologyFunctor _ i).map (r.mapDerivedCategory.map π)) :=
    (r.isIso_homologyFunctor_map_mapDerivedCategory_map_iff π i).2 inferInstance
  have hrπ : IsIso ((H i).map (sh.mapDerivedCategory.map (r.mapDerivedCategory.map π))) :=
    (sh.isIso_homologyFunctor_map_mapDerivedCategory_map_iff _ i).2 inferInstance
  have hcomp := congrArg (H i).map (adj.mapDerivedCategory.counit.naturality π)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at hcomp
  have : IsIso ((H i).map (adj.mapDerivedCategory.counit.app E) ≫ (H i).map π) := by
    rw [← hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((H i).map π)

/-- **Stacks 08HL.**  Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of
algebraic spaces over a scheme `S`, let `T ⊆ |X| \ |U|` and let `(T, E, m)` be a triple as in
Stacks 08HI.  If

1. approximation holds for `(j^{-1}T, E|_V, m)`, and
2. the sheaves `Hⁱ(E)` for `i ≥ m` are supported on `T`,

then approximation holds for `(T, E, m)`.

The approximation produced is `j_!P ⟶ j_!(E|_V) ⟶ E` for an approximation `P ⟶ E|_V` of the
restricted triple; `j_!P = Rj_*P` by Stacks 08GG part (2) clause (c). -/
@[stacks 08HL "for an elementary distinguished square (U ⊆ X, j : V ⟶ X), T ⊆ |X| \\ |U| and a
triple (T, E, m): approximation for (j^{-1}T, E|_V, m) with E|_V = quasicoherentDerivedEtalePullback
of E, together with H^i(E) supported on T for i ≥ m, gives approximation for (T, E, m); nothing
else is bound. T is any subset of |X| \\ |U|, closedness being unused"]
theorem approximationHolds_of_approximationHolds_edsEtale
    (T : Set (points B S hS W.1)) (hTU : T ⊆ edsComplementPoints B S hS Uo)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2) (m : ℤ)
    (happrox : ApproximationHolds B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T)
      ((quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj E) m)
    (hsupp : ∀ i : ℤ, m ≤ i →
      supportOfSheaf B S hS W.1
        ((SheafOfModules.toSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).obj E.obj)) ⊆ T) :
    ApproximationHolds B S hS W.1 W.2 T E m := by
  let adj := etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  let sh := etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
  obtain ⟨P, hPperf, hPsupp, α, hαiso, hαepi⟩ := happrox
  have hPsupp' : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2 (edsEtalePreimageComplementPoints B S hS hsq) P :=
    CohomologySupportedOn.mono B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 hPsupp
      (Set.preimage_mono hTU)
  let c : sh.mapDerivedCategory.obj ((quasicoherentDerivedEtalePullback B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).obj E).obj ⟶ E.obj :=
    adj.mapDerivedCategory.counit.app E.obj
  have hcounit : ∀ i : ℤ, m ≤ i →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).map c) :=
    isIso_homology_counit_of_supportedFrom B S hS hsq E.obj m
      (fun i hi => (hsupp i hi).trans hTU)
  refine ⟨sh.mapDerivedCategory.obj P,
    isPerfect_lowerShriek_of_cohomologySupportedOn B S hS hsq P hPperf hPsupp',
    cohomologySupportedOn_mapDerivedCategory_etaleModuleLowerShriek B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) P T hPsupp,
    sh.mapDerivedCategory.map α ≫ c, ?_, ?_⟩
  · intro i hi
    have h₁ : IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).map
        (sh.mapDerivedCategory.map α)) :=
      sh.isIso_homologyFunctor_map_mapDerivedCategory_map α i (hαiso i hi)
    have h₂ := hcounit i hi.le
    rw [Functor.map_comp]
    infer_instance
  · have h₁ : Epi ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) m).map
        (sh.mapDerivedCategory.map α)) :=
      sh.epi_homologyFunctor_map_mapDerivedCategory_map α m hαepi
    have h₂ := hcounit m le_rfl
    rw [Functor.map_comp]
    infer_instance

end Square

end AlgebraicGeometry.Space

end
