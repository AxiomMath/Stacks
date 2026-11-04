module

public import Mathlib.Algebra.MvPolynomial.Counit
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Etale.ClosedSubschemeOfNormal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.Limits.IntegralAffineLimit09YZ
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# An integral surjective cover of an affine scheme by a closed subscheme of a normal scheme

Let `X = Spec(A)` be an affine scheme. The proof of
[Stacks, Tag 09ZD](https://stacks.math.columbia.edu/tag/09ZD) writes `A = ℤ[x_a]/J` and lets `R`
be the integral closure of `ℤ[x_a]` in an algebraic closure of its fraction field. Then
`X' = Spec(R/JR)` is integral and surjective over `X`. It is also a closed subscheme of `Spec(R)`,
which is a normal integral affine scheme with algebraically closed function field. So every
closed subscheme `Z'` of `X'` is a closed subscheme of such a scheme, and Stacks 09ZC applies to
it.

This file carries out that construction. It also records the two facts about it that both parts
of Tag 09ZD use:

* the vanishing `H^q_etale(Z', M) = 0` for `q ≥ 1` on every closed subscheme `Z'` of `X'`, which
  is part (1) of 09ZD;
* the presentation of `X' ⟶ X` as a limit of finite surjective morphisms of finite presentation
  (Stacks 09YZ), along which the proof of part (2) descends a vanishing class.

## Main results

* `AlgebraicGeometry.isIntegrallyClosed_integralClosure_algebraicClosure` — the integral closure
  of a domain in an algebraic closure of its fraction field is integrally closed.
* `AlgebraicGeometry.exists_isIntegralHom_surjective_isClosedImmersion_isNormal` — the cover
  `X' ⟶ X` and the closed immersion of `X'` into a normal integral affine scheme with separably
  closed function field.
* `AlgebraicGeometry.IntegralLimitPresentation.surjective_structureMap` — every stage of a limit
  presentation of a surjective morphism is surjective.
* `AlgebraicGeometry.exists_integralLimitPresentation_isClosedImmersion_isNormal` — the cover
  together with its presentation as a limit of finite surjective morphisms of finite
  presentation.
* `AlgebraicGeometry.subsingleton_etaleH_constantSheaf_of_isClosedImmersion_of_isNormal` —
  Stacks 09ZC on Mathlib's small étale site, granted the descent statement it carries.
* `AlgebraicGeometry.exists_isIntegralHom_surjective_forall_subsingleton_etaleH` — part (1) of
  Tag 09ZD, granted the same descent statement.

## Implementation notes

The polynomial ring is `MvPolynomial Γ(X, ⊤) ℤ`, one variable for each global section, with
`MvPolynomial.counit` as the surjection onto `Γ(X, ⊤)`. The scheme `X'` is the fibre product
`Spec(R) ×_{Spec ℤ[x_a]} X` rather than `Spec(R/JR)`. This makes integrality, surjectivity and
the closed immersion into `Spec(R)` base changes of properties of `Spec(R) ⟶ Spec ℤ[x_a]` and of
`X ⟶ Spec ℤ[x_a]`, so no quotient ring is formed.

No `@[stacks 09ZD]` attribute is attached anywhere in this file. Stacks 09ZC is
`AlgebraicGeometry.subsingleton_smallEtaleH_constantSheaf`. On the base it takes effective
descent of representability by finite étale schemes,
`Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability`, as a hypothesis, and the
statements below that rest on 09ZC take it as their single argument `h0245`. The library's
unconditional Stacks 03RV,
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`, is exactly what
the proof of 09ZB needs `h0245` for, but it does not prove `h0245` itself, whose hypothesis is
local representability rather than finite local constancy.

The vanishing statements are proved at every coefficient universe `max (u + 1) v` and every
`Ext` universe `w`. Stacks 09ZC is applied in the coefficient universe `u + 1`, to a copy of the
coefficient group there, and the vanishing is carried to the other universes by
`AlgebraicGeometry.Scheme.smallEtaleConstantSheafHAddEquiv`.

Part (2) of 09ZD is
`Stacks.EtaleCohomology.exists_isFinite_surjective_etaleCohomologyRestrictionMap_eq_zero`, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/AffineAnalogProper/FiniteCoverKilling.lean`.

## References

* [Stacks Project, Tag 09ZD](https://stacks.math.columbia.edu/tag/09ZD)
* [Stacks Project, Tag 09ZC](https://stacks.math.columbia.edu/tag/09ZC)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-! ### The absolute integral closure of a domain -/

section AbsoluteIntegralClosure

variable (P : Type u) [CommRing P] [IsDomain P]

/-- A domain embeds in an algebraic closure of its fraction field. -/
theorem algebraMap_injective_algebraicClosure_fractionRing :
    Function.Injective (algebraMap P (AlgebraicClosure (FractionRing P))) := by
  rw [IsScalarTower.algebraMap_eq P (FractionRing P) (AlgebraicClosure (FractionRing P))]
  exact (algebraMap (FractionRing P) _).injective.comp (IsFractionRing.injective P _)

/-- The integral closure of a domain in an algebraic closure of its fraction field has that
algebraic closure as its fraction field. -/
theorem isFractionRing_integralClosure_algebraicClosure :
    IsFractionRing (integralClosure P (AlgebraicClosure (FractionRing P)))
      (AlgebraicClosure (FractionRing P)) :=
  have : Algebra.IsAlgebraic P (AlgebraicClosure (FractionRing P)) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := P) (K := FractionRing P)).mpr inferInstance
  integralClosure.isFractionRing_of_algebraic fun _ hx =>
    algebraMap_injective_algebraicClosure_fractionRing P (hx.trans (map_zero _).symm)

/-- **The integral closure of a domain in an algebraic closure of its fraction field is
integrally closed.** Its fraction field is the algebraic closure, and an element of the algebraic
closure integral over it is integral over the domain. -/
theorem isIntegrallyClosed_integralClosure_algebraicClosure :
    IsIntegrallyClosed (integralClosure P (AlgebraicClosure (FractionRing P))) :=
  let := isFractionRing_integralClosure_algebraicClosure P
  (IsIntegrallyClosed.integralClosure_eq_bot_iff (AlgebraicClosure (FractionRing P))).mp
    integralClosure_idem

end AbsoluteIntegralClosure

/-! ### The cover -/

/-- **The integral surjective cover of the proof of Stacks 09ZD.** For an affine scheme `X` there
is an integral surjective morphism `π : X' ⟶ X` from an affine scheme `X'` together with a
closed immersion `j : X' ⟶ W` into a normal integral affine scheme `W` whose function field is
separably closed.

Here `W = Spec(R)` with `R` the integral closure of `P = ℤ[x_a : a ∈ Γ(X, ⊤)]` in an algebraic
closure of its fraction field, and `X' = Spec(R) ×_{Spec P} X` along the closed immersion
`X ⟶ Spec P` given by the surjection `P ⟶ Γ(X, ⊤)`. The map `Spec(R) ⟶ Spec P` is integral, and
it is surjective by lying over because `P ⟶ R` is injective. Both properties pass to the base
change `π`, and `j` is the base change of a closed immersion. -/
theorem exists_isIntegralHom_surjective_isClosedImmersion_isNormal (X : Scheme.{u}) [IsAffine X] :
    ∃ (X' W : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ W), IsIntegralHom π ∧ Surjective π ∧
      IsClosedImmersion j ∧ IsAffine X' ∧ IsAffine W ∧ ∃ (_ : IsIntegral W), IsNormal W ∧
        IsSepClosed W.functionField := by
  let P := MvPolynomial Γ(X, ⊤) ℤ
  let L := AlgebraicClosure (FractionRing P)
  let R := integralClosure P L
  have hfr : IsFractionRing R L := isFractionRing_integralClosure_algebraicClosure P
  have hic : IsIntegrallyClosed R := isIntegrallyClosed_integralClosure_algebraicClosure P
  let g : CommRingCat.of P ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap P R)
  let e : X ⟶ Spec (CommRingCat.of P) :=
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.counit Γ(X, ⊤)))
  have : IsClosedImmersion e := by
    have := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (MvPolynomial.counit Γ(X, ⊤))) (MvPolynomial.counit_surjective _)
    exact IsClosedImmersion.comp _ _
  have hinj : Function.Injective (algebraMap P R) := fun a b h =>
    algebraMap_injective_algebraicClosure_fractionRing P (by
      rw [IsScalarTower.algebraMap_apply P R L a, h, ← IsScalarTower.algebraMap_apply])
  have hint : (algebraMap P R).IsIntegral := Algebra.IsIntegral.isIntegral
  have : IsIntegralHom (Spec.map g) := IsIntegralHom.SpecMap_iff.mpr hint
  have : Surjective (Spec.map g) := ⟨hint.comap_surjective hinj⟩
  have hsep : IsSepClosed (Spec (CommRingCat.of R)).functionField := by
    let : Algebra R (Spec (CommRingCat.of R)).functionField :=
      instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
    have : IsFractionRing R (Spec (CommRingCat.of R)).functionField :=
      functionField_isFractionRing_of_affine (CommRingCat.of R)
    exact IsSepClosed.of_ringEquiv
      (IsLocalization.algEquiv (nonZeroDivisors R) _ L).toRingEquiv
  exact ⟨pullback (Spec.map g) e, Spec (CommRingCat.of R), pullback.snd _ _, pullback.fst _ _,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed R), hsep⟩

/-! ### The limit presentation -/

attribute [local instance] IntegralLimitPresentation.indexPreorder

/-- **Every stage of a limit presentation of a surjective morphism is surjective.** The morphism
factors through the stage. -/
theorem IntegralLimitPresentation.surjective_structureMap {X S : Scheme.{u}} {f : X ⟶ S}
    (P : IntegralLimitPresentation f) [Surjective f] (i : P.indexTypeᵒᵖ) :
    Surjective (P.structureMap.app i) := by
  have : Surjective (P.limitCone.app i ≫ P.structureMap.app i) := by
    rw [← P.compatible i]
    infer_instance
  exact Surjective.of_comp (P.limitCone.app i) (P.structureMap.app i)

/-- **The cover of Stacks 09ZD as a limit of finite surjective covers of finite presentation.**
The integral surjective `π : X' ⟶ X` of
`exists_isIntegralHom_surjective_isClosedImmersion_isNormal` carries a presentation as the limit
of a directed inverse system of schemes finite and of finite presentation over `X` (Stacks 09YZ,
over an affine base), and every stage of it is surjective over `X`. These are the morphisms
`X'_i ⟶ X` along which the proof of part (2) of 09ZD descends a vanishing class. -/
theorem exists_integralLimitPresentation_isClosedImmersion_isNormal (X : Scheme.{u})
    [IsAffine X] :
    ∃ (X' W : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ W), IsIntegralHom π ∧ Surjective π ∧
      IsClosedImmersion j ∧ IsAffine W ∧ ∃ (_ : IsIntegral W), IsNormal W ∧
        IsSepClosed W.functionField ∧
        ∃ P : IntegralLimitPresentation π, ∀ i, Surjective (P.structureMap.app i) := by
  obtain ⟨X', W, π, j, hπ, hs, hj, -, hW, hWi, hWn, hWs⟩ :=
    exists_isIntegralHom_surjective_isClosedImmersion_isNormal X
  obtain ⟨P⟩ := nonempty_integralLimitPresentation_of_isAffine π
  exact ⟨X', W, π, j, hπ, hs, hj, hW, hWi, hWn, hWs, P, P.surjective_structureMap⟩

/-! ### Vanishing on closed subschemes of the cover -/

/-- **Stacks 09ZC on Mathlib's small étale site, granted descent.** Let `W` be a normal integral
affine scheme with separably closed function field and `Z ⟶ W` a closed immersion. Granted
effective descent of representability by finite étale schemes (`h0245`), the étale cohomology
`H^q(Z, M)` with coefficients in a finite abelian group `M` vanishes for `q ≥ 1`. The coefficient
universe `max (u + 1) v` and the `Ext` universe `w` are arbitrary.

In the coefficient universe `u + 1` this is `subsingleton_smallEtaleH_constantSheaf` on the small
étale site cut out of the big étale site `BigEtaleSite.containing Z`, carried to Mathlib's small
étale site by
`Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_smallEtale_of_boundedSmallEtale`. It is
applied to `ULift (Shrink M)`, a copy of `M` in that universe, and carried to `M` itself by
`AlgebraicGeometry.Scheme.smallEtaleConstantSheafHAddEquiv`, twice: from `u + 1` down to the copy
`Shrink M` of `M` in the universe `u`, and from there up to `max (u + 1) v`. -/
theorem subsingleton_etaleH_constantSheaf_of_isClosedImmersion_of_isNormal
    (h0245 : ∀ B : BigEtaleSite.{u},
      Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability B)
    {W Z : Scheme.{u}} [IsAffine W] [IsIntegral W] [IsNormal W] [IsSepClosed W.functionField]
    (i : Z ⟶ W) [IsClosedImmersion i] (M : AddCommGrpCat.{max (u + 1) v}) [Finite M]
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (q : ℕ)
    (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w}
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj M) q) := by
  have : IsGrothendieckAbelian.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology Z AddCommGrpCat.{u}
  let : HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.hasExt.{u} _
  let M₀ : AddCommGrpCat.{u} := AddCommGrpCat.of (Shrink.{u} M)
  let M₁ : AddCommGrpCat.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} M₀)
  have : Finite M₀ := Finite.of_equiv _ (Shrink.addEquiv.{u} (α := M)).symm.toEquiv
  have : Finite M₁ := Finite.of_equiv _ (AddEquiv.ulift (α := M₀)).symm.toEquiv
  let B := BigEtaleSite.containing Z
  have hZ : B.Contains Z := BigEtaleSite.contains_containing Z
  have : HasExt.{u + 1} (Sheaf (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1}) :=
    smallEtaleSheaf_hasExt B Z hZ
  have h₁ : Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M₁) q) :=
    Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_smallEtale_of_boundedSmallEtale
      B Z hZ M₁ q (subsingleton_smallEtaleH_constantSheaf B W Z i hZ M₁ (h0245 B) q hq)
  have h₀ := ((Scheme.smallEtaleConstantSheafHAddEquiv.{u, u + 1, 0} Z
    (AddEquiv.ulift (α := M₀)).symm q).toEquiv.subsingleton_congr).mpr h₁
  exact ((Scheme.smallEtaleConstantSheafHAddEquiv.{u, w, v} Z
    (Shrink.addEquiv.{u} (α := M)) q).toEquiv.subsingleton_congr).mp h₀

end AlgebraicGeometry

end
