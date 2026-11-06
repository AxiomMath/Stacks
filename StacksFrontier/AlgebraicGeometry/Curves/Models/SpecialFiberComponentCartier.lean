module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberCartier
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Decomposition
public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralDivisorMultiplicity
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorStalk
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineComponents
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
public import StacksCore.Tactic.StacksAttribute

/-!
# The components of the special fibre are effective Cartier divisors

Let `X` be a regular model of a smooth curve over a discrete valuation ring `R` with residue
field `k`. Each irreducible component of the special fibre `X_k`, taken with its reduced induced
structure as a closed subscheme of `X`, is an effective Cartier divisor on `X`. This is the
component clause of [Stacks, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z), the clause
that gives meaning to writing `X_k = ∑ mᵢ Cᵢ`.

## Main definitions

* `Stacks.Models.RegularModelSituation.specialFiberComponentIdeal` — the reduced ideal sheaf on
  `X` of an irreducible component of `X_k`.
* `Stacks.Models.RegularModelSituation.specialFiberComponentPrimeDivisor` — the same component as
  a prime divisor of `X`.
* `Stacks.Models.RegularModelSituation.specialFiberMultiplicity` — the multiplicity `mᵢ` of a
  component `Cᵢ` in `X_k`, the length of `𝒪_{X_k, ξᵢ}` at its generic point.

## Main results

* `Stacks.Models.RegularModelSituation.isEffectiveCartierDivisor_specialFiberComponent` — each
  component of the special fibre is an effective Cartier divisor on the model.
* `Stacks.Models.RegularModelSituation.specialFiberIdeal_eq_prod` — part (3) of Tag 0C5Z,
  `X_k = ∑ mᵢ Cᵢ` as effective Cartier divisors, over the finitely many components.
* `Stacks.Models.RegularModelSituation.specialFiberMultiplicity_pos` — every `mᵢ` is positive.

## The argument

The criterion applied is Tag 0AGA
(`AlgebraicGeometry.isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid`):
an integral closed subscheme of codimension one whose ambient local rings are factorial is an
effective Cartier divisor. Its three inputs are supplied as follows.

*Integral.* The reduced induced structure on an irreducible closed subset is integral — that is
`isIntegral_subscheme_vanishingIdeal_of_isIrreducible`, in the namespace
`Stacks.AlgebraicGeometry.IrreducibleDevissage` — and the image of a component of `X_k` under
the closed immersion `X_k ⟶ X` is irreducible and closed.

*Factorial.* The model is regular, so every local ring of `X` is a regular local ring, hence a
unique factorization domain (`IsRegularLocalRing.uniqueFactorizationMonoid`, Tag 0AG0).

*Codimension one.* The special fibre is an effective Cartier divisor on `X`
(`Stacks.Models.isEffectiveCartierDivisor_specialFiber`, Tag 0C5Z), and a generic point of one of
its components has a one-dimensional local ring by Tag 0BCN
(`AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor`); one-dimensionality
of the local ring at a point is codimension one of the closure of that point
(`AlgebraicGeometry.ringKrullDim_stalk_eq_one_iff_codimension_closureSingleton_eq_one`).

## Implementation notes

Tag 0BCN speaks about components of `ℐ_{X_k}.subscheme`, the closed subscheme of `X` cut out by
the special fibre, whereas a component of the special fibre is given as a component of the
*pullback* `X ×_{Spec R} Spec(k)`. The two schemes are identified by
`AlgebraicGeometry.Scheme.Hom.toImage`, which is an isomorphism because the projection is a
closed immersion, and components transport along the resulting homeomorphism by
`Homeomorph.image_mem_irreducibleComponents`.

The two generic points that then have to be compared — the one Tag 0BCN produces inside
`ℐ_{X_k}.subscheme` and the one Tag 0AGA asks about inside the component's own subscheme — are
both generic points of the same irreducible closed subset of `X`, so they agree by
`IsGenericPoint.eq`; a scheme is `T0Space`.

That the projection `X ×_{Spec R} Spec(k) ⟶ X` is a closed immersion comes from surjectivity of
`R ⟶ k`, which the chosen identification of `k` with the canonical residue field provides
(`Stacks.Models.RegularModelSituation.surjective_algebraMap_residueField`).

## References

* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 0AGA](https://stacks.math.columbia.edu/tag/0AGA)
* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
* [Stacks Project, Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.Models

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-- **The residue map of the discrete valuation ring onto the chosen residue field is
surjective.** The chosen field is identified with `IsLocalRing.ResidueField R` as an
`R`-algebra, and the canonical residue map is surjective. -/
public theorem surjective_algebraMap_residueField : Function.Surjective (algebraMap S.R S.k) := by
  intro z
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (S.residueEquiv.symm z)
  refine ⟨r, ?_⟩
  calc
    algebraMap S.R S.k r = S.residueEquiv (IsLocalRing.residue S.R r) :=
      (S.residueEquiv.commutes r).symm
    _ = z := by rw [hr]; simp

/-- The inclusion `X_k ⟶ X` of the special fibre is a closed immersion, being the base change of
the closed immersion `Spec k ⟶ Spec R`. -/
public instance isClosedImmersion_specialFiberι : IsClosedImmersion S.specialFiberι := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) :=
    IsClosedImmersion.spec_of_surjective _ S.surjective_algebraMap_residueField
  infer_instance

/-- The total space of a regular model is locally Noetherian, being regular. -/
public theorem isLocallyNoetherian_X : IsLocallyNoetherian S.X := by
  obtain ⟨hN, -⟩ := ((isRegular_tfae S.X).out 1 2).mp S.regular
  exact hN

/-- Every local ring of the total space of a regular model is a regular local ring. -/
public theorem isRegularLocalRing_stalk (x : S.X) :
    IsRegularLocalRing (S.X.presheaf.stalk x) := by
  obtain ⟨-, hreg⟩ := ((isRegular_tfae S.X).out 1 2).mp S.regular
  exact hreg x

/-- Every local ring of the total space of a regular model is a unique factorization domain:
it is a regular local ring, and regular local rings are factorial (Tag 0AG0). -/
@[ega "IV 21.11.1" "special case", sga "6 X 7.8" "special case", sga "7 VIII 6.5.1" "special case"]
public theorem uniqueFactorizationMonoid_stalk (x : S.X) :
    UniqueFactorizationMonoid (S.X.presheaf.stalk x) := by
  let _ : IsRegularLocalRing (S.X.presheaf.stalk x) := S.isRegularLocalRing_stalk x
  exact IsRegularLocalRing.uniqueFactorizationMonoid _

variable (Z : irreducibleComponents S.specialFiber)

/-- The image in the model of an irreducible component of the special fibre is closed. -/
public theorem isClosed_image_specialFiberComponent :
    IsClosed (S.specialFiberι.base '' (Z.1 : Set S.specialFiber)) :=
  S.specialFiberι.isClosedEmbedding.isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ Z.2)

/-- The image in the model of an irreducible component of the special fibre is irreducible. -/
public theorem isIrreducible_image_specialFiberComponent :
    IsIrreducible (S.specialFiberι.base '' (Z.1 : Set S.specialFiber)) :=
  Z.2.1.image S.specialFiberι.base S.specialFiberι.continuous.continuousOn

/-- The reduced ideal sheaf of an irreducible component of the special fibre, regarded as a
closed subscheme of the model: the vanishing ideal of the closure of its image in `X`. -/
public abbrev specialFiberComponentIdeal : S.X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (.closure (S.specialFiberι.base '' (Z.1 : Set S.specialFiber)))

/-- The closed set underlying the component ideal is the image of the component itself: the
image is already closed, so taking its closure changes nothing. -/
public theorem coe_closure_image_specialFiberComponent :
    ((Closeds.closure (S.specialFiberι.base '' (Z.1 : Set S.specialFiber)) : Closeds S.X) :
        Set S.X) = S.specialFiberι.base '' (Z.1 : Set S.specialFiber) :=
  (S.isClosed_image_specialFiberComponent Z).closure_eq

/-- The reduced closed subscheme of the model supported on an irreducible component of the
special fibre is integral. -/
public instance isIntegral_specialFiberComponentIdeal :
    IsIntegral (S.specialFiberComponentIdeal Z).subscheme :=
  Stacks.AlgebraicGeometry.IrreducibleDevissage.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    _ (by
      rw [S.coe_closure_image_specialFiberComponent Z]
      exact S.isIrreducible_image_specialFiberComponent Z)

/-- The support of the component ideal is the image of the component. -/
public theorem coe_support_specialFiberComponentIdeal :
    (((S.specialFiberComponentIdeal Z).support : Closeds S.X) : Set S.X) =
      S.specialFiberι.base '' (Z.1 : Set S.specialFiber) := by
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact S.coe_closure_image_specialFiberComponent Z

/-- The generic point of the component, viewed in the model, has the image of the component as
the closure of its singleton. -/
public theorem closure_singleton_genericPoint_specialFiberComponent :
    closure ({(S.specialFiberComponentIdeal Z).subschemeι.base
                (genericPoint (S.specialFiberComponentIdeal Z).subscheme)} : Set S.X) =
      S.specialFiberι.base '' (Z.1 : Set S.specialFiber) := by
  rw [← Set.image_singleton,
    (S.specialFiberComponentIdeal Z).subschemeι.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ,
    (S.specialFiberComponentIdeal Z).range_subschemeι]
  exact S.coe_support_specialFiberComponentIdeal Z

/-- Mapping a point of the special fibre into `ℐ_{X_k}.subscheme` and then into `X` agrees with
the inclusion `X_k ⟶ X`. -/
private theorem subschemeι_base_toImage_hom (x : S.specialFiber) :
    S.specialFiberIdeal.subschemeι.base ((asIso S.specialFiberι.toImage).hom.base x) =
      S.specialFiberι.base x := by
  have he : (asIso S.specialFiberι.toImage).hom ≫ S.specialFiberIdeal.subschemeι =
      S.specialFiberι := S.specialFiberι.toImage_imageι
  have hx := congrArg (fun g : S.specialFiber ⟶ S.X => g.base x) he
  exact hx

/-- The image of an irreducible component of the special fibre has codimension one in the
model.

The special fibre is an effective Cartier divisor on `X` (Tag 0C5Z), so Tag 0BCN gives a
one-dimensional local ring at a generic point of one of its components, and that is codimension
one of the closure of the point. -/
public theorem codimension_specialFiberComponent_eq_one :
    codimension (IrreducibleCloseds.closureSingleton
        ((S.specialFiberComponentIdeal Z).subschemeι.base
          (genericPoint (S.specialFiberComponentIdeal Z).subscheme))) = 1 := by
  let _ : IsLocallyNoetherian S.X := S.isLocallyNoetherian_X
  have hZcl : IsClosed (Z.1 : Set S.specialFiber) :=
    isClosed_of_mem_irreducibleComponents _ Z.2
  -- identify the special fibre with the closed subscheme it cuts out
  let e : S.specialFiber ≅ S.specialFiberIdeal.subscheme := asIso S.specialFiberι.toImage
  let h : S.specialFiber ≃ₜ S.specialFiberIdeal.subscheme := e.hom.homeomorph
  have hh : ∀ x : S.specialFiber, S.specialFiberIdeal.subschemeι.base (h x) =
      S.specialFiberι.base x := S.subschemeι_base_toImage_hom
  -- the corresponding component downstairs, and a generic point of it
  have hZ' : h '' (Z.1 : Set S.specialFiber) ∈
      irreducibleComponents S.specialFiberIdeal.subscheme :=
    h.image_mem_irreducibleComponents Z.2
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober Z.2.1 hZcl
  have hξgen : IsGenericPoint (h ζ) (h '' (Z.1 : Set S.specialFiber)) := by
    have himg := hζ.image (f := h) h.continuous
    rwa [(h.isClosedEmbedding.isClosedMap _ hZcl).closure_eq] at himg
  -- Tag 0BCN at that generic point
  have hdim : ringKrullDim
      (S.X.presheaf.stalk (S.specialFiberIdeal.subschemeι.base (h ζ))) = 1 :=
    ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor S.specialFiberIdeal
      (isEffectiveCartierDivisor_specialFiber S.residueEquiv S.X_to_R) (h ζ)
      ⟨⟨_, hZ'⟩, hξgen⟩
  -- the two generic points in `X` agree
  have hclos : closure ({S.specialFiberIdeal.subschemeι.base (h ζ)} : Set S.X) =
      S.specialFiberι.base '' (Z.1 : Set S.specialFiber) := by
    rw [← Set.image_singleton,
      S.specialFiberIdeal.subschemeι.isClosedEmbedding.closure_image_eq, hξgen.def]
    rw [← Set.image_comp]
    exact Set.image_congr' hh
  have hpteq : S.specialFiberIdeal.subschemeι.base (h ζ) =
      (S.specialFiberComponentIdeal Z).subschemeι.base
        (genericPoint (S.specialFiberComponentIdeal Z).subscheme) :=
    IsGenericPoint.eq hclos (S.closure_singleton_genericPoint_specialFiberComponent Z)
  rw [hpteq] at hdim
  exact (ringKrullDim_stalk_eq_one_iff_codimension_closureSingleton_eq_one _).mp hdim

/-- **Stacks Project, Tag 0C5Z (component clause).** Each irreducible component of the special
fibre of a regular model, taken with its reduced induced structure as a closed subscheme of the
model, is an effective Cartier divisor on the model.

It is an integral closed subscheme of codimension one, and every local ring of the regular
scheme `X` is factorial, so Tag 0AGA applies. -/
@[stacks 0C5Z "component_cartier"]
public theorem isEffectiveCartierDivisor_specialFiberComponent :
    IsEffectiveCartierDivisor (S.specialFiberComponentIdeal Z) := by
  let _ : IsLocallyNoetherian S.X := S.isLocallyNoetherian_X
  exact isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid
    (S.specialFiberComponentIdeal Z) (S.codimension_specialFiberComponent_eq_one Z)
    fun x _ => S.uniqueFactorizationMonoid_stalk x

/-! ### The multiplicities of the components: `X_k = ∑ mᵢ Cᵢ` -/

/-- The support of the ideal sheaf cutting out the special fibre is the image of the special
fibre in the model: the special fibre maps isomorphically onto that closed subscheme. -/
public theorem coe_support_specialFiberIdeal :
    ((S.specialFiberIdeal.support : Closeds S.X) : Set S.X) =
      Set.range S.specialFiberι.base := by
  have hsurj : Function.Surjective (asIso S.specialFiberι.toImage).hom.base :=
    (asIso S.specialFiberι.toImage).hom.homeomorph.surjective
  rw [← Scheme.IdealSheafData.range_subschemeι,
    show S.specialFiberι.base = S.specialFiberIdeal.subschemeι.base ∘
      (asIso S.specialFiberι.toImage).hom.base from
        funext fun w => (S.subschemeι_base_toImage_hom w).symm,
    Set.range_comp, hsurj.range_eq, Set.image_univ]


/-- The total space of a regular model is Noetherian: it is locally Noetherian, and it is
quasi-compact because it is quasi-compact over the affine scheme `Spec(R)`. -/
public instance isNoetherian_X : IsNoetherian S.X := by
  have : IsLocallyNoetherian S.X := S.isLocallyNoetherian_X
  have : CompactSpace S.X := QuasiCompact.compactSpace_of_compactSpace S.X_to_R
  exact ⟨⟩

/-- The special fibre of a regular model has finitely many irreducible components: it is
homeomorphic to a closed subset of the Noetherian space `X`. -/
public instance finite_irreducibleComponents_specialFiber :
    Finite (irreducibleComponents S.specialFiber) := by
  have : NoetherianSpace S.X := inferInstance
  have : NoetherianSpace S.specialFiber :=
    S.specialFiberι.isClosedEmbedding.isEmbedding.noetherianSpace
  exact NoetherianSpace.finite_irreducibleComponents.to_subtype

/-- The irreducible components of the special fibre, as a finite type. -/
public instance fintypeIrreducibleComponentsSpecialFiber :
    Fintype (irreducibleComponents S.specialFiber) :=
  Fintype.ofFinite _

/-- An irreducible component of the special fibre, with its reduced induced structure, as a
prime divisor of the model: an integral closed subscheme of codimension one. -/
public def specialFiberComponentPrimeDivisor (Z : irreducibleComponents S.specialFiber) :
    AlgebraicGeometry.PrimeDivisor S.X where
  idealSheaf := S.specialFiberComponentIdeal Z
  integral := inferInstance
  codimension_one := S.codimension_specialFiberComponent_eq_one Z

/-- The generic point of the prime divisor of a component is the image in `X` of the generic
point of the component. -/
public theorem genericPoint_specialFiberComponentPrimeDivisor
    (Z : irreducibleComponents S.specialFiber) :
    (S.specialFiberComponentPrimeDivisor Z).genericPoint =
      (S.specialFiberComponentIdeal Z).subschemeι
        (genericPoint (S.specialFiberComponentIdeal Z).subscheme) := rfl

/-- **The multiplicity `mᵢ` of an irreducible component `Cᵢ` of the special fibre in `X_k`**:
the length of the local ring `𝒪_{X_k, ξᵢ} = 𝒪_{X, ξᵢ}/ℐ_{X_k, ξᵢ}` of the special fibre at the
generic point `ξᵢ` of the component, the coefficient of `Cᵢ` in the Weil divisor of the
effective Cartier divisor `X_k`. -/
@[sga "7 I 3.2" "partial", sga "7 IX 12.1" "12.1.2"]
public def specialFiberMultiplicity (Z : irreducibleComponents S.specialFiber) : ℕ :=
  (effectiveCartierMultiplicity S.specialFiberIdeal (S.specialFiberComponentPrimeDivisor Z)).toNat

/-- The generic point of a component of the special fibre lies on no other component. -/
theorem genericPoint_specialFiberComponent_notMem_support
    {Z W : irreducibleComponents S.specialFiber}
    (h : Z ≠ W) :
    (S.specialFiberComponentPrimeDivisor W).genericPoint ∉
      (((S.specialFiberComponentIdeal Z).support : Closeds S.X) : Set S.X) := by
  intro hmem
  apply h
  rw [S.coe_support_specialFiberComponentIdeal Z] at hmem
  have hsub : S.specialFiberι.base '' (W.1 : Set S.specialFiber) ⊆
      S.specialFiberι.base '' (Z.1 : Set S.specialFiber) := by
    rw [← S.closure_singleton_genericPoint_specialFiberComponent W]
    exact (closure_minimal (Set.singleton_subset_iff.2 hmem)
      (S.isClosed_image_specialFiberComponent Z))
  have hWZ : (W.1 : Set S.specialFiber) ⊆ Z.1 :=
    (Set.image_subset_image_iff S.specialFiberι.isClosedEmbedding.injective).1 hsub
  exact (Subtype.ext (hWZ.antisymm (W.2.2 Z.2.1 hWZ))).symm

/-- The stalk of a finite product `∏ Cⱼ ^ aⱼ` of component ideals at the generic point of the
component `Cᵢ` is the stalk of the single factor `Cᵢ ^ aᵢ`: the other components do not pass
through that point. -/
theorem stalk_prod_specialFiberComponentIdeal_pow
    (s : Finset (irreducibleComponents S.specialFiber))
    (a : irreducibleComponents S.specialFiber → ℕ) (W : irreducibleComponents S.specialFiber) :
    IdealSheafData.stalk (∏ Z ∈ s, S.specialFiberComponentIdeal Z ^ a Z)
        (S.specialFiberComponentPrimeDivisor W).genericPoint =
      if W ∈ s then
        IdealSheafData.stalk (S.specialFiberComponentIdeal W ^ a W)
          (S.specialFiberComponentPrimeDivisor W).genericPoint
      else ⊤ := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.notMem_empty, ite_false]
      rw [show (1 : S.X.IdealSheafData) = ⊤ from Scheme.IdealSheafData.one_eq_top,
        IdealSheafData.stalk_eq_top_iff_notMem_support]
      exact fun h => Set.notMem_empty _ h
  | cons Z s hZ ih =>
      rw [Finset.prod_cons, IdealSheafData.stalk_mul, ih]
      by_cases hZW : Z = W
      · subst hZW
        simp [hZ]
      · have htop : IdealSheafData.stalk (S.specialFiberComponentIdeal Z ^ a Z)
            (S.specialFiberComponentPrimeDivisor W).genericPoint = ⊤ := by
          rw [IdealSheafData.stalk_pow,
            (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
              (S.genericPoint_specialFiberComponent_notMem_support hZW), Ideal.top_pow]
        have hmem : W ∈ Finset.cons Z s hZ ↔ W ∈ s := by
          simp [Ne.symm hZW]
        rw [htop, Ideal.top_mul]
        simp only [hmem]

/-- At the generic point of a component, the stalk of the component's ideal is the maximal
ideal of the local ring, which is a discrete valuation ring. -/
theorem stalk_specialFiberComponentIdeal_genericPoint (W : irreducibleComponents S.specialFiber) :
    IdealSheafData.stalk (S.specialFiberComponentIdeal W)
        (S.specialFiberComponentPrimeDivisor W).genericPoint =
      IsLocalRing.maximalIdeal
        (S.X.presheaf.stalk (S.specialFiberComponentPrimeDivisor W).genericPoint) :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.Quotient.maximal_of_isField _
      (isField_quotient_stalk_subschemeι_genericPoint (D := S.specialFiberComponentIdeal W)))

/-- The order at the generic point of a component `Cᵢ` of a finite product `∏ Cⱼ ^ aⱼ` of
component ideals is the exponent `aᵢ` (or `0` if `Cᵢ` does not occur). -/
theorem effectiveCartierMultiplicity_prod_specialFiberComponentIdeal_pow
    (s : Finset (irreducibleComponents S.specialFiber))
    (a : irreducibleComponents S.specialFiber → ℕ) (W : irreducibleComponents S.specialFiber) :
    effectiveCartierMultiplicity (∏ Z ∈ s, S.specialFiberComponentIdeal Z ^ a Z)
        (S.specialFiberComponentPrimeDivisor W) = if W ∈ s then (a W : ℤ) else 0 := by
  have : IsLocallyNoetherian S.X := S.isLocallyNoetherian_X
  rw [effectiveCartierMultiplicity, S.stalk_prod_specialFiberComponentIdeal_pow s a W]
  by_cases hW : W ∈ s
  · obtain ⟨hdom, hdvr⟩ := isDiscreteValuationRing_stalk_genericPoint
      (S.specialFiberComponentIdeal W) (S.isEffectiveCartierDivisor_specialFiberComponent W)
    rw [ite_eq_left hW, ite_eq_left hW, IdealSheafData.stalk_pow,
      S.stalk_specialFiberComponentIdeal_genericPoint W]
    have : IsDomain (S.X.presheaf.stalk (S.specialFiberComponentPrimeDivisor W).genericPoint) :=
      hdom
    have : IsDiscreteValuationRing
        (S.X.presheaf.stalk (S.specialFiberComponentPrimeDivisor W).genericPoint) := hdvr
    rw [IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    simp
  · rw [ite_eq_right hW, ite_eq_right hW]
    simp

/-- **Stacks Project, Tag 0C5Z, part (3).** The special fibre of a regular model is the sum
`X_k = ∑ mᵢ Cᵢ` of its irreducible components `Cᵢ`, as effective Cartier divisors, with `mᵢ`
the multiplicity of `Cᵢ` in `X_k`. Divisor sums are written multiplicatively.

The components are integral effective Cartier divisors covering the special fibre, so
[Stacks, Tag 0BCP] writes `X_k` as some nonnegative combination `∑ aᵢ Cᵢ`; reading off the order
at the generic point of each `Cᵢ`, which is a discrete valuation ring, gives `aᵢ = mᵢ`. -/
@[stacks 0C5Z "part (3): X_k = ∑ mᵢ Cᵢ with mᵢ the multiplicity of Cᵢ in X_k"]
public theorem specialFiberIdeal_eq_prod :
    S.specialFiberIdeal =
      ∏ Z, S.specialFiberComponentIdeal Z ^ S.specialFiberMultiplicity Z := by
  classical
  obtain ⟨a, ha⟩ := exists_finsupp_eq_prod_of_support_cover S.specialFiberIdeal
    (isEffectiveCartierDivisor_specialFiber S.residueEquiv S.X_to_R)
    (fun Z => S.specialFiberComponentIdeal Z)
    (fun Z => ⟨inferInstance, S.isEffectiveCartierDivisor_specialFiberComponent Z⟩)
    (by
      intro x hx
      have hx' : x ∈ (((S.specialFiberIdeal.support : Closeds S.X) : Set S.X)) := hx
      rw [S.coe_support_specialFiberIdeal] at hx'
      obtain ⟨y, rfl⟩ := hx'
      obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
        ({y} : Set S.specialFiber) isIrreducible_singleton
      refine ⟨⟨Z, hZ⟩, ?_⟩
      show S.specialFiberι.base y ∈
        (((S.specialFiberComponentIdeal ⟨Z, hZ⟩).support : Closeds S.X) : Set S.X)
      rw [S.coe_support_specialFiberComponentIdeal]
      exact ⟨y, hyZ rfl, rfl⟩)
  have hprod : (a.prod fun Z n => S.specialFiberComponentIdeal Z ^ n) =
      ∏ Z, S.specialFiberComponentIdeal Z ^ a Z :=
    Finsupp.prod_fintype _ _ fun _ => pow_zero _
  have hm : ∀ W, S.specialFiberMultiplicity W = a W := by
    intro W
    rw [specialFiberMultiplicity, ha, hprod,
      S.effectiveCartierMultiplicity_prod_specialFiberComponentIdeal_pow, ite_eq_left
        (Finset.mem_univ W)]
    simp
  rw [ha, hprod]
  exact Finset.prod_congr rfl fun W _ => by rw [hm W]

/-- The stalk of the special fibre at the generic point of a component `Cᵢ` is the `mᵢ`-th power
of the maximal ideal of the discrete valuation ring `𝒪_{X, ξᵢ}`. -/
public theorem stalk_specialFiberIdeal_genericPoint (W : irreducibleComponents S.specialFiber) :
    IdealSheafData.stalk S.specialFiberIdeal
        (S.specialFiberComponentPrimeDivisor W).genericPoint =
      IsLocalRing.maximalIdeal
        (S.X.presheaf.stalk (S.specialFiberComponentPrimeDivisor W).genericPoint) ^
          S.specialFiberMultiplicity W := by
  conv_lhs => rw [S.specialFiberIdeal_eq_prod]
  rw [S.stalk_prod_specialFiberComponentIdeal_pow, ite_eq_left (Finset.mem_univ W),
    IdealSheafData.stalk_pow, S.stalk_specialFiberComponentIdeal_genericPoint W]

/-- **Every multiplicity is positive**, `mᵢ ≥ 1`: the generic point of `Cᵢ` lies on `X_k`, so the
stalk of `X_k` there is a proper ideal, which `𝔪⁰` is not. -/
public theorem specialFiberMultiplicity_pos (W : irreducibleComponents S.specialFiber) :
    0 < S.specialFiberMultiplicity W := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have hstalk := S.stalk_specialFiberIdeal_genericPoint W
  rw [h0, pow_zero, Ideal.one_eq_top,
    IdealSheafData.stalk_eq_top_iff_notMem_support] at hstalk
  apply hstalk
  rw [← SetLike.mem_coe, S.coe_support_specialFiberIdeal]
  have hmem : (S.specialFiberComponentPrimeDivisor W).genericPoint ∈
      S.specialFiberι.base '' (W.1 : Set S.specialFiber) := by
    rw [← S.closure_singleton_genericPoint_specialFiberComponent W]
    exact subset_closure rfl
  obtain ⟨y, -, hy⟩ := hmem
  exact ⟨y, hy⟩

end RegularModelSituation

end Stacks.Models

end
