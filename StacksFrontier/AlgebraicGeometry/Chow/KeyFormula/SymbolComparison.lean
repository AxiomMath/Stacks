module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.ResidueFunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.OutsideFamily
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureSummandIdentity

/-!
# The summand of the local reciprocity law and the tame symbol of the situation

At a point `x` of an integral, locally Noetherian scheme `X` the local reciprocity law
Stacks 0EAX is indexed by the height-one primes `𝔮` of `A = 𝒪_{X, x}`, and its summand at `𝔮` is
`ord_{A/𝔮}(∂_{A_𝔮}(f, g))`. The key formula Stacks 0AYC speaks instead of the prime divisor
`Z = closure {z}` cut out by `𝔮`, of the tame symbol `∂_{𝒪_{X, z}}(f, g)` of Stacks 0EAH at its
generic point `z`, and of the order of vanishing of that symbol on `Z` at `x`. This file compares
the two.

The symbol comparison is a transport along the identification of `𝒪_{X, z}` with `A_𝔮`: the local
ring at the point cut out by `𝔮` is the localization `A_𝔮`
(`Stacks.Chow.stalkLocalizationAtPrimeEquiv`), the two structure maps into `Frac(A) = R(X)` agree
because both extend `A → Frac(A)` over a localization of `A`, and the tame symbol of Stacks 02Q1
is transported by such a compatible pair (`Stacks.Chow.map_tameSymbol_ringEquiv`, whose proof is
the uniqueness `Stacks.Chow.eq_tameSymbol` of the symbol). Both symbols at issue are
`Stacks.Chow.tameSymbolOfKrullDimOne`, which is a term of `AlgebraicGeometry.TameSymbol` for a
local domain (`Stacks.Chow.tameSymbolOfKrullDimOneDomain`), so the uniqueness applies to each.

The order comparison is a transport along the identification of `A ⧸ 𝔮` with the local ring
`𝒪_{Z, x}` (`Stacks.Chow.quotStalkEquivIntermediatePointStalk`), compatible with the
identification of their fraction fields `κ(𝔮) ≅ κ(z) ≅ R(Z)`;
`Stacks.Chow.ordFrac_ringEquiv` then carries one order of vanishing to the other. For the
scheme-level order of vanishing to be the right quantity, `x` has to have codimension one on `Z`,
which it does: when `A` is two-dimensional, `z` specializes immediately to `x`, and immediacy
transfers from `X` to `Z`.

The two comparisons combine into the summand identity: the summand of Stacks 0EAX at the
height-one prime cut out by a member `Z_i` of the family of Stacks 0AYB is the coefficient at `x`
of the pushforward to `X` of the principal divisor of `∂_{B_i}(f_i, g_i)` on `Z_i`, which is one
summand of `Stacks.Chow.KeyFormulaData.tameSymbolCoeff`.

## Main definitions

* `Stacks.Chow.heightOnePrimeIdeal` — a height-one prime in the spelling
  `{q : Ideal A // q.IsPrime ∧ q.height = 1}` of the height-one correspondence.
* `Stacks.Chow.localizationEquivStalkOfHeightOnePrime` — the identification `A_𝔮 ≅ 𝒪_{X, z}`.
* `Stacks.Chow.closurePointOfHeightOnePrime` — the point `x`, read as a point of `Z`.
* `Stacks.Chow.quotEquivStalkClosurePointOfHeightOnePrime` — the identification
  `A ⧸ 𝔮 ≅ 𝒪_{Z, x}`.

## Main results

* `Stacks.Chow.functionFieldEquivFractionRing_algebraMap_localizationEquivStalk` — the
  identification `A_𝔮 ≅ 𝒪_{X, z}` is compatible with the two structure maps into
  `Frac(A) = R(X)`.
* `Stacks.Chow.map_tameSymbolAtCoheightOne_eq_tameSymbolOfKrullDimOne` — **the symbol
  comparison**: the tame symbol of `𝒪_{X, z}` on `R(X)^*`, read in the residue field of `A_𝔮`, is
  the tame symbol of `A_𝔮` on `Frac(A)^*`.
* `Stacks.Chow.fracTameSymbolOrderAt_canonical_eq_heightOneOrd_tameSymbolOfKrullDimOne` — the
  summand of Stacks 0EAX, with its symbol written as `Stacks.Chow.tameSymbolOfKrullDimOne`.
* `Stacks.Chow.coheight_closurePointOfHeightOnePrime` — `x` has codimension one on `Z`.
* `Stacks.Chow.heightOneOrd_eq_ord_integralComponentAt` — **the order comparison**: the order
  along `A ⧸ 𝔮` of a unit of `κ(𝔮)` is the order of vanishing at `x` of the corresponding
  rational function on `Z`.
* `Stacks.Chow.fracTameSymbolOrderAt_canonical_eq_ord_tameSymbolAtCoheightOne` — the two
  comparisons combined, for a pair of rational functions on `X`.
* `Stacks.Chow.KeyFormulaSituation.fracTameSymbolOrderAt_component_eq_principalDivisorPushforward`
  — **the summand identity for the situation of Stacks 0AYB**.

## References

* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-! ### A height-one prime in the spelling of the height-one correspondence -/

/-- A height-one prime of `A`, as a prime ideal of height one. This is the index type of
`Stacks.Chow.heightOnePrimeEquivIntermediatePoint` and of the identifications attached to it. -/
def heightOnePrimeIdeal {A : Type u} [CommRing A] (𝔮 : HeightOnePrime A) :
    {q : Ideal A // q.IsPrime ∧ q.height = 1} :=
  ⟨𝔮.1.asIdeal, 𝔮.1.isPrime, 𝔮.2⟩

variable {X : Scheme.{u}}

/-- The point cut out by a height-one prime of `𝒪_{X, x}` is the point the height-one
correspondence attaches to it. -/
theorem intermediatePointOfHeightOnePrime_heightOnePrimeIdeal {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) :
    intermediatePointOfHeightOnePrime x (heightOnePrimeIdeal 𝔮) = pointOfHeightOnePrime 𝔮 :=
  rfl

/-! ### The local ring at the point cut out by a height-one prime -/

/-- **The localization `A_𝔮` is the local ring at the point `𝔮` cuts out.** This is
`Stacks.Chow.stalkLocalizationAtPrimeEquiv` at the point `Stacks.Chow.pointOfHeightOnePrime`. -/
def localizationEquivStalkOfHeightOnePrime {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) :
    Localization.AtPrime 𝔮.1.asIdeal ≃+* X.presheaf.stalk (pointOfHeightOnePrime 𝔮) :=
  stalkLocalizationAtPrimeEquiv x (heightOnePrimeIdeal 𝔮)

/-- The identification carries the image of a germ at `x` to its specialization to a germ at the
point cut out by `𝔮`. -/
theorem localizationEquivStalkOfHeightOnePrime_algebraMap {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) (r : X.presheaf.stalk x) :
    localizationEquivStalkOfHeightOnePrime 𝔮
        (algebraMap (X.presheaf.stalk x) (Localization.AtPrime 𝔮.1.asIdeal) r) =
      (X.presheaf.stalkSpecializes (pointOfHeightOnePrime_specializes 𝔮)).hom r :=
  stalkLocalizationAtPrimeEquiv_algebraMap x (heightOnePrimeIdeal 𝔮) r

section Compatibility

variable [IsIntegral X]

/-- **The identification `A_𝔮 ≅ 𝒪_{X, z}` is compatible with the two structure maps into
`Frac(A) = R(X)`.** Both are maps out of a localization of `A` extending `A → Frac(A)`, so they
agree; this is the compatibility that the transport of the tame symbol of Stacks 02Q1 consumes. -/
theorem functionFieldEquivFractionRing_algebraMap_localizationEquivStalk {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) (w : Localization.AtPrime 𝔮.1.asIdeal) :
    functionFieldEquivFractionRing x
        (algebraMap (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) X.functionField
          (localizationEquivStalkOfHeightOnePrime 𝔮 w)) =
      algebraMap (Localization.AtPrime 𝔮.1.asIdeal) (FractionRing (X.presheaf.stalk x)) w := by
  have hspec : pointOfHeightOnePrime 𝔮 ⤳ x := pointOfHeightOnePrime_specializes 𝔮
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) :=
    (X.presheaf.stalkSpecializes hspec).hom.toAlgebra
  have hcomp : ∀ r : X.presheaf.stalk x,
      functionFieldEquivFractionRing x
          (algebraMap (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) X.functionField
            (localizationEquivStalkOfHeightOnePrime 𝔮
              (algebraMap (X.presheaf.stalk x) (Localization.AtPrime 𝔮.1.asIdeal) r))) =
        algebraMap (Localization.AtPrime 𝔮.1.asIdeal) (FractionRing (X.presheaf.stalk x))
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime 𝔮.1.asIdeal) r) := by
    intro r
    have h1 : localizationEquivStalkOfHeightOnePrime 𝔮
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime 𝔮.1.asIdeal) r) =
        algebraMap (X.presheaf.stalk x) (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) r :=
      localizationEquivStalkOfHeightOnePrime_algebraMap 𝔮 r
    rw [h1, algebraMap_stalk_functionField_algebraMap hspec r, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  have key : ((functionFieldEquivFractionRing x).toRingEquiv.toRingHom.comp
        ((algebraMap (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) X.functionField).comp
          (localizationEquivStalkOfHeightOnePrime 𝔮).toRingHom)) =
      algebraMap (Localization.AtPrime 𝔮.1.asIdeal) (FractionRing (X.presheaf.stalk x)) :=
    IsLocalization.ringHom_ext 𝔮.1.asIdeal.primeCompl (RingHom.ext hcomp)
  exact RingHom.congr_fun key w

end Compatibility

/-! ### The symbol comparison -/

section SymbolComparison

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- **The tame symbol at the point cut out by a height-one prime is the tame symbol of the
localization.** Let `x` be a point of an integral, locally Noetherian scheme, let `𝔮` be a
height-one prime of `A = 𝒪_{X, x}` and let `z` be the point of `X` it cuts out, a point of
codimension one. The tame symbol `∂_{𝒪_{X, z}} : R(X)^* × R(X)^* → κ(z)^*` of Stacks 0EAH and the
tame symbol `∂_{A_𝔮} : Frac(A)^* × Frac(A)^* → κ(𝔮)^*` correspond under the identification
`𝒪_{X, z} ≅ A_𝔮` and the identification `R(X) ≅ Frac(A)` of their fraction fields. -/
theorem map_tameSymbolAtCoheightOne_eq_tameSymbolOfKrullDimOne {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) (f g : X.functionFieldˣ) :
    Units.map (IsLocalRing.ResidueField.mapEquiv
          (localizationEquivStalkOfHeightOnePrime 𝔮).symm).toMonoidHom
        (tameSymbolAtCoheightOne (coheight_pointOfHeightOnePrime 𝔮) f g) =
      tameSymbolOfKrullDimOne (ringKrullDim_localization_heightOnePrime 𝔮)
        (FractionRing (X.presheaf.stalk x))
        (Units.map ((functionFieldEquivFractionRing x).toRingEquiv :
          X.functionField →+* FractionRing (X.presheaf.stalk x)).toMonoidHom f)
        (Units.map ((functionFieldEquivFractionRing x).toRingEquiv :
          X.functionField →+* FractionRing (X.presheaf.stalk x)).toMonoidHom g) := by
  have hA : ringKrullDim (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) = 1 :=
    ringKrullDim_stalk_eq_one_of_coheight_eq_one (coheight_pointOfHeightOnePrime 𝔮)
  have hB : ringKrullDim (Localization.AtPrime 𝔮.1.asIdeal) = 1 :=
    ringKrullDim_localization_heightOnePrime 𝔮
  have key := map_tameSymbol_ringEquiv (localizationEquivStalkOfHeightOnePrime 𝔮).symm
    (functionFieldEquivFractionRing x).toRingEquiv
    (fun a => by
      rw [← functionFieldEquivFractionRing_algebraMap_localizationEquivStalk 𝔮
        ((localizationEquivStalkOfHeightOnePrime 𝔮).symm a), RingEquiv.apply_symm_apply]
      rfl)
    hA hB f g
  exact (congrArg _ (eq_tameSymbol hA (tameSymbolOfKrullDimOneDomain hA) f g)).trans
    (key.trans (eq_tameSymbol hB (tameSymbolOfKrullDimOneDomain hB) _ _).symm)

/-- The summand of Stacks 0EAX at a height-one prime, with the tame symbol written as
`Stacks.Chow.tameSymbolOfKrullDimOne`: the canonical symbol of Stacks 0EAH on `A_𝔮` extended to
`Frac(A)` is that symbol. -/
theorem fracTameSymbolOrderAt_canonical_eq_heightOneOrd_tameSymbolOfKrullDimOne {x : X}
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (𝔮 : HeightOnePrime (X.presheaf.stalk x))
    (F G : (FractionRing (X.presheaf.stalk x))ˣ) :
    fracTameSymbolOrderAt hdim 𝔮 (canonicalHeightOneSymbol 𝔮) F G =
      heightOneOrd hdim 𝔮
        (tameSymbolOfKrullDimOne (ringKrullDim_localization_heightOnePrime 𝔮)
          (FractionRing (X.presheaf.stalk x)) F G) :=
  rfl

end SymbolComparison

/-! ### The order of vanishing across the correspondence -/

section OrderComparison

/-- The point `x`, read as a point of the prime divisor `Z = closure {z}` cut out by a height-one
prime `𝔮` of `A = 𝒪_{X, x}`. -/
def closurePointOfHeightOnePrime {x : X} (𝔮 : HeightOnePrime (X.presheaf.stalk x)) :
    (integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme :=
  intermediatePointClosurePoint x (heightOnePrimeIdeal 𝔮)

/-- The inclusion of the prime divisor cut out by `𝔮` carries
`Stacks.Chow.closurePointOfHeightOnePrime 𝔮` back to `x`. -/
@[simp] theorem subschemeι_closurePointOfHeightOnePrime {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) :
    (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι
      (closurePointOfHeightOnePrime 𝔮) = x :=
  rfl

/-- **The quotient `A ⧸ 𝔮` is the local ring at `x` of the prime divisor cut out by `𝔮`.** This is
`Stacks.Chow.quotStalkEquivIntermediatePointStalk` at the point
`Stacks.Chow.pointOfHeightOnePrime`. -/
def quotEquivStalkClosurePointOfHeightOnePrime {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) :
    (X.presheaf.stalk x ⧸ 𝔮.1.asIdeal) ≃+*
      (integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme.presheaf.stalk
        (closurePointOfHeightOnePrime 𝔮) :=
  quotStalkEquivIntermediatePointStalk x (heightOnePrimeIdeal 𝔮)

/-- The identification carries the class of a germ at `x` to the restriction of that germ to the
prime divisor. -/
theorem quotEquivStalkClosurePointOfHeightOnePrime_mk {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) (r : X.presheaf.stalk x) :
    quotEquivStalkClosurePointOfHeightOnePrime 𝔮 (Ideal.Quotient.mk 𝔮.1.asIdeal r) =
      ((integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι.stalkMap
        (closurePointOfHeightOnePrime 𝔮)).hom r :=
  rfl

/-- The function field of the closure of a point, identified with the residue field there, is the
identification `Stacks.Chow.functionFieldIntegralComponentEquiv`. -/
theorem pointClosureFunctionFieldEquiv_eq_functionFieldIntegralComponentEquiv (z : X)
    (f : (integralComponentAt z).subscheme.functionField) :
    pointClosureFunctionFieldEquiv z f = functionFieldIntegralComponentEquiv z f :=
  rfl

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The integral component at a point of a locally Noetherian scheme is locally Noetherian, its
inclusion being locally of finite type. -/
local instance isLocallyNoetherian_integralComponentSubscheme (z : X) :
    IsLocallyNoetherian (integralComponentAt z).subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt z).subschemeι

omit [IsLocallyNoetherian X] in
/-- **`x` has codimension one on the prime divisor cut out by a height-one prime of `𝒪_{X, x}`.**
When `𝒪_{X, x}` is two-dimensional the point `z` cut out by `𝔮` specializes immediately to `x`,
and immediacy transfers to the closure of `z`, whose structural morphism is injective on points
and both preserves and reflects specialization. -/
theorem coheight_closurePointOfHeightOnePrime {x : X}
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) :
    coheight (closurePointOfHeightOnePrime 𝔮) = 1 := by
  have himm : IsImmediateSpecialization (pointOfHeightOnePrime 𝔮) x :=
    isImmediateSpecialization_intermediatePointOfHeightOnePrime hdim (heightOnePrimeIdeal 𝔮)
  have hgen : (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι
        (genericPoint (integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme) =
      pointOfHeightOnePrime 𝔮 :=
    genericPointOf_integralComponentAt (pointOfHeightOnePrime 𝔮)
  have hinj : ∀ a b : (integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme,
      (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι a =
        (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι b → a = b :=
    fun _ _ h => Subtype.ext h
  refine (coheight_eq_one_iff_isImmediateSpecialization_genericPoint _).mpr
    ⟨genericPoint_specializes _, ?_, ?_⟩
  · intro heq
    refine himm.2.1 ?_
    have h : (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι
          (genericPoint (integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme) =
        (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι
          (closurePointOfHeightOnePrime 𝔮) :=
      congrArg _ heq
    rw [hgen] at h
    exact h
  · intro w hηw hwt
    have h1 : pointOfHeightOnePrime 𝔮 ⤳
        (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι w := by
      have h := (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι.base.hom.map_specializes
        hηw
      rwa [hgen] at h
    have h2 : (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι w ⤳ x :=
      (integralComponentAt (pointOfHeightOnePrime 𝔮)).subschemeι.base.hom.map_specializes hwt
    rcases himm.2.2 _ h1 h2 with h | h
    · exact Or.inl (hinj _ _ (h.trans hgen.symm))
    · exact Or.inr (hinj _ _ h)

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- **The two identifications of `A ⧸ 𝔮` with the local ring at `x` of the prime divisor cut out
by `𝔮` are compatible with the identifications of their fraction fields.** This is the square
that `Stacks.Chow.ordFrac_ringEquiv` consumes; checked on the class of a germ at `x`, where both
sides are the residue at `z` of that germ specialized to `z`. -/
theorem functionFieldIntegralComponentEquiv_symm_residueField_mapEquiv_algebraMap {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) (r : X.presheaf.stalk x ⧸ 𝔮.1.asIdeal) :
    (functionFieldIntegralComponentEquiv (pointOfHeightOnePrime 𝔮)).symm
        (IsLocalRing.ResidueField.mapEquiv (localizationEquivStalkOfHeightOnePrime 𝔮)
          (algebraMap (X.presheaf.stalk x ⧸ 𝔮.1.asIdeal)
            (IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal)) r)) =
      algebraMap ((integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme.presheaf.stalk
          (closurePointOfHeightOnePrime 𝔮))
        ((integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme.functionField)
        (quotEquivStalkClosurePointOfHeightOnePrime 𝔮 r) := by
  obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
  have h1 : IsLocalRing.ResidueField.mapEquiv (localizationEquivStalkOfHeightOnePrime 𝔮)
        (algebraMap (X.presheaf.stalk x ⧸ 𝔮.1.asIdeal)
          (IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal))
          (Ideal.Quotient.mk 𝔮.1.asIdeal r')) =
      IsLocalRing.residue (X.presheaf.stalk (pointOfHeightOnePrime 𝔮))
        ((X.presheaf.stalkSpecializes (pointOfHeightOnePrime_specializes 𝔮)).hom r') :=
    residueField_mapEquiv_stalkLocalizationAtPrimeEquiv x (heightOnePrimeIdeal 𝔮) r'
  have h2 := pointClosureFunctionFieldEquiv_algebraMap_stalkMap (pointOfHeightOnePrime 𝔮)
    (closurePointOfHeightOnePrime 𝔮) (pointOfHeightOnePrime_specializes 𝔮) r'
  rw [RingEquiv.symm_apply_eq, h1, quotEquivStalkClosurePointOfHeightOnePrime_mk,
    ← pointClosureFunctionFieldEquiv_eq_functionFieldIntegralComponentEquiv, h2]
  rfl

/-- **The order of a residue-field unit along `A ⧸ 𝔮` is its order of vanishing on the prime
divisor cut out by `𝔮`.** Let `𝔮` be a height-one prime of a two-dimensional `A = 𝒪_{X, x}`, let
`z` be the point of `X` it cuts out and let `Z = closure {z}` be the prime divisor spanned by `z`.
A unit `d` of the residue field `κ(𝔮)` is a rational function on `Z` through the identifications
`κ(𝔮) ≅ κ(z) ≅ R(Z)`, and the order of vanishing of that rational function at `x` is the order of
`d` along `A ⧸ 𝔮`.

The rings `A ⧸ 𝔮` and `𝒪_{Z, x}` are identified compatibly with their fraction fields, so
`Stacks.Chow.ordFrac_ringEquiv` carries one order of vanishing to the other. -/
theorem heightOneOrd_eq_ord_integralComponentAt {x : X}
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (𝔮 : HeightOnePrime (X.presheaf.stalk x))
    (d : (IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal))ˣ) :
    heightOneOrd hdim 𝔮 d =
      (integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme.ord
        ((functionFieldIntegralComponentEquiv (pointOfHeightOnePrime 𝔮)).symm
          (IsLocalRing.ResidueField.mapEquiv (localizationEquivStalkOfHeightOnePrime 𝔮)
            (d : IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal))))
        (closurePointOfHeightOnePrime 𝔮) := by
  have ht : coheight (closurePointOfHeightOnePrime 𝔮) = 1 :=
    coheight_closurePointOfHeightOnePrime hdim 𝔮
  let _ : Ring.KrullDimLE 1 (X.presheaf.stalk x ⧸ 𝔮.1.asIdeal) :=
    krullDimLE_quotient_of_height_eq_one hdim 𝔮.1.asIdeal 𝔮.2
  let _ : Ring.KrullDimLE 1
      ((integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme.presheaf.stalk
        (closurePointOfHeightOnePrime 𝔮)) := krullDimLE_of_coheight_le ht.le
  have hord : Ring.ordFrac
        ((integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme.presheaf.stalk
          (closurePointOfHeightOnePrime 𝔮))
        ((functionFieldIntegralComponentEquiv (pointOfHeightOnePrime 𝔮)).symm
          (IsLocalRing.ResidueField.mapEquiv (localizationEquivStalkOfHeightOnePrime 𝔮)
            (d : IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal)))) =
      Ring.ordFrac (X.presheaf.stalk x ⧸ 𝔮.1.asIdeal)
        (d : IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal)) := by
    rw [← RingEquiv.trans_apply]
    exact ordFrac_ringEquiv (quotEquivStalkClosurePointOfHeightOnePrime 𝔮)
      ((IsLocalRing.ResidueField.mapEquiv (localizationEquivStalkOfHeightOnePrime 𝔮)).trans
        (functionFieldIntegralComponentEquiv (pointOfHeightOnePrime 𝔮)).symm)
      (fun r => by
        rw [RingEquiv.trans_apply]
        exact functionFieldIntegralComponentEquiv_symm_residueField_mapEquiv_algebraMap 𝔮 r)
      (d : IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal))
  have hne : Ring.ordFrac (X.presheaf.stalk x ⧸ 𝔮.1.asIdeal)
      (d : IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal)) ≠ 0 :=
    ((Units.isUnit d).map (Ring.ordFrac (X.presheaf.stalk x ⧸ 𝔮.1.asIdeal))).ne_zero
  have hne' : Ring.ordFrac
      ((integralComponentAt (pointOfHeightOnePrime 𝔮)).subscheme.presheaf.stalk
        (closurePointOfHeightOnePrime 𝔮))
      ((functionFieldIntegralComponentEquiv (pointOfHeightOnePrime 𝔮)).symm
        (IsLocalRing.ResidueField.mapEquiv (localizationEquivStalkOfHeightOnePrime 𝔮)
          (d : IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal)))) ≠ 0 :=
    hord ▸ hne
  have htoAdd : Multiplicative.toAdd (WithZero.unzero hne') =
      Multiplicative.toAdd (WithZero.unzero hne) :=
    congrArg Multiplicative.toAdd
      (WithZero.coe_inj.mp (by simp only [WithZero.coe_unzero]; exact hord))
  exact ((ord_eq_toAdd_unzero_ordFrac ht hne').trans htoAdd).symm

/-! ### The summand of the key formula at a member of the family -/

/-- **The summand of Stacks 0EAX at a height-one prime is an order of vanishing of the tame symbol
on the prime divisor the prime cuts out.** Let `𝔮` be a height-one prime of a two-dimensional
`A = 𝒪_{X, x}` cutting out the point `z`, and let `f`, `g` be nonzero rational functions on `X`.
The summand `ord_{A/𝔮}(∂_{A_𝔮}(f, g))` of Stacks 0EAX is the order of vanishing at `x`, on the
prime divisor `Z = closure {z}`, of the tame symbol `∂_{𝒪_{X, z}}(f, g)` read as a rational
function on `Z`.

This joins the symbol comparison to the order identification. -/
theorem fracTameSymbolOrderAt_canonical_eq_ord_tameSymbolAtCoheightOne {x : X}
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) {z : X}
    (hz : pointOfHeightOnePrime 𝔮 = z) (hz1 : coheight z = 1)
    (hmem : x ∈ closure ({z} : Set X)) (f g : X.functionFieldˣ) :
    fracTameSymbolOrderAt hdim 𝔮 (canonicalHeightOneSymbol 𝔮)
        (Units.map ((functionFieldEquivFractionRing x).toRingEquiv :
          X.functionField →+* FractionRing (X.presheaf.stalk x)).toMonoidHom f)
        (Units.map ((functionFieldEquivFractionRing x).toRingEquiv :
          X.functionField →+* FractionRing (X.presheaf.stalk x)).toMonoidHom g) =
      (integralComponentAt z).subscheme.ord
        ((functionFieldIntegralComponentEquiv z).symm (tameSymbolAtCoheightOne hz1 f g))
        (pointClosurePoint z hmem) := by
  subst hz
  have hz1' : hz1 = coheight_pointOfHeightOnePrime 𝔮 := rfl
  subst hz1'
  have hval : IsLocalRing.ResidueField.mapEquiv (localizationEquivStalkOfHeightOnePrime 𝔮)
        ((Units.map (IsLocalRing.ResidueField.mapEquiv
            (localizationEquivStalkOfHeightOnePrime 𝔮).symm).toMonoidHom
            (tameSymbolAtCoheightOne (coheight_pointOfHeightOnePrime 𝔮) f g) :
          IsLocalRing.ResidueField (Localization.AtPrime 𝔮.1.asIdeal))) =
      (tameSymbolAtCoheightOne (coheight_pointOfHeightOnePrime 𝔮) f g :
        IsLocalRing.ResidueField (X.presheaf.stalk (pointOfHeightOnePrime 𝔮))) := by
    rw [Units.coe_map, ← IsLocalRing.ResidueField.mapEquiv.symm]
    exact RingEquiv.apply_symm_apply _ _
  rw [fracTameSymbolOrderAt_canonical_eq_heightOneOrd_tameSymbolOfKrullDimOne,
    ← map_tameSymbolAtCoheightOne_eq_tameSymbolOfKrullDimOne,
    heightOneOrd_eq_ord_integralComponentAt, hval]
  rfl

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The tame symbol, read as a rational function on `Z_ξ` in the `Stacks.Chow.rationalFunctions`
spelling that `Stacks.Chow.KeyFormulaData` uses, is the one read through
`Stacks.Chow.functionFieldIntegralComponentEquiv`. -/
theorem rationalFunctionsEquivFunctionField_rationalFunctionsUnitsIntegralComponentEquiv_symm
    (z : X) (S : (IsLocalRing.ResidueField (X.presheaf.stalk z))ˣ) :
    (rationalFunctionsEquivFunctionField (integralComponentAt z).subscheme).1
        ((rationalFunctionsUnitsIntegralComponentEquiv z).symm S :
          rationalFunctions (integralComponentAt z).subscheme) =
      (functionFieldIntegralComponentEquiv z).symm
        (S : IsLocalRing.ResidueField (X.presheaf.stalk z)) :=
  rfl

namespace KeyFormulaSituation

variable {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N) (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- **The summand of Stacks 0EAX at a member of the family is the summand of the right hand side
of the key formula.** Let `x` be a point of `X` at which `A = 𝒪_{X, x}` is two-dimensional and let
`Z_i` be a member of the family of Stacks 0AYB whose generic point `ξ_i` specializes to `x`. The
summand `ord_{A/𝔮_i}(∂_{A_{𝔮_i}}(f_i, g_i))` of Stacks 0EAX at the height-one prime `𝔮_i` cut out
by `Z_i` is the coefficient at `x` of the pushforward to `X` of the principal divisor of the tame
symbol `∂_{B_i}(f_i, g_i)` on `Z_i`.

This is the `i`-th summand of `Stacks.Chow.KeyFormulaData.tameSymbolCoeff` for the data
`Stacks.Chow.KeyFormulaSituation.toKeyFormulaData`, so it is the identification of one summand of
the right hand side of Stacks 0AYC with one summand of the local reciprocity law. -/
theorem fracTameSymbolOrderAt_component_eq_principalDivisorPushforward
    {x : X} (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x}) :
    fracTameSymbolOrderAt hdim (ℱ.componentHeightOnePrime i)
        (canonicalHeightOneSymbol (ℱ.componentHeightOnePrime i))
        (Units.map ((functionFieldEquivFractionRing x).toRingEquiv :
            X.functionField →+* FractionRing (X.presheaf.stalk x)).toMonoidHom
          (Units.mk0 (ℱ.ratioL i.1) (ℱ.ratioL_ne_zero i.1)))
        (Units.map ((functionFieldEquivFractionRing x).toRingEquiv :
            X.functionField →+* FractionRing (X.presheaf.stalk x)).toMonoidHom
          (Units.mk0 (ℱ.ratioN i.1) (ℱ.ratioN_ne_zero i.1))) =
      principalDivisorPushforward C p ((ℱ.toKeyFormulaData C p).component i.1)
        ((ℱ.toKeyFormulaData C p).isIntegral_component i.1)
        ((ℱ.toKeyFormulaData C p).tameSymbol i.1) x := by
  have hmem : x ∈ closure ({ℱ.componentPoint i.1} : Set X) :=
    specializes_iff_mem_closure.mp i.2
  have hpd := principalDivisorPushforward_apply_image C p
    (integralComponentAt (ℱ.componentPoint i.1)) ((ℱ.toKeyFormulaData C p).tameSymbol i.1)
    (pointClosurePoint (ℱ.componentPoint i.1) hmem)
  rw [subschemeι_pointClosurePoint] at hpd
  refine Eq.trans ?_ hpd.symm
  rw [fracTameSymbolOrderAt_canonical_eq_ord_tameSymbolAtCoheightOne hdim
      (ℱ.componentHeightOnePrime i) (ℱ.pointOfHeightOnePrime_componentHeightOnePrime i)
      (ℱ.coheight_componentPoint i.1) hmem,
    principalCycle_apply, toKeyFormulaData_tameSymbol,
    rationalFunctionsEquivFunctionField_rationalFunctionsUnitsIntegralComponentEquiv_symm]
  rfl

end KeyFormulaSituation

end OrderComparison

end Stacks.Chow

end
