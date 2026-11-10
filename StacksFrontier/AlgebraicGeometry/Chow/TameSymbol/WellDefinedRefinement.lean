module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Tower
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.WellDefined

/-!
# The formula defining the tame symbol: the factorization half in an arbitrary local ring, and the
half about the choice of `B` against a refinement

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring and let `a₁, a₂ ∈ A` be nonzerodivisors.
Stacks 0EAG produces a finite ring extension `A ⊆ B` with `B/A` annihilated by a power of `𝔪`,
a nonzerodivisor `π_j ∈ B_j = B_{𝔪_j}` at each maximal ideal of `B`, and factorizations
`a_i = u_{i, j} π_j^{e_{i, j}}` with `u_{i, j}` units of `B_j` — that is a
`AlgebraicGeometry.TameSymbolPreparation`. The formula (Stacks 0EAQ) then reads

`∂_A(a₁, a₂) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}((-1)^{e_{1,j}e_{2,j}} u_{1,j}^{e_{2,j}} u_{2,j}^{-e_{1,j}}
  mod 𝔪_j)^{m_j}`,  `m_j = length_{B_j}(B_j / π_j B_j)`,

and Stacks 0EAR asserts that the right-hand side depends neither on the local factorizations nor
on `B`. The formula is `Stacks.Chow.factorizationValue` for the factor at a single maximal ideal
and `AlgebraicGeometry.TameSymbolPreparation.symbolValue` for the whole right-hand side, both of
`StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.WellDefined`, which also proves the factorization
half at the Noetherian one-dimensional local rings of the source.

This file adds the steps of Stacks 0EAR that need the refinement machinery of
`StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Tower`:

* `Stacks.Chow.factorizationValue_eq_of_factorizations_general` is the factorization half at one
  maximal ideal in an arbitrary local ring;
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_normPushforward` and
  `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_common_refinement` are the half about
  `B`, relative to a refinement: the value at a preparation over `B` is the value at `(x, y)` of
  the tame symbol on `A` that a finite refinement `B ⊆ C` furnishes by Stacks 0EAT, an expression
  in which neither `B` nor the preparation appears, so two extensions refined by one `C` give the
  same value.

Stacks 0EAR itself, at the source's hypotheses, is
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_preparations`, which builds that
refinement.

The argument for the choice of `B` is the source's. Two extensions are compared through a common
finite refinement `C`, which the source builds as `(B ⊗_A B') / (𝔪`-power torsion`)` by the
glueing of Stacks 0EAE; against a fixed `C` the comparison reduces to the norm-transitivity
identity of Stacks 0BIJ. That identity appears at the geometry in two shapes whose index
correspondence is derived from the semilocalizations `C_𝔮` rather than posited:
`Stacks.Chow.prod_norm_factorizationValue_tower_maximalSpectrum`, between the two products of the
factors of the formula Stacks 0EAQ, and
`Stacks.Chow.normPushforward_apply_eq_prod_norm_normPushforward`, between the two tame symbols
those products define. The last is the one the independence argument uses, because its two sides
are tame symbols in the sense of Stacks 0EAH rather than bare products: the factor at `𝔮` is a
tame symbol on `B_𝔮`, and a tame symbol on `B_𝔮` is forced by Stacks 0EAL, 0EAM and 0EAN to take
the value of the formula Stacks 0EAQ on a simultaneous power factorization. The common refinement
is a hypothesis of the two `symbolValue` statements below; it is built from the two preparations by
`Stacks.Chow.nonempty_commonRefinement`.

## Main results

* `Stacks.Chow.factorizationValue_eq_of_factorizations_general` — the factorization half of
  Stacks 0EAR at one maximal ideal, in an arbitrary local ring.
* `Stacks.Chow.prod_norm_factorizationValue_tower_maximalSpectrum` — Stacks 0EAT for the symbol
  the formula Stacks 0EAQ defines: the product over the maximal ideals of `C` of the residue-field
  norms of the local factors regroups over the maximal ideals of `B`, the correspondence of
  maximal ideals being derived from the semilocalizations.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_normPushforward` — the value of the
  formula Stacks 0EAQ at a preparation over `B` is the value of the tame symbol on `A` that a
  finite refinement `B ⊆ C` furnishes, an expression free of `B`.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_common_refinement` — the half of
  Stacks 0EAR about the choice of `B`, against a refinement taken as a hypothesis.

## References

* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Tag 0BIJ](https://stacks.math.columbia.edu/tag/0BIJ)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

universe u v w

namespace Stacks.Chow

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R]


/-- **The factorization half of Stacks 0EAR at a single maximal ideal, in an arbitrary local
ring.** The same identity as `Stacks.Chow.factorizationValue_eq_of_factorizations`, with `R`
neither Noetherian nor one-dimensional: the argument needs only that `π` and `θ` are
nonzerodivisors, so this is `Stacks.Chow.factorizationResidue_pow_ord_eq` read as a statement
about `Stacks.Chow.factorizationValue`. Since it implies the form at the Noetherian
one-dimensional local rings the source speaks of, namely
`Stacks.Chow.factorizationValue_eq_of_factorizations` of
`StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.WellDefined`, it too carries Stacks 0EAR. -/
@[stacks 0EAR "the first clause, at a single maximal ideal and in an ARBITRARY local ring: the \
value of the formula of Stacks 0EAQ does not depend on the choice of the local factorizations.  \
This is strictly more general than the form the source states -- R is neither Noetherian nor \
one-dimensional here -- and Stacks.Chow.factorizationValue_eq_of_factorizations, the form at the \
rings of the source, is this statement specialised to them"]
theorem factorizationValue_eq_of_factorizations_general
    {π θ : R} (hπ : π ∈ nonZeroDivisors R) (hθ : θ ∈ nonZeroDivisors R)
    {a₁ a₂ : R} {u₁ u₂ v₁ v₂ : Rˣ} {e₁ e₂ f₁ f₂ : ℕ}
    (hu₁ : a₁ = u₁ * π ^ e₁) (hu₂ : a₂ = u₂ * π ^ e₂)
    (hv₁ : a₁ = v₁ * θ ^ f₁) (hv₂ : a₂ = v₂ * θ ^ f₂) :
    factorizationValue π u₁ u₂ e₁ e₂ = factorizationValue θ v₁ v₂ f₁ f₂ :=
  factorizationResidue_pow_ord_eq hπ hθ hu₁ hu₂ hv₁ hv₂

end Local

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]

section FactorizationTower

variable {C : Type w} [CommRing C] [Algebra B C] [Module.Finite B C] [Algebra A C]
  [IsScalarTower A B C]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ r : MaximalSpectrum C, IsLocalHom (algebraMap A (Localization.AtPrime r.asIdeal))]
  [∀ (q : MaximalSpectrum B)
      (s : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
    Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (s.asIdeal.under C))]
  [∀ (q : MaximalSpectrum B)
      (s : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
    IsScalarTower B (Localization.AtPrime q.asIdeal) (Localization.AtPrime (s.asIdeal.under C))]
  [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum C)]
  [∀ q : MaximalSpectrum B,
    Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- **Stacks 0EAT for the symbol the formula Stacks 0EAQ defines.** Let `(A, 𝔪)` be a
one-dimensional Noetherian local ring, let `A ⊆ B` be a finite ring extension and let `B ⊆ C` be a
further finite extension. Then

`∂_A(a, b) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}(∂_{B_j}(a, b))`,

the product being over the maximal ideals `𝔪_j` of `B`, for both symbols read as the formula
Stacks 0EAQ attaches to the local factorization data on the local rings of `C`: the left-hand side
is the product over the maximal ideals of `C` of the residue-field norms down to `κ(𝔪)` of the
local factors, and the factor at `𝔪_j` on the right is the product over the maximal ideals of the
semilocalization `C_{𝔪_j}` of their norms down to `κ(𝔪_j)`. The two agree by transitivity of norms
for `κ(𝔪_{j,k})/κ(𝔪_j)/κ(𝔪)`, Stacks 0BIJ.

The correspondence between the maximal ideals of `C` and those of `B` — the content the source
takes from Stacks 0EAE — is *derived* here, from
`Stacks.Localization.prod_maximalSpectrum_eq_prod_prod`: the maximal ideals of `C` over `𝔪_j` are
the maximal ideals of the semilocalization `C_{𝔪_j}`, and the local ring of `C` at the one below
`v` is `Stacks.Chow.fibrePoint`. The tower `A → B_{𝔪_j} → C_{𝔪_{j,k}}` and the locality of its
structure maps are derived too, from the scalar towers `B → B_{𝔪_j} → C_{𝔪_{j,k}}` and
`Stacks.Chow.isLocalHom_fibreAlgebraMap`.

The statement quantifies over arbitrary local factorization data `(π, u₁, u₂, e₁, e₂)` on the
local rings of `C` rather than over data factoring two fixed elements of `A`, which is a
generalization and not a restriction: the elements `a` and `b` of the source enter the formula
only through that data, and the identity holds for all of it. The same equation between the two
tame symbols of Stacks 0EAH that the two sides define, rather than between the two products, is
`Stacks.Chow.normProd_eq_prod_norm_normProd` and
`Stacks.Chow.normPushforward_apply_eq_prod_norm_normPushforward`. -/
@[stacks 0EAT "the displayed equation for the symbol as the formula of Stacks 0EAQ defines it, \
over the maximal ideals of the refinement C the statement quantifies over, and generalized to \
arbitrary local factorization data on the local rings of C. The correspondence between the \
maximal ideals of C and those of B (Stacks 0EAE) is derived here from the semilocalizations \
rather than assumed, as is the tower of local rings along a fibre"]
theorem prod_norm_factorizationValue_tower_maximalSpectrum
    (π : ∀ r : MaximalSpectrum C, Localization.AtPrime r.asIdeal)
    (u₁ u₂ : ∀ r : MaximalSpectrum C, (Localization.AtPrime r.asIdeal)ˣ)
    (e₁ e₂ : MaximalSpectrum C → ℕ) :
    ∏ r : MaximalSpectrum C,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime r.asIdeal) →* ResidueField A)
          (factorizationValue (π r) (u₁ r) (u₂ r) (e₁ r) (e₂ r)) =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (∏ s : MaximalSpectrum
              (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)),
            Units.map (Algebra.norm (ResidueField (Localization.AtPrime q.asIdeal)) :
                ResidueField (Localization.AtPrime (fibrePoint q s).asIdeal) →*
                  ResidueField (Localization.AtPrime q.asIdeal))
              (factorizationValue (π (fibrePoint q s)) (u₁ (fibrePoint q s))
                (u₂ (fibrePoint q s)) (e₁ (fibrePoint q s)) (e₂ (fibrePoint q s)))) := by
  rw [Stacks.Localization.prod_maximalSpectrum_eq_prod_prod B C]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  exact (units_map_norm_residueField_comp (A := A) (B := Localization.AtPrime q.asIdeal)
    (factorizationValue (π (fibrePoint q s)) (u₁ (fibrePoint q s)) (u₂ (fibrePoint q s))
      (e₁ (fibrePoint q s)) (e₂ (fibrePoint q s)))).symm

end FactorizationTower

end Stacks.Chow

universe w'


namespace AlgebraicGeometry.TameSymbolPreparation

open Stacks.Chow

section Refinement

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {C : Type w} [CommRing C] [Algebra A C] [Module.Finite A C] [Fintype (MaximalSpectrum C)]
  [∀ s : MaximalSpectrum C, IsLocalHom (algebraMap A (Localization.AtPrime s.asIdeal))]
  {r : ℕ} {a : Fin r → A}

/-- **The half of Stacks 0EAR about the choice of `B`, at one refinement.** Let `(A, 𝔪)` be a
one-dimensional Noetherian local ring, let `A ⊆ B` be a finite extension carrying a tame-symbol
preparation `P` of
the family `a`, and let `B ⊆ C` be a further finite extension with `𝔪` not an associated prime of
either and with `𝔮 B_𝔮` not an associated prime of the semilocalization `C_𝔮` at any maximal ideal
`𝔮` of `B`. Then the value of the formula Stacks 0EAQ computed from `P` is the value at `(x, y)` of
the tame symbol on `A` that `C` furnishes by Stacks 0EAT,

`∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_i e_j} ū_i^{e_j} ū_j^{-e_i})^{m_𝔮}
  = ∏_𝔰 Norm_{κ(𝔰)/κ(𝔪)}(∂_{C_𝔰}(x, y))`,

the left product being over the maximal ideals of `B` and the right one over those of `C`. The
right-hand side mentions neither `B` nor `P`, so this is independence of the choice of `B` among
the extensions a single `C` refines; the two-sided form is
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_common_refinement`.

This is the source's argument. Stacks 0EAT regroups the product over the maximal ideals of `C`
into a product over the maximal ideals `𝔮` of `B` of residue-field norms of the norm pushforwards
along the semilocalizations `C_𝔮`, by transitivity of norms (Stacks 0BIJ); that is
`Stacks.Chow.normPushforward_apply_eq_prod_norm_normPushforward`. Each of those pushforwards is a
tame symbol on `B_𝔮` in the sense of Stacks 0EAH, and `P` factors `x` and `y` simultaneously
against one parameter there, so Stacks 0EAL, 0EAM and 0EAN force its value to be the local factor
of Stacks 0EAQ — that is `Stacks.Chow.RegularTameSymbol.apply_eq_factorizationValue`, applied to a
symbol the refinement produces rather than to one assumed on `B_𝔮`.

This is a conditional step of Stacks 0EAR and not Stacks 0EAR: the refinement `B ⊆ C`, the tame
symbols on the local rings of `C`, and the hypotheses of Stacks 0EAT for `A ⊆ C` read at the
maximal ideals of `B` are all hypotheses here. Stacks 0EAR itself, with every one of them built
from the preparations, is
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_preparations`. -/
theorem symbolValue_eq_normPushforward
    {B : Type v} [CommRing B] [Algebra A B] [Algebra B C] [IsScalarTower A B C]
    [Module.Finite B C] [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    [∀ q : MaximalSpectrum B,
      Finite (MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))]
    [∀ (q : MaximalSpectrum B)
        (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
    [∀ (q : MaximalSpectrum B)
        (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
      IsScalarTower B (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (hfibre : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (symb : ∀ s : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime s.asIdeal))
    (hinj : Function.Injective (algebraMap A C))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A C) ≤
      LinearMap.range (Algebra.linearMap A C))
    (hinjFibre : ∀ q : MaximalSpectrum B,
      Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hquotFibre : ∀ q : MaximalSpectrum B,
      ∃ n : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (P : TameSymbolPreparation a B) (i j : Fin r)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    P.symbolValue i j = normPushforward hC symb hinj hquot x y := by
  have : ∀ q : MaximalSpectrum B,
      Fintype (MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) :=
    fun q => Fintype.ofFinite
      (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
  rw [normPushforward_apply_eq_prod_norm_normPushforward hB hC hfibre symb hinj hquot
    hinjFibre hquotFibre x y]
  refine Finset.prod_congr rfl fun q _ => ?_
  congr 1
  refine (RegularTameSymbol.apply_eq_factorizationValue _
    ⟨P.parameter q.asIdeal,
      isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q.asIdeal)⟩ _ _
    (P.factorUnit q.asIdeal i) (P.factorUnit q.asIdeal j)
    (P.exponent q.asIdeal i) (P.exponent q.asIdeal j) ?_ ?_).symm
  all_goals rw [toExtensionNonZeroDivisor_val,
    IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal)]
  · rw [hx]
    exact P.factorization q.asIdeal i
  · rw [hy]
    exact P.factorization q.asIdeal j

omit [Fintype (MaximalSpectrum C)] in
/-- **The half of Stacks 0EAR about the choice of `B`, against a given refinement.** Two
tame-symbol preparations of the same family over two different finite extensions `A ⊆ B` and
`A ⊆ B'`, both refined by a single finite extension `A ⊆ C` as in Stacks 0EAT, give the same value
of the formula Stacks 0EAQ. Both values are the
value at `(x, y)` of the tame symbol on `A` that `C` furnishes, by
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_normPushforward`, which mentions neither
extension.

Together with `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_sameExtension` this
accounts for both of the source's assertions, against a given refinement. The refinement is the
one input taken as a hypothesis; the source gets it from the glueing of Stacks 0EAE, formalized as
`Stacks.RingHomGluing.exists_ringHom_inducing_at_maximal_ideal`, applied to
`C = (B ⊗_A B')/(𝔪`-power torsion`)`, which is built by
`Stacks.Chow.nonempty_commonRefinement`.

This is therefore a conditional step of Stacks 0EAR and not Stacks 0EAR: the refinement and the
localized hypotheses are assumed here. Stacks 0EAR itself is this statement with all of them
discharged, `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_preparations`. -/
theorem symbolValue_eq_of_common_refinement [Finite (MaximalSpectrum C)]
    {B : Type v} [CommRing B] [Algebra A B] [Algebra B C] [IsScalarTower A B C]
    [Module.Finite B C] [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    [∀ q : MaximalSpectrum B,
      Finite (MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))]
    [∀ (q : MaximalSpectrum B)
        (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
    [∀ (q : MaximalSpectrum B)
        (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
      IsScalarTower B (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
    {B' : Type w'} [CommRing B'] [Algebra A B'] [Algebra B' C] [IsScalarTower A B' C]
    [Module.Finite B' C] [Fintype (MaximalSpectrum B')]
    [∀ q : MaximalSpectrum B', IsNoetherianRing (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B', Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B', IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    [∀ q : MaximalSpectrum B',
      Finite (MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))]
    [∀ (q : MaximalSpectrum B')
        (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
    [∀ (q : MaximalSpectrum B')
        (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
      IsScalarTower B' (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hB' : ¬ IsAssociatedPrime (maximalIdeal A) B')
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (hfibre : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (hfibre' : ∀ q : MaximalSpectrum B',
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (symb : ∀ s : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime s.asIdeal))
    (hinj : Function.Injective (algebraMap A C))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A C) ≤
      LinearMap.range (Algebra.linearMap A C))
    (hinjFibre : ∀ q : MaximalSpectrum B,
      Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hinjFibre' : ∀ q : MaximalSpectrum B',
      Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hquotFibre : ∀ q : MaximalSpectrum B,
      ∃ n : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hquotFibre' : ∀ q : MaximalSpectrum B',
      ∃ n : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (P : TameSymbolPreparation a B) (P' : TameSymbolPreparation a B') (i j : Fin r)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    P.symbolValue i j = P'.symbolValue i j := by
  have : Fintype (MaximalSpectrum C) := Fintype.ofFinite (MaximalSpectrum C)
  exact (symbolValue_eq_normPushforward hB hC hfibre symb hinj hquot hinjFibre hquotFibre
      P i j x y hx hy).trans
    (symbolValue_eq_normPushforward hB' hC hfibre' symb hinj hquot hinjFibre' hquotFibre'
      P' i j x y hx hy).symm

end Refinement

end AlgebraicGeometry.TameSymbolPreparation

end
