module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ResidueFunctoriality
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The connecting morphism of the residue sequence, and its naturality in the ring

Let `A → R` be a ring map and let `t ∈ R` cut out the effective Cartier divisor
`Y = Spec (R ⧸ (t))` in `X = Spec R`, with the de Rham complex of log poles defined for `Y ⊆ X`
over `S = Spec A` in the sense of Stacks Tag 0FMV. Stacks Tag 0FMW gives the short exact sequence
of complexes

`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`,

`Stacks.LogPoles.shortExact_logShortComplex`, and the connecting morphism of a short exact
sequence of cochain complexes in the derived category is Mathlib's
`DerivedCategory.triangleOfSESδ`. This file carries the sequence across the ℕ-to-ℤ reindexing
`DerivedCategory` requires, forms that connecting morphism, and proves it **natural in the ring**
under the morphism of sequences built in
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ResidueFunctoriality`.

## Main definitions

* `Stacks.LogPoles.logShortComplexInt`: the residue sequence of Tag 0FMW reindexed from `ℕ` to
  `ℤ`, which is the shape `DerivedCategory` consumes.
* `Stacks.LogPoles.logResidueTriangle`: the distinguished triangle of the residue sequence.
* `Stacks.LogPoles.logResidueConnecting`: **the connecting morphism `δ`** of the residue
  sequence, `Ω^•_{Y/S}[-1] ⟶ Ω^•_{X/S}[1]` in the derived category.
* `Stacks.LogPoles.logShortComplexIntTowerHom`: the morphism of the reindexed sequences induced
  by a tower `R → R'`.

## Main results

* `Stacks.LogPoles.shortExact_logShortComplexInt`: the reindexed sequence is still short exact.
  In degrees below zero all three terms vanish; in degree `n ≥ 0` the sequence is isomorphic to
  the degree-`n` part of the sequence of Tag 0FMW.
* `Stacks.LogPoles.logResidueTriangle_distinguished`: its triangle is distinguished.
* `Stacks.LogPoles.logResidueConnecting_naturality`: **`δ` is natural in the ring.** This is
  `DerivedCategory.triangleOfSESδ_naturality` applied to the morphism of the two residue
  sequences, which is what
  `StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ResidueFunctoriality` supplies.
* `Stacks.LogPoles.logResidueTriangleMap`: the same naturality packaged as a morphism of
  distinguished triangles.

## Implementation notes

`DerivedCategory.triangleOfSESδ` is stated for `ShortComplex (CochainComplex C ℤ)`, while the de
Rham complex and its complex of log poles are indexed by `ℕ`; `ℕ` carries no `HasShift`, which is
why the residue sequence of Tag 0FMW was built with the hand-made shift
`LaurentDeRham.deRhamComplexShift` in the first place. The reindexing used here is Mathlib's
`ComplexShape.embeddingUpNat.extendFunctor`, which places the complex in the non-negative degrees
and zero elsewhere. It is additive and fully faithful, so it carries the sequence and the
morphism of sequences across without loss, and short exactness is checked degreewise: in a
negative degree every term of the extended sequence is a zero object, and in a non-negative
degree the extended sequence is isomorphic — by
`ComplexShape.Embedding.extendFunctorCompEvalIso` — to the corresponding degree of the original,
where `Stacks.LogPoles.shortExact_map_eval_logShortComplex` applies.

`HasDerivedCategory` is not an instance in Mathlib, by design, so it is carried as an instance
hypothesis `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` as elsewhere in this repository; a caller
with no preference supplies `HasDerivedCategory.standard`.

This is naturality of `δ` for the *ring-level* residue sequence. It is **not** Stacks Tag 0FUQ.
Tag 0FUQ asserts the commutativity of a square in `D(X, f^{-1}𝒪_S)` whose `δ` is the connecting
morphism of the *sheaf-level* Tag 0FMW sequence on a scheme, and whose vertical maps are the
degree-two self-maps of Tag 0FU7 attached to the de Rham first Chern classes
`c₁^{dR}(𝒪_X(-Y))` and its restriction to `Y`, identified with boundary maps by Tag 0FUG. The
sheaf-level Tag 0FMW sequence does not exist in this library — what exists is the affine local
case proved here — so the subject of Tag 0FUQ cannot yet be written down, and no clause of it is
claimed.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), the residue sequence
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), the hypothesis
* [Stacks Project, Tag 011G](https://stacks.math.columbia.edu/tag/011G), the sign of the shift
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace Stacks.LogPoles

/-! ### The residue sequence reindexed by the integers -/

section Reindex

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] {t : R}

/-- **The residue sequence of Stacks Tag 0FMW, reindexed from `ℕ` to `ℤ`.** The complexes are
placed in the non-negative degrees and are zero elsewhere. This is the shape the derived category
consumes, `ℕ` having no shift. -/
def logShortComplexInt (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  (logShortComplex ht hsplit).map
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A))

/-- The left-hand map of the reindexed sequence is the reindexed inclusion of the forms with no
pole. -/
@[simp]
theorem logShortComplexInt_f (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    (logShortComplexInt ht hsplit).f =
      HomologicalComplex.extendMap (logIncl ht) ComplexShape.embeddingUpNat := rfl

/-- The right-hand map of the reindexed sequence is the reindexed residue. -/
@[simp]
theorem logShortComplexInt_g (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    (logShortComplexInt ht hsplit).g =
      HomologicalComplex.extendMap (logResidue ht hsplit) ComplexShape.embeddingUpNat := rfl

/-- **The reindexed residue sequence is still short exact.** Below degree zero all three terms
are zero objects; in degree `n ≥ 0` the sequence is isomorphic to the degree-`n` part of the
sequence of Stacks Tag 0FMW, where `Stacks.LogPoles.shortExact_map_eval_logShortComplex`
applies. -/
theorem shortExact_logShortComplexInt
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    (logShortComplexInt ht hsplit).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  rcases le_or_gt 0 n with hn | hn
  · have h : ComplexShape.embeddingUpNat.f n.toNat = n := Int.toNat_of_nonneg hn
    exact ShortComplex.shortExact_of_iso
      ((ShortComplex.mapNatIso (logShortComplex ht hsplit)
        (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso (ModuleCat.{u} A) h)).symm)
      (shortExact_map_eval_logShortComplex ht hsplit n.toNat)
  · have key : ∀ K : CochainComplex (ModuleCat.{u} A) ℕ,
        Limits.IsZero ((K.extend ComplexShape.embeddingUpNat).X n) := fun K ↦
      K.isZero_extend_X ComplexShape.embeddingUpNat n fun i hi ↦ by
        simp only [ComplexShape.embeddingUpNat_f] at hi
        omega
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ (key _)
        mono_f := ⟨fun g h _ ↦ (key _).eq_of_tgt g h⟩
        epi_g := ⟨fun a b _ ↦ (key _).eq_of_src a b⟩ }

end Reindex

/-! ### The distinguished triangle and the connecting morphism -/

section Connecting

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] {t : R}
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- **The distinguished triangle of the residue sequence** of Stacks Tag 0FMW, affine locally:
`Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → Ω^•_{X/S}[1]`. -/
def logResidueTriangle (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)) :=
  DerivedCategory.triangleOfSES (shortExact_logShortComplexInt ht hsplit)

/-- The triangle of the residue sequence is distinguished. -/
theorem logResidueTriangle_distinguished
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    logResidueTriangle ht hsplit ∈
      Pretriangulated.distinguishedTriangles (C := DerivedCategory (ModuleCat.{u} A)) :=
  DerivedCategory.triangleOfSES_distinguished (shortExact_logShortComplexInt ht hsplit)

/-- **The connecting morphism `δ` of the residue sequence** of Stacks Tag 0FMW, affine locally:
the third arrow of the distinguished triangle, `Ω^•_{Y/S}[-1] ⟶ Ω^•_{X/S}[1]` in the derived
category of `A`-modules. -/
def logResidueConnecting (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    DerivedCategory.Q.obj (logShortComplexInt ht hsplit).X₃ ⟶
      (DerivedCategory.Q.obj (logShortComplexInt ht hsplit).X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ (shortExact_logShortComplexInt ht hsplit)

/-- The connecting morphism is the third arrow of the distinguished triangle. -/
@[simp]
theorem logResidueTriangle_mor₃ (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    (logResidueTriangle ht hsplit).mor₃ = logResidueConnecting ht hsplit := rfl

end Connecting

/-! ### Naturality of the connecting morphism in the ring -/

section Naturality

variable {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R']
  {t : R} {s : R'}
  [Algebra (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]
  [IsScalarTower A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]
  [IsScalarTower R (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s})]

/-- **The morphism of the two reindexed residue sequences** induced by a tower `R → R'` carrying
the equation `t` of the divisor to the equation `s`: the morphism of sequences of
`Stacks.LogPoles.logShortComplexTowerHom`, reindexed. -/
def logShortComplexIntTowerHom (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    logShortComplexInt ht hsplit ⟶ logShortComplexInt hs' hsplit' :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)).mapShortComplex.map
    (logShortComplexTowerHom hs ht hs' hsplit hsplit')

/-- The left-hand component of the morphism of reindexed sequences is the reindexed standard map
of de Rham complexes. -/
@[simp]
theorem logShortComplexIntTowerHom_τ₁ (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    (logShortComplexIntTowerHom hs ht hs' hsplit hsplit').τ₁ =
      HomologicalComplex.extendMap (KaehlerDifferential.deRhamComplexMap A R R')
        ComplexShape.embeddingUpNat := rfl

/-- The right-hand component of the morphism of reindexed sequences is the reindexed restriction
of forms to the divisor. -/
@[simp]
theorem logShortComplexIntTowerHom_τ₃ (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    (logShortComplexIntTowerHom hs ht hs' hsplit hsplit').τ₃ =
      HomologicalComplex.extendMap
        (deRhamShiftTowerMap A (R ⧸ Ideal.span {t}) (R' ⧸ Ideal.span {s}))
        ComplexShape.embeddingUpNat := rfl

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- **The connecting morphism of the residue sequence is natural in the ring.** Given a tower
`R → R'` of `A`-algebras carrying the equation `t` of the divisor to the equation `s`, the square
formed by the two connecting morphisms, the restriction of forms to the divisors on the left and
the standard map of de Rham complexes on the right commutes in the derived category. This is
`DerivedCategory.triangleOfSESδ_naturality` applied to the morphism of the two residue sequences
of Stacks Tag 0FMW, whose residue square is
`Stacks.LogPoles.logComplexTowerMap_comp_logResidue`. -/
theorem logResidueConnecting_naturality (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    logResidueConnecting ht hsplit ≫
        (DerivedCategory.Q.map
          (logShortComplexIntTowerHom hs ht hs' hsplit hsplit').τ₁)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (logShortComplexIntTowerHom hs ht hs' hsplit hsplit').τ₃ ≫
        logResidueConnecting hs' hsplit' :=
  DerivedCategory.triangleOfSESδ_naturality _ _ _

/-- **The naturality of `δ` as a morphism of distinguished triangles.** The restriction maps of
`Ω^•(log Y)` give a morphism of the two distinguished triangles of the residue sequence, whose
third square is `Stacks.LogPoles.logResidueConnecting_naturality`. -/
def logResidueTriangleMap (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (hsplit' : ∃ r : Ω[R'⁄A] →ₗ[R'] R',
      r ∘ₗ LinearMap.toSpanSingleton R' Ω[R'⁄A] (KaehlerDifferential.D A R' s) =
        LinearMap.id) :
    logResidueTriangle ht hsplit ⟶ logResidueTriangle hs' hsplit' :=
  DerivedCategory.triangleOfSES.map (shortExact_logShortComplexInt ht hsplit)
    (shortExact_logShortComplexInt hs' hsplit')
    (logShortComplexIntTowerHom hs ht hs' hsplit hsplit')

end Naturality

end Stacks.LogPoles

end
