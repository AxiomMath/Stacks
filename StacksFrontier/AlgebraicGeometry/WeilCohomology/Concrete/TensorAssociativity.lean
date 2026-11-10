module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionIntersectionUnit
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorBifunctor

/-!
# Associativity, commutativity and unit of the tensor product of correspondences

The tensor product of correspondences `x ⊗ x' = pr₁₃^* x · pr₂₄^* x'`
(`Stacks.WeilCohomology.tensorInt`, for schemes of constant dimension, formed with the canonical
diagonal classes) is associative, commutative and unital up to the constraints of products of
schemes, which is the content of Stacks 0FG7 beyond bifunctoriality:

* transporting `(x₁ ⊗ x₂) ⊗ x₃` along the associativity isomorphisms
  `(A₁ × A₂) × A₃ ≅ A₁ × (A₂ × A₃)` and `(B₁ × B₂) × B₃ ≅ B₁ × (B₂ × B₃)` gives
  `x₁ ⊗ (x₂ ⊗ x₃)`;
* transporting `x ⊗ x'` along the factor switches `A × A' ≅ A' × A` and `B × B' ≅ B' × B` gives
  `x' ⊗ x`;
* for `P ≅ Spec k`, transporting `x ⊗ [Δ_P]` along `(A × P) × (B × P) ≅ A × B` gives `x`, and
  likewise for `[Δ_P] ⊗ x`.

The statements are recorded as propositions and then proved, for the canonical diagonal classes:
each side is a product of classes pulled back from the factors, transported along the constraint
isomorphism by iso-invariance of the intersection product, and the two sides agree by
associativity (Stacks 0FC1), commutativity, and the unit law `β · [W] = β` of the intersection
product.

## Main definitions

* `Stacks.WeilCohomology.TensorIntAssoc`, `Stacks.WeilCohomology.TensorIntSymm`,
  `Stacks.WeilCohomology.TensorIntRightUnit`, `Stacks.WeilCohomology.TensorIntLeftUnit`: the
  four statements.
* `Stacks.WeilCohomology.diagonalChowClass`: the class `[Δ_P] ∈ CH_*(P × P)` of the diagonal,
  the integral class underlying `Stacks.WeilCohomology.diagonalBlock`.

## Main results

* `Stacks.WeilCohomology.tensorInt_assoc`, `Stacks.WeilCohomology.tensorInt_symm`,
  `Stacks.WeilCohomology.tensorInt_rightUnit`, `Stacks.WeilCohomology.tensorInt_leftUnit`: the
  four statements hold.
* `Stacks.WeilCohomology.chowPushforwardOfIso_selfIntersectionProduct_heq`: the transport of
  `p₁^* a · p₂^* b` along an isomorphism `Ψ` with `Ψ ≫ q_i = p_i` is `q₁^* a · q₂^* b`.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-- `X × Y` has dimension `d + e` for `X` of dimension `d` and `Y` of dimension `e`. -/
theorem relativeDimension_prodBase_add {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    [Smooth sX] [Smooth sY] {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) : RelativeDimension (prodBase sX sY) (d + e) :=
  add_comm e d ▸ relativeDimension_prodBase k sX sY hX hY

/-- The product of two isomorphisms over the base is an isomorphism. -/
instance isIso_prodHom {S X Y X' Y' : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sX' : X' ⟶ S)
    (sY' : Y' ⟶ S) (φX : X' ⟶ X) (φY : Y' ⟶ Y) [IsIso φX] [IsIso φY] (hφX : φX ≫ sX = sX')
    (hφY : φY ≫ sY = sY') : IsIso (prodHom sX sY sX' sY' φX φY hφX hφY) :=
  Limits.pullback.map_isIso (i₃ := 𝟙 _) ..

/-- A morphism `(A₁ × A₂) × A₃ ⟶ A₁ × (A₂ × A₃)` compatible with the three projections is a
morphism over the base. -/
theorem assocHom_comp_prodBase {S A₁ A₂ A₃ : Scheme.{u}} (sA₁ : A₁ ⟶ S) (sA₂ : A₂ ⟶ S)
    (sA₃ : A₃ ⟶ S)
    (φ : Limits.pullback (prodBase sA₁ sA₂) sA₃ ⟶ Limits.pullback sA₁ (prodBase sA₂ sA₃))
    (h₁ : φ ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _) :
    φ ≫ prodBase sA₁ (prodBase sA₂ sA₃) = prodBase (prodBase sA₁ sA₂) sA₃ := by
  change φ ≫ (Limits.pullback.fst _ _ ≫ sA₁) =
    Limits.pullback.fst _ _ ≫ (Limits.pullback.fst _ _ ≫ sA₁)
  rw [← Category.assoc, h₁, Category.assoc]

attribute [local instance] isClosedImmersion_graphMorphism

/-- The class `[Δ_P] ∈ CH_n(P × P)` of the diagonal of `P`: the cycle of the graph of the
identity. -/
abbrev diagonalChowClass {P : Scheme.{u}} (sP : P ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sP] [IsSeparated sP] (n : ℤ) :
    chowGroup (fieldChowSituation k) (prodBase sP sP) n :=
  QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
    (prodBase sP sP) (graphMorphism sP sP (𝟙 P) (Category.id_comp _)) n)

section Statements

variable {A A' A₁ A₂ A₃ B B' B₁ B₂ B₃ P : Scheme.{u}}
  (sA : A ⟶ (fieldChowSituation k).S) (sA' : A' ⟶ (fieldChowSituation k).S)
  (sA₁ : A₁ ⟶ (fieldChowSituation k).S) (sA₂ : A₂ ⟶ (fieldChowSituation k).S)
  (sA₃ : A₃ ⟶ (fieldChowSituation k).S)
  (sB : B ⟶ (fieldChowSituation k).S) (sB' : B' ⟶ (fieldChowSituation k).S)
  (sB₁ : B₁ ⟶ (fieldChowSituation k).S) (sB₂ : B₂ ⟶ (fieldChowSituation k).S)
  (sB₃ : B₃ ⟶ (fieldChowSituation k).S) (sP : P ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sA₁]
  [LocallyOfFiniteType sA₂] [LocallyOfFiniteType sA₃] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB'] [LocallyOfFiniteType sB₁] [LocallyOfFiniteType sB₂]
  [LocallyOfFiniteType sB₃] [LocallyOfFiniteType sP]
  [Smooth sA] [Smooth sA'] [Smooth sA₁] [Smooth sA₂] [Smooth sA₃] [Smooth sB] [Smooth sB']
  [Smooth sB₁] [Smooth sB₂] [Smooth sB₃] [Smooth sP]
  [IsSeparated sA] [IsSeparated sA'] [IsSeparated sA₁] [IsSeparated sA₂] [IsSeparated sA₃]
  [IsSeparated sB] [IsSeparated sB'] [IsSeparated sB₁] [IsSeparated sB₂] [IsSeparated sB₃]
  [IsSeparated sP]

/-- **Associativity of the tensor product of correspondences**, up to the associativity
constraints: for isomorphisms `φA : (A₁ × A₂) × A₃ ⟶ A₁ × (A₂ × A₃)` and
`φB : (B₁ × B₂) × B₃ ⟶ B₁ × (B₂ × B₃)` compatible with the three projections, the transport of
`(x₁ ⊗ x₂) ⊗ x₃` along `φA × φB` is `x₁ ⊗ (x₂ ⊗ x₃)` (the degrees
`(e₁ + e₂) + e₃ - ((r₁ + r₂) + r₃)` and `e₁ + (e₂ + e₃) - (r₁ + (r₂ + r₃))` agree, whence the
heterogeneous equality). -/
def TensorIntAssoc : Prop :=
  ∀ {d₁ d₂ d₃ e₁ e₂ e₃ : ℕ} (hA₁ : RelativeDimension sA₁ d₁) (hA₂ : RelativeDimension sA₂ d₂)
    (hA₃ : RelativeDimension sA₃ d₃) (hB₁ : RelativeDimension sB₁ e₁)
    (hB₂ : RelativeDimension sB₂ e₂) (hB₃ : RelativeDimension sB₃ e₃)
    (φA : Limits.pullback (prodBase sA₁ sA₂) sA₃ ⟶ Limits.pullback sA₁ (prodBase sA₂ sA₃))
    [IsIso φA]
    (hφA₁ : φA ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _),
    φA ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _ →
    φA ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ →
    ∀ (φB : Limits.pullback (prodBase sB₁ sB₂) sB₃ ⟶ Limits.pullback sB₁ (prodBase sB₂ sB₃))
    [IsIso φB]
    (hφB₁ : φB ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _),
    φB ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _ →
    φB ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ →
    ∀ (r₁ r₂ r₃ : ℤ)
    (x₁ : chowGroup (fieldChowSituation k) (prodBase sA₁ sB₁) ((e₁ : ℤ) - r₁))
    (x₂ : chowGroup (fieldChowSituation k) (prodBase sA₂ sB₂) ((e₂ : ℤ) - r₂))
    (x₃ : chowGroup (fieldChowSituation k) (prodBase sA₃ sB₃) ((e₃ : ℤ) - r₃)),
    chowPushforwardOfIso (fieldChowSituation k)
        (prodBase (prodBase (prodBase sA₁ sA₂) sA₃) (prodBase (prodBase sB₁ sB₂) sB₃))
        (prodBase (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃)))
        (prodHom (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃))
          (prodBase (prodBase sA₁ sA₂) sA₃) (prodBase (prodBase sB₁ sB₂) sB₃) φA φB
          (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁))
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _
        (tensorInt k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (canonicalDiagonalClassFamily k)
          (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂) hA₃
          (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂) hB₃ (r₁ + r₂) r₃
          (tensorInt k sA₁ sA₂ sB₁ sB₂ (canonicalDiagonalClassFamily k) hA₁ hA₂ hB₁ hB₂ r₁ r₂
            x₁ x₂) x₃) ≍
      tensorInt k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) (canonicalDiagonalClassFamily k)
        hA₁ (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃) hB₁
        (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃) r₁ (r₂ + r₃) x₁
        (tensorInt k sA₂ sA₃ sB₂ sB₃ (canonicalDiagonalClassFamily k) hA₂ hA₃ hB₂ hB₃ r₂ r₃
          x₂ x₃)

/-- **Commutativity of the tensor product of correspondences**, up to the commutativity
constraints: the transport of `x ⊗ x'` along the factor switches `A × A' ≅ A' × A` and
`B × B' ≅ B' × B` is `x' ⊗ x`. -/
def TensorIntSymm : Prop :=
  ∀ {d d' e e' : ℕ} (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB e) (hB' : RelativeDimension sB' e') (r r' : ℤ)
    (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r))
    (x' : chowGroup (fieldChowSituation k) (prodBase sA' sB') ((e' : ℤ) - r')),
    chowPushforwardOfIso (fieldChowSituation k) (tensorBase sA sA' sB sB')
        (tensorBase sA' sA sB' sB)
        (prodHom (prodBase sA' sA) (prodBase sB' sB) (prodBase sA sA') (prodBase sB sB')
          (pullbackSymmetry sA sA').hom (pullbackSymmetry sB sB').hom
          (pullbackSymmetry_hom_comp_base sA sA') (pullbackSymmetry_hom_comp_base sB sB'))
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _
        (tensorInt k sA sA' sB sB' (canonicalDiagonalClassFamily k) hA hA' hB hB' r r' x x') ≍
      tensorInt k sA' sA sB' sB (canonicalDiagonalClassFamily k) hA' hA hB' hB r' r x' x

/-- **`[Δ_P]` is a right unit for the tensor product of correspondences**, for `P ≅ Spec k`:
the transport of `x ⊗ [Δ_P]` along the projections `(A × P) × (B × P) ≅ A × B` is `x`. -/
def TensorIntRightUnit : Prop :=
  ∀ [IsIso sP] {d e : ℕ} (hA : RelativeDimension sA d) (hB : RelativeDimension sB e)
    (hP : RelativeDimension sP 0) (r : ℤ)
    (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r)),
    chowPushforwardOfIso (fieldChowSituation k) (tensorBase sA sP sB sP) (prodBase sA sB)
        (prodHom sA sB (prodBase sA sP) (prodBase sB sP) (Limits.pullback.fst sA sP)
          (Limits.pullback.fst sB sP) rfl rfl)
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _
        (tensorInt k sA sP sB sP (canonicalDiagonalClassFamily k) hA hP hB hP r 0 x
          (diagonalChowClass k sP _)) ≍ x

/-- **`[Δ_P]` is a left unit for the tensor product of correspondences**, for `P ≅ Spec k`:
the transport of `[Δ_P] ⊗ x` along the projections `(P × A) × (P × B) ≅ A × B` is `x`. -/
def TensorIntLeftUnit : Prop :=
  ∀ [IsIso sP] {d e : ℕ} (hA : RelativeDimension sA d) (hB : RelativeDimension sB e)
    (hP : RelativeDimension sP 0) (r : ℤ)
    (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r)),
    chowPushforwardOfIso (fieldChowSituation k) (tensorBase sP sA sP sB) (prodBase sA sB)
        (prodHom sA sB (prodBase sP sA) (prodBase sP sB) (Limits.pullback.snd sP sA)
          (Limits.pullback.snd sP sB) Limits.pullback.condition.symm
          Limits.pullback.condition.symm)
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _
        (tensorInt k sP sA sP sB (canonicalDiagonalClassFamily k) hP hA hP hB 0 r
          (diagonalChowClass k sP _) x) ≍ x

end Statements

/-! ### Transport of products of pulled back classes along isomorphisms -/

section Transport

local notation "μ" =>
  selfIntersectionProduct (fieldChowSituation k)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k)

local notation "pb[" sA ", " sB ", " v ", " hv ", " r ", " hr ", " n "]" =>
  flatPullbackChow (fieldChowSituation k) sA sB v hv r hr n
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)

/-- Pushing a flat pullback forward along an isomorphism `Ψ : W ⟶ W'` with `Ψ ≫ q = p` gives
the flat pullback along `q`: `Ψ_* p^* a = q^* a`. -/
theorem chowPushforwardOfIso_flatPullbackChow {W W' V : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
    (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW']
    (sV : V ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV]
    (Ψ : W ⟶ W') [IsIso Ψ] (hΨ : Ψ ≫ sW' = sW) (p : W ⟶ V) [LocallyOfFiniteType p] [Flat p]
    (q : W' ⟶ V) [LocallyOfFiniteType q] [Flat q] (hp : p ≫ sV = sW) (hq : q ≫ sV = sW')
    (hc : Ψ ≫ q = p) {n : ℕ} (hpd : RelativeDimension p n) (hqd : RelativeDimension q n)
    (i : ℤ) (a : chowGroup (fieldChowSituation k) sV i) :
    chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ (i + n)
        (pb[sW, sV, p, hp, n, hpd, i] a) =
      pb[sW', sV, q, hq, n, hqd, i] a := by
  have h := flatPullbackChow_chowPushforwardOfIso (fieldChowSituation k) sV sW sV sW' (𝟙 V)
    (Category.id_comp _) Ψ hΨ p hp q hq (by rw [Category.comp_id, hc]) n hpd hqd i
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) a
  rw [chowPushforwardOfIso_id] at h
  exact h.symm

/-- Transport of a product along an isomorphism: `Ψ_*(x · y) = Ψ_* x · Ψ_* y`, for the canonical
diagonal classes. -/
private theorem chowPushforwardOfIso_selfIntersectionProduct {W W' : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW'] [Smooth sW']
    (Ψ : W ⟶ W') [IsIso Ψ] (hΨ : Ψ ≫ sW' = sW) {N : ℕ} (hN : RelativeDimension sW N)
    (hN' : RelativeDimension sW' N) (a b : ℤ) (x : chowGroup (fieldChowSituation k) sW a)
    (y : chowGroup (fieldChowSituation k) sW b) :
    chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ (a + b - N)
        (μ sW N (canonicalDiagonalClassFamily k sW N hN) a b x y) =
      μ sW' N (canonicalDiagonalClassFamily k sW' N hN') a b
        (chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ a x)
        (chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ b y) := by
  have hinv : ∀ (l : ℤ) (z : chowGroup (fieldChowSituation k) sW' l),
      chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ l
        (chowPushforwardOfIso (fieldChowSituation k) sW' sW (inv Ψ)
          (by rw [IsIso.inv_comp_eq, hΨ]) l z) = z :=
    fun l z ↦ (chowGroupEquivOfIso (fieldChowSituation k) sW sW' Ψ hΨ l).apply_symm_apply z
  rw [canonicalDiagonalClassFamily_isoInvariant k sW' sW Ψ hΨ N hN' hN, hinv]

/-- **Transport of a product of pulled back classes along an isomorphism**: for an isomorphism
`Ψ : W ⟶ W'` over `k` with `Ψ ≫ q₁ = p₁` and `Ψ ≫ q₂ = p₂`,
`Ψ_*(p₁^* a · p₂^* b) = q₁^* a · q₂^* b`, for the canonical diagonal classes. -/
theorem chowPushforwardOfIso_selfIntersectionProduct_heq {W W' V₁ V₂ : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW'] [Smooth sW']
    (sV₁ : V₁ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV₁]
    (sV₂ : V₂ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV₂]
    (Ψ : W ⟶ W') [IsIso Ψ] (hΨ : Ψ ≫ sW' = sW)
    (p₁ : W ⟶ V₁) [LocallyOfFiniteType p₁] [Flat p₁] (p₂ : W ⟶ V₂) [LocallyOfFiniteType p₂]
    [Flat p₂] (q₁ : W' ⟶ V₁) [LocallyOfFiniteType q₁] [Flat q₁] (q₂ : W' ⟶ V₂)
    [LocallyOfFiniteType q₂] [Flat q₂] (hp₁ : p₁ ≫ sV₁ = sW) (hp₂ : p₂ ≫ sV₂ = sW)
    (hq₁ : q₁ ≫ sV₁ = sW') (hq₂ : q₂ ≫ sV₂ = sW') (hc₁ : Ψ ≫ q₁ = p₁) (hc₂ : Ψ ≫ q₂ = p₂)
    {n₁ n₂ N N' : ℕ} (hp₁d : RelativeDimension p₁ n₁) (hp₂d : RelativeDimension p₂ n₂)
    (hq₁d : RelativeDimension q₁ n₁) (hq₂d : RelativeDimension q₂ n₂)
    (hN : RelativeDimension sW N) (hN' : RelativeDimension sW' N') (hNN : N = N') (i j : ℤ)
    (a : chowGroup (fieldChowSituation k) sV₁ i) (b : chowGroup (fieldChowSituation k) sV₂ j) :
    chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ ((i + n₁) + (j + n₂) - N)
        (μ sW N (canonicalDiagonalClassFamily k sW N hN) (i + n₁) (j + n₂)
          (pb[sW, sV₁, p₁, hp₁, n₁, hp₁d, i] a) (pb[sW, sV₂, p₂, hp₂, n₂, hp₂d, j] b)) ≍
      μ sW' N' (canonicalDiagonalClassFamily k sW' N' hN') (i + n₁) (j + n₂)
        (pb[sW', sV₁, q₁, hq₁, n₁, hq₁d, i] a) (pb[sW', sV₂, q₂, hq₂, n₂, hq₂d, j] b) := by
  subst hNN
  refine heq_of_eq ?_
  rw [chowPushforwardOfIso_selfIntersectionProduct k sW sW' Ψ hΨ hN hN',
    chowPushforwardOfIso_flatPullbackChow k sW sW' sV₁ Ψ hΨ p₁ q₁ hp₁ hq₁ hc₁ hp₁d hq₁d,
    chowPushforwardOfIso_flatPullbackChow k sW sW' sV₂ Ψ hΨ p₂ q₂ hp₂ hq₂ hc₂ hp₂d hq₂d]

end Transport

/-! ### Commutativity -/

section Symm

variable {A A' B B' : Scheme.{u}}
  (sA : A ⟶ (fieldChowSituation k).S) (sA' : A' ⟶ (fieldChowSituation k).S)
  (sB : B ⟶ (fieldChowSituation k).S) (sB' : B' ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB'] [Smooth sA] [Smooth sA'] [Smooth sB] [Smooth sB']
  [IsSeparated sA] [IsSeparated sA'] [IsSeparated sB] [IsSeparated sB']

/-- The factor switch of `(A × A') × (B × B')`, as a morphism to `(A' × A) × (B' × B)`. -/
abbrev tensorSwap : tensorProduct sA sA' sB sB' ⟶ tensorProduct sA' sA sB' sB :=
  prodHom (prodBase sA' sA) (prodBase sB' sB) (prodBase sA sA') (prodBase sB sB')
    (pullbackSymmetry sA sA').hom (pullbackSymmetry sB sB').hom
    (pullbackSymmetry_hom_comp_base sA sA') (pullbackSymmetry_hom_comp_base sB sB')

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB'] [Smooth sA] [Smooth sA'] [Smooth sB] [Smooth sB'] [IsSeparated sA]
  [IsSeparated sA'] [IsSeparated sB] [IsSeparated sB'] in
/-- The factor switch followed by `pr₂₄ : (A' × A) × (B' × B) ⟶ A × B` is
`pr₁₃ : (A × A') × (B × B') ⟶ A × B`. -/
theorem tensorSwap_tensorPr₂₄ :
    tensorSwap k sA sA' sB sB' ≫ tensorPr₂₄ sA' sA sB' sB = tensorPr₁₃ sA sA' sB sB' := by
  apply Limits.pullback.hom_ext <;> simp [tensorSwap]

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB'] [Smooth sA] [Smooth sA'] [Smooth sB] [Smooth sB'] [IsSeparated sA]
  [IsSeparated sA'] [IsSeparated sB] [IsSeparated sB'] in
/-- The factor switch followed by `pr₁₃ : (A' × A) × (B' × B) ⟶ A' × B'` is
`pr₂₄ : (A × A') × (B × B') ⟶ A' × B'`. -/
theorem tensorSwap_tensorPr₁₃ :
    tensorSwap k sA sA' sB sB' ≫ tensorPr₁₃ sA' sA sB' sB = tensorPr₂₄ sA sA' sB sB' := by
  apply Limits.pullback.hom_ext <;> simp [tensorSwap]

omit [IsSeparated sA] [IsSeparated sA'] [IsSeparated sB] [IsSeparated sB'] in
/-- **Commutativity of the tensor product of correspondences** up to the factor switches. -/
theorem tensorInt_symm : TensorIntSymm k sA sA' sB sB' := by
  intro d d' e e' hA hA' hB hB' r r' x x'
  have hT := tensorInt_heq k sA sA' sB sB' (Δ := canonicalDiagonalClassFamily k) hA hA' hB hB'
    r r' x x'
  have hT' := tensorInt_heq k sA' sA sB' sB (Δ := canonicalDiagonalClassFamily k) hA' hA hB' hB
    r' r x' x
  refine (chowPushforwardOfIso_heq_congr _ _ _ _ _ (by push_cast; ring) _ _ hT).trans ?_
  refine HEq.trans ?_ hT'.symm
  refine (chowPushforwardOfIso_selfIntersectionProduct_heq k _ _ _ _ (tensorSwap k sA sA' sB sB')
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _ _ _ _ (tensorPr₁₃_comp_prodBase sA sA' sB sB')
    (tensorPr₂₄_comp_prodBase sA sA' sB sB') (tensorPr₂₄_comp_prodBase sA' sA sB' sB)
    (tensorPr₁₃_comp_prodBase sA' sA sB' sB)
    (tensorSwap_tensorPr₂₄ k sA sA' sB sB') (tensorSwap_tensorPr₁₃ k sA sA' sB sB') _ _
    (relativeDimension_tensorPr₂₄ k sA' sA sB' sB hA' hB')
    (relativeDimension_tensorPr₁₃ k sA' sA sB' sB hA hB)
    (relativeDimension_tensorBase k sA sA' sB sB' hA hA' hB hB')
    (relativeDimension_tensorBase k sA' sA sB' sB hA' hA hB' hB) (by ring) _ _ x x').trans ?_
  refine (heq_of_eq (canonicalDiagonalClassFamily_isSymmetric k _ _ _ _ _ _ _)).trans ?_
  exact chowGroupDegreeEquiv_heq _ _ _ _

end Symm

/-! ### The unit -/

section Unit

local notation "μ" =>
  selfIntersectionProduct (fieldChowSituation k)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k)

local notation "pb[" sA ", " sB ", " v ", " hv ", " r ", " hr ", " n "]" =>
  flatPullbackChow (fieldChowSituation k) sA sB v hv r hr n
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)

/-- Casting a Chow class along an equality of degrees `a = b` gives a heterogeneously equal
class. -/
theorem chowGroupCast_heq_self {X : Scheme.{u}} (q : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType q] {a b : ℤ} (h : a = b) (x : chowGroup (fieldChowSituation k) q a) :
    chowGroupCast (fieldChowSituation k) q h x ≍ x := by
  subst h
  rfl

/-- The fundamental classes of `X` in degrees `a` and `b` are heterogeneously equal when
`a = b`. -/
theorem fundamentalChowClass_heq_of_degree_eq {X : Scheme.{u}}
    (q : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] {a b : ℤ} (h : a = b) :
    fundamentalChowClass (fieldChowSituation k) q a ≍
      fundamentalChowClass (fieldChowSituation k) q b := by
  subst h
  rfl

/-- Flat pullback along the identity, of relative dimension `0`, is the identity. -/
theorem flatPullbackChow_id_heq {X : Scheme.{u}} (q : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType q] {n : ℕ} (h0 : n = 0) (hn : RelativeDimension (𝟙 X) n) (i : ℤ)
    (x : chowGroup (fieldChowSituation k) q i) :
    pb[q, q, 𝟙 X, Category.id_comp q, n, hn, i] x ≍ x := by
  subst h0
  exact (heq_of_eq (flatPullbackChow_id (fieldChowSituation k) q i x)).trans
    (chowGroupCast_heq_self k q _ x)

variable {P : Scheme.{u}} (sP : P ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sP]
  [IsSeparated sP]

/-- For `P ≅ Spec k` the diagonal of `P` is all of `P × P`: `[Δ_P] = [P × P]`. -/
theorem diagonalChowClass_eq_fundamentalChowClass [IsIso sP] (n : ℤ) :
    diagonalChowClass k sP n = fundamentalChowClass (fieldChowSituation k) (prodBase sP sP) n := by
  have : IsIso (graphMorphism sP sP (𝟙 P) (Category.id_comp _)) := by
    rw [IsIso.eq_inv_of_inv_hom_id (graphMorphism_snd sP sP (𝟙 P) (Category.id_comp _))]
    infer_instance
  exact congrArg (QuotientAddGroup.mk' _) (cycleAssociatedToClosedSubscheme_eq_of_iso
    (fieldChowSituation k) (prodBase sP sP) (graphMorphism sP sP (𝟙 P) (Category.id_comp _))
    (𝟙 _) (asIso (graphMorphism sP sP (𝟙 P) (Category.id_comp _))) (Category.comp_id _) n)

/-- For `P ≅ Spec k`, `[Δ_P]` pulled back along a flat morphism `f : W ⟶ P × P` is the
fundamental class of `W`. -/
theorem flatPullbackChow_diagonalChowClass [IsIso sP] [Smooth sP] {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] (f : W ⟶ Limits.pullback sP sP)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ prodBase sP sP = sW) {n : ℕ}
    (hfn : RelativeDimension f n) (hP : RelativeDimension sP 0) :
    pb[sW, prodBase sP sP, f, hf, n, hfn, ((0 : ℕ) : ℤ) - 0] (diagonalChowClass k sP _) =
      fundamentalChowClass (fieldChowSituation k) sW (((0 : ℕ) : ℤ) - 0 + (n : ℤ)) := by
  rw [diagonalChowClass_eq_fundamentalChowClass]
  refine flatPullbackChow_fundamentalChowClass (fieldChowSituation k) _ _ _ _ _ _ _ _ ?_
  simpa using schemeDeltaDimension_le_of_relativeDimension (prodBase sP sP)
    (relativeDimension_prodBase k sP sP hP hP)

/-- Transporting a flat pullback of relative dimension `0` along an isomorphism `Ψ = p` to its
target returns the class. -/
private theorem chowPushforwardOfIso_flatPullbackChow_self_heq {W V : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
    (sV : V ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV]
    (Ψ : W ⟶ V) [IsIso Ψ] (hΨ : Ψ ≫ sV = sW) (p : W ⟶ V) [LocallyOfFiniteType p] [Flat p]
    (hp : p ≫ sV = sW) (hc : Ψ = p) {n : ℕ} (h0 : n = 0) (hpd : RelativeDimension p n) (i : ℤ)
    (x : chowGroup (fieldChowSituation k) sV i) :
    chowPushforwardOfIso (fieldChowSituation k) sW sV Ψ hΨ (i + n)
        (pb[sW, sV, p, hp, n, hpd, i] x) ≍ x := by
  subst h0
  rw [chowPushforwardOfIso_flatPullbackChow k sW sV sV Ψ hΨ p (𝟙 _) hp (Category.id_comp _)
    ((Category.comp_id _).trans hc) hpd (relativeDimension_identity _)]
  exact flatPullbackChow_id_heq k _ rfl _ _ x

variable {A B : Scheme.{u}} (sA : A ⟶ (fieldChowSituation k).S)
  (sB : B ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sA] [LocallyOfFiniteType sB]
  [Smooth sA] [Smooth sB] [IsSeparated sA] [IsSeparated sB] [Smooth sP]

/-- **`[Δ_P]` is a right unit for the tensor product of correspondences**, for `P ≅ Spec k`. -/
theorem tensorInt_rightUnit : TensorIntRightUnit k sA sB sP := by
  intro _ d e hA hB hP r x
  have hT := tensorInt_heq k sA sP sB sP (Δ := canonicalDiagonalClassFamily k) hA hP hB hP r 0 x
    (diagonalChowClass k sP _)
  have hN := relativeDimension_tensorBase k sA sP sB sP hA hP hB hP
  have hc : prodHom sA sB (prodBase sA sP) (prodBase sB sP) (Limits.pullback.fst sA sP)
      (Limits.pullback.fst sB sP) rfl rfl = tensorPr₁₃ sA sP sB sP := by
    apply Limits.pullback.hom_ext <;> simp
  have H2 : μ (tensorBase sA sP sB sP) _ (canonicalDiagonalClassFamily k _ _ hN)
      (((e : ℤ) - r) + ((0 + 0 : ℕ) : ℤ)) ((((0 : ℕ) : ℤ) - 0) + ((e + d : ℕ) : ℤ))
      (pb[tensorBase sA sP sB sP, prodBase sA sB, tensorPr₁₃ sA sP sB sP,
        tensorPr₁₃_comp_prodBase sA sP sB sP, 0 + 0,
        relativeDimension_tensorPr₁₃ k sA sP sB sP hP hP, (e : ℤ) - r] x)
      (pb[tensorBase sA sP sB sP, prodBase sP sP, tensorPr₂₄ sA sP sB sP,
        tensorPr₂₄_comp_prodBase sA sP sB sP, e + d,
        relativeDimension_tensorPr₂₄ k sA sP sB sP hA hB, ((0 : ℕ) : ℤ) - 0]
        (diagonalChowClass k sP _)) ≍
      pb[tensorBase sA sP sB sP, prodBase sA sB, tensorPr₁₃ sA sP sB sP,
        tensorPr₁₃_comp_prodBase sA sP sB sP, 0 + 0,
        relativeDimension_tensorPr₁₃ k sA sP sB sP hP hP, (e : ℤ) - r] x := by
    refine (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl
      (m' := ((0 + e + (0 + d) : ℕ) : ℤ)) (by push_cast; ring) HEq.rfl
      ((heq_of_eq (flatPullbackChow_diagonalChowClass k sP _ _ _
        (relativeDimension_tensorPr₂₄ k sA sP sB sP hA hB) hP)).trans
        (fundamentalChowClass_heq_of_degree_eq k _ (by push_cast; ring)))).trans ?_
    rw [selfIntersectionProduct_fundamentalChowClass_right]
    exact chowGroupDegreeEquiv_heq _ _ _ _
  refine (chowPushforwardOfIso_heq_congr _ _ _ _ _ (by push_cast; ring) _ _ (hT.trans H2)).trans ?_
  exact chowPushforwardOfIso_flatPullbackChow_self_heq k _ _ _ _ _
    (tensorPr₁₃_comp_prodBase sA sP sB sP) hc rfl
    (relativeDimension_tensorPr₁₃ k sA sP sB sP hP hP) _ x

/-- **`[Δ_P]` is a left unit for the tensor product of correspondences**, for `P ≅ Spec k`. -/
theorem tensorInt_leftUnit : TensorIntLeftUnit k sA sB sP := by
  intro _ d e hA hB hP r x
  have hT := tensorInt_heq k sP sA sP sB (Δ := canonicalDiagonalClassFamily k) hP hA hP hB 0 r
    (diagonalChowClass k sP _) x
  have hN := relativeDimension_tensorBase k sP sA sP sB hP hA hP hB
  have hc : prodHom sA sB (prodBase sP sA) (prodBase sP sB) (Limits.pullback.snd sP sA)
      (Limits.pullback.snd sP sB) Limits.pullback.condition.symm Limits.pullback.condition.symm =
        tensorPr₂₄ sP sA sP sB := by
    apply Limits.pullback.hom_ext <;> simp
  have H2 : μ (tensorBase sP sA sP sB) _ (canonicalDiagonalClassFamily k _ _ hN)
      ((((0 : ℕ) : ℤ) - 0) + ((e + d : ℕ) : ℤ)) (((e : ℤ) - r) + ((0 + 0 : ℕ) : ℤ))
      (pb[tensorBase sP sA sP sB, prodBase sP sP, tensorPr₁₃ sP sA sP sB,
        tensorPr₁₃_comp_prodBase sP sA sP sB, e + d,
        relativeDimension_tensorPr₁₃ k sP sA sP sB hA hB, ((0 : ℕ) : ℤ) - 0]
        (diagonalChowClass k sP _))
      (pb[tensorBase sP sA sP sB, prodBase sA sB, tensorPr₂₄ sP sA sP sB,
        tensorPr₂₄_comp_prodBase sP sA sP sB, 0 + 0,
        relativeDimension_tensorPr₂₄ k sP sA sP sB hP hP, (e : ℤ) - r] x) ≍
      pb[tensorBase sP sA sP sB, prodBase sA sB, tensorPr₂₄ sP sA sP sB,
        tensorPr₂₄_comp_prodBase sP sA sP sB, 0 + 0,
        relativeDimension_tensorPr₂₄ k sP sA sP sB hP hP, (e : ℤ) - r] x := by
    refine (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl
      (n' := ((e + 0 + (d + 0) : ℕ) : ℤ)) (by push_cast; ring) rfl
      ((heq_of_eq (flatPullbackChow_diagonalChowClass k sP _ _ _
        (relativeDimension_tensorPr₁₃ k sP sA sP sB hA hB) hP)).trans
        (fundamentalChowClass_heq_of_degree_eq k _ (by push_cast; ring))) HEq.rfl).trans ?_
    rw [selfIntersectionProduct_fundamentalChowClass_left]
    exact chowGroupDegreeEquiv_heq _ _ _ _
  refine (chowPushforwardOfIso_heq_congr _ _ _ _ _ (by push_cast; ring) _ _ (hT.trans H2)).trans ?_
  exact chowPushforwardOfIso_flatPullbackChow_self_heq k _ _ _ _ _
    (tensorPr₂₄_comp_prodBase sP sA sP sB) hc rfl
    (relativeDimension_tensorPr₂₄ k sP sA sP sB hP hP) _ x

end Unit

/-! ### Associativity -/

section Assoc

local notation "μ" =>
  selfIntersectionProduct (fieldChowSituation k)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k)

local notation "pb[" sA ", " sB ", " v ", " hv ", " r ", " hr ", " n "]" =>
  flatPullbackChow (fieldChowSituation k) sA sB v hv r hr n
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)

/-- `Stacks.WeilCohomology.chowPushforwardOfIso_flatPullbackChow` with the two relative
dimensions written differently. -/
theorem chowPushforwardOfIso_flatPullbackChow_heq {W W' V : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
    (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW']
    (sV : V ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV]
    (Ψ : W ⟶ W') [IsIso Ψ] (hΨ : Ψ ≫ sW' = sW) (p : W ⟶ V) [LocallyOfFiniteType p] [Flat p]
    (q : W' ⟶ V) [LocallyOfFiniteType q] [Flat q] (hp : p ≫ sV = sW) (hq : q ≫ sV = sW')
    (hc : Ψ ≫ q = p) {n n' : ℕ} (hnn : n = n') (hpd : RelativeDimension p n)
    (hqd : RelativeDimension q n') (i : ℤ) (a : chowGroup (fieldChowSituation k) sV i) :
    chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ (i + n)
        (pb[sW, sV, p, hp, n, hpd, i] a) ≍
      pb[sW', sV, q, hq, n', hqd, i] a := by
  subst hnn
  exact heq_of_eq (chowPushforwardOfIso_flatPullbackChow k sW sW' sV Ψ hΨ p q hp hq hc hpd hqd i a)

/-- **Transport of a product along an isomorphism**: `Ψ_*(x · y) = Ψ_* x · Ψ_* y`, for the
canonical diagonal classes. -/
theorem chowPushforwardOfIso_selfIntersectionProduct_heq' {W W' : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW'] [Smooth sW']
    (Ψ : W ⟶ W') [IsIso Ψ] (hΨ : Ψ ≫ sW' = sW) {N N' : ℕ} (hN : RelativeDimension sW N)
    (hN' : RelativeDimension sW' N') (hNN : N = N') (a b : ℤ)
    (x : chowGroup (fieldChowSituation k) sW a) (y : chowGroup (fieldChowSituation k) sW b) :
    chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ (a + b - N)
        (μ sW N (canonicalDiagonalClassFamily k sW N hN) a b x y) ≍
      μ sW' N' (canonicalDiagonalClassFamily k sW' N' hN') a b
        (chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ a x)
        (chowPushforwardOfIso (fieldChowSituation k) sW sW' Ψ hΨ b y) := by
  subst hNN
  exact heq_of_eq (chowPushforwardOfIso_selfIntersectionProduct k sW sW' Ψ hΨ hN hN' a b x y)

/-- **Flat pullback of a product of pulled back classes**, for the canonical diagonal classes:
`h^*(q₁^* a · q₂^* b) = (h ≫ q₁)^* a · (h ≫ q₂)^* b`. -/
theorem flatPullbackChow_selfIntersectionProduct_comp_heq {V W V₁ V₂ : Scheme.{u}}
    (sV : V ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV] [Smooth sV]
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW]
    (sV₁ : V₁ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV₁]
    (sV₂ : V₂ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV₂]
    (h : W ⟶ V) [LocallyOfFiniteType h] [Flat h] (q₁ : V ⟶ V₁) [LocallyOfFiniteType q₁]
    [Flat q₁] (q₂ : V ⟶ V₂) [LocallyOfFiniteType q₂] [Flat q₂] (hh : h ≫ sV = sW)
    (hq₁ : q₁ ≫ sV₁ = sV) (hq₂ : q₂ ≫ sV₂ = sV) {t n₁ n₂ N M : ℕ}
    (ht : RelativeDimension h t) (hq₁d : RelativeDimension q₁ n₁)
    (hq₂d : RelativeDimension q₂ n₂) (hN : RelativeDimension sV N)
    (hM : RelativeDimension sW M) (eM : M = t + N) (i j : ℤ)
    (a : chowGroup (fieldChowSituation k) sV₁ i) (b : chowGroup (fieldChowSituation k) sV₂ j) :
    pb[sW, sV, h, hh, t, ht, (i + n₁) + (j + n₂) - N]
        (μ sV N (canonicalDiagonalClassFamily k sV N hN) (i + n₁) (j + n₂)
          (pb[sV, sV₁, q₁, hq₁, n₁, hq₁d, i] a) (pb[sV, sV₂, q₂, hq₂, n₂, hq₂d, j] b)) ≍
      μ sW M (canonicalDiagonalClassFamily k sW M hM) (i + ((t + n₁ : ℕ) : ℤ))
        (j + ((t + n₂ : ℕ) : ℤ))
        (pb[sW, sV₁, h ≫ q₁, (by rw [Category.assoc, hq₁, hh]), t + n₁,
          RelativeDimension.comp_of_flat h q₁ ht hq₁d, i] a)
        (pb[sW, sV₂, h ≫ q₂, (by rw [Category.assoc, hq₂, hh]), t + n₂,
          RelativeDimension.comp_of_flat h q₂ ht hq₂d, j] b) := by
  refine (DiagonalClassFamily.FlatPullbackMul.heq (canonicalDiagonalClassFamily_flatPullbackMul k)
    sV sW h hh eM ht hN hM _ _ _ _).trans ?_
  exact selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by push_cast; ring) (by push_cast; ring)
    (flatPullbackChow_comp _ sW sV sV₁ h q₁ hh hq₁ t n₁ ht hq₁d i _ _ _ a)
    (flatPullbackChow_comp _ sW sV sV₂ h q₂ hh hq₂ t n₂ ht hq₂d j _ _ _ b)

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Scheme.{u}}
  (sA₁ : A₁ ⟶ (fieldChowSituation k).S) (sA₂ : A₂ ⟶ (fieldChowSituation k).S)
  (sA₃ : A₃ ⟶ (fieldChowSituation k).S) (sB₁ : B₁ ⟶ (fieldChowSituation k).S)
  (sB₂ : B₂ ⟶ (fieldChowSituation k).S) (sB₃ : B₃ ⟶ (fieldChowSituation k).S)
  (φA : Limits.pullback (prodBase sA₁ sA₂) sA₃ ⟶ Limits.pullback sA₁ (prodBase sA₂ sA₃))
  (φB : Limits.pullback (prodBase sB₁ sB₂) sB₃ ⟶ Limits.pullback sB₁ (prodBase sB₂ sB₃))
  (hφA₁ : φA ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
  (hφA₂ : φA ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
    Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _)
  (hφA₃ : φA ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _)
  (hφB₁ : φB ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
  (hφB₂ : φB ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
    Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _)
  (hφB₃ : φB ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _)

/-- The associativity isomorphism of the sixfold product, `φA × φB`. -/
abbrev tensorAssocHom :
    tensorProduct (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ ⟶
      tensorProduct sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) :=
  prodHom (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃))
    (prodBase (prodBase sA₁ sA₂) sA₃) (prodBase (prodBase sB₁ sB₂) sB₃) φA φB
    (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁)

/-- Under `φA × φB`, the projection to `A₁ × B₁` of `A₁ × (A₂ × A₃)` and `B₁ × (B₂ × B₃)` agrees
with the projection to `A₁ × B₁` of `(A₁ × A₂) × A₃` and `(B₁ × B₂) × B₃`. -/
theorem tensorAssocHom_pr₁ :
    tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁ ≫
        tensorPr₁₃ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) =
      tensorPr₁₃ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ ≫ tensorPr₁₃ sA₁ sA₂ sB₁ sB₂ := by
  apply Limits.pullback.hom_ext
  · simp [tensorAssocHom, hφA₁]
  · simp [tensorAssocHom, hφB₁]

include hφA₂ hφB₂ in
/-- Under `φA × φB`, the projection to `A₂ × B₂` of `A₁ × (A₂ × A₃)` and `B₁ × (B₂ × B₃)` agrees
with the projection to `A₂ × B₂` of `(A₁ × A₂) × A₃` and `(B₁ × B₂) × B₃`. -/
theorem tensorAssocHom_pr₂ :
    tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁ ≫
        tensorPr₂₄ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) ≫ tensorPr₁₃ sA₂ sA₃ sB₂ sB₃ =
      tensorPr₁₃ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ ≫ tensorPr₂₄ sA₁ sA₂ sB₁ sB₂ := by
  apply Limits.pullback.hom_ext
  · simp [tensorAssocHom, hφA₂]
  · simp [tensorAssocHom, hφB₂]

include hφA₃ hφB₃ in
/-- Under `φA × φB`, the projection to `A₃ × B₃` of `A₁ × (A₂ × A₃)` and `B₁ × (B₂ × B₃)` agrees
with the projection to `A₃ × B₃` of `(A₁ × A₂) × A₃` and `(B₁ × B₂) × B₃`. -/
theorem tensorAssocHom_pr₃ :
    tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁ ≫
        tensorPr₂₄ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) ≫ tensorPr₂₄ sA₂ sA₃ sB₂ sB₃ =
      tensorPr₂₄ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ := by
  apply Limits.pullback.hom_ext
  · simp [tensorAssocHom, hφA₃]
  · simp [tensorAssocHom, hφB₃]

end Assoc

section AssocMain

local notation "μ" =>
  selfIntersectionProduct (fieldChowSituation k)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k)

local notation "pb[" sA ", " sB ", " v ", " hv ", " r ", " hr ", " n "]" =>
  flatPullbackChow (fieldChowSituation k) sA sB v hv r hr n
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Scheme.{u}}
  (sA₁ : A₁ ⟶ (fieldChowSituation k).S) (sA₂ : A₂ ⟶ (fieldChowSituation k).S)
  (sA₃ : A₃ ⟶ (fieldChowSituation k).S) (sB₁ : B₁ ⟶ (fieldChowSituation k).S)
  (sB₂ : B₂ ⟶ (fieldChowSituation k).S) (sB₃ : B₃ ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sA₁] [LocallyOfFiniteType sA₂] [LocallyOfFiniteType sA₃]
  [LocallyOfFiniteType sB₁] [LocallyOfFiniteType sB₂] [LocallyOfFiniteType sB₃]
  [Smooth sA₁] [Smooth sA₂] [Smooth sA₃] [Smooth sB₁] [Smooth sB₂] [Smooth sB₃]
  [IsSeparated sA₁] [IsSeparated sA₂] [IsSeparated sA₃] [IsSeparated sB₁] [IsSeparated sB₂]
  [IsSeparated sB₃]

omit [LocallyOfFiniteType sA₁] [LocallyOfFiniteType sA₂] [LocallyOfFiniteType sA₃]
  [LocallyOfFiniteType sB₁] [LocallyOfFiniteType sB₂] [LocallyOfFiniteType sB₃]
  [Smooth sA₁] [Smooth sA₂] [Smooth sA₃] [Smooth sB₁] [Smooth sB₂] [Smooth sB₃]
  [IsSeparated sA₁] [IsSeparated sA₂] [IsSeparated sA₃] [IsSeparated sB₁] [IsSeparated sB₂]
  [IsSeparated sB₃] in
/-- The projection of `((A₁ × A₂) × A₃) × ((B₁ × B₂) × B₃)` to `A₁ × B₁` commutes with the
structure morphisms to `S`. -/
theorem assoc_hp₁ : (tensorPr₁₃ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ ≫
    tensorPr₁₃ sA₁ sA₂ sB₁ sB₂) ≫ prodBase sA₁ sB₁ =
    tensorBase (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ := by
  rw [Category.assoc, tensorPr₁₃_comp_prodBase, tensorPr₁₃_comp_prodBase]

omit [LocallyOfFiniteType sA₁] [LocallyOfFiniteType sA₂] [LocallyOfFiniteType sA₃]
  [LocallyOfFiniteType sB₁] [LocallyOfFiniteType sB₂] [LocallyOfFiniteType sB₃]
  [Smooth sA₁] [Smooth sA₂] [Smooth sA₃] [Smooth sB₁] [Smooth sB₂] [Smooth sB₃]
  [IsSeparated sA₁] [IsSeparated sA₂] [IsSeparated sA₃] [IsSeparated sB₁] [IsSeparated sB₂]
  [IsSeparated sB₃] in
/-- The projection of `((A₁ × A₂) × A₃) × ((B₁ × B₂) × B₃)` to `A₂ × B₂` commutes with the
structure morphisms to `S`. -/
theorem assoc_hp₂ : (tensorPr₁₃ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ ≫
    tensorPr₂₄ sA₁ sA₂ sB₁ sB₂) ≫ prodBase sA₂ sB₂ =
    tensorBase (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ := by
  rw [Category.assoc, tensorPr₂₄_comp_prodBase, tensorPr₁₃_comp_prodBase]

omit [LocallyOfFiniteType sA₁] [LocallyOfFiniteType sA₂] [LocallyOfFiniteType sA₃]
  [LocallyOfFiniteType sB₁] [LocallyOfFiniteType sB₂] [LocallyOfFiniteType sB₃]
  [Smooth sA₁] [Smooth sA₂] [Smooth sA₃] [Smooth sB₁] [Smooth sB₂] [Smooth sB₃]
  [IsSeparated sA₁] [IsSeparated sA₂] [IsSeparated sA₃] [IsSeparated sB₁] [IsSeparated sB₂]
  [IsSeparated sB₃] in
/-- The projection of `(A₁ × (A₂ × A₃)) × (B₁ × (B₂ × B₃))` to `A₂ × B₂` commutes with the
structure morphisms to `S`. -/
theorem assoc_hq₂ : (tensorPr₂₄ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) ≫
    tensorPr₁₃ sA₂ sA₃ sB₂ sB₃) ≫ prodBase sA₂ sB₂ =
    tensorBase sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) := by
  rw [Category.assoc, tensorPr₁₃_comp_prodBase, tensorPr₂₄_comp_prodBase]

omit [LocallyOfFiniteType sA₁] [LocallyOfFiniteType sA₂] [LocallyOfFiniteType sA₃]
  [LocallyOfFiniteType sB₁] [LocallyOfFiniteType sB₂] [LocallyOfFiniteType sB₃]
  [Smooth sA₁] [Smooth sA₂] [Smooth sA₃] [Smooth sB₁] [Smooth sB₂] [Smooth sB₃]
  [IsSeparated sA₁] [IsSeparated sA₂] [IsSeparated sA₃] [IsSeparated sB₁] [IsSeparated sB₂]
  [IsSeparated sB₃] in
/-- The projection of `(A₁ × (A₂ × A₃)) × (B₁ × (B₂ × B₃))` to `A₃ × B₃` commutes with the
structure morphisms to `S`. -/
theorem assoc_hq₃ : (tensorPr₂₄ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) ≫
    tensorPr₂₄ sA₂ sA₃ sB₂ sB₃) ≫ prodBase sA₃ sB₃ =
    tensorBase sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) := by
  rw [Category.assoc, tensorPr₂₄_comp_prodBase, tensorPr₂₄_comp_prodBase]

variable {d₁ d₂ d₃ e₁ e₂ e₃ : ℕ} (hA₁ : RelativeDimension sA₁ d₁)
  (hA₂ : RelativeDimension sA₂ d₂) (hA₃ : RelativeDimension sA₃ d₃)
  (hB₁ : RelativeDimension sB₁ e₁) (hB₂ : RelativeDimension sB₂ e₂)
  (hB₃ : RelativeDimension sB₃ e₃)

/-- The left side of associativity, unfolded:
`(x₁ ⊗ x₂) ⊗ x₃ = (π₁^* x₁ · π₂^* x₂) · π₃^* x₃` on `((A₁ × A₂) × A₃) × ((B₁ × B₂) × B₃)`. -/
theorem tensorInt_tensorInt_left_heq (r₁ r₂ r₃ : ℤ)
    (x₁ : chowGroup (fieldChowSituation k) (prodBase sA₁ sB₁) ((e₁ : ℤ) - r₁))
    (x₂ : chowGroup (fieldChowSituation k) (prodBase sA₂ sB₂) ((e₂ : ℤ) - r₂))
    (x₃ : chowGroup (fieldChowSituation k) (prodBase sA₃ sB₃) ((e₃ : ℤ) - r₃)) :
    tensorInt k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (canonicalDiagonalClassFamily k)
        (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂) hA₃
        (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂) hB₃ (r₁ + r₂) r₃
        (tensorInt k sA₁ sA₂ sB₁ sB₂ (canonicalDiagonalClassFamily k) hA₁ hA₂ hB₁ hB₂ r₁ r₂
          x₁ x₂) x₃ ≍
      μ _ _ (canonicalDiagonalClassFamily k _ _ (relativeDimension_tensorBase k
          (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃
          (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂) hA₃
          (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂) hB₃)) _ _
        (μ _ _ (canonicalDiagonalClassFamily k _ _ (relativeDimension_tensorBase k
            (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃
            (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂) hA₃
            (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂) hB₃)) _ _
          (pb[_, _, _, assoc_hp₁ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃, _, RelativeDimension.comp_of_flat _ _
            (relativeDimension_tensorPr₁₃ k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ hA₃ hB₃)
            (relativeDimension_tensorPr₁₃ k sA₁ sA₂ sB₁ sB₂ hA₂ hB₂), (e₁ : ℤ) - r₁] x₁)
          (pb[_, _, _, assoc_hp₂ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃, _, RelativeDimension.comp_of_flat _ _
            (relativeDimension_tensorPr₁₃ k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ hA₃ hB₃)
            (relativeDimension_tensorPr₂₄ k sA₁ sA₂ sB₁ sB₂ hA₁ hB₁), (e₂ : ℤ) - r₂] x₂))
        (pb[_, _, tensorPr₂₄ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃,
          tensorPr₂₄_comp_prodBase _ _ _ _, _, relativeDimension_tensorPr₂₄ k (prodBase sA₁ sA₂)
            sA₃ (prodBase sB₁ sB₂) sB₃ (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂)
            (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂), (e₃ : ℤ) - r₃] x₃) := by
  have hA₁₂ := relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂
  have hB₁₂ := relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂
  have hNW := relativeDimension_tensorBase k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃
    hA₁₂ hA₃ hB₁₂ hB₃
  have hL := tensorInt_heq k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃
    (Δ := canonicalDiagonalClassFamily k) hA₁₂ hA₃ hB₁₂ hB₃ (r₁ + r₂) r₃
    (tensorInt k sA₁ sA₂ sB₁ sB₂ (canonicalDiagonalClassFamily k) hA₁ hA₂ hB₁ hB₂ r₁ r₂ x₁ x₂) x₃
  have hL₁ := tensorInt_heq k sA₁ sA₂ sB₁ sB₂ (Δ := canonicalDiagonalClassFamily k)
    hA₁ hA₂ hB₁ hB₂ r₁ r₂ x₁ x₂
  have hLx := (flatPullbackChow_heq_congr (fieldChowSituation k) _ _
    (tensorPr₁₃ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃)
    (tensorPr₁₃ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃)
    (tensorPr₁₃_comp_prodBase _ _ _ _) (tensorPr₁₃_comp_prodBase _ _ _ _) rfl rfl
    (relativeDimension_tensorPr₁₃ k _ _ _ _ hA₃ hB₃)
    (relativeDimension_tensorPr₁₃ k _ _ _ _ hA₃ hB₃) (by push_cast; ring)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) _ _ hL₁).trans
    (flatPullbackChow_selfIntersectionProduct_comp_heq k _ _ _ _
      (tensorPr₁₃ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃) (tensorPr₁₃ sA₁ sA₂ sB₁ sB₂)
      (tensorPr₂₄ sA₁ sA₂ sB₁ sB₂) (tensorPr₁₃_comp_prodBase _ _ _ _)
      (tensorPr₁₃_comp_prodBase sA₁ sA₂ sB₁ sB₂) (tensorPr₂₄_comp_prodBase sA₁ sA₂ sB₁ sB₂)
      (relativeDimension_tensorPr₁₃ k _ _ _ _ hA₃ hB₃)
      (relativeDimension_tensorPr₁₃ k sA₁ sA₂ sB₁ sB₂ hA₂ hB₂)
      (relativeDimension_tensorPr₂₄ k sA₁ sA₂ sB₁ sB₂ hA₁ hB₁)
      (relativeDimension_tensorBase k sA₁ sA₂ sB₁ sB₂ hA₁ hA₂ hB₁ hB₂) hNW (by omega) _ _ x₁ x₂)
  exact hL.trans (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by push_cast; ring) rfl
    hLx HEq.rfl)

/-- The right side of associativity, unfolded:
`x₁ ⊗ (x₂ ⊗ x₃) = π₁'^* x₁ · (π₂'^* x₂ · π₃'^* x₃)` on `(A₁ × (A₂ × A₃)) × (B₁ × (B₂ × B₃))`. -/
theorem tensorInt_tensorInt_right_heq (r₁ r₂ r₃ : ℤ)
    (x₁ : chowGroup (fieldChowSituation k) (prodBase sA₁ sB₁) ((e₁ : ℤ) - r₁))
    (x₂ : chowGroup (fieldChowSituation k) (prodBase sA₂ sB₂) ((e₂ : ℤ) - r₂))
    (x₃ : chowGroup (fieldChowSituation k) (prodBase sA₃ sB₃) ((e₃ : ℤ) - r₃)) :
    tensorInt k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) (canonicalDiagonalClassFamily k)
        hA₁ (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃) hB₁
        (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃) r₁ (r₂ + r₃) x₁
        (tensorInt k sA₂ sA₃ sB₂ sB₃ (canonicalDiagonalClassFamily k) hA₂ hA₃ hB₂ hB₃ r₂ r₃
          x₂ x₃) ≍
      μ _ _ (canonicalDiagonalClassFamily k _ _ (relativeDimension_tensorBase k
          sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁
          (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃) hB₁
          (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃))) _ _
        (pb[_, _, tensorPr₁₃ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃),
          tensorPr₁₃_comp_prodBase _ _ _ _, _, relativeDimension_tensorPr₁₃ k sA₁
            (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃)
            (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃)
            (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃), (e₁ : ℤ) - r₁] x₁)
        (μ _ _ (canonicalDiagonalClassFamily k _ _ (relativeDimension_tensorBase k
            sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁
            (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃) hB₁
            (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃))) _ _
          (pb[_, _, _, assoc_hq₂ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃, _, RelativeDimension.comp_of_flat _ _
            (relativeDimension_tensorPr₂₄ k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁ hB₁)
            (relativeDimension_tensorPr₁₃ k sA₂ sA₃ sB₂ sB₃ hA₃ hB₃), (e₂ : ℤ) - r₂] x₂)
          (pb[_, _, _, assoc_hq₃ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃, _, RelativeDimension.comp_of_flat _ _
            (relativeDimension_tensorPr₂₄ k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁ hB₁)
            (relativeDimension_tensorPr₂₄ k sA₂ sA₃ sB₂ sB₃ hA₂ hB₂), (e₃ : ℤ) - r₃] x₃)) := by
  have hA₂₃ := relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃
  have hB₂₃ := relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃
  have hNW' := relativeDimension_tensorBase k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃)
    hA₁ hA₂₃ hB₁ hB₂₃
  have hR := tensorInt_heq k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃)
    (Δ := canonicalDiagonalClassFamily k) hA₁ hA₂₃ hB₁ hB₂₃ r₁ (r₂ + r₃) x₁
    (tensorInt k sA₂ sA₃ sB₂ sB₃ (canonicalDiagonalClassFamily k) hA₂ hA₃ hB₂ hB₃ r₂ r₃ x₂ x₃)
  have hR₂ := tensorInt_heq k sA₂ sA₃ sB₂ sB₃ (Δ := canonicalDiagonalClassFamily k)
    hA₂ hA₃ hB₂ hB₃ r₂ r₃ x₂ x₃
  have hRy := (flatPullbackChow_heq_congr (fieldChowSituation k) _ _
    (tensorPr₂₄ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃))
    (tensorPr₂₄ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃))
    (tensorPr₂₄_comp_prodBase _ _ _ _) (tensorPr₂₄_comp_prodBase _ _ _ _) rfl rfl
    (relativeDimension_tensorPr₂₄ k _ _ _ _ hA₁ hB₁)
    (relativeDimension_tensorPr₂₄ k _ _ _ _ hA₁ hB₁) (by push_cast; ring)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) _ _ hR₂).trans
    (flatPullbackChow_selfIntersectionProduct_comp_heq k _ _ _ _
      (tensorPr₂₄ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃)) (tensorPr₁₃ sA₂ sA₃ sB₂ sB₃)
      (tensorPr₂₄ sA₂ sA₃ sB₂ sB₃) (tensorPr₂₄_comp_prodBase _ _ _ _)
      (tensorPr₁₃_comp_prodBase sA₂ sA₃ sB₂ sB₃) (tensorPr₂₄_comp_prodBase sA₂ sA₃ sB₂ sB₃)
      (relativeDimension_tensorPr₂₄ k _ _ _ _ hA₁ hB₁)
      (relativeDimension_tensorPr₁₃ k sA₂ sA₃ sB₂ sB₃ hA₃ hB₃)
      (relativeDimension_tensorPr₂₄ k sA₂ sA₃ sB₂ sB₃ hA₂ hB₂)
      (relativeDimension_tensorBase k sA₂ sA₃ sB₂ sB₃ hA₂ hA₃ hB₂ hB₃) hNW' (by omega) _ _ x₂ x₃)
  exact hR.trans (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl (by push_cast; ring)
    HEq.rfl hRy)

variable (φA : Limits.pullback (prodBase sA₁ sA₂) sA₃ ⟶ Limits.pullback sA₁ (prodBase sA₂ sA₃))
  (φB : Limits.pullback (prodBase sB₁ sB₂) sB₃ ⟶ Limits.pullback sB₁ (prodBase sB₂ sB₃))
  [IsIso φA] [IsIso φB]
  (hφA₁ : φA ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
  (hφA₂ : φA ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
    Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _)
  (hφA₃ : φA ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _)
  (hφB₁ : φB ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
  (hφB₂ : φB ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
    Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _)
  (hφB₃ : φB ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _)

include hφA₂ hφA₃ hφB₂ hφB₃ in
/-- The transport of `(π₁^* x₁ · π₂^* x₂) · π₃^* x₃` along the associativity isomorphism is
`(π₁'^* x₁ · π₂'^* x₂) · π₃'^* x₃`. -/
theorem chowPushforwardOfIso_tensorAssocHom_heq (r₁ r₂ r₃ : ℤ)
    (x₁ : chowGroup (fieldChowSituation k) (prodBase sA₁ sB₁) ((e₁ : ℤ) - r₁))
    (x₂ : chowGroup (fieldChowSituation k) (prodBase sA₂ sB₂) ((e₂ : ℤ) - r₂))
    (x₃ : chowGroup (fieldChowSituation k) (prodBase sA₃ sB₃) ((e₃ : ℤ) - r₃)) :
    chowPushforwardOfIso (fieldChowSituation k) _ _
        (tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁)
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _
      (μ _ _ (canonicalDiagonalClassFamily k _ _ (relativeDimension_tensorBase k
          (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃
          (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂) hA₃
          (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂) hB₃)) _ _
        (μ _ _ (canonicalDiagonalClassFamily k _ _ (relativeDimension_tensorBase k
            (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃
            (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂) hA₃
            (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂) hB₃)) _ _
          (pb[_, _, _, assoc_hp₁ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃, _, RelativeDimension.comp_of_flat _ _
            (relativeDimension_tensorPr₁₃ k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ hA₃ hB₃)
            (relativeDimension_tensorPr₁₃ k sA₁ sA₂ sB₁ sB₂ hA₂ hB₂), (e₁ : ℤ) - r₁] x₁)
          (pb[_, _, _, assoc_hp₂ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃, _, RelativeDimension.comp_of_flat _ _
            (relativeDimension_tensorPr₁₃ k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ hA₃ hB₃)
            (relativeDimension_tensorPr₂₄ k sA₁ sA₂ sB₁ sB₂ hA₁ hB₁), (e₂ : ℤ) - r₂] x₂))
        (pb[_, _, tensorPr₂₄ (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃,
          tensorPr₂₄_comp_prodBase _ _ _ _, _, relativeDimension_tensorPr₂₄ k (prodBase sA₁ sA₂)
            sA₃ (prodBase sB₁ sB₂) sB₃ (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂)
            (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂), (e₃ : ℤ) - r₃] x₃)) ≍
      μ _ _ (canonicalDiagonalClassFamily k _ _ (relativeDimension_tensorBase k
          sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁
          (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃) hB₁
          (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃))) _ _
        (μ _ _ (canonicalDiagonalClassFamily k _ _ (relativeDimension_tensorBase k
            sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁
            (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃) hB₁
            (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃))) _ _
          (pb[_, _, tensorPr₁₃ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃),
            tensorPr₁₃_comp_prodBase _ _ _ _, _, relativeDimension_tensorPr₁₃ k sA₁
              (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃)
              (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃)
              (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃), (e₁ : ℤ) - r₁] x₁)
          (pb[_, _, _, assoc_hq₂ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃, _, RelativeDimension.comp_of_flat _ _
            (relativeDimension_tensorPr₂₄ k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁ hB₁)
            (relativeDimension_tensorPr₁₃ k sA₂ sA₃ sB₂ sB₃ hA₃ hB₃), (e₂ : ℤ) - r₂] x₂))
        (pb[_, _, _, assoc_hq₃ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃, _, RelativeDimension.comp_of_flat _ _
          (relativeDimension_tensorPr₂₄ k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁ hB₁)
          (relativeDimension_tensorPr₂₄ k sA₂ sA₃ sB₂ sB₃ hA₂ hB₂), (e₃ : ℤ) - r₃] x₃) := by
  have hNW := relativeDimension_tensorBase k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃
    (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂) hA₃
    (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂) hB₃
  have hNW' := relativeDimension_tensorBase k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁
    (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃) hB₁
    (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃)
  have hΨ : tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁ ≫
      tensorBase sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) =
      tensorBase (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ :=
    prodHom_comp_prodBase _ _ _ _ _ _ _ _
  have hQ₁ := chowPushforwardOfIso_flatPullbackChow_heq k _ _ _
    (tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁) hΨ _
    (tensorPr₁₃ sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃)) (assoc_hp₁ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃)
    (tensorPr₁₃_comp_prodBase _ _ _ _)
    (tensorAssocHom_pr₁ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁)
    (by omega) (RelativeDimension.comp_of_flat _ _
      (relativeDimension_tensorPr₁₃ k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ hA₃ hB₃)
      (relativeDimension_tensorPr₁₃ k sA₁ sA₂ sB₁ sB₂ hA₂ hB₂))
    (relativeDimension_tensorPr₁₃ k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃)
      (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃)
      (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃)) ((e₁ : ℤ) - r₁) x₁
  have hQ₂ := chowPushforwardOfIso_flatPullbackChow_heq k _ _ _
    (tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁) hΨ _ _
    (assoc_hp₂ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃) (assoc_hq₂ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃)
    (tensorAssocHom_pr₂ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφA₂ hφB₁ hφB₂)
    (by omega) (RelativeDimension.comp_of_flat _ _
      (relativeDimension_tensorPr₁₃ k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ hA₃ hB₃)
      (relativeDimension_tensorPr₂₄ k sA₁ sA₂ sB₁ sB₂ hA₁ hB₁))
    (RelativeDimension.comp_of_flat _ _
      (relativeDimension_tensorPr₂₄ k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁ hB₁)
      (relativeDimension_tensorPr₁₃ k sA₂ sA₃ sB₂ sB₃ hA₃ hB₃)) ((e₂ : ℤ) - r₂) x₂
  have hQ₃ := chowPushforwardOfIso_flatPullbackChow_heq k _ _ _
    (tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁) hΨ _ _
    (tensorPr₂₄_comp_prodBase _ _ _ _) (assoc_hq₃ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃)
    (tensorAssocHom_pr₃ k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφA₃ hφB₁ hφB₃)
    (by omega) (relativeDimension_tensorPr₂₄ k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃
      (relativeDimension_prodBase_add k sA₁ sA₂ hA₁ hA₂)
      (relativeDimension_prodBase_add k sB₁ sB₂ hB₁ hB₂))
    (RelativeDimension.comp_of_flat _ _
      (relativeDimension_tensorPr₂₄ k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁ hB₁)
      (relativeDimension_tensorPr₂₄ k sA₂ sA₃ sB₂ sB₃ hA₂ hB₂)) ((e₃ : ℤ) - r₃) x₃
  have hM := (chowPushforwardOfIso_selfIntersectionProduct_heq' k _ _
    (tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁) hΨ hNW hNW' (by omega) _ _ _
    _).trans (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by push_cast; ring)
      (by push_cast; ring) hQ₁ hQ₂)
  exact (chowPushforwardOfIso_selfIntersectionProduct_heq' k _ _
    (tensorAssocHom k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA φB hφA₁ hφB₁) hΨ hNW hNW' (by omega) _ _ _
    _).trans (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by push_cast; ring)
      (by push_cast; ring) hM hQ₃)

end AssocMain

section AssocFinal

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Scheme.{u}}
  (sA₁ : A₁ ⟶ (fieldChowSituation k).S) (sA₂ : A₂ ⟶ (fieldChowSituation k).S)
  (sA₃ : A₃ ⟶ (fieldChowSituation k).S) (sB₁ : B₁ ⟶ (fieldChowSituation k).S)
  (sB₂ : B₂ ⟶ (fieldChowSituation k).S) (sB₃ : B₃ ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sA₁] [LocallyOfFiniteType sA₂] [LocallyOfFiniteType sA₃]
  [LocallyOfFiniteType sB₁] [LocallyOfFiniteType sB₂] [LocallyOfFiniteType sB₃]
  [Smooth sA₁] [Smooth sA₂] [Smooth sA₃] [Smooth sB₁] [Smooth sB₂] [Smooth sB₃]
  [IsSeparated sA₁] [IsSeparated sA₂] [IsSeparated sA₃] [IsSeparated sB₁] [IsSeparated sB₂]
  [IsSeparated sB₃]

/-- **Associativity of the tensor product of correspondences** up to the associativity
constraints. -/
theorem tensorInt_assoc : TensorIntAssoc k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ := by
  intro d₁ d₂ d₃ e₁ e₂ e₃ hA₁ hA₂ hA₃ hB₁ hB₂ hB₃ φA _ hφA₁ hφA₂ hφA₃ φB _ hφB₁ hφB₂ hφB₃
    r₁ r₂ r₃ x₁ x₂ x₃
  have hNW' := relativeDimension_tensorBase k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) hA₁
    (relativeDimension_prodBase_add k sA₂ sA₃ hA₂ hA₃) hB₁
    (relativeDimension_prodBase_add k sB₂ sB₃ hB₂ hB₃)
  refine (chowPushforwardOfIso_heq_congr _ _ _ _ _ (by push_cast; ring) _ _
    (tensorInt_tensorInt_left_heq k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ hA₁ hA₂ hA₃ hB₁ hB₂ hB₃
      r₁ r₂ r₃ x₁ x₂ x₃)).trans ?_
  refine (chowPushforwardOfIso_tensorAssocHom_heq k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ hA₁ hA₂ hA₃ hB₁ hB₂
    hB₃ φA φB hφA₁ hφA₂ hφA₃ hφB₁ hφB₂ hφB₃ r₁ r₂ r₃ x₁ x₂ x₃).trans ?_
  refine HEq.trans ?_ (tensorInt_tensorInt_right_heq k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ hA₁ hA₂ hA₃
    hB₁ hB₂ hB₃ r₁ r₂ r₃ x₁ x₂ x₃).symm
  exact DiagonalClassFamily.IntersectionAssoc.heq
    (canonicalDiagonalClassFamily_intersectionAssoc k) _ hNW' _ _ _ _ _ _

end AssocFinal


end Stacks.WeilCohomology

end
