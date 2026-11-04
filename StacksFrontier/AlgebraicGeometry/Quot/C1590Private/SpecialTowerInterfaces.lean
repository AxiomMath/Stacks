module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeCharts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesOpenVersality

/-!
# Effectivity of special square-zero towers for curves: the interfaces

The proof of Stacks 0CXU (openness of versality from strong formal effectiveness) applies its
condition (4) to one kind of tower only: the tower of Stacks 0G2S, built over an affine scheme
`Spec A` of finite type over the base by adjoining one residue field `κ(uₙ)` at a time, at
pairwise distinct closed points `uₙ`. For such a *special* tower `lim Rₙ → A` has kernel
`∏ κ(uᵢ)`, and étale base change on `A` commutes with the limit. This makes effectivity of the
tower étale local on `A`, and on étale charts a family of curves is a scheme covered by two
affine opens `U = X_s`, `V = X_t`, the non-vanishing loci of two sections of a line bundle `L`
with `H¹(X, L^{⊗ k}) = 0` for `k ≥ 1`. There the limit object is built from the modules
`Γ(X, L^{⊗ k})` (finite projective, compatible with base change), with no derived categories.

This file fixes the propositions passed between the pieces of that argument. Nothing here is
proved; every declaration is a definition.

## The two-chart datum

`AlgebraicGeometry.C1590Private.TwoChartDatum X` records affine opens `U`, `V` covering `X` and
`b ∈ Γ(X, U)`, `a ∈ Γ(X, V)` with `U ∩ V = D(b) = D(a)` and `a b = 1` on `U ∩ V`. It is the
datum of a line bundle `L` with sections `s`, `t` such that `U = X_s`, `V = X_t`, read in the
trivializations of `L` by `s` on `U` and by `t` on `V`: `b = t / s` and `a = s / t`. A section
of `L^{⊗ k}` is a pair `(x, y) ∈ Γ(X, U) × Γ(X, V)` (the coefficients of `s^k` and `t^k`) with
`x = b^k y` on `U ∩ V`; the Čech differential of the cover is `(x, y) ↦ x - b^k y`, and its
surjectivity is `H¹(X, L^{⊗ k}) = 0`.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsSpecialTower`: a tower of the shape of Stacks 0G2S.
* `AlgebraicGeometry.C1590Private.IsSpecialSquareZeroTowerEffectiveOnClasses`: condition (4) of
  Stacks 0CXU on lift classes, for special towers. It replaces
  `Deformation.Artin.IsSquareZeroTowerEffectiveOnClasses` in the assembly of Stacks 0D5A.
* `AlgebraicGeometry.C1590Private.SpecialTowerOpenVersality`: (A), Stacks 0CXU with condition
  (4) for special towers only.
* `AlgebraicGeometry.C1590Private.IsEtaleCompatibleTower` and
  `AlgebraicGeometry.C1590Private.SpecialTowerEtaleCompatible`: (B), étale base change commutes
  with the limit of a special tower.
* `AlgebraicGeometry.C1590Private.TwoChartDatum`, `TwoChartDatum.IsGood`: the chart datum.
* `AlgebraicGeometry.C1590Private.HasTwoChartEtaleCovers`: (C), every point of an affine
  Noetherian base of a family of curves is in the image of an étale chart from an affine scheme
  over which the family acquires a good two-chart datum.
* `AlgebraicGeometry.C1590Private.TwoChartDatumLifts`,
  `AlgebraicGeometry.C1590Private.TwoChartGoodOfThickening`: (D), the datum lifts along flat
  square-zero thickenings and stays good, with finite projective section modules compatible with
  the base change.
* `AlgebraicGeometry.C1590Private.TwoChartTowerEffective`: (E), a tower of flat deformations of a
  proper scheme with a good two-chart datum is effective over `lim Rₙ`, with compatible maps.

The curves statement assembled from these pieces, with (F) + (G), is
`AlgebraicGeometry.C1590Private.isSpecialSquareZeroTowerEffectiveOnClasses_curvesSmall`.

## References

* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0G2S](https://stacks.math.columbia.edu/tag/0G2S)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin
open Deformation.Artin.SquareZeroTower

universe u v w

namespace AlgebraicGeometry.C1590Private

/-! ### Special towers: the boundary between (A) and (G) -/

section SpecialTower

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)

/-- **A tower of the shape of Stacks 0G2S.** The base `R₀` is Noetherian, and the kernel of the
`n`-th step `Rₙ₊₁ → Rₙ` is killed by the preimage in `Rₙ₊₁` of a maximal ideal `𝔪ₙ` of `R₀`, the
`𝔪ₙ` being pairwise distinct. In the tower of Stacks 0G2S that kernel is `κ(uₙ) = R₀ / 𝔪ₙ` at
pairwise distinct closed points `uₙ`; only its annihilator is recorded. -/
structure IsSpecialTower : Prop where
  isNoetherianRing : IsNoetherianRing (R 0)
  exists_points : ∃ 𝔪 : ℕ → Ideal (R 0),
    (∀ n, (𝔪 n).IsMaximal) ∧ Pairwise (fun n m => 𝔪 n ≠ 𝔪 m) ∧
    ∀ n (r : R (n + 1)), toBase f (n + 1) r ∈ 𝔪 n → ∀ z ∈ RingHom.ker (f n), r * z = 0

/-- The projection `lim Rₙ → Rₙ`. -/
abbrev towerLimitProj (n : ℕ) : limit f →+* R n :=
  (Pi.evalRingHom R n).comp (limit f).subtype

/-- The transition map `Rₙ₊₁ → Rₙ`, as a map of `lim Rₙ`-algebras. -/
def towerTransitionAlgHom (n : ℕ) :
    letI := fun m => (towerLimitProj f m).toAlgebra
    R (n + 1) →ₐ[limit f] R n :=
  letI := fun m => (towerLimitProj f m).toAlgebra
  { f n with commutes' := fun r => r.2 n }

/-- **Étale base change commutes with the limit of the tower.** For every étale
`lim Rₙ`-algebra `C`, every compatible sequence of elements of `C ⊗ Rₙ` comes from exactly one
element of `C`. With `C ⊗ Rₙ` the étale lift of `C ⊗ R₀` to `Rₙ`, this says `C = lim (C ⊗ Rₙ)`. -/
def IsEtaleCompatibleTower : Prop :=
  letI := fun m => (towerLimitProj f m).toAlgebra
  ∀ (C : Type u) [CommRing C] [Algebra (limit f) C] [Algebra.Etale (limit f) C]
    (s : ∀ n, TensorProduct (limit f) C (R n)),
    (∀ n, Algebra.TensorProduct.map (AlgHom.id (limit f) C) (towerTransitionAlgHom f n)
      (s (n + 1)) = s n) →
    ∃! c : C, ∀ n, (c ⊗ₜ[limit f] (1 : R n)) = s n

end SpecialTower

/-- **(B).** The limit of a special tower of square-zero thickenings commutes with étale base
change. -/
def SpecialTowerEtaleCompatible : Prop :=
  ∀ (R : ℕ → Type u) [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n),
    (∀ n, Function.Surjective (f n)) → (∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥) →
    IsSpecialTower f → IsEtaleCompatibleTower f

section Classes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Condition (4) of Stacks 0CXU on lift classes, for special towers.** This is
`Deformation.Artin.IsSquareZeroTowerEffectiveOnClasses` with the tower required to be special
(`AlgebraicGeometry.C1590Private.IsSpecialTower`); it is the only case the proof of Stacks 0CXU
uses. -/
def IsSpecialSquareZeroTowerEffectiveOnClasses : Prop :=
  ∀ (R : ℕ → Type u) [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
    (_hf : ∀ n, Function.Surjective (f n)) (_hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥),
    IsSpecialTower f →
    ∀ (toS : Spec (.of (R 0)) ⟶ S) (hA : B.Contains (Spec (.of (R 0))))
    (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
    (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
    (hR : ∀ n, B.Contains (Spec (.of (R n)))),
    MapsIntoAffineOpen S toS →
    ∀ (x : X) (hx : p.obj x = algebraOver (R 0) B S hS toS hA)
      (b : ∀ n, BasedSiteRing.classes p x hx (SquareZeroTower.level f Λ β hβ hβ0 hR n)),
      (∀ n, BasedSiteRing.map p x hx hp (SquareZeroTower.transition f Λ β hβ hβ0 hR n) (b (n + 1)) =
        b n) →
      ∃ ξ : BasedSiteRing.classes p x hx (SquareZeroTower.limitRing f Λ β hβ hβ0 hR),
        ∀ n, BasedSiteRing.map p x hx hp (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n) ξ = b n

end Classes

/-- **(A): Stacks 0CXU, with condition (4) for special towers only.** Let `𝒳` be a category
fibred in groupoids over the big fppf site of a locally Noetherian Jacobson scheme `S` (such as
`Spec ℤ`; this makes the points of the tower of Stacks 0G2S closed), with diagonal representable by
algebraic spaces, satisfying (RS*) and limit preserving, in which special
towers are effective on lift classes. Then `𝒳` satisfies openness of versality. The conclusion
is that of `Deformation.Artin.isOpenVersality_of_isSquareZeroTowerEffectiveOnClasses`. -/
def SpecialTowerOpenVersality : Prop :=
  ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    [JacobsonSpace S] (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)),
    Stack.HasRepresentableDiagonal B S hS 𝒳 →
    SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids →
    IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳 →
    IsSpecialSquareZeroTowerEffectiveOnClasses B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids →
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : 𝒳.val.obj) (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ →
        IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u x hx

/-! ### The two-chart datum: shared by (C), (D) and (E) -/

/-- **A two-chart datum on a scheme.** Affine opens `U`, `V` covering `X`, with `b ∈ Γ(X, U)`
and `a ∈ Γ(X, V)` such that `U ∩ V = D(b) = D(a)` and `a b = 1` on `U ∩ V`. This is a line
bundle `L` with two sections `s`, `t` with `U = X_s`, `V = X_t`, read in the trivializations by
`s` on `U` and `t` on `V`: `b = t / s` and `a = s / t`. -/
structure TwoChartDatum (X : Scheme.{u}) where
  /-- The open `X_s`. -/
  U : X.Opens
  /-- The open `X_t`. -/
  V : X.Opens
  isAffineOpen_U : IsAffineOpen U
  isAffineOpen_V : IsAffineOpen V
  sup_eq_top : U ⊔ V = ⊤
  /-- The function `t / s` on `X_s`. -/
  b : Γ(X, U)
  /-- The function `s / t` on `X_t`. -/
  a : Γ(X, V)
  basicOpen_b : X.basicOpen b = U ⊓ V
  basicOpen_a : X.basicOpen a = U ⊓ V
  mul_eq_one : X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op b *
    X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op a = 1

namespace TwoChartDatum

variable {X : Scheme.{u}} (D : TwoChartDatum X)

/-- Restriction from `U` to `U ∩ V`. -/
def resU : Γ(X, D.U) →+* Γ(X, D.U ⊓ D.V) := (X.presheaf.map (homOfLE inf_le_left).op).hom

/-- Restriction from `V` to `U ∩ V`. -/
def resV : Γ(X, D.V) →+* Γ(X, D.U ⊓ D.V) := (X.presheaf.map (homOfLE inf_le_right).op).hom

/-- The Čech differential of `L^{⊗ k}` for the cover `{U, V}`, in the trivialization by `s^k`
on `U ∩ V`: `(x, y) ↦ x - b^k y`. Its kernel is `Γ(X, L^{⊗ k})`, its cokernel `H¹(X, L^{⊗ k})`. -/
def cechDiff (k : ℕ) : Γ(X, D.U) × Γ(X, D.V) →+ Γ(X, D.U ⊓ D.V) :=
  D.resU.toAddMonoidHom.comp (AddMonoidHom.fst _ _) -
    (AddMonoidHom.mulLeft (D.resU D.b ^ k)).comp
      (D.resV.toAddMonoidHom.comp (AddMonoidHom.snd _ _))

section BaseRing

variable {R : Type u} [CommRing R] (σ : R →+* Γ(X, ⊤))

/-- `Γ(X, U)` as an algebra over the base ring `R`, through `σ : R → Γ(X, X)`. -/
abbrev algebraU : Algebra R Γ(X, D.U) :=
  ((X.presheaf.map (homOfLE le_top : D.U ⟶ ⊤).op).hom.comp σ).toAlgebra

/-- `Γ(X, V)` as an algebra over the base ring `R`, through `σ : R → Γ(X, X)`. -/
abbrev algebraV : Algebra R Γ(X, D.V) :=
  ((X.presheaf.map (homOfLE le_top : D.V ⟶ ⊤).op).hom.comp σ).toAlgebra

/-- The `R`-module `Γ(X, L^{⊗ k})`: the pairs `(x, y)` with `x = b^k y` on `U ∩ V`. -/
def sections (k : ℕ) :
    letI := D.algebraU σ
    letI := D.algebraV σ
    Submodule R (Γ(X, D.U) × Γ(X, D.V)) :=
  letI := D.algebraU σ
  letI := D.algebraV σ
  { carrier := {q | D.cechDiff k q = 0}
    add_mem' := fun {q₁ q₂} h₁ h₂ => by
      simp only [Set.mem_setOf_eq, map_add] at h₁ h₂ ⊢
      rw [h₁, h₂, add_zero]
    zero_mem' := by simp
    smul_mem' := fun r q hq => by
      simp only [Set.mem_setOf_eq] at hq ⊢
      have hU : D.resU (algebraMap R Γ(X, D.U) r) = D.resV (algebraMap R Γ(X, D.V) r) := by
        simp only [resU, resV, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
          ← Functor.map_comp]
        rfl
      have hq' : D.resU q.1 - D.resU D.b ^ k * D.resV q.2 = 0 := hq
      change D.resU (algebraMap R Γ(X, D.U) r * q.1) -
        D.resU D.b ^ k * D.resV (algebraMap R Γ(X, D.V) r * q.2) = 0
      rw [map_mul, map_mul, ← hU, mul_left_comm, ← mul_sub, hq', mul_zero] }

/-- **A good two-chart datum.** For every `k ≥ 1`, `H¹(X, L^{⊗ k}) = 0` (the Čech differential is
surjective) and `Γ(X, L^{⊗ k})` is a finite projective `R`-module. Projectivity is recorded, not
deduced: finite and flat gives projective only for finitely presented modules, and the levels of
a tower need not be Noetherian. -/
def IsGood : Prop :=
  (∀ k, 1 ≤ k → Function.Surjective (D.cechDiff k)) ∧
    letI := D.algebraU σ
    letI := D.algebraV σ
    ∀ k, 1 ≤ k → Module.Finite R (D.sections σ k) ∧ Module.Projective R (D.sections σ k)

end BaseRing

/-- The base ring of a scheme over `Spec R`: `R → Γ(Spec R) → Γ(X)`. -/
abbrev baseOfSpec {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R)) : R →+* Γ(X, ⊤) :=
  π.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

end TwoChartDatum

/-! ### (C): two-chart data on an étale cover -/

section Curves

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **(C).** Every point `s` of the affine Noetherian base `S` of a family of curves is in the
image of an étale morphism `φ : U ⟶ S` from an affine `U` over which the family acquires a good
two-chart datum: the base change is represented by a scheme `Z` over `U` (a cartesian square of
algebraic spaces, as in `AlgebraicGeometry.C1590Private.HasEtaleLocalSchemeCharts`), and `Z`
carries a good two-chart datum over the ring `Γ(U, 𝒪_U)`. The family of all such `φ` is an
étale covering of `S`. -/
def HasTwoChartEtaleCovers : Prop :=
  ∀ (X : CurveFamily B hZ),
    IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base) →
    IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base) →
    ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
    ∃ (U Z : BigFppfOver B integerBase hZ) (φ : U ⟶ X.base) (q : Z ⟶ U)
      (p : schemeSpace Z ⟶ X.total),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) ∧
      IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ) ∧
      ∃ D : TwoChartDatum ((BigFppfOver.toScheme B integerBase hZ).obj Z),
        D.IsGood ((BigFppfOver.toScheme B integerBase hZ).map q).appTop.hom

end Curves

/-! ### (D): the datum along flat square-zero thickenings -/

/-- **(D), lifting.** Let `R' → R` be surjective with square-zero kernel, `X' ⟶ Spec R'` flat
and `X = X' ×_{R'} R`. A good two-chart datum on `X` lifts to a two-chart datum on `X'` with the
same opens (`X ⟶ X'` is a homeomorphism) restricting to it. -/
def TwoChartDatumLifts : Prop :=
  ∀ (R R' : Type u) [CommRing R] [CommRing R'] (g : R' →+* R),
    Function.Surjective g → RingHom.ker g ^ 2 = ⊥ →
    ∀ (X X' : Scheme.{u}) (π : X ⟶ Spec (.of R)) (π' : X' ⟶ Spec (.of R')) (i : X ⟶ X'),
      IsPullback i π π' (Spec.map (CommRingCat.ofHom g)) → Flat π' →
      ∀ D : TwoChartDatum X, D.IsGood (TwoChartDatum.baseOfSpec π) →
        ∃ (D' : TwoChartDatum X') (hU : D.U ≤ i ⁻¹ᵁ D'.U) (hV : D.V ≤ i ⁻¹ᵁ D'.V),
          i ⁻¹ᵁ D'.U = D.U ∧ i ⁻¹ᵁ D'.V = D.V ∧
          i.appLE D'.U D.U hU D'.b = D.b ∧ i.appLE D'.V D.V hV D'.a = D.a

/-- **(D), goodness and base change.** In the situation of
`AlgebraicGeometry.C1590Private.TwoChartDatumLifts`, let `D'` be a two-chart datum on `X'`
restricting to a good datum `D` on `X`. Then `D'` is good, every `Γ(X', L'^{⊗ k})` (`k ≥ 1`) is a
projective `R'`-module, and restriction `Γ(X', L'^{⊗ k}) → Γ(X, L^{⊗ k})` is surjective with
kernel `Ker(R' → R) · Γ(X', L'^{⊗ k})`: the formation of `Γ(L^{⊗ k})` commutes with the base
change `R' → R`. -/
def TwoChartGoodOfThickening : Prop :=
  ∀ (R R' : Type u) [CommRing R] [CommRing R'] (g : R' →+* R),
    Function.Surjective g → RingHom.ker g ^ 2 = ⊥ →
    ∀ (X X' : Scheme.{u}) (π : X ⟶ Spec (.of R)) (π' : X' ⟶ Spec (.of R')) (i : X ⟶ X'),
      IsPullback i π π' (Spec.map (CommRingCat.ofHom g)) → Flat π' →
      ∀ (D : TwoChartDatum X) (D' : TwoChartDatum X') (hU : D.U ≤ i ⁻¹ᵁ D'.U)
        (hV : D.V ≤ i ⁻¹ᵁ D'.V),
        i ⁻¹ᵁ D'.U = D.U → i ⁻¹ᵁ D'.V = D.V →
        i.appLE D'.U D.U hU D'.b = D.b → i.appLE D'.V D.V hV D'.a = D.a →
        D.IsGood (TwoChartDatum.baseOfSpec π) →
        D'.IsGood (TwoChartDatum.baseOfSpec π') ∧
          letI := D.algebraU (TwoChartDatum.baseOfSpec π)
          letI := D.algebraV (TwoChartDatum.baseOfSpec π)
          letI := D'.algebraU (TwoChartDatum.baseOfSpec π')
          letI := D'.algebraV (TwoChartDatum.baseOfSpec π')
          ∀ k, 1 ≤ k →
            Module.Projective R' (D'.sections (TwoChartDatum.baseOfSpec π') k) ∧
            (∀ q ∈ D.sections (TwoChartDatum.baseOfSpec π) k,
              ∃ q' ∈ D'.sections (TwoChartDatum.baseOfSpec π') k,
                (i.appLE D'.U D.U hU q'.1, i.appLE D'.V D.V hV q'.2) = q) ∧
            (∀ q' ∈ D'.sections (TwoChartDatum.baseOfSpec π') k,
              (i.appLE D'.U D.U hU q'.1, i.appLE D'.V D.V hV q'.2) = 0 →
                q' ∈ RingHom.ker g • D'.sections (TwoChartDatum.baseOfSpec π') k)

/-! ### (E): effectivity of a tower with a good two-chart datum -/

/-- **(E).** Let `⋯ → R₁ → R₀` be a tower with surjective transition maps, every `Rₙ → R₀`
having square-zero kernel, and `R₀` Noetherian. Let `Xₙ ⟶ Spec Rₙ` be flat, with cartesian
transition maps `Xₙ ⟶ Xₙ₊₁`, and `X₀ ⟶ Spec R₀` proper and of finite presentation, carrying a
good two-chart datum. Then there is a flat, proper, finitely presented `Y ⟶ Spec (lim Rₙ)` with
maps `Xₙ ⟶ Y` exhibiting each `Xₙ` as the base change of `Y` to `Rₙ`, compatibly with the
transition maps. The tower need not be special: the limit is taken over `lim Rₙ` itself. -/
def TwoChartTowerEffective : Prop :=
  ∀ (R : ℕ → Type u) [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n),
    (∀ n, Function.Surjective (f n)) → (∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥) →
    IsNoetherianRing (R 0) →
    ∀ (X : ℕ → Scheme.{u}) (π : ∀ n, X n ⟶ Spec (.of (R n))) (ι : ∀ n, X n ⟶ X (n + 1)),
      (∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n)))) →
      (∀ n, Flat (π n)) → IsProper (π 0) → LocallyOfFinitePresentation (π 0) →
      ∀ D : TwoChartDatum (X 0), D.IsGood (TwoChartDatum.baseOfSpec (π 0)) →
        ∃ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of (limit f))) (j : ∀ n, X n ⟶ Y),
          Flat πY ∧ IsProper πY ∧ LocallyOfFinitePresentation πY ∧
          (∀ n, IsPullback (j n) (π n) πY
            (Spec.map (CommRingCat.ofHom (towerLimitProj f n)))) ∧
          ∀ n, ι n ≫ j (n + 1) = j n

end AlgebraicGeometry.C1590Private

end
