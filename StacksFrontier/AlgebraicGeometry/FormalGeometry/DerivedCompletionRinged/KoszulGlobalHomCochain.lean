module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulGlobalHomComplex
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulSectionsProjection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower

/-!
# The `A`-linear Hom cochains out of a Koszul complex are the coefficient Koszul terms

Let `(𝒞, 𝒪)` be a ringed site, let `A` be a commutative ring with `ρ : A ⟶ Γ(𝒞, 𝒪)`, let
`a_1, …, a_r ∈ A`, write `f_i = ρ(a_i)` for the corresponding global sections of `𝒪` and let
`K^n = K(𝒪, f_1^{n+1}, …, f_r^{n+1})` be `AlgebraicGeometry.RingedSite.koszulPowerComplex`. For a
cochain complex `J` of `𝒪`-modules this file identifies, degreewise and `A`-linearly,

`Γ_A(𝒞, SheafHom•_𝒪(K^n, J))^t  ≅  ∏_{S ⊆ \{1, …, r\}} Γ_A(𝒞, J^{t + #S})`,

the right-hand side being `KoszulCoefficientTower.coefficientKoszulTerm` of
`StacksFrontier/Homology/DerivedComplete/AdicKoszulCoefficientTower.lean` applied to `Γ_A(𝒞, J)`,
and then **assembles that into an isomorphism of towers**

`(n ↦ Γ_A(𝒞, SheafHom•_𝒪(K^n, J))) ≅ (KoszulCoefficientTower.coefficientKoszulTower a).obj
  (Γ_A(𝒞, J))`

of functors `ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ`. This compares the two towers of the
identity `RΓ(𝒞, ℱ)^∧ = RΓ(𝒞, ℱ^∧)` of [Stacks, Tag 0BLX]: the sheaf side of that identity is
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem` and
the module side is `KoszulCompletion.isDerivedLimit_coefficientKoszulTower_derivedCompletion`.
Here `𝒪` is an arbitrary sheaf of `A`-algebras on an arbitrary ringed site, the `a_i` are
arbitrary and `J` is an arbitrary complex of `𝒪`-modules.

The left-hand side is read through [Stacks, Tag 0A8Z] over `A`,
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso` of
`KoszulGlobalHomComplex.lean`, so its degree-`t` term is the `A`-module of degree-`t` cochains
`K^n ⟶ J` with the differential `CochainComplex.HomComplex.δ`, which is the only form in which
the differential of `AlgebraicGeometry.RingedSite.sheafHomComplex` is usable.

## Main definitions

* `AlgebraicGeometry.RingedSite.koszulTwist`: the sign `ε_S = (-1)^{#S(#S-1)/2}`.
* `AlgebraicGeometry.RingedSite.koszulFactorι` and
  `AlgebraicGeometry.RingedSite.koszulFactorDesc`: the inclusion of the factor of `K^n` indexed
  by a subset, and a morphism out of a term of `K^n` assembled from its values on the factors.
* `AlgebraicGeometry.RingedSite.koszulHomComponent` and
  `AlgebraicGeometry.RingedSite.koszulHomOfComponents`: the two directions of the comparison.
* `AlgebraicGeometry.RingedSite.koszulHomTermEquiv`: **the degreewise comparison**, as an
  `A`-linear equivalence.
* `AlgebraicGeometry.RingedSite.homComplexPrecomp`: precomposition with a map of complexes on
  the Hom cochain complexes, which is the transition of the tower on the left-hand side.
* `AlgebraicGeometry.RingedSite.koszulHomComplexSystem`: **the tower
  `n ↦ Γ_A(𝒞, SheafHom•_𝒪(K^n, J))`**, as a functor `ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ`.
* `AlgebraicGeometry.RingedSite.koszulHomComplexIso`: **the comparison at a fixed `n`**, as an
  isomorphism of cochain complexes of `A`-modules.
* `AlgebraicGeometry.RingedSite.koszulHomComplexSystemIso`: **the comparison of towers.**
* `AlgebraicGeometry.RingedSite.koszulSheafHomComplexSystem`: the tower
  `n ↦ SheafHom•_𝒪(K^n, J)` of internal Hom complexes, as a functor
  `ℕᵒᵖ ⥤ CochainComplex (Mod 𝒪) ℤ`.
* `AlgebraicGeometry.RingedSite.globalSectionsKoszulSheafHomComplexSystemIso`: **`Γ_A(𝒞, -)`
  carries that tower to `KoszulCoefficientTower.coefficientKoszulTower a` applied to
  `Γ_A(𝒞, J)`.**
* `AlgebraicGeometry.RingedSite.DerivedKoszulHomTowerComparison`: the passage from that tower of
  complexes to the tower in `D(A)`, as one proposition.
* `AlgebraicGeometry.RingedSite.koszulDerivedSheafHomComplexSystemComparison` and
  `AlgebraicGeometry.RingedSite.derivedGlobalSectionsKoszulHomTowerComparison`: the two towers of
  that proposition compared, first in `D(𝒪)` and then in `D(A)`.

## Main results

* `AlgebraicGeometry.RingedSite.koszulTwist_mul_negOnePow`: **the sign identity behind the
  twist.** Mathlib's `δ` carries `(-1)^{t+1}` while
  `KoszulCoefficientTower.coefficientKoszulDifferential` carries `(-1)^{t+#S+1}`; the ratio
  `(-1)^{#S}` is `ε_{S ∪ \{i\}} / ε_S`, so the twist absorbs it exactly.
* `AlgebraicGeometry.RingedSite.koszulFactorι_comp_d`: the Koszul differential out of the factor
  indexed by `S` is the contraction `∑_{i ∉ S} (-1)^{#\{j ∈ S : j < i\}} f_i^{n+1} ι_{S ∪ \{i\}}`.
* `AlgebraicGeometry.RingedSite.smul_eq_koszulScalar_comp` and
  `AlgebraicGeometry.RingedSite.moduleKoszulValue_koszulExp_insert`: the entries of that
  contraction act on `Γ_A(𝒞, J^j) = Hom_𝒪(𝒪, J^j)` as multiplication by `a_i^{n+1} ∈ A`. These
  are the left-hand companions of
  `AlgebraicGeometry.RingedSite.map_koszulScalarOn` of `KoszulSectionsProjection.lean`, which is
  the same statement for the action of the functor.
* `AlgebraicGeometry.RingedSite.koszulHomComponent_delta`: **the differentials agree.** Out of
  the factor indexed by `S`, Mathlib's `δ` is the coefficient differential plus the signed
  Koszul contraction that `KoszulCoefficientTower.coefficientKoszulDifferential` carries.
* `AlgebraicGeometry.RingedSite.koszulHomComponent_coefficientKoszulDifferential` and
  `AlgebraicGeometry.RingedSite.koszulHomTermEquiv_comm`: the degreewise comparison commutes
  with the differentials, which is what makes `koszulHomComplexIso` an isomorphism of complexes.
* `AlgebraicGeometry.RingedSite.koszulHomComponent_precomp` and
  `AlgebraicGeometry.RingedSite.koszulHomComponent_coefficientKoszulTransitionTerm`: it commutes
  with the transitions, which is what makes `koszulHomComplexSystemIso` an isomorphism of
  towers. Both transitions multiply the factor indexed by `S` by `∏_{i ∈ S} a_i`, on one side
  through `AlgebraicGeometry.RingedSite.koszulPowerTrans` and on the other through
  `KoszulCoefficientTower.coefficientKoszulTransitionTerm`.
* `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso_naturality_source`:
  **[Stacks, Tag 0A8Z] over `A` is natural in its source variable** — it carries
  `Γ_A(𝒞, homMap X φ (𝟙 G))` to `homComplexPrecomp X G φ`. This is
  `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v`, which is [Stacks, Tag 0A90] (1)
  globally, read on the cochain attached to an `A`-linear global section.
* `CategoryTheory.AlternatingCech.termι_comp_mapX`: the map of alternating Čech complexes
  induced by a morphism of systems, read in the inclusion basis.
* `AlgebraicGeometry.RingedSite.koszulHomComponent_add`,
  `AlgebraicGeometry.RingedSite.koszulHomComponent_smul`,
  `AlgebraicGeometry.RingedSite.koszulHomOfComponents_koszulHomComponent` and
  `AlgebraicGeometry.RingedSite.koszulHomComponent_koszulHomOfComponents`: the comparison is an
  `A`-linear bijection.
* `AlgebraicGeometry.RingedSite.derivedKoszulHomTowerComparison`: **the tower in `D(A)` of
  `AlgebraicGeometry.RingedSite.isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem` is
  the image of the complex-level tower**, for `J` K-injective. This is
  `AlgebraicGeometry.RingedSite.DerivedKoszulHomTowerComparison`.

## Implementation notes

The comparison of towers is given, at the level of complexes, in two forms.
`AlgebraicGeometry.RingedSite.koszulHomComplexSystemIso` is an isomorphism of functors
`ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ` between
`AlgebraicGeometry.RingedSite.koszulHomComplexSystem`, the tower
`n ↦ Γ_A(𝒞, SheafHom•_𝒪(K^n, J))` in its Hom-cochain reading, and
`KoszulCoefficientTower.coefficientKoszulTower a` applied to `Γ_A(𝒞, J)`, whose derived limit is
the derived completion of `RΓ(𝒞, J)` by
`KoszulCompletion.isDerivedLimit_coefficientKoszulTower_derivedCompletion`. Its degreewise half
is `koszulHomComplexIso`, twisted by `koszulTwist`; its transitions carry no twist, `ε_S` being
a scalar. And `AlgebraicGeometry.RingedSite.globalSectionsKoszulSheafHomComplexSystemIso` is the
same isomorphism with the left-hand tower written as `Γ_A(𝒞, -)` applied to the tower of
internal Hom complexes `AlgebraicGeometry.RingedSite.koszulSheafHomComplexSystem`, which is
`(koszulPowerSystem X f).op ⋙ (sheafHomComplexBifunctor X).flip.obj J`. The bridge between the
two forms is
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso_naturality_source`, the
naturality of [Stacks, Tag 0A8Z] over `A` in its source variable, proved here out of
`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v`.

The passage from that tower of complexes to the tower in `D(A)` whose derived limit is
`RΓ(𝒞, ℱ^∧)` is the proposition
`AlgebraicGeometry.RingedSite.DerivedKoszulHomTowerComparison` below, which holds for a
K-injective `J` by `AlgebraicGeometry.RingedSite.derivedKoszulHomTowerComparison`. The
isomorphism is `AlgebraicGeometry.RingedSite.derivedGlobalSectionsKoszulHomTowerComparison`,
assembled out of the two objectwise comparisons its docstring names: at each `n` it is
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsDerivedUnit` — already a natural
transformation on all of `CochainComplex (Mod 𝒪) ℤ`, so it is whiskered rather than made natural
— followed by `RΓ_A(𝒞, -)` applied to
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`, whose naturality in the source
complex is `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality`. Since
`AlgebraicGeometry.RingedSite.derivedSheafHomSystem` is built from
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` while
`strictlyPerfectHomComparison` is stated for an arbitrary
`AlgebraicGeometry.RingedSite.DerivedInternalHom`, the assembly runs at the explicit
`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor` and never at
`AlgebraicGeometry.RingedSite.canonicalDerivedInternalHom`, which is a `Classical.choice`.

From it, `CategoryTheory.Pretriangulated.IsDerivedLimit.of_natIso` transports the derived
limit of
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem` to
`koszulSheafHomComplexSystem ⋙ Γ_A(𝒞, -) ⋙ Q`, hence along
`globalSectionsKoszulSheafHomComplexSystemIso` to
`KoszulCoefficientTower.coefficientKoszulTower a` applied to `Γ_A(𝒞, J)`, and
`CategoryTheory.Pretriangulated.nonempty_iso_of_isDerivedLimit` against
`KoszulCompletion.isDerivedLimit_coefficientKoszulTower_derivedCompletion` gives
`RΓ(𝒞, ℱ)^∧ ≅ RΓ(𝒞, ℱ^∧)`.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0920](https://stacks.math.columbia.edu/tag/0920)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe u

/-! ## Transporting the value of a cochain along an equality of degrees -/

namespace CochainComplex.HomComplex.Cochain

variable {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] {F G : CochainComplex 𝒜 ℤ} {m : ℤ}

/-- The value of a cochain at a target degree `q`, followed by the identification of `G.X q`
with `G.X q'` for `q = q'`, is its value at `q'`. -/
theorem v_comp_eqToHom (z : Cochain F G m) (p q q' : ℤ) (h : p + m = q) (e : q = q')
    (he : G.X q = G.X q') : z.v p q h ≫ eqToHom he = z.v p q' (h.trans e) := by
  subst e
  simp

/-- The identification of `F.X p` with `F.X p'` for `p = p'`, followed by the value of a cochain
at the source degree `p'`, is its value at `p`. -/
theorem eqToHom_comp_v (z : Cochain F G m) (p p' q : ℤ) (h : p' + m = q) (e : p = p')
    (he : F.X p = F.X p') : eqToHom he ≫ z.v p' q h = z.v p q (by rw [e]; exact h) := by
  subst e
  simp

end CochainComplex.HomComplex.Cochain

/-! ## The alternating Čech comparison map in the inclusion basis -/

namespace CategoryTheory.AlternatingCech

variable {r : ℕ} {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasFiniteBiproducts 𝒜]
  {F G : Finset (Fin r) ⥤ 𝒜}

/-- **The map of alternating Čech complexes induced by a morphism of systems, read in the
inclusion basis.** Out of the factor indexed by `S` it is the component of the morphism at `S`
followed by the inclusion of the factor indexed by `S`. This is the companion of
`CategoryTheory.AlternatingCech.mapX_comp_pi`, which reads the same map in the projection
basis. -/
theorem termι_comp_mapX (α : F ⟶ G) {p : ℤ} (S : Idx r p) :
    termι F S ≫ mapX α p = α.app S.1 ≫ termι G S := by
  refine Pi.hom_ext _ _ fun T ↦ ?_
  rw [Category.assoc, mapX_comp_pi, Category.assoc, ← Category.assoc (termι F S)]
  by_cases h : S = T
  · subst h
    rw [termι_comp_π_self, termι_comp_π_self, Category.comp_id, Category.id_comp]
  · rw [termι_comp_π_of_ne F h, termι_comp_π_of_ne G h, zero_comp, comp_zero]

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

/-! ## The Koszul sign twist -/

section Twist

variable {r : ℕ}

/-- **The sign `ε_S = (-1)^{#S(#S-1)/2}`**, written as `(-1)` to the `#S`-th triangular number
so that `koszulTwist_insert` is `Finset.sum_range_succ`. It is the twist by which the degreewise
identification of `Γ_A(𝒞, SheafHom•_𝒪(K^n, J))` with the coefficient Koszul term has to be
corrected, because Mathlib's `δ` carries the sign `(-1)^{t+1}` while
`KoszulCoefficientTower.coefficientKoszulDifferential` carries `(-1)^{t+#S+1}`. -/
def koszulTwist (S : Finset (Fin r)) : ℤ := (-1) ^ ∑ j ∈ Finset.range S.card, j

/-- **The twist changes by `(-1)^{#S}` when one index is added.** This is the identity that
absorbs the discrepancy between the two signed differentials. -/
theorem koszulTwist_insert {S : Finset (Fin r)} {i : Fin r} (hi : i ∉ S) :
    koszulTwist (insert i S) = (-1) ^ S.card * koszulTwist S := by
  rw [koszulTwist, koszulTwist, Finset.card_insert_of_notMem hi, Finset.sum_range_succ,
    pow_add, mul_comm]

/-- The twist is its own inverse. -/
theorem koszulTwist_mul_self (S : Finset (Fin r)) : koszulTwist S * koszulTwist S = 1 := by
  rw [koszulTwist, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- `(-1)^{|m|}` is `Int.negOnePow m`: `Int.natAbs` preserves parity. -/
theorem coe_negOnePow_natAbs (m : ℤ) : ((m.negOnePow : ℤ)) = (-1 : ℤ) ^ m.natAbs := by
  rw [← Int.coe_negOnePow_natCast, Int.natCast_natAbs, Int.negOnePow_abs]

/-- `(-1)^{|m|}` in a ring is the image of `Int.negOnePow m`. -/
theorem cast_negOnePow_natAbs (R : Type*) [Ring R] (m : ℤ) :
    (((m.negOnePow : ℤ) : R)) = (-1 : R) ^ m.natAbs := by
  rw [coe_negOnePow_natAbs]
  push_cast
  rfl

/-- **The sign identity behind the twist.** Mathlib's `δ` carries the sign `(-1)^{t+1}` out of
degree `t`, while `KoszulCoefficientTower.coefficientKoszulDifferential` carries
`(-1)^{t+#S+1}` out of the factor indexed by `S`. The two differ by `(-1)^{#S}`, which is
exactly the ratio `ε_{S ∪ \{i\}} / ε_S` of the twists, so twisting the degreewise identification
by `koszulTwist` makes the two differentials agree. -/
theorem koszulTwist_mul_negOnePow (S : Finset (Fin r)) (i : Fin r) (hi : i ∉ S) (t : ℤ) :
    ((t + 1).negOnePow : ℤ) * (koszulTwist S * koszulTwist (insert i S)) =
      (-1 : ℤ) ^ (t + (S.card : ℤ) + 1).natAbs := by
  have h1 : koszulTwist S * koszulTwist (insert i S) = (-1 : ℤ) ^ S.card := by
    rw [koszulTwist_insert hi, mul_comm ((-1 : ℤ) ^ S.card), ← mul_assoc,
      koszulTwist_mul_self, one_mul]
  have h2 : ((t + (S.card : ℤ) + 1).negOnePow : ℤ) =
      ((t + 1).negOnePow : ℤ) * (-1 : ℤ) ^ S.card := by
    rw [show t + (S.card : ℤ) + 1 = (t + 1) + (S.card : ℤ) by ring, Int.negOnePow_add,
      Units.val_mul, Int.coe_negOnePow_natCast]
  rw [h1, ← coe_negOnePow_natAbs, h2]

end Twist

/-! ## The degreewise comparison -/

section Degreewise

attribute [local instance] hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) {r : ℕ}
  (a : Fin r → A)
  (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (n : ℕ)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **Precomposition with multiplication by a monomial in `ρ a_1, …, ρ a_r` is multiplication by
the monomial in `a_1, …, a_r`.** The entries of the Koszul differential are the multiplications
on the left, and the `A`-action on `Γ(𝒞, M) = Hom_𝒪(𝒪, M)` is precomposition with multiplication
by a global section, so this is where the ring map `ρ` enters the comparison.

This is the left-hand companion of `AlgebraicGeometry.RingedSite.map_koszulScalarOn`, which is
the same statement for postcomposition, that is for the action of the functor. -/
theorem smul_eq_koszulScalar_comp (e : Fin r → ℕ)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : (moduleGlobalSectionsOver X A ρ).obj M) :
    (moduleKoszulValue a e • h : (moduleGlobalSectionsOver X A ρ).obj M) =
      koszulScalar X (fun i ↦ globalSectionOfSections (ρ (a i))) e ≫
        (show SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ M from h) := by
  rw [smul_moduleGlobalSectionsOver, koszulScalar, koszulFamily_globalSectionOfSections]

/-! ### The factors of the Koszul complex -/

/-- **The inclusion of the factor indexed by `T` into the degree-`p` term of the Koszul
complex.** This is `CategoryTheory.AlternatingCech.termι` at the system
`AlgebraicGeometry.RingedSite.koszulPowerFunctor`, whose values are all the unit object, written
so that its source is `𝒪` and its target the degree-`p` term of
`AlgebraicGeometry.RingedSite.koszulPowerComplex` on the nose. -/
def koszulFactorι {p : ℤ} (T : AlternatingCech.Idx r p) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n).X p :=
  AlternatingCech.termι (koszulPowerFunctor X (fun i ↦ globalSectionOfSections (ρ (a i))) n) T

/-- **A morphism out of the degree-`p` term of the Koszul complex assembled from its values on
the factors.** This is `CategoryTheory.AlternatingCech.termDesc`, written with the factors
spelled as `𝒪`. -/
def koszulFactorDesc {p : ℤ} {Z : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : AlternatingCech.Idx r p →
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ Z)) :
    (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n).X p ⟶ Z :=
  AlternatingCech.termDesc (koszulPowerFunctor X (fun i ↦ globalSectionOfSections (ρ (a i))) n) g

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The morphism assembled by `koszulFactorDesc` restricts on the factor indexed by `T` to
`g T`.** -/
@[simp]
theorem koszulFactorι_comp_koszulFactorDesc {p : ℤ}
    {Z : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : AlternatingCech.Idx r p →
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ Z))
    (T : AlternatingCech.Idx r p) :
    koszulFactorι X A ρ a n T ≫ koszulFactorDesc X A ρ a n g = g T :=
  AlternatingCech.termι_comp_termDesc _ _ _

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **Two morphisms out of the degree-`p` term of the Koszul complex agreeing on every factor
are equal.** -/
theorem koszulFactor_hom_ext {p : ℤ}
    {Z : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {h h' : (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n).X p ⟶ Z}
    (hyp : ∀ T : AlternatingCech.Idx r p,
      koszulFactorι X A ρ a n T ≫ h = koszulFactorι X A ρ a n T ≫ h') : h = h' :=
  AlternatingCech.term_hom_ext _ hyp

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The inclusion of a factor transported along an equality of degrees.** The factor indexed
by a subset `S` sits in degree `#S`, and the Čech differential presents it in degree `#S' + 1`
for `S = S' ∪ \{i\}`; the two spellings of the degree are equal but not identical. -/
theorem koszulFactorι_congr {p p' : ℤ} (T : AlternatingCech.Idx r p)
    (T' : AlternatingCech.Idx r p') (hp : p = p') (hT : (T.1 : Finset (Fin r)) = T'.1) :
    koszulFactorι X A ρ a n T ≫
        eqToHom (congrArg
          (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n).X hp) =
      koszulFactorι X A ρ a n T' := by
  subst hp
  obtain rfl : T = T' := Subtype.ext hT
  exact Category.comp_id _

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The Koszul differential read out of the factor indexed by `T`**: the signed sum, over the
indices `i` outside `T`, of multiplication by `f_i^{n+1}` followed by the inclusion of the factor
indexed by `T ∪ \{i\}`. This is `CategoryTheory.AlternatingCech.termι_comp_d` of
`KoszulGlobalHomComplex.lean` at the Koszul system, with the transition map named. -/
theorem koszulFactorι_comp_d {p : ℤ} (T : AlternatingCech.Idx r p) :
    koszulFactorι X A ρ a n T ≫
        (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n).d p (p + 1) =
      ∑ i : {i : Fin r // i ∉ T.1}, Cech.cechSign T.1 i.1 •
        (koszulScalar X (fun j ↦ globalSectionOfSections (ρ (a j)))
            (koszulExp n T.1 (insert i.1 T.1)) ≫
          koszulFactorι X A ρ a n (AlternatingCech.insertIdx T i)) := by
  refine Eq.trans (congrArg (fun φ ↦ koszulFactorι X A ρ a n T ≫ φ)
    (AlternatingCech.complex_d
      (koszulPowerFunctor X (fun i ↦ globalSectionOfSections (ρ (a i))) n) p)) ?_
  refine Eq.trans (AlternatingCech.termι_comp_d T) (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [show Cech.cechSign (AlternatingCech.insertIdx T i).1 i.1 = Cech.cechSign T.1 i.1 from
    Cech.cechSign_insert _ _]
  rfl

/-- **The monomial attached to the inclusion `S ⊆ S ∪ \{i\}` is `a_i^{n+1}`.** -/
theorem moduleKoszulValue_koszulExp_insert {S : Finset (Fin r)} {i : Fin r} (hi : i ∉ S) :
    moduleKoszulValue a (koszulExp n S (insert i S)) = a i ^ (n + 1) := by
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin r)), j ≠ i →
      a j ^ koszulExp n S (insert i S) j = 1 := by
    intro j _ hj
    rw [show koszulExp n S (insert i S) j = 0 from by
      simp [koszulExp, Finset.mem_sdiff, Finset.mem_insert, hj], pow_zero]
  rw [moduleKoszulValue, Finset.prod_eq_single_of_mem i (Finset.mem_univ i) h0,
    show koszulExp n S (insert i S) i = n + 1 from by
      simp [koszulExp, hi]]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- `A`-linear global sections act on a global section by postcomposition. -/
theorem moduleGlobalSectionsOver_map_apply
    {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (g : M ⟶ N)
    (h : (moduleGlobalSectionsOver X A ρ).obj M) :
    ((moduleGlobalSectionsOver X A ρ).map g).hom h =
      (show SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ M from h) ≫ g :=
  rfl

/-! ### The degreewise comparison -/

/-- **The factor at `S` of the degreewise comparison**: restrict the cochain to the factor of
`K^n` indexed by `S`, which is a copy of `𝒪`, and twist by `ε_S`. -/
def koszulHomComponent (t : ℤ)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t)
    (S : Finset (Fin r)) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ J.X (t + (S.card : ℤ)) :=
  koszulTwist S • (koszulFactorι X A ρ a n (⟨S, rfl⟩ : AlternatingCech.Idx r (S.card : ℤ)) ≫
    z.v (S.card : ℤ) (t + (S.card : ℤ)) (add_comm _ _))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The factor at `S` of the degreewise comparison is the twist by `ε_S` of the restriction of
the cochain to the factor indexed by `S`.** -/
theorem koszulHomComponent_def (t : ℤ)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t)
    (S : Finset (Fin r)) :
    koszulHomComponent X A ρ a J n t z S =
      koszulTwist S • (koszulFactorι X A ρ a n (⟨S, rfl⟩ : AlternatingCech.Idx r (S.card : ℤ)) ≫
        z.v (S.card : ℤ) (t + (S.card : ℤ)) (add_comm _ _)) :=
  rfl

/-- **The cochain assembled from a family of twisted global sections**, the inverse of
`koszulHomComponent`. -/
def koszulHomOfComponents (t : ℤ)
    (g : ∀ S : Finset (Fin r),
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ J.X (t + (S.card : ℤ))) :
    Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t :=
  Cochain.mk fun p q h ↦ koszulFactorDesc X A ρ a n (p := p) fun T ↦ koszulTwist T.1 •
    (g T.1 ≫ eqToHom (congrArg J.X (show t + (T.1.card : ℤ) = q by have := T.2; omega)))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The component of `koszulHomOfComponents` from degree `p` to degree `q` is assembled from
the twisted global sections on the factors.** -/
theorem koszulHomOfComponents_v (t : ℤ)
    (g : ∀ S : Finset (Fin r),
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ J.X (t + (S.card : ℤ)))
    (p q : ℤ) (h : p + t = q) :
    (koszulHomOfComponents X A ρ a J n t g).v p q h =
      koszulFactorDesc X A ρ a n (p := p) (fun T ↦ koszulTwist T.1 •
        (g T.1 ≫ eqToHom (congrArg J.X (show t + (T.1.card : ℤ) = q by
          have := T.2; omega)))) :=
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The twisted restriction is additive.** -/
theorem koszulHomComponent_add (t : ℤ)
    (z z' : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t)
    (S : Finset (Fin r)) :
    koszulHomComponent X A ρ a J n t (z + z') S =
      koszulHomComponent X A ρ a J n t z S + koszulHomComponent X A ρ a J n t z' S := by
  rw [koszulHomComponent_def, koszulHomComponent_def, koszulHomComponent_def, Cochain.add_v,
    Preadditive.comp_add, smul_add]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The twisted restriction is linear over the global sections of `𝒪`**, hence over `A`
through `ρ`: the scalar acts on a cochain degreewise and on a global section by precomposition
with multiplication, and the inclusion of a Koszul factor is a morphism of `𝒪`-modules. -/
theorem koszulHomComponent_smul (t : ℤ)
    (c : RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t)
    (S : Finset (Fin r)) :
    koszulHomComponent X A ρ a J n t (c • z) S =
      c • koszulHomComponent X A ρ a J n t z S := by
  rw [koszulHomComponent_def, koszulHomComponent_def, Cochain.smul_v, Linear.comp_smul, smul_comm]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Assembling the twisted factors of a cochain returns that cochain. -/
theorem koszulHomOfComponents_koszulHomComponent (t : ℤ)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t) :
    koszulHomOfComponents X A ρ a J n t (fun S ↦ koszulHomComponent X A ρ a J n t z S) = z := by
  refine Cochain.ext _ _ fun p q h ↦ ?_
  refine koszulFactor_hom_ext X A ρ a n fun T ↦ ?_
  obtain ⟨S, hS⟩ := T
  subst hS
  subst h
  rw [koszulHomOfComponents_v, koszulFactorι_comp_koszulFactorDesc, koszulHomComponent_def,
    Preadditive.zsmul_comp, Category.assoc,
    Cochain.v_comp_eqToHom z (S.card : ℤ) (t + (S.card : ℤ)) ((S.card : ℤ) + t)
      (add_comm _ _) (add_comm _ _) _,
    smul_smul, koszulTwist_mul_self, one_smul]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The twisted factors of the cochain assembled from a family are that family. -/
theorem koszulHomComponent_koszulHomOfComponents (t : ℤ)
    (g : ∀ S : Finset (Fin r),
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ J.X (t + (S.card : ℤ)))
    (S : Finset (Fin r)) :
    koszulHomComponent X A ρ a J n t (koszulHomOfComponents X A ρ a J n t g) S = g S := by
  rw [koszulHomComponent_def, koszulHomOfComponents_v, koszulFactorι_comp_koszulFactorDesc]
  simp only [eqToHom_refl, Category.comp_id]
  rw [smul_smul, koszulTwist_mul_self, one_smul]

/-- **The degreewise comparison on the underlying types.** -/
def koszulHomTermRawEquiv (t : ℤ) :
    Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t ≃
      (∀ S : Finset (Fin r),
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
          J.X (t + (S.card : ℤ))) where
  toFun z S := koszulHomComponent X A ρ a J n t z S
  invFun g := koszulHomOfComponents X A ρ a J n t g
  left_inv z := koszulHomOfComponents_koszulHomComponent X A ρ a J n t z
  right_inv g := funext (koszulHomComponent_koszulHomOfComponents X A ρ a J n t g)

/-- **The degreewise comparison, as an `A`-linear equivalence.** The degree-`t` part of the
`A`-linear global sections of the internal Hom complex `SheafHom•_𝒪(K^n, J)` — read through
[Stacks, Tag 0A8Z] as the `A`-module of degree-`t` cochains `K^n ⟶ J`, which is what
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso` of
`KoszulGlobalHomComplex.lean` identifies it with — is the product over the subsets `S` of
`{1, …, r}` of the `A`-module `Γ(𝒞, J^{t + #S})`, which is the degree-`t` term
`KoszulCoefficientTower.coefficientKoszulTerm` of the coefficient Koszul complex of
`Γ_A(𝒞, J)`.

The identification is twisted by `koszulTwist`; the twist is invisible in this statement, and is
exactly what makes the two signed differentials agree. -/
def koszulHomTermEquiv (t : ℤ) :
    ((ModuleCat.restrictScalars ρ).obj
        (((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
          (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J).X t)) ≃ₗ[A]
      KoszulCoefficientTower.coefficientKoszulTerm (r := r)
        (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) t where
  toFun := (koszulHomTermRawEquiv X A ρ a J n t).toFun
  invFun := (koszulHomTermRawEquiv X A ρ a J n t).invFun
  left_inv := (koszulHomTermRawEquiv X A ρ a J n t).left_inv
  right_inv := (koszulHomTermRawEquiv X A ρ a J n t).right_inv
  map_add' z z' := funext fun S ↦ koszulHomComponent_add X A ρ a J n t z z' S
  map_smul' c z := funext fun S ↦ koszulHomComponent_smul X A ρ a J n t (ρ c) z S

/-! ### The differentials agree -/

/-- Inserting one index outside `S` raises the degree `t + #S` by one. -/
theorem koszulInsertDegree (t : ℤ) (S : Finset (Fin r)) {i : Fin r} (hi : i ∉ S) :
    t + ((insert i S).card : ℤ) = t + 1 + (S.card : ℤ) := by
  rw [Finset.card_insert_of_notMem hi]
  push_cast
  ring

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The factor of the Koszul complex indexed by `S ∪ \{i\}`, read in degree `#S + 1`. -/
theorem koszulFactorι_insertIdx_comp_v (t : ℤ)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t)
    (S : Finset (Fin r)) (i : {i : Fin r // i ∉ S}) :
    koszulFactorι X A ρ a n
        (AlternatingCech.insertIdx (⟨S, rfl⟩ : AlternatingCech.Idx r (S.card : ℤ)) i) ≫
          z.v ((S.card : ℤ) + 1) (t + 1 + (S.card : ℤ)) (by ring) =
      koszulTwist (insert i.1 S) • (koszulHomComponent X A ρ a J n t z (insert i.1 S) ≫
        eqToHom (congrArg J.X (koszulInsertDegree t S i.2))) := by
  rw [← koszulFactorι_congr X A ρ a n
      (⟨insert i.1 S, rfl⟩ : AlternatingCech.Idx r ((insert i.1 S).card : ℤ))
      (AlternatingCech.insertIdx (⟨S, rfl⟩ : AlternatingCech.Idx r (S.card : ℤ)) i)
      (by rw [Finset.card_insert_of_notMem i.2]; push_cast; ring) rfl,
    Category.assoc,
    Cochain.eqToHom_comp_v z ((insert i.1 S).card : ℤ) ((S.card : ℤ) + 1)
      (t + 1 + (S.card : ℤ)) (by ring)
      (by rw [Finset.card_insert_of_notMem i.2]; push_cast; ring) _,
    koszulHomComponent_def, Preadditive.zsmul_comp, smul_smul, koszulTwist_mul_self, one_smul,
    Category.assoc,
    Cochain.v_comp_eqToHom z ((insert i.1 S).card : ℤ) (t + ((insert i.1 S).card : ℤ))
      (t + 1 + (S.card : ℤ)) (add_comm _ _) (koszulInsertDegree t S i.2) _]

/-- The combined sign of the contraction term. -/
theorem koszulTwist_cechSign (t : ℤ) (S : Finset (Fin r)) (i : {i : Fin r // i ∉ S}) :
    koszulTwist S * ((t + 1).negOnePow : ℤ) * Cech.cechSign S i.1 *
        koszulTwist (insert i.1 S) =
      (-1 : ℤ) ^ (t + (S.card : ℤ) + 1).natAbs *
        (-1 : ℤ) ^ (S.filter (· < i.1)).card := by
  rw [show Cech.cechSign S i.1 = (-1 : ℤ) ^ (S.filter (· < i.1)).card from rfl,
    ← koszulTwist_mul_negOnePow S i.1 i.2 t]
  ring

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The differentials agree.** Out of the factor indexed by `S`, the differential of the
`A`-linear Hom complex `Γ_A(𝒞, SheafHom•_𝒪(K^n, J))` — which is
`CochainComplex.HomComplex.δ` by [Stacks, Tag 0A8Z] — is, after the twist by `koszulTwist`,
the differential `KoszulCoefficientTower.coefficientKoszulDifferential` of the coefficient
Koszul complex: the coefficient differential of `Γ_A(𝒞, J)` plus the contraction, whose term at
an index `i ∉ S` carries the sign `(-1)^{|t+#S+1|}(-1)^{#\{j ∈ S : j < i\}}` and multiplication
by `f_i^{n+1}`.

The three ingredients are `CochainComplex.HomComplex.δ_v`,
`AlgebraicGeometry.RingedSite.koszulFactorι_comp_d` and
`AlgebraicGeometry.RingedSite.koszulTwist_mul_negOnePow`. -/
theorem koszulHomComponent_delta (t : ℤ)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t)
    (S : Finset (Fin r)) :
    koszulHomComponent X A ρ a J n (t + 1) (δ t (t + 1) z) S =
      koszulHomComponent X A ρ a J n t z S ≫ J.d (t + (S.card : ℤ)) (t + 1 + (S.card : ℤ)) +
        ∑ i : {i : Fin r // i ∉ S},
          ((-1 : ℤ) ^ (t + (S.card : ℤ) + 1).natAbs *
            (-1 : ℤ) ^ (S.filter (· < i.1)).card) •
            (koszulScalar X (fun j ↦ globalSectionOfSections (ρ (a j)))
                (koszulExp n S (insert i.1 S)) ≫
              koszulHomComponent X A ρ a J n t z (insert i.1 S) ≫
                eqToHom (congrArg J.X (koszulInsertDegree t S i.2))) := by
  rw [koszulHomComponent_def,
    δ_v t (t + 1) rfl z (S.card : ℤ) (t + 1 + (S.card : ℤ)) (add_comm _ _)
      (t + (S.card : ℤ)) ((S.card : ℤ) + 1) (by ring) rfl,
    Preadditive.comp_add, smul_add]
  congr 1
  · rw [koszulHomComponent_def, Preadditive.zsmul_comp, Category.assoc]
  · rw [Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc,
      koszulFactorι_comp_d X A ρ a n (⟨S, rfl⟩ : AlternatingCech.Idx r (S.card : ℤ)),
      Preadditive.sum_comp, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.zsmul_comp, Category.assoc,
      koszulFactorι_insertIdx_comp_v X A ρ a J n t z S i, Preadditive.comp_zsmul,
      smul_smul, smul_smul, smul_smul]
    congr 1
    exact koszulTwist_cechSign t S i

/-! ### The isomorphism of complexes -/

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The degreewise comparison, evaluated at a subset, is the twisted restriction to the factor
indexed by it. -/
theorem koszulHomTermEquiv_apply (t : ℤ)
    (z : (ModuleCat.restrictScalars ρ).obj
      (((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
        (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J).X t))
    (S : Finset (Fin r)) :
    koszulHomTermEquiv X A ρ a J n t z S = koszulHomComponent X A ρ a J n t z S :=
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The differential of the complex of `A`-linear global sections of `J` is postcomposition
with the differential of `J`.** -/
theorem moduleGlobalSectionsOverComplex_d_apply (p q : ℤ)
    (h : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ J.X p) :
    ((((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J).d
        p q).hom h = h ≫ J.d p q :=
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The transport of degrees on the complex of `A`-linear global sections is postcomposition
with the transport of degrees of `J`.** This is `CategoryTheory.eqToHom_map` for
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOver`, read on an element. -/
theorem moduleGlobalSectionsOverComplex_eqToHom_apply {p q : ℤ} (hpq : p = q)
    (he : (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).X p =
      (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J).X q)
    (h : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ J.X p) :
    (eqToHom he).hom h = h ≫ eqToHom (congrArg J.X hpq) := by
  subst hpq
  rw [eqToHom_refl, eqToHom_refl]
  exact (Category.comp_id _).symm

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **An integer acts on `Γ_A(𝒞, M)` through its image in `A`.** This is
`Int.cast_smul_eq_zsmul` at the `A`-module of global sections; it is what matches the integer
signs of `AlgebraicGeometry.RingedSite.koszulHomComponent_delta` with the signs in `A` that
`KoszulCoefficientTower.coefficientKoszulDifferential` carries. -/
theorem intCast_smul_moduleGlobalSectionsOver (c : ℤ)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (v : (moduleGlobalSectionsOver X A ρ).obj M) :
    ((c : A) • v : (moduleGlobalSectionsOver X A ρ).obj M) = c • v :=
  Int.cast_smul_eq_zsmul A c v

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The comparison turns Mathlib's `δ` into the coefficient Koszul differential.** This is
`AlgebraicGeometry.RingedSite.koszulHomComponent_delta` with the three remaining pieces of
bookkeeping discharged: the multiplication by `f_i^{n+1}` is moved across to the scalar
`a_i^{n+1} ∈ A` by `AlgebraicGeometry.RingedSite.smul_eq_koszulScalar_comp` and
`AlgebraicGeometry.RingedSite.moduleKoszulValue_koszulExp_insert`, the differential and the
degree transport of `Γ_A(𝒞, J)` are read as postcompositions, and the signs, which are integers
on one side and their images in `A` on the other, are matched by `Int.cast_smul_eq_zsmul`. -/
theorem koszulHomComponent_coefficientKoszulDifferential (t : ℤ)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t)
    (S : Finset (Fin r)) :
    koszulHomComponent X A ρ a J n (t + 1) (δ t (t + 1) z) S =
      (KoszulCoefficientTower.coefficientKoszulDifferential a n
          (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
          t).hom (fun T ↦ koszulHomComponent X A ρ a J n t z T) S := by
  rw [koszulHomComponent_delta X A ρ a J n t z S]
  dsimp only [KoszulCoefficientTower.coefficientKoszulDifferential, ModuleCat.hom_ofHom,
    LinearMap.coe_mk, AddHom.coe_mk]
  refine congrArg (fun w ↦ _ + w) (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [show ((-1 : A) ^ (t + (S.card : ℤ) + 1).natAbs *
        (-1 : A) ^ (S.filter (· < i.1)).card * a i.1 ^ (n + 1)) =
      ((((-1 : ℤ) ^ (t + (S.card : ℤ) + 1).natAbs *
          (-1 : ℤ) ^ (S.filter (· < i.1)).card : ℤ) : A) *
        moduleKoszulValue a (koszulExp n S (insert i.1 S))) from by
      rw [moduleKoszulValue_koszulExp_insert A a n i.2]; push_cast; ring,
    mul_smul ((((-1 : ℤ) ^ (t + (S.card : ℤ) + 1).natAbs *
        (-1 : ℤ) ^ (S.filter (· < i.1)).card : ℤ) : A))
      (moduleKoszulValue a (koszulExp n S (insert i.1 S))),
    smul_eq_koszulScalar_comp X A ρ a (koszulExp n S (insert i.1 S))
      (J.X (t + 1 + (S.card : ℤ)))]
  have hdeg : (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).X (t + ((insert i.1 S).card : ℤ)) =
      (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).X (t + 1 + (S.card : ℤ)) :=
    congrArg _ (koszulInsertDegree t S i.2)
  exact Eq.trans
    (congrArg (fun u : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
          J.X (t + 1 + (S.card : ℤ)) ↦
        (((-1 : ℤ) ^ (t + (S.card : ℤ) + 1).natAbs *
            (-1 : ℤ) ^ (S.filter (· < i.1)).card) •
          (koszulScalar X (fun j ↦ globalSectionOfSections (ρ (a j)))
            (koszulExp n S (insert i.1 S)) ≫ u)))
      (moduleGlobalSectionsOverComplex_eqToHom_apply X A ρ J (koszulInsertDegree t S i.2) hdeg
        (koszulHomComponent X A ρ a J n t z (insert i.1 S))).symm)
    (intCast_smul_moduleGlobalSectionsOver X A ρ
      ((-1 : ℤ) ^ (t + (S.card : ℤ) + 1).natAbs * (-1 : ℤ) ^ (S.filter (· < i.1)).card)
      (J.X (t + 1 + (S.card : ℤ))) _).symm

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The differential of the `A`-linear DG Hom complex, on an element, is Mathlib's `δ`. This is
`CochainComplex.dgCategoryLinear_homComplexModules_d_apply` read after the restriction of
scalars along `ρ`, which changes neither the underlying map nor the element. -/
theorem restrictScalars_homComplexModules_d_apply (t : ℤ)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t) :
    ((((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
          (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J)).d
            t (t + 1)).hom z =
      δ t (t + 1) z :=
  CochainComplex.dgCategoryLinear_homComplexModules_d_apply
    (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J t (t + 1) rfl z

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The degreewise comparison commutes with the differentials.** -/
theorem koszulHomTermEquiv_comm (t : ℤ) :
    (koszulHomTermEquiv X A ρ a J n t).toModuleIso.hom ≫
        KoszulCoefficientTower.coefficientKoszulDifferential a n
          (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
          t =
      (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
            (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J)).d
              t (t + 1) ≫
        (koszulHomTermEquiv X A ρ a J n (t + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [restrictScalars_homComplexModules_d_apply X A ρ a J n t z]
  exact funext fun S ↦
    (koszulHomComponent_coefficientKoszulDifferential X A ρ a J n t z S).symm

/-- **The degreewise comparison is an isomorphism of cochain complexes of `A`-modules.** For
each `n`, the complex of `A`-linear global sections of the internal Hom complex
`SheafHom•_𝒪(K^n, J)` — read through [Stacks, Tag 0A8Z] over `A` as the `A`-linear Hom complex
of the differential graded category of complexes of `𝒪`-modules, which is
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso` — is the `n`-th stage of
`KoszulCoefficientTower.coefficientKoszulTower a` applied to `Γ_A(𝒞, J)`.

This is the degreewise `AlgebraicGeometry.RingedSite.koszulHomTermEquiv` assembled by
`HomologicalComplex.Hom.isoOfComponents`, the commutation with the differentials being
`AlgebraicGeometry.RingedSite.koszulHomComponent_coefficientKoszulDifferential`. -/
def koszulHomComplexIso :
    ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
          (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J) ≅
      ((KoszulCoefficientTower.coefficientKoszulTower a).obj
          (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J)).obj (op n) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun t ↦ (koszulHomTermEquiv X A ρ a J n t).toModuleIso)
    (fun t t' htt' ↦ by
      obtain rfl : t + 1 = t' := htt'
      rw [KoszulCoefficientTower.coefficientKoszulTower_d]
      exact koszulHomTermEquiv_comm X A ρ a J n t)

/-! ### Naturality in `n` -/

/-- **The monomial of the Koszul power transition is `∏_{i ∈ S} a_i`**, which is the scalar
`∏_{i ∈ S} a_i^{(n+1)-n}` by which
`KoszulCoefficientTower.coefficientKoszulTransitionTerm` multiplies the factor indexed by
`S`. -/
theorem moduleKoszulValue_indicator (S : Finset (Fin r)) :
    moduleKoszulValue a (fun i ↦ if i ∈ S then 1 else 0) = ∏ i ∈ S, a i ^ (n + 1 - n) := by
  rw [show n + 1 - n = 1 from by omega, moduleKoszulValue,
    Finset.prod_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) ↦
      show a i ^ (if i ∈ S then 1 else 0) = if i ∈ S then a i ^ 1 else 1 from by
        split <;> simp),
    Finset.prod_ite_mem, Finset.univ_inter]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The Koszul power transition out of the factor indexed by `T`** is multiplication by
`∏_{i ∈ T} f_i` followed by the inclusion of the factor indexed by `T` at the next power. This
is `CategoryTheory.AlternatingCech.termι_comp_mapX` at
`AlgebraicGeometry.RingedSite.koszulPowerTrans`. -/
theorem koszulFactorι_comp_koszulPowerComplexMap {p : ℤ} (T : AlternatingCech.Idx r p) :
    koszulFactorι X A ρ a n T ≫
        (koszulPowerComplexMap X (fun i ↦ globalSectionOfSections (ρ (a i))) n).f p =
      koszulScalar X (fun i ↦ globalSectionOfSections (ρ (a i)))
          (fun i ↦ if i ∈ T.1 then 1 else 0) ≫
        koszulFactorι X A ρ a (n + 1) T :=
  AlternatingCech.termι_comp_mapX
    (koszulPowerTrans X (fun i ↦ globalSectionOfSections (ρ (a i))) n) T

/-- **Precomposition with a map of complexes, on the `Γ(𝒞, 𝒪)`-linear DG Hom complexes.** For
`φ : F ⟶ F'` this is `SheafHom•_𝒪(F', J) ⟶ SheafHom•_𝒪(F, J)` read through [Stacks, Tag 0A8Z];
on cochains it is `z ↦ φ ∘ z`, and it commutes with `CochainComplex.HomComplex.δ` by
`CochainComplex.HomComplex.δ_ofHom_comp`. -/
def homComplexPrecomp
    {F F' : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ}
    (φ : F ⟶ F') :
    (compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules F' J ⟶
      (compDGGlobalSections
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules F J where
  f t := ModuleCat.ofHom
    { toFun := fun z ↦ (Cochain.ofHom φ).comp z (zero_add t)
      map_add' := fun z z' ↦ Cochain.comp_add _ z z' (zero_add t)
      map_smul' := fun c z ↦ Cochain.comp_smul _ c z (zero_add t) }
  comm' t t' htt' := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
    have h1 := CochainComplex.dgCategoryLinear_homComplexModules_d_apply
      (R := ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) F J t t' htt'
      ((Cochain.ofHom φ).comp z (zero_add t))
    have h2 := CochainComplex.dgCategoryLinear_homComplexModules_d_apply
      (R := ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) F' J t t' htt' z
    exact h1.trans ((CochainComplex.HomComplex.δ_ofHom_comp φ z t').trans
      (congrArg (fun y ↦ (Cochain.ofHom φ).comp y (zero_add t')) h2.symm))

/-- **The tower `n ↦ Γ_A(𝒞, SheafHom•_𝒪(K^n, J))`** of cochain complexes of `A`-modules, read
through [Stacks, Tag 0A8Z] over `A` as the `A`-linear Hom cochain complexes, with the transition
from the power `n + 2` to the power `n + 1` given by precomposition with
`AlgebraicGeometry.RingedSite.koszulPowerComplexMap`. -/
def koszulHomComplexSystem : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Functor.ofOpSequence (X := fun m ↦
      ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
          (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m) J))
    fun m ↦ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (homComplexPrecomp X J
        (koszulPowerComplexMap X (fun i ↦ globalSectionOfSections (ρ (a i))) m))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The transition of the tower, on the factor indexed by `S`**, is precomposition with
multiplication by `∏_{i ∈ S} f_i`. No sign enters: the twist `ε_S` is a scalar and commutes with
the Koszul entry. -/
theorem koszulHomComponent_precomp (t : ℤ)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) (n + 1)) J t)
    (S : Finset (Fin r)) :
    koszulHomComponent X A ρ a J n t
        ((Cochain.ofHom (koszulPowerComplexMap X
          (fun i ↦ globalSectionOfSections (ρ (a i))) n)).comp z (zero_add t)) S =
      koszulScalar X (fun i ↦ globalSectionOfSections (ρ (a i)))
          (fun i ↦ if i ∈ S then 1 else 0) ≫
        koszulHomComponent X A ρ a J (n + 1) t z S := by
  rw [koszulHomComponent_def,
    Cochain.comp_v _ z (zero_add t) (S.card : ℤ) (S.card : ℤ) (t + (S.card : ℤ))
      (add_zero _) (add_comm _ _),
    Cochain.ofHom_v, ← Category.assoc,
    koszulFactorι_comp_koszulPowerComplexMap X A ρ a n
      (⟨S, rfl⟩ : AlternatingCech.Idx r (S.card : ℤ)),
    Category.assoc, ← Preadditive.comp_zsmul, koszulHomComponent_def]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The comparison commutes with the transitions.** The transition of
`AlgebraicGeometry.RingedSite.koszulHomComplexSystem` multiplies the factor indexed by `S` by
`∏_{i ∈ S} f_i`, and that of `KoszulCoefficientTower.coefficientKoszulTower` multiplies it by
`∏_{i ∈ S} a_i^{(n+1)-n}`; the two agree by
`AlgebraicGeometry.RingedSite.smul_eq_koszulScalar_comp`. -/
theorem koszulHomComponent_coefficientKoszulTransitionTerm (t : ℤ)
    (z : Cochain (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) (n + 1)) J t)
    (S : Finset (Fin r)) :
    koszulHomComponent X A ρ a J n t
        ((Cochain.ofHom (koszulPowerComplexMap X
          (fun i ↦ globalSectionOfSections (ρ (a i))) n)).comp z (zero_add t)) S =
      (KoszulCoefficientTower.coefficientKoszulTransitionTerm a (n + 1) n
          (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
          t).hom (fun T ↦ koszulHomComponent X A ρ a J (n + 1) t z T) S := by
  dsimp only [KoszulCoefficientTower.coefficientKoszulTransitionTerm, ModuleCat.hom_ofHom,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [← moduleKoszulValue_indicator A a n S]
  exact Eq.trans (koszulHomComponent_precomp X A ρ a J n t z S)
    (smul_eq_koszulScalar_comp X A ρ a (fun i ↦ if i ∈ S then 1 else 0)
      (J.X (t + (S.card : ℤ))) (koszulHomComponent X A ρ a J (n + 1) t z S)).symm

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The degreewise comparison commutes with the transitions.** -/
theorem koszulHomTermEquiv_trans (t : ℤ) :
    (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (homComplexPrecomp X J (koszulPowerComplexMap X
              (fun i ↦ globalSectionOfSections (ρ (a i))) n))).f t ≫
        (koszulHomTermEquiv X A ρ a J n t).toModuleIso.hom =
      (koszulHomTermEquiv X A ρ a J (n + 1) t).toModuleIso.hom ≫
        KoszulCoefficientTower.coefficientKoszulTransitionTerm a (n + 1) n
          (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
          t := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
  exact funext fun S ↦
    koszulHomComponent_coefficientKoszulTransitionTerm X A ρ a J n t z S

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **One step of the comparison of towers.** Precomposition with
`AlgebraicGeometry.RingedSite.koszulPowerComplexMap` corresponds, under the degreewise
comparison, to the transition of `KoszulCoefficientTower.coefficientKoszulTower`. -/
theorem koszulHomComplexIso_precomp :
    ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexPrecomp X J (koszulPowerComplexMap X
            (fun i ↦ globalSectionOfSections (ρ (a i))) n)) ≫
        (koszulHomComplexIso X A ρ a J n).hom =
      (koszulHomComplexIso X A ρ a J (n + 1)).hom ≫
        ((KoszulCoefficientTower.coefficientKoszulTower a).obj
            (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj J)).map (homOfLE (n.le_add_right 1)).op := by
  refine HomologicalComplex.hom_ext _ _ fun t ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    KoszulCoefficientTower.coefficientKoszulTower_transition_f a _ (n + 1) n
      (n.le_add_right 1) t]
  exact koszulHomTermEquiv_trans X A ρ a J n t

/-- **The comparison of towers.** For each `n` the complex of `A`-linear global sections of
`SheafHom•_𝒪(K^n, J)` is the `n`-th stage of `KoszulCoefficientTower.coefficientKoszulTower a`
applied to `Γ_A(𝒞, J)`, naturally in `n`: this is
`AlgebraicGeometry.RingedSite.koszulHomComplexIso` together with
`AlgebraicGeometry.RingedSite.koszulHomComponent_coefficientKoszulTransitionTerm`, which says
that the two transitions agree.

With this, the tower on which `Γ(𝒞, -)` computes `RΓ(𝒞, -)` for the derived limit formula
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem` is
identified, as a tower of complexes of `A`-modules, with the tower whose derived limit is the
derived completion of `RΓ(𝒞, J)` by
`KoszulCompletion.isDerivedLimit_coefficientKoszulTower_derivedCompletion`. -/
def koszulHomComplexSystemIso :
    koszulHomComplexSystem X A ρ a J ≅
      (KoszulCoefficientTower.coefficientKoszulTower a).obj
        (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) := by
  let e : koszulHomComplexSystem X A ρ a J ⟶
      (KoszulCoefficientTower.coefficientKoszulTower a).obj
        (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    NatTrans.ofOpSequence (fun m ↦ (koszulHomComplexIso X A ρ a J m).hom) fun m ↦
      Eq.trans
        (congrArg (fun φ ↦ φ ≫ (koszulHomComplexIso X A ρ a J m).hom)
          (Functor.ofOpSequence_map_homOfLE_succ _ m))
        (koszulHomComplexIso_precomp X A ρ a J m)
  exact NatIso.ofComponents (fun m ↦ koszulHomComplexIso X A ρ a J m.unop)
    fun h ↦ e.naturality h

end Degreewise

/-! ## [Stacks, Tag 0A8Z] over `A` is natural in its source variable -/

section Naturality

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The reading of [Stacks, Tag 0A8Z] over `A` is natural in its source variable.** For
`φ : F ⟶ F'` the identification
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso` carries the `A`-linear
global sections of `AlgebraicGeometry.RingedSite.homMap X φ (𝟙 G)` — the action in the source
variable of `AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor` — to
`AlgebraicGeometry.RingedSite.homComplexPrecomp X G φ`, precomposition on cochains.

This is `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v`, which is [Stacks, Tag 0A90]
(1) globally, read on the cochain attached to an `A`-linear global section: the bridge
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverIso` is the identity on sections, so the
restriction of scalars along `ρ` changes nothing.

It is what carries the tower `n ↦ SheafHom•_𝒪(K^n, J)` of complexes of `𝒪`-modules to
`AlgebraicGeometry.RingedSite.koszulHomComplexSystem`, and so joins the comparison of towers
`AlgebraicGeometry.RingedSite.koszulHomComplexSystemIso` to the sheaf side of
[Stacks, Tag 0BLX]. -/
theorem moduleGlobalSectionsOverHomComplexIso_naturality_source
    {F F' G : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ}
    (φ : F ⟶ F') :
    ((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homMap X φ (𝟙 G)) ≫ (moduleGlobalSectionsOverHomComplexIso A ρ F G).hom =
      (moduleGlobalSectionsOverHomComplexIso A ρ F' G).hom ≫
        ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexPrecomp X G φ) := by
  refine HomologicalComplex.hom_ext _ _ fun t ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  refine (globalSectionsIso_homMap_v X φ (𝟙 G) t p q hpq
      (((sheafHomComplex X F' G).obj.X t).unitHomEquiv s)).trans
    (Eq.trans ?_ (Cochain.comp_v (Cochain.ofHom φ)
      ((AddCommGrpCat.Hom.hom ((sheafHomComplex X F' G).globalSectionsIso.hom.f t)
        (((sheafHomComplex X F' G).obj.X t).unitHomEquiv s)).down)
      (zero_add t) p p q (add_zero p) hpq).symm)
  rw [Cochain.ofHom_v, HomologicalComplex.id_f, Category.comp_id]

end Naturality

/-! ## `Γ_A(𝒞, -)` carries the Koszul Hom tower to the coefficient Koszul tower -/

section SheafTower

attribute [local instance] hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) {r : ℕ}
  (a : Fin r → A)
  (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (n : ℕ)

/-- **The tower `n ↦ SheafHom•_𝒪(K^n, J)`** of internal Hom complexes against the Koszul tower,
as a functor `ℕᵒᵖ ⥤ CochainComplex (Mod 𝒪) ℤ`: the Koszul tower
`AlgebraicGeometry.RingedSite.koszulPowerSystem` composed with the internal Hom bifunctor
`AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor` in its source variable. -/
def koszulSheafHomComplexSystem :
    ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ :=
  (koszulPowerSystem X (fun i ↦ globalSectionOfSections (ρ (a i)))).op ⋙
    (sheafHomComplexBifunctor X).flip.obj J

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The transition of that tower is precomposition with
`AlgebraicGeometry.RingedSite.koszulPowerComplexMap`. -/
theorem koszulSheafHomComplexSystem_map_succ :
    (koszulSheafHomComplexSystem X A ρ a J).map (homOfLE (n.le_add_right 1)).op =
      homMap X (koszulPowerComplexMap X (fun i ↦ globalSectionOfSections (ρ (a i))) n)
        (𝟙 J) := by
  rw [show (koszulSheafHomComplexSystem X A ρ a J).map (homOfLE (n.le_add_right 1)).op =
      ((sheafHomComplexBifunctor X).map
        (op ((koszulPowerSystem X (fun i ↦ globalSectionOfSections (ρ (a i)))).map
          (homOfLE (n.le_add_right 1))))).app J from rfl,
    koszulPowerSystem_map_succ]
  exact sheafHomComplexBifunctor_map_app X _ J

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **One step of the comparison.** [Stacks, Tag 0A8Z] over `A` followed by the Koszul
comparison carries precomposition with `AlgebraicGeometry.RingedSite.koszulPowerComplexMap` to
the transition of `KoszulCoefficientTower.coefficientKoszulTower`. -/
theorem globalSectionsKoszulSheafHomComplexIso_succ :
    ((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homMap X (koszulPowerComplexMap X
            (fun i ↦ globalSectionOfSections (ρ (a i))) n) (𝟙 J)) ≫
        ((moduleGlobalSectionsOverHomComplexIso A ρ
            (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J).trans
          (koszulHomComplexIso X A ρ a J n)).hom =
      ((moduleGlobalSectionsOverHomComplexIso A ρ
            (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) (n + 1)) J).trans
          (koszulHomComplexIso X A ρ a J (n + 1))).hom ≫
        ((KoszulCoefficientTower.coefficientKoszulTower a).obj
            (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj J)).map (homOfLE (n.le_add_right 1)).op := by
  dsimp only [Iso.trans_hom]
  rw [← Category.assoc, moduleGlobalSectionsOverHomComplexIso_naturality_source X A ρ
      (koszulPowerComplexMap X (fun i ↦ globalSectionOfSections (ρ (a i))) n),
    Category.assoc, koszulHomComplexIso_precomp X A ρ a J n, ← Category.assoc]

/-- **`Γ_A(𝒞, -)` carries the tower of Koszul internal Hom complexes to the coefficient Koszul
tower of `Γ_A(𝒞, J)`**, as an isomorphism of functors
`ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ`:

`(n ↦ Γ_A(𝒞, SheafHom•_𝒪(K^n, J))) ≅ (KoszulCoefficientTower.coefficientKoszulTower a).obj
  (Γ_A(𝒞, J))`.

It is the composite of
[Stacks, Tag 0A8Z] over `A`,
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso`, with the Koszul comparison
`AlgebraicGeometry.RingedSite.koszulHomComplexIso`; it is natural in `n` because the former is,
by `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso_naturality_source`, and
the latter is, by `AlgebraicGeometry.RingedSite.koszulHomComplexIso_precomp`.

Here `𝒪` is an arbitrary sheaf of `A`-algebras on an arbitrary ringed site,
`a_1, …, a_r` are arbitrary elements of `A`, and `J` is an arbitrary complex of `𝒪`-modules. -/
def globalSectionsKoszulSheafHomComplexSystemIso :
    koszulSheafHomComplexSystem X A ρ a J ⋙
        (moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (KoszulCoefficientTower.coefficientKoszulTower a).obj
        (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) := by
  let e : koszulSheafHomComplexSystem X A ρ a J ⋙
        (moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (KoszulCoefficientTower.coefficientKoszulTower a).obj
        (((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J) :=
    NatTrans.ofOpSequence
      (fun m ↦ ((moduleGlobalSectionsOverHomComplexIso A ρ
            (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m) J).trans
          (koszulHomComplexIso X A ρ a J m)).hom)
      fun m ↦ Eq.trans
        (congrArg (fun φ ↦ ((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex
              (ComplexShape.up ℤ)).map φ ≫
            ((moduleGlobalSectionsOverHomComplexIso A ρ
                (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m) J).trans
              (koszulHomComplexIso X A ρ a J m)).hom)
          (koszulSheafHomComplexSystem_map_succ X A ρ a J m))
        (globalSectionsKoszulSheafHomComplexIso_succ X A ρ a J m)
  exact NatIso.ofComponents
    (fun m ↦ (moduleGlobalSectionsOverHomComplexIso A ρ
        (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m.unop) J).trans
      (koszulHomComplexIso X A ρ a J m.unop)) fun h ↦ e.naturality h

end SheafTower

/-! ## The comparison of the towers in `D(A)`, as a proposition -/

section Remainder

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}]
  (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)
  {r : ℕ} (a : Fin r → A)
  (J : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ)

/-- **The statement the identity `RΓ(𝒞, ℱ)^∧ ≅ RΓ(𝒞, ℱ^∧)` of [Stacks, Tag 0BLX] rests on**:
that the tower in `D(A)` whose derived limit is `RΓ(𝒞, ℱ^∧)`, namely
`n ↦ RΓ_A(𝒞, R𝑆heafHom_𝒪(K^n, ℱ))` of
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem`, is
the image in `D(A)` of the complex-level tower `n ↦ Γ_A(𝒞, SheafHom•_𝒪(K^n, J))` for `J` a
K-injective representative of `ℱ`.

It holds for `J` K-injective by
`AlgebraicGeometry.RingedSite.derivedKoszulHomTowerComparison`. K-injectivity of `J` is not
removable: for a general `J` the two towers are `RΓ_A(𝒞, -)` and `Γ_A(𝒞, -)` of the same system,
and those differ already at `r = 0`.

Granted this:

* `CategoryTheory.Pretriangulated.IsDerivedLimit.of_natIso` carries the derived limit of
  `isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem` to
  `koszulSheafHomComplexSystem X A ρ a J ⋙ Γ_A(𝒞, -) ⋙ Q`;
* `AlgebraicGeometry.RingedSite.globalSectionsKoszulSheafHomComplexSystemIso` of this file
  carries it on to `KoszulCoefficientTower.coefficientKoszulTower a` applied to `Γ_A(𝒞, J)`;
* `KoszulCompletion.isDerivedLimit_coefficientKoszulTower_derivedCompletion` is a second
  derived limit of that same tower, namely the derived completion of `Γ_A(𝒞, J)`, and
  `CategoryTheory.Pretriangulated.nonempty_iso_of_isDerivedLimit` identifies the two.

Its two halves are objectwise, and the proof below assembles them:
`AlgebraicGeometry.RingedSite.koszulDerivedSheafHomComplexIso` of `KoszulKFlat.lean`, whose
naturality in the source complex is
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality`, and
`isIso_moduleGlobalSectionsDerivedUnit_app_sheafHomComplex_koszulPowerComplex`, which is a
component of the natural transformation
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsDerivedUnit`. Since
`AlgebraicGeometry.RingedSite.derivedSheafHomSystem` is built from
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` while
`koszulDerivedSheafHomComplexIso` is stated for an arbitrary
`AlgebraicGeometry.RingedSite.DerivedInternalHom`, and
`AlgebraicGeometry.RingedSite.canonicalDerivedInternalHom` is a `Classical.choice`, the
assembly is run at the explicit derived internal Hom built from that bifunctor rather than at
the canonical one. -/
def DerivedKoszulHomTowerComparison : Prop :=
  Nonempty (derivedSheafHomSystem X
        (koszulPowerSystem X (fun i ↦ globalSectionOfSections (ρ (a i))) ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj J) ⋙ derivedGlobalSectionsOverUnbounded X A ρ ≅
      koszulSheafHomComplexSystem X A ρ a J ⋙
        (moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q)

end Remainder

/-! ## The comparison of the two towers in `D(A)` -/

section Assembly

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ B, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj B).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)
  {r : ℕ} (a : Fin r → A)
  (J : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ)

/-- **The tower of internal Hom complexes against the Koszul tower compares with the tower of
derived internal Homs**, as a morphism of functors `ℕᵒᵖ ⥤ D(𝒪)`

`(n ↦ Q(SheafHom•_𝒪(K^n, J)))  ⟶  (n ↦ R𝑆heafHom_𝒪(K^n, QJ))`.

At each `n` it is `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`, the canonical
comparison of [Stacks, Tag 08JH], taken at the **explicit** derived internal Hom
`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor` built from
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` — and not at
`AlgebraicGeometry.RingedSite.canonicalDerivedInternalHom`, which is a `Classical.choice` and
whose bifunctor is therefore not the one
`AlgebraicGeometry.RingedSite.derivedSheafHomSystem` is built from.

Naturality in `n` is `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality` in
its source variable, at the transition
`AlgebraicGeometry.RingedSite.koszulPowerComplexMap` of the Koszul tower: both towers act on a
transition by that map, on the left through
`AlgebraicGeometry.RingedSite.koszulSheafHomComplexSystem_map_succ` and on the right through
`AlgebraicGeometry.RingedSite.koszulPowerSystem_map_succ`.

Nothing is assumed of `J` here; it is only the passage to global sections below that needs `J`
to be K-injective. -/
def koszulDerivedSheafHomComplexSystemComparison :
    koszulSheafHomComplexSystem X A ρ a J ⋙ DerivedCategory.Q ⟶
      derivedSheafHomSystem X
        (koszulPowerSystem X (fun i ↦ globalSectionOfSections (ρ (a i))) ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj J) :=
  NatTrans.ofOpSequence
    (fun n ↦ strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
      (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J)
    (fun n ↦ by
      have hcmp := strictlyPerfectHomComparison_naturality X (derivedInternalHomOfBifunctor X)
        (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) (n + 1))
        (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) n) J J
        (koszulPowerComplexMap X (fun i ↦ globalSectionOfSections (ρ (a i))) n) (𝟙 J)
      simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hcmp
      simp only [derivedSheafHomSystem, Functor.comp_map, koszulSheafHomComplexSystem_map_succ,
        koszulPowerSystem_map_succ, Functor.flip_obj_map, Functor.op_map,
        Quiver.Hom.unop_op] at hcmp ⊢
      exact hcmp)

omit [HasWeakSheafify X.J CommRingCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) ⥤
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)).Additive]
  [∀ B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj B).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)] in
/-- The comparison of towers of `AlgebraicGeometry.RingedSite.koszulPowerComplex` is, at each
`n`, the comparison of [Stacks, Tag 08JH]. -/
theorem koszulDerivedSheafHomComplexSystemComparison_app (m : ℕᵒᵖ) :
    (koszulDerivedSheafHomComplexSystemComparison X A ρ a J).app m =
      strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
        (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m.unop) J :=
  rfl

/-- **The comparison of the two towers in `D(A)`**, as a morphism of functors `ℕᵒᵖ ⥤ D(A)`

`(n ↦ Q(Γ_A(𝒞, SheafHom•_𝒪(K^n, J))))  ⟶  (n ↦ RΓ_A(𝒞, R𝑆heafHom_𝒪(K^n, QJ)))`.

It is the composite of two whiskerings and so needs no naturality argument of its own: the
complex-level comparison `Q(Γ_A(𝒞, -)) ⟶ RΓ_A(𝒞, Q -)` is already the natural transformation
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsDerivedUnit` on all of
`CochainComplex (Mod 𝒪) ℤ`, so it may simply be whiskered with the tower
`AlgebraicGeometry.RingedSite.koszulSheafHomComplexSystem`, and
`AlgebraicGeometry.RingedSite.koszulDerivedSheafHomComplexSystemComparison` may then be
whiskered with `RΓ_A(𝒞, -)`. -/
def derivedGlobalSectionsKoszulHomTowerComparison :
    koszulSheafHomComplexSystem X A ρ a J ⋙
        (moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ⟶
      derivedSheafHomSystem X
          (koszulPowerSystem X (fun i ↦ globalSectionOfSections (ρ (a i))) ⋙ DerivedCategory.Q)
          (DerivedCategory.Q.obj J) ⋙
        derivedGlobalSectionsOverUnbounded X A ρ :=
  Functor.whiskerLeft (koszulSheafHomComplexSystem X A ρ a J)
      (moduleGlobalSectionsDerivedUnit X A ρ) ≫
    Functor.whiskerRight (koszulDerivedSheafHomComplexSystemComparison X A ρ a J)
      (derivedGlobalSectionsOverUnbounded X A ρ)

omit [HasWeakSheafify X.J CommRingCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) ⥤
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)).Additive]
  [∀ B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj B).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)] in
/-- The comparison of towers in `D(A)` is, at each `n`, the complex-level comparison
`Q(Γ_A(𝒞, -)) ⟶ RΓ_A(𝒞, Q -)` followed by `RΓ_A(𝒞, -)` applied to the comparison of
[Stacks, Tag 08JH]. -/
theorem derivedGlobalSectionsKoszulHomTowerComparison_app (m : ℕᵒᵖ) :
    (derivedGlobalSectionsKoszulHomTowerComparison X A ρ a J).app m =
      (moduleGlobalSectionsDerivedUnit X A ρ).app
          (sheafHomComplex X
            (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m.unop) J).obj ≫
        (derivedGlobalSectionsOverUnbounded X A ρ).map
          (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
            (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m.unop) J) :=
  rfl

variable [J.IsKInjective]

/-- **Each term of the comparison of towers is invertible**, for `J` K-injective. Its two
factors are: the comparison `Q(Γ_A(𝒞, C)) ⟶ RΓ_A(𝒞, Q C)` at
`C = SheafHom•_𝒪(K^n, J)`, which is K-injective because the Koszul complex is K-flat —
`isIso_moduleGlobalSectionsDerivedUnit_app_sheafHomComplex_koszulPowerComplex`; and the
comparison of [Stacks, Tag 08JH] at the Koszul source, which is invertible because the Koszul
complex is strictly perfect —
`AlgebraicGeometry.RingedSite.isIso_strictlyPerfectHomComparison_koszulPowerComplex`. -/
instance isIso_derivedGlobalSectionsKoszulHomTowerComparison_app (m : ℕᵒᵖ) :
    IsIso ((derivedGlobalSectionsKoszulHomTowerComparison X A ρ a J).app m) := by
  have h₁ : IsIso ((moduleGlobalSectionsDerivedUnit X A ρ).app
      (sheafHomComplex X
        (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m.unop) J).obj) :=
    isIso_moduleGlobalSectionsDerivedUnit_app_sheafHomComplex_koszulPowerComplex X A ρ
      (fun i ↦ globalSectionOfSections (ρ (a i))) m.unop J
  have h₂ : IsIso (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
      (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m.unop) J) :=
    isIso_strictlyPerfectHomComparison_koszulPowerComplex X (derivedInternalHomOfBifunctor X)
      (fun i ↦ globalSectionOfSections (ρ (a i))) m.unop J
  have h₃ : IsIso ((derivedGlobalSectionsOverUnbounded X A ρ).map
      (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
        (koszulPowerComplex X (fun i ↦ globalSectionOfSections (ρ (a i))) m.unop) J)) :=
    Functor.map_isIso _ _
  rw [derivedGlobalSectionsKoszulHomTowerComparison_app]
  exact IsIso.comp_isIso' h₁ h₃

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **`AlgebraicGeometry.RingedSite.DerivedKoszulHomTowerComparison` holds for a K-injective
complex**, the statement the identity `RΓ(𝒞, ℱ)^∧ ≅ RΓ(𝒞, ℱ^∧)` of [Stacks, Tag 0BLX] rests on.
For a K-injective complex `J` of `𝒪`-modules the tower in `D(A)` whose derived limit is
`RΓ(𝒞, ℱ^∧)`, namely `n ↦ RΓ_A(𝒞, R𝑆heafHom_𝒪(K^n, QJ))` of
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem`, is
the image in `D(A)` of the complex-level tower `n ↦ Γ_A(𝒞, SheafHom•_𝒪(K^n, J))`.

The isomorphism is
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsKoszulHomTowerComparison`, invertible
termwise by
`AlgebraicGeometry.RingedSite.isIso_derivedGlobalSectionsKoszulHomTowerComparison_app` and
hence invertible as a morphism of functors by `CategoryTheory.NatIso.isIso_of_isIso_app`.

K-injectivity of `J` is not a restriction on the tag: the identity is proved by choosing a
K-injective representative of `ℱ`, which exists because `Mod(𝒪)` is Grothendieck abelian. It is
also not removable — for a general `J` the right hand tower is `RΓ_A(𝒞, -)` of the derived
internal Homs while the left is `Γ_A(𝒞, -)` of the internal Hom complexes, and those differ
already for `r = 0` and `J` a sheaf with nonvanishing higher cohomology. -/
theorem derivedKoszulHomTowerComparison :
    DerivedKoszulHomTowerComparison X A ρ a J :=
  have : IsIso (derivedGlobalSectionsKoszulHomTowerComparison X A ρ a J) :=
    NatIso.isIso_of_isIso_app (derivedGlobalSectionsKoszulHomTowerComparison X A ρ a J)
  ⟨(asIso (derivedGlobalSectionsKoszulHomTowerComparison X A ρ a J)).symm⟩

end Assembly

end AlgebraicGeometry.RingedSite

end
