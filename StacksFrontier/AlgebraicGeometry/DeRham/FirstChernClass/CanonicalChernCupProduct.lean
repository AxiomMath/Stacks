module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Cup products of Hodge-filtered first Chern classes

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` whose
stalks are local rings, let `Ω^•_{𝒪_X/A}` be the relative de Rham complex, and let
`γ₁ : Pic(X) ⟶ H²(X, σ^{≥1}Ω^•_{𝒪_X/A})` be the Hodge-filtered first Chern class of
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass`. Taking the cup
product of Section 50.7 we obtain, for `a` invertible modules `L₁, …, L_a`, the class

`ξ = γ₁(L₁) ∪ … ∪ γ₁(L_a) ∈ H^{2a}(X, σ^{≥a}Ω^•_{𝒪_X/A})`.

The inclusion `σ^{≥a}Ω^• ⟶ Ω^•` sends `ξ` to `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)` in
`H^{2a}_{dR}(X/S)`, so that product lies in the `a`-th step `F^a H^{2a}_{dR}(X/S)` of the Hodge
filtration, and the projection `σ^{≥a}Ω^• ⟶ Ω^a[-a]` sends `ξ` to
`(-1)^{a(a - 1)/2} · c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)` in `H^{2a}(X, Ω^a[-a]) = H^a(X, Ω^a)`,
for the cup product on Hodge cohomology of Tag 0FM4. These are the clauses `F`–`I` of
Remark 50.9.2, Tag 0FME, for every `a`; the source states clause `I` without the sign, which the
identifications force (it is `-1` for `a ≡ 2, 3 mod 4`). The clauses `A`–`E`, the case of a
single invertible module, are in
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass`, and
`AlgebraicGeometry.SheafOfModules.remark_filteredFirstChernClass` states all nine at once.

All cup products here are the cup product of Cohomology, Section 0FKU, along the multiplication of
complexes the source names, with no parameter: they are the pairing
`AlgebraicGeometry.SheafOfModules.canonicalPairing` built from the canonical global cup product in
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct`, along

* the multiplication `Tot(σ^{≥i}Ω^• ⊗_A σ^{≥j}Ω^•) ⟶ σ^{≥(i + j)}Ω^•` of the Hodge filtration,
  giving the cup product `AlgebraicGeometry.SheafOfModules.hodgeFiltrationCup` of Section 50.7 on
  the hypercohomology of the brutal truncations;
* the wedge product of Tag 0FM2, giving the cup product
  `AlgebraicGeometry.SheafOfModules.deRhamCup` on `H^*_{dR}(X/S)` of Section 50.4;
* the wedge product `Tot(Ω^p[-p] ⊗_A Ω^q[-q]) ⟶ Ω^{p + q}[-(p + q)]` of the graded pieces, giving
  the cup product `AlgebraicGeometry.SheafOfModules.gradedPieceCup` on the graded pieces
  `H^n(X, Ω^p[-p])`;
* the wedge product `Ω^p[0] ⊗_A Ω^q[0] ⟶ Ω^{p + q}[0]` of the sheaves of forms placed in degree
  `0`, giving the cup product `AlgebraicGeometry.SheafOfModules.hodgeCup` on Hodge cohomology
  `H^i(X, Ω^p)` of Tag 0FM4, of
  `StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct`.

Through `H^{i + p}(X, Ω^p[-p]) = H^i(X, Ω^p)` the cup product on the graded pieces is the Hodge
cup product up to the sign `(-1)^{iq}`
(`AlgebraicGeometry.SheafOfModules.hodgeGradedIso_gradedPieceCup`), from which clause `I` and its
sign follow.

The proofs are the inductions on the number of factors of
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredChernCupProduct`, which are carried
out there for every natural pairing, specialised to this one.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.gradedPieceCup`: the cup product on the graded pieces
  `H^*(X, Ω^p[-p])` of the Hodge filtration.
* `AlgebraicGeometry.SheafOfModules.filteredChernProduct`: **the `a`-fold cup product
  `ξ = γ₁(L₁) ∪ … ∪ γ₁(L_a) ∈ H^{2a}(X, σ^{≥a}Ω^•)`**, clause `F`.
* `AlgebraicGeometry.SheafOfModules.deRhamChernProduct` and
  `AlgebraicGeometry.SheafOfModules.hodgeChernProduct`: the `a`-fold cup products
  `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)` and `c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)`.

## Main results

* `AlgebraicGeometry.SheafOfModules.gradedPieceProjectionCohomologyMap_hodgeFiltrationCup`: the
  projections `σ^{≥p}Ω^• ⟶ Ω^p[-p]` onto the bottom graded pieces are multiplicative.
* `AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianMap_filteredChernProduct`:
  **the image of `ξ` under `σ^{≥a}Ω^• ⟶ Ω^•` is `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)`**, clause `G`.
* `AlgebraicGeometry.SheafOfModules.deRhamChernProduct_mem_hodgeFiltrationAbelian`:
  **`c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a) ∈ F^a H^{2a}_{dR}(X/S)`**, clause `H`.
* `AlgebraicGeometry.SheafOfModules.hodgeGradedIso_inv_gradedPieceProjection_filteredChernProduct`:
  **the image of `ξ` under `σ^{≥a}Ω^• ⟶ Ω^a[-a]`, read in `H^a(X, Ω^a)`, is
  `(-1)^{a(a - 1)/2} · c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)`** for the Hodge cup product of
  Tag 0FM4, clause `I` with its sign.
* `AlgebraicGeometry.SheafOfModules.remark_filteredFirstChernClass`: **Remark 50.9.2 in full**,
  all nine clauses for every `a` in one statement.

## Implementation notes

A product of `a` classes is indexed by `k = a - 1` and a family `L : ℕ → Pic(X)`, the factors
being `L 0, …, L k` in that order, so that the number of factors is at least one, as in the
source. Its filtration index and degree are `AlgebraicGeometry.SheafOfModules.cupLength k` and
`AlgebraicGeometry.SheafOfModules.cupDegree k`, built by the same recursion as the product, and
`cupLength_eq` and `cupDegree_eq` identify them with `a` and `2a`. The group
`H^{2a}(X, Ω^a[-a])` of clause `I` is the Hodge cohomology group `H^a(X, Ω^a)` of the source by
`AlgebraicGeometry.SheafOfModules.hodgeGradedIso`.

## References

* [Stacks Project, Tag 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Section 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The cup product on the graded pieces -/

/-- **The cup product on the graded pieces of the Hodge filtration**,

`H^i(X, Ω^p[-p]) × H^j(X, Ω^q[-q]) ⟶ H^{i + j}(X, Ω^{p + q}[-(p + q)])`,

the cup product of Cohomology, Section 0FKU along the wedge product
`AlgebraicGeometry.SheafOfModules.gradedPieceWedge` of the graded pieces. Through
`H^i(X, Ω^p[-p]) = H^{i - p}(X, Ω^p)` this is the cup product on Hodge cohomology with its total
grading. The filtration indices are natural numbers `a` and `b`, read into `ℤ` through `p` and `q`
constrained by `hp` and `hq`. -/
def gradedPieceCup (a b : ℕ) (p q : ℤ) (hp : (a : ℤ) = p) (hq : (b : ℤ) = q) (i j : ℤ) :
    gradedPieceCohomology B D p i → gradedPieceCohomology B D q j →
      gradedPieceCohomology B D (p + q) (i + j) :=
  TruncationCupProduct.cupGradedPiece B D truncationCupProduct a b p q hp hq i j

/-- **The projections onto the bottom graded pieces are multiplicative**: the maps
`H^n(X, σ^{≥p}Ω^•) ⟶ H^n(X, Ω^p[-p])` carry the cup product of Section 50.7 on the brutal
truncations to the cup product on the graded pieces. -/
theorem gradedPieceProjectionCohomologyMap_hodgeFiltrationCup (a b : ℕ) (p q : ℤ)
    (hp : (a : ℤ) = p) (hq : (b : ℤ) = q) (i j : ℤ)
    (x : truncatedDeRhamCohomologyAbelian B D p i)
    (y : truncatedDeRhamCohomologyAbelian B D q j) :
    (gradedPieceProjectionCohomologyMap B D (p + q) (i + j)).hom
        (hodgeFiltrationCup B D p q i j x y) =
      gradedPieceCup B D a b p q hp hq i j
        ((gradedPieceProjectionCohomologyMap B D p i).hom x)
        ((gradedPieceProjectionCohomologyMap B D q j).hom y) :=
  TruncationCupProduct.gradedPieceMap_cup B D truncationCupProduct a b p q hp hq i j x y

/-! ### Hodge cohomology and the graded pieces -/

/-- **`H^i(X, Ω^a) ≅ H^n(X, Ω^a[-a])`** for `i + a = n`,
`AlgebraicGeometry.SheafOfModules.hodgeCohomologyIsoGradedPiece` with the filtration index a
parameter constrained by `hp`, so that it can be read off
`AlgebraicGeometry.SheafOfModules.cupLength`. -/
def hodgeGradedIso (a i : ℕ) (p n : ℤ) (hp : (a : ℤ) = p) (hn : (i : ℤ) + p = n) :
    ((sectionsFunctor X.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X a) ≅
      gradedPieceCohomology B D p n := by
  subst hp
  exact hodgeCohomologyIsoGradedPiece B D a i n hn

/-- **The cup product on the graded pieces is the Hodge cup product of Tag 0FM4, up to the sign
`(-1)^{ib}`**, in the indexing of `gradedPieceCup`: for `x ∈ H^n(X, Ω^a[-a])` and
`y ∈ H^m(X, Ω^b[-b])`, read in `H^i(X, Ω^a)` and `H^j(X, Ω^b)`. -/
theorem hodgeGradedIso_gradedPieceCup (a b c i j l : ℕ) (hc : a + b = c) (hl : i + j = l)
    (p q n m : ℤ) (hp : (a : ℤ) = p) (hq : (b : ℤ) = q) (hn : (i : ℤ) + p = n)
    (hm : (j : ℤ) + q = m) (x : gradedPieceCohomology B D p n)
    (y : gradedPieceCohomology B D q m) :
    (hodgeGradedIso B D c l (p + q) (n + m) (by subst hc hp hq; push_cast; rfl)
        (by subst hl hn hm; push_cast; ring)).inv.hom (gradedPieceCup B D a b p q hp hq n m x y) =
      ((i : ℤ) * (b : ℤ)).negOnePow • hodgeCup B D a b c hc i j l hl
        ((hodgeGradedIso B D a i p n hp hn).inv.hom x)
        ((hodgeGradedIso B D b j q m hq hm).inv.hom y) := by
  subst hc hl hp hq hn hm
  exact hodgeCohomologyIsoGradedPiece_gradedPieceCup B D a b i j _ _ rfl rfl x y

/-! ### The `a`-fold products -/

section Classes

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- **Stacks Project, Tag 0FME.** **The `a`-fold cup product
`ξ = γ₁(L₁) ∪ … ∪ γ₁(L_a) ∈ H^{2a}(X, σ^{≥a}Ω^•_{𝒪_X/A})`** of Hodge-filtered first Chern
classes, for `a = k + 1` invertible modules with Picard classes `L 0, …, L k`, the cup product
being the one of Section 50.7, `AlgebraicGeometry.SheafOfModules.hodgeFiltrationCup`.

The filtration index and the cohomological degree are `AlgebraicGeometry.SheafOfModules.cupLength`
and `AlgebraicGeometry.SheafOfModules.cupDegree`, which `cupLength_eq` and `cupDegree_eq` identify
with `a` and `2a`. -/
@[stacks 0FME "Remark 50.9.2, clause F of A-I: the a-fold cup product \
ξ = γ₁(L₁) ∪ … ∪ γ₁(L_a) ∈ H^{2a}(X, σ^{≥a}Ω^•), for every a, formed with the cup product of \
Section 50.7 on the hypercohomology of the brutal truncations (`hodgeFiltrationCup`, the cup \
product of Cohomology Section 0FKU along the multiplication of the Hodge filtration) from the \
class γ₁ of clause B"]
def filteredChernProduct : (k : ℕ) →
    (ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) →
      truncatedDeRhamCohomologyAbelian B D (cupLength k) (cupDegree k)
  | 0, L => filteredFirstChernClass B D (L 0)
  | (k + 1), L => hodgeFiltrationCup B D 1 (cupLength k) 2 (cupDegree k)
      (filteredFirstChernClass B D (L 0)) (filteredChernProduct k (fun i => L (i + 1)))

/-- The `a`-fold cup product `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a) ∈ H^{2a}_{dR}(X/S)` of de Rham first
Chern classes, for the cup product `AlgebraicGeometry.SheafOfModules.deRhamCup` on de Rham
cohomology. -/
def deRhamChernProduct : (k : ℕ) →
    (ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) →
      deRhamCohomologyAbelian B D (cupDegree k)
  | 0, L => deRhamFirstChernClassAbelian B D (L 0)
  | (k + 1), L => deRhamCup B D 2 (cupDegree k)
      (deRhamFirstChernClassAbelian B D (L 0)) (deRhamChernProduct k (fun i => L (i + 1)))

/-- The `a`-fold cup product `c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)` of Hodge first Chern classes,
for the cup product `AlgebraicGeometry.SheafOfModules.gradedPieceCup` on Hodge cohomology, formed
in `H^{2a}(X, Ω^a[-a])`, which is the Hodge cohomology group `H^a(X, Ω^a)` of the source by
`gradedPieceCohomologyIsoHodgeCohomology B D (k + 1) (cupLength k) (cupDegree k)
  (cast_eq_cupLength k) (cupLength_add_cupLength k)`. -/
def hodgeChernProduct : (k : ℕ) →
    (ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) →
      gradedPieceCohomology B D (cupLength k) (cupDegree k)
  | 0, L => hodgeFirstChernClassGraded B D (L 0)
  | (k + 1), L => gradedPieceCup B D 1 (k + 1) 1 (cupLength k) rfl (cast_eq_cupLength k)
      2 (cupDegree k) (hodgeFirstChernClassGraded B D (L 0))
      (hodgeChernProduct k (fun i => L (i + 1)))

/-- The `a`-fold cup product `c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a) ∈ H^a(X, Ω^a_{𝒪_X/A})` of
Hodge first Chern classes, for the cup product on Hodge cohomology of Tag 0FM4,
`AlgebraicGeometry.SheafOfModules.hodgeCup`: the cup product of Cohomology, Section 0FKU along
the wedge product `Ω^p ⊗_A Ω^q ⟶ Ω^{p + q}` on the sheaves of forms placed in degree `0`. -/
def hodgeCupChernProduct : (k : ℕ) →
    (ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) →
      ((sectionsFunctor X.carrier ⊤).rightDerived (k + 1)).obj
        ((deRhamAbelianComplex B D).X (k + 1))
  | 0, L => hodgeFirstChernClassAbelian B D (L 0)
  | (k + 1), L => hodgeCup B D 1 (k + 1) (k + 1 + 1) (by omega) 1 (k + 1) (k + 1 + 1) (by omega)
      (hodgeFirstChernClassAbelian B D (L 0)) (hodgeCupChernProduct k (fun i => L (i + 1)))

/-- **The sign `(-1)^{a(a - 1)/2}`** of a product of `a = k + 1` Hodge first Chern classes. -/
def hodgeChernSign (k : ℕ) : ℤˣ := (((k + 1) * k / 2 : ℕ) : ℤ).negOnePow

/-- `(-1)^{(a + 1)a/2} = (-1)^a (-1)^{a(a - 1)/2}`. -/
theorem hodgeChernSign_succ (k : ℕ) :
    hodgeChernSign (k + 1) = ((1 : ℕ) * ((k + 1 : ℕ) : ℤ)).negOnePow * hodgeChernSign k := by
  have h : (k + 1 + 1) * (k + 1) / 2 = (k + 1) * k / 2 + (k + 1) := by
    have : (k + 1 + 1) * (k + 1) = (k + 1) * k + (k + 1) * 2 := by ring
    rw [this, Nat.add_mul_div_right _ _ (by norm_num)]
  rw [hodgeChernSign, hodgeChernSign, h, Nat.cast_add, Int.negOnePow_add, mul_comm]
  push_cast
  ring_nf

/-- The `a`-fold product of Hodge-filtered first Chern classes is the one formed with the natural
pairing `AlgebraicGeometry.SheafOfModules.truncationCupProduct`. -/
theorem filteredChernProduct_eq (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    filteredChernProduct B D k L =
      TruncationCupProduct.filteredChernProduct B D truncationCupProduct k L := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    change hodgeFiltrationCup B D 1 (cupLength k) 2 (cupDegree k) _
        (filteredChernProduct B D k (fun i => L (i + 1))) = _
    rw [ih]
    rfl

/-- The `a`-fold product of de Rham first Chern classes is the one formed with the natural pairing
`AlgebraicGeometry.SheafOfModules.truncationCupProduct`. -/
theorem deRhamChernProduct_eq (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    deRhamChernProduct B D k L =
      TruncationCupProduct.deRhamChernProduct B D truncationCupProduct k L := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    change deRhamCup B D 2 (cupDegree k) _ (deRhamChernProduct B D k (fun i => L (i + 1))) = _
    rw [ih]
    rfl

/-- The `a`-fold product of Hodge first Chern classes is the one formed with the natural pairing
`AlgebraicGeometry.SheafOfModules.truncationCupProduct`. -/
theorem hodgeChernProduct_eq (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    hodgeChernProduct B D k L =
      TruncationCupProduct.hodgeChernProduct B D truncationCupProduct k L := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    change gradedPieceCup B D 1 (k + 1) 1 (cupLength k) rfl (cast_eq_cupLength k) 2 (cupDegree k) _
        (hodgeChernProduct B D k (fun i => L (i + 1))) = _
    rw [ih]
    rfl

/-- The degree of the `a`-fold product: `a + a = 2a`, read off `cupLength` and `cupDegree`. -/
theorem cast_add_cupLength (k : ℕ) : ((k + 1 : ℕ) : ℤ) + cupLength k = cupDegree k := by
  rw [cast_eq_cupLength]
  exact cupLength_add_cupLength k

/-- The Hodge-graded first Chern class is the Hodge first Chern class read in
`H^2(X, Ω^1[-1])` through `hodgeGradedIso`. -/
theorem hodgeGradedIso_hom_hodgeFirstChernClassAbelian
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property) :
    (hodgeGradedIso B D 1 1 1 2 rfl rfl).hom.hom (hodgeFirstChernClassAbelian B D c) =
      hodgeFirstChernClassGraded B D c :=
  rfl

/-- Reading the Hodge first Chern class in `H^2(X, Ω^1[-1])` and back is the identity. -/
private theorem hodgeGradedIso_inv_hom_hodgeFirstChernClassAbelian
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property) :
    (hodgeGradedIso B D 1 1 1 2 rfl rfl).inv.hom (hodgeFirstChernClassGraded B D c) =
      hodgeFirstChernClassAbelian B D c := by
  have h := ConcreteCategory.congr_hom (hodgeGradedIso B D 1 1 1 2 rfl rfl).hom_inv_id
    (hodgeFirstChernClassAbelian B D c)
  rw [← hodgeGradedIso_hom_hodgeFirstChernClassAbelian]
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h

/-- **The `a`-fold graded-piece product of Hodge first Chern classes, read in `H^a(X, Ω^a)`, is
`(-1)^{a(a - 1)/2}` times the `a`-fold Hodge cup product.** -/
theorem hodgeGradedIso_inv_hodgeChernProduct (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (hodgeGradedIso B D (k + 1) (k + 1) (cupLength k) (cupDegree k) (cast_eq_cupLength k)
        (cast_add_cupLength k)).inv.hom (hodgeChernProduct B D k L) =
      hodgeChernSign k • hodgeCupChernProduct B D k L := by
  induction k generalizing L with
  | zero =>
    have hs : hodgeChernSign 0 = 1 := by simp [hodgeChernSign]
    rw [hs, one_smul]
    exact hodgeGradedIso_inv_hom_hodgeFirstChernClassAbelian B D (L 0)
  | succ k ih =>
    have e := hodgeGradedIso_gradedPieceCup B D 1 (k + 1) (k + 1 + 1) 1 (k + 1) (k + 1 + 1)
      (by omega) (by omega) 1 (cupLength k) 2 (cupDegree k) rfl (cast_eq_cupLength k) rfl
      (cast_add_cupLength k) (hodgeFirstChernClassGraded B D (L 0))
      (hodgeChernProduct B D k (fun i => L (i + 1)))
    refine e.trans ?_
    rw [hodgeGradedIso_inv_hom_hodgeFirstChernClassAbelian, ih, hodgeCup_units_smul_right,
      smul_smul, hodgeChernSign_succ]
    rfl

/-! ### The images of the `a`-fold product -/

/-- **Stacks Project, Tag 0FME.** **The image of `ξ = γ₁(L₁) ∪ … ∪ γ₁(L_a)` under
`σ^{≥a}Ω^• ⟶ Ω^•` is `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)` in `H^{2a}_{dR}(X/S)`.**

The induction is on the number of factors: for one factor this is clause `C`,
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian_eq`, and the inductive step is the
commutative diagram of Section 50.7,
`AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianMap_hodgeFiltrationCup`. -/
@[stacks 0FME "Remark 50.9.2, clause G of A-I: the map σ^{≥a}Ω^• ⟶ Ω^• sends ξ to the a-fold \
product c₁^dR(L₁) ∪ … ∪ c₁^dR(L_a) in H^{2a}_dR(X/S), for every a, both cup products being those \
of Cohomology Section 0FKU (`hodgeFiltrationCup` and `deRhamCup`)"]
theorem truncatedDeRhamCohomologyAbelianMap_filteredChernProduct (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (truncatedDeRhamCohomologyAbelianMap B D (cupLength k) (cupDegree k)).hom
        (filteredChernProduct B D k L) = deRhamChernProduct B D k L := by
  rw [filteredChernProduct_eq, deRhamChernProduct_eq]
  exact TruncationCupProduct.truncatedDeRhamCohomologyAbelianMap_filteredChernProduct B D
    truncationCupProduct k L

/-- **Stacks Project, Tag 0FME.** **`c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)` lies in
`F^a H^{2a}_{dR}(X/S)`**, the `a`-th step of the Hodge filtration of Tag 0FM8.

The step `F^a H^{2a}_{dR}` is the image of `H^{2a}(X, σ^{≥a}Ω^•) ⟶ H^{2a}_{dR}`, and
`AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianMap_filteredChernProduct`
exhibits the `a`-fold product as the image of `ξ` under exactly that map. Membership in the step is
written as in
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian_mem_hodgeFiltrationAbelian`: the
class is the image of an element of the subobject. -/
@[stacks 0FME "Remark 50.9.2, clause H of A-I: the a-fold product c₁^dR(L₁) ∪ … ∪ c₁^dR(L_a), for \
the cup product of Cohomology Section 0FKU on de Rham cohomology (`deRhamCup`), is contained in \
the a-th step F^a H^{2a}_dR(X/S) of the Hodge filtration, for every a"]
theorem deRhamChernProduct_mem_hodgeFiltrationAbelian (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    ∃ y : (hodgeFiltrationAbelian B D (cupLength k) (cupDegree k) : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D (cupLength k) (cupDegree k)).arrow).hom y =
        deRhamChernProduct B D k L := by
  rw [← truncatedDeRhamCohomologyAbelianMap_filteredChernProduct B D k L]
  exact truncatedDeRhamCohomologyAbelianMap_mem_hodgeFiltrationAbelian B D _ _ _

/-- **The image of `ξ = γ₁(L₁) ∪ … ∪ γ₁(L_a)` under `σ^{≥a}Ω^• ⟶ Ω^a_{𝒪_X/A}[-a]` is the `a`-fold
product of the `c₁^{Hodge}(L_i)` for the cup product on the graded pieces**,
`AlgebraicGeometry.SheafOfModules.gradedPieceCup`, in `H^{2a}(X, Ω^a[-a])`. Clause `I` itself,
with the Hodge cup product of Tag 0FM4, is
`AlgebraicGeometry.SheafOfModules.hodgeGradedIso_inv_gradedPieceProjection_filteredChernProduct`,
deduced from this one.

The induction is on the number of factors: for one factor this is clause `E`, in the form
`AlgebraicGeometry.SheafOfModules.gradedPieceProjectionCohomologyMap_filteredFirstChernClass`, and
the inductive step is the multiplicativity of the projection,
`AlgebraicGeometry.SheafOfModules.gradedPieceProjectionCohomologyMap_hodgeFiltrationCup`. -/
theorem gradedPieceProjectionCohomologyMap_filteredChernProduct (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (gradedPieceProjectionCohomologyMap B D (cupLength k) (cupDegree k)).hom
        (filteredChernProduct B D k L) = hodgeChernProduct B D k L := by
  rw [filteredChernProduct_eq, hodgeChernProduct_eq]
  exact TruncationCupProduct.gradedPieceProjectionCohomologyMap_filteredChernProduct B D
    truncationCupProduct k L

/-- **Stacks Project, Tag 0FME.** **The image of `ξ = γ₁(L₁) ∪ … ∪ γ₁(L_a)` under
`σ^{≥a}Ω^• ⟶ Ω^a_{𝒪_X/A}[-a]`, read in `H^a(X, Ω^a_{𝒪_X/A})`, is
`(-1)^{a(a - 1)/2} · c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)`**, the cup product being the one on
Hodge cohomology of Tag 0FM4, `AlgebraicGeometry.SheafOfModules.hodgeCup`: the cup product of
Cohomology, Section 0FKU along the wedge product `Ω^p ⊗_A Ω^q ⟶ Ω^{p + q}` on the sheaves of forms
placed in degree `0`. The identification `H^{2a}(X, Ω^a[-a]) = H^a(X, Ω^a)` is
`AlgebraicGeometry.SheafOfModules.hodgeGradedIso`, the comparison of the two indexings of the
right derived functors followed by the degree shift of
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`, which for `a = 1` is the
identification of clause `E`.

**The sign.** The source states clause `I` without a sign. Through these identifications the cup
product on the graded pieces is the Hodge cup product up to `(-1)^{ib}` on
`H^{i + a}(Ω^a[-a]) × H^{j + b}(Ω^b[-b])`
(`AlgebraicGeometry.SheafOfModules.hodgeCohomologyIsoGradedPiece_gradedPieceCup`): moving the
shift `[-b]` of the second factor past a class of degree `i` costs `(-1)^{ib}`
(`Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_shift₂`), and moving the shift `[-a]`
of the first factor costs nothing (`totalCupPairing_shift₁`). Each new factor `c₁(L)` has `i = 1`,
so the `(k + 1)`-st factor contributes `(-1)^k`, and the product of `a` factors carries
`(-1)^{0 + 1 + ⋯ + (a - 1)} = (-1)^{a(a - 1)/2}`, which is `-1` for `a ≡ 2, 3 mod 4`. This is the
corrected form of clause `I`. -/
@[stacks 0FME "Remark 50.9.2, clause I of A-I, with the sign the identifications force: the map \
σ^{≥a}Ω^• ⟶ Ω^a[-a] sends ξ to (-1)^{a(a-1)/2} · c₁^Hodge(L₁) ∪ … ∪ c₁^Hodge(L_a) in \
H^{2a}(X, Ω^a[-a]) = H^a(X, Ω^a), for every a, the cup product being the Hodge cup product of \
Tag 0FM4 (`hodgeCup`: the cup product of Cohomology Section 0FKU along the wedge product \
Ω^p ⊗ Ω^q ⟶ Ω^{p+q} on the sheaves of forms in degree 0). The source states it without the sign; \
the sign is -1 for a ≡ 2, 3 mod 4"]
theorem hodgeGradedIso_inv_gradedPieceProjection_filteredChernProduct (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (hodgeGradedIso B D (k + 1) (k + 1) (cupLength k) (cupDegree k) (cast_eq_cupLength k)
        (cast_add_cupLength k)).inv.hom
      ((gradedPieceProjectionCohomologyMap B D (cupLength k) (cupDegree k)).hom
        (filteredChernProduct B D k L)) =
      hodgeChernSign k • hodgeCupChernProduct B D k L := by
  rw [gradedPieceProjectionCohomologyMap_filteredChernProduct]
  exact hodgeGradedIso_inv_hodgeChernProduct B D k L

/-! ### Remark 50.9.2 in full -/

/-- **Stacks Project, Tag 0FME.** **Remark 50.9.2 in full**: all nine clauses of the remark, for
every number `a = k + 1` of invertible modules, in one statement. In order:

* **(A)** `d log`, viewed as a map `𝒪_X^*[-1] ⟶ σ^{≥1}Ω^•_{𝒪_X/A}` — the morphism is
  `AlgebraicGeometry.SheafOfModules.filteredLogarithmicDifferentialComplexMap`, and the first
  conjunct says that it is `d log`;
* **(B)** the class `γ₁(L) ∈ H²(X, σ^{≥1}Ω^•)` — the morphism
  `AlgebraicGeometry.SheafOfModules.filteredFirstChernClass` occurring in the conjuncts below;
* **(C)** the image of `γ₁(L)` under `σ^{≥1}Ω^• ⟶ Ω^•` is `c₁^{dR}(L)`;
* **(D)** hence `c₁^{dR}(L) ∈ F¹H²_{dR}(X/S)`;
* **(E)** the image of `γ₁(L)` under `σ^{≥1}Ω^• ⟶ Ω¹[-1]` is `c₁^{Hodge}(L)`;
* **(F)** the `a`-fold cup product `ξ = γ₁(L₁) ∪ … ∪ γ₁(L_a) ∈ H^{2a}(X, σ^{≥a}Ω^•)` — the class
  `AlgebraicGeometry.SheafOfModules.filteredChernProduct` occurring in the conjuncts below;
* **(G)** the image of `ξ` under `σ^{≥a}Ω^• ⟶ Ω^•` is `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)` in
  `H^{2a}_{dR}(X/S)`;
* **(H)** hence that product lies in `F^a H^{2a}_{dR}(X/S)`;
* **(I)** the image of `ξ` under `σ^{≥a}Ω^• ⟶ Ω^a[-a]`, read in `H^a(X, Ω^a_{𝒪_X/A})`, is
  `(-1)^{a(a - 1)/2} · c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)` for the Hodge cup product of
  Tag 0FM4; the sign, absent from the source, is the one the identifications force (see
  `hodgeGradedIso_inv_gradedPieceProjection_filteredChernProduct`).

Each conjunct is one of the theorems above or of
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass`. -/
@[stacks 0FME "Remark 50.9.2 IN FULL: ALL NINE CLAUSES A-I, FOR EVERY a. The conjuncts in order \
are A (d log as a map into σ^{≥1}Ω^•, pinned down to d log), B (the class γ₁(L), the morphism \
`filteredFirstChernClass` the conjuncts speak of), C (its image in H²_dR is c₁^dR), D (so \
c₁^dR ∈ F¹H²_dR), E (its image in H²(Ω¹[-1]) = H¹(Ω¹) is c₁^Hodge), F (the a-fold product ξ, the \
class `filteredChernProduct` the conjuncts speak of), G (its image in H^{2a}_dR is the a-fold \
product of the c₁^dR), H (so that product lies in F^a H^{2a}_dR) and I (its image in \
H^{2a}(Ω^a[-a]) = H^a(Ω^a) is (-1)^{a(a-1)/2} times the a-fold Hodge cup product of Tag 0FM4 of \
the c₁^Hodge, the sign being the one the identifications force, absent from the source). Every \
cup product is the one of Cohomology Section 0FKU along the multiplication the source names"]
theorem remark_filteredFirstChernClass (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (filteredLogarithmicDifferentialComplexMap B D ≫
        HomologicalComplex.ιStupidTrunc (deRhamAbelianComplexInt B D) (embeddingUpIntGE 1) =
      logarithmicDifferentialComplexMap B D) ∧
    (∀ c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property,
      deRhamFirstChernClassAbelian B D c =
        (truncatedDeRhamCohomologyAbelianMap B D 1 2).hom (filteredFirstChernClass B D c)) ∧
    (∀ c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property,
      ∃ y : (hodgeFiltrationAbelian B D 1 2 : AddCommGrpCat.{u}),
        ((hodgeFiltrationAbelian B D 1 2).arrow).hom y = deRhamFirstChernClassAbelian B D c) ∧
    (∀ c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property,
      (degreeOneProjectionCohomologyMap B D).hom (filteredFirstChernClass B D c) =
        (sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier
          ((deRhamAbelianComplex B D).X 1)).hom.hom (hodgeFirstChernClassAbelian B D c)) ∧
    ((truncatedDeRhamCohomologyAbelianMap B D (cupLength k) (cupDegree k)).hom
      (filteredChernProduct B D k L) = deRhamChernProduct B D k L) ∧
    (∃ y : (hodgeFiltrationAbelian B D (cupLength k) (cupDegree k) : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D (cupLength k) (cupDegree k)).arrow).hom y =
        deRhamChernProduct B D k L) ∧
    ((hodgeGradedIso B D (k + 1) (k + 1) (cupLength k) (cupDegree k) (cast_eq_cupLength k)
        (cast_add_cupLength k)).inv.hom
      ((gradedPieceProjectionCohomologyMap B D (cupLength k) (cupDegree k)).hom
        (filteredChernProduct B D k L)) =
      hodgeChernSign k • hodgeCupChernProduct B D k L) :=
  ⟨filteredLogarithmicDifferentialComplexMap_ι B D,
    deRhamFirstChernClassAbelian_eq B D,
    deRhamFirstChernClassAbelian_mem_hodgeFiltrationAbelian B D,
    hodgeFirstChernClassAbelian_eq B D,
    truncatedDeRhamCohomologyAbelianMap_filteredChernProduct B D k L,
    deRhamChernProduct_mem_hodgeFiltrationAbelian B D k L,
    hodgeGradedIso_inv_gradedPieceProjection_filteredChernProduct B D k L⟩

end Classes

end AlgebraicGeometry.SheafOfModules

end
